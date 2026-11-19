module

public import LeanQbe.T.Arm64.Base

/-!
# AArch64 Scalar Instruction Selection (`T9`, `GprIsa`)

Defines `LeanQbe.T.Arm64.armGpr : GprIsa Reg Empty ArmCond Directive` over `LeanQbe.T.Arm64.Base`:
* Move-class snippets (`armMov`, `armMovi`, `armSetcc`), `armClearFlags` (`ADDS xzr, xzr, xzr`),
  `armJmp`, `armJcc`, and bit-0 `armJnzGpr` (`TBNZ w_r, #0, l`), all handling `.SP` cleanly.
* `armLoad` and `armStore` routing `.baseDisp .SP` through `.X16` to avoid Kraken's
  `checkSPAlignment` fault, supporting arbitrary 64-bit displacements, `.SP` destinations/sources,
  and `.flag`/`.imm` boolean stores.
* Scalar `armOp` and `armSupportsScalarOp`:
  - `[8, 16, 32, 64]`: `copy`, `add`, `sub`, `mul`, `neg`, `and`, `or`, `xor`, `not`, `shl`, `lshr`,
    `ashr`, `rotl`, `rotr`, `ofBool`, `udiv`, `sdiv`, `urem`, `srem`, `udiv0`, `sdiv0`, `cmp`
    (`.gpr` and `.flag`), `select` (`CSEL`), `zext`, `sext`, `trunc`, `bitcast`, plus `.bool`
    `copy`/`and`/`or`/`xor`/`not`.
  - `[16, 32, 64]`: `bswap`.
  - `[32, 64]`: `clz`, `cls`, `rbit`, `ctz`, `addc`, `subb`, `umulw`, `smulw`, `fshl`, `fshr`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64

/-! ## 1. Low-level instruction builders and operand helpers -/

/-- Register width (`W64` for 64-bit operations, `W32` for 8/16/32-bit operations). -/
abbrev armWidthOf (n : Nat) : RegWidth :=
  if n == 64 then .W64 else .W32

/-- Materialize architectural condition `c` as `0/1` into `x_d` without clobbering flags. -/
abbrev armCset64 (d : XReg) (c : ArmCond) : Directive :=
  ins (w := .W64) (.CSINC (zr d .W64) (xzr .W64) (xzr .W64) (armNegCond c).toKraken)

/-- Memory operand `[rb, #disp]`. -/
abbrev armAtDisp (rb : XReg) (disp : Int64) : AddrExpr :=
  { base := .low (.reg rb) .W64, off := .imm { imm := .int64 disp, index := none } }

/-- Memory operand `[rb, idx]`. -/
abbrev armAtIdx (rb idx : XReg) : AddrExpr :=
  { base := .low (.reg rb) .W64,
    off := .reg { reg := ⟨.W64, zr idx .W64⟩, ext := { type := .UXTX, amount := .E0 } } }

/-- Load an unsigned `n`-bit operand into `tmp` if immediate, or return its GP `XReg`. -/
def armArgIn {n : Nat} (tmp : XReg) : PArg Reg Empty ArmCond (.bits n) → Option (List Directive × XReg)
  | .gpr (.reg r) => some ([], r)
  | .gpr .SP => none
  | .imm c => some ([armLdrPoolBv tmp (c.setWidth 64)], tmp)

/-- Load a `.bool` operand into `tmp` if immediate/flag, or return its GP `XReg`. -/
def armBoolArgIn (tmp : XReg) : PArg Reg Empty ArmCond .bool → Option (List Directive × XReg)
  | .gpr (.reg r) => some ([], r)
  | .gpr .SP => none
  | .imm b => some ([armLdrPoolBv tmp (BitVec.ofNat 64 b.toNat)], tmp)
  | .flag c => some ([armCset64 tmp c], tmp)

/-- 12-bit unsigned arithmetic immediate if `c.toNat < 4096`. -/
def armImm12? {n : Nat} (c : BitVec n) : Option ExtOrImmReg :=
  if Nat.blt c.toNat 4096 then
    some (.imm { imm := .int64 (Int64.ofNat c.toNat), shift := .S0 })
  else none

/-- Logical immediate `n - 1` (`7`, `15`, `31`, or `63`) for shift/bit masks. -/
def armShiftMaskConst (n : Nat) : ConstExpr :=
  .int64 (Int64.ofNat (n - 1))

/-! ## 2. Moves, branches, flag clearing, loads, and stores -/

/-- Flags guaranteed false immediately after `armClearFlags`. -/
def armZeroFlags : List ArmCond := [.cs, .vs]

/-- `adds xzr, xzr, xzr`: clears `C` and `V` (and sets `N = 0, Z = 1`) without touching any GPR. -/
def armClearFlags : List Directive :=
  [ins (w := .W64) (.ADDS_s (xzr .W64) (xzr .W64) { reg := xzr .W64, amount := 0, shift := .LSL })]

/-- `add rd, rs, #0`: valid for all `rd, rs : Reg` including `.SP`, preserving all flags. -/
def armMov (rd rs : Reg) : List Directive :=
  [ins (w := .W64) (.ADD_e (.low rd .W64) (.low rs .W64) imm0)]

/-- Load 64-bit constant `c` into `rd` (routing `.SP` via `.X16`), preserving all flags. -/
def armMovi (rd : Reg) (c : BitVec 64) : List Directive :=
  match rd with
  | .reg d => [armLdrPoolBv d c]
  | .SP => [armLdrPoolBv .X16 c, armMovToSp .X16]

/-- Materialize flag condition `c` into `rd` (`0/1`, routing `.SP` via `.X16`), preserving flags. -/
def armSetcc (rd : Reg) (c : ArmCond) : List Directive :=
  match rd with
  | .reg d => [armCset64 d c]
  | .SP => [armCset64 .X16 c, armMovToSp .X16]

/-- Unconditional branch `b l`. -/
def armJmp (l : Sym) : List Directive :=
  [ins (w := .W64) (.B (.label l))]

/-- Conditional branch `b.<c> l`. -/
def armJcc (c : ArmCond) (l : Sym) : List Directive :=
  [ins (w := .W64) (.B_cond c.toKraken (.label l))]

/-- Test low bit `0` of `.bool` register `r` via `tbnz` (routing `.SP` via `.X16`), preserving flags. -/
def armJnzGpr (r : Reg) (l : Sym) : List Directive × FlagMask :=
  match r with
  | .reg x => ([ins (w := .W32) (.TBNZ (zr x .W32) 0 (.label l))], maskNone)
  | .SP => ([armMovToX .X16 .SP, ins (w := .W32) (.TBNZ (zr .X16 .W32) 0 (.label l))], maskNone)

/-- True iff `disp` fits as a scaled unsigned offset `[xb, #disp]` for access size `scale`. -/
def armFitsScaledOff (scale : Nat) (disp : Int64) : Bool :=
  Nat.ble disp.toBitVec.toNat (4095 * scale) && (disp.toBitVec.toNat % scale == 0)

/-- Compute effective `AddrExpr` using scratch `.X16` only, ensuring `mem.base` is never `.SP`. -/
def armSetupAddr (scale : Nat) : AddrArg Reg → List Directive × AddrExpr
  | .imm addr => ([armLdrPoolBv .X16 addr], atReg .X16)
  | .baseDisp (.reg rb) disp =>
    if disp == 0 then ([], atReg rb)
    else if armFitsScaledOff scale disp then ([], armAtDisp rb disp)
    else ([armLdrPoolBv .X16 disp.toBitVec], armAtIdx rb .X16)
  | .baseDisp .SP disp =>
    if disp == 0 then ([armMovToX .X16 .SP], atReg .X16)
    else if Nat.blt disp.toBitVec.toNat 4096 then
      ([ins (w := .W64) (.ADD_e (.low (.reg .X16) .W64) (.low .SP .W64)
        (.imm { imm := .int64 disp, shift := .S0 }))], atReg .X16)
    else
      ([armLdrPoolBv .X16 disp.toBitVec,
        ins (w := .W64) (.ADD_e (.low (.reg .X16) .W64) (.low .SP .W64)
          (.ext { reg := ⟨.W64, zr .X16 .W64⟩, ext := { type := .UXTX, amount := .E0 } }))],
        atReg .X16)

/-- Byte scale of a scalar memory access type, or `none` if unsupported. -/
def armMemScale : Ty → Option Nat
  | .bool | .bits 8 => some 1
  | .bits 16 => some 2
  | .bits 32 => some 4
  | .bits 64 => some 8
  | _ => none

/-- Single load directive from effective address `addr` into `x_d`/`w_d`. -/
def armLoadDir (t : Ty) (d : XReg) (addr : AddrExpr) : Option Directive :=
  match t with
  | .bool | .bits 8 => some (ins (.LDRB (zr d .W32) addr))
  | .bits 16 => some (ins (.LDRH (zr d .W32) addr))
  | .bits 32 => some (ins (w := .W32) (.LDR (zr d .W32) (.addr addr)))
  | .bits 64 => some (ins (w := .W64) (.LDR (zr d .W64) (.addr addr)))
  | _ => none

/-- Single store directive from `x_s`/`w_s` to effective address `addr`. -/
def armStoreDir (t : Ty) (s : XReg) (addr : AddrExpr) : Option Directive :=
  match t with
  | .bool | .bits 8 => some (ins (.STRB (zr s .W32) addr))
  | .bits 16 => some (ins (.STRH (zr s .W32) addr))
  | .bits 32 => some (ins (w := .W32) (.STR (zr s .W32) addr))
  | .bits 64 => some (ins (w := .W64) (.STR (zr s .W64) addr))
  | _ => none

/-- Load scalar `t` from `a` into `rd` (handling `.SP` base/destination), preserving all flags. -/
def armLoad (t : Ty) (rd : Reg) (a : AddrArg Reg) : Option (List Directive × FlagMask) := do
  let scale ← armMemScale t
  let (setup, addr) := armSetupAddr scale a
  match rd with
  | .reg d =>
    let dir ← armLoadDir t d addr
    some (setup ++ [dir], maskNone)
  | .SP =>
    let dir ← armLoadDir t .X16 addr
    some (setup ++ [dir, armMovToSp .X16], maskNone)

/-- Materialize stored operand `pa` into `.X17` (or return its `XReg`) without clobbering flags. -/
def armStoreValIn : (t : Ty) → PArg Reg Empty ArmCond t → Option (List Directive × XReg)
  | .bool, .gpr (.reg r) => some ([], r)
  | .bool, .gpr .SP => some ([armMovToX .X17 .SP], .X17)
  | .bool, .imm b => some ([armLdrPoolBv .X17 (BitVec.ofNat 64 b.toNat)], .X17)
  | .bool, .flag c => some ([armCset64 .X17 c], .X17)
  | .bits _, .gpr (.reg r) => some ([], r)
  | .bits _, .gpr .SP => some ([armMovToX .X17 .SP], .X17)
  | .bits _, .imm c => some ([armLdrPoolBv .X17 (c.setWidth 64)], .X17)
  | _, _ => none

/-- Store scalar `pa` of type `t` to `a`, preserving all flags. -/
def armStore (t : Ty) (pa : PArg Reg Empty ArmCond t) (a : AddrArg Reg) :
    Option (List Directive × FlagMask) := do
  let scale ← armMemScale t
  let (valSetup, rx) ← armStoreValIn t pa
  let (addrSetup, addr) := armSetupAddr scale a
  let dir ← armStoreDir t rx addr
  some (valSetup ++ addrSetup ++ [dir], maskNone)

/-! ## 3. Scalar `armOp` helpers (`[8, 16, 32, 64]`, `bswap`, `[32, 64]` bit/carry/mulw/fsh) -/

/-- `ArmCond` corresponding to integer comparison `o` after `cmp a, b` (`SUBS`). -/
def armCmpCond : CmpOp → ArmCond
  | .eq => .eq | .ne => .ne | .ult => .cc | .ule => .ls | .ugt => .hi
  | .uge => .cs | .slt => .lt | .sle => .le | .sgt => .gt | .sge => .ge

/-- Swap comparison orientation when immediate is on the left (`a o b ↔ b (swap o) a`). -/
def armSwapCmp : CmpOp → CmpOp
  | .eq => .eq | .ne => .ne | .ult => .ugt | .ule => .uge | .ugt => .ult
  | .uge => .ule | .slt => .sgt | .sle => .sge | .sgt => .slt | .sge => .sle

def armIsSignedCmp : CmpOp → Bool
  | .slt | .sle | .sgt | .sge => true
  | _ => false

/-- Extend low `n` bits (`8` or `16`) into `.W32` (`UBFM` or `SBFM`). -/
def armExt32 (signed : Bool) (n : Nat) (d s : XReg) : Directive :=
  if signed then ins (.SBFM (zr d .W32) (zr s .W32) 0 (n - 1))
  else ins (.UBFM (zr d .W32) (zr s .W32) 0 (n - 1))

/-- Emit boolean `copy`, `and`, `or`, `xor`, or `not` into GP register `d`. -/
def armBoolOp {sig : List Ty} (code : OpCode sig [.bool]) (pas : Tup (PArg Reg Empty ArmCond) sig)
    (d : XReg) : Option (List Directive × FlagMask) :=
  match code, pas with
  | .copy .bool, (.gpr (.reg r), ()) => some ([ins (.ORR_s (zr d .W32) (xzr .W32) (sh r))], maskNone)
  | .copy .bool, (.imm b, ()) => some ([armLdrPoolBv d (BitVec.ofNat 64 b.toNat)], maskNone)
  | .copy .bool, (.flag c, ()) => some ([armCset64 d c], maskNone)
  | .not .bool, (pa, ()) => do
    let (ca, ra) ← armBoolArgIn .X16 pa
    some (ca ++ [ins (.EOR_i (.low (.reg d) .W32) (zr ra .W32) (.int64 1))], maskNone)
  | .and .bool, (pa, pb, ()) => do
    let (ca, ra) ← armBoolArgIn .X16 pa
    let (cb, rb) ← armBoolArgIn .X17 pb
    some (ca ++ cb ++ [ins (.AND_s (zr d .W32) (zr ra .W32) (sh rb))], maskNone)
  | .or .bool, (pa, pb, ()) => do
    let (ca, ra) ← armBoolArgIn .X16 pa
    let (cb, rb) ← armBoolArgIn .X17 pb
    some (ca ++ cb ++ [ins (.ORR_s (zr d .W32) (zr ra .W32) (sh rb))], maskNone)
  | .xor .bool, (pa, pb, ()) => do
    let (ca, ra) ← armBoolArgIn .X16 pa
    let (cb, rb) ← armBoolArgIn .X17 pb
    some (ca ++ cb ++ [ins (.EOR_s (zr d .W32) (zr ra .W32) (sh rb))], maskNone)
  | _, _ => none

/-- Copy `n`-bit value (`n ∈ {8, 16, 32, 64}`) from `pa` into GP register `d`. -/
def armCopyBits (n : Nat) (pa : PArg Reg Empty ArmCond (.bits n)) (d : XReg) :
    Option (List Directive × FlagMask) :=
  let w := armWidthOf n
  match pa with
  | .gpr (.reg r) => some ([ins (.ORR_s (zr d w) (xzr w) (sh r))], maskNone)
  | .gpr .SP => none
  | .imm c => some ([armLdrPoolBv d (c.setWidth 64)], maskNone)

/-- Zero-extension `zext m n` (`m, n ∈ {8, 16, 32, 64}`, `m ≤ n`). -/
def armZextOp (m n : Nat) (pa : PArg Reg Empty ArmCond (.bits m)) (d : XReg) :
    Option (List Directive × FlagMask) :=
  if !([8, 16, 32, 64].contains m && [8, 16, 32, 64].contains n && Nat.ble m n) then none
  else match pa with
    | .imm c => some ([armLdrPoolBv d ((c.setWidth n).setWidth 64)], maskNone)
    | .gpr .SP => none
    | .gpr (.reg r) =>
      if m == 8 then some ([ins (.UBFM (zr d .W64) (zr r .W64) 0 7)], maskNone)
      else if m == 16 then some ([ins (.UBFM (zr d .W64) (zr r .W64) 0 15)], maskNone)
      else if m == 32 then some ([ins (.ORR_s (zr d .W32) (xzr .W32) (sh r))], maskNone)
      else some ([ins (.ORR_s (zr d .W64) (xzr .W64) (sh r))], maskNone)

/-- Sign-extension `sext m n` (`m, n ∈ {8, 16, 32, 64}`, `m ≤ n`). -/
def armSextOp (m n : Nat) (pa : PArg Reg Empty ArmCond (.bits m)) (d : XReg) :
    Option (List Directive × FlagMask) :=
  if !([8, 16, 32, 64].contains m && [8, 16, 32, 64].contains n && Nat.ble m n) then none
  else match pa with
    | .imm c => some ([armLdrPoolBv d ((c.signExtend n).setWidth 64)], maskNone)
    | .gpr .SP => none
    | .gpr (.reg r) =>
      if m == 8 then some ([ins (.SBFM (zr d .W64) (zr r .W64) 0 7)], maskNone)
      else if m == 16 then some ([ins (.SBFM (zr d .W64) (zr r .W64) 0 15)], maskNone)
      else if m == 32 then some ([ins (.SBFM (zr d .W64) (zr r .W64) 0 31)], maskNone)
      else some ([ins (.ORR_s (zr d .W64) (xzr .W64) (sh r))], maskNone)

/-- Truncation `trunc m n` (`m, n ∈ {8, 16, 32, 64}`, `n ≤ m`). -/
def armTruncOp (m n : Nat) (pa : PArg Reg Empty ArmCond (.bits m)) (d : XReg) :
    Option (List Directive × FlagMask) :=
  if !([8, 16, 32, 64].contains m && [8, 16, 32, 64].contains n && Nat.ble n m) then none
  else match pa with
    | .imm c => some ([armLdrPoolBv d ((c.setWidth n).setWidth 64)], maskNone)
    | .gpr .SP => none
    | .gpr (.reg r) =>
      let w := armWidthOf n
      some ([ins (.ORR_s (zr d w) (xzr w) (sh r))], maskNone)

/-- Materialize `.bool` operand as `0/1` in `n`-bit register `d`. -/
def armOfBoolOp (n : Nat) (pa : PArg Reg Empty ArmCond .bool) (d : XReg) :
    Option (List Directive × FlagMask) :=
  if ![8, 16, 32, 64].contains n then none
  else match pa with
    | .gpr (.reg r) => some ([ins (.UBFM (zr d .W64) (zr r .W64) 0 7)], maskNone)
    | .gpr .SP => none
    | .imm b => some ([armLdrPoolBv d (BitVec.ofNat 64 b.toNat)], maskNone)
    | .flag c => some ([armCset64 d c], maskNone)

/-- Wrapping binary ALU operations (`add`, `sub`, `mul`, `and`, `or`, `xor`) at `[8, 16, 32, 64]`. -/
inductive ArmBinK | add | sub | mul | and | or | xor

def armBinDir (k : ArmBinK) (w : RegWidth) (d ra rb : XReg) : Directive :=
  match k with
  | .add => ins (.ADD_s (zr d w) (zr ra w) (sh rb))
  | .sub => ins (.SUB_s (zr d w) (zr ra w) (sh rb))
  | .mul => ins (.MADD (zr d w) (zr ra w) (zr rb w) (xzr w))
  | .and => ins (.AND_s (zr d w) (zr ra w) (sh rb))
  | .or => ins (.ORR_s (zr d w) (zr ra w) (sh rb))
  | .xor => ins (.EOR_s (zr d w) (zr ra w) (sh rb))

def armBinOp (k : ArmBinK) (n : Nat) (pa pb : PArg Reg Empty ArmCond (.bits n)) (d : XReg) :
    Option (List Directive × FlagMask) := do
  if ![8, 16, 32, 64].contains n then none
  else
    let w := armWidthOf n
    match k, pa, pb with
    | .add, .gpr (.reg ra), .imm cb =>
      match armImm12? cb with
      | some ei => some ([ins (.ADD_e (.low (.reg d) w) (.low (.reg ra) w) ei)], maskNone)
      | none =>
        let (cb', rb) ← armArgIn .X17 pb
        some (cb' ++ [armBinDir k w d ra rb], maskNone)
    | .add, .imm ca, .gpr (.reg rb) =>
      match armImm12? ca with
      | some ei => some ([ins (.ADD_e (.low (.reg d) w) (.low (.reg rb) w) ei)], maskNone)
      | none =>
        let (ca', ra) ← armArgIn .X16 pa
        some (ca' ++ [armBinDir k w d ra rb], maskNone)
    | .sub, .gpr (.reg ra), .imm cb =>
      match armImm12? cb with
      | some ei => some ([ins (.SUB_e (.low (.reg d) w) (.low (.reg ra) w) ei)], maskNone)
      | none =>
        let (cb', rb) ← armArgIn .X17 pb
        some (cb' ++ [armBinDir k w d ra rb], maskNone)
    | _, _, _ =>
      let (ca, ra) ← armArgIn .X16 pa
      let (cb, rb) ← armArgIn .X17 pb
      some (ca ++ cb ++ [armBinDir k w d ra rb], maskNone)

/-- Shifts (`shl`, `lshr`, `ashr`) at `[8, 16, 32, 64]`. -/
inductive ArmShiftK | shl | lshr | ashr

def armShiftOp (k : ArmShiftK) (n : Nat) (pa pb : PArg Reg Empty ArmCond (.bits n)) (d : XReg) :
    Option (List Directive × FlagMask) := do
  if ![8, 16, 32, 64].contains n then none
  else if n == 32 || n == 64 then
    let w := armWidthOf n
    match pa, pb with
    | .gpr (.reg ra), .imm cb =>
      let amt := cb.toNat % n
      let dir := match k with
        | .shl => ins (.UBFM (zr d w) (zr ra w) ((w.bits - amt) % w.bits) (w.bits - 1 - amt))
        | .lshr => ins (.UBFM (zr d w) (zr ra w) amt (w.bits - 1))
        | .ashr => ins (.SBFM (zr d w) (zr ra w) amt (w.bits - 1))
      some ([dir], maskNone)
    | _, _ =>
      let (ca, ra) ← armArgIn .X16 pa
      let (cb, rb) ← armArgIn .X17 pb
      let dir := match k with
        | .shl => ins (.LSLV (zr d w) (zr ra w) (zr rb w))
        | .lshr => ins (.LSRV (zr d w) (zr ra w) (zr rb w))
        | .ashr => ins (.ASRV (zr d w) (zr ra w) (zr rb w))
      some (ca ++ cb ++ [dir], maskNone)
  else
    let (ca, ra) ← armArgIn .X16 pa
    let (cb, rb) ← armArgIn .X17 pb
    let prepA : List Directive := match k with
      | .shl => []
      | .lshr => [armExt32 false n .X16 ra]
      | .ashr => [armExt32 true n .X16 ra]
    let ra' : XReg := match k with | .shl => ra | .lshr | .ashr => .X16
    let prepB : List Directive :=
      [ins (.AND_i (.low (.reg .X17) .W32) (zr rb .W32) (armShiftMaskConst n))]
    let dir := match k with
      | .shl => ins (.LSLV (zr d .W32) (zr ra' .W32) (zr .X17 .W32))
      | .lshr => ins (.LSRV (zr d .W32) (zr ra' .W32) (zr .X17 .W32))
      | .ashr => ins (.ASRV (zr d .W32) (zr ra' .W32) (zr .X17 .W32))
    some (ca ++ cb ++ prepA ++ prepB ++ [dir], maskNone)

/-- Rotates (`rotl`, `rotr`) at `[8, 16, 32, 64]`. -/
def armRotOp (isLeft : Bool) (n : Nat) (pa pb : PArg Reg Empty ArmCond (.bits n)) (d : XReg) :
    Option (List Directive × FlagMask) := do
  if ![8, 16, 32, 64].contains n then none
  else if n == 32 || n == 64 then
    let w := armWidthOf n
    match pa, pb with
    | .gpr (.reg ra), .imm cb =>
      let k := if isLeft then (n - cb.toNat % n) % n else cb.toNat % n
      some ([ins (.EXTR (zr d w) (zr ra w) (zr ra w) k)], maskNone)
    | _, _ =>
      let (ca, ra) ← armArgIn .X16 pa
      let (cb, rb) ← armArgIn .X17 pb
      if isLeft then
        some (ca ++ cb ++
          [ins (.SUB_s (zr .X17 w) (xzr w) (sh rb)),
           ins (.RORV (zr d w) (zr ra w) (zr .X17 w))], maskNone)
      else
        some (ca ++ cb ++ [ins (.RORV (zr d w) (zr ra w) (zr rb w))], maskNone)
  else
    let (ca, ra) ← armArgIn .X16 pa
    let (cb, rb) ← armArgIn .X17 pb
    let repA : List Directive :=
      [armExt32 false n .X16 ra,
       ins (.ORR_s (zr .X16 .W32) (zr .X16 .W32)
         { reg := zr .X16 .W32, amount := Int64.ofNat n, shift := .LSL })]
    let cntB : List Directive :=
      if isLeft then
        [ins (.SUB_s (zr .X17 .W32) (xzr .W32) (sh rb)),
         ins (.AND_i (.low (.reg .X17) .W32) (zr .X17 .W32) (armShiftMaskConst n))]
      else
        [ins (.AND_i (.low (.reg .X17) .W32) (zr rb .W32) (armShiftMaskConst n))]
    some (ca ++ cb ++ repA ++ cntB ++
      [ins (.LSRV (zr d .W32) (zr .X16 .W32) (zr .X17 .W32))], maskNone)

/-- Division/remainder (`udiv`, `sdiv`, `urem`, `srem`, `udiv0`, `sdiv0`) at `[8, 16, 32, 64]`. -/
inductive ArmDivK | udiv | sdiv | urem | srem

def armDivRemOp (k : ArmDivK) (n : Nat) (pa pb : PArg Reg Empty ArmCond (.bits n)) (d : XReg) :
    Option (List Directive × FlagMask) := do
  if ![8, 16, 32, 64].contains n then none
  else
    let isSigned := match k with | .sdiv | .srem => true | .udiv | .urem => false
    let isRem := match k with | .urem | .srem => true | .udiv | .sdiv => false
    if n == 32 || n == 64 then
      let w := armWidthOf n
      match pa, pb with
      | .imm ca, .imm cb =>
        let res := if isRem then (if isSigned then ca.srem cb else ca % cb)
                   else if cb == 0 then 0
                   else if isSigned then ca.sdiv cb else ca / cb
        some ([armLdrPoolBv d (res.setWidth 64)], maskNone)
      | _, _ =>
        let (ca, ra) ← armArgIn .X16 pa
        let (cb, rb) ← armArgIn .X17 pb
        if isRem then
          let t : XReg := match pb with | .gpr _ => .X17 | .imm _ => .X16
          let divD := if isSigned then ins (.SDIV (zr t w) (zr ra w) (zr rb w))
                      else ins (.UDIV (zr t w) (zr ra w) (zr rb w))
          some (ca ++ cb ++ [divD, ins (.MSUB (zr d w) (zr t w) (zr rb w) (zr ra w))], maskNone)
        else
          let divD := if isSigned then ins (.SDIV (zr d w) (zr ra w) (zr rb w))
                      else ins (.UDIV (zr d w) (zr ra w) (zr rb w))
          some (ca ++ cb ++ [divD], maskNone)
    else
      let (ca, ra) ← armArgIn .X16 pa
      let (cb, rb) ← armArgIn .X17 pb
      let prep := [armExt32 isSigned n .X16 ra, armExt32 isSigned n .X17 rb]
      let divD := if isSigned then ins (.SDIV (zr d .W32) (zr .X16 .W32) (zr .X17 .W32))
                  else ins (.UDIV (zr d .W32) (zr .X16 .W32) (zr .X17 .W32))
      if isRem then
        some (ca ++ cb ++ prep ++
          [divD, ins (.MSUB (zr d .W32) (zr d .W32) (zr .X17 .W32) (zr .X16 .W32))], maskNone)
      else
        some (ca ++ cb ++ prep ++ [divD], maskNone)

/-- Integer comparisons `cmp o (.bits n)` targeting `.flag c` or `.gpr d`. -/
def armCmpOp (o : CmpOp) (n : Nat) (pa pb : PArg Reg Empty ArmCond (.bits n))
    (dst : PDst Reg Empty ArmCond .bool) : Option (List Directive × FlagMask) := do
  if ![8, 16, 32, 64].contains n then none
  else
    let finish (cmpCode : List Directive) (cond : ArmCond) : Option (List Directive × FlagMask) :=
      match dst with
      | .flag c => if c == cond then some (cmpCode, maskNZCV) else none
      | .gpr (.reg d) => some (cmpCode ++ [armCset64 d cond], maskNZCV)
      | .gpr .SP | .vec _ => none
    if n == 32 || n == 64 then
      let w := armWidthOf n
      match pa, pb with
      | .gpr (.reg ra), .imm cb =>
        match armImm12? cb with
        | some ei => finish [ins (.SUBS_e (xzr w) (.low (.reg ra) w) ei)] (armCmpCond o)
        | none =>
          let (cb', rb) ← armArgIn .X17 pb
          finish (cb' ++ [ins (.SUBS_s (xzr w) (zr ra w) (sh rb))]) (armCmpCond o)
      | .imm ca, .gpr (.reg rb) =>
        match armImm12? ca with
        | some ei => finish [ins (.SUBS_e (xzr w) (.low (.reg rb) w) ei)] (armCmpCond (armSwapCmp o))
        | none =>
          let (ca', ra) ← armArgIn .X16 pa
          finish (ca' ++ [ins (.SUBS_s (xzr w) (zr ra w) (sh rb))]) (armCmpCond o)
      | _, _ =>
        let (ca, ra) ← armArgIn .X16 pa
        let (cb, rb) ← armArgIn .X17 pb
        finish (ca ++ cb ++ [ins (.SUBS_s (xzr w) (zr ra w) (sh rb))]) (armCmpCond o)
    else
      let sgn := armIsSignedCmp o
      let (ca, ra) ← armArgIn .X16 pa
      let (cb, rb) ← armArgIn .X17 pb
      finish (ca ++ cb ++ [armExt32 sgn n .X16 ra, armExt32 sgn n .X17 rb,
        ins (.SUBS_s (xzr .W32) (zr .X16 .W32) (sh .X17))]) (armCmpCond o)

/-- Branchless `CSEL` conditional select at `[8, 16, 32, 64]`. -/
def armSelectOp (n : Nat) (pc : PArg Reg Empty ArmCond .bool)
    (pa pb : PArg Reg Empty ArmCond (.bits n)) (d : XReg) :
    Option (List Directive × FlagMask) := do
  if ![8, 16, 32, 64].contains n then none
  else
    let w := armWidthOf n
    match pc with
    | .imm true => armCopyBits n pa d
    | .imm false => armCopyBits n pb d
    | .flag cond =>
      let (ca, ra) ← armArgIn .X16 pa
      let (cb, rb) ← armArgIn .X17 pb
      some (ca ++ cb ++ [ins (.CSEL (zr d w) (zr ra w) (zr rb w) cond.toKraken)], maskNone)
    | .gpr (.reg rc) =>
      let (ca, ra) ← armArgIn .X16 pa
      let (cb, rb) ← armArgIn .X17 pb
      some (ca ++ cb ++
        [ins (.ANDS_i (xzr .W32) (zr rc .W32) (.int64 1)),
         ins (.CSEL (zr d w) (zr ra w) (zr rb w) .NE)], maskNZCV)
    | .gpr .SP => none

/-- Carry addition `addc n` at `[32, 64]`: `.flag .cs` / `.gpr` / `.imm` carry-in, `.flag .cs` / `.gpr` carry-out. -/
def armAddcOp (n : Nat) (pa pb : PArg Reg Empty ArmCond (.bits n))
    (cin : PArg Reg Empty ArmCond .bool) (d : XReg) (cout : PDst Reg Empty ArmCond .bool)
    (vh : VariantHint) : Option (List Directive × FlagMask) := do
  if !(n == 32 || n == 64) || vh != .default then none
  else
    let w := armWidthOf n
    let post : Option (List Directive) := match cout with
      | .flag .cs => some []
      | .gpr (.reg dc) => if dc == d then none else some [armCset64 dc .cs]
      | _ => none
    let p ← post
    let (ca, ra) ← armArgIn .X16 pa
    let (cb, rb) ← armArgIn .X17 pb
    let main : Option (List Directive) := match cin with
      | .flag .cs => some (ca ++ cb ++ [ins (.ADCS (zr d w) (zr ra w) (zr rb w))])
      | .imm false => some (ca ++ cb ++ [ins (.ADDS_s (zr d w) (zr ra w) (sh rb))])
      | .imm true =>
        some ([ins (.SUBS_s (xzr .W32) (xzr .W32) { reg := xzr .W32, amount := 0, shift := .LSL })] ++
          ca ++ cb ++ [ins (.ADCS (zr d w) (zr ra w) (zr rb w))])
      | .gpr (.reg rc) =>
        some ([ins (.AND_i (.low (.reg .X16) .W32) (zr rc .W32) (.int64 1)),
               ins (.SUBS_e (xzr .W32) (.low (.reg .X16) .W32)
                 (.imm { imm := .int64 1, shift := .S0 }))] ++
          ca ++ cb ++ [ins (.ADCS (zr d w) (zr ra w) (zr rb w))])
      | _ => none
    let m ← main
    some (m ++ p, maskNZCV)

/-- Borrow subtraction `subb n` at `[32, 64]` with inverted ARM carry (`.flag .cc`, `.gpr`, `.imm`). -/
def armSubbOp (n : Nat) (pa pb : PArg Reg Empty ArmCond (.bits n))
    (bin : PArg Reg Empty ArmCond .bool) (d : XReg) (bout : PDst Reg Empty ArmCond .bool)
    (vh : VariantHint) : Option (List Directive × FlagMask) := do
  if !(n == 32 || n == 64) || vh != .default then none
  else
    let w := armWidthOf n
    let post : Option (List Directive) := match bout with
      | .flag .cc => some []
      | .gpr (.reg dc) => if dc == d then none else some [armCset64 dc .cc]
      | _ => none
    let p ← post
    let (ca, ra) ← armArgIn .X16 pa
    let (cb, rb) ← armArgIn .X17 pb
    let main : Option (List Directive) := match bin with
      | .flag .cc => some (ca ++ cb ++ [ins (.SBCS (zr d w) (zr ra w) (zr rb w))])
      | .imm false => some (ca ++ cb ++ [ins (.SUBS_s (zr d w) (zr ra w) (sh rb))])
      | .imm true =>
        some ([ins (.ADDS_s (xzr .W32) (xzr .W32) { reg := xzr .W32, amount := 0, shift := .LSL })] ++
          ca ++ cb ++ [ins (.SBCS (zr d w) (zr ra w) (zr rb w))])
      | .gpr (.reg rc) =>
        some ([ins (.AND_i (.low (.reg .X16) .W32) (zr rc .W32) (.int64 1)),
               ins (.SUBS_s (xzr .W32) (xzr .W32) (sh .X16))] ++
          ca ++ cb ++ [ins (.SBCS (zr d w) (zr ra w) (zr rb w))])
      | _ => none
    let m ← main
    some (m ++ p, maskNZCV)

/-- Full double-width multiplication `umulw` / `smulw` at `[32, 64]`. -/
def armMulwOp (isSigned : Bool) (n : Nat) (pa pb : PArg Reg Empty ArmCond (.bits n))
    (dlo dhi : XReg) : Option (List Directive × FlagMask) := do
  if !(n == 32 || n == 64) || dlo == dhi then none
  else
    let (ca, ra) ← armArgIn .X16 pa
    let (cb, rb) ← armArgIn .X17 pb
    if n == 32 then
      let mul64 := if isSigned then ins (.SMADDL (zr dlo .W64) (zr ra .W32) (zr rb .W32) (xzr .W64))
                   else ins (.UMADDL (zr dlo .W64) (zr ra .W32) (zr rb .W32) (xzr .W64))
      some (ca ++ cb ++ [mul64, ins (.UBFM (zr dhi .W64) (zr dlo .W64) 32 63)], maskNone)
    else
      let mulH (dst : XReg) :=
        if isSigned then ins (.SMULH (zr dst .W64) (zr ra .W64) (zr rb .W64))
        else ins (.UMULH (zr dst .W64) (zr ra .W64) (zr rb .W64))
      let mulL := ins (.MADD (zr dlo .W64) (zr ra .W64) (zr rb .W64) (xzr .W64))
      if dhi != ra && dhi != rb then
        some (ca ++ cb ++ [mulH dhi, mulL], maskNone)
      else if dlo != ra && dlo != rb then
        some (ca ++ cb ++ [mulL, mulH dhi], maskNone)
      else
        some (ca ++ cb ++ [mulH .X16, mulL, ins (.ORR_s (zr dhi .W64) (xzr .W64) (sh .X16))],
          maskNone)

/-- Funnel shifts `fshl` / `fshr` at `[32, 64]`. -/
def armFunnelOp (isLeft : Bool) (n : Nat) (pa pb pc : PArg Reg Empty ArmCond (.bits n))
    (d : XReg) : Option (List Directive × FlagMask) := do
  if !(n == 32 || n == 64) then none
  else
    let w := armWidthOf n
    let (ca, ra) ← armArgIn .X16 pa
    let (cb, rb) ← armArgIn .X17 pb
    match pc with
    | .imm cc =>
      let k := cc.toNat % n
      if isLeft then
        if k == 0 then
          some (ca ++ [ins (.ORR_s (zr d w) (xzr w) (sh ra))], maskNone)
        else
          some (ca ++ cb ++ [ins (.EXTR (zr d w) (zr ra w) (zr rb w) (n - k))], maskNone)
      else
        some (ca ++ cb ++ [ins (.EXTR (zr d w) (zr ra w) (zr rb w) k)], maskNone)
    | .gpr (.reg rc) =>
      let tst := ins (.ANDS_i (xzr w) (zr rc w) (armShiftMaskConst n))
      let body : List Directive := match pa, pb with
        | .imm _, .imm _ =>
          if isLeft then
            [tst,
             ins (.LSLV (zr .X16 w) (zr .X16 w) (zr rc w)),
             ins (.SUB_s (zr d w) (xzr w) (sh rc)),
             ins (.LSRV (zr .X17 w) (zr .X17 w) (zr d w)),
             ins (.ORR_s (zr d w) (zr .X16 w) (sh .X17)),
             ins (.CSEL (zr d w) (zr .X16 w) (zr d w) .EQ)]
          else
            [tst,
             ins (.LSRV (zr .X17 w) (zr .X17 w) (zr rc w)),
             ins (.SUB_s (zr d w) (xzr w) (sh rc)),
             ins (.LSLV (zr .X16 w) (zr .X16 w) (zr d w)),
             ins (.ORR_s (zr d w) (zr .X17 w) (sh .X16)),
             ins (.CSEL (zr d w) (zr .X17 w) (zr d w) .EQ)]
        | _, .gpr _ =>
          if isLeft then
            [tst,
             ins (.SUB_s (zr .X17 w) (xzr w) (sh rc)),
             ins (.LSRV (zr .X17 w) (zr rb w) (zr .X17 w)),
             ins (.LSLV (zr .X16 w) (zr ra w) (zr rc w)),
             ins (.ORR_s (zr .X17 w) (zr .X16 w) (sh .X17)),
             ins (.CSEL (zr d w) (zr .X16 w) (zr .X17 w) .EQ)]
          else
            [tst,
             ins (.SUB_s (zr .X17 w) (xzr w) (sh rc)),
             ins (.LSLV (zr .X17 w) (zr ra w) (zr .X17 w)),
             ins (.LSRV (zr .X16 w) (zr rb w) (zr rc w)),
             ins (.ORR_s (zr .X17 w) (zr .X16 w) (sh .X17)),
             ins (.CSEL (zr d w) (zr .X16 w) (zr .X17 w) .EQ)]
        | _, .imm _ =>
          if isLeft then
            [tst,
             ins (.SUB_s (zr .X16 w) (xzr w) (sh rc)),
             ins (.LSRV (zr .X17 w) (zr .X17 w) (zr .X16 w)),
             ins (.LSLV (zr .X16 w) (zr ra w) (zr rc w)),
             ins (.ORR_s (zr .X17 w) (zr .X16 w) (sh .X17)),
             ins (.CSEL (zr d w) (zr .X16 w) (zr .X17 w) .EQ)]
          else
            [tst,
             ins (.SUB_s (zr .X16 w) (xzr w) (sh rc)),
             ins (.LSLV (zr .X16 w) (zr ra w) (zr .X16 w)),
             ins (.LSRV (zr .X17 w) (zr .X17 w) (zr rc w)),
             ins (.ORR_s (zr .X16 w) (zr .X17 w) (sh .X16)),
             ins (.CSEL (zr d w) (zr .X17 w) (zr .X16 w) .EQ)]
      some (ca ++ cb ++ body, maskNZCV)
    | .gpr .SP => none

/-- Scalar `OpCode` lowering for AArch64. -/
def armOp {sig rs : List Ty} (code : OpCode sig rs) (pas : Tup (PArg Reg Empty ArmCond) sig)
    (dsts : Tup (PDst Reg Empty ArmCond) rs) (vh : VariantHint) : Option (List Directive × FlagMask) :=
  match sig, rs, code, pas, dsts with
  | _, _, .copy .bool, (pa, ()), (.gpr (.reg d), ()) => armBoolOp (.copy .bool) (pa, ()) d
  | _, _, .and .bool, (pa, pb, ()), (.gpr (.reg d), ()) => armBoolOp (.and .bool) (pa, pb, ()) d
  | _, _, .or .bool, (pa, pb, ()), (.gpr (.reg d), ()) => armBoolOp (.or .bool) (pa, pb, ()) d
  | _, _, .xor .bool, (pa, pb, ()), (.gpr (.reg d), ()) => armBoolOp (.xor .bool) (pa, pb, ()) d
  | _, _, .not .bool, (pa, ()), (.gpr (.reg d), ()) => armBoolOp (.not .bool) (pa, ()) d
  | _, _, .copy (.bits n), (pa, ()), (.gpr (.reg d), ()) =>
    if [8, 16, 32, 64].contains n then armCopyBits n pa d else none
  | _, _, .bitcast (.bits m) (.bits n) _, (pa, ()), (.gpr (.reg d), ()) =>
    if [8, 16, 32, 64].contains m && [8, 16, 32, 64].contains n then
      armCopyBits m pa d
    else none
  | _, _, .zext m n, (pa, ()), (.gpr (.reg d), ()) => armZextOp m n pa d
  | _, _, .sext m n, (pa, ()), (.gpr (.reg d), ()) => armSextOp m n pa d
  | _, _, .trunc m n, (pa, ()), (.gpr (.reg d), ()) => armTruncOp m n pa d
  | _, _, .ofBool n, (pa, ()), (.gpr (.reg d), ()) => armOfBoolOp n pa d
  | _, _, .add (.bits n), (pa, pb, ()), (.gpr (.reg d), ()) => armBinOp .add n pa pb d
  | _, _, .sub (.bits n), (pa, pb, ()), (.gpr (.reg d), ()) => armBinOp .sub n pa pb d
  | _, _, .mul (.bits n), (pa, pb, ()), (.gpr (.reg d), ()) => armBinOp .mul n pa pb d
  | _, _, .and (.bits n), (pa, pb, ()), (.gpr (.reg d), ()) => armBinOp .and n pa pb d
  | _, _, .or (.bits n), (pa, pb, ()), (.gpr (.reg d), ()) => armBinOp .or n pa pb d
  | _, _, .xor (.bits n), (pa, pb, ()), (.gpr (.reg d), ()) => armBinOp .xor n pa pb d
  | _, _, .neg (.bits n), (pa, ()), (.gpr (.reg d), ()) =>
    if ![8, 16, 32, 64].contains n then none
    else match pa with
      | .imm c => some ([armLdrPoolBv d ((-c).setWidth 64)], maskNone)
      | .gpr (.reg r) =>
        let w := armWidthOf n
        some ([ins (.SUB_s (zr d w) (xzr w) (sh r))], maskNone)
      | .gpr .SP => none
  | _, _, .not (.bits n), (pa, ()), (.gpr (.reg d), ()) =>
    if ![8, 16, 32, 64].contains n then none
    else match pa with
      | .imm c => some ([armLdrPoolBv d ((~~~c).setWidth 64)], maskNone)
      | .gpr (.reg r) =>
        let w := armWidthOf n
        some ([ins (.ORN_s (zr d w) (xzr w) (sh r))], maskNone)
      | .gpr .SP => none
  | _, _, .shl (.bits n), (pa, pb, ()), (.gpr (.reg d), ()) => armShiftOp .shl n pa pb d
  | _, _, .lshr (.bits n), (pa, pb, ()), (.gpr (.reg d), ()) => armShiftOp .lshr n pa pb d
  | _, _, .ashr (.bits n), (pa, pb, ()), (.gpr (.reg d), ()) => armShiftOp .ashr n pa pb d
  | _, _, .rotl (.bits n), (pa, pb, ()), (.gpr (.reg d), ()) => armRotOp true n pa pb d
  | _, _, .rotr (.bits n), (pa, pb, ()), (.gpr (.reg d), ()) => armRotOp false n pa pb d
  | _, _, .udiv n, (pa, pb, ()), (.gpr (.reg d), ()) => armDivRemOp .udiv n pa pb d
  | _, _, .udiv0 n, (pa, pb, ()), (.gpr (.reg d), ()) => armDivRemOp .udiv n pa pb d
  | _, _, .sdiv n, (pa, pb, ()), (.gpr (.reg d), ()) => armDivRemOp .sdiv n pa pb d
  | _, _, .sdiv0 n, (pa, pb, ()), (.gpr (.reg d), ()) => armDivRemOp .sdiv n pa pb d
  | _, _, .urem n, (pa, pb, ()), (.gpr (.reg d), ()) => armDivRemOp .urem n pa pb d
  | _, _, .srem n, (pa, pb, ()), (.gpr (.reg d), ()) => armDivRemOp .srem n pa pb d
  | _, _, .bswap (.bits n), (pa, ()), (.gpr (.reg d), ()) => do
    if ![16, 32, 64].contains n then none
    else
      let (ca, ra) ← armArgIn .X16 pa
      let dir := if n == 16 then ins (.REV16 (zr d .W32) (zr ra .W32))
                 else if n == 32 then ins (.REV (zr d .W32) (zr ra .W32))
                 else ins (.REV (zr d .W64) (zr ra .W64))
      some (ca ++ [dir], maskNone)
  | _, _, .clz n, (pa, ()), (.gpr (.reg d), ()) => do
    if !(n == 32 || n == 64) then none
    else
      let (ca, ra) ← armArgIn .X16 pa
      let w := armWidthOf n
      some (ca ++ [ins (.CLZ (zr d w) (zr ra w))], maskNone)
  | _, _, .cls n, (pa, ()), (.gpr (.reg d), ()) => do
    if !(n == 32 || n == 64) then none
    else
      let (ca, ra) ← armArgIn .X16 pa
      let w := armWidthOf n
      some (ca ++ [ins (.CLS (zr d w) (zr ra w))], maskNone)
  | _, _, .rbit n, (pa, ()), (.gpr (.reg d), ()) => do
    if !(n == 32 || n == 64) then none
    else
      let (ca, ra) ← armArgIn .X16 pa
      let w := armWidthOf n
      some (ca ++ [ins (.RBIT (zr d w) (zr ra w))], maskNone)
  | _, _, .ctz n, (pa, ()), (.gpr (.reg d), ()) => do
    if !(n == 32 || n == 64) then none
    else
      let (ca, ra) ← armArgIn .X16 pa
      let w := armWidthOf n
      some (ca ++ [ins (.RBIT (zr d w) (zr ra w)), ins (.CLZ (zr d w) (zr d w))], maskNone)
  | _, _, .cmp o (.bits n) _ rfl, (pa, pb, ()), (dst, ()) => armCmpOp o n pa pb dst
  | _, _, .select (.bits n), (pc, pa, pb, ()), (.gpr (.reg d), ()) => armSelectOp n pc pa pb d
  | _, _, .addc n, (pa, pb, cin, ()), (.gpr (.reg d), cout, ()) =>
    armAddcOp n pa pb cin d cout vh
  | _, _, .subb n, (pa, pb, bin, ()), (.gpr (.reg d), bout, ()) =>
    armSubbOp n pa pb bin d bout vh
  | _, _, .umulw n, (pa, pb, ()), (.gpr (.reg dlo), .gpr (.reg dhi), ()) =>
    armMulwOp false n pa pb dlo dhi
  | _, _, .smulw n, (pa, pb, ()), (.gpr (.reg dlo), .gpr (.reg dhi), ()) =>
    armMulwOp true n pa pb dlo dhi
  | _, _, .fshl n, (pa, pb, pc, ()), (.gpr (.reg d), ()) => armFunnelOp true n pa pb pc d
  | _, _, .fshr n, (pa, pb, pc, ()), (.gpr (.reg d), ()) => armFunnelOp false n pa pb pc d
  | _, _, _, _, _ => none

/-- Computable `rfl`-safe scalar opcode support gate for AArch64 (`GprIsa.supportsScalarOp`). -/
def armSupportsScalarOp {sig rs : List Ty} (code : OpCode sig rs)
    (_args : Tup (Arg (fun _ => Unit)) sig) : Bool :=
  match sig, rs, code with
  | _, _, .copy (.bits n) | _, _, .add (.bits n) | _, _, .sub (.bits n) | _, _, .mul (.bits n)
  | _, _, .neg (.bits n) | _, _, .and (.bits n) | _, _, .or (.bits n) | _, _, .xor (.bits n)
  | _, _, .not (.bits n) | _, _, .shl (.bits n) | _, _, .lshr (.bits n) | _, _, .ashr (.bits n)
  | _, _, .rotl (.bits n) | _, _, .rotr (.bits n) | _, _, .ofBool n
  | _, _, .udiv n | _, _, .sdiv n | _, _, .urem n | _, _, .srem n
  | _, _, .udiv0 n | _, _, .sdiv0 n | _, _, .cmp _ (.bits n) _ _
  | _, _, .select (.bits n) => [8, 16, 32, 64].contains n
  | _, _, .copy .bool | _, _, .and .bool | _, _, .or .bool
  | _, _, .xor .bool | _, _, .not .bool => true
  | _, _, .bswap (.bits n) => [16, 32, 64].contains n
  | _, _, .clz n | _, _, .cls n | _, _, .rbit n | _, _, .ctz n
  | _, _, .fshl n | _, _, .fshr n
  | _, _, .addc n | _, _, .subb n | _, _, .umulw n | _, _, .smulw n => [32, 64].contains n
  | _, _, .zext m n | _, _, .sext m n =>
    [8, 16, 32, 64].contains m && [8, 16, 32, 64].contains n && Nat.ble (m + 1) n
  | _, _, .trunc m n =>
    [8, 16, 32, 64].contains m && [8, 16, 32, 64].contains n && Nat.ble (n + 1) m
  | _, _, .bitcast (.bits m) (.bits n) _ =>
    [8, 16, 32, 64].contains m && [8, 16, 32, 64].contains n
  | _, _, _ => false

/-- AArch64 `GprIsa` instance over `LeanQbe.T.Arm64.Base`. -/
@[reducible] def armGpr : GprIsa Reg Empty ArmCond Directive where
  condReads := armCondReads
  negCond := armNegCond
  zeroFlags := armZeroFlags
  clearFlags := armClearFlags
  mov := armMov
  movi := armMovi
  setcc := armSetcc
  jmp := armJmp
  jcc := armJcc
  jnzGpr := armJnzGpr
  op := armOp
  load := armLoad
  store := armStore
  supportsScalarOp := armSupportsScalarOp

end LeanQbe.T.Arm64
