module

public import LeanQbe.T.Arm64.Base
public import LeanQbe.T.IselStepAttr

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

open LeanQbe.T

/-! ## 1. Low-level instruction builders and operand helpers -/

/-- Low-level AArch64 `Instr` constructor matching `ins`. -/
abbrev armIselInsI {w : RegWidth} (op : Operation w) : Instr :=
  { operation_size := w, operation := op }

/-- Load 64-bit literal pool constant `c` into GP register `d` (`Instr`). -/
abbrev armIselLdrPoolBvI (d : XReg) (c : BitVec 64) : Instr :=
  armIselInsI (w := .W64) (.LDR (zr d .W64) (.lit (.pool { expr := .int64 (Int64.ofBitVec c) })))

/-- Move `s : Reg` (possibly `.SP`) to `d : XReg` (`Instr`). -/
abbrev armIselMovToXI (d : XReg) (s : Reg) : Instr :=
  armIselInsI (.ADD_e (.low (.reg d) .W64) (.low s .W64) imm0)

/-- Move `s : XReg` to `.SP` (`Instr`). -/
abbrev armIselMovToSpI (s : XReg) : Instr :=
  armIselInsI (.ADD_e (.low .SP .W64) (.low (.reg s) .W64) imm0)

/-- Register width (`W64` for 64-bit operations, `W32` for 8/16/32-bit operations). -/
abbrev armWidthOf (n : Nat) : RegWidth :=
  if n == 64 then .W64 else .W32

/-- Materialize condition `c` as `0/1` into `x_d` without clobbering flags (`Instr`). -/
abbrev armCset64I (d : XReg) (c : ArmCond) : Instr :=
  armIselInsI (.CSINC (zr d .W64) (xzr .W64) (xzr .W64) (armNegCond c).toKraken)

/-- Materialize architectural condition `c` as `0/1` into `x_d` without clobbering flags. -/
abbrev armCset64 (d : XReg) (c : ArmCond) : Directive :=
  .instr (armCset64I d c)

/-- Memory operand `[rb, #disp]`. -/
abbrev armAtDisp (rb : XReg) (disp : Int64) : AddrExpr :=
  { base := .low (.reg rb) .W64, off := .imm { imm := .int64 disp, index := none } }

/-- Memory operand `[rb, idx]`. -/
abbrev armAtIdx (rb idx : XReg) : AddrExpr :=
  { base := .low (.reg rb) .W64,
    off := .reg { reg := ⟨.W64, zr idx .W64⟩, ext := { type := .UXTX, amount := .E0 } } }

/-- Memory extension shift amount for `AddrScale` at byte access size `scale`. -/
def armMemExtendAmount (scale : Nat) : AddrScale → Option MemExtendAmount
  | .s1 => some .E0
  | .s2 => if scale == 2 then some .E1 else none
  | .s4 => if scale == 4 then some .E2 else none
  | .s8 => if scale == 8 then some .E3 else none

/-- Memory operand `[rb, ri, lsl #amt]`. -/
abbrev armAtIdxScale (rb ri : XReg) (amt : MemExtendAmount) : AddrExpr :=
  { base := .low (.reg rb) .W64,
    off := .reg { reg := ⟨.W64, zr ri .W64⟩, ext := { type := .UXTX, amount := amt } } }

/-- `MOVZ x_d, #k, lsl #sh` (`Instr`). -/
abbrev armMovzI (d : XReg) (k : Nat) (sh : MovShift .W64) : Instr :=
  armIselInsI (w := .W64) (.MOVZ (zr d .W64) (.int64 (Int64.ofNat k)) sh)

/-- `MOVN x_d, #k, lsl #sh` (`Instr`). -/
abbrev armMovnI (d : XReg) (k : Nat) (sh : MovShift .W64) : Instr :=
  armIselInsI (w := .W64) (.MOVN (zr d .W64) (.int64 (Int64.ofNat k)) sh)

/-- `MOVK x_d, #k, lsl #sh` (`Instr`). -/
abbrev armMovkI (d : XReg) (k : Nat) (sh : MovShift .W64) : Instr :=
  armIselInsI (w := .W64) (.MOVK (zr d .W64) (.int64 (Int64.ofNat k)) sh)

/-- Non-zero `(chunk16, shift)` pairs of a 64-bit constant. -/
def armNonZeroChunks (v : BitVec 64) : List (Nat × MovShift .W64) :=
  let n := v.toNat
  ([(n &&& 0xFFFF, .LSL0),
    ((n >>> 16) &&& 0xFFFF, .LSL16),
    ((n >>> 32) &&& 0xFFFF, .LSL32),
    ((n >>> 48) &&& 0xFFFF, .LSL48)]).filter fun p => p.1 != 0

/-- Materialize 64-bit constant `c` into `x_d` via `MOVZ`, `MOVN`, 2-insn `MOVZ+MOVK` /
`MOVN+MOVK`, or literal-pool `LDR` fallback (`3..4` non-trivial chunks). -/
def armMovImmI (d : XReg) (c : BitVec 64) : List Instr :=
  if c == 0#64 then [armMovzI d 0 .LSL0]
  else match armNonZeroChunks c with
    | [(k, sh)] => [armMovzI d k sh]
    | _ => match armNonZeroChunks (~~~c) with
      | [(k, sh)] => [armMovnI d k sh]
      | _ => match armNonZeroChunks c with
        | [(k1, sh1), (k2, sh2)] => [armMovzI d k1 sh1, armMovkI d k2 sh2]
        | _ => match armNonZeroChunks (~~~c) with
          | [(k1, sh1), (k2, sh2)] => [armMovnI d k1 sh1, armMovkI d (k2 ^^^ 0xFFFF) sh2]
          | _ => [armIselLdrPoolBvI d c]

/-- Load unsigned `n`-bit operand into `tmp` if immediate, or return its GP `XReg` (`Instr`). -/
def armArgInIns {n : Nat} (tmp : XReg) :
    PArg Reg Empty ArmCond (.bits n) → Option (List Instr × XReg)
  | .gpr (.reg r) => some ([], r)
  | .gpr .SP => none
  | .imm c => some (armMovImmI tmp (c.setWidth 64), tmp)

/-- Load a `.bool` operand into `tmp` if immediate/flag, or return its GP `XReg` (`Instr`). -/
def armBoolArgInIns (tmp : XReg) : PArg Reg Empty ArmCond .bool → Option (List Instr × XReg)
  | .gpr (.reg r) => some ([], r)
  | .gpr .SP => none
  | .imm b => some (armMovImmI tmp (BitVec.ofNat 64 b.toNat), tmp)
  | .flag c => some ([armCset64I tmp c], tmp)

/-- 12-bit unsigned arithmetic immediate (`S0` or `S12`). -/
def armImm12? {n : Nat} (c : BitVec n) : Option ExtOrImmReg :=
  if Nat.blt c.toNat 4096 then
    some (.imm { imm := .int64 (Int64.ofNat c.toNat), shift := .S0 })
  else if Nat.blt c.toNat 16777216 && (c.toNat % 4096 == 0) then
    some (.imm { imm := .int64 (Int64.ofNat (c.toNat / 4096)), shift := .S12 })
  else none

def armIsContiguousOnes (v E : Nat) : Bool :=
  v > 0 && v < ((1 <<< E) - 1) && ((v + 1) &&& v) == 0

def armIsRotatedRunOfOnesAux (elem E : Nat) : Nat → Bool
  | 0 => false
  | n + 1 =>
    if armIsContiguousOnes elem E then true
    else
      let nextElem := (elem >>> 1) ||| ((elem &&& 1) <<< (E - 1))
      armIsRotatedRunOfOnesAux nextElem E n

def armRepeatElement (pattern wBits E : Nat) : Nat :=
  match wBits, E with
  | 64, 64 => pattern
  | 64, 32 => pattern * 0x0000000100000001
  | 64, 16 => pattern * 0x0001000100010001
  | 64, 8  => pattern * 0x0101010101010101
  | 64, 4  => pattern * 0x1111111111111111
  | 64, 2  => pattern * 0x5555555555555555
  | 32, 32 => pattern
  | 32, 16 => pattern * 0x00010001
  | 32, 8  => pattern * 0x01010101
  | 32, 4  => pattern * 0x11111111
  | 32, 2  => pattern * 0x55555555
  | _, _ => 0

/-- True iff `v` encodes a valid ARMv8-A logical bitmask immediate at width `w`. -/
def armIsValidLogicalImm (w : RegWidth) (v : BitVec 64) : Bool :=
  let vNat := match w with
    | .W32 => v.toNat &&& 0xFFFFFFFF
    | .W64 => v.toNat
  let wBits := w.bits
  let maxVal := (1 <<< wBits) - 1
  if vNat == 0 || vNat == maxVal then false
  else
    let sizes := match w with
      | .W32 => [2, 4, 8, 16, 32]
      | .W64 => [2, 4, 8, 16, 32, 64]
    sizes.any fun E =>
      let pat := vNat &&& ((1 <<< E) - 1)
      vNat == armRepeatElement pat wBits E && armIsRotatedRunOfOnesAux pat E E

/-- Logical immediate `n - 1` (`7`, `15`, `31`, or `63`) for shift/bit masks. -/
def armShiftMaskConst (n : Nat) : ConstExpr :=
  .int64 (Int64.ofNat (n - 1))

/-! ## 2. Moves, branches, flag clearing, loads, and stores -/

/-- Flags guaranteed false immediately after `armClearFlags`. -/
def armZeroFlags : List ArmCond := [.cs, .vs]

/-- `adds xzr, xzr, xzr` (`Instr` builder). -/
def armClearFlagsIns : List Instr :=
  [armIselInsI (w := .W64)
    (.ADDS_s (xzr .W64) (xzr .W64) { reg := xzr .W64, amount := 0, shift := .LSL })]

/-- `adds xzr, xzr, xzr`: clears `C` and `V` (and sets `N = 0, Z = 1`) without touching any GPR. -/
def armClearFlags : List Directive :=
  emitClean armClearFlagsIns

/-- `add rd, rs, #0` (`Instr` builder). -/
def armMovIns (rd rs : Reg) : List Instr :=
  [armIselInsI (w := .W64) (.ADD_e (.low rd .W64) (.low rs .W64) imm0)]

/-- `add rd, rs, #0`: valid for all `rd, rs : Reg` including `.SP`, preserving all flags. -/
def armMov (rd rs : Reg) : List Directive :=
  emitClean (armMovIns rd rs)

/-- Load 64-bit constant `c` into `rd` (`Instr` builder). -/
def armMoviIns (rd : Reg) (c : BitVec 64) : List Instr :=
  match rd with
  | .reg d => armMovImmI d c
  | .SP => armMovImmI .X16 c ++ [armIselMovToSpI .X16]

/-- Load 64-bit constant `c` into `rd` (routing `.SP` via `.X16`), preserving all flags. -/
def armMovi (rd : Reg) (c : BitVec 64) : List Directive :=
  emitClean (armMoviIns rd c)

/-- Materialize flag condition `c` into `rd` (`Instr` builder). -/
def armSetccIns (rd : Reg) (c : ArmCond) : List Instr :=
  match rd with
  | .reg d => [armCset64I d c]
  | .SP => [armCset64I .X16 c, armIselMovToSpI .X16]

/-- Materialize flag condition `c` into `rd` (`0/1`, routing `.SP` via `.X16`), preserving flags. -/
def armSetcc (rd : Reg) (c : ArmCond) : List Directive :=
  emitClean (armSetccIns rd c)

/-- Unconditional branch `b l` (`Instr` builder). -/
def armJmpIns (l : Sym) : List Instr :=
  [armIselInsI (w := .W64) (.B (.label l))]

/-- Unconditional branch `b l`. -/
def armJmp (l : Sym) : List Directive :=
  emitClean (armJmpIns l)

/-- Conditional branch `b.<c> l` (`Instr` builder). -/
def armJccIns (c : ArmCond) (l : Sym) : List Instr :=
  [armIselInsI (w := .W64) (.B_cond c.toKraken (.label l))]

/-- Conditional branch `b.<c> l`. -/
def armJcc (c : ArmCond) (l : Sym) : List Directive :=
  emitClean (armJccIns c l)

/-- Test low bit `0` of `.bool` register `r` via `tbnz` (`Instr` builder). -/
def armJnzGprIns (r : Reg) (l : Sym) : List Instr × FlagMask :=
  match r with
  | .reg x => ([armIselInsI (w := .W32) (.TBNZ (zr x .W32) 0 (.label l))], maskNone)
  | .SP =>
    ([armIselMovToXI .X16 .SP, armIselInsI (w := .W32) (.TBNZ (zr .X16 .W32) 0 (.label l))],
      maskNone)

/-- Test low bit `0` of `.bool` register `r` via `tbnz` (routing `.SP` via `.X16`), preserving flags. -/
def armJnzGpr (r : Reg) (l : Sym) : List Directive × FlagMask :=
  let p := armJnzGprIns r l
  (emitClean p.1, p.2)

/-- True iff `disp` fits as a scaled unsigned offset `[xb, #disp]` for access size `scale`. -/
def armFitsScaledOff (scale : Nat) (disp : Int64) : Bool :=
  Nat.ble disp.toBitVec.toNat (4095 * scale) && (disp.toBitVec.toNat % scale == 0)

/-- Compute effective `AddrExpr` using scratch `.X16` only (`Instr` builder). -/
def armSetupAddrIns (scale : Nat) : AddrArg Reg → List Instr × AddrExpr
  | .imm addr => (armMovImmI .X16 addr, atReg .X16)
  | .baseDisp (.reg rb) disp =>
    if disp == 0 then ([], atReg rb)
    else if armFitsScaledOff scale disp then ([], armAtDisp rb disp)
    else (armMovImmI .X16 disp.toBitVec, armAtIdx rb .X16)
  | .baseDisp .SP disp =>
    if disp == 0 then ([armIselMovToXI .X16 .SP], atReg .X16)
    else if Nat.blt disp.toBitVec.toNat 4096 then
      ([armIselInsI (w := .W64) (.ADD_e (.low (.reg .X16) .W64) (.low .SP .W64)
        (.imm { imm := .int64 disp, shift := .S0 }))], atReg .X16)
    else
      (armMovImmI .X16 disp.toBitVec ++
        [armIselInsI (w := .W64) (.ADD_e (.low (.reg .X16) .W64) (.low .SP .W64)
          (.ext { reg := ⟨.W64, zr .X16 .W64⟩, ext := { type := .UXTX, amount := .E0 } }))],
        atReg .X16)
  | .baseIdxDisp (.reg rb) (.reg ri) sc _ =>
    match armMemExtendAmount scale sc with
    | some amt => ([], armAtIdxScale rb ri amt)
    | none => ([], atReg .X16)
  | .baseIdxDisp .. => ([], atReg .X16)

/-- Byte scale of a scalar memory access type, or `none` if unsupported. -/
def armMemScale : Ty → Option Nat
  | .bool | .bits 8 => some 1
  | .bits 16 => some 2
  | .bits 32 => some 4
  | .bits 64 => some 8
  | _ => none

/-- Single load `Instr` from effective address `addr` into `x_d`/`w_d`. -/
def armLoadDirI (t : Ty) (d : XReg) (addr : AddrExpr) : Option Instr :=
  match t with
  | .bool | .bits 8 => some (armIselInsI (.LDRB (zr d .W32) addr))
  | .bits 16 => some (armIselInsI (.LDRH (zr d .W32) addr))
  | .bits 32 => some (armIselInsI (w := .W32) (.LDR (zr d .W32) (.addr addr)))
  | .bits 64 => some (armIselInsI (w := .W64) (.LDR (zr d .W64) (.addr addr)))
  | _ => none

/-- Single store `Instr` from `x_s`/`w_s` to effective address `addr`. -/
def armStoreDirI (t : Ty) (s : XReg) (addr : AddrExpr) : Option Instr :=
  match t with
  | .bool | .bits 8 => some (armIselInsI (.STRB (zr s .W32) addr))
  | .bits 16 => some (armIselInsI (.STRH (zr s .W32) addr))
  | .bits 32 => some (armIselInsI (w := .W32) (.STR (zr s .W32) addr))
  | .bits 64 => some (armIselInsI (w := .W64) (.STR (zr s .W64) addr))
  | _ => none

/-- Address validity gate for AArch64 scalar loads/stores at byte access size `scale`. -/
def armAddrValid (scale : Nat) : AddrArg Reg → Bool
  | .baseIdxDisp (.reg _) (.reg _) sc disp =>
    disp == 0 && (armMemExtendAmount scale sc).isSome
  | .baseIdxDisp .. => false
  | _ => true

/-- Load scalar `t` from `a` into `rd` (`Instr` builder). -/
def armLoadIns (t : Ty) (rd : Reg) (a : AddrArg Reg) : Option (List Instr × FlagMask) := do
  let scale ← armMemScale t
  if !armAddrValid scale a then none
  else
    let (setup, addr) := armSetupAddrIns scale a
    match rd with
    | .reg d =>
      let dir ← armLoadDirI t d addr
      some (setup ++ [dir], maskNone)
    | .SP =>
      let dir ← armLoadDirI t .X16 addr
      some (setup ++ [dir, armIselMovToSpI .X16], maskNone)

/-- Load scalar `t` from `a` into `rd` (handling `.SP` base/destination), preserving all flags. -/
def armLoad (t : Ty) (rd : Reg) (a : AddrArg Reg) : Option (List Directive × FlagMask) :=
  emitCleanPair (armLoadIns t rd a)

/-- Materialize stored operand `pa` into `.X17` (or return its `XReg`) (`Instr` builder). -/
def armStoreValInIns : (t : Ty) → PArg Reg Empty ArmCond t → Option (List Instr × XReg)
  | .bool, .gpr (.reg r) => some ([], r)
  | .bool, .gpr .SP => some ([armIselMovToXI .X17 .SP], .X17)
  | .bool, .imm b => some (armMovImmI .X17 (BitVec.ofNat 64 b.toNat), .X17)
  | .bool, .flag c => some ([armCset64I .X17 c], .X17)
  | .bits _, .gpr (.reg r) => some ([], r)
  | .bits _, .gpr .SP => some ([armIselMovToXI .X17 .SP], .X17)
  | .bits _, .imm c => some (armMovImmI .X17 (c.setWidth 64), .X17)
  | _, _ => none

/-- Store scalar `pa` of type `t` to `a` (`Instr` builder). -/
def armStoreIns (t : Ty) (pa : PArg Reg Empty ArmCond t) (a : AddrArg Reg) :
    Option (List Instr × FlagMask) := do
  let scale ← armMemScale t
  if !armAddrValid scale a then none
  else
    let (valSetup, rx) ← armStoreValInIns t pa
    let (addrSetup, addr) := armSetupAddrIns scale a
    let dir ← armStoreDirI t rx addr
    some (valSetup ++ addrSetup ++ [dir], maskNone)

/-- Store scalar `pa` of type `t` to `a`, preserving all flags. -/
def armStore (t : Ty) (pa : PArg Reg Empty ArmCond t) (a : AddrArg Reg) :
    Option (List Directive × FlagMask) :=
  emitCleanPair (armStoreIns t pa a)

/-! ## 3. Scalar `armOp` helpers (`[8, 16, 32, 64]`, `bswap`, `[32, 64]` bit/carry/mulw/fsh) -/

/-- `ArmCond` corresponding to integer comparison `o` after `cmp a, b` (`SUBS`). -/
def armCmpCond : CmpOp → ArmCond
  | .eq => .eq | .ne => .ne | .ult => .cc | .ule => .ls | .ugt => .hi
  | .uge => .cs | .slt => .lt | .sle => .le | .sgt => .gt | .sge => .ge

def armIsSignedCmp : CmpOp → Bool
  | .slt | .sle | .sgt | .sge => true
  | _ => false

/-- Extend low `n` bits (`8` or `16`) into `.W32` (`UBFM` or `SBFM`) (`Instr`). -/
abbrev armExt32I (signed : Bool) (n : Nat) (d s : XReg) : Instr :=
  if signed then armIselInsI (.SBFM (zr d .W32) (zr s .W32) 0 (n - 1))
  else armIselInsI (.UBFM (zr d .W32) (zr s .W32) 0 (n - 1))

/-- Extend low `n` bits (`8` or `16`) into `.W32` (`UBFM` or `SBFM`). -/
abbrev armExt32 (signed : Bool) (n : Nat) (d s : XReg) : Directive :=
  .instr (armExt32I signed n d s)

/-- Emit boolean `copy`, `and`, `or`, `xor`, or `not` into GP register `d` (`Instr` builder). -/
def armBoolOpIns {sig : List Ty} (code : OpCode sig [.bool])
    (pas : Tup (PArg Reg Empty ArmCond) sig) (d : XReg) : Option (List Instr × FlagMask) :=
  match code, pas with
  | .copy .bool, (.gpr (.reg r), ()) =>
    some ([armIselInsI (.ORR_s (zr d .W32) (xzr .W32) (sh r))], maskNone)
  | .copy .bool, (.imm b, ()) =>
    some (armMovImmI d (BitVec.ofNat 64 b.toNat), maskNone)
  | .copy .bool, (.flag c, ()) => some ([armCset64I d c], maskNone)
  | .not .bool, (pa, ()) => do
    let (ca, ra) ← armBoolArgInIns .X16 pa
    some (ca ++ [armIselInsI (.EOR_i (.low (.reg d) .W32) (zr ra .W32) (.int64 1))], maskNone)
  | .and .bool, (pa, pb, ()) => do
    let (ca, ra) ← armBoolArgInIns .X16 pa
    let (cb, rb) ← armBoolArgInIns .X17 pb
    some (ca ++ cb ++ [armIselInsI (.AND_s (zr d .W32) (zr ra .W32) (sh rb))], maskNone)
  | .or .bool, (pa, pb, ()) => do
    let (ca, ra) ← armBoolArgInIns .X16 pa
    let (cb, rb) ← armBoolArgInIns .X17 pb
    some (ca ++ cb ++ [armIselInsI (.ORR_s (zr d .W32) (zr ra .W32) (sh rb))], maskNone)
  | .xor .bool, (pa, pb, ()) => do
    let (ca, ra) ← armBoolArgInIns .X16 pa
    let (cb, rb) ← armBoolArgInIns .X17 pb
    some (ca ++ cb ++ [armIselInsI (.EOR_s (zr d .W32) (zr ra .W32) (sh rb))], maskNone)
  | _, _ => none

/-- Copy `n`-bit value (`n ∈ {8, 16, 32, 64}`) from `pa` into GP register `d` (`Instr` builder). -/
def armCopyBitsIns (n : Nat) (pa : PArg Reg Empty ArmCond (.bits n)) (d : XReg) :
    Option (List Instr × FlagMask) :=
  let w := armWidthOf n
  match pa with
  | .gpr (.reg r) => some ([armIselInsI (.ORR_s (zr d w) (xzr w) (sh r))], maskNone)
  | .gpr .SP => none
  | .imm c => some (armMovImmI d (c.setWidth 64), maskNone)

/-- Zero-extension `zext m n` (`Instr` builder). -/
def armZextOpIns (m n : Nat) (pa : PArg Reg Empty ArmCond (.bits m)) (d : XReg) :
    Option (List Instr × FlagMask) :=
  if !([8, 16, 32, 64].contains m && [8, 16, 32, 64].contains n && Nat.ble m n) then none
  else match pa with
    | .imm c => some (armMovImmI d ((c.setWidth n).setWidth 64), maskNone)
    | .gpr .SP => none
    | .gpr (.reg r) =>
      if m == 8 then some ([armIselInsI (.UBFM (zr d .W64) (zr r .W64) 0 7)], maskNone)
      else if m == 16 then some ([armIselInsI (.UBFM (zr d .W64) (zr r .W64) 0 15)], maskNone)
      else if m == 32 then some ([armIselInsI (.ORR_s (zr d .W32) (xzr .W32) (sh r))], maskNone)
      else some ([armIselInsI (.ORR_s (zr d .W64) (xzr .W64) (sh r))], maskNone)

/-- Sign-extension `sext m n` (`Instr` builder). -/
def armSextOpIns (m n : Nat) (pa : PArg Reg Empty ArmCond (.bits m)) (d : XReg) :
    Option (List Instr × FlagMask) :=
  if !([8, 16, 32, 64].contains m && [8, 16, 32, 64].contains n && Nat.ble m n) then none
  else match pa with
    | .imm c => some (armMovImmI d ((c.signExtend n).setWidth 64), maskNone)
    | .gpr .SP => none
    | .gpr (.reg r) =>
      let w := armWidthOf n
      if m == 8 then some ([armIselInsI (.SBFM (zr d w) (zr r w) 0 7)], maskNone)
      else if m == 16 then some ([armIselInsI (.SBFM (zr d w) (zr r w) 0 15)], maskNone)
      else if m == 32 then some ([armIselInsI (.SBFM (zr d w) (zr r w) 0 31)], maskNone)
      else some ([armIselInsI (.ORR_s (zr d .W64) (xzr .W64) (sh r))], maskNone)

/-- Truncation `trunc m n` (`Instr` builder). -/
def armTruncOpIns (m n : Nat) (pa : PArg Reg Empty ArmCond (.bits m)) (d : XReg) :
    Option (List Instr × FlagMask) :=
  if !([8, 16, 32, 64].contains m && [8, 16, 32, 64].contains n && Nat.ble n m) then none
  else match pa with
    | .imm c => some (armMovImmI d ((c.setWidth n).setWidth 64), maskNone)
    | .gpr .SP => none
    | .gpr (.reg r) =>
      let w := armWidthOf n
      some ([armIselInsI (.ORR_s (zr d w) (xzr w) (sh r))], maskNone)

/-- Materialize `.bool` operand as `0/1` in `n`-bit register `d` (`Instr` builder). -/
def armOfBoolOpIns (n : Nat) (pa : PArg Reg Empty ArmCond .bool) (d : XReg) :
    Option (List Instr × FlagMask) :=
  if ![8, 16, 32, 64].contains n then none
  else match pa with
    | .gpr (.reg r) => some ([armIselInsI (.UBFM (zr d .W64) (zr r .W64) 0 7)], maskNone)
    | .gpr .SP => none
    | .imm b => some (armMovImmI d (BitVec.ofNat 64 b.toNat), maskNone)
    | .flag c => some ([armCset64I d c], maskNone)

/-- Wrapping binary ALU operations (`add`, `sub`, `mul`, `and`, `or`, `xor`) at `[8, 16, 32, 64]`. -/
inductive ArmBinK | add | sub | mul | and | or | xor

abbrev armBinDirI (k : ArmBinK) (w : RegWidth) (d ra rb : XReg) : Instr :=
  match k with
  | .add => armIselInsI (.ADD_s (zr d w) (zr ra w) (sh rb))
  | .sub => armIselInsI (.SUB_s (zr d w) (zr ra w) (sh rb))
  | .mul => armIselInsI (.MADD (zr d w) (zr ra w) (zr rb w) (xzr w))
  | .and => armIselInsI (.AND_s (zr d w) (zr ra w) (sh rb))
  | .or => armIselInsI (.ORR_s (zr d w) (zr ra w) (sh rb))
  | .xor => armIselInsI (.EOR_s (zr d w) (zr ra w) (sh rb))

abbrev armBinDir (k : ArmBinK) (w : RegWidth) (d ra rb : XReg) : Directive :=
  .instr (armBinDirI k w d ra rb)

abbrev armLogicImmDirI (k : ArmBinK) (w : RegWidth) (d ra : XReg) (imm : Int64) : Option Instr :=
  match k with
  | .and => some (armIselInsI (.AND_i (.low (.reg d) w) (zr ra w) (.int64 imm)))
  | .or => some (armIselInsI (.ORR_i (.low (.reg d) w) (zr ra w) (.int64 imm)))
  | .xor => some (armIselInsI (.EOR_i (.low (.reg d) w) (zr ra w) (.int64 imm)))
  | _ => none

def armBinOpIns (k : ArmBinK) (n : Nat) (pa pb : PArg Reg Empty ArmCond (.bits n)) (d : XReg) :
    Option (List Instr × FlagMask) := do
  if ![8, 16, 32, 64].contains n then none
  else
    let w := armWidthOf n
    match k, pa, pb with
    | .add, .gpr (.reg ra), .imm cb =>
      match armImm12? cb with
      | some ei => some ([armIselInsI (.ADD_e (.low (.reg d) w) (.low (.reg ra) w) ei)], maskNone)
      | none =>
        let (cb', rb) ← armArgInIns .X17 pb
        some (cb' ++ [armBinDirI k w d ra rb], maskNone)
    | .add, .imm ca, .gpr (.reg rb) =>
      match armImm12? ca with
      | some ei => some ([armIselInsI (.ADD_e (.low (.reg d) w) (.low (.reg rb) w) ei)], maskNone)
      | none =>
        let (ca', ra) ← armArgInIns .X16 pa
        some (ca' ++ [armBinDirI k w d ra rb], maskNone)
    | .sub, .gpr (.reg ra), .imm cb =>
      match armImm12? cb with
      | some ei => some ([armIselInsI (.SUB_e (.low (.reg d) w) (.low (.reg ra) w) ei)], maskNone)
      | none =>
        let (cb', rb) ← armArgInIns .X17 pb
        some (cb' ++ [armBinDirI k w d ra rb], maskNone)
    | .and, .gpr (.reg ra), .imm cb
    | .or, .gpr (.reg ra), .imm cb
    | .xor, .gpr (.reg ra), .imm cb =>
      let c64 := cb.setWidth 64
      if armIsValidLogicalImm w c64 then
        let dir ← armLogicImmDirI k w d ra (Int64.ofBitVec c64)
        some ([dir], maskNone)
      else
        let (cb', rb) ← armArgInIns .X17 pb
        some (cb' ++ [armBinDirI k w d ra rb], maskNone)
    | .and, .imm ca, .gpr (.reg rb)
    | .or, .imm ca, .gpr (.reg rb)
    | .xor, .imm ca, .gpr (.reg rb) =>
      let c64 := ca.setWidth 64
      if armIsValidLogicalImm w c64 then
        let dir ← armLogicImmDirI k w d rb (Int64.ofBitVec c64)
        some ([dir], maskNone)
      else
        let (ca', ra) ← armArgInIns .X16 pa
        some (ca' ++ [armBinDirI k w d ra rb], maskNone)
    | _, _, _ =>
      let (ca, ra) ← armArgInIns .X16 pa
      let (cb, rb) ← armArgInIns .X17 pb
      some (ca ++ cb ++ [armBinDirI k w d ra rb], maskNone)

/-- Shifts (`shl`, `lshr`, `ashr`) at `[8, 16, 32, 64]`. -/
inductive ArmShiftK | shl | lshr | ashr

def armShiftOpIns (k : ArmShiftK) (n : Nat) (pa pb : PArg Reg Empty ArmCond (.bits n))
    (d : XReg) : Option (List Instr × FlagMask) := do
  if ![8, 16, 32, 64].contains n then none
  else if n == 32 || n == 64 then
    let w := armWidthOf n
    match pa, pb with
    | .gpr (.reg ra), .imm cb =>
      let amt := cb.toNat % n
      let dir := match k with
        | .shl =>
          armIselInsI (.UBFM (zr d w) (zr ra w) ((w.bits - amt) % w.bits) (w.bits - 1 - amt))
        | .lshr => armIselInsI (.UBFM (zr d w) (zr ra w) amt (w.bits - 1))
        | .ashr => armIselInsI (.SBFM (zr d w) (zr ra w) amt (w.bits - 1))
      some ([dir], maskNone)
    | _, _ =>
      let (ca, ra) ← armArgInIns .X16 pa
      let (cb, rb) ← armArgInIns .X17 pb
      let dir := match k with
        | .shl => armIselInsI (.LSLV (zr d w) (zr ra w) (zr rb w))
        | .lshr => armIselInsI (.LSRV (zr d w) (zr ra w) (zr rb w))
        | .ashr => armIselInsI (.ASRV (zr d w) (zr ra w) (zr rb w))
      some (ca ++ cb ++ [dir], maskNone)
  else
    let (ca, ra) ← armArgInIns .X16 pa
    let (cb, rb) ← armArgInIns .X17 pb
    let prepA : List Instr := match k with
      | .shl => []
      | .lshr => [armExt32I false n .X16 ra]
      | .ashr => [armExt32I true n .X16 ra]
    let ra' : XReg := match k with | .shl => ra | .lshr | .ashr => .X16
    let prepB : List Instr :=
      [armIselInsI (.AND_i (.low (.reg .X17) .W32) (zr rb .W32) (armShiftMaskConst n))]
    let dir := match k with
      | .shl => armIselInsI (.LSLV (zr d .W32) (zr ra' .W32) (zr .X17 .W32))
      | .lshr => armIselInsI (.LSRV (zr d .W32) (zr ra' .W32) (zr .X17 .W32))
      | .ashr => armIselInsI (.ASRV (zr d .W32) (zr ra' .W32) (zr .X17 .W32))
    some (ca ++ cb ++ prepA ++ prepB ++ [dir], maskNone)

/-- Rotates (`rotl`, `rotr`) at `[8, 16, 32, 64]` (`Instr` builder). -/
def armRotOpIns (isLeft : Bool) (n : Nat) (pa pb : PArg Reg Empty ArmCond (.bits n))
    (d : XReg) : Option (List Instr × FlagMask) := do
  if ![8, 16, 32, 64].contains n then none
  else if n == 32 || n == 64 then
    let w := armWidthOf n
    match pa, pb with
    | .gpr (.reg ra), .imm cb =>
      let k := if isLeft then (n - cb.toNat % n) % n else cb.toNat % n
      some ([armIselInsI (.EXTR (zr d w) (zr ra w) (zr ra w) k)], maskNone)
    | _, _ =>
      let (ca, ra) ← armArgInIns .X16 pa
      let (cb, rb) ← armArgInIns .X17 pb
      if isLeft then
        some (ca ++ cb ++
          [armIselInsI (.SUB_s (zr .X17 w) (xzr w) (sh rb)),
           armIselInsI (.RORV (zr d w) (zr ra w) (zr .X17 w))], maskNone)
      else
        some (ca ++ cb ++ [armIselInsI (.RORV (zr d w) (zr ra w) (zr rb w))], maskNone)
  else
    let (ca, ra) ← armArgInIns .X16 pa
    let (cb, rb) ← armArgInIns .X17 pb
    let repA : List Instr :=
      [armExt32I false n .X16 ra,
       armIselInsI (.ORR_s (zr .X16 .W32) (zr .X16 .W32)
         { reg := zr .X16 .W32, amount := Int64.ofNat n, shift := .LSL })]
    let cntB : List Instr :=
      if isLeft then
        [armIselInsI (.SUB_s (zr .X17 .W32) (xzr .W32) (sh rb)),
         armIselInsI (.AND_i (.low (.reg .X17) .W32) (zr .X17 .W32) (armShiftMaskConst n))]
      else
        [armIselInsI (.AND_i (.low (.reg .X17) .W32) (zr rb .W32) (armShiftMaskConst n))]
    some (ca ++ cb ++ repA ++ cntB ++
      [armIselInsI (.LSRV (zr d .W32) (zr .X16 .W32) (zr .X17 .W32))], maskNone)

/-- Division/remainder (`udiv`, `sdiv`, `urem`, `srem`, `udiv0`, `sdiv0`) at `[8, 16, 32, 64]`. -/
inductive ArmDivK | udiv | sdiv | urem | srem

def armDivRemOpIns (k : ArmDivK) (n : Nat) (pa pb : PArg Reg Empty ArmCond (.bits n))
    (d : XReg) : Option (List Instr × FlagMask) := do
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
        some (armMovImmI d (res.setWidth 64), maskNone)
      | _, _ =>
        let (ca, ra) ← armArgInIns .X16 pa
        let (cb, rb) ← armArgInIns .X17 pb
        if isRem then
          let t : XReg := match pb with | .gpr _ => .X17 | .imm _ => .X16
          let divD := if isSigned then armIselInsI (.SDIV (zr t w) (zr ra w) (zr rb w))
                      else armIselInsI (.UDIV (zr t w) (zr ra w) (zr rb w))
          some (ca ++ cb ++ [divD, armIselInsI (.MSUB (zr d w) (zr t w) (zr rb w) (zr ra w))],
            maskNone)
        else
          let divD := if isSigned then armIselInsI (.SDIV (zr d w) (zr ra w) (zr rb w))
                      else armIselInsI (.UDIV (zr d w) (zr ra w) (zr rb w))
          some (ca ++ cb ++ [divD], maskNone)
    else
      let (ca, ra) ← armArgInIns .X16 pa
      let (cb, rb) ← armArgInIns .X17 pb
      let prep := [armExt32I isSigned n .X16 ra, armExt32I isSigned n .X17 rb]
      let divD := if isSigned then armIselInsI (.SDIV (zr d .W32) (zr .X16 .W32) (zr .X17 .W32))
                  else armIselInsI (.UDIV (zr d .W32) (zr .X16 .W32) (zr .X17 .W32))
      if isRem then
        some (ca ++ cb ++ prep ++
          [divD, armIselInsI (.MSUB (zr d .W32) (zr d .W32) (zr .X17 .W32) (zr .X16 .W32))],
          maskNone)
      else
        some (ca ++ cb ++ prep ++ [divD], maskNone)

/-- Integer comparisons `cmp o (.bits n)` targeting `.flag c` or `.gpr d` (`Instr` builder). -/
def armCmpOpIns (o : CmpOp) (n : Nat) (pa pb : PArg Reg Empty ArmCond (.bits n))
    (dst : PDst Reg Empty ArmCond .bool) : Option (List Instr × FlagMask) := do
  if ![8, 16, 32, 64].contains n then none
  else
    let finish (cmpCode : List Instr) (cond : ArmCond) : Option (List Instr × FlagMask) :=
      match dst with
      | .flag c => if c == cond then some (cmpCode, maskNZCV) else none
      | .gpr (.reg d) => some (cmpCode ++ [armCset64I d cond], maskNZCV)
      | .gpr .SP | .vec _ => none
    if n == 32 || n == 64 then
      let w := armWidthOf n
      match pa, pb with
      | .gpr (.reg ra), .imm cb =>
        match armImm12? cb with
        | some ei => finish [armIselInsI (.SUBS_e (xzr w) (.low (.reg ra) w) ei)] (armCmpCond o)
        | none =>
          let (cb', rb) ← armArgInIns .X17 pb
          finish (cb' ++ [armIselInsI (.SUBS_s (xzr w) (zr ra w) (sh rb))]) (armCmpCond o)
      | .imm ca, .gpr (.reg rb) =>
        match armImm12? ca with
        | some ei =>
          finish [armIselInsI (.SUBS_e (xzr w) (.low (.reg rb) w) ei)] (armCmpCond o.swap)
        | none =>
          let (ca', ra) ← armArgInIns .X16 pa
          finish (ca' ++ [armIselInsI (.SUBS_s (xzr w) (zr ra w) (sh rb))]) (armCmpCond o)
      | _, _ =>
        let (ca, ra) ← armArgInIns .X16 pa
        let (cb, rb) ← armArgInIns .X17 pb
        finish (ca ++ cb ++ [armIselInsI (.SUBS_s (xzr w) (zr ra w) (sh rb))]) (armCmpCond o)
    else
      let sgn := armIsSignedCmp o
      let (ca, ra) ← armArgInIns .X16 pa
      let (cb, rb) ← armArgInIns .X17 pb
      finish (ca ++ cb ++ [armExt32I sgn n .X16 ra, armExt32I sgn n .X17 rb,
        armIselInsI (.SUBS_s (xzr .W32) (zr .X16 .W32) (sh .X17))]) (armCmpCond o)

/-- Branchless `CSEL` conditional select at `[8, 16, 32, 64]` (`Instr` builder). -/
def armSelectOpIns (n : Nat) (pc : PArg Reg Empty ArmCond .bool)
    (pa pb : PArg Reg Empty ArmCond (.bits n)) (d : XReg) :
    Option (List Instr × FlagMask) := do
  if ![8, 16, 32, 64].contains n then none
  else
    let w := armWidthOf n
    match pc with
    | .imm true => armCopyBitsIns n pa d
    | .imm false => armCopyBitsIns n pb d
    | .flag cond =>
      let (ca, ra) ← armArgInIns .X16 pa
      let (cb, rb) ← armArgInIns .X17 pb
      some (ca ++ cb ++ [armIselInsI (.CSEL (zr d w) (zr ra w) (zr rb w) cond.toKraken)], maskNone)
    | .gpr (.reg rc) =>
      let (ca, ra) ← armArgInIns .X16 pa
      let (cb, rb) ← armArgInIns .X17 pb
      some (ca ++ cb ++
        [armIselInsI (.ANDS_i (xzr .W32) (zr rc .W32) (.int64 1)),
         armIselInsI (.CSEL (zr d w) (zr ra w) (zr rb w) .NE)], maskNZCV)
    | .gpr .SP => none

/-- Carry addition `addc n` at `[32, 64]` (`Instr` builder). -/
def armAddcOpIns (n : Nat) (pa pb : PArg Reg Empty ArmCond (.bits n))
    (cin : PArg Reg Empty ArmCond .bool) (d : XReg) (cout : PDst Reg Empty ArmCond .bool)
    (vh : VariantHint) : Option (List Instr × FlagMask) := do
  if !(n == 32 || n == 64) || vh != .default then none
  else
    let w := armWidthOf n
    let post : Option (List Instr) := match cout with
      | .flag .cs => some []
      | .gpr (.reg dc) => if dc == d then none else some [armCset64I dc .cs]
      | _ => none
    let p ← post
    let (ca, ra) ← armArgInIns .X16 pa
    let (cb, rb) ← armArgInIns .X17 pb
    let main : Option (List Instr) := match cin with
      | .flag .cs => some (ca ++ cb ++ [armIselInsI (.ADCS (zr d w) (zr ra w) (zr rb w))])
      | .imm false => some (ca ++ cb ++ [armIselInsI (.ADDS_s (zr d w) (zr ra w) (sh rb))])
      | .imm true =>
        some ([armIselInsI (.SUBS_s (xzr .W32) (xzr .W32)
                { reg := xzr .W32, amount := 0, shift := .LSL })] ++
          ca ++ cb ++ [armIselInsI (.ADCS (zr d w) (zr ra w) (zr rb w))])
      | .gpr (.reg rc) =>
        some ([armIselInsI (.AND_i (.low (.reg .X16) .W32) (zr rc .W32) (.int64 1)),
               armIselInsI (.SUBS_e (xzr .W32) (.low (.reg .X16) .W32)
                 (.imm { imm := .int64 1, shift := .S0 }))] ++
          ca ++ cb ++ [armIselInsI (.ADCS (zr d w) (zr ra w) (zr rb w))])
      | _ => none
    let m ← main
    some (m ++ p, maskNZCV)

/-- Borrow subtraction `subb n` at `[32, 64]` (`Instr` builder). -/
def armSubbOpIns (n : Nat) (pa pb : PArg Reg Empty ArmCond (.bits n))
    (bin : PArg Reg Empty ArmCond .bool) (d : XReg) (bout : PDst Reg Empty ArmCond .bool)
    (vh : VariantHint) : Option (List Instr × FlagMask) := do
  if !(n == 32 || n == 64) || vh != .default then none
  else
    let w := armWidthOf n
    let post : Option (List Instr) := match bout with
      | .flag .cc => some []
      | .gpr (.reg dc) => if dc == d then none else some [armCset64I dc .cc]
      | _ => none
    let p ← post
    let (ca, ra) ← armArgInIns .X16 pa
    let (cb, rb) ← armArgInIns .X17 pb
    let main : Option (List Instr) := match bin with
      | .flag .cc => some (ca ++ cb ++ [armIselInsI (.SBCS (zr d w) (zr ra w) (zr rb w))])
      | .imm false => some (ca ++ cb ++ [armIselInsI (.SUBS_s (zr d w) (zr ra w) (sh rb))])
      | .imm true =>
        some ([armIselInsI (.ADDS_s (xzr .W32) (xzr .W32)
                { reg := xzr .W32, amount := 0, shift := .LSL })] ++
          ca ++ cb ++ [armIselInsI (.SBCS (zr d w) (zr ra w) (zr rb w))])
      | .gpr (.reg rc) =>
        some ([armIselInsI (.AND_i (.low (.reg .X16) .W32) (zr rc .W32) (.int64 1)),
               armIselInsI (.SUBS_s (xzr .W32) (xzr .W32) (sh .X16))] ++
          ca ++ cb ++ [armIselInsI (.SBCS (zr d w) (zr ra w) (zr rb w))])
      | _ => none
    let m ← main
    some (m ++ p, maskNZCV)

/-- Full double-width multiplication `umulw` / `smulw` at `[32, 64]` (`Instr` builder). -/
def armMulwOpIns (isSigned : Bool) (n : Nat) (pa pb : PArg Reg Empty ArmCond (.bits n))
    (dlo dhi : XReg) : Option (List Instr × FlagMask) := do
  if !(n == 32 || n == 64) || dlo == dhi then none
  else
    let (ca, ra) ← armArgInIns .X16 pa
    let (cb, rb) ← armArgInIns .X17 pb
    if n == 32 then
      let mul64 :=
        if isSigned then armIselInsI (.SMADDL (zr dlo .W64) (zr ra .W32) (zr rb .W32) (xzr .W64))
        else armIselInsI (.UMADDL (zr dlo .W64) (zr ra .W32) (zr rb .W32) (xzr .W64))
      some (ca ++ cb ++ [mul64, armIselInsI (.UBFM (zr dhi .W64) (zr dlo .W64) 32 63)], maskNone)
    else
      let mulH (dst : XReg) :=
        if isSigned then armIselInsI (.SMULH (zr dst .W64) (zr ra .W64) (zr rb .W64))
        else armIselInsI (.UMULH (zr dst .W64) (zr ra .W64) (zr rb .W64))
      let mulL := armIselInsI (.MADD (zr dlo .W64) (zr ra .W64) (zr rb .W64) (xzr .W64))
      if dhi != ra && dhi != rb then
        some (ca ++ cb ++ [mulH dhi, mulL], maskNone)
      else if dlo != ra && dlo != rb then
        some (ca ++ cb ++ [mulL, mulH dhi], maskNone)
      else
        some (ca ++ cb ++
          [mulH .X16, mulL, armIselInsI (.ORR_s (zr dhi .W64) (xzr .W64) (sh .X16))],
          maskNone)

/-- Funnel shifts `fshl` / `fshr` at `[32, 64]` (`Instr` builder). -/
def armFunnelOpIns (isLeft : Bool) (n : Nat) (pa pb pc : PArg Reg Empty ArmCond (.bits n))
    (d : XReg) : Option (List Instr × FlagMask) := do
  if !(n == 32 || n == 64) then none
  else
    let w := armWidthOf n
    let (ca, ra) ← armArgInIns .X16 pa
    let (cb, rb) ← armArgInIns .X17 pb
    match pc with
    | .imm cc =>
      let k := cc.toNat % n
      if isLeft then
        if k == 0 then
          some (ca ++ [armIselInsI (.ORR_s (zr d w) (xzr w) (sh ra))], maskNone)
        else
          some (ca ++ cb ++ [armIselInsI (.EXTR (zr d w) (zr ra w) (zr rb w) (n - k))], maskNone)
      else
        some (ca ++ cb ++ [armIselInsI (.EXTR (zr d w) (zr ra w) (zr rb w) k)], maskNone)
    | .gpr (.reg rc) =>
      let tst := armIselInsI (.ANDS_i (xzr w) (zr rc w) (armShiftMaskConst n))
      let body : List Instr := match pa, pb with
        | .imm _, .imm _ =>
          if isLeft then
            [tst,
             armIselInsI (.LSLV (zr .X16 w) (zr .X16 w) (zr rc w)),
             armIselInsI (.SUB_s (zr d w) (xzr w) (sh rc)),
             armIselInsI (.LSRV (zr .X17 w) (zr .X17 w) (zr d w)),
             armIselInsI (.ORR_s (zr d w) (zr .X16 w) (sh .X17)),
             armIselInsI (.CSEL (zr d w) (zr .X16 w) (zr d w) .EQ)]
          else
            [tst,
             armIselInsI (.LSRV (zr .X17 w) (zr .X17 w) (zr rc w)),
             armIselInsI (.SUB_s (zr d w) (xzr w) (sh rc)),
             armIselInsI (.LSLV (zr .X16 w) (zr .X16 w) (zr d w)),
             armIselInsI (.ORR_s (zr d w) (zr .X17 w) (sh .X16)),
             armIselInsI (.CSEL (zr d w) (zr .X17 w) (zr d w) .EQ)]
        | _, .gpr _ =>
          if isLeft then
            [tst,
             armIselInsI (.SUB_s (zr .X17 w) (xzr w) (sh rc)),
             armIselInsI (.LSRV (zr .X17 w) (zr rb w) (zr .X17 w)),
             armIselInsI (.LSLV (zr .X16 w) (zr ra w) (zr rc w)),
             armIselInsI (.ORR_s (zr .X17 w) (zr .X16 w) (sh .X17)),
             armIselInsI (.CSEL (zr d w) (zr .X16 w) (zr .X17 w) .EQ)]
          else
            [tst,
             armIselInsI (.SUB_s (zr .X17 w) (xzr w) (sh rc)),
             armIselInsI (.LSLV (zr .X17 w) (zr ra w) (zr .X17 w)),
             armIselInsI (.LSRV (zr .X16 w) (zr rb w) (zr rc w)),
             armIselInsI (.ORR_s (zr .X17 w) (zr .X16 w) (sh .X17)),
             armIselInsI (.CSEL (zr d w) (zr .X16 w) (zr .X17 w) .EQ)]
        | _, .imm _ =>
          if isLeft then
            [tst,
             armIselInsI (.SUB_s (zr .X16 w) (xzr w) (sh rc)),
             armIselInsI (.LSRV (zr .X17 w) (zr .X17 w) (zr .X16 w)),
             armIselInsI (.LSLV (zr .X16 w) (zr ra w) (zr rc w)),
             armIselInsI (.ORR_s (zr .X17 w) (zr .X16 w) (sh .X17)),
             armIselInsI (.CSEL (zr d w) (zr .X16 w) (zr .X17 w) .EQ)]
          else
            [tst,
             armIselInsI (.SUB_s (zr .X16 w) (xzr w) (sh rc)),
             armIselInsI (.LSLV (zr .X16 w) (zr ra w) (zr .X16 w)),
             armIselInsI (.LSRV (zr .X17 w) (zr .X17 w) (zr rc w)),
             armIselInsI (.ORR_s (zr .X16 w) (zr .X17 w) (sh .X16)),
             armIselInsI (.CSEL (zr d w) (zr .X17 w) (zr .X16 w) .EQ)]
      some (ca ++ cb ++ body, maskNZCV)
    | .gpr .SP => none

/-- Scalar `OpCode` lowering for AArch64 (`Instr` builder). -/
def armOpIns {sig rs : List Ty} (code : OpCode sig rs) (pas : Tup (PArg Reg Empty ArmCond) sig)
    (dsts : Tup (PDst Reg Empty ArmCond) rs) (vh : VariantHint) : Option (List Instr × FlagMask) :=
  match sig, rs, code, pas, dsts with
  | _, _, .copy .bool, (pa, ()), (.gpr (.reg d), ()) => armBoolOpIns (.copy .bool) (pa, ()) d
  | _, _, .and .bool, (pa, pb, ()), (.gpr (.reg d), ()) =>
    armBoolOpIns (.and .bool) (pa, pb, ()) d
  | _, _, .or .bool, (pa, pb, ()), (.gpr (.reg d), ()) =>
    armBoolOpIns (.or .bool) (pa, pb, ()) d
  | _, _, .xor .bool, (pa, pb, ()), (.gpr (.reg d), ()) =>
    armBoolOpIns (.xor .bool) (pa, pb, ()) d
  | _, _, .not .bool, (pa, ()), (.gpr (.reg d), ()) => armBoolOpIns (.not .bool) (pa, ()) d
  | _, _, .copy (.bits n), (pa, ()), (.gpr (.reg d), ()) =>
    if [8, 16, 32, 64].contains n then armCopyBitsIns n pa d else none
  | _, _, .bitcast (.bits m) (.bits n) _, (pa, ()), (.gpr (.reg d), ()) =>
    if [8, 16, 32, 64].contains m && [8, 16, 32, 64].contains n then
      armCopyBitsIns m pa d
    else none
  | _, _, .zext m n, (pa, ()), (.gpr (.reg d), ()) => armZextOpIns m n pa d
  | _, _, .sext m n, (pa, ()), (.gpr (.reg d), ()) => armSextOpIns m n pa d
  | _, _, .trunc m n, (pa, ()), (.gpr (.reg d), ()) => armTruncOpIns m n pa d
  | _, _, .ofBool n, (pa, ()), (.gpr (.reg d), ()) => armOfBoolOpIns n pa d
  | _, _, .add (.bits n), (pa, pb, ()), (.gpr (.reg d), ()) => armBinOpIns .add n pa pb d
  | _, _, .sub (.bits n), (pa, pb, ()), (.gpr (.reg d), ()) => armBinOpIns .sub n pa pb d
  | _, _, .mul (.bits n), (pa, pb, ()), (.gpr (.reg d), ()) => armBinOpIns .mul n pa pb d
  | _, _, .and (.bits n), (pa, pb, ()), (.gpr (.reg d), ()) => armBinOpIns .and n pa pb d
  | _, _, .or (.bits n), (pa, pb, ()), (.gpr (.reg d), ()) => armBinOpIns .or n pa pb d
  | _, _, .xor (.bits n), (pa, pb, ()), (.gpr (.reg d), ()) => armBinOpIns .xor n pa pb d
  | _, _, .neg (.bits n), (pa, ()), (.gpr (.reg d), ()) =>
    if ![8, 16, 32, 64].contains n then none
    else match pa with
      | .imm c => some (armMovImmI d ((-c).setWidth 64), maskNone)
      | .gpr (.reg r) =>
        let w := armWidthOf n
        some ([armIselInsI (.SUB_s (zr d w) (xzr w) (sh r))], maskNone)
      | .gpr .SP => none
  | _, _, .not (.bits n), (pa, ()), (.gpr (.reg d), ()) =>
    if ![8, 16, 32, 64].contains n then none
    else match pa with
      | .imm c => some (armMovImmI d ((~~~c).setWidth 64), maskNone)
      | .gpr (.reg r) =>
        let w := armWidthOf n
        some ([armIselInsI (.ORN_s (zr d w) (xzr w) (sh r))], maskNone)
      | .gpr .SP => none
  | _, _, .shl (.bits n), (pa, pb, ()), (.gpr (.reg d), ()) => armShiftOpIns .shl n pa pb d
  | _, _, .lshr (.bits n), (pa, pb, ()), (.gpr (.reg d), ()) => armShiftOpIns .lshr n pa pb d
  | _, _, .ashr (.bits n), (pa, pb, ()), (.gpr (.reg d), ()) => armShiftOpIns .ashr n pa pb d
  | _, _, .rotl (.bits n), (pa, pb, ()), (.gpr (.reg d), ()) => armRotOpIns true n pa pb d
  | _, _, .rotr (.bits n), (pa, pb, ()), (.gpr (.reg d), ()) => armRotOpIns false n pa pb d
  | _, _, .udiv n, (pa, pb, ()), (.gpr (.reg d), ()) => armDivRemOpIns .udiv n pa pb d
  | _, _, .udiv0 n, (pa, pb, ()), (.gpr (.reg d), ()) => armDivRemOpIns .udiv n pa pb d
  | _, _, .sdiv n, (pa, pb, ()), (.gpr (.reg d), ()) => armDivRemOpIns .sdiv n pa pb d
  | _, _, .sdiv0 n, (pa, pb, ()), (.gpr (.reg d), ()) => armDivRemOpIns .sdiv n pa pb d
  | _, _, .urem n, (pa, pb, ()), (.gpr (.reg d), ()) => armDivRemOpIns .urem n pa pb d
  | _, _, .srem n, (pa, pb, ()), (.gpr (.reg d), ()) => armDivRemOpIns .srem n pa pb d
  | _, _, .bswap (.bits n), (pa, ()), (.gpr (.reg d), ()) => do
    if ![16, 32, 64].contains n then none
    else
      let (ca, ra) ← armArgInIns .X16 pa
      let dir := if n == 16 then armIselInsI (.REV16 (zr d .W32) (zr ra .W32))
                 else if n == 32 then armIselInsI (.REV (zr d .W32) (zr ra .W32))
                 else armIselInsI (.REV (zr d .W64) (zr ra .W64))
      some (ca ++ [dir], maskNone)
  | _, _, .clz n, (pa, ()), (.gpr (.reg d), ()) => do
    if !(n == 32 || n == 64) then none
    else
      let (ca, ra) ← armArgInIns .X16 pa
      let w := armWidthOf n
      some (ca ++ [armIselInsI (.CLZ (zr d w) (zr ra w))], maskNone)
  | _, _, .cls n, (pa, ()), (.gpr (.reg d), ()) => do
    if !(n == 32 || n == 64) then none
    else
      let (ca, ra) ← armArgInIns .X16 pa
      let w := armWidthOf n
      some (ca ++ [armIselInsI (.CLS (zr d w) (zr ra w))], maskNone)
  | _, _, .rbit n, (pa, ()), (.gpr (.reg d), ()) => do
    if !(n == 32 || n == 64) then none
    else
      let (ca, ra) ← armArgInIns .X16 pa
      let w := armWidthOf n
      some (ca ++ [armIselInsI (.RBIT (zr d w) (zr ra w))], maskNone)
  | _, _, .ctz n, (pa, ()), (.gpr (.reg d), ()) => do
    if !(n == 32 || n == 64) then none
    else
      let (ca, ra) ← armArgInIns .X16 pa
      let w := armWidthOf n
      some (ca ++ [armIselInsI (.RBIT (zr d w) (zr ra w)),
        armIselInsI (.CLZ (zr d w) (zr d w))], maskNone)
  | _, _, .cmp o (.bits n) _ rfl, (pa, pb, ()), (dst, ()) => armCmpOpIns o n pa pb dst
  | _, _, .select (.bits n), (pc, pa, pb, ()), (.gpr (.reg d), ()) =>
    armSelectOpIns n pc pa pb d
  | _, _, .addc n, (pa, pb, cin, ()), (.gpr (.reg d), cout, ()) =>
    armAddcOpIns n pa pb cin d cout vh
  | _, _, .subb n, (pa, pb, bin, ()), (.gpr (.reg d), bout, ()) =>
    armSubbOpIns n pa pb bin d bout vh
  | _, _, .umulw n, (pa, pb, ()), (.gpr (.reg dlo), .gpr (.reg dhi), ()) =>
    armMulwOpIns false n pa pb dlo dhi
  | _, _, .smulw n, (pa, pb, ()), (.gpr (.reg dlo), .gpr (.reg dhi), ()) =>
    armMulwOpIns true n pa pb dlo dhi
  | _, _, .fshl n, (pa, pb, pc, ()), (.gpr (.reg d), ()) => armFunnelOpIns true n pa pb pc d
  | _, _, .fshr n, (pa, pb, pc, ()), (.gpr (.reg d), ()) => armFunnelOpIns false n pa pb pc d
  | _, _, _, _, _ => none

/-- Scalar `OpCode` lowering for AArch64. -/
def armOp {sig rs : List Ty} (code : OpCode sig rs) (pas : Tup (PArg Reg Empty ArmCond) sig)
    (dsts : Tup (PDst Reg Empty ArmCond) rs) (vh : VariantHint) :
    Option (List Directive × FlagMask) :=
  emitCleanPair (armOpIns code pas dsts vh)

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

/-- `true` when `armOp` writes `[.bits 32]` to `.gpr (.reg _)` with bits `32..63` zeroed. -/
def armZeroUpper32Op : {sig rs : List Ty} → OpCode sig rs →
    Tup (PArg Reg Empty ArmCond) sig → Tup (PDst Reg Empty ArmCond) rs → Bool
  | _, [.bits 32], _, _, (.gpr (.reg _), ()) => true
  | _, _, _, _, _ => false

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
  cmpFlags := [.eq, .ne, .lt, .ge, .le, .gt, .ls, .hi]
  zeroUpper32Load := true
  zeroUpper32Op := armZeroUpper32Op
  elideZext32 := true

end LeanQbe.T.Arm64
