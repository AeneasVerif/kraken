module

public import LeanQbe.T.Arm64.Base
public import LeanQbe.T.IselStepAttr
public import LeanQbe.T.Arm64.IselFlagHooks
public import LeanQbe.T.Arm64.IselShift

/-!
# AArch64 Scalar Instruction Selection (`GprIsa`)

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

/-- Load 64-bit literal pool constant `c` into GP register `d` (`Instr`). -/
abbrev armIselLdrPoolBvI (d : XReg) (c : BitVec 64) : Instr :=
  armIselInsI (w := .W64) (.LDR (zr d .W64) (.lit (.pool { expr := .int64 (Int64.ofBitVec c) })))

/-- Move `s : XReg` to `.SP` (`Instr`). -/
abbrev armIselMovToSpI (s : XReg) : Instr :=
  armIselInsI (.ADD_e (.low .SP .W64) (.low (.reg s) .W64) imm0)

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

/-- Arithmetic extension shift amount (`E0..E4`) for shift `sh ≤ 4`. -/
def armExtendAmount? : Nat → Option ExtendAmount
  | 0 => some .E0
  | 1 => some .E1
  | 2 => some .E2
  | 3 => some .E3
  | 4 => some .E4
  | _ => none

/-- Arithmetic extension shift amount (`E0..E3`) for `AddrScale`. -/
def armExtendAmount : AddrScale → ExtendAmount
  | .s1 => .E0 | .s2 => .E1 | .s4 => .E2 | .s8 => .E3

/-- Memory operand `[rb, ri, lsl #amt]` (`zextIdx = false`) or
`[rb, w_ri, uxtw #amt]` (`zextIdx = true`). -/
abbrev armAtIdxExtScale (zextIdx : Bool) (rb ri : XReg) (amt : MemExtendAmount) : AddrExpr :=
  { base := .low (.reg rb) .W64,
    off := .reg
      { reg := if zextIdx then ⟨.W32, zr ri .W32⟩ else ⟨.W64, zr ri .W64⟩,
        ext := { type := if zextIdx then .UXTW else .UXTX, amount := amt } } }

/-- Memory operand `[rb, ri, lsl #amt]`. -/
abbrev armAtIdxScale (rb ri : XReg) (amt : MemExtendAmount) : AddrExpr :=
  armAtIdxExtScale false rb ri amt

/-- Memory operand `[rb, w_ri, uxtw #amt]`. -/
abbrev armAtIdxZextScale (rb ri : XReg) (amt : MemExtendAmount) : AddrExpr :=
  armAtIdxExtScale true rb ri amt

/-- 64-bit extended-register add `ADD rd, rb, w_ri, uxtw #amt` (`Instr`). -/
abbrev armAddUxtwI (d rb : Reg) (ri : XReg) (amt : ExtendAmount) : Instr :=
  armIselInsI (w := .W64)
    (.ADD_e (.low d .W64) (.low rb .W64)
      (.ext { reg := ⟨.W32, zr ri .W32⟩, ext := { type := .UXTW, amount := amt } }))

/-- Compute `xd := xb + ((zext 32 64 or full) ri <<< sc.shift)` (`Instr`). -/
def armAddIdxShiftI (zextIdx : Bool) (d rb ri : XReg) (sc : AddrScale) : Instr :=
  if zextIdx then armAddUxtwI (.reg d) (.reg rb) ri (armExtendAmount sc)
  else armIselInsI (.ADD_s (zr d .W64) (zr rb .W64)
    { reg := zr ri .W64, amount := Int64.ofNat sc.shift, shift := .LSL })

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

/-- Materialize 64-bit constant `c` into `x_d` via `MOVZ`, `MOVN`, 1-insn logical `ORR`,
2-insn `MOVZ+MOVK` / `MOVN+MOVK`, or literal-pool `LDR` fallback (`3..4` non-trivial chunks). -/
def armMovImmI (d : XReg) (c : BitVec 64) : List Instr :=
  if c == 0#64 then [armMovzI d 0 .LSL0]
  else if c == ~~~0#64 then [armMovnI d 0 .LSL0]
  else match armNonZeroChunks c with
    | [(k, sh)] => [armMovzI d k sh]
    | _ => match armNonZeroChunks (~~~c) with
      | [(k, sh)] => [armMovnI d k sh]
      | _ =>
        if armIsValidLogicalImm .W64 c then
          [armIselInsI
            (.ORR_i (.low (.reg d) .W64) (xzr .W64) (.int64 (Int64.ofBitVec c)))]
        else match armNonZeroChunks c with
          | [(k1, sh1), (k2, sh2)] => [armMovzI d k1 sh1, armMovkI d k2 sh2]
          | _ => match armNonZeroChunks (~~~c) with
            | [(k1, sh1), (k2, sh2)] =>
              [armMovnI d k1 sh1, armMovkI d (k2 ^^^ 0xFFFF) sh2]
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

/-- 12-bit immediate add/sub instruction, flipping sign via `ADD_e`/`SUB_e` for negative imms. -/
def armAddSubImmI? {n : Nat} (isSub : Bool) (w : RegWidth) (d rx : XReg) (c : BitVec n) :
    Option Instr :=
  match armImm12? c with
  | some ei =>
    some (armIselInsI (if isSub then .SUB_e (.low (.reg d) w) (.low (.reg rx) w) ei
      else .ADD_e (.low (.reg d) w) (.low (.reg rx) w) ei))
  | none =>
    match armImm12? (-c) with
    | some ei =>
      some (armIselInsI (if isSub then .ADD_e (.low (.reg d) w) (.low (.reg rx) w) ei
        else .SUB_e (.low (.reg d) w) (.low (.reg rx) w) ei))
    | none => none

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

/-- `orr xd, xzr, xs` (`mov xd, xs`, zero-cycle register rename) for GP-to-GP moves;
`add rd, rs, #0` when either operand is `.SP` (`Instr` builder). -/
def armMovIns (rd rs : Reg) : List Instr :=
  match rd, rs with
  | .reg d, .reg s => [armIselInsI (w := .W64) (.ORR_s (zr d .W64) (xzr .W64) (sh s))]
  | _, _ => [armIselInsI (w := .W64) (.ADD_e (.low rd .W64) (.low rs .W64) imm0)]

/-- Move `rs` into `rd` (`orr`/`mov` for GP-to-GP, `add #0` for `.SP`), preserving all flags. -/
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

/-- True iff `disp` fits as a scaled unsigned offset `[xb, #disp]` for access size `scale`. -/
def armFitsScaledOff (scale : Nat) (disp : Int64) : Bool :=
  Nat.ble disp.toBitVec.toNat (4095 * scale) && (disp.toBitVec.toNat % scale == 0)

/-- True iff `[rb, ri, sc, disp]` lowers via `armSetupAddrIns` using at most `.X16`. -/
def armAddrIdxValid (scale : Nat) (sc : AddrScale) (disp : Int64) : Bool :=
  (disp != 0 && armFitsScaledOff scale disp) ||
  ((armMemExtendAmount scale sc).isSome &&
    (disp == 0 || (armImm12? disp.toBitVec).isSome || (armImm12? (-disp.toBitVec)).isSome))

/-- Shared `[rb, ri, lsl/uxtw #sh, #disp]` lowering using at most `.X16` (`Instr` builder). -/
def armSetupIdxDispIns (zextIdx : Bool) (scale : Nat) (rb ri : XReg)
    (sc : AddrScale) (disp : Int64) : List Instr × AddrExpr :=
  match (if disp == 0 then armMemExtendAmount scale sc else none) with
  | some amt => ([], armAtIdxExtScale zextIdx rb ri amt)
  | none =>
    if armFitsScaledOff scale disp then
      ([armAddIdxShiftI zextIdx .X16 rb ri sc], armAtDisp .X16 disp)
    else
      match armMemExtendAmount scale sc, armAddSubImmI? false .W64 .X16 rb disp.toBitVec with
      | some amt, some addIns => ([addIns], armAtIdxExtScale zextIdx .X16 ri amt)
      | _, _ => ([], atReg .X16)

/-- Compute effective `AddrExpr` for `base + ((zext 32 64 idx) <<< sc.shift) + disp`
using scratch `.X16` only (`Instr` builder). -/
def armSetupAddrZextIns (scale : Nat) (base idx : Reg) (sc : AddrScale) (disp : Int64) :
    Option (List Instr × AddrExpr) :=
  match base, idx with
  | .reg rb, .reg ri =>
    if armAddrIdxValid scale sc disp then some (armSetupIdxDispIns true scale rb ri sc disp)
    else none
  | _, _ => none

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
  | .baseIdxDisp (.reg rb) (.reg ri) sc disp => armSetupIdxDispIns false scale rb ri sc disp
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

/-- Single store `Instr` from `x_s`/`w_s` (or `xzr`/`wzr`) to effective address `addr`. -/
def armStoreDirI (t : Ty) (s : XRegOrXzr) (addr : AddrExpr) : Option Instr :=
  match t with
  | .bool | .bits 8 => some (armIselInsI (.STRB (.low s .W32) addr))
  | .bits 16 => some (armIselInsI (.STRH (.low s .W32) addr))
  | .bits 32 => some (armIselInsI (w := .W32) (.STR (.low s .W32) addr))
  | .bits 64 => some (armIselInsI (w := .W64) (.STR (.low s .W64) addr))
  | _ => none

/-- Address validity gate for AArch64 scalar loads/stores at byte access size `scale`. -/
def armAddrValid (scale : Nat) : AddrArg Reg → Bool
  | .baseIdxDisp (.reg _) (.reg _) sc disp => armAddrIdxValid scale sc disp
  | .baseIdxDisp .. => false
  | _ => true

/-- Single sign-extending load `Instr` (`ldrsb`/`ldrsh`/`ldrsw`) into 64-bit `x_d`. -/
def armLoadSextDirI (m : Nat) (d : XReg) (addr : AddrExpr) : Option Instr :=
  match m with
  | 8 => some (armIselInsI (w := .W64) (.LDRSB (zr d .W64) addr))
  | 16 => some (armIselInsI (w := .W64) (.LDRSH (zr d .W64) addr))
  | 32 => some (armIselInsI (w := .W64) (.LDRSW (zr d .W64) (.addr addr)))
  | _ => none

/-- Shared tail builder for `armLoadSextIns` and `armLoadSextZextIdxIns`. -/
def armLoadSextTailIns (m : Nat) (rd : Reg) (setup : List Instr) (addr : AddrExpr) :
    Option (List Instr × FlagMask) := do
  match rd with
  | .reg d =>
    let dir ← armLoadSextDirI m d addr
    some (setup ++ [dir], maskNone)
  | .SP =>
    let dir ← armLoadSextDirI m .X16 addr
    some (setup ++ [dir, armIselMovToSpI .X16], maskNone)

/-- Fused sign-extending load of `m ∈ {8, 16, 32}` bits (`m < n ≤ 64`) from `a` into `rd`
(`Instr` builder). -/
def armLoadSextIns (m n : Nat) (rd : Reg) (a : AddrArg Reg) : Option (List Instr × FlagMask) := do
  if !(m == 8 || m == 16 || m == 32) || !Nat.blt m n || !Nat.ble n 64 then none
  else
    let scale ← armMemScale (.bits m)
    if !armAddrValid scale a then none
    else
      let (setup, addr) := armSetupAddrIns scale a
      armLoadSextTailIns m rd setup addr

/-- Fused sign-extending load (`ldrsb`/`ldrsh`/`ldrsw`) with `zext 32 64` scaled index (`Instr`). -/
def armLoadSextZextIdxIns (m n : Nat) (rd base idx : Reg) (sc : AddrScale) (disp : Int64) :
    Option (List Instr × FlagMask) := do
  if !(m == 8 || m == 16 || m == 32) || !Nat.blt m n || !Nat.ble n 64 then none
  else
    let scale ← armMemScale (.bits m)
    let (setup, addr) ← armSetupAddrZextIns scale base idx sc disp
    armLoadSextTailIns m rd setup addr

/-- Fused sign-extending load (`ldrsb`/`ldrsh`/`ldrsw`) into `rd`, preserving all flags. -/
def armLoadSext (m n : Nat) (rd : Reg) (a : AddrArg Reg) : Option (List Directive × FlagMask) :=
  emitCleanPair (armLoadSextIns m n rd a)

/-- Fused sign-extending load (`ldrsb`/`ldrsh`) with `zext 32 64` scaled index, preserving flags. -/
def armLoadSextZextIdx (m n : Nat) (rd base idx : Reg) (sc : AddrScale) (disp : Int64) :
    Option (List Directive × FlagMask) :=
  emitCleanPair (armLoadSextZextIdxIns m n rd base idx sc disp)

/-- Shared tail builder for `armLoadIns` and `armLoadZextIdxIns`. -/
def armLoadTailIns (t : Ty) (rd : Reg) (setup : List Instr) (addr : AddrExpr) :
    Option (List Instr × FlagMask) := do
  match rd with
  | .reg d =>
    let dir ← armLoadDirI t d addr
    some (setup ++ [dir], maskNone)
  | .SP =>
    let dir ← armLoadDirI t .X16 addr
    some (setup ++ [dir, armIselMovToSpI .X16], maskNone)

/-- Load scalar `t` from `a` into `rd` (`Instr` builder). -/
def armLoadIns (t : Ty) (rd : Reg) (a : AddrArg Reg) : Option (List Instr × FlagMask) := do
  let scale ← armMemScale t
  if !armAddrValid scale a then none
  else
    let (setup, addr) := armSetupAddrIns scale a
    armLoadTailIns t rd setup addr

/-- Load scalar `t` from `base + ((zext 32 64 idx) <<< sc.shift) + disp` (`Instr` builder). -/
def armLoadZextIdxIns (t : Ty) (rd base idx : Reg) (sc : AddrScale) (disp : Int64) :
    Option (List Instr × FlagMask) := do
  let scale ← armMemScale t
  let (setup, addr) ← armSetupAddrZextIns scale base idx sc disp
  armLoadTailIns t rd setup addr

/-- Load scalar `t` from `a` into `rd` (handling `.SP` base/destination), preserving all flags. -/
def armLoad (t : Ty) (rd : Reg) (a : AddrArg Reg) : Option (List Directive × FlagMask) :=
  emitCleanPair (armLoadIns t rd a)

/-- Load scalar `t` from `base + ((zext 32 64 idx) <<< sc.shift) + disp`, preserving flags. -/
def armLoadZextIdx (t : Ty) (rd base idx : Reg) (sc : AddrScale) (disp : Int64) :
    Option (List Directive × FlagMask) :=
  emitCleanPair (armLoadZextIdxIns t rd base idx sc disp)

/-- Materialize stored operand `pa` into `.X17` (or return its `XReg`/`.XZR`) (`Instr` builder). -/
def armStoreValInIns : (t : Ty) → PArg Reg Empty ArmCond t → Option (List Instr × XRegOrXzr)
  | .bool, .gpr (.reg r) => some ([], .reg r)
  | .bool, .gpr .SP => some ([armIselMovToXI .X17 .SP], .reg .X17)
  | .bool, .imm false => some ([], .XZR)
  | .bool, .imm true => some (armMovImmI .X17 1#64, .reg .X17)
  | .bool, .flag c => some ([armCset64I .X17 c], .reg .X17)
  | .bits _, .gpr (.reg r) => some ([], .reg r)
  | .bits _, .gpr .SP => some ([armIselMovToXI .X17 .SP], .reg .X17)
  | .bits n, .imm c =>
    if c == 0#n then some ([], .XZR)
    else some (armMovImmI .X17 (c.setWidth 64), .reg .X17)
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

/-- Store scalar `pa` to `base + ((zext 32 64 idx) <<< sc.shift) + disp` (`Instr` builder). -/
def armStoreZextIdxIns (t : Ty) (pa : PArg Reg Empty ArmCond t) (base idx : Reg)
    (sc : AddrScale) (disp : Int64) : Option (List Instr × FlagMask) := do
  let scale ← armMemScale t
  let (addrSetup, addr) ← armSetupAddrZextIns scale base idx sc disp
  let (valSetup, rx) ← armStoreValInIns t pa
  let dir ← armStoreDirI t rx addr
  some (valSetup ++ addrSetup ++ [dir], maskNone)

/-- Store scalar `pa` of type `t` to `a`, preserving all flags. -/
def armStore (t : Ty) (pa : PArg Reg Empty ArmCond t) (a : AddrArg Reg) :
    Option (List Directive × FlagMask) :=
  emitCleanPair (armStoreIns t pa a)

/-- Store scalar `pa` to `base + ((zext 32 64 idx) <<< sc.shift) + disp`, preserving flags. -/
def armStoreZextIdx (t : Ty) (pa : PArg Reg Empty ArmCond t) (base idx : Reg)
    (sc : AddrScale) (disp : Int64) : Option (List Directive × FlagMask) :=
  emitCleanPair (armStoreZextIdxIns t pa base idx sc disp)

/-! ## 3. Scalar `armOp` helpers (`[8, 16, 32, 64]`, `bswap`, `[32, 64]` bit/carry/mulw/fsh) -/

/-- Extend low `n` bits (`8` or `16`) into `.W32` (`UBFM` or `SBFM`) (`Instr`). -/
abbrev armExt32I (signed : Bool) (n : Nat) (d s : XReg) : Instr :=
  if signed then armIselInsI (.SBFM (zr d .W32) (zr s .W32) 0 (n - 1))
  else armIselInsI (.UBFM (zr d .W32) (zr s .W32) 0 (n - 1))

/-- Extend low `n` bits (`8` or `16`) into `.W32` (`UBFM` or `SBFM`). -/
abbrev armExt32 (signed : Bool) (n : Nat) (d s : XReg) : Directive :=
  .instr (armExt32I signed n d s)

/-- Shared builder for boolean `.and`/`.or` into GP register `d` (`Instr` builder). -/
def armBoolAndOrIns (isOr : Bool) (pa pb : PArg Reg Empty ArmCond .bool) (d : XReg) :
    Option (List Instr × FlagMask) :=
  let binBool (op : Operation .W32) := armIselInsI op
  let andOrFlagGpr (c : ArmCond) (r : XReg) : List Instr :=
    if isOr then [binBool (.CSINC (zr d .W32) (zr r .W32) (xzr .W32) (armNegCond c).toKraken)]
    else [binBool (.CSEL (zr d .W32) (zr r .W32) (xzr .W32) c.toKraken)]
  let andOrFlags (c1 c2 : ArmCond) : List Instr :=
    if c1 == c2 then [armCset64I d c1]
    else if c1 == armNegCond c2 then armMovImmI d (BitVec.ofNat 64 isOr.toNat)
    else armCset64I .X16 c1 :: andOrFlagGpr c2 .X16
  let fallback : Option (List Instr × FlagMask) := do
    let (ca, ra) ← armBoolArgInIns .X16 pa
    let (cb, rb) ← armBoolArgInIns .X17 pb
    let insDir := if isOr then binBool (.ORR_s (zr d .W32) (zr ra .W32) (sh rb))
      else binBool (.AND_s (zr d .W32) (zr ra .W32) (sh rb))
    some (ca ++ cb ++ [insDir], maskNone)
  match pa with
  | .gpr (.reg r) =>
    match pb with
    | .flag c => some (andOrFlagGpr c r, maskNone)
    | .imm b =>
      if b == isOr then some (armMovImmI d (BitVec.ofNat 64 isOr.toNat), maskNone)
      else some ([binBool (.ORR_s (zr d .W32) (xzr .W32) (sh r))], maskNone)
    | _ => fallback
  | .flag c1 =>
    match pb with
    | .gpr (.reg r) => some (andOrFlagGpr c1 r, maskNone)
    | .flag c2 => some (andOrFlags c1 c2, maskNone)
    | .imm b =>
      if b == isOr then some (armMovImmI d (BitVec.ofNat 64 isOr.toNat), maskNone)
      else some ([armCset64I d c1], maskNone)
    | _ => fallback
  | .imm b =>
    match pb with
    | .gpr (.reg r) =>
      if b == isOr then some (armMovImmI d (BitVec.ofNat 64 isOr.toNat), maskNone)
      else some ([binBool (.ORR_s (zr d .W32) (xzr .W32) (sh r))], maskNone)
    | .flag c =>
      if b == isOr then some (armMovImmI d (BitVec.ofNat 64 isOr.toNat), maskNone)
      else some ([armCset64I d c], maskNone)
    | _ => fallback
  | _ => fallback

/-- Builder for boolean `.xor` into GP register `d` (`Instr` builder). -/
def armBoolXorIns (pa pb : PArg Reg Empty ArmCond .bool) (d : XReg) :
    Option (List Instr × FlagMask) :=
  let binBool (op : Operation .W32) := armIselInsI op
  let xorRegImm (r : XReg) (b : Bool) : List Instr :=
    if b then [binBool (.EOR_i (.low (.reg d) .W32) (zr r .W32) (.int64 1))]
    else [binBool (.ORR_s (zr d .W32) (xzr .W32) (sh r))]
  let fallback : Option (List Instr × FlagMask) := do
    let (ca, ra) ← armBoolArgInIns .X16 pa
    let (cb, rb) ← armBoolArgInIns .X17 pb
    some (ca ++ cb ++ [binBool (.EOR_s (zr d .W32) (zr ra .W32) (sh rb))], maskNone)
  match pa with
  | .gpr (.reg r) => match pb with | .imm b => some (xorRegImm r b, maskNone) | _ => fallback
  | .flag c => match pb with
    | .imm b => some ([armCset64I d (if b then armNegCond c else c)], maskNone)
    | _ => fallback
  | .imm b => match pb with
    | .gpr (.reg r) => some (xorRegImm r b, maskNone)
    | .flag c => some ([armCset64I d (if b then armNegCond c else c)], maskNone)
    | _ => fallback
  | _ => fallback

/-- Emit boolean `copy`, `and`, `or`, `xor`, or `not` into GP register `d` (`Instr` builder). -/
def armBoolOpIns {sig : List Ty} (code : OpCode sig [.bool])
    (pas : Tup (PArg Reg Empty ArmCond) sig) (d : XReg) : Option (List Instr × FlagMask) :=
  let binBool (op : Operation .W32) := armIselInsI op
  match code with
  | .copy .bool => match pas.1 with
    | .gpr (.reg r) => some ([binBool (.ORR_s (zr d .W32) (xzr .W32) (sh r))], maskNone)
    | .imm b => some (armMovImmI d (BitVec.ofNat 64 b.toNat), maskNone)
    | .flag c => some ([armCset64I d c], maskNone)
    | _ => none
  | .not .bool => match pas.1 with
    | .imm b => some (armMovImmI d (BitVec.ofNat 64 (!b).toNat), maskNone)
    | .flag c => some ([armCset64I d (armNegCond c)], maskNone)
    | .gpr (.reg r) =>
      some ([binBool (.EOR_i (.low (.reg d) .W32) (zr r .W32) (.int64 1))], maskNone)
    | _ => none
  | .and .bool => armBoolAndOrIns false pas.1 pas.2.1 d
  | .or .bool => armBoolAndOrIns true pas.1 pas.2.1 d
  | .xor .bool => armBoolXorIns pas.1 pas.2.1 d
  | _ => none

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

/-- Wrapping binary ALU ops (`add`, `sub`, `mul`, `and`, `or`, `xor`) at `[8, 16, 32, 64]`. -/
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

/-- Shift amount `k < n` if `c == 1#n <<< k`. -/
def armPow2Shift? {n : Nat} (c : BitVec n) : Option Nat :=
  (List.range n).find? fun k => c == 1#n <<< k

/-- Shift amount `1 ≤ k < n` if `c == (1#n <<< k) + 1#n`. -/
def armPow2Plus1Shift? {n : Nat} (c : BitVec n) : Option Nat :=
  (List.range n).tail.find? fun k => c == (1#n <<< k) + 1#n

/-- Multiply `r` by constant `imm` in `n`-bit mode (`w := armWidthOf n`), avoiding `MADD` for
`0`, `1`, `-1`, `2^k`, and `2^k + 1`. -/
def armMulRegImmIns {n : Nat} (w : RegWidth) (d r : XReg) (imm : BitVec n) : List Instr :=
  if imm == 0#n then armMovImmI d 0#64
  else if imm == ~~~0#n then [armIselInsI (.SUB_s (zr d w) (xzr w) (sh r))]
  else match armPow2Shift? imm with
    | some k =>
      if k == 0 then [armIselInsI (.ORR_s (zr d w) (xzr w) (sh r))]
      else [armIselInsI (.UBFM (zr d w) (zr r w) ((w.bits - k) % w.bits) (w.bits - 1 - k))]
    | none => match armPow2Plus1Shift? imm with
      | some k =>
        [armIselInsI (.ADD_s (zr d w) (zr r w)
          { reg := zr r w, amount := Int64.ofNat k, shift := .LSL })]
      | none => armMovImmI .X17 (imm.setWidth 64) ++ [armBinDirI .mul w d r .X17]

def armBinOpIns (k : ArmBinK) (n : Nat) (pa pb : PArg Reg Empty ArmCond (.bits n)) (d : XReg) :
    Option (List Instr × FlagMask) := do
  if ![8, 16, 32, 64].contains n then none
  else
    let w := armWidthOf n
    match k, pa, pb with
    | .add, .gpr (.reg ra), .imm cb =>
      match armAddSubImmI? false w d ra cb with
      | some dir => some ([dir], maskNone)
      | none =>
        let (cb', rb) ← armArgInIns .X17 pb
        some (cb' ++ [armBinDirI k w d ra rb], maskNone)
    | .add, .imm ca, .gpr (.reg rb) =>
      match armAddSubImmI? false w d rb ca with
      | some dir => some ([dir], maskNone)
      | none =>
        let (ca', ra) ← armArgInIns .X16 pa
        some (ca' ++ [armBinDirI k w d ra rb], maskNone)
    | .sub, .gpr (.reg ra), .imm cb =>
      match armAddSubImmI? true w d ra cb with
      | some dir => some ([dir], maskNone)
      | none =>
        let (cb', rb) ← armArgInIns .X17 pb
        some (cb' ++ [armBinDirI k w d ra rb], maskNone)
    | .sub, .imm ca, .gpr (.reg rb) =>
      if ca == 0#n then
        some ([armIselInsI (.SUB_s (zr d w) (xzr w) (sh rb))], maskNone)
      else if ca == ~~~0#n then
        some ([armIselInsI (.ORN_s (zr d w) (xzr w) (sh rb))], maskNone)
      else
        let (ca', ra) ← armArgInIns .X16 pa
        some (ca' ++ [armBinDirI k w d ra rb], maskNone)
    | .mul, .gpr (.reg ra), .imm cb => some (armMulRegImmIns w d ra cb, maskNone)
    | .mul, .imm ca, .gpr (.reg rb) => some (armMulRegImmIns w d rb ca, maskNone)
    | .and, .gpr (.reg ra), .imm cb
    | .or, .gpr (.reg ra), .imm cb
    | .xor, .gpr (.reg ra), .imm cb =>
      let c64 := cb.setWidth 64
      if armIsValidLogicalImm w c64 then
        let dir ← armLogicImmDirI k w d ra (Int64.ofBitVec c64)
        some ([dir], maskNone)
      else if (n == 8 || n == 16) && armIsValidLogicalImm .W32 (cb.signExtend 64) then
        let dir ← armLogicImmDirI k .W32 d ra (Int64.ofBitVec (cb.signExtend 64))
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
      else if (n == 8 || n == 16) && armIsValidLogicalImm .W32 (ca.signExtend 64) then
        let dir ← armLogicImmDirI k .W32 d rb (Int64.ofBitVec (ca.signExtend 64))
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
    match pa, pb with
    | .gpr (.reg ra), .imm cb =>
      if cb == 0#n then
        match armZeroCmpIns? o n ra dst with
        | some r => some r
        | none =>
          if n == 32 || n == 64 then
            match armCmpImmIns? (armWidthOf n) ra cb with
            | some cmp => finish cmp (armCmpCond o)
            | none => none
          else
            let ext := armExt32I (armIsSignedCmp o) n .X16 ra
            match armCmpImmIns? .W32 .X16 0#32 with
            | some cmp => finish (ext :: cmp) (armCmpCond o)
            | none => none
      else if n == 32 || n == 64 then
        let w := armWidthOf n
        match armCmpImmIns? w ra cb with
        | some cmp => finish cmp (armCmpCond o)
        | none =>
          let (cb', rb) ← armArgInIns .X17 pb
          finish (cb' ++ [armIselInsI (.SUBS_s (xzr w) (zr ra w) (sh rb))]) (armCmpCond o)
      else
        let sgn := armIsSignedCmp o
        let c32 := if sgn then cb.signExtend 32 else cb.setWidth 32
        let ext := armExt32I sgn n .X16 ra
        let cmp := match armCmpImmIns? .W32 .X16 c32 with
          | some cmp => ext :: cmp
          | none => ext :: armMovImmI .X17 (c32.setWidth 64) ++
              [armIselInsI (.SUBS_s (xzr .W32) (zr .X16 .W32) (sh .X17))]
        finish cmp (armCmpCond o)
    | .imm ca, .gpr (.reg rb) =>
      if ca == 0#n then
        match armZeroCmpIns? o.swap n rb dst with
        | some r => some r
        | none =>
          if n == 32 || n == 64 then
            match armCmpImmIns? (armWidthOf n) rb ca with
            | some cmp => finish cmp (armCmpCond o.swap)
            | none => none
          else
            let ext := armExt32I (armIsSignedCmp o) n .X16 rb
            match armCmpImmIns? .W32 .X16 0#32 with
            | some cmp => finish (ext :: cmp) (armCmpCond o.swap)
            | none => none
      else if n == 32 || n == 64 then
        let w := armWidthOf n
        match armCmpImmIns? w rb ca with
        | some cmp => finish cmp (armCmpCond o.swap)
        | none =>
          let (ca', ra) ← armArgInIns .X16 pa
          finish (ca' ++ [armIselInsI (.SUBS_s (xzr w) (zr ra w) (sh rb))]) (armCmpCond o)
      else
        let sgn := armIsSignedCmp o
        let c32 := if sgn then ca.signExtend 32 else ca.setWidth 32
        let ext := armExt32I sgn n .X16 rb
        let cmp := match armCmpImmIns? .W32 .X16 c32 with
          | some cmp => ext :: cmp
          | none => ext :: armMovImmI .X17 (c32.setWidth 64) ++
              [armIselInsI (.SUBS_s (xzr .W32) (zr .X16 .W32) (sh .X17))]
        finish cmp (armCmpCond o.swap)
    | _, _ =>
      let (ca, ra) ← armArgInIns .X16 pa
      let (cb, rb) ← armArgInIns .X17 pb
      if n == 32 || n == 64 then
        let w := armWidthOf n
        finish (ca ++ cb ++ [armIselInsI (.SUBS_s (xzr w) (zr ra w) (sh rb))]) (armCmpCond o)
      else
        let sgn := armIsSignedCmp o
        finish (ca ++ cb ++ [armExt32I sgn n .X16 ra, armExt32I sgn n .X17 rb,
          armIselInsI (.SUBS_s (xzr .W32) (zr .X16 .W32) (sh .X17))]) (armCmpCond o)

/-- Conditional select lowering given live architectural `cond` (`CSEL`/`CSINC`/`CSINV` with
`0`/`1`/`-1` without literal materialization, `maskNone`). -/
def armSelectCondIns (n : Nat) (cond : ArmCond) (pa pb : PArg Reg Empty ArmCond (.bits n))
    (d : XReg) : Option (List Instr) :=
  let w := armWidthOf n
  let mkSel (ra rb : XRegOrXzr) (op : Nat) (cnd : ArmCond) : Instr :=
    match op with
    | 0 => armIselInsI (.CSEL (zr d w) (.low ra w) (.low rb w) cnd.toKraken)
    | 1 => armIselInsI (.CSINC (zr d w) (.low ra w) (.low rb w) cnd.toKraken)
    | _ => armIselInsI (.CSINV (zr d w) (.low ra w) (.low rb w) cnd.toKraken)
  let mkNeg (rx : XReg) (cnd : ArmCond) : Instr :=
    armIselInsI (.CSNEG (zr d w) (zr rx w) (zr rx w) cnd.toKraken)
  match pa, pb with
  | .imm ca, .imm cb =>
    if ca == cb then some (armMovImmI d (ca.setWidth 64))
    else if ca == 1#n && cb == 0#n then some [mkSel .XZR .XZR 1 (armNegCond cond)]
    else if ca == 0#n && cb == 1#n then some [mkSel .XZR .XZR 1 cond]
    else if ca == ~~~0#n && cb == 0#n then some [mkSel .XZR .XZR 2 (armNegCond cond)]
    else if ca == 0#n && cb == ~~~0#n then some [mkSel .XZR .XZR 2 cond]
    else if ca == -cb then
      if Nat.ble cb.toNat ca.toNat then do
        let (cb', rb) ← armArgInIns .X17 pb
        some (cb' ++ [mkNeg rb (armNegCond cond)])
      else do
        let (ca', ra) ← armArgInIns .X16 pa
        some (ca' ++ [mkNeg ra cond])
    else if cb == 0#n then do
      let (ca', ra) ← armArgInIns .X16 pa
      some (ca' ++ [mkSel (.reg ra) .XZR 0 cond])
    else if cb == 1#n then do
      let (ca', ra) ← armArgInIns .X16 pa
      some (ca' ++ [mkSel (.reg ra) .XZR 1 cond])
    else if cb == ~~~0#n then do
      let (ca', ra) ← armArgInIns .X16 pa
      some (ca' ++ [mkSel (.reg ra) .XZR 2 cond])
    else if ca == 0#n then do
      let (cb', rb) ← armArgInIns .X17 pb
      some (cb' ++ [mkSel (.reg rb) .XZR 0 (armNegCond cond)])
    else if ca == 1#n then do
      let (cb', rb) ← armArgInIns .X17 pb
      some (cb' ++ [mkSel (.reg rb) .XZR 1 (armNegCond cond)])
    else if ca == ~~~0#n then do
      let (cb', rb) ← armArgInIns .X17 pb
      some (cb' ++ [mkSel (.reg rb) .XZR 2 (armNegCond cond)])
    else if cb == ca + 1#n then do
      let (ca', ra) ← armArgInIns .X16 pa
      some (ca' ++ [mkSel (.reg ra) (.reg ra) 1 cond])
    else if ca == cb + 1#n then do
      let (cb', rb) ← armArgInIns .X17 pb
      some (cb' ++ [mkSel (.reg rb) (.reg rb) 1 (armNegCond cond)])
    else if cb == ~~~ca then
      if Nat.ble cb.toNat ca.toNat then do
        let (cb', rb) ← armArgInIns .X17 pb
        some (cb' ++ [mkSel (.reg rb) (.reg rb) 2 (armNegCond cond)])
      else do
        let (ca', ra) ← armArgInIns .X16 pa
        some (ca' ++ [mkSel (.reg ra) (.reg ra) 2 cond])
    else do
      let (ca', ra) ← armArgInIns .X16 pa
      let (cb', rb) ← armArgInIns .X17 pb
      some (ca' ++ cb' ++ [mkSel (.reg ra) (.reg rb) 0 cond])
  | .gpr (.reg ra), .imm cb =>
    if cb == 0#n then some [mkSel (.reg ra) .XZR 0 cond]
    else if cb == 1#n then some [mkSel (.reg ra) .XZR 1 cond]
    else if cb == ~~~0#n then some [mkSel (.reg ra) .XZR 2 cond]
    else do
      let (cb', rb) ← armArgInIns .X17 pb
      some (cb' ++ [mkSel (.reg ra) (.reg rb) 0 cond])
  | .imm ca, .gpr (.reg rb) =>
    if ca == 0#n then some [mkSel (.reg rb) .XZR 0 (armNegCond cond)]
    else if ca == 1#n then some [mkSel (.reg rb) .XZR 1 (armNegCond cond)]
    else if ca == ~~~0#n then some [mkSel (.reg rb) .XZR 2 (armNegCond cond)]
    else do
      let (ca', ra) ← armArgInIns .X16 pa
      some (ca' ++ [mkSel (.reg ra) (.reg rb) 0 cond])
  | _, _ => do
    let (ca, ra) ← armArgInIns .X16 pa
    let (cb, rb) ← armArgInIns .X17 pb
    some (ca ++ cb ++ [mkSel (.reg ra) (.reg rb) 0 cond])

/-- Branchless `CSEL`/`CSINC`/`CSINV` conditional select at `[8, 16, 32, 64]` (`Instr` builder). -/
def armSelectOpIns (n : Nat) (pc : PArg Reg Empty ArmCond .bool)
    (pa pb : PArg Reg Empty ArmCond (.bits n)) (d : XReg) :
    Option (List Instr × FlagMask) := do
  if ![8, 16, 32, 64].contains n then none
  else
    match pc with
    | .imm true => armCopyBitsIns n pa d
    | .imm false => armCopyBitsIns n pb d
    | .flag cond =>
      let sel ← armSelectCondIns n cond pa pb d
      some (sel, maskNone)
    | .gpr (.reg rc) =>
      let sel ← armSelectCondIns n .ne pa pb d
      some (armIselInsI (.ANDS_i (xzr .W32) (zr rc .W32) (.int64 1)) :: sel, maskNZCV)
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

/-- Emit `ANDS` setting flags for `va &&& vb` at `[8, 16, 32, 64]` without clobbering GPRs
other than `.X16`/`.X17`. -/
def armTestDirectIns (n : Nat) (pa pb : PArg Reg Empty ArmCond (.bits n)) :
    Option (List Instr) :=
  if n == 32 || n == 64 then
    let w := armWidthOf n
    let regImm (rx : XReg) (cy : BitVec n) : Option (List Instr) :=
      let c64 := cy.setWidth 64
      if armIsValidLogicalImm w c64 then
        some [armIselInsI (.ANDS_i (xzr w) (zr rx w) (.int64 (Int64.ofBitVec c64)))]
      else if cy == ~~~0#n then
        some [armIselInsI (.ANDS_s (xzr w) (zr rx w) (sh rx))]
      else if cy == 0#n then
        some [armIselInsI (.ANDS_s (xzr w) (xzr w)
          { reg := xzr w, amount := 0, shift := .LSL })]
      else do
        let (cb, ry) ← armArgInIns .X17 (.imm cy)
        some (cb ++ [armIselInsI (.ANDS_s (xzr w) (zr rx w) (sh ry))])
    match pa, pb with
    | .gpr (.reg rx), .gpr (.reg ry) =>
      some [armIselInsI (.ANDS_s (xzr w) (zr rx w) (sh ry))]
    | .gpr (.reg rx), .imm cy => regImm rx cy
    | .imm cx, .gpr (.reg ry) => regImm ry cx
    | .imm _, .imm _ => do
      let (ca, rx) ← armArgInIns .X16 pa
      let (cb, ry) ← armArgInIns .X17 pb
      some (ca ++ cb ++ [armIselInsI (.ANDS_s (xzr w) (zr rx w) (sh ry))])
    | _, _ => none
  else
    let regImm816 (rx : XReg) (cy : BitVec n) : Option (List Instr) :=
      let c64 := cy.setWidth 64
      if armIsValidLogicalImm .W32 c64 then
        some [armIselInsI (.ANDS_i (xzr .W32) (zr rx .W32) (.int64 (Int64.ofBitVec c64)))]
      else if cy == 0#n then
        some [armIselInsI (.ANDS_s (xzr .W32) (xzr .W32)
          { reg := xzr .W32, amount := 0, shift := .LSL })]
      else
        some (armMovImmI .X17 c64 ++
          [armIselInsI (.ANDS_s (xzr .W32) (zr rx .W32) (sh .X17))])
    match pa, pb with
    | .gpr (.reg rx), .gpr (.reg ry) =>
      some [armExt32I false n .X16 rx,
        armIselInsI (.ANDS_s (xzr .W32) (zr .X16 .W32) (sh ry))]
    | .gpr (.reg rx), .imm cy => regImm816 rx cy
    | .imm cx, .gpr (.reg ry) => regImm816 ry cx
    | .imm cx, .imm cy =>
      some (armMovImmI .X16 (cx.setWidth 64) ++ armMovImmI .X17 (cy.setWidth 64) ++
        [armIselInsI (.ANDS_s (xzr .W32) (zr .X16 .W32) (sh .X17))])
    | _, _ => none

/-- Lower fused `(pa &&& pb) ==/!= 0` bit-test (`neg = false` -> `== 0`, `true` -> `!= 0`). -/
def armTestOpIns (n : Nat) (neg : Bool) (pa pb : PArg Reg Empty ArmCond (.bits n))
    (pd : PDst Reg Empty ArmCond .bool) : Option (List Instr × FlagMask) :=
  if ![8, 16, 32, 64].contains n then none
  else
    let wantCond : ArmCond := if neg then .ne else .eq
    match pd with
    | .gpr (.reg d) =>
      match pa, pb with
      | .imm cx, .imm cy =>
        let res := (if neg then CmpOp.ne else CmpOp.eq).evalBits (cx &&& cy) 0#n
        some (armMovImmI d (BitVec.ofNat 64 res.toNat), maskNone)
      | _, _ => do
        let tst ← armTestDirectIns n pa pb
        some (tst ++ [armCset64I d wantCond], maskNZCV)
    | .flag c =>
      if c == wantCond then do
        let tst ← armTestDirectIns n pa pb
        some (tst, maskNZCV)
      else none
    | .gpr .SP | .vec _ => none

/-- Lower fused `(pa &&& pb) ==/!= 0` bit-test into AArch64 directives. -/
def armTestOp (n : Nat) (neg : Bool) (pa pb : PArg Reg Empty ArmCond (.bits n))
    (pd : PDst Reg Empty ArmCond .bool) : Option (List Directive × FlagMask) :=
  emitCleanPair (armTestOpIns n neg pa pb pd)

/-- Return bit index `k < n` iff `mask == 1#n <<< k`. -/
def armSingleBit? (n : Nat) (mask : BitVec n) : Option Nat :=
  (List.range n).find? fun k => mask == (1#n <<< k)

/-- Emit `CBZ`/`CBNZ` sequence for `n ∈ {8, 16, 32, 64}` (zero-extending `8`/`16` via `.X16`). -/
def armCmpZeroCbIns (isNz : Bool) (n : Nat) (x : XReg) (l : Sym) : List Instr :=
  let w := armWidthOf n
  let op : Operation w := if isNz then .CBNZ (zr x w) (.label l) else .CBZ (zr x w) (.label l)
  if n == 32 || n == 64 then [armIselInsI (w := w) op]
  else
    let op32 : Operation .W32 :=
      if isNz then .CBNZ (zr .X16 .W32) (.label l) else .CBZ (zr .X16 .W32) (.label l)
    [armExt32I false n .X16 x, armIselInsI (w := .W32) op32]

/-- Fused compare-against-zero branch (`CBZ`/`CBNZ` for `== 0`/`!= 0`, `TBZ`/`TBNZ`
for signed `< 0`/`>= 0`). -/
def armCmpZeroJccIns (co : CmpOp) (n : Nat) (r : Reg) (l : Sym) :
    Option (List Instr × FlagMask) :=
  if ![8, 16, 32, 64].contains n then none
  else match r with
    | .SP => none
    | .reg x =>
      let w := armWidthOf n
      match co with
      | .eq | .ule => some (armCmpZeroCbIns false n x l, maskNone)
      | .ne | .ugt => some (armCmpZeroCbIns true n x l, maskNone)
      | .slt => some ([armIselInsI (w := w) (.TBNZ (zr x w) (n - 1) (.label l))], maskNone)
      | .sge => some ([armIselInsI (w := w) (.TBZ (zr x w) (n - 1) (.label l))], maskNone)
      | _ => none

/-- Lower fused compare-against-zero branch into AArch64 directives. -/
def armCmpZeroJcc (co : CmpOp) (n : Nat) (r : Reg) (l : Sym) :
    Option (List Directive × FlagMask) :=
  emitCleanPair (armCmpZeroJccIns co n r l)

/-- Fused `(r &&& (1 <<< k)) ==/!= 0` single-bit branch (`TBZ`/`TBNZ`). -/
def armTestJccIns (neg : Bool) (n : Nat) (r : Reg) (mask : BitVec n) (l : Sym) :
    Option (List Instr × FlagMask) :=
  if ![8, 16, 32, 64].contains n then none
  else match r, armSingleBit? n mask with
    | .reg x, some k =>
      let w := armWidthOf n
      let op : Operation w :=
        if neg then .TBNZ (zr x w) k (.label l) else .TBZ (zr x w) k (.label l)
      some ([armIselInsI (w := w) op], maskNone)
    | _, _ => none

/-- Lower fused single-bit `(r &&& mask) ==/!= 0` branch into AArch64 directives. -/
def armTestJcc (neg : Bool) (n : Nat) (r : Reg) (mask : BitVec n) (l : Sym) :
    Option (List Directive × FlagMask) :=
  emitCleanPair (armTestJccIns neg n r mask l)


end LeanQbe.T.Arm64
