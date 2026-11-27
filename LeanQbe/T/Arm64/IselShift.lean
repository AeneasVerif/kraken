module

public import LeanQbe.T.Arm64.Base
public import LeanQbe.T.IselStepAttr
public import LeanQbe.T.Arm64.IselFlagHooks

/-!
# Arm64 Shifted-Register & Extended-Register ALU/CMP Instruction Selection

Pure instruction selection for AArch64 32-bit and 64-bit:
* Shifted-register ALU (`ADD_s`, `SUB_s`, `AND_s`, `ORR_s`, `EOR_s` with `LSL`/`LSR`/`ASR`).
* Shifted-register compare (`SUBS_s` with `LSL`/`LSR`/`ASR` on either LHS or RHS, targeting
  `.flag c` or `.gpr d` via `CSET`).
* Extended-register ALU & compare (`ADD_e`, `SUB_e`, `SUBS_e` with `UXTB`/`SXTB`/`UXTH`/`SXTH`/
  `UXTW`/`SXTW` and shift `0..4`).

Kept free of `*Lemmas*` and `Arm64.Isel` imports so `Arm64.Isel` / `Target` / `Rega` can wire
these hooks cleanly without import cycles.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Arm64

open LeanQbe.T

/-! ## 1. Shifted-Register ALU (`ADD_s`/`SUB_s`/`AND_s`/`ORR_s`/`EOR_s`) -/

/-- Supported barrel-shifter operations on the second GPR operand in Arm64 shifted ops. -/
inductive ArmShiftOp where
  | lsl
  | lsr
  | asr
  deriving DecidableEq, Repr, BEq

/-- Map `ArmShiftOp` to the corresponding Kraken AArch64 `ShiftType`. -/
@[expose]
def ArmShiftOp.toKraken : ArmShiftOp → ShiftType
  | .lsl => .LSL
  | .lsr => .LSR
  | .asr => .ASR

/-- Pure bitvector semantics of `ArmShiftOp` at width `w` with non-negative shift count `k`. -/
@[expose]
def ArmShiftOp.eval {w : Nat} : ArmShiftOp → BitVec w → Nat → BitVec w
  | .lsl, v, k => v <<< k
  | .lsr, v, k => v >>> k
  | .asr, v, k => v.sshiftRight k

/-- ALU opcodes supported by Arm64 shifted-register instruction selection. -/
inductive ArmShiftAluOp where
  | add
  | sub
  | and
  | or
  | xor
  deriving DecidableEq, Repr, BEq

/-- Pure bitvector evaluation of `ArmShiftAluOp` at width `w`. -/
@[expose]
def ArmShiftAluOp.eval {w : Nat} : ArmShiftAluOp → BitVec w → BitVec w → BitVec w
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .and, a, b => a &&& b
  | .or,  a, b => a ||| b
  | .xor, a, b => a ^^^ b

/-- Reconstruct the `OpCode` corresponding to an `ArmShiftAluOp` at width `w`. -/
@[expose]
def ArmShiftAluOp.toOpCode (w : Nat) :
    ArmShiftAluOp → OpCode [.bits w, .bits w] [.bits w]
  | .add => .add (.bits w)
  | .sub => .sub (.bits w)
  | .and => .and (.bits w)
  | .or  => .or  (.bits w)
  | .xor => .xor (.bits w)

/-- Arm64 hardware register widths accepted by shifted/extended ALU and CMP lowering. -/
@[expose]
def armShiftWidth? : Nat → Option RegWidth
  | 32 => some .W32
  | 64 => some .W64
  | _  => none

/-- Explicit GPR guard rejecting `.SP` (while `zr` guarantees `.XZR` is never selected). -/
@[expose]
def armRegX? : Reg → Option XReg
  | .reg r => some r
  | .SP    => none

/-- Match binary bitvector `OpCode` into `ArmShiftAluOp`. -/
@[expose]
def armShiftAluOfOpCode? :
    {w : Nat} → OpCode [.bits w, .bits w] [.bits w] → Option ArmShiftAluOp
  | _, .add _ => some .add
  | _, .sub _ => some .sub
  | _, .and _ => some .and
  | _, .or  _ => some .or
  | _, .xor _ => some .xor
  | _, _      => none

/-- Build a shifted non-XZR `ShiftRegExpr` for operand `rb` shifted by `k`. -/
@[expose]
def armShiftRegExpr (rw : RegWidth) (rb : XReg) (sh : ArmShiftOp) (k : Nat) :
    ShiftRegExpr rw :=
  { reg := zr rb rw, amount := Int64.ofNat k, shift := sh.toKraken }

/-- Emit the single Kraken `Instr` for `rd := ra <op> (rb <sh> #k)`. -/
@[expose]
def armShiftedAluInstrI (op : ArmShiftAluOp) (rw : RegWidth)
    (rd ra rb : XReg) (sh : ArmShiftOp) (k : Nat) : Instr :=
  let src2 := armShiftRegExpr rw rb sh k
  let oper : Operation rw :=
    match op with
    | .add => .ADD_s (zr rd rw) (zr ra rw) src2
    | .sub => .SUB_s (zr rd rw) (zr ra rw) src2
    | .and => .AND_s (zr rd rw) (zr ra rw) src2
    | .or  => .ORR_s (zr rd rw) (zr ra rw) src2
    | .xor => .EOR_s (zr rd rw) (zr ra rw) src2
  { operation_size := rw, operation := oper }

/-- Directive wrapper for `armShiftedAluInstrI`. -/
@[expose]
def armShiftedAluDirI (op : ArmShiftAluOp) (rw : RegWidth)
    (rd ra rb : XReg) (sh : ArmShiftOp) (k : Nat) : Directive :=
  .instr (armShiftedAluInstrI op rw rd ra rb sh k)

/-- Lower a shifted-register ALU operation when `w ∈ {32, 64}`, `k < w`, and regs are GPRs. -/
@[expose]
def armShiftedAluIns (w : Nat) (c : OpCode [.bits w, .bits w] [.bits w])
    (ra rb : Reg) (sh : ArmShiftOp) (k : Nat) (rd : Reg) : Option (List Instr) :=
  if !Nat.blt k w then none
  else
    match armShiftWidth? w, armShiftAluOfOpCode? c,
        armRegX? rd, armRegX? ra, armRegX? rb with
    | some rw, some op, some d, some a, some b =>
        some [armShiftedAluInstrI op rw d a b sh k]
    | _, _, _, _, _ => none

/-- Pure shifted-register ALU selection entry point returning clean directives and `maskNone`. -/
@[expose]
def armShiftedAlu? (w : Nat) (c : OpCode [.bits w, .bits w] [.bits w])
    (ra rb : Reg) (sh : ArmShiftOp) (k : Nat) (rd : Reg) :
    Option (List Directive × FlagMask) :=
  emitCleanPair ((armShiftedAluIns w c ra rb sh k rd).map (·, maskNone))

/-- Flag indicating 32-bit `armShiftedAlu?` zeroes upper 32 bits of `rd`. -/
@[expose]
def armZeroUpper32ShiftedAlu : Bool := true

/-- Generic `AluShift` as the Arm64 barrel-shifter operation. -/
@[expose]
def armAluShift : AluShift → ArmShiftOp
  | .lsl => .lsl
  | .lsr => .lsr
  | .asr => .asr

/-- `GprIsa.shiftAlu` adapter onto `armShiftedAlu?`. -/
@[expose]
def armShiftAlu (w : Nat) (c : OpCode [.bits w, .bits w] [.bits w]) (ra rb : Reg) (sh : AluShift)
    (k : Nat) (rd : Reg) : Option (List Directive × FlagMask) :=
  armShiftedAlu? w c ra rb (armAluShift sh) k rd

/-! ## 2. Shifted-Register `CMP` (`SUBS_s`) -/

/-- Shared destination finalizer for NZCV-setting comparisons (`SUBS_s`/`SUBS_e`). -/
@[expose]
def armCmpFinish (cmpIns : Instr) (cond : ArmCond) (dst : PDst Reg Empty ArmCond .bool) :
    Option (List Instr × FlagMask) :=
  match dst with
  | .flag c => if c == cond then some ([cmpIns], maskNZCV) else none
  | .gpr (.reg d) => some ([cmpIns, armCset64I d cond], maskNZCV)
  | .gpr .SP | .vec _ => none

/-- Emit `SUBS_s xzr/wzr, lhs, rhs, <sh> #k` (using `o.swap` when `lhsShift = true`). -/
@[expose]
def armShiftedCmpInstrI (rw : RegWidth) (baseR shiftR : XReg) (sh : ArmShiftOp) (k : Nat) :
    Instr :=
  armIselInsI (.SUBS_s (xzr rw) (zr baseR rw) (armShiftRegExpr rw shiftR sh k))

/-- Lower shifted comparison `lhs <o> rhs` into `SUBS_s` (+ optional `CSET`) when `w ∈ {32, 64}`
and `k < w`. When `lhsShift = true`, compares `(ra <sh> #k)` against `rb` using `o.swap`; when
`lhsShift = false`, compares `ra` against `(rb <sh> #k)` using `o`. -/
@[expose]
def armShiftedCmpIns (o : CmpOp) (w : Nat) (ra rb : Reg) (sh : ArmShiftOp) (k : Nat)
    (lhsShift : Bool) (dst : PDst Reg Empty ArmCond .bool) : Option (List Instr × FlagMask) :=
  if !Nat.blt k w then none
  else
    match armShiftWidth? w, armRegX? ra, armRegX? rb with
    | some rw, some a, some b =>
      let (baseR, shiftR, effOp) := if lhsShift then (b, a, o.swap) else (a, b, o)
      armCmpFinish (armShiftedCmpInstrI rw baseR shiftR sh k) (armCmpCond effOp) dst
    | _, _, _ => none

/-- Pure shifted-register `CMP` selection entry point returning clean directives and `maskNZCV`. -/
@[expose]
def armShiftedCmp? (o : CmpOp) (w : Nat) (ra rb : Reg) (sh : ArmShiftOp) (k : Nat)
    (lhsShift : Bool) (dst : PDst Reg Empty ArmCond .bool) :
    Option (List Directive × FlagMask) :=
  emitCleanPair (armShiftedCmpIns o w ra rb sh k lhsShift dst)

/-- `GprIsa.shiftCmp` adapter onto `armShiftedCmp?`. -/
@[expose]
def armShiftCmp (o : CmpOp) (w : Nat) (ra rb : Reg) (sh : AluShift) (k : Nat)
    (lhsShift : Bool) (dst : PDst Reg Empty ArmCond .bool) : Option (List Directive × FlagMask) :=
  armShiftedCmp? o w ra rb (armAluShift sh) k lhsShift dst

/-- Operand-order flag-reuse oracle (`some (!lhsShift)`) for `armShiftedCmp?`. -/
@[expose]
def armShiftedCmpFlagsOut (o : CmpOp) (w : Nat) (lhsShift : Bool)
    (dst : PDst Reg Empty ArmCond .bool) : Option Bool :=
  if !(w == 32 || w == 64) then none
  else
    let effOp := if lhsShift then o.swap else o
    match dst with
    | .gpr (.reg _) => some (!lhsShift)
    | .flag cf => if cf == armCmpCond effOp then some (!lhsShift) else none
    | .gpr .SP | .vec _ => none

/-! ## 3. Extended-Register ALU & `CMP` (`UXTB`..`SXTW`, Shift `0..4`) -/

/-- Supported AArch64 register-extension modes for `ADD_e`/`SUB_e`/`SUBS_e`. -/
inductive ArmExtType where
  | uxtb
  | sxtb
  | uxth
  | sxth
  | uxtw
  | sxtw
  deriving DecidableEq, Repr, BEq

/-- Map `ArmExtType` to Kraken's `ExtendType`. -/
@[expose]
def ArmExtType.toKraken : ArmExtType → ExtendType
  | .uxtb => .UXTB | .sxtb => .SXTB
  | .uxth => .UXTH | .sxth => .SXTH
  | .uxtw => .UXTW | .sxtw => .SXTW

/-- Source sub-word bit width (`8`, `16`, or `32`) read by `ArmExtType`. -/
@[expose]
def ArmExtType.srcBits : ArmExtType → Nat
  | .uxtb | .sxtb => 8
  | .uxth | .sxth => 16
  | .uxtw | .sxtw => 32

/-- Whether `ArmExtType` sign-extends (true) or zero-extends (false) bits `0..<srcBits>`. -/
@[expose]
def ArmExtType.isSigned : ArmExtType → Bool
  | .sxtb | .sxth | .sxtw => true
  | .uxtb | .uxth | .uxtw => false

/-- Pure bitvector semantics of extending `vb : BitVec e.srcBits` to width `w` and shifting left
by `k ≤ 4`. -/
@[expose]
def ArmExtType.eval {w : Nat} (e : ArmExtType) (vb : BitVec e.srcBits) (k : Nat) : BitVec w :=
  (if e.isSigned then vb.signExtend w else vb.zeroExtend w) <<< k

/-- Arithmetic opcodes supported by extended-register instruction selection (`add`, `sub`). -/
inductive ArmExtAluOp where
  | add
  | sub
  deriving DecidableEq, Repr, BEq

/-- Pure bitvector evaluation of `ArmExtAluOp` at width `w`. -/
@[expose]
def ArmExtAluOp.eval {w : Nat} : ArmExtAluOp → BitVec w → BitVec w → BitVec w
  | .add, a, b => a + b
  | .sub, a, b => a - b

/-- Match binary `OpCode` into `ArmExtAluOp`. -/
@[expose]
def armExtAluOfOpCode? :
    {w : Nat} → OpCode [.bits w, .bits w] [.bits w] → Option ArmExtAluOp
  | _, .add _ => some .add
  | _, .sub _ => some .sub
  | _, _      => none

/-- Shift amount `0..4` encoded as `ExtendAmount`. -/
@[expose]
def armExtShiftAmount? : Nat → Option ExtendAmount
  | 0 => some .E0 | 1 => some .E1 | 2 => some .E2 | 3 => some .E3 | 4 => some .E4
  | _ => none

/-- Build a 32-bit-source `ExtRegExpr` for `w_rb, <ext> #amt`. -/
@[expose]
def armExtRegExpr (rb : XReg) (e : ArmExtType) (amt : ExtendAmount) : ExtRegExpr :=
  { reg := ⟨.W32, zr rb .W32⟩, ext := { type := e.toKraken, amount := amt } }

/-- Emit `ADD_e` or `SUB_e` instruction `rd := ra <op> (rb <e> #amt)`. -/
@[expose]
def armExtAluInstrI (op : ArmExtAluOp) (rw : RegWidth) (rd ra rb : XReg)
    (e : ArmExtType) (amt : ExtendAmount) : Instr :=
  let src2 := ExtOrImmReg.ext (armExtRegExpr rb e amt)
  let oper : Operation rw := match op with
    | .add => .ADD_e (.low (.reg rd) rw) (.low (.reg ra) rw) src2
    | .sub => .SUB_e (.low (.reg rd) rw) (.low (.reg ra) rw) src2
  { operation_size := rw, operation := oper }

/-- Directive wrapper for `armExtAluInstrI`. -/
@[expose]
def armExtAluDirI (op : ArmExtAluOp) (rw : RegWidth) (rd ra rb : XReg)
    (e : ArmExtType) (amt : ExtendAmount) : Directive :=
  .instr (armExtAluInstrI op rw rd ra rb e amt)

/-- Lower an extended-register ALU op when `w ∈ {32, 64}`, `k ≤ 4`, and regs are GPRs. -/
@[expose]
def armExtAluIns (w : Nat) (c : OpCode [.bits w, .bits w] [.bits w])
    (ra rb : Reg) (e : ArmExtType) (k : Nat) (rd : Reg) : Option (List Instr) :=
  match armShiftWidth? w, armExtAluOfOpCode? c, armExtShiftAmount? k,
      armRegX? rd, armRegX? ra, armRegX? rb with
  | some rw, some op, some amt, some d, some a, some b =>
      some [armExtAluInstrI op rw d a b e amt]
  | _, _, _, _, _, _ => none

/-- Pure extended-register ALU selection returning clean directives and `maskNone`. -/
@[expose]
def armExtAlu? (w : Nat) (c : OpCode [.bits w, .bits w] [.bits w])
    (ra rb : Reg) (e : ArmExtType) (k : Nat) (rd : Reg) :
    Option (List Directive × FlagMask) :=
  emitCleanPair ((armExtAluIns w c ra rb e k rd).map (·, maskNone))

/-- Flag indicating 32-bit `armExtAlu?` zeroes upper 32 bits of `rd`. -/
@[expose]
def armZeroUpper32ExtAlu : Bool := true

/-- Emit `SUBS_e xzr/wzr, baseR, extR, <e> #amt`. -/
@[expose]
def armExtCmpInstrI (rw : RegWidth) (baseR extR : XReg) (e : ArmExtType)
    (amt : ExtendAmount) : Instr :=
  armIselInsI (.SUBS_e (xzr rw) (.low (.reg baseR) rw) (.ext (armExtRegExpr extR e amt)))

/-- Lower extended-register comparison into `SUBS_e` (+ optional `CSET`) when `w ∈ {32, 64}`
and `k ≤ 4`. When `lhsExt = true`, compares `(ra <e> #k)` against `rb` using `o.swap`. -/
@[expose]
def armExtCmpIns (o : CmpOp) (w : Nat) (ra rb : Reg) (e : ArmExtType) (k : Nat)
    (lhsExt : Bool) (dst : PDst Reg Empty ArmCond .bool) : Option (List Instr × FlagMask) :=
  match armShiftWidth? w, armExtShiftAmount? k, armRegX? ra, armRegX? rb with
  | some rw, some amt, some a, some b =>
    let (baseR, extR, effOp) := if lhsExt then (b, a, o.swap) else (a, b, o)
    armCmpFinish (armExtCmpInstrI rw baseR extR e amt) (armCmpCond effOp) dst
  | _, _, _, _ => none

/-- Pure extended-register `CMP` selection returning clean directives and `maskNZCV`. -/
@[expose]
def armExtCmp? (o : CmpOp) (w : Nat) (ra rb : Reg) (e : ArmExtType) (k : Nat)
    (lhsExt : Bool) (dst : PDst Reg Empty ArmCond .bool) :
    Option (List Directive × FlagMask) :=
  emitCleanPair (armExtCmpIns o w ra rb e k lhsExt dst)

/-- Operand-order flag-reuse oracle (`some (!lhsExt)`) for `armExtCmp?`. -/
@[expose]
def armExtCmpFlagsOut (o : CmpOp) (w : Nat) (lhsExt : Bool)
    (dst : PDst Reg Empty ArmCond .bool) : Option Bool :=
  armShiftedCmpFlagsOut o w lhsExt dst

end LeanQbe.T.Arm64
