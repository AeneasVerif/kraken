module

public import LeanQbe.T.Arm64.Base
public import LeanQbe.T.IselStepAttr

/-!
# Arm64 Shifted-Register ALU Selection

Pure instruction selection for Arm64 shifted-register 32-bit and 64-bit ALU instructions
(`ADD_s`, `SUB_s`, `AND_s`, `ORR_s`, `EOR_s`). This sibling module is kept free of `*Lemmas*`
and `Arm64.Isel` imports so `Arm64.Isel` can wire `GprIsa.shiftedAlu?` cleanly without cycles.
-/

public section

namespace LeanQbe.T.Arm64

/-- Supported barrel-shifter operations on the second GPR operand in Arm64 shifted ALU ops. -/
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

/-- Arm64 hardware register widths accepted by shifted-register ALU lowering. -/
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

end LeanQbe.T.Arm64
