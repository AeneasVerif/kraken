module

public import Kraken.Mem

/-!
# Operations (QBE `ops.h`)

The integer operations of QBE's IL and their semantics on single-sorted values (decision D3).

* Every SSA value is a `Val = BitVec 64`. The width lives on the operation: a class `Cls.w` or `Cls.l`.
* An operation of class `w` reads the low 32 bits of its operands and **zero-extends** its result.
* Shift counts are masked (to 5 bits for `w`, 6 bits for `l`), as on x64 and AArch64.
* Division and remainder are undefined (`none`) on a zero divisor, and signed division and remainder
  also on `intMin / -1` (x64 `idiv` traps there).
* Comparisons produce `0` or `1`; their class says how many operand bits are compared.
* Operands are `Arg V`: a variable or an immediate, as QBE's `Ref` (`RTmp` / `RCon`).

Memory accesses (`load`, `store`) are not operations here but constructors of the IL term (`IL.lean`),
so that every `Op` is pure. Their semantics on Kraken's `Mem 64` is at the end of this file and matches
Kraken's x64 and AArch64 `MachineData.load` / `MachineData.store` (`Mem.loadInt`, `Mem.storeInt`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe

/-- Every SSA value (decision D3). -/
abbrev Val := BitVec 64

/-- QBE base class of an integer operation (`Kw`, `Kl`). -/
inductive Cls
  | w
  | l
  deriving DecidableEq, Repr, Inhabited

/-- Memory access width (QBE extended types `b h w l`). -/
inductive Sz
  | b
  | h
  | w
  | l
  deriving DecidableEq, Repr, Inhabited

def Sz.bytes : Sz → Nat
  | .b => 1
  | .h => 2
  | .w => 4
  | .l => 8

/-- Binary integer operations of `ops.h` ("Arithmetic and Bits"). `neg` is `sub 0 x`. -/
inductive BinOp
  | add | sub | mul | div | rem | udiv | urem | and | or | xor | sar | shr | shl
  deriving DecidableEq, Repr, Inhabited

/-- Integer comparisons of `ops.h` (`ceq`, `cne`, `csle`, ...); the class is on `Op.cmp`. -/
inductive CmpOp
  | eq | ne | sle | slt | sge | sgt | ule | ult | uge | ugt
  deriving DecidableEq, Repr, Inhabited

/-- An operand: a variable or an immediate (QBE `Ref`). -/
inductive Arg (V : Type) : Type
  | var (v : V)
  | imm (c : Val)
  deriving DecidableEq, Repr, Inhabited

/-- Pure operations. The result class of `bin`, `ext`, `copy` is `k`; `cmp` always yields `0` or `1`. -/
inductive Op (V : Type) : Type
  /-- `%r =k o a, b` -/
  | bin (k : Cls) (o : BinOp) (a b : Arg V)
  /-- `%r =w c{o}{k} a, b`: compare the low `k` bits of `a` and `b`. -/
  | cmp (k : Cls) (o : CmpOp) (a b : Arg V)
  /-- `%r =k ext{s|u}{s} a`: sign- or zero-extend the low `s` bits of `a` (`extsb` ... `extuw`). -/
  | ext (k : Cls) (s : Sz) (signed : Bool) (a : Arg V)
  /-- `%r =k copy a` -/
  | copy (k : Cls) (a : Arg V)
  deriving DecidableEq, Repr, Inhabited

/-! ## Names, as printed in QBE IL -/

def Cls.name : Cls → String
  | .w => "w"
  | .l => "l"

def Sz.name : Sz → String
  | .b => "b"
  | .h => "h"
  | .w => "w"
  | .l => "l"

def BinOp.name : BinOp → String
  | .add => "add" | .sub => "sub" | .mul => "mul" | .div => "div" | .rem => "rem"
  | .udiv => "udiv" | .urem => "urem" | .and => "and" | .or => "or" | .xor => "xor"
  | .sar => "sar" | .shr => "shr" | .shl => "shl"

def CmpOp.name : CmpOp → String
  | .eq => "eq" | .ne => "ne" | .sle => "sle" | .slt => "slt" | .sge => "sge" | .sgt => "sgt"
  | .ule => "ule" | .ult => "ult" | .uge => "uge" | .ugt => "ugt"

/-! ## Semantics -/

/-- The value of an operand, once variables are values. -/
def Arg.val : Arg Val → Val
  | .var v => v
  | .imm c => c

def Arg.map {V W : Type} (f : V → W) : Arg V → Arg W
  | .var v => .var (f v)
  | .imm c => .imm c

/-- Signed division and remainder are undefined on a zero divisor and on `intMin / -1`. -/
def sdivDefined {n : Nat} (a b : BitVec n) : Bool :=
  b != 0 && !(a == BitVec.intMin n && b == BitVec.allOnes n)

/-- A binary operation at bit width `n`; `none` means undefined behaviour. -/
def BinOp.eval {n : Nat} : BinOp → BitVec n → BitVec n → Option (BitVec n)
  | .add, a, b => some (a + b)
  | .sub, a, b => some (a - b)
  | .mul, a, b => some (a * b)
  | .div, a, b => if sdivDefined a b then some (a.sdiv b) else none
  | .rem, a, b => if sdivDefined a b then some (a.srem b) else none
  | .udiv, a, b => if b = 0 then none else some (a / b)
  | .urem, a, b => if b = 0 then none else some (a % b)
  | .and, a, b => some (a &&& b)
  | .or, a, b => some (a ||| b)
  | .xor, a, b => some (a ^^^ b)
  | .sar, a, b => some (a.sshiftRight (b.toNat % n))
  | .shr, a, b => some (a >>> (b.toNat % n))
  | .shl, a, b => some (a <<< (b.toNat % n))

def CmpOp.eval {n : Nat} : CmpOp → BitVec n → BitVec n → Bool
  | .eq, a, b => a == b
  | .ne, a, b => a != b
  | .sle, a, b => a.sle b
  | .slt, a, b => a.slt b
  | .sge, a, b => b.sle a
  | .sgt, a, b => b.slt a
  | .ule, a, b => a.ule b
  | .ult, a, b => a.ult b
  | .uge, a, b => b.ule a
  | .ugt, a, b => b.ult a

/- `grind` proves bit-vector facts in `Nat` and `Int`, through its `[grind hom]` rules. The default
rules cover the signed comparisons; these add the sign bit and the unsigned comparisons. -/
attribute [grind hom] BitVec.msb_eq_toInt BitVec.ult_eq_decide BitVec.ule_eq_decide

/-- Low 32 bits. -/
abbrev lo32 (x : Val) : BitVec 32 := x.setWidth 32

/-- Zero-extension of a 32-bit result. -/
abbrev zext32 (x : BitVec 32) : Val := x.setWidth 64

/-- Result normalisation of class `k`: `w` results are zero-extended from 32 bits. -/
def Cls.trunc : Cls → Val → Val
  | .w, x => zext32 (lo32 x)
  | .l, x => x

/-- Sign- or zero-extend the low `s` bits. -/
def Sz.extend : Sz → Bool → Val → Val
  | .b, true, x => (x.setWidth 8).signExtend 64
  | .b, false, x => (x.setWidth 8).setWidth 64
  | .h, true, x => (x.setWidth 16).signExtend 64
  | .h, false, x => (x.setWidth 16).setWidth 64
  | .w, true, x => (x.setWidth 32).signExtend 64
  | .w, false, x => (x.setWidth 32).setWidth 64
  | .l, _, x => x

def boolVal (b : Bool) : Val := if b then 1 else 0

/-- Semantics of a pure operation; `none` is undefined behaviour. -/
def Op.eval : Op Val → Option Val
  | .bin .l o a b => o.eval a.val b.val
  | .bin .w o a b => (o.eval (lo32 a.val) (lo32 b.val)).map zext32
  | .cmp .l o a b => some (boolVal (o.eval a.val b.val))
  | .cmp .w o a b => some (boolVal (o.eval (lo32 a.val) (lo32 b.val)))
  | .ext k s sg a => some (k.trunc (s.extend sg a.val))
  | .copy k a => some (k.trunc a.val)

/-- Continuation form, as used by `wp`. -/
def Op.wp (op : Op Val) (post : Val → Prop) : Prop :=
  ∃ v, op.eval = some v ∧ post v

def Op.map {V W : Type} (f : V → W) : Op V → Op W
  | .bin k o a b => .bin k o (a.map f) (b.map f)
  | .cmp k o a b => .cmp k o (a.map f) (b.map f)
  | .ext k s sg a => .ext k s sg (a.map f)
  | .copy k a => .copy k (a.map f)

/-! ## Memory (Kraken's `Mem 64`) -/

/-- `load{s}{sg}` at `a`: the bytes must be mapped. The result is extended per `sg` and normalised per
class `k`. For `Sz.l` and `Sz.w` (unsigned) this is exactly `BitVec.ofInt` of Kraken's `Mem.loadInt`. -/
def loadVal (m : Mem 64) (k : Cls) (s : Sz) (sg : Bool) (a : Val) : Option Val :=
  (m.loadInt a s.bytes).map fun i => k.trunc (s.extend sg (BitVec.ofInt 64 i))

/-- `store{s} v, a` writes the low `s` bytes of `v`, as Kraken's `MachineData.store` at that width. -/
def storeMem (m : Mem 64) (s : Sz) (a v : Val) : Mem 64 :=
  match s with
  | .b => m.storeInt a 1 (v.setWidth 8).toInt
  | .h => m.storeInt a 2 (v.setWidth 16).toInt
  | .w => m.storeInt a 4 (v.setWidth 32).toInt
  | .l => m.storeInt a 8 v.toInt

/-- A store is defined iff the target bytes are mapped (Kraken checks this with `Mem.loadInt`). -/
def storeOk (m : Mem 64) (s : Sz) (a : Val) : Prop :=
  ∃ i, m.loadInt a s.bytes = some i

end LeanQbe
