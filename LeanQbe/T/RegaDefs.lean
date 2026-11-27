module

public import LeanQbe.T.Target

/-!
# Shared Types, Symbolic State, and Pure Predicates for `Rega`

Factored out of `LeanQbe.T.Rega` so helper modules (`RegaZext`, `Live`) and `Rega` share the exact
`LeanQbe.T.Rega` data definitions (`RegLoc`, `SlotEntry`, `DefFact`, `SymState`, `findGprFor`)
while keeping every module well under 2,500 lines.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T
namespace Rega

abbrev VNat : Ty → Type := fun _ => Nat
abbrev LNat : List Ty → Type := fun _ => Nat

inductive RegLoc (Reg VReg Cond : Type) where
  | gpr (r : Reg) | gprZ (r : Reg) | vec (v : VReg) | flag (c : Cond)
  deriving DecidableEq, Repr

inductive SlotEntry where
  | gpr (sas : List SymArg)
  | gprZ (sas : List (SymArg × Bool))
  | vec (w : SlotWidth) (sas : List SymArg)
  deriving DecidableEq, Repr

def SlotEntry.slots : SlotEntry → Nat
  | .gpr _ | .gprZ _ => 1 | .vec w _ => w.slots

inductive RmwOp where
  | add | sub | and | or | xor
  deriving DecidableEq, Repr

def RmwOp.toOpCode (w : Nat) : RmwOp → OpCode [.bits w, .bits w] [.bits w]
  | .add => .add (.bits w)
  | .sub => .sub (.bits w)
  | .and => .and (.bits w)
  | .or  => .or  (.bits w)
  | .xor => .xor (.bits w)

def RmwOp.isComm : RmwOp → Bool
  | .add | .and | .or | .xor => true
  | .sub => false

inductive DefFact where
  | addImm64 (base : Nat) (disp : BitVec 64)
  | scaleOff (idx : Nat) (sh : Nat) (disp : BitVec 64)
  | addrSum (base idx : Nat) (sh : Nat) (disp : BitVec 64)
  | imm64 (c : BitVec 64)
  | andVarVar (w x y : Nat)
  | andVarImm (w x : Nat) (c : BitVec 64)
  | binVarVar (w : Nat) (op : RmwOp) (x y : Nat)
  | binVarImm (w : Nat) (op : RmwOp) (x : Nat) (c : BitVec 64)
  | sextVar (m n x : Nat)
  | zextVar (m n x : Nat)
  | cmpZeroVar (co : CmpOp) (w x : Nat)
  | testBitVar (neg : Bool) (w x : Nat) (c : BitVec 64)
  | shlVarImm (w x sh : Nat)
  /-- `x` shifted right (`sk ∈ {lsr, asr}`) by an immediate `k < w` at width `w`. -/
  | shiftVarImm (w : Nat) (sk : AluShift) (x k : Nat)
  | negVar (w x : Nat)
  deriving DecidableEq, Repr

/-- `recordDef` fact of `lshr`/`ashr (.bits n) (.var x) (.imm k)`. -/
def recordShiftImm (n : Nat) (sk : AluShift) (x : Nat) (k : BitVec n) : Option DefFact :=
  if Nat.ble n 64 && Nat.blt k.toNat n then some (.shiftVarImm n sk x k.toNat) else none

def DefFact.isAddr : DefFact → Bool
  | .imm64 _ | .addImm64 _ _ | .scaleOff _ _ _ | .addrSum _ _ _ _ => true
  | _ => false

inductive FlagFact where
  | cmp (w : Nat) (lhs rhs : SymArg) (eqNeOnly : Bool)
  deriving DecidableEq, Repr

structure SymState (I : Isa) where
  regs : List (SymArg × RegLoc I.Reg I.VReg I.Cond)
  slots : Trie SlotEntry
  defs : Trie DefFact
  vecWidths : Trie SlotWidth
  memDefs : Trie (Ty × Arg VNat i64) := .empty
  zeroExt32 : List I.Reg := []
  flags : Option FlagFact := none
  scrConsts : List (I.Reg × BitVec 64) := []

structure Ext where
  callees : List (Sym × List Ty × List Ty) := []
  exits : List Sym := []
  deriving DecidableEq, Repr, Inhabited

abbrev Res (I : Isa) := Except String (List I.Directive × Nat × Nat × Nat)

/-! ## Pure `Bool` Equalities, Labels, and Bank Predicates -/

def slotWidthEq : SlotWidth → SlotWidth → Bool
  | .w64, .w64 | .w128, .w128 | .w256, .w256 | .w512, .w512 => true
  | _, _ => false

def symArgEq : SymArg → SymArg → Bool
  | .var x, .var y => Nat.beq x y
  | .immBool a, .immBool b => Bool.beq a b
  | .immBits w1 c1, .immBits w2 c2 => Nat.beq w1 w2 && c1 == c2
  | .immVec w1 c1, .immVec w2 c2 => slotWidthEq w1 w2 && c1 == c2
  | _, _ => false

def regLocEq {I : Isa} : RegLoc I.Reg I.VReg I.Cond → RegLoc I.Reg I.VReg I.Cond → Bool
  | .gpr a, .gpr b | .gprZ a, .gprZ b => a == b
  | .vec a, .vec b => a == b
  | .flag a, .flag b => a == b
  | _, _ => false

def regLocMatchesGpr {I : Isa} (rl : RegLoc I.Reg I.VReg I.Cond) (r : I.Reg) : Bool :=
  match rl with
  | .gpr r' | .gprZ r' => r' == r
  | _ => false

def locEq {I : Isa} : I.Loc → I.Loc → Bool
  | .gpr a, .gpr b => a == b | .vec a, .vec b => a == b | .flag a, .flag b => a == b
  | .slot i w1, .slot j w2 => Nat.beq i j && slotWidthEq w1 w2
  | _, _ => false

def tyEq : Ty → Ty → Bool
  | .bool, .bool => true | .bits m, .bits n => Nat.beq m n | .float f, .float g => f == g
  | .pair a1 b1, .pair a2 b2 => tyEq a1 a2 && tyEq b1 b2 | _, _ => false

def listTyEq : List Ty → List Ty → Bool
  | [], [] => true | x :: xs, y :: ys => tyEq x y && listTyEq xs ys | _, _ => false

def natDigits : Nat → Nat → List Char → List Char
  | 0, _, acc => acc
  | fuel + 1, n, acc =>
    let acc := Char.ofNat (48 + n % 10) :: acc
    if Nat.ble 10 n then natDigits fuel (n / 10) acc else acc

def lname (fn : Sym) (n : Nat) : Sym :=
  ".L" ++ fn ++ "." ++ String.ofList (natDigits (n + 1) n [])

def isGprTy (I : Isa) : Ty → Bool
  | .bool => true | .bits n => I.frame.bitWidths.contains n && Nat.ble n 64 | _ => false

def vecWidth? (I : Isa) : Ty → Option SlotWidth
  | .pair a b =>
    match I.vec.vecSlotWidth (.pair a b) with
    | some w => if Nat.ble (Ty.pair a b).size w.bits then some w else none
    | none => none
  | _ => none

def isAllocGpr (I : Isa) (saved : List I.Reg) (r : I.Reg) : Bool :=
  I.frame.allocatable.contains r || saved.contains r ||
    I.frame.argRegs.contains r || I.frame.retRegs.contains r

def isMoveGpr (I : Isa) (saved : List I.Reg) (r : I.Reg) : Bool :=
  isAllocGpr I saved r || I.frame.scratch.contains r

def isAllocVec (I : Isa) (v : I.VReg) : Bool :=
  I.vec.vecAllocatable.contains v || I.vec.vecArgRegs.contains v || I.vec.vecRetRegs.contains v

def isMoveVec (I : Isa) (v : I.VReg) : Bool := isAllocVec I v || I.vec.vecScratch.contains v

def toSymArg (I : Isa) : (t : Ty) → Arg VNat t → Option SymArg
  | _, .var x => some (.var x)
  | .bool, .imm b => some (.immBool b)
  | .bits n, .imm c => if Nat.ble n 64 then some (.immBits n (c.setWidth 64)) else none
  | .pair a b, .imm c =>
    (vecWidth? I (.pair a b)).map fun w => .immVec w ((toBits (.pair a b) c).setWidth 512)
  | .float _, .imm _ => none

def symArgWidth (vw : Trie SlotWidth) : SymArg → Option SlotWidth
  | .var x => vw.find? x | .immVec w _ => some w | _ => none

def symArgMatchesGpr (stored target : SymArg) : Bool :=
  if symArgEq stored target then true
  else match stored, target with
    | .immBits w' c, .immBits w k => Nat.beq w' 64 && Nat.ble w 64 && c == k
    | .immBits w' c, .immBool b => Nat.beq w' 64 && c == (if b then 1#64 else 0#64)
    | _, _ => false

def symArgScopeOk (nv : Nat) : SymArg → Bool
  | .var x => Nat.ble (x + 1) nv | _ => true

def entryScopeOk {I : Isa} (nv : Nat) (en : Entry I.Reg I.VReg I.Cond) : Bool :=
  en.live.all fun (sa, _) => symArgScopeOk nv sa

def findGprFor (I : Isa) (noScr : Bool)
    (R : List (SymArg × RegLoc I.Reg I.VReg I.Cond)) (sa : SymArg) : Option I.Reg :=
  R.findSome? fun (sa', rl) =>
    match rl with
    | .gpr r | .gprZ r =>
      if (!noScr || !(I.frame.scratch.contains r)) && symArgMatchesGpr sa' sa then some r
      else none
    | _ => none

end Rega
end LeanQbe.T
