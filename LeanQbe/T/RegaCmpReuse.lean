module

public import LeanQbe.T.RegaDefs

/-!
# Narrow/Wide Comparison Normalization and Flag-Reuse Matching (`C-P1.3`)

Extracted from `LeanQbe.T.Rega` to keep every file well under `2,500` LOC:
* `cmpIsSignedOrEq` / `cmpIsUnsignedOrEq`: predicates whose `sext`/`zext` constant-roundtrip
  soundness justifies width-crossing compare reuse.
* `reuseCmpPair?`: matches an in-progress scalar `.bits n` compare `(co, a, b)` against an active
  width-`w` `FlagFact` (`lhs`, `rhs`) across:
  - exact width (`w = n`),
  - narrow flag / wide consumer (`0 < w < n` via consumer `sextVar`/`zextVar` in `defs`), and
  - wide flag / narrow consumer (`0 < n < w` via flag `lhs`/`rhs` `sextVar`/`zextVar` in `defs`).
* `cmpZeroFlagCond?`: deferred zero-compare `jnz` flag reuse routed through `reuseCmpPair?`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T
namespace Rega

def cmpIsSignedOrEq : CmpOp → Bool
  | .eq | .ne | .slt | .sle | .sgt | .sge => true
  | _ => false

def cmpIsUnsignedOrEq : CmpOp → Bool
  | .eq | .ne | .ult | .ule | .ugt | .uge => true
  | _ => false

def reuseWideSide? (defs : Trie DefFact) (w n : Nat) (co' : CmpOp) (x0 : Nat) (cn : BitVec n)
    (side other : SymArg) : Option (CmpOp × SymArg × SymArg) :=
  match side, other with
  | .var t, .immBits w' cw64 =>
    if !Nat.beq w' w then none
    else
      let cw := cw64.setWidth w
      let ok := match defs.find? t with
        | some (.sextVar m w'' x) =>
          Nat.beq m n && Nat.beq w'' w && Nat.beq x0 x &&
            cmpIsSignedOrEq co' && cw.truncate n == cn &&
            (cw.truncate n).signExtend w == cw
        | some (.zextVar m w'' x) =>
          Nat.beq m n && Nat.beq w'' w && Nat.beq x0 x &&
            cmpIsUnsignedOrEq co' && cw.truncate n == cn &&
            (cw.truncate n).zeroExtend w == cw
        | _ => false
      if ok then some (co', .var t, other) else none
  | _, _ => none

def normZeroCmp : CmpOp → CmpOp
  | .ugt => .ne
  | .ule => .eq
  | o => o

def normCmpZero1 {n : Nat} (o : CmpOp) (c : BitVec n) : CmpOp × BitVec n :=
  if c == 0#n then (normZeroCmp o, 0#n)
  else if c == 1#n && Nat.ble 1 n then
    match o with
    | .ult => (.eq, 0#n)
    | .uge => (.ne, 0#n)
    | .sge => if Nat.ble 2 n then (.sgt, 0#n) else (o, c)
    | .slt => if Nat.ble 2 n then (.sle, 0#n) else (o, c)
    | _ => (o, c)
  else (o, c)

def normCmpExpr (co : CmpOp) (n : Nat) :
    Arg VNat (.bits n) → Arg VNat (.bits n) → CmpOp × Arg VNat (.bits n) × Arg VNat (.bits n)
  | .var t, .imm c =>
    let (co', c') := normCmpZero1 co c
    (co', .var t, .imm c')
  | .imm c, .var t =>
    let (co', c') := normCmpZero1 co.swap c
    if c' == 0#n then (co', .var t, .imm 0#n) else (co, .imm c, .var t)
  | a, b => (co, a, b)

def reuseCmpPair? (I : Isa) (defs : Trie DefFact) (w : Nat) (lhs rhs : SymArg)
    (n : Nat) (co : CmpOp) (a b : Arg VNat (.bits n)) : Option (CmpOp × SymArg × SymArg) :=
  let (co, a, b) := normCmpExpr co n a b
  if Nat.beq w n then
    (toSymArg I (.bits n) a).bind fun sa =>
      (toSymArg I (.bits n) b).map fun sb => (co, sa, sb)
  else if Nat.blt 0 w && Nat.blt w n then
    let ext? (co' : CmpOp) (t : Nat) (c : BitVec n) :=
      let ok := match defs.find? t with
        | some (.sextVar m n' x) =>
          if Nat.beq m w && Nat.beq n' n && cmpIsSignedOrEq co' &&
             (c.truncate w).signExtend n == c then some x else none
        | some (.zextVar m n' x) =>
          if Nat.beq m w && Nat.beq n' n && cmpIsUnsignedOrEq co' &&
             (c.truncate w).zeroExtend n == c then some x else none
        | _ => none
      ok.map fun x => (co', .var x, .immBits w ((c.truncate w).setWidth 64))
    match a, b with
    | .var t, .imm c => ext? co t c
    | .imm c, .var t => ext? co.swap t c
    | _, _ => none
  else if Nat.blt 0 n && Nat.blt n w then
    match a, b with
    | .var x, .imm cn =>
      reuseWideSide? defs w n co x cn lhs rhs <|> reuseWideSide? defs w n co x cn rhs lhs
    | .imm cn, .var x =>
      reuseWideSide? defs w n co.swap x cn lhs rhs <|>
        reuseWideSide? defs w n co.swap x cn rhs lhs
    | _, _ => none
  else none

def cmpZeroFlagCond? (I : Isa) (defs : Trie DefFact) (fl : Option FlagFact)
    (co : CmpOp) (w y : Nat) : Option I.Cond :=
  match fl with
  | some (.cmp w' lhs rhs eqNe) =>
    (reuseCmpPair? I defs w' lhs rhs w co (.var y) (.imm 0#w)).bind fun (coBase, sa, sb) =>
      let coUsed? :=
        if symArgEq sa lhs && symArgEq sb rhs then some coBase
        else if symArgEq sb lhs && symArgEq sa rhs then some coBase.swap
        else none
      coUsed?.bind fun coU =>
        if !eqNe || coU == .eq || coU == .ne then I.gpr.condOfCmp? coU else none
  | none => none

end Rega
end LeanQbe.T
