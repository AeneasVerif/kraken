module

public import LeanQbe.WP

/-!
# Constant folding and copy propagation (QBE `fold.c`, `copy.c`), PHOAS to PHOAS

`fold : Expr (Arg V) L → Expr V L` reads its input at `V' := Arg V`: every input variable stands for the
operand that replaces it in the output. So substitution is instantiation, and the pass is one structural
recursion:

* `%x = op` with all operands immediate and `op` defined: `%x` becomes that immediate, no instruction;
* `%x =l copy a`: `%x` becomes `a`, no instruction;
* `jnz c` with an immediate `c`: only the taken branch is kept;
* everything else is kept, with operands substituted.

An undefined constant operation (division by zero) is kept, so that the output is undefined there too.
Correctness (`FoldLemmas`): the source `wp` implies the `wp` of the output, and `Wf` is preserved.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe

def Arg.join {V : Type} : Arg (Arg V) → Arg V
  | .var a => a
  | .imm c => .imm c

def Arg.imm? {V : Type} : Arg V → Option Val
  | .var _ => none
  | .imm c => some c

def Op.mapArgs {V W : Type} (f : Arg V → Arg W) : Op V → Op W
  | .bin k o a b => .bin k o (f a) (f b)
  | .cmp k o a b => .cmp k o (f a) (f b)
  | .ext k s sg a => .ext k s sg (f a)
  | .copy k a => .copy k (f a)

def Op.join {V : Type} : Op (Arg V) → Op V := Op.mapArgs Arg.join

/-- The operation with all operands immediate, if they are. -/
def Op.toImm? {V : Type} : Op V → Option (Op Val)
  | .bin k o a b => do let a ← a.imm?; let b ← b.imm?; pure (.bin k o (.imm a) (.imm b))
  | .cmp k o a b => do let a ← a.imm?; let b ← b.imm?; pure (.cmp k o (.imm a) (.imm b))
  | .ext k s sg a => do let a ← a.imm?; pure (.ext k s sg (.imm a))
  | .copy k a => do let a ← a.imm?; pure (.copy k (.imm a))

/-- The value of an operation whose operands are all immediate and which is defined. -/
def Op.constVal? {V : Type} (op : Op V) : Option Val := op.toImm?.bind Op.eval

/-- `copy` at class `l` is the identity. -/
def Op.copyL? {V : Type} : Op V → Option (Arg V)
  | .copy .l a => some a
  | _ => none

/-- `fold n e`: `n` is the number of labels declared and not yet defined at `e` (statically known;
it is the length of `wp`'s `acc`). Instructions are only removed where `n = 0`: removing one elsewhere
would let pending labels reach the code after it, which `wp` keeps from them (junk shapes). -/
def fold {V L : Type} (n : Nat) : Expr (Arg V) L → Expr V L
  | .let_ op k =>
    if n = 0 then
      match op.join.constVal? with
      | some c => fold 0 (k (.imm c))
      | none =>
        match op.join.copyL? with
        | some a => fold 0 (k a)
        | none => .let_ op.join fun v => fold 0 (k (.var v))
    else .let_ op.join fun v => fold 0 (k (.var v))
  | .load c s sg a k => .load c s sg a.join fun v => fold 0 (k (.var v))
  | .store s v a k => .store s v.join a.join (fold 0 k)
  | .call f as k => .call f (as.map Arg.join) (fold 0 k)
  | .jnz c t e =>
    if n = 0 then
      match c.join with
      | .imm c => if Truthy c then fold 0 t else fold 0 e
      | .var v => .jnz (.var v) (fold 0 t) (fold 0 e)
    else .jnz c.join (fold 0 t) (fold 0 e)
  | .jump j as => .jump j (as.map Arg.join)
  | .ret vs => .ret (vs.map Arg.join)
  | .exit f as => .exit f (as.map Arg.join)
  | .hlt => .hlt
  | .param f => .param fun v => fold 0 (f (.var v))
  | .label f => .label fun j => fold (n + 1) (f j)
  | .block b r => .block (fold 0 b) (fold (n - 1) r)

def Func.fold (f : Func) : Func := fun V L => LeanQbe.fold 0 (f (Arg V) L)

end LeanQbe
