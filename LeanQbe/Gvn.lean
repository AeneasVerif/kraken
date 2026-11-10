module

public import LeanQbe.Fold

/-!
# Common-subexpression elimination of pure operations in lexical scope (QBE `gvn.c`, simplified)

`gvn n next tbl : Expr (Arg V × Key) L → Expr V L` reads its input at `V' := Arg V × Key`: an input
variable stands for the operand that replaces it, and for its *key*, a symbolic name. Keys are
`Arg Nat`: `.var i` for the `i`-th value defined so far (a counter `next`, since variables of an arbitrary
`V` cannot be compared), or an immediate. `tbl` maps an operation over keys to the operand and key of the
value that computed it. Then:

* `%x = op` whose key-level operation is in the table: `%x` becomes the earlier value, no instruction;
* otherwise `op` is kept, and recorded under the fresh key `next`.

The table is passed down the term, so it holds exactly the operations that were executed before the
current point on every path (lexical scope = dominance for this IL). Like `fold`, nothing is removed while
labels are pending (`n > 0`). Loads, parameters and call results get fresh keys and no table entry.
Correctness: `GvnLemmas`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe

/-- The symbolic name of a value in `gvn`. -/
abbrev Key := Arg Nat

/-- The key of an operand of the input. -/
def Arg.key {V : Type} : Arg (Arg V × Key) → Key
  | .var p => p.2
  | .imm c => .imm c

/-- The output operand of an operand of the input. -/
def Arg.out {V : Type} : Arg (Arg V × Key) → Arg V
  | .var p => p.1
  | .imm c => .imm c

/-- Operations already computed, at the level of keys. -/
abbrev Tbl (V : Type) := List (Op Nat × (Arg V × Key))

def Tbl.find {V : Type} (ko : Op Nat) : Tbl V → Option (Arg V × Key)
  | [] => none
  | (o, r) :: t => if o = ko then some r else Tbl.find ko t

def gvn {V L : Type} (n next : Nat) (tbl : Tbl V) : Expr (Arg V × Key) L → Expr V L
  | .let_ op k =>
    let ko := op.mapArgs Arg.key
    if n = 0 then
      match tbl.find ko with
      | some r => gvn 0 next tbl (k r)
      | none =>
        .let_ (op.mapArgs Arg.out) fun v => gvn 0 (next + 1) ((ko, .var v, .var next) :: tbl) (k (.var v, .var next))
    else
      .let_ (op.mapArgs Arg.out) fun v => gvn 0 (next + 1) ((ko, .var v, .var next) :: tbl) (k (.var v, .var next))
  | .load c s sg a k => .load c s sg a.out fun v => gvn 0 (next + 1) tbl (k (.var v, .var next))
  | .store s v a k => .store s v.out a.out (gvn 0 next tbl k)
  | .call f as k => .call f (as.map Arg.out) (gvn 0 next tbl k)
  | .jnz c t e => .jnz c.out (gvn 0 next tbl t) (gvn 0 next tbl e)
  | .jump j as => .jump j (as.map Arg.out)
  | .ret vs => .ret (vs.map Arg.out)
  | .exit f as => .exit f (as.map Arg.out)
  | .hlt => .hlt
  | .param f => .param fun v => gvn 0 (next + 1) tbl (f (.var v, .var next))
  | .label f => .label fun j => gvn (n + 1) next tbl (f j)
  | .block b r => .block (gvn 0 next tbl b) (gvn (n - 1) next tbl r)

def Func.gvn (f : Func) : Func := fun V L => LeanQbe.gvn 0 0 [] (f (Arg V × Key) L)

end LeanQbe
