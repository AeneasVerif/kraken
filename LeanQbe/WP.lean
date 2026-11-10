module

public import LeanQbe.IL

/-!
# Weakest precondition of the IL

The structural `wp` of E1, extended with operands, memory (Kraken's `Mem 64`), calls and exits.

`wp Γ Q X e args acc m`:
* `Γ` gives a contract to every global symbol that may be called;
* `Q rets m'` is the return postcondition, `X f args m'` the exit postcondition (decision D5);
* `args` are the arguments still to be consumed by `param`s (block, function or call-result parameters);
* `acc` are the join points declared by `label` and not yet defined by `block`, oldest first.

It is total correctness: `wp` holds only if every run terminates by `ret` (in `Q`) or `exit` (in `X`),
never reaching undefined behaviour (an undefined `Op`, an unmapped `load` / `store`, `hlt`, an arity
mismatch, a junk shape). Loops terminate because a join point `J` is universally quantified and
constrained only by "the body of the block implies `J`": `wp` asks for the least such predicate.

A call needs only *some* contract `P E` of the callee that implies the continuation, so `wp` is
monotone without any hypothesis on `Γ`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe

/-- The meaning of a join point: a predicate on its arguments and the memory. -/
abbrev Cont := List Val → Mem 64 → Prop
/-- Return postcondition: results and final memory. -/
abbrev Post := List Val → Mem 64 → Prop
/-- Exit postcondition: the symbol jumped to, its arguments, the memory (decision D5). -/
abbrev XPost := Sym → List Val → Mem 64 → Prop
/-- A function contract: `spec args m Q X` says that every run from `args` and `m` returns in `Q` or
exits in `X`. -/
abbrev Spec := List Val → Mem 64 → Post → XPost → Prop
/-- Contracts of the global symbols. -/
abbrev Env := Sym → Spec

/-- `jnz` takes the first branch iff the low 32 bits of its argument are nonzero (QBE: the argument is
used at class `w`). -/
def Truthy (c : Val) : Prop := lo32 c ≠ 0

instance (c : Val) : Decidable (Truthy c) := inferInstanceAs (Decidable (¬ _))

def wp (Γ : Env) (Q : Post) (X : XPost) : Expr Val Cont → List Val → List Cont → Mem 64 → Prop
  | .let_ op k, args, _, m => args = [] ∧ op.wp (fun v => wp Γ Q X (k v) [] [] m)
  | .load c s sg a k, args, _, m =>
      args = [] ∧ ∃ v, loadVal m c s sg a.val = some v ∧ wp Γ Q X (k v) [] [] m
  | .store s v a k, args, _, m =>
      args = [] ∧ storeOk m s a.val ∧ wp Γ Q X k [] [] (storeMem m s a.val v.val)
  | .call f as k, args, _, m =>
      args = [] ∧ ∃ (P : Post) (E : XPost), Γ f (as.map Arg.val) m P E ∧
        (∀ rs m', P rs m' → wp Γ Q X k rs [] m') ∧ (∀ g xs m', E g xs m' → X g xs m')
  | .jnz c t e, args, _, m =>
      args = [] ∧ (Truthy c.val → wp Γ Q X t [] [] m) ∧ (¬ Truthy c.val → wp Γ Q X e [] [] m)
  | .jump j as, args, _, m => args = [] ∧ j (as.map Arg.val) m
  | .ret vs, args, _, m => args = [] ∧ Q (vs.map Arg.val) m
  | .exit f as, args, _, m => args = [] ∧ X f (as.map Arg.val) m
  | .hlt, _, _, _ => False
  | .param _, [], _, _ => False
  | .param f, a :: as, _, m => wp Γ Q X (f a) as [] m
  | .label f, args, acc, m => args = [] ∧ ∀ J : Cont, wp Γ Q X (f J) [] (acc ++ [J]) m
  | .block b rest, args, acc, m =>
      args = [] ∧
      match acc with
      | [] => False
      | J :: acc' => (∀ as m', wp Γ Q X b as [] m' → J as m') → wp Γ Q X rest [] acc' m

/-- The contract a function body satisfies by its `wp`. -/
def Func.spec (Γ : Env) (f : Func) : Spec :=
  fun args m Q X => wp Γ Q X (f Val Cont) args [] m

end LeanQbe
