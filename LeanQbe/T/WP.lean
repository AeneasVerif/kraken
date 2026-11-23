module

public import LeanQbe.T.IL

/-!
# Weakest precondition of the typed IL

Total-correctness weakest precondition `wp Γ Q X e m`:
* `Γ : Env` assigns contracts `Spec as bs` per symbol and signature `(as, bs)`;
* `Q : Post rs` is the return postcondition;
* `X : XPost` is the abnormal-exit postcondition (indexed by target symbol and
  argument signature);
* `m : Mem 64` is Kraken's partial 64-bit byte memory;
* `Closed Γ Q X bs Js` asserts that every block in `bs` implies its join-point predicate in `Js`.

Notice how head-bound `Tup` binders and `group` eliminate all arity and label-pairing junk cases
from `wp`: the only `False` clauses are genuine undefined behaviour (`hlt`, UB `OpCode`, unmapped
`load`/`store`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

/-- Continuation predicate for a join point taking parameter tuple `ts`. -/
abbrev Cont (ts : List Ty) : Type := Tup Val ts → Mem 64 → Prop

/-- Return postcondition for result tuple `rs`. -/
abbrev Post (rs : List Ty) : Type := Tup Val rs → Mem 64 → Prop

/-- Exit postcondition: symbol jumped to, argument signature, argument values, memory (D5). -/
abbrev XPost : Type := Sym → (as : List Ty) → Tup Val as → Mem 64 → Prop

/-- A function contract: `spec args m Q X` means every run from `args` and `m` terminates
either by returning in `Q` or by exiting in `X`. -/
abbrev Spec (as bs : List Ty) : Type := Tup Val as → Mem 64 → Post bs → XPost → Prop

/-- Contracts of global symbols, indexed by signature `(as, bs)`. -/
abbrev Env : Type := Sym → (as bs : List Ty) → Spec as bs

mutual
/-- Weakest precondition of `e : Expr Val Cont rs` in memory `m`. -/
def wp (Γ : Env) {rs : List Ty} (Q : Post rs) (X : XPost) : Expr Val Cont rs → Mem 64 → Prop
  | .let_ op k, m => op.wp (fun r => wp Γ Q X (k r) m)
  | .load t a k, m => ∃ v, loadVal m t a.val = some v ∧ wp Γ Q X (k v) m
  | .store (t := t) v a k, m =>
      storeOk m t a.val ∧ wp Γ Q X k (storeMem m t a.val v.val)
  | .call f (as := as) (bs := bs) args k, m =>
      ∃ (P : Post bs) (E : XPost), Γ f as bs (vals args) m P E ∧
        (∀ r m', P r m' → wp Γ Q X (k r) m') ∧
        (∀ g cs xs m', E g cs xs m' → X g cs xs m')
  | .jnz c t e, m => (c.val = true → wp Γ Q X t m) ∧ (c.val = false → wp Γ Q X e m)
  | .jump j args, m => j (vals args) m
  | .ret vs, m => Q (vals vs) m
  | .exit f (as := as) args, m => X f as (vals args) m
  | .hlt, _ => False
  | .group bodies k, m => ∀ Js, Closed Γ Q X (bodies Js) Js → wp Γ Q X (k Js) m

/-- Every block body in `bs` implies its corresponding join-point continuation in `Js`. -/
def Closed (Γ : Env) {rs : List Ty} (Q : Post rs) (X : XPost) :
    {sig : List (List Ty)} → Blocks Val Cont rs sig → Tup Cont sig → Prop
  | [], .nil, () => True
  | _ :: _, .cons b bs, Js =>
      (∀ xs m, wp Γ Q X (b xs) m → Js.1 xs m) ∧ Closed Γ Q X bs Js.2
end

/-- The specification satisfied by a function body `f` under environment `Γ`. -/
def Func.wp {as rs : List Ty} (Γ : Env) (f : Func as rs) : Spec as rs :=
  fun xs m Q X => _root_.LeanQbe.T.wp Γ Q X (f Val Cont xs) m

/-- Specification-form alias for `Func.wp`. -/
abbrev Func.spec {as rs : List Ty} (Γ : Env) (f : Func as rs) : Spec as rs :=
  Func.wp Γ f

end LeanQbe.T
