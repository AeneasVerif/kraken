module

public import LeanQbe.WPLemmas

/-!
# Proof rules for user programs

`wp` is structural, so straight-line code is handled by unfolding it (`wp_unfold`). The rules here are
for what unfolding cannot do:

* `wp_loop`: a one-block join-point group with a back edge (a loop), proved by an invariant indexed by
  a natural-number measure. It is *derived* from the closure hypothesis that `wp` gives a `block`
  (`∀ as m', wp b as m' → J as m'`), by strong induction on the measure: total correctness needs no
  extra machinery.
* `wp_join`: the same without a back edge (a join after `jnz`, or a continuation label).
* Evaluation lemmas for comparisons in `jnz` and shift-by-immediate address arithmetic.

Larger groups (mutual recursion between blocks, as in `Smoke.evenOdd`) use the closure hypotheses
directly after `simp only [wp, closed_param, forall_args_nil]`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe

/-- Loop rule for `label J => block (b J) (rest J)`. `Inv n as m` is the invariant at measure `n`
for the block arguments `as`; the body may jump back to `J` only with a smaller measure. -/
theorem wp_loop {Γ : Env} {Q : Post} {X : XPost} {b rest : Cont → Expr Val Cont} {m : Mem 64}
    (Inv : Nat → List Val → Mem 64 → Prop)
    (hbody : ∀ J : Cont, ∀ n as m, Inv n as m →
      (∀ n' as' m', n' < n → Inv n' as' m' → J as' m') → wp Γ Q X (b J) as [] m)
    (hrest : ∀ J : Cont, (∀ n as m, Inv n as m → J as m) → wp Γ Q X (rest J) [] [] m) :
    wp Γ Q X (.label fun J => .block (b J) (rest J)) [] [] m := by
  simp only [wp, List.nil_append, true_and]
  intro J hJ
  refine hrest J fun n => ?_
  induction n using Nat.strongRecOn with
  | _ n ih => exact fun as m h => hJ as m (hbody J n as m h fun n' as' m' hlt => ih n' hlt as' m')

/-- Forward join point `label J => block b (rest J)`: `P` is what every jump to `J` establishes. -/
theorem wp_join {Γ : Env} {Q : Post} {X : XPost} {b : Expr Val Cont} {rest : Cont → Expr Val Cont}
    {m : Mem 64} (P : List Val → Mem 64 → Prop) (hbody : ∀ as m, P as m → wp Γ Q X b as [] m)
    (hrest : ∀ J : Cont, (∀ as m, P as m → J as m) → wp Γ Q X (rest J) [] [] m) :
    wp Γ Q X (.label fun J => .block b (rest J)) [] [] m :=
  wp_loop (fun _ => P) (fun _ _ as m h _ => hbody as m h) fun J hJ => hrest J (hJ 0)

@[simp] theorem truthy_boolVal (b : Bool) : Truthy (boolVal b) ↔ b = true := by
  cases b <;> decide

/-- Address arithmetic: `shl x, 3` is `8 * x`. -/
@[simp] theorem shl_three (x : Val) : x <<< 3 = BitVec.ofNat 64 (8 * x.toNat) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_shiftLeft]; omega

/-- Unfold `wp` over straight-line code and evaluate the pure operations. Leaves `∃ v, loadVal … = some
v ∧ …`, `storeOk … ∧ …`, `jnz` cases as implications, and join points as `∀ J, closure → …`. -/
macro "wp_unfold" : tactic =>
  `(tactic| simp only [LeanQbe.wp, LeanQbe.Op.wp, LeanQbe.Op.eval, LeanQbe.BinOp.eval,
    LeanQbe.CmpOp.eval, LeanQbe.Arg.val, List.map, true_and, Option.some.injEq, exists_eq_left',
    LeanQbe.truthy_boolVal, beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq, Bool.not_eq_true,
    beq_eq_false_iff_ne, BitVec.reduceToNat, Nat.reduceMod, LeanQbe.shl_three])

end LeanQbe
