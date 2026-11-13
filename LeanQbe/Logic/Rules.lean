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
* `wp_unroll`: no invariant at all, only the closure hypothesis of the block; with the tactic `wp_step`
  (jump to the block once more) this executes a loop on concrete data, iteration by iteration. There,
  `branch_t tac` / `branch_f tac` take the branch of a `jnz` whose condition is decided (true / false) and
  continue with `tac`.
* `wp_call_ret1`: a call whose contract returns exactly one value and never exits.
* Evaluation lemmas for comparisons in `jnz` (`truthy_boolVal`, `first_eq_zero`) and shift-by-immediate
  address arithmetic.

Larger groups (mutual recursion between blocks, as in `Smoke.evenOdd`) use the closure hypotheses
directly after `simp only [wp, closed_param, forall_args_nil]`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe

/-! ## `wp` of each construct except join points

`wp_unfold` rewrites with these instead of `wp`'s own equations, so that it stops at `label` (a join-point
group), which the user handles with `wp_loop` / `wp_join`, keeping the goal small. -/

section
variable {Γ : Env} {Q : Post} {X : XPost} {acc : List Cont} {m : Mem 64}

theorem wp_let (op : Op Val) (k : Val → Expr Val Cont) :
    wp Γ Q X (.let_ op k) [] acc m = op.wp (fun v => wp Γ Q X (k v) [] [] m) := by simp [wp]
theorem wp_load (c : Cls) (s : Sz) (sg : Bool) (a : Arg Val) (k : Val → Expr Val Cont) :
    wp Γ Q X (.load c s sg a k) [] acc m =
      ∃ v, loadVal m c s sg a.val = some v ∧ wp Γ Q X (k v) [] [] m := by simp [wp]
theorem wp_store (s : Sz) (v a : Arg Val) (k : Expr Val Cont) :
    wp Γ Q X (.store s v a k) [] acc m =
      (storeOk m s a.val ∧ wp Γ Q X k [] [] (storeMem m s a.val v.val)) := by simp [wp]
theorem wp_jnz (c : Arg Val) (t e : Expr Val Cont) :
    wp Γ Q X (.jnz c t e) [] acc m =
      ((Truthy c.val → wp Γ Q X t [] [] m) ∧ (¬ Truthy c.val → wp Γ Q X e [] [] m)) := by simp [wp]
theorem wp_jump (j : Cont) (as : List (Arg Val)) :
    wp Γ Q X (.jump j as) [] acc m = j (as.map Arg.val) m := by simp [wp]
theorem wp_ret (vs : List (Arg Val)) : wp Γ Q X (.ret vs) [] acc m = Q (vs.map Arg.val) m := by
  simp [wp]
theorem wp_exit (f : Sym) (as : List (Arg Val)) :
    wp Γ Q X (.exit f as) [] acc m = X f (as.map Arg.val) m := by simp [wp]
theorem wp_param (f : Val → Expr Val Cont) (a : Val) (as : List Val) :
    wp Γ Q X (.param f) (a :: as) acc m = wp Γ Q X (f a) as [] m := rfl

end

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

theorem wp_unroll {Γ : Env} {Q : Post} {X : XPost} {b rest : Cont → Expr Val Cont} {m : Mem 64}
    (h : ∀ J : Cont, (∀ as m', wp Γ Q X (b J) as [] m' → J as m') → wp Γ Q X (rest J) [] [] m) :
    wp Γ Q X (.label fun J => .block (b J) (rest J)) [] [] m := by
  simp only [wp, List.nil_append, true_and]; exact h

theorem wp_call_ret1 {Γ : Env} {Q : Post} {X : XPost} {f : Sym} {args : List (Arg Val)}
    {k : Expr Val Cont} {m : Mem 64} (Pred : Val → Mem 64 → Prop)
    (hcall : Γ f (args.map Arg.val) m (fun rs m' => ∃ r, rs = [r] ∧ Pred r m') (fun _ _ _ => False))
    (hk : ∀ r m', Pred r m' → wp Γ Q X k [r] [] m') :
    wp Γ Q X (.call f args k) [] [] m := by
  simp only [wp, true_and]
  grind

@[simp] theorem truthy_boolVal (b : Bool) : Truthy (boolVal b) ↔ b = true := by
  cases b <;> decide

theorem first_eq_zero {first : Val} (h : first = 0 ∨ first = 1) (hf : ¬ Truthy first) :
    first = 0 :=
  h.elim id fun h1 => absurd (by subst h1; decide : Truthy first) hf

/-- Address arithmetic: `shl x, 3` is `8 * x`. -/
@[simp] theorem shl_three (x : Val) : x <<< 3 = BitVec.ofNat 64 (8 * x.toNat) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_shiftLeft]; omega

/-- Unfold `wp` over straight-line code and evaluate the pure operations. Leaves `∃ v, loadVal … = some
v ∧ …`, `storeOk … ∧ …`, `jnz` cases as implications, and stops at join-point groups (`label`), at
calls, and at Lean macros (definitions applied to the continuation), which have their own lemmas. -/
macro "wp_unfold" : tactic =>
  `(tactic| simp only [LeanQbe.wp_let, LeanQbe.wp_load, LeanQbe.wp_store, LeanQbe.wp_jnz,
    LeanQbe.wp_jump, LeanQbe.wp_ret, LeanQbe.wp_exit, LeanQbe.wp_param, LeanQbe.Op.wp, LeanQbe.Op.eval, LeanQbe.BinOp.eval,
    LeanQbe.CmpOp.eval, LeanQbe.Arg.val, List.map, true_and, Option.some.injEq, exists_eq_left',
    LeanQbe.truthy_boolVal, beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq, Bool.not_eq_true,
    beq_eq_false_iff_ne, BitVec.reduceToNat, Nat.reduceMod, LeanQbe.shl_three])

macro "wp_step" h:term : tactic =>
  `(tactic| (refine $h _ _ ?_; dsimp only [wp_param]; wp_unfold))

macro "branch_t" t:tacticSeq : tactic =>
  `(tactic| refine ⟨fun _ => by $t, fun hc => by first | exact absurd hc (by decide) | exact absurd (by decide) hc | exact absurd rfl hc⟩)

macro "branch_f" t:tacticSeq : tactic =>
  `(tactic| refine ⟨fun hc => absurd hc (by decide), fun _ => by $t⟩)

end LeanQbe
