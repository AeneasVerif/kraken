module

public import LeanQbe.T.GroupLfpLemmas
public import LeanQbe.T.FlatLemmas

/-!
# Tests of `LeanQbe.T.GroupLfpLemmas` (least join-point solution `Js^*`)

Covers:
1. `Tup.ofMember` / `Tup.get_ofMember`, and that `Tup Cont sig` lives in `Type`.
2. `DiagV` / `MonoD` context builders, `argRel_val`, `trel_vals`.
3. `wp_label_mono` (jumping to a weaker label) and `wp_labelfree_iff`.
4. `lfp` computed on a non-recursive join (`Js^* = Q`) and on a self-loop (`Js^* = False`,
   total correctness), `lfp_le`, `lfp_closed`, and `wp_group_iff` used to evaluate a group.
5. Every `.group` commutation lemma on a closed `Func` pair (source with the join opened high,
   target with the join sunk), with the `Wf` side conditions obtained from `t_wf_reify` and
   inversion: `group_let`, `group_load`, `group_store`, `group_call` (arbitrary `Γ`),
   `group_jnz_then`, `group_jnz_else`, `group_const`, `group_group_swap`.
6. `#print axioms` of every exported theorem.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.GroupLfpTest

open LeanQbe.T

/-! ## 1. Tuples from positions -/

example : Tup.ofMember (f := fun _ : Nat => Nat) [3, 5] (fun {a} _ => 2 * a) = (6, 10, ()) := rfl

example (h : ∀ {a : Nat}, Member a [3, 5] → Nat) :
    (Tup.ofMember (f := fun _ => Nat) [3, 5] h).get (.there .here) = h (.there .here) :=
  Tup.get_ofMember _ _ _

/-- No universe bump: label tuples are ordinary `Type`-level products of predicates. -/
example : (Tup Cont [[i64]] : Type) = (Cont [i64] × Unit) := rfl

/-! ## 2. Contexts -/

example (x : Val i64) (v : Val i32) :
    DiagV (⟨i32, v, v⟩ :: (Tup.zip (as := [i64]) (x, ()) (x, ()) ++ [])) :=
  (DiagV.nil.append (ts := [i64]) (x, ())).cons v

example (J : Cont [i64]) :
    MonoD (Tup.zip (as := [[i64]]) (fun _ _ => False, ()) (J, ()) ++
      Tup.zip (as := [[i64]]) (J, ()) (J, ())) :=
  (mono_zip (sig := [[i64]]) _ _ fun i _ _ h => by
    cases i with
    | here => exact h.elim
    | there i => nomatch i).append ((mono_zip_self (sig := [[i64]]) (J, ())).append MonoD.nil)

example {G : Ctx Val Val} (hG : DiagV G) {t : Ty} {v₁ v₂ : Val t} (h : ⟨t, v₁, v₂⟩ ∈ G) :
    v₁ = v₂ :=
  argRel_val hG (.var h)

example {G : Ctx Val Val} (hG : DiagV G) {t : Ty} {v₁ v₂ : Val t} (h : ⟨t, v₁, v₂⟩ ∈ G)
    (c : Val i64) :
    vals (ts := [t, i64]) (.var v₁, .imm c, ()) = vals (ts := [t, i64]) (.var v₂, .imm c, ()) :=
  trel_vals hG (TRel.cons' (.var h) (TRel.cons' (.imm c) TRel.nil'))

/-! ## 3. Label monotonicity -/

/-- Jumping to a pointwise weaker label is weaker. -/
theorem jump_label_mono (Γ : Env) (Q : Post [i64]) (X : XPost) (x : Val i64)
    (J₁ J₂ : Cont [i64]) (h : ∀ xs m, J₁ xs m → J₂ xs m) (m : Mem 64) :
    wp Γ Q X (.jump J₁ (ts := [i64]) (.var x, ())) m →
      wp Γ Q X (.jump J₂ (ts := [i64]) (.var x, ())) m :=
  wp_label_mono (G := Tup.zip (as := [i64]) (x, ()) (x, ()))
    (D := Tup.zip (as := [[i64]]) (J₁, ()) (J₂, ()))
    (.jump (by simp [Tup.zip]) (TRel.cons' (.var (by simp [Tup.zip])) TRel.nil'))
    (diag_zip (ts := [i64]) (x, ()))
    (mono_zip (sig := [[i64]]) _ _ fun i xs m hi => by
      cases i with
      | here => exact h xs m hi
      | there i => nomatch i) m

/-! ## 4. `Js^*` on concrete groups -/

/-- One non-recursive join block returning its parameter. -/
def joinB (V : Ty → Type) (L : List Ty → Type) : Tup L [[i64]] → Blocks V L [i64] [[i64]] :=
  fun _ => .cons (fun (r, ()) => .ret (.var r, ())) .nil

/-- One block that jumps back to itself forever. -/
def spinB (V : Ty → Type) (L : List Ty → Type) : Tup L [[i64]] → Blocks V L [i64] [[i64]] :=
  fun (h, ()) => .cons (fun (y, ()) => .jump h (.var y, ())) .nil

/-- The least solution of a non-recursive join is the `wp` of its body. -/
theorem lfp_joinB (Γ : Env) (Q : Post [i64]) (X : XPost) (r : Val i64) (m : Mem 64) :
    (lfp Γ Q X (joinB Val Cont)).get .here (r, ()) m ↔ Q (r, ()) m := by
  rw [lfp_get]
  constructor
  · intro h
    refine h (fun xs m => Q xs m, ()) ((closed_iff ..).2 fun i xs m hw => ?_)
    cases i with
    | here => simpa [joinB, Blocks.get, Tup.get, wp, vals, Arg.val] using hw
    | there i => nomatch i
  · intro hq Js hcl
    exact (closed_iff ..).1 hcl .here (r, ()) m
      (by simpa [joinB, Blocks.get, wp, vals, Arg.val] using hq)

/-- The least solution of a self-loop is `False`: `wp` is a total-correctness predicate. -/
theorem lfp_spinB (Γ : Env) (Q : Post [i64]) (X : XPost) (y : Val i64) (m : Mem 64) :
    ¬ (lfp Γ Q X (spinB Val Cont)).get .here (y, ()) m := by
  rw [lfp_get]
  intro h
  refine h (fun _ _ => False, ()) ((closed_iff ..).2 fun i xs m hw => ?_)
  cases i with
  | here => simp [spinB, Blocks.get] at hw
  | there i => nomatch i

/-- Join opened *above* an addition (the shape `withJoin` used to emit before `isScalarObj`). -/
def letSrc : Func [i64] [i64] := fun V L (x, ()) =>
  .group (joinB V L) fun (j, ()) =>
    .let_ (op2 (.add i64) (.var x) (.imm 1)) fun (y, ()) => .jump j (.var y, ())

/-- The same join sunk below the addition. -/
def letTgt : Func [i64] [i64] := fun V L (x, ()) =>
  .let_ (op2 (.add i64) (.var x) (.imm 1)) fun (y, ()) =>
  .group (joinB V L) fun (j, ()) => .jump j (.var y, ())

theorem letSrc_wf : letSrc.Wf := by t_wf_reify
theorem letTgt_wf : letTgt.Wf := by t_wf_reify

/-- `lfp_closed` and `lfp_le` on the bodies of `letSrc`: `Js^*` is closed, and below `Q`. -/
theorem joinB_lfp_closed (Γ : Env) (Q : Post [i64]) (X : XPost) (x : Val i64) :
    Closed Γ Q X (joinB Val Cont (lfp Γ Q X (joinB Val Cont))) (lfp Γ Q X (joinB Val Cont)) :=
  lfp_closed (diag_zip (ts := [i64]) (x, ())) MonoD.nil
    (Wf.group_inv (letSrc_wf.refl Val Cont (x, ()))).1

theorem joinB_lfp_le (Γ : Env) (Q : Post [i64]) (X : XPost) (r : Val i64) (m : Mem 64)
    (h : (lfp Γ Q X (joinB Val Cont)).get .here (r, ()) m) : Q (r, ()) m :=
  lfp_le (Γ := Γ) (X := X) (bodies := joinB Val Cont) (Js := (fun xs m => Q xs m, ()))
    ((closed_iff ..).2 fun i xs m hw => by
      cases i with
      | here => simpa [joinB, Blocks.get, Tup.get, wp, vals, Arg.val] using hw
      | there i => nomatch i) .here (r, ()) m h

/-- `wp_group_iff` evaluates the group at `Js^*`, and `lfp_joinB` computes it: the join is
inlined without guessing a join-point invariant. -/
theorem letSrc_spec (Γ : Env) (x : Val i64) (m : Mem 64) (Q : Post [i64]) (X : XPost) :
    Func.wp Γ letSrc (x, ()) m Q X ↔
      wp Γ Q X (.let_ (op2 (.add i64) (.var x) (.imm 1)) fun (y, ()) => .ret (.var y, ())) m := by
  have hwf := Wf.group_inv (letSrc_wf.refl Val Cont (x, ()))
  refine (wp_group_iff (diag_zip (ts := [i64]) (x, ())) MonoD.nil hwf.1 hwf.2 m).trans ?_
  simp only [wp]
  exact ⟨Op.wp_mono fun r h => (lfp_joinB Γ Q X r.1 m).1 h,
    Op.wp_mono fun r h => (lfp_joinB Γ Q X r.1 m).2 h⟩

/-- A label-free family has the same `wp` at every label instantiation. -/
example (Γ : Env) (Q : Post [i64]) (X : XPost) (x : Val i64) (Js₁ Js₂ : Tup Cont [[i64]])
    (m : Mem 64) :
    wp Γ Q X ((fun _ : Tup Cont [[i64]] => letTgt Val Cont (x, ())) Js₁) m ↔
      wp Γ Q X ((fun _ : Tup Cont [[i64]] => letTgt Val Cont (x, ())) Js₂) m :=
  wp_labelfree_iff (diag_zip (ts := [i64]) (x, ())) MonoD.nil _
    (fun _ _ => letTgt_wf.refl Val Cont (x, ())) Js₁ Js₂ m

/-! ## 5. Commutation lemmas on closed functions -/

/-- `group_let`. -/
theorem let_commute (Γ : Env) (x : Val i64) (m : Mem 64) (Q : Post [i64]) (X : XPost) :
    Func.wp Γ letSrc (x, ()) m Q X ↔ Func.wp Γ letTgt (x, ()) m Q X :=
  group_let _ _ (diag_zip (ts := [i64]) (x, ())) MonoD.nil (letSrc_wf.refl Val Cont (x, ())) m

/-- Join above a `load`. -/
def loadSrc : Func [i64] [i64] := fun V L (p, ()) =>
  .group (joinB V L) fun (j, ()) => .load i64 (.var p) fun v => .jump j (.var v, ())

/-- Join below the `load`. -/
def loadTgt : Func [i64] [i64] := fun V L (p, ()) =>
  .load i64 (.var p) fun v => .group (joinB V L) fun (j, ()) => .jump j (.var v, ())

theorem loadSrc_wf : loadSrc.Wf := by t_wf_reify

/-- `group_load`. -/
theorem load_commute (Γ : Env) (p : Val i64) (m : Mem 64) (Q : Post [i64]) (X : XPost) :
    Func.wp Γ loadSrc (p, ()) m Q X ↔ Func.wp Γ loadTgt (p, ()) m Q X :=
  group_load _ _ _ (diag_zip (ts := [i64]) (p, ())) MonoD.nil
    (loadSrc_wf.refl Val Cont (p, ())) m

/-- Join above a `store`. -/
def storeSrc : Func [i64, i64] [i64] := fun V L (p, v, ()) =>
  .group (joinB V L) fun (j, ()) => .store (t := i64) (.var v) (.var p) (.jump j (.var v, ()))

/-- Join below the `store`. -/
def storeTgt : Func [i64, i64] [i64] := fun V L (p, v, ()) =>
  .store (t := i64) (.var v) (.var p) (.group (joinB V L) fun (j, ()) => .jump j (.var v, ()))

theorem storeSrc_wf : storeSrc.Wf := by t_wf_reify

/-- `group_store`. -/
theorem store_commute (Γ : Env) (p v : Val i64) (m : Mem 64) (Q : Post [i64]) (X : XPost) :
    Func.wp Γ storeSrc (p, v, ()) m Q X ↔ Func.wp Γ storeTgt (p, v, ()) m Q X :=
  group_store _ _ _ (diag_zip (ts := [i64, i64]) (p, v, ())) MonoD.nil
    (storeSrc_wf.refl Val Cont (p, v, ())) m

/-- Join above a `call` of an arbitrary external symbol. -/
def callSrc : Func [i64] [i64] := fun V L (x, ()) =>
  .group (joinB V L) fun (j, ()) =>
    .call "ext" (as := [i64]) (bs := [i64]) (.var x, ()) fun (r, ()) => .jump j (.var r, ())

/-- Join below the `call`. -/
def callTgt : Func [i64] [i64] := fun V L (x, ()) =>
  .call "ext" (as := [i64]) (bs := [i64]) (.var x, ()) fun (r, ()) =>
  .group (joinB V L) fun (j, ()) => .jump j (.var r, ())

theorem callSrc_wf : callSrc.Wf := by t_wf_reify

/-- `group_call`: holds for every environment `Γ`, i.e. for every contract of `ext`. -/
theorem call_commute (Γ : Env) (x : Val i64) (m : Mem 64) (Q : Post [i64]) (X : XPost) :
    Func.wp Γ callSrc (x, ()) m Q X ↔ Func.wp Γ callTgt (x, ()) m Q X :=
  group_call _ _ (diag_zip (ts := [i64]) (x, ())) MonoD.nil
    (callSrc_wf.refl Val Cont (x, ())) m

/-- Join above a `jnz` whose `else` arm does not use it. -/
def thenSrc : Func [i64] [i64] := fun V L (x, ()) =>
  .let_ (op2 (.eq i64) (.var x) (.imm 0)) fun (z, ()) =>
  .group (joinB V L) fun (j, ()) =>
    .jnz (.var z) (.jump j (.var x, ())) (.ret (.imm 7, ()))

/-- Join sunk into the `then` arm. -/
def thenTgt : Func [i64] [i64] := fun V L (x, ()) =>
  .let_ (op2 (.eq i64) (.var x) (.imm 0)) fun (z, ()) =>
  .jnz (.var z) (.group (joinB V L) fun (j, ()) => .jump j (.var x, ())) (.ret (.imm 7, ()))

theorem thenSrc_wf : thenSrc.Wf := by t_wf_reify

/-- `group_jnz_then`, under a `let_` binder (`DiagV.append` extends the diagonal context). -/
theorem then_commute (Γ : Env) (x : Val i64) (m : Mem 64) (Q : Post [i64]) (X : XPost) :
    Func.wp Γ thenSrc (x, ()) m Q X ↔ Func.wp Γ thenTgt (x, ()) m Q X := by
  have hk := (Wf.let_inv (thenSrc_wf.refl Val Cont (x, ()))).2
  have hG := diag_zip (ts := [i64]) (x, ())
  simp only [Func.wp, thenSrc, thenTgt, wp_let]
  exact ⟨Op.wp_mono fun r h => (group_jnz_then _ _ _ (hG.append r) MonoD.nil (hk r r) m).1 h,
    Op.wp_mono fun r h => (group_jnz_then _ _ _ (hG.append r) MonoD.nil (hk r r) m).2 h⟩

/-- Join above a `jnz` whose `then` arm does not use it. -/
def elseSrc : Func [i64] [i64] := fun V L (x, ()) =>
  .let_ (op2 (.eq i64) (.var x) (.imm 0)) fun (z, ()) =>
  .group (joinB V L) fun (j, ()) =>
    .jnz (.var z) (.ret (.imm 7, ())) (.jump j (.var x, ()))

/-- Join sunk into the `else` arm. -/
def elseTgt : Func [i64] [i64] := fun V L (x, ()) =>
  .let_ (op2 (.eq i64) (.var x) (.imm 0)) fun (z, ()) =>
  .jnz (.var z) (.ret (.imm 7, ())) (.group (joinB V L) fun (j, ()) => .jump j (.var x, ()))

theorem elseSrc_wf : elseSrc.Wf := by t_wf_reify

/-- `group_jnz_else`. -/
theorem else_commute (Γ : Env) (x : Val i64) (m : Mem 64) (Q : Post [i64]) (X : XPost) :
    Func.wp Γ elseSrc (x, ()) m Q X ↔ Func.wp Γ elseTgt (x, ()) m Q X := by
  have hk := (Wf.let_inv (elseSrc_wf.refl Val Cont (x, ()))).2
  have hG := diag_zip (ts := [i64]) (x, ())
  simp only [Func.wp, elseSrc, elseTgt, wp_let]
  exact ⟨Op.wp_mono fun r h => (group_jnz_else _ _ _ (hG.append r) MonoD.nil (hk r r) m).1 h,
    Op.wp_mono fun r h => (group_jnz_else _ _ _ (hG.append r) MonoD.nil (hk r r) m).2 h⟩

/-- A join (here even a diverging one) that the entry never jumps to. -/
def deadSrc : Func [i64] [i64] := fun V L (x, ()) =>
  .group (spinB V L) fun _ => .ret (.var x, ())

/-- The entry alone. -/
def deadTgt : Func [i64] [i64] := fun _ _ (x, ()) => .ret (.var x, ())

theorem deadSrc_wf : deadSrc.Wf := by t_wf_reify
theorem deadTgt_wf : deadTgt.Wf := by t_wf_reify

/-- `group_const`. -/
theorem dead_commute (Γ : Env) (x : Val i64) (m : Mem 64) (Q : Post [i64]) (X : XPost) :
    Func.wp Γ deadSrc (x, ()) m Q X ↔ Func.wp Γ deadTgt (x, ()) m Q X :=
  group_const _ (diag_zip (ts := [i64]) (x, ())) MonoD.nil
    (Wf.group_inv (deadSrc_wf.refl Val Cont (x, ()))).1 (deadTgt_wf.refl Val Cont (x, ())) m

/-- A countdown loop: a recursive inner group. -/
def downB (V : Ty → Type) (L : List Ty → Type) : Tup L [[i64]] → Blocks V L [i64] [[i64]] :=
  fun (h, ()) => .cons (fun (y, ()) =>
    .let_ (op2 (.sub i64) (.var y) (.imm 1)) fun (y', ()) =>
    .let_ (op2 (.eq i64) (.var y') (.imm 0)) fun (z, ()) =>
    .jnz (.var z) (.ret (.var y', ())) (.jump h (.var y', ()))) .nil

/-- Join `j` opened outside the loop `h`; the entry uses both. -/
def swapSrc : Func [i64] [i64] := fun V L (x, ()) =>
  .group (joinB V L) fun (j, ()) =>
  .group (downB V L) fun (h, ()) =>
    .let_ (op2 (.eq i64) (.var x) (.imm 0)) fun (z, ()) =>
    .jnz (.var z) (.jump j (.var x, ())) (.jump h (.var x, ()))

/-- The two groups swapped. -/
def swapTgt : Func [i64] [i64] := fun V L (x, ()) =>
  .group (downB V L) fun (h, ()) =>
  .group (joinB V L) fun (j, ()) =>
    .let_ (op2 (.eq i64) (.var x) (.imm 0)) fun (z, ()) =>
    .jnz (.var z) (.jump j (.var x, ())) (.jump h (.var x, ()))

theorem swapSrc_wf : swapSrc.Wf := by t_wf_reify
theorem swapTgt_wf : swapTgt.Wf := by t_wf_reify

/-- `group_group_swap`: `hc` (the loop ignores `j`) comes from the target's `Wf`, `hbk` and `hk`
from the source's. -/
theorem swap_commute (Γ : Env) (x : Val i64) (m : Mem 64) (Q : Post [i64]) (X : XPost) :
    Func.wp Γ swapSrc (x, ()) m Q X ↔ Func.wp Γ swapTgt (x, ()) m Q X := by
  have hs := Wf.group_inv (swapSrc_wf.refl Val Cont (x, ()))
  have ht := Wf.group_inv (swapTgt_wf.refl Val Cont (x, ()))
  exact group_group_swap _ _ (diag_zip (ts := [i64]) (x, ())) MonoD.nil ht.1 hs.1
    (fun J₁ J₂ H₁ H₂ => (Wf.group_inv (hs.2 J₁ J₂)).2 H₁ H₂) m

/-! ## 6. Axioms -/

#print axioms Tup.get_ofMember
#print axioms diag_zip
#print axioms DiagV.append
#print axioms DiagV.cons
#print axioms mono_zip
#print axioms mono_zip_self
#print axioms MonoD.append
#print axioms argRel_val
#print axioms trel_vals
#print axioms wp_label_mono
#print axioms wp_labelfree_iff
#print axioms lfp_get
#print axioms lfp_le
#print axioms lfp_closed
#print axioms wp_group_iff
#print axioms WfB.weaken_append
#print axioms group_const
#print axioms group_let
#print axioms group_load
#print axioms group_store
#print axioms group_call
#print axioms group_jnz_then
#print axioms group_jnz_else
#print axioms group_group_swap
#print axioms letSrc_spec
#print axioms lfp_spinB
#print axioms call_commute
#print axioms swap_commute

end LeanQbe.T.GroupLfpTest
