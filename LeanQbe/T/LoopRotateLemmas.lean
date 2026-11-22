module

public import LeanQbe.T.LoopRotate
import LeanQbe.T.OptUtilLemmas
import LeanQbe.T.FlatLemmas
public import LeanQbe.T.Module

/-!
# Correctness Proofs for `LeanQbe.T.LoopRotate`

Proves relational well-formedness (`*_wf`), weakest-precondition refinement (`*_spec` /
`Func.loopRotate_correct`), and call/exit well-scopedness (`*_callsOk`) for the two-phase
loop rotation pass:

* `RotImpl.flatExpr_wf`, `RotImpl.rewriteRot_wf`, `Func.loopRotateWithPlan_wf`,
  `Func.loopRotate_wf`, `Fn.loopRotate_wf`
* `RotImpl.flatExpr_wp`, `RotImpl.rewriteRot_wp`, `Func.loopRotateWithPlan_spec`,
  `Func.loopRotate_spec`, `Func.loopRotate_correct`, `Fn.loopRotate_spec`
* `RotImpl.rewriteRot_callsOk`, `Func.loopRotateWithPlan_callsOk`,
  `Func.loopRotate_callsOk`, `Fn.loopRotate_callsOk`
-/

set_option autoImplicit false

public section

namespace LeanQbe.T

namespace RotImpl

open LoopRotate

/-! ## Decidable equality and tuple plumbing helpers -/

private theorem tysDecEq_self_isTrue (dts : List Ty) : tysDecEq dts dts = isTrue rfl := by
  cases h : tysDecEq dts dts with
  | isTrue _ => rfl
  | isFalse hne => exact absurd rfl hne

private theorem tyDecEq_self_isTrue (t : Ty) : tyDecEq t t = isTrue rfl := by
  cases h : tyDecEq t t with
  | isTrue _ => rfl
  | isFalse hne => exact absurd rfl hne

private theorem tysDecEq_false_of_ne {a b : List Ty} (hne : a ≠ b) :
    ∃ h : a ≠ b, tysDecEq a b = isFalse h := by
  cases h : tysDecEq a b with
  | isTrue heq => exact absurd heq hne
  | isFalse hf => exact ⟨hf, rfl⟩

private theorem tyDecEq_false_of_ne {a b : Ty} (hne : a ≠ b) :
    ∃ h : a ≠ b, tyDecEq a b = isFalse h := by
  cases h : tyDecEq a b with
  | isTrue heq => exact absurd heq hne
  | isFalse hf => exact ⟨hf, rfl⟩

/-- Heterogeneous-tuple concatenation preserves `vals` pointwise. -/
private theorem vals_tupAppend :
    {as bs : List Ty} → (xs : Tup (Arg Val) as) → (ys : Tup (Arg Val) bs) →
    vals (tupAppend xs ys) = tupAppend (vals xs) (vals ys)
  | [], _, (), _ => rfl
  | _ :: _, _, (_, xs), ys => Prod.ext rfl (vals_tupAppend xs ys)

/-- `tupSplit` is the exact inverse of `tupAppend`. -/
private theorem tupSplit_tupAppend {f : Ty → Type} :
    {as bs : List Ty} → (xs : Tup f as) → (ys : Tup f bs) →
    tupSplit as (tupAppend xs ys) = (xs, ys)
  | [], _, (), ys => rfl
  | _ :: _, _, (x, xs), ys => by
    dsimp only [tupAppend, tupSplit]; rw [tupSplit_tupAppend xs ys]

private theorem tupSplit_mem_left {f₁ f₂ : Ty → Type} {G : Ctx f₁ f₂} :
    (as : List Ty) → {bs : List Ty} →
    {xs₁ : Tup f₁ (as ++ bs)} → {xs₂ : Tup f₂ (as ++ bs)} →
    (∀ p ∈ Tup.zip xs₁ xs₂, p ∈ G) →
    ∀ p ∈ Tup.zip (tupSplit as xs₁).1 (tupSplit as xs₂).1, p ∈ G
  | [], _, _, _, _, _, hp => nomatch hp
  | _ :: as, _, (_, _), (_, _), hmem, p, hp => by
    dsimp only [tupSplit, Tup.zip] at hp; simp only [List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact hmem _ List.mem_cons_self
    · exact tupSplit_mem_left as (fun _ hq => hmem _ (List.mem_cons_of_mem _ hq)) _ hp

private theorem tupSplit_mem_right {f₁ f₂ : Ty → Type} {G : Ctx f₁ f₂} :
    (as : List Ty) → {bs : List Ty} →
    {xs₁ : Tup f₁ (as ++ bs)} → {xs₂ : Tup f₂ (as ++ bs)} →
    (∀ p ∈ Tup.zip xs₁ xs₂, p ∈ G) →
    ∀ p ∈ Tup.zip (tupSplit as xs₁).2 (tupSplit as xs₂).2, p ∈ G
  | [], _, _, _, hmem, p, hp => hmem p hp
  | _ :: as, _, (_, _), (_, _), hmem, p, hp => by
    dsimp only [tupSplit] at hp
    exact tupSplit_mem_right as (fun _ hq => hmem _ (List.mem_cons_of_mem _ hq)) p hp

private theorem splitTail_mem {V₁ V₂ : Ty → Type} {G : Ctx V₁ V₂} {tail : List Ty} :
    (hdr : HdrPlan) → (ms : List (List Bool)) →
    {xs₁ : Tup V₁ (stepMasksSig hdr ms tail)} → {xs₂ : Tup V₂ (stepMasksSig hdr ms tail)} →
    (∀ p ∈ Tup.zip xs₁ xs₂, p ∈ G) →
    ∀ p ∈ Tup.zip (splitTail hdr ms xs₁) (splitTail hdr ms xs₂), p ∈ G
  | [], _, _, _, hmem, p, hp => hmem p hp
  | st :: ss, ms, _, _, hmem, p, hp => by
    dsimp only [splitTail] at hp
    exact splitTail_mem ss ms.tail (tupSplit_mem_right _ hmem) p hp

private theorem tupAppend_argRel {V₁ V₂ : Ty → Type} {G : Ctx V₁ V₂} :
    {as bs : List Ty} → {xs₁ : Tup (Arg V₁) as} → {xs₂ : Tup (Arg V₂) as} →
    {ys₁ : Tup (Arg V₁) bs} → {ys₂ : Tup (Arg V₂) bs} →
    TRel (ArgRel G) xs₁ xs₂ → TRel (ArgRel G) ys₁ ys₂ →
    TRel (ArgRel G) (tupAppend xs₁ ys₁) (tupAppend xs₂ ys₂)
  | [], _, (), (), _, _, .nil, hy => hy
  | _ :: _, _, (_, _), (_, _), _, _, .cons hx hxs, hy =>
    .cons hx (tupAppend_argRel hxs hy)

private theorem eq_mpr_of_heq {α β : Sort _} (h : α = β) (x : β) (y : α) (hx : HEq x y) :
    Eq.mpr h x = y := by
  cases h; exact eq_of_heq hx

private theorem tupWiden_pair_cast {V : Ty → Type} {t : Ty} {ts : List Ty} {bs₁ bs₂ : List Bool}
    (hb : bs₁ = bs₂) {α : Type} (h : α = (V t × Tup V (filterTys ts bs₁)))
    (x : α) (y : V t) (ys : Tup V (filterTys ts bs₂)) (hx : HEq x (y, ys)) :
    (some (Arg.var (Eq.mp h x).1), tupWiden ts bs₁ (Eq.mp h x).2) =
      (some (Arg.var y), tupWiden ts bs₂ ys) := by
  subst hb
  have hxy : Eq.mp h x = (y, ys) := eq_of_heq ((cast_heq h x).trans hx)
  rw [hxy]

private theorem tupWiden_tail_cast {V : Ty → Type} {t : Ty} {ts : List Ty} {bs₁ bs₂ : List Bool}
    (hb : bs₁ = bs₂) {α : Type} (h : α = Tup V (filterTys ts bs₁))
    (x : α) (ys : Tup V (filterTys ts bs₂)) (hx : HEq x ys) :
    ((none : OptArg V t), tupWiden ts bs₁ (Eq.mp h x)) = (none, tupWiden ts bs₂ ys) := by
  subst hb
  have hxy : Eq.mp h x = ys := eq_of_heq ((cast_heq h x).trans hx)
  rw [hxy]

private theorem tupSelectArgs_nil_mask {V : Ty → Type} {t : Ty} {ts : List Ty}
    (a : Arg V t) (as : Tup (Arg V) ts) :
    tupSelectArgs (t :: ts) [] (a, as) = (a, tupSelectArgs ts [] as) := by
  dsimp only [tupSelectArgs]; split
  · exact eq_mpr_of_heq _ _ _ .rfl
  · contradiction

private theorem tupSelectArgs_true {V : Ty → Type} {t : Ty} {ts : List Ty} {bs : List Bool}
    (a : Arg V t) (as : Tup (Arg V) ts) :
    tupSelectArgs (t :: ts) (true :: bs) (a, as) = (a, tupSelectArgs ts bs as) := by
  dsimp only [tupSelectArgs]; split
  · exact eq_mpr_of_heq _ _ _ .rfl
  · contradiction

private theorem tupSelectArgs_false {V : Ty → Type} {t : Ty} {ts : List Ty} {bs : List Bool}
    (a : Arg V t) (as : Tup (Arg V) ts) :
    tupSelectArgs (t :: ts) (false :: bs) (a, as) = tupSelectArgs ts bs as := by
  dsimp only [tupSelectArgs]; split
  · contradiction
  · exact eq_mpr_of_heq _ _ _ .rfl

private theorem tupSelectArgs_argRel {V₁ V₂ : Ty → Type} {G : Ctx V₁ V₂} :
    (ts : List Ty) → (bs : List Bool) →
    {xs₁ : Tup (Arg V₁) ts} → {xs₂ : Tup (Arg V₂) ts} →
    TRel (ArgRel G) xs₁ xs₂ →
    TRel (ArgRel G) (tupSelectArgs ts bs xs₁) (tupSelectArgs ts bs xs₂)
  | [], _, (), (), .nil => .nil
  | _ :: ts, [], (_, _), (_, _), .cons hx hxs => by
    rw [tupSelectArgs_nil_mask, tupSelectArgs_nil_mask]
    exact .cons hx (tupSelectArgs_argRel ts [] hxs)
  | _ :: ts, true :: bs, (_, _), (_, _), .cons hx hxs => by
    rw [tupSelectArgs_true, tupSelectArgs_true]
    exact .cons hx (tupSelectArgs_argRel ts bs hxs)
  | _ :: ts, false :: bs, (_, _), (_, _), .cons _ hxs => by
    rw [tupSelectArgs_false, tupSelectArgs_false]
    exact tupSelectArgs_argRel ts bs hxs

/-- Semantic counterpart of `tupSelectArgs` on `Val` tuples. -/
private def tupSelectVals :
    (ts : List Ty) → (bs : List Bool) → Tup Val ts → Tup Val (filterTys ts bs)
  | [], _, () => ()
  | _ :: ts, bs, (v, vs) =>
    if h : bs.headD true = true then by
      dsimp only [filterTys]; simpa only [h, ↓reduceIte] using (v, tupSelectVals ts bs.tail vs)
    else by
      dsimp only [filterTys]
      simpa only [h, Bool.false_eq_true, ↓reduceIte] using tupSelectVals ts bs.tail vs

private theorem tupSelectVals_nil_mask {t : Ty} {ts : List Ty} (v : Val t) (vs : Tup Val ts) :
    tupSelectVals (t :: ts) [] (v, vs) = (v, tupSelectVals ts [] vs) := by
  dsimp only [tupSelectVals]; split
  · exact eq_mpr_of_heq _ _ _ .rfl
  · contradiction

private theorem tupSelectVals_true {t : Ty} {ts : List Ty} {bs : List Bool}
    (v : Val t) (vs : Tup Val ts) :
    tupSelectVals (t :: ts) (true :: bs) (v, vs) = (v, tupSelectVals ts bs vs) := by
  dsimp only [tupSelectVals]; split
  · exact eq_mpr_of_heq _ _ _ .rfl
  · contradiction

private theorem tupSelectVals_false {t : Ty} {ts : List Ty} {bs : List Bool}
    (v : Val t) (vs : Tup Val ts) :
    tupSelectVals (t :: ts) (false :: bs) (v, vs) = tupSelectVals ts bs vs := by
  dsimp only [tupSelectVals]; split
  · contradiction
  · exact eq_mpr_of_heq _ _ _ .rfl

private theorem tupWiden_nil_mask {V : Ty → Type} {t : Ty} {ts : List Ty}
    (y : V t) (ys : Tup V (filterTys ts [])) :
    tupWiden (t :: ts) [] (y, ys) = (some (.var y), tupWiden ts [] ys) := by
  dsimp only [tupWiden]; split
  · exact tupWiden_pair_cast rfl _ _ y ys .rfl
  · contradiction

private theorem tupWiden_true {V : Ty → Type} {t : Ty} {ts : List Ty} {bs : List Bool}
    (y : V t) (ys : Tup V (filterTys ts bs)) :
    tupWiden (t :: ts) (true :: bs) (y, ys) = (some (.var y), tupWiden ts bs ys) := by
  dsimp only [tupWiden]; split
  · exact tupWiden_pair_cast rfl _ _ y ys .rfl
  · contradiction

private theorem tupWiden_false {V : Ty → Type} {t : Ty} {ts : List Ty} {bs : List Bool}
    (ys : Tup V (filterTys ts bs)) :
    tupWiden (t :: ts) (false :: bs) ys = (none, tupWiden ts bs ys) := by
  dsimp only [tupWiden]; split
  · contradiction
  · exact tupWiden_tail_cast rfl _ _ ys .rfl

private theorem tupWiden_nil_eq {V : Ty → Type} {t : Ty} {ts : List Ty}
    (xs : Tup V (filterTys (t :: ts) [])) (y : V t) (ys : Tup V (filterTys ts []))
    (h : xs = (y, ys)) :
    tupWiden (t :: ts) [] xs = (some (.var y), tupWiden ts [] ys) := by
  subst h; exact tupWiden_nil_mask y ys

private theorem tupWiden_true_eq {V : Ty → Type} {t : Ty} {ts : List Ty} {bs : List Bool}
    (xs : Tup V (filterTys (t :: ts) (true :: bs))) (y : V t) (ys : Tup V (filterTys ts bs))
    (h : xs = (y, ys)) :
    tupWiden (t :: ts) (true :: bs) xs = (some (.var y), tupWiden ts bs ys) := by
  subst h; exact tupWiden_true y ys

private theorem tupWiden_false_eq {V : Ty → Type} {t : Ty} {ts : List Ty} {bs : List Bool}
    (xs : Tup V (filterTys (t :: ts) (false :: bs))) (ys : Tup V (filterTys ts bs))
    (h : xs = ys) :
    tupWiden (t :: ts) (false :: bs) xs = (none, tupWiden ts bs ys) := by
  subst h; exact tupWiden_false _

private theorem tupWiden_tupSelectVals_nil {t : Ty} {ts : List Ty} (y : Val t) (ys : Tup Val ts) :
    tupWiden (t :: ts) [] (tupSelectVals (t :: ts) [] (y, ys)) =
      (some (.var y), tupWiden ts [] (tupSelectVals ts [] ys)) :=
  tupWiden_nil_eq _ _ _ (tupSelectVals_nil_mask y ys)

private theorem tupWiden_tupSelectVals_true {t : Ty} {ts : List Ty} {bs : List Bool}
    (y : Val t) (ys : Tup Val ts) :
    tupWiden (t :: ts) (true :: bs) (tupSelectVals (t :: ts) (true :: bs) (y, ys)) =
      (some (.var y), tupWiden ts bs (tupSelectVals ts bs ys)) :=
  tupWiden_true_eq _ _ _ (tupSelectVals_true y ys)

private theorem tupWiden_tupSelectVals_false {t : Ty} {ts : List Ty} {bs : List Bool}
    (y : Val t) (ys : Tup Val ts) :
    tupWiden (t :: ts) (false :: bs) (tupSelectVals (t :: ts) (false :: bs) (y, ys)) =
      (none, tupWiden ts bs (tupSelectVals ts bs ys)) :=
  tupWiden_false_eq _ _ (tupSelectVals_false y ys)

private theorem vals_tupSelectArgs :
    {ts : List Ty} → (bs : List Bool) → (args : Tup (Arg Val) ts) →
    vals (tupSelectArgs ts bs args) = tupSelectVals ts bs (vals args)
  | [], _, () => rfl
  | _ :: ts, [], (_, args) => by
    rw [tupSelectArgs_nil_mask, tupSelectVals_nil_mask]
    exact Prod.ext rfl (vals_tupSelectArgs [] args)
  | _ :: ts, true :: bs, (_, args) => by
    rw [tupSelectArgs_true, tupSelectVals_true]
    exact Prod.ext rfl (vals_tupSelectArgs bs args)
  | _ :: ts, false :: bs, (_, args) => by
    rw [tupSelectArgs_false, tupSelectVals_false]
    exact vals_tupSelectArgs bs args

/-- Heterogeneous tuple of `HdrStep` output values produced while evaluating `hdr`. -/
@[reducible] private def HdrVals : HdrPlan → Type
  | [] => Unit
  | s :: ss => Tup Val s.tys × HdrVals ss

/-- Select masked header values concatenated with `tl`, matching `hdrEmit`'s argument order. -/
private def hdrSelect {tail : List Ty} :
    (hdr : HdrPlan) → (ms : List (List Bool)) → HdrVals hdr → Tup Val tail →
    Tup Val (stepMasksSig hdr ms tail)
  | [], _, (), tl => tl
  | s :: ss, ms, (ys, rest), tl =>
    tupAppend (tupSelectVals s.tys (ms.headD []) ys) (hdrSelect ss ms.tail rest tl)

private theorem splitTail_hdrSelect {tail : List Ty} :
    (hdr : HdrPlan) → (ms : List (List Bool)) → (hv : HdrVals hdr) → (tl : Tup Val tail) →
    splitTail hdr ms (hdrSelect hdr ms hv tl) = tl
  | [], _, (), _ => rfl
  | s :: ss, ms, (_, rest), tl => by
    dsimp only [hdrSelect, splitTail]; rw [tupSplit_tupAppend]
    exact splitTail_hdrSelect ss ms.tail rest tl

/-! ## Relational invariants (`OptWfRel`, `RotLRel`) and `rewriteRot_wf` -/

/-- Binder invariant for `OptArg` contexts: both dropped (`none, none`) or both kept (`some`). -/
private def OptWfRel {V₁ V₂ : Ty → Type}
    (G' : Ctx V₁ V₂) (G : Ctx (OptArg V₁) (OptArg V₂)) : Prop :=
  ∀ {t : Ty} {o₁ : OptArg V₁ t} {o₂ : OptArg V₂ t}, ⟨t, o₁, o₂⟩ ∈ G →
    (o₁ = none ∧ o₂ = none) ∨
    ∃ a₁ a₂, o₁ = some a₁ ∧ o₂ = some a₂ ∧ ArgRel G' t a₁ a₂

private theorem OptWfRel.weaken {V₁ V₂ : Ty → Type} {G₁ G₂ : Ctx V₁ V₂}
    {G : Ctx (OptArg V₁) (OptArg V₂)}
    (hG : ∀ p ∈ G₁, p ∈ G₂) (h : OptWfRel G₁ G) : OptWfRel G₂ G := by
  intro t o₁ o₂ hm
  rcases h hm with h0 | ⟨a₁, a₂, h1, h2, ha⟩
  · exact Or.inl h0
  · exact Or.inr ⟨a₁, a₂, h1, h2, ha.weaken hG⟩

private theorem OptWfRel.append {V₁ V₂ : Ty → Type} {G' : Ctx V₁ V₂}
    {H G : Ctx (OptArg V₁) (OptArg V₂)}
    (hH : OptWfRel G' H) (hG : OptWfRel G' G) : OptWfRel G' (H ++ G) := by
  intro t o₁ o₂ hm
  rcases List.mem_append.1 hm with hm | hm
  · exact hH hm
  · exact hG hm

private theorem OptWfRel.cons_var {V₁ V₂ : Ty → Type} {G' : Ctx V₁ V₂}
    {G : Ctx (OptArg V₁) (OptArg V₂)}
    (hG : OptWfRel G' G) {t : Ty} (v₁ : V₁ t) (v₂ : V₂ t) :
    OptWfRel (⟨t, v₁, v₂⟩ :: G') (⟨t, some (.var v₁), some (.var v₂)⟩ :: G) := by
  intro u o₁ o₂ hm
  cases hm with
  | head => exact Or.inr ⟨.var v₁, .var v₂, rfl, rfl, .var List.mem_cons_self⟩
  | tail _ hm => exact (hG.weaken (fun _ hp => List.mem_cons_of_mem _ hp)) hm

private theorem someVarsToOpt_optWfRel {V₁ V₂ : Ty → Type} :
    {ts : List Ty} → (xs₁ : Tup V₁ ts) → (xs₂ : Tup V₂ ts) →
    OptWfRel (Tup.zip xs₁ xs₂) (Tup.zip (someVarsToOpt xs₁) (someVarsToOpt xs₂))
  | [], (), (), _, _, _, hm => nomatch hm
  | _ :: _, (x₁, xs₁), (x₂, xs₂), _, _, _, hm => by
    cases hm with
    | head => exact Or.inr ⟨.var x₁, .var x₂, rfl, rfl, .var List.mem_cons_self⟩
    | tail _ hm =>
      exact OptWfRel.weaken (fun _ hp => List.mem_cons_of_mem _ hp)
        (someVarsToOpt_optWfRel xs₁ xs₂) hm

private theorem OptWfRel.append_someVars {V₁ V₂ : Ty → Type} {G' : Ctx V₁ V₂}
    {G : Ctx (OptArg V₁) (OptArg V₂)} (hG : OptWfRel G' G)
    {ts : List Ty} (xs₁ : Tup V₁ ts) (xs₂ : Tup V₂ ts) :
    OptWfRel (Tup.zip xs₁ xs₂ ++ G')
      (Tup.zip (someVarsToOpt xs₁) (someVarsToOpt xs₂) ++ G) :=
  OptWfRel.append
    (OptWfRel.weaken (fun _ hp => List.mem_append_left _ hp) (someVarsToOpt_optWfRel xs₁ xs₂))
    (OptWfRel.weaken (fun _ hp => List.mem_append_right _ hp) hG)

private theorem someArgsToOpt_optWfRel {V₁ V₂ : Ty → Type} {G' : Ctx V₁ V₂} :
    {ts : List Ty} → {a₁ : Tup (Arg V₁) ts} → {a₂ : Tup (Arg V₂) ts} →
    TRel (ArgRel G') a₁ a₂ →
    OptWfRel G' (Tup.zip (someArgsToOpt a₁) (someArgsToOpt a₂))
  | [], (), (), .nil, _, _, _, hm => nomatch hm
  | _ :: _, (_, _), (_, _), .cons ha has, _, _, _, hm => by
    cases hm with
    | head => exact Or.inr ⟨_, _, rfl, rfl, ha⟩
    | tail _ hm => exact someArgsToOpt_optWfRel has hm

private theorem tupWiden_optWfRel {V₁ V₂ : Ty → Type} {G' : Ctx V₁ V₂} :
    (ts : List Ty) → (bs : List Bool) →
    {ys₁ : Tup V₁ (filterTys ts bs)} → {ys₂ : Tup V₂ (filterTys ts bs)} →
    (∀ p ∈ Tup.zip ys₁ ys₂, p ∈ G') →
    OptWfRel G' (Tup.zip (tupWiden ts bs ys₁) (tupWiden ts bs ys₂))
  | [], _, _, _, _, _, _, _, hm => nomatch hm
  | _ :: ts, [], ys₁, ys₂, hmem, _, _, _, hm => by
    let p₁ : V₁ _ × Tup V₁ (filterTys ts []) := ys₁
    let p₂ : V₂ _ × Tup V₂ (filterTys ts []) := ys₂
    rw [tupWiden_nil_eq ys₁ p₁.1 p₁.2 rfl, tupWiden_nil_eq ys₂ p₂.1 p₂.2 rfl] at hm
    cases hm with
    | head => exact Or.inr ⟨_, _, rfl, rfl, .var (hmem _ List.mem_cons_self)⟩
    | tail _ hm' =>
      exact tupWiden_optWfRel ts [] (fun _ hp => hmem _ (List.mem_cons_of_mem _ hp)) hm'
  | _ :: ts, true :: bs, ys₁, ys₂, hmem, _, _, _, hm => by
    let p₁ : V₁ _ × Tup V₁ (filterTys ts bs) := ys₁
    let p₂ : V₂ _ × Tup V₂ (filterTys ts bs) := ys₂
    rw [tupWiden_true_eq ys₁ p₁.1 p₁.2 rfl, tupWiden_true_eq ys₂ p₂.1 p₂.2 rfl] at hm
    cases hm with
    | head => exact Or.inr ⟨_, _, rfl, rfl, .var (hmem _ List.mem_cons_self)⟩
    | tail _ hm' =>
      exact tupWiden_optWfRel ts bs (fun _ hp => hmem _ (List.mem_cons_of_mem _ hp)) hm'
  | _ :: ts, false :: bs, ys₁, ys₂, hmem, _, _, _, hm => by
    let p₁ : Tup V₁ (filterTys ts bs) := ys₁
    let p₂ : Tup V₂ (filterTys ts bs) := ys₂
    rw [tupWiden_false_eq ys₁ p₁ rfl, tupWiden_false_eq ys₂ p₂ rfl] at hm
    cases hm with
    | head => exact Or.inl ⟨rfl, rfl⟩
    | tail _ hm' => exact tupWiden_optWfRel ts bs hmem hm'

private theorem flatOptArg_argRel {V₁ V₂ : Ty → Type} {G' : Ctx V₁ V₂}
    {G : Ctx (OptArg V₁) (OptArg V₂)} (hG : OptWfRel G' G)
    {t : Ty} {a₁ : Arg (OptArg V₁) t} {a₂ : Arg (OptArg V₂) t} :
    ArgRel G t a₁ a₂ → ArgRel G' t (LeanQbe.T.LoopRotate.flatOptArg a₁)
      (LeanQbe.T.LoopRotate.flatOptArg a₂)
  | .var hm => by
    rcases hG hm with ⟨h1, h2⟩ | ⟨a₁', a₂', h1, h2, ha⟩
    · subst h1 h2; exact .imm default
    · subst h1 h2; exact ha
  | .imm c => .imm c

private theorem flatOptArgs_trel {V₁ V₂ : Ty → Type} {G' : Ctx V₁ V₂}
    {G : Ctx (OptArg V₁) (OptArg V₂)} (hG : OptWfRel G' G)
    {ts : List Ty} {as₁ : Tup (Arg (OptArg V₁)) ts} {as₂ : Tup (Arg (OptArg V₂)) ts} :
    TRel (ArgRel G) as₁ as₂ →
    TRel (ArgRel G') (LeanQbe.T.LoopRotate.flatOptArgs as₁)
      (LeanQbe.T.LoopRotate.flatOptArgs as₂) :=
  TRel.tupMapArg_rel (fun _ => LeanQbe.T.LoopRotate.flatOptArg)
    (fun _ => LeanQbe.T.LoopRotate.flatOptArg) (fun ha => flatOptArg_argRel hG ha)

private theorem flatOptOp_opRel {V₁ V₂ : Ty → Type} {G' : Ctx V₁ V₂}
    {G : Ctx (OptArg V₁) (OptArg V₂)} (hG : OptWfRel G' G)
    {rs : List Ty} {op₁ : Op (OptArg V₁) rs} {op₂ : Op (OptArg V₂) rs} :
    OpRel G op₁ op₂ →
    OpRel G' (LeanQbe.T.LoopRotate.flatOptOp op₁) (LeanQbe.T.LoopRotate.flatOptOp op₂)
  | .mk code hargs => .mk code (flatOptArgs_trel hG hargs)

/-- Label relation pairing `RotL` entries across target contexts `(G', D')`. -/
private inductive RotLRelEntry {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    (G' : Ctx V₁ V₂) (D' : Ctx L₁ L₂) :
    {ts : List Ty} → RotL V₁ L₁ rs ts → RotL V₂ L₂ rs ts → Prop
  | keep {ts : List Ty} {l₁ : L₁ ts} {l₂ : L₂ ts} :
      ⟨ts, l₁, l₂⟩ ∈ D' → RotLRelEntry G' D' (.keep l₁) (.keep l₂)
  | dead {ts : List Ty} :
      RotLRelEntry G' D' (ts := ts) .dead .dead
  | expand {ts : List Ty}
      {f₁ : Tup (Arg V₁) ts → Expr V₁ L₁ rs}
      {f₂ : Tup (Arg V₂) ts → Expr V₂ L₂ rs} :
      (∀ {G'' D''}, (∀ p ∈ G', p ∈ G'') → (∀ p ∈ D', p ∈ D'') →
        ∀ (a₁ : Tup (Arg V₁) ts) (a₂ : Tup (Arg V₂) ts),
          TRel (ArgRel G'') a₁ a₂ → Wf G'' D'' (f₁ a₁) (f₂ a₂)) →
      RotLRelEntry G' D' (.expand f₁) (.expand f₂)

private theorem RotLRelEntry.weaken {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G₁ G₂ : Ctx V₁ V₂} {D₁ D₂ : Ctx L₁ L₂}
    (hG : ∀ p ∈ G₁, p ∈ G₂) (hD : ∀ p ∈ D₁, p ∈ D₂)
    {ts : List Ty} {l₁ : RotL V₁ L₁ rs ts} {l₂ : RotL V₂ L₂ rs ts} :
    RotLRelEntry G₁ D₁ l₁ l₂ → RotLRelEntry G₂ D₂ l₁ l₂
  | .keep h => .keep (hD _ h)
  | .dead => .dead
  | .expand hb =>
    .expand fun hG' hD' => hb (fun _ hp => hG' _ (hG _ hp)) (fun _ hp => hD' _ (hD _ hp))

/-- Context-wide `RotLRelEntry` invariant. -/
private def RotLRel {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    (G' : Ctx V₁ V₂) (D' : Ctx L₁ L₂)
    (D : Ctx (RotL V₁ L₁ rs) (RotL V₂ L₂ rs)) : Prop :=
  ∀ p ∈ D, RotLRelEntry G' D' p.2.1 p.2.2

private theorem RotLRel.weaken {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G₁ G₂ : Ctx V₁ V₂} {D₁ D₂ : Ctx L₁ L₂}
    {D : Ctx (RotL V₁ L₁ rs) (RotL V₂ L₂ rs)}
    (hG : ∀ p ∈ G₁, p ∈ G₂) (hD : ∀ p ∈ D₁, p ∈ D₂)
    (h : RotLRel G₁ D₁ D) : RotLRel G₂ D₂ D :=
  fun p hp => (h p hp).weaken hG hD

private theorem RotLRel.append {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G' : Ctx V₁ V₂} {D' : Ctx L₁ L₂}
    {H D : Ctx (RotL V₁ L₁ rs) (RotL V₂ L₂ rs)}
    (hH : RotLRel G' D' H) (hD : RotLRel G' D' D) : RotLRel G' D' (H ++ D) := fun p hp =>
  (List.mem_append.1 hp).elim (hH p) (hD p)

private theorem wrapKeepLabels_rel {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G' : Ctx V₁ V₂} {D' : Ctx L₁ L₂} :
    {sig : List (List Ty)} → (Js₁ : Tup L₁ sig) → (Js₂ : Tup L₂ sig) →
    RotLRel G' (Tup.zip Js₁ Js₂ ++ D')
      (Tup.zip (wrapKeepLabels (V := V₁) (rs := rs) Js₁)
        (wrapKeepLabels (V := V₂) (rs := rs) Js₂))
  | [], (), (), _, hp => nomatch hp
  | _ :: _, (_, js₁), (_, js₂), p, hp => by
    cases hp with
    | head => exact .keep List.mem_cons_self
    | tail _ hp =>
      exact (wrapKeepLabels_rel js₁ js₂ p hp).weaken (fun _ h => h)
        (fun _ h => List.mem_cons_of_mem _ h)

private theorem exitLabels_rel {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G' : Ctx V₁ V₂} {D' : Ctx L₁ L₂} (ts : List Ty) :
    RotLRel G' D' (Tup.zip (exitLabels (V := V₁) (L := L₁) (rs := rs) ts)
      (exitLabels (V := V₂) (L := L₂) (rs := rs) ts)) := by
  intro p hp
  cases hp with
  | head => exact .dead
  | tail _ h => nomatch h

private theorem flatBlocks_get {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    {sig : List (List Ty)} → {bs : Blocks (OptArg V) (RotL V L rs) rs sig} →
    {ts : List Ty} → (i : Member ts sig) → (xs : Tup V ts) →
    (flatExpr.flatBlocks bs).get i xs = flatExpr (bs.get i (someVarsToOpt xs))
  | _, .cons _ _, _, .here, _ => rfl
  | _, .cons _ _, _, .there i, xs => flatBlocks_get i xs

/-- `flatExpr` preserves relational well-formedness `Wf`. -/
private theorem flatExpr_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx (OptArg V₁) (OptArg V₂)} {D : Ctx (RotL V₁ L₁ rs) (RotL V₂ L₂ rs)}
    {e₁ : Expr (OptArg V₁) (RotL V₁ L₁ rs) rs} {e₂ : Expr (OptArg V₂) (RotL V₂ L₂ rs) rs}
    (hwf : Wf G D e₁ e₂) :
    ∀ {G' : Ctx V₁ V₂} {D' : Ctx L₁ L₂},
      OptWfRel G' G → RotLRel G' D' D →
      Wf G' D' (flatExpr e₁) (flatExpr e₂) := by
  induction hwf using Wf.induct with
  | let_ hop _ ih =>
    intro G' D' hG hD
    exact .let_ (flatOptOp_opRel hG hop) fun xs₁ xs₂ =>
      ih (someVarsToOpt xs₁) (someVarsToOpt xs₂)
        (OptWfRel.append_someVars hG xs₁ xs₂)
        (RotLRel.weaken (fun _ hp => List.mem_append_right _ hp) (fun _ hp => hp) hD)
  | load t ha _ ih =>
    intro G' D' hG hD
    exact .load t (flatOptArg_argRel hG ha) fun v₁ v₂ =>
      ih (some (.var v₁)) (some (.var v₂)) (OptWfRel.cons_var hG v₁ v₂)
        (RotLRel.weaken (fun _ hp => List.mem_cons_of_mem _ hp) (fun _ hp => hp) hD)
  | store hv ha _ ih =>
    intro G' D' hG hD
    exact .store (flatOptArg_argRel hG hv) (flatOptArg_argRel hG ha) (ih hG hD)
  | call f hargs _ ih =>
    intro G' D' hG hD
    exact .call f (flatOptArgs_trel hG hargs) fun xs₁ xs₂ =>
      ih (someVarsToOpt xs₁) (someVarsToOpt xs₂)
        (OptWfRel.append_someVars hG xs₁ xs₂)
        (RotLRel.weaken (fun _ hp => List.mem_append_right _ hp) (fun _ hp => hp) hD)
  | jnz hc _ _ iht ihe =>
    intro G' D' hG hD
    exact .jnz (flatOptArg_argRel hG hc) (iht hG hD) (ihe hG hD)
  | jump hj hargs =>
    intro G' D' hG hD
    have hdj := hD _ hj
    dsimp only at hdj
    cases hdj with
    | keep hj' => exact .jump hj' (flatOptArgs_trel hG hargs)
    | dead => exact .hlt
    | expand hf => exact hf (fun _ h => h) (fun _ h => h) _ _ (flatOptArgs_trel hG hargs)
  | ret hvs =>
    intro G' D' hG _
    exact .ret (flatOptArgs_trel hG hvs)
  | exit f hargs =>
    intro G' D' hG _
    exact .exit f (flatOptArgs_trel hG hargs)
  | hlt =>
    intro _ _ _ _
    exact .hlt
  | @group _ D sig _ _ _ _ _ _ ihb ihk =>
    intro G' D' hG hD
    refine .group (fun Js₁ Js₂ => WfB.of_get fun i xs₁ xs₂ => ?_) (fun Js₁ Js₂ => ?_)
    · rw [flatBlocks_get, flatBlocks_get]
      have hD'' : RotLRel G' (Tup.zip Js₁ Js₂ ++ D')
          (Tup.zip (wrapKeepLabels Js₁) (wrapKeepLabels Js₂) ++ D) :=
        RotLRel.append (wrapKeepLabels_rel Js₁ Js₂)
          (RotLRel.weaken (fun _ h => h) (fun _ h => List.mem_append_right _ h) hD)
      exact ihb (wrapKeepLabels Js₁) (wrapKeepLabels Js₂) i
        (someVarsToOpt xs₁) (someVarsToOpt xs₂)
        (OptWfRel.append_someVars hG xs₁ xs₂)
        (RotLRel.weaken (fun _ hp => List.mem_append_right _ hp) (fun _ hp => hp) hD'')
    · exact ihk (wrapKeepLabels Js₁) (wrapKeepLabels Js₂) hG
        (RotLRel.append (wrapKeepLabels_rel Js₁ Js₂)
          (RotLRel.weaken (fun _ h => h) (fun _ h => List.mem_append_right _ h) hD))

private theorem hdrPeel_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G' : Ctx V₁ V₂} {tail : List Ty} (dir wantCont : Bool) :
    (hdr : HdrPlan) → (ms : List (List Bool)) →
    {params₁ : Tup V₁ (stepMasksSig hdr ms tail)} →
    {params₂ : Tup V₂ (stepMasksSig hdr ms tail)} →
    {G : Ctx (OptArg V₁) (OptArg V₂)} → {D : Ctx (RotL V₁ L₁ rs) (RotL V₂ L₂ rs)} →
    {e₁ : Expr (OptArg V₁) (RotL V₁ L₁ rs) rs} →
    {e₂ : Expr (OptArg V₂) (RotL V₂ L₂ rs) rs} →
    (∀ p ∈ Tup.zip params₁ params₂, p ∈ G') →
    OptWfRel G' G → Wf G D e₁ e₂ →
    ∃ G_out, OptWfRel G' G_out ∧
      Wf G_out D (hdrPeel dir wantCont hdr ms params₁ e₁)
        (hdrPeel dir wantCont hdr ms params₂ e₂)
  | [], _, _, _, _, _, e₁, e₂, _, hG, hwf => by
    cases hwf with
    | jnz _ ht he =>
      refine ⟨_, hG, ?_⟩
      cases hwd : wantCont == dir
      · dsimp only [hdrPeel]; simp [hwd, he]
      · dsimp only [hdrPeel]; simp [hwd, ht]
    | let_ _ _ | load _ _ _ | store _ _ _ | call _ _ _ | jump _ _ | ret _
    | exit _ _ | hlt | group _ _ =>
      exact ⟨_, hG, .hlt⟩
  | .let_ dts :: ss, ms, params₁, params₂, G, D, e₁, e₂, hpar, hG, hwf => by
    cases hwf with
    | @let_ _ _ dts' _ _ k₁ k₂ _ hk =>
      cases hdec : tysDecEq dts dts' with
      | isFalse hne =>
        have hne' : dts ≠ dts' := fun heq => hne heq
        obtain ⟨hf, hfeq⟩ := tysDecEq_false_of_ne hne'
        dsimp only [hdrPeel]; simp only [hfeq]; exact ⟨_, hG, .hlt⟩
      | isTrue heq =>
        subst heq
        dsimp only [hdrPeel]; simp only [tysDecEq_self_isTrue dts]
        have hL := tupSplit_mem_left (filterTys dts (ms.headD [])) hpar
        have hR := tupSplit_mem_right (filterTys dts (ms.headD [])) hpar
        let ys₁ := tupWiden dts (ms.headD []) (tupSplit (filterTys dts (ms.headD [])) params₁).1
        let ys₂ := tupWiden dts (ms.headD []) (tupSplit (filterTys dts (ms.headD [])) params₂).1
        have hGnext : OptWfRel G' (Tup.zip ys₁ ys₂ ++ G) :=
          OptWfRel.append (tupWiden_optWfRel dts (ms.headD []) hL) hG
        exact hdrPeel_wf dir wantCont ss ms.tail hR hGnext (hk ys₁ ys₂)
    | load _ _ _ | store _ _ _ | call _ _ _ | jnz _ _ _ | jump _ _ | ret _
    | exit _ _ | hlt | group _ _ =>
      exact ⟨_, hG, .hlt⟩
  | .load t :: ss, ms, params₁, params₂, G, D, e₁, e₂, hpar, hG, hwf => by
    cases hwf with
    | @load _ _ t' _ _ k₁ k₂ _ hk =>
      cases hdec : tyDecEq t t' with
      | isFalse hne =>
        have hne' : t ≠ t' := fun heq => hne heq
        obtain ⟨hf, hfeq⟩ := tyDecEq_false_of_ne hne'
        dsimp only [hdrPeel]; simp only [hfeq]; exact ⟨_, hG, .hlt⟩
      | isTrue heq =>
        subst heq
        dsimp only [hdrPeel]; simp only [tyDecEq_self_isTrue t]
        have hL := tupSplit_mem_left (filterTys [t] (ms.headD [])) hpar
        have hR := tupSplit_mem_right (filterTys [t] (ms.headD [])) hpar
        have w : OptWfRel G' (Tup.zip (tupWiden [t] (ms.headD [])
            (tupSplit (filterTys [t] (ms.headD [])) params₁).1)
            (tupWiden [t] (ms.headD [])
            (tupSplit (filterTys [t] (ms.headD [])) params₂).1)) :=
          tupWiden_optWfRel [t] (ms.headD []) hL
        let y₁ := (tupWiden [t] (ms.headD []) (tupSplit (filterTys [t] (ms.headD [])) params₁).1).1
        let y₂ := (tupWiden [t] (ms.headD []) (tupSplit (filterTys [t] (ms.headD [])) params₂).1).1
        have hGnext : OptWfRel G' (⟨t, y₁, y₂⟩ :: G) := by
          intro u o₁ o₂ hm
          cases hm with
          | head => exact w List.mem_cons_self
          | tail _ hm => exact hG hm
        exact hdrPeel_wf dir wantCont ss ms.tail hR hGnext (hk y₁ y₂)
    | let_ _ _ | store _ _ _ | call _ _ _ | jnz _ _ _ | jump _ _ | ret _
    | exit _ _ | hlt | group _ _ =>
      exact ⟨_, hG, .hlt⟩

private theorem hdrEmit_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {D' : Ctx L₁ L₂} {tailC tailX : List Ty} (dir : Bool) :
    (hdr : HdrPlan) → (cMs xMs : List (List Bool)) →
    {G' : Ctx V₁ V₂} →
    {G : Ctx (OptArg V₁) (OptArg V₂)} → {D : Ctx (RotL V₁ L₁ rs) (RotL V₂ L₂ rs)} →
    {e₁ : Expr (OptArg V₁) (RotL V₁ L₁ rs) rs} →
    {e₂ : Expr (OptArg V₂) (RotL V₂ L₂ rs) rs} →
    {tc₁ : Tup (Arg V₁) tailC} → {tc₂ : Tup (Arg V₂) tailC} →
    {tx₁ : Tup (Arg V₁) tailX} → {tx₂ : Tup (Arg V₂) tailX} →
    {kC₁ : Tup (Arg V₁) (stepMasksSig hdr cMs tailC) → Expr V₁ L₁ rs} →
    {kC₂ : Tup (Arg V₂) (stepMasksSig hdr cMs tailC) → Expr V₂ L₂ rs} →
    {kX₁ : Expr (OptArg V₁) (RotL V₁ L₁ rs) rs →
      Tup (Arg V₁) (stepMasksSig hdr xMs tailX) → Expr V₁ L₁ rs} →
    {kX₂ : Expr (OptArg V₂) (RotL V₂ L₂ rs) rs →
      Tup (Arg V₂) (stepMasksSig hdr xMs tailX) → Expr V₂ L₂ rs} →
    OptWfRel G' G → RotLRel G' D' D → Wf G D e₁ e₂ →
    TRel (ArgRel G') tc₁ tc₂ → TRel (ArgRel G') tx₁ tx₂ →
    (∀ {G''}, (∀ p ∈ G', p ∈ G'') →
      ∀ {a₁ a₂}, TRel (ArgRel G'') a₁ a₂ → Wf G'' D' (kC₁ a₁) (kC₂ a₂)) →
    (∀ {G'' G_ex D_ex}, (∀ p ∈ G', p ∈ G'') → OptWfRel G'' G_ex → RotLRel G'' D' D_ex →
      ∀ {ex₁ ex₂}, Wf G_ex D_ex ex₁ ex₂ →
      ∀ {a₁ a₂}, TRel (ArgRel G'') a₁ a₂ → Wf G'' D' (kX₁ ex₁ a₁) (kX₂ ex₂ a₂)) →
    Wf G' D'
      (hdrEmit dir tc₁ tx₁ hdr cMs xMs e₁ kC₁ kX₁)
      (hdrEmit dir tc₂ tx₂ hdr cMs xMs e₂ kC₂ kX₂)
  | [], _, _, _, _, _, e₁, e₂, _, _, _, _, _, _, _, _, hG, hD, hwf, htc, htx, hkC, hkX => by
    cases hwf with
    | jnz hc ht he =>
      cases dir <;> dsimp only [hdrEmit]
      · exact .jnz (flatOptArg_argRel hG hc)
          (hkX (fun _ h => h) hG hD ht htx) (hkC (fun _ h => h) htc)
      · exact .jnz (flatOptArg_argRel hG hc)
          (hkC (fun _ h => h) htc) (hkX (fun _ h => h) hG hD he htx)
    | let_ _ _ | load _ _ _ | store _ _ _ | call _ _ _ | jump _ _ | ret _
    | exit _ _ | hlt | group _ _ =>
      exact .hlt
  | .let_ dts :: ss, cMs, xMs, G', G, D, e₁, e₂, tc₁, tc₂, tx₁, tx₂, kC₁, kC₂, kX₁, kX₂,
      hG, hD, hwf, htc, htx, hkC, hkX => by
    cases hwf with
    | @let_ _ _ dts' _ _ ek₁ ek₂ hop hk =>
      cases hdec : tysDecEq dts dts' with
      | isFalse hne =>
        have hne' : dts ≠ dts' := fun heq => hne heq
        obtain ⟨hf, hfeq⟩ := tysDecEq_false_of_ne hne'
        dsimp only [hdrEmit]; simp only [hfeq]; exact .hlt
      | isTrue heq =>
        subst heq
        dsimp only [hdrEmit]; simp only [tysDecEq_self_isTrue dts]
        refine .let_ (flatOptOp_opRel hG hop) fun ys₁ ys₂ => ?_
        have hsub : ∀ p ∈ G', p ∈ Tup.zip ys₁ ys₂ ++ G' := fun _ hp => List.mem_append_right _ hp
        refine hdrEmit_wf dir ss cMs.tail xMs.tail
          (OptWfRel.append_someVars hG ys₁ ys₂)
          (RotLRel.weaken hsub (fun _ h => h) hD)
          (hk (someVarsToOpt ys₁) (someVarsToOpt ys₂))
          (htc.argRel_weaken hsub) (htx.argRel_weaken hsub) ?_ ?_
        · intro G'' hG'' a₁ a₂ ha
          refine hkC (fun _ hp => hG'' _ (hsub _ hp)) ?_
          have hys : TRel (ArgRel G'') (toArgTup ys₁) (toArgTup ys₂) :=
            (toArgTup_trel ys₁ ys₂).argRel_weaken fun _ hp => hG'' _ (List.mem_append_left _ hp)
          exact tupAppend_argRel (tupSelectArgs_argRel dts (cMs.headD []) hys) ha
        · intro G'' G_ex D_ex hG'' hGex hDex _ _ hex a₁ a₂ ha
          refine hkX (fun _ hp => hG'' _ (hsub _ hp)) hGex hDex hex ?_
          have hys : TRel (ArgRel G'') (toArgTup ys₁) (toArgTup ys₂) :=
            (toArgTup_trel ys₁ ys₂).argRel_weaken fun _ hp => hG'' _ (List.mem_append_left _ hp)
          exact tupAppend_argRel (tupSelectArgs_argRel dts (xMs.headD []) hys) ha
    | load _ _ _ | store _ _ _ | call _ _ _ | jnz _ _ _ | jump _ _ | ret _
    | exit _ _ | hlt | group _ _ =>
      exact .hlt
  | .load t :: ss, cMs, xMs, G', G, D, e₁, e₂, tc₁, tc₂, tx₁, tx₂, kC₁, kC₂, kX₁, kX₂,
      hG, hD, hwf, htc, htx, hkC, hkX => by
    cases hwf with
    | @load _ _ t' _ _ ek₁ ek₂ ha hk =>
      cases hdec : tyDecEq t t' with
      | isFalse hne =>
        have hne' : t ≠ t' := fun heq => hne heq
        obtain ⟨hf, hfeq⟩ := tyDecEq_false_of_ne hne'
        dsimp only [hdrEmit]; simp only [hfeq]; exact .hlt
      | isTrue heq =>
        subst heq
        dsimp only [hdrEmit]; simp only [tyDecEq_self_isTrue t]
        refine .load t (flatOptArg_argRel hG ha) fun v₁ v₂ => ?_
        have hsub : ∀ p ∈ G', p ∈ ⟨t, v₁, v₂⟩ :: G' := fun _ hp => List.mem_cons_of_mem _ hp
        refine hdrEmit_wf dir ss cMs.tail xMs.tail
          (OptWfRel.cons_var hG v₁ v₂)
          (RotLRel.weaken hsub (fun _ h => h) hD)
          (hk (some (.var v₁)) (some (.var v₂)))
          (htc.argRel_weaken hsub) (htx.argRel_weaken hsub) ?_ ?_
        · intro G'' hG'' a₁ a₂ harg
          refine hkC (fun _ hp => hG'' _ (hsub _ hp)) ?_
          have hv : TRel (ArgRel G'') (as := [t]) (.var v₁, ()) (.var v₂, ()) :=
            .cons (.var (hG'' _ List.mem_cons_self)) .nil
          exact tupAppend_argRel (tupSelectArgs_argRel [t] (cMs.headD []) hv) harg
        · intro G'' G_ex D_ex hG'' hGex hDex _ _ hex a₁ a₂ harg
          refine hkX (fun _ hp => hG'' _ (hsub _ hp)) hGex hDex hex ?_
          have hv : TRel (ArgRel G'') (as := [t]) (.var v₁, ()) (.var v₂, ()) :=
            .cons (.var (hG'' _ List.mem_cons_self)) .nil
          exact tupAppend_argRel (tupSelectArgs_argRel [t] (xMs.headD []) hv) harg
    | let_ _ _ | store _ _ _ | call _ _ _ | jnz _ _ _ | jump _ _ | ret _
    | exit _ _ | hlt | group _ _ =>
      exact .hlt

private theorem rewriteRot_wf : (plan : RotPlan) →
    ∀ {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
      {G' : Ctx V₁ V₂} {D' : Ctx L₁ L₂}
      {G : Ctx (OptArg V₁) (OptArg V₂)} {D : Ctx (RotL V₁ L₁ rs) (RotL V₂ L₂ rs)}
      {e₁ : Expr (OptArg V₁) (RotL V₁ L₁ rs) rs}
      {e₂ : Expr (OptArg V₂) (RotL V₂ L₂ rs) rs},
      OptWfRel G' G → RotLRel G' D' D → Wf G D e₁ e₂ →
      Wf G' D' (rewriteRot plan e₁) (rewriteRot plan e₂)
  | .leaf => fun hG hD hwf => by
    dsimp only [rewriteRot]
    exact flatExpr_wf hwf hG hD
  | .letP p => fun hG hD hwf => by
    cases hwf with
    | let_ hop hk =>
      dsimp only [rewriteRot]
      exact .let_ (flatOptOp_opRel hG hop) fun xs₁ xs₂ =>
        rewriteRot_wf p
          (OptWfRel.append_someVars hG xs₁ xs₂)
          (RotLRel.weaken (fun _ hp => List.mem_append_right _ hp) (fun _ h => h) hD)
          (hk (someVarsToOpt xs₁) (someVarsToOpt xs₂))
    | load _ _ _ | store _ _ _ | call _ _ _ | jnz _ _ _ | jump _ _ | ret _
    | exit _ _ | hlt | group _ _ =>
      dsimp only [rewriteRot]; exact .hlt
  | .loadP p => fun hG hD hwf => by
    cases hwf with
    | load t ha hk =>
      dsimp only [rewriteRot]
      exact .load t (flatOptArg_argRel hG ha) fun v₁ v₂ =>
        rewriteRot_wf p (OptWfRel.cons_var hG v₁ v₂)
          (RotLRel.weaken (fun _ hp => List.mem_cons_of_mem _ hp) (fun _ h => h) hD)
          (hk (some (.var v₁)) (some (.var v₂)))
    | let_ _ _ | store _ _ _ | call _ _ _ | jnz _ _ _ | jump _ _ | ret _
    | exit _ _ | hlt | group _ _ =>
      dsimp only [rewriteRot]; exact .hlt
  | .storeP p => fun hG hD hwf => by
    cases hwf with
    | store hv ha hk =>
      dsimp only [rewriteRot]
      exact .store (flatOptArg_argRel hG hv) (flatOptArg_argRel hG ha) (rewriteRot_wf p hG hD hk)
    | let_ _ _ | load _ _ _ | call _ _ _ | jnz _ _ _ | jump _ _ | ret _
    | exit _ _ | hlt | group _ _ =>
      dsimp only [rewriteRot]; exact .hlt
  | .callP p => fun hG hD hwf => by
    cases hwf with
    | call f hargs hk =>
      dsimp only [rewriteRot]
      exact .call f (flatOptArgs_trel hG hargs) fun xs₁ xs₂ =>
        rewriteRot_wf p
          (OptWfRel.append_someVars hG xs₁ xs₂)
          (RotLRel.weaken (fun _ hp => List.mem_append_right _ hp) (fun _ h => h) hD)
          (hk (someVarsToOpt xs₁) (someVarsToOpt xs₂))
    | let_ _ _ | load _ _ _ | store _ _ _ | jnz _ _ _ | jump _ _ | ret _
    | exit _ _ | hlt | group _ _ =>
      dsimp only [rewriteRot]; exact .hlt
  | .jnzP tp ep => fun hG hD hwf => by
    cases hwf with
    | jnz hc ht he =>
      dsimp only [rewriteRot]
      exact .jnz (flatOptArg_argRel hG hc)
        (rewriteRot_wf tp hG hD ht) (rewriteRot_wf ep hG hD he)
    | let_ _ _ | load _ _ _ | store _ _ _ | call _ _ _ | jump _ _ | ret _
    | exit _ _ | hlt | group _ _ =>
      dsimp only [rewriteRot]; exact .hlt
  | .groupKeep bsP kP => fun hG hD hwf => by
    cases hwf with
    | @group _ _ sig b₁ b₂ k₁ k₂ hb hk =>
      dsimp only [rewriteRot]
      refine .group (fun Js₁ Js₂ => ?_) (fun Js₁ Js₂ => ?_)
      · have hD'' := RotLRel.append (wrapKeepLabels_rel Js₁ Js₂)
          (RotLRel.weaken (fun _ h => h) (fun _ h => List.mem_append_right _ h) hD)
        exact rewriteKeepB_wf bsP hG hD'' (hb (wrapKeepLabels Js₁) (wrapKeepLabels Js₂))
      · exact rewriteRot_wf kP hG
          (RotLRel.append (wrapKeepLabels_rel Js₁ Js₂)
            (RotLRel.weaken (fun _ h => h) (fun _ h => List.mem_append_right _ h) hD))
          (hk (wrapKeepLabels Js₁) (wrapKeepLabels Js₂))
    | let_ _ _ | load _ _ _ | store _ _ _ | call _ _ _ | jnz _ _ _ | jump _ _ | ret _
    | exit _ _ | hlt =>
      dsimp only [rewriteRot]; exact .hlt
  | .groupRot dir hdr contMasks exitMode contP exitP entryP => fun hG hD hwf => by
    suffices ∀ {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
        {G' : Ctx V₁ V₂} {D' : Ctx L₁ L₂}
        {G : Ctx (OptArg V₁) (OptArg V₂)} {D : Ctx (RotL V₁ L₁ rs) (RotL V₂ L₂ rs)}
        {e₁ : Expr (OptArg V₁) (RotL V₁ L₁ rs) rs}
        {e₂ : Expr (OptArg V₂) (RotL V₂ L₂ rs) rs},
        OptWfRel G' G → RotLRel G' D' D → Wf G D e₁ e₂ →
        Wf G' D'
          (rewriteRot (.groupRot dir hdr contMasks exitMode contP exitP entryP) e₁)
          (rewriteRot (.groupRot dir hdr contMasks exitMode contP exitP entryP) e₂) by
      exact this hG hD hwf
    intro V₁ V₂ L₁ L₂ rs G' D' G D e₁ e₂ hG hD hwf
    cases hwf with
    | @group _ _ sig bs₁ bs₂ k₁ k₂ hb hk =>
      cases sig with
      | nil => dsimp only [rewriteRot]; exact .hlt
      | cons ts sig' =>
        cases sig' with
        | cons _ _ => dsimp only [rewriteRot]; exact .hlt
        | nil =>
          cases exitMode with
          | inline =>
            dsimp only [rewriteRot]
            refine .group (fun (J_rot₁, ()) (J_rot₂, ()) => WfB.cons (fun p₁ p₂ => ?_) .nil)
              (fun (J_rot₁, ()) (J_rot₂, ()) => ?_)
            · let G'' := Tup.zip p₁ p₂ ++ G'
              let D'' := ⟨rotSig hdr contMasks ts, J_rot₁, J_rot₂⟩ :: D'
              have hG'sub : ∀ q ∈ G', q ∈ G'' := fun _ hq => List.mem_append_right _ hq
              have hD'sub : ∀ q ∈ D', q ∈ D'' := fun _ hq => List.mem_cons_of_mem _ hq
              have hRotMem : ⟨rotSig hdr contMasks ts, J_rot₁, J_rot₂⟩ ∈ D'' := List.mem_cons_self
              let mk₁ := fun (args : Tup (Arg _) ts) =>
                hdrEmit (tailC := ts) (tailX := ts) dir args args hdr contMasks []
                  ((bs₁ (exitLabels ts)).get .here (someArgsToOpt args))
                  (fun rotArgs => .jump J_rot₁ rotArgs)
                  (fun exitExpr _ => rewriteRot exitP exitExpr)
              let mk₂ := fun (args : Tup (Arg _) ts) =>
                hdrEmit (tailC := ts) (tailX := ts) dir args args hdr contMasks []
                  ((bs₂ (exitLabels ts)).get .here (someArgsToOpt args))
                  (fun rotArgs => .jump J_rot₂ rotArgs)
                  (fun exitExpr _ => rewriteRot exitP exitExpr)
              have hexpRel : RotLRel G'' D''
                  (Tup.zip (as := [ts]) (RotL.expand mk₁, ()) (RotL.expand mk₂, ()) ++ D) := by
                intro q hq
                cases hq with
                | head =>
                  refine .expand fun hG'' hD'' a₁ a₂ ha => ?_
                  refine hdrEmit_wf dir hdr contMasks []
                    (OptWfRel.append (someArgsToOpt_optWfRel ha)
                      (OptWfRel.weaken (fun _ hp => hG'' _ (hG'sub _ hp)) hG))
                    (RotLRel.append (exitLabels_rel ts)
                      (RotLRel.weaken (fun _ hp => hG'' _ (hG'sub _ hp))
                        (fun _ hp => hD'' _ (hD'sub _ hp)) hD))
                    ((hb (exitLabels ts) (exitLabels ts)).get .here (someArgsToOpt a₁)
                      (someArgsToOpt a₂))
                    ha ha ?_ ?_
                  · intro _ _ _ _ hrot
                    exact .jump (hD'' _ hRotMem) hrot
                  · intro _ _ _ _ hGex hDex _ _ hex _ _ _
                    exact rewriteRot_wf exitP hGex hDex hex
                | tail _ hq =>
                  exact RotLRel.weaken (fun _ hp => hG'sub _ hp) hD'sub hD q hq
              have hpMem : ∀ q ∈ Tup.zip p₁ p₂, q ∈ G'' := fun _ hq => List.mem_append_left _ hq
              have hxsMem : ∀ q ∈ Tup.zip (splitTail hdr contMasks p₁)
                  (splitTail hdr contMasks p₂), q ∈ G'' :=
                splitTail_mem hdr contMasks hpMem
              have hG_b : OptWfRel G''
                  (Tup.zip (someVarsToOpt (splitTail hdr contMasks p₁))
                    (someVarsToOpt (splitTail hdr contMasks p₂)) ++ G) :=
                OptWfRel.append
                  (OptWfRel.weaken hxsMem (someVarsToOpt_optWfRel _ _))
                  (OptWfRel.weaken hG'sub hG)
              obtain ⟨G_peel, hG_peel, hpeel⟩ := hdrPeel_wf dir true hdr contMasks hpMem hG_b
                ((hb (.expand mk₁, ()) (.expand mk₂, ())).get .here
                  (someVarsToOpt (splitTail hdr contMasks p₁))
                  (someVarsToOpt (splitTail hdr contMasks p₂)))
              exact rewriteRot_wf contP hG_peel hexpRel hpeel
            · let D'' := ⟨rotSig hdr contMasks ts, J_rot₁, J_rot₂⟩ :: D'
              have hD'sub : ∀ q ∈ D', q ∈ D'' := fun _ hq => List.mem_cons_of_mem _ hq
              have hRotMem : ⟨rotSig hdr contMasks ts, J_rot₁, J_rot₂⟩ ∈ D'' := List.mem_cons_self
              let mk₁ := fun (args : Tup (Arg _) ts) =>
                hdrEmit (tailC := ts) (tailX := ts) dir args args hdr contMasks []
                  ((bs₁ (exitLabels ts)).get .here (someArgsToOpt args))
                  (fun rotArgs => .jump J_rot₁ rotArgs)
                  (fun exitExpr _ => rewriteRot exitP exitExpr)
              let mk₂ := fun (args : Tup (Arg _) ts) =>
                hdrEmit (tailC := ts) (tailX := ts) dir args args hdr contMasks []
                  ((bs₂ (exitLabels ts)).get .here (someArgsToOpt args))
                  (fun rotArgs => .jump J_rot₂ rotArgs)
                  (fun exitExpr _ => rewriteRot exitP exitExpr)
              have hexpRel : RotLRel G' D''
                  (Tup.zip (as := [ts]) (RotL.expand mk₁, ()) (RotL.expand mk₂, ()) ++ D) := by
                intro q hq
                cases hq with
                | head =>
                  refine .expand fun hG'' hD'' a₁ a₂ ha => ?_
                  refine hdrEmit_wf dir hdr contMasks []
                    (OptWfRel.append (someArgsToOpt_optWfRel ha) (OptWfRel.weaken hG'' hG))
                    (RotLRel.append (exitLabels_rel ts)
                      (RotLRel.weaken hG'' (fun _ hp => hD'' _ (hD'sub _ hp)) hD))
                    ((hb (exitLabels ts) (exitLabels ts)).get .here (someArgsToOpt a₁)
                      (someArgsToOpt a₂))
                    ha ha ?_ ?_
                  · intro _ _ _ _ hrot
                    exact .jump (hD'' _ hRotMem) hrot
                  · intro _ _ _ _ hGex hDex _ _ hex _ _ _
                    exact rewriteRot_wf exitP hGex hDex hex
                | tail _ hq => exact RotLRel.weaken (fun _ h => h) hD'sub hD q hq
              exact rewriteRot_wf entryP hG hexpRel (hk (.expand mk₁, ()) (.expand mk₂, ()))
          | wrap xsMask hMasks =>
            dsimp only [rewriteRot]
            refine .group (fun (J_exit₁, ()) (J_exit₂, ()) => WfB.cons (fun x₁ x₂ => ?_) .nil)
              (fun (J_exit₁, ()) (J_exit₂, ()) => ?_)
            · let G'' := Tup.zip x₁ x₂ ++ G'
              have hG'sub : ∀ q ∈ G', q ∈ G'' := fun _ hq => List.mem_append_right _ hq
              have hxMem : ∀ q ∈ Tup.zip x₁ x₂, q ∈ G'' := fun _ hq => List.mem_append_left _ hq
              have hxtMem := splitTail_mem hdr hMasks hxMem
              have hG_b : OptWfRel G''
                  (Tup.zip (tupWiden ts xsMask (splitTail hdr hMasks x₁))
                    (tupWiden ts xsMask (splitTail hdr hMasks x₂)) ++ G) :=
                OptWfRel.append (tupWiden_optWfRel ts xsMask hxtMem)
                  (OptWfRel.weaken hG'sub hG)
              have hD_b : RotLRel G''
                  (Tup.zip (as := [exitSig hdr hMasks xsMask ts]) (J_exit₁, ()) (J_exit₂, ()) ++ D')
                  (Tup.zip (exitLabels ts) (exitLabels ts) ++ D) :=
                RotLRel.append (exitLabels_rel ts)
                  (RotLRel.weaken hG'sub (fun _ hq => List.mem_append_right _ hq) hD)
              obtain ⟨G_peel, hG_peel, hpeel⟩ := hdrPeel_wf dir false hdr hMasks hxMem hG_b
                ((hb (exitLabels ts) (exitLabels ts)).get .here
                  (tupWiden ts xsMask (splitTail hdr hMasks x₁))
                  (tupWiden ts xsMask (splitTail hdr hMasks x₂)))
              exact rewriteRot_wf exitP hG_peel hD_b hpeel
            · let D_ex := ⟨exitSig hdr hMasks xsMask ts, J_exit₁, J_exit₂⟩ :: D'
              have hDexSub : ∀ q ∈ D', q ∈ D_ex := fun _ hq => List.mem_cons_of_mem _ hq
              have hExitMem : ⟨exitSig hdr hMasks xsMask ts, J_exit₁, J_exit₂⟩ ∈ D_ex :=
                List.mem_cons_self
              have hDx : RotLRel G' D_ex D := RotLRel.weaken (fun _ h => h) hDexSub hD
              refine .group (fun (J_rot₁, ()) (J_rot₂, ()) => WfB.cons (fun p₁ p₂ => ?_) .nil)
                (fun (J_rot₁, ()) (J_rot₂, ()) => ?_)
              · let G'' := Tup.zip p₁ p₂ ++ G'
                let D'' := ⟨rotSig hdr contMasks ts, J_rot₁, J_rot₂⟩ :: D_ex
                have hG'sub : ∀ q ∈ G', q ∈ G'' := fun _ hq => List.mem_append_right _ hq
                have hD'sub : ∀ q ∈ D_ex, q ∈ D'' := fun _ hq => List.mem_cons_of_mem _ hq
                have hRotMem : ⟨rotSig hdr contMasks ts, J_rot₁, J_rot₂⟩ ∈ D'' :=
                  List.mem_cons_self
                let mk₁ := fun (args : Tup (Arg _) ts) =>
                  hdrEmit (tailC := ts) (tailX := filterTys ts xsMask)
                    dir args (tupSelectArgs ts xsMask args) hdr contMasks hMasks
                    ((bs₁ (exitLabels ts)).get .here (someArgsToOpt args))
                    (fun rotArgs => .jump J_rot₁ rotArgs)
                    (fun _ exitArgs => .jump J_exit₁ exitArgs)
                let mk₂ := fun (args : Tup (Arg _) ts) =>
                  hdrEmit (tailC := ts) (tailX := filterTys ts xsMask)
                    dir args (tupSelectArgs ts xsMask args) hdr contMasks hMasks
                    ((bs₂ (exitLabels ts)).get .here (someArgsToOpt args))
                    (fun rotArgs => .jump J_rot₂ rotArgs)
                    (fun _ exitArgs => .jump J_exit₂ exitArgs)
                have hexpRel : RotLRel G'' D''
                    (Tup.zip (as := [ts]) (RotL.expand mk₁, ()) (RotL.expand mk₂, ()) ++ D) := by
                  intro q hq
                  cases hq with
                  | head =>
                    refine .expand fun hG'' hD'' a₁ a₂ ha => ?_
                    refine hdrEmit_wf dir hdr contMasks hMasks
                      (OptWfRel.append (someArgsToOpt_optWfRel ha)
                        (OptWfRel.weaken (fun _ hp => hG'' _ (hG'sub _ hp)) hG))
                      (RotLRel.append (exitLabels_rel ts)
                        (RotLRel.weaken (fun _ hp => hG'' _ (hG'sub _ hp))
                          (fun _ hp => hD'' _ (hD'sub _ hp)) hDx))
                      ((hb (exitLabels ts) (exitLabels ts)).get .here (someArgsToOpt a₁)
                        (someArgsToOpt a₂))
                      ha (tupSelectArgs_argRel ts xsMask ha) ?_ ?_
                    · intro _ _ _ _ hrot
                      exact .jump (hD'' _ hRotMem) hrot
                    · intro _ _ _ _ _ _ _ _ _ _ _ hexArgs
                      exact .jump (hD'' _ (hD'sub _ hExitMem)) hexArgs
                  | tail _ hq => exact RotLRel.weaken hG'sub hD'sub hDx q hq
                have hpMem : ∀ q ∈ Tup.zip p₁ p₂, q ∈ G'' := fun _ hq => List.mem_append_left _ hq
                have hxsMem := splitTail_mem hdr contMasks hpMem
                have hG_b : OptWfRel G''
                    (Tup.zip (someVarsToOpt (splitTail hdr contMasks p₁))
                      (someVarsToOpt (splitTail hdr contMasks p₂)) ++ G) :=
                  OptWfRel.append
                    (OptWfRel.weaken hxsMem (someVarsToOpt_optWfRel _ _))
                    (OptWfRel.weaken hG'sub hG)
                obtain ⟨G_peel, hG_peel, hpeel⟩ := hdrPeel_wf dir true hdr contMasks hpMem hG_b
                  ((hb (.expand mk₁, ()) (.expand mk₂, ())).get .here
                    (someVarsToOpt (splitTail hdr contMasks p₁))
                    (someVarsToOpt (splitTail hdr contMasks p₂)))
                exact rewriteRot_wf contP hG_peel hexpRel hpeel
              · let D'' := ⟨rotSig hdr contMasks ts, J_rot₁, J_rot₂⟩ :: D_ex
                have hD'sub : ∀ q ∈ D_ex, q ∈ D'' := fun _ hq => List.mem_cons_of_mem _ hq
                have hRotMem : ⟨rotSig hdr contMasks ts, J_rot₁, J_rot₂⟩ ∈ D'' :=
                  List.mem_cons_self
                let mk₁ := fun (args : Tup (Arg _) ts) =>
                  hdrEmit (tailC := ts) (tailX := filterTys ts xsMask)
                    dir args (tupSelectArgs ts xsMask args) hdr contMasks hMasks
                    ((bs₁ (exitLabels ts)).get .here (someArgsToOpt args))
                    (fun rotArgs => .jump J_rot₁ rotArgs)
                    (fun _ exitArgs => .jump J_exit₁ exitArgs)
                let mk₂ := fun (args : Tup (Arg _) ts) =>
                  hdrEmit (tailC := ts) (tailX := filterTys ts xsMask)
                    dir args (tupSelectArgs ts xsMask args) hdr contMasks hMasks
                    ((bs₂ (exitLabels ts)).get .here (someArgsToOpt args))
                    (fun rotArgs => .jump J_rot₂ rotArgs)
                    (fun _ exitArgs => .jump J_exit₂ exitArgs)
                have hexpRel : RotLRel G' D''
                    (Tup.zip (as := [ts]) (RotL.expand mk₁, ()) (RotL.expand mk₂, ()) ++ D) := by
                  intro q hq
                  cases hq with
                  | head =>
                    refine .expand fun hG'' hD'' a₁ a₂ ha => ?_
                    refine hdrEmit_wf dir hdr contMasks hMasks
                      (OptWfRel.append (someArgsToOpt_optWfRel ha) (OptWfRel.weaken hG'' hG))
                      (RotLRel.append (exitLabels_rel ts)
                        (RotLRel.weaken hG'' (fun _ hp => hD'' _ (hD'sub _ hp)) hDx))
                      ((hb (exitLabels ts) (exitLabels ts)).get .here (someArgsToOpt a₁)
                        (someArgsToOpt a₂))
                      ha (tupSelectArgs_argRel ts xsMask ha) ?_ ?_
                    · intro _ _ _ _ hrot
                      exact .jump (hD'' _ hRotMem) hrot
                    · intro _ _ _ _ _ _ _ _ _ _ _ hexArgs
                      exact .jump (hD'' _ (hD'sub _ hExitMem)) hexArgs
                  | tail _ hq => exact RotLRel.weaken (fun _ h => h) hD'sub hDx q hq
                exact rewriteRot_wf entryP hG hexpRel (hk (.expand mk₁, ()) (.expand mk₂, ()))
    | let_ _ _ | load _ _ _ | store _ _ _ | call _ _ _ | jnz _ _ _ | jump _ _ | ret _
    | exit _ _ | hlt =>
      dsimp only [rewriteRot]; exact .hlt
where
  rewriteKeepB_wf : (ps : List RotPlan) →
      ∀ {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
        {G' : Ctx V₁ V₂} {D' : Ctx L₁ L₂}
        {G : Ctx (OptArg V₁) (OptArg V₂)} {D : Ctx (RotL V₁ L₁ rs) (RotL V₂ L₂ rs)}
        {sig : List (List Ty)}
        {bs₁ : Blocks (OptArg V₁) (RotL V₁ L₁ rs) rs sig}
        {bs₂ : Blocks (OptArg V₂) (RotL V₂ L₂ rs) rs sig},
        OptWfRel G' G → RotLRel G' D' D → WfB G D bs₁ bs₂ →
        WfB G' D' (rewriteRot.rewriteKeepB ps bs₁) (rewriteRot.rewriteKeepB ps bs₂)
    | [] => fun hG hD hbs => by
      cases hbs with
      | nil => dsimp only [rewriteRot.rewriteKeepB, flatExpr.flatBlocks]; exact .nil
      | cons hb hbs' =>
        dsimp only [rewriteRot.rewriteKeepB, flatExpr.flatBlocks]
        refine .cons (fun xs₁ xs₂ => ?_) ?_
        · exact flatExpr_wf (hb (someVarsToOpt xs₁) (someVarsToOpt xs₂))
            (OptWfRel.append_someVars hG xs₁ xs₂)
            (RotLRel.weaken (fun _ hp => List.mem_append_right _ hp) (fun _ h => h) hD)
        · exact rewriteKeepB_wf [] hG hD hbs'
    | p :: ps => fun hG hD hbs => by
      cases hbs with
      | nil => dsimp only [rewriteRot.rewriteKeepB]; exact .nil
      | cons hb hbs' =>
        dsimp only [rewriteRot.rewriteKeepB]
        refine .cons (fun xs₁ xs₂ => ?_) (rewriteKeepB_wf ps hG hD hbs')
        exact rewriteRot_wf p
          (OptWfRel.append_someVars hG xs₁ xs₂)
          (RotLRel.weaken (fun _ hp => List.mem_append_right _ hp) (fun _ h => h) hD)
          (hb (someVarsToOpt xs₁) (someVarsToOpt xs₂))

/-! ## Weakest-precondition invariants (`NoneDeadOpt`, `SomeValEq`, `ValidDk`, `RotWpD`) -/

/-- Whether a `RotL` label is live (not `.dead`). -/
private def rotLIsLive {V : Ty → Type} {L : List Ty → Type} {rs ts : List Ty} :
    RotL V L rs ts → Bool
  | .keep _ => true
  | .expand _ => true
  | .dead => false

/-- Every `true` label in `Dk` pairs with a live (`keep` or `expand`) `RotL` label. -/
private def ValidDk {rs : List Ty} (Dk : Ctx BoolL (RotL Val Cont rs)) : Prop :=
  ∀ p ∈ Dk, p.2.1 = true → rotLIsLive p.2.2 = true

private theorem ValidDk.append {rs : List Ty} {H Dk : Ctx BoolL (RotL Val Cont rs)}
    (hH : ValidDk H) (hD : ValidDk Dk) : ValidDk (H ++ Dk) := fun p hp =>
  (List.mem_append.1 hp).elim (hH p) (hD p)

private theorem validDk_wrapKeepLabels {rs : List Ty} :
    {sig : List (List Ty)} → (Js : Tup Cont sig) →
    ValidDk (Tup.zip (trueLabels sig) (wrapKeepLabels (V := Val) (rs := rs) Js))
  | [], (), _, hp, _ => nomatch hp
  | _ :: _, (_, Js), p, hp, h => by
    cases hp with
    | head => rfl
    | tail _ hp => exact validDk_wrapKeepLabels Js p hp h

/-- Every dropped (`none`) binder level in `Gk` is absent from liveness trie `s`. -/
private def NoneDeadOpt {V : Ty → Type} (s : Trie Unit) (Gk : Ctx K (OptArg V)) : Prop :=
  ∀ {t : Ty} {k : Nat} {o : OptArg V t}, ⟨t, k, o⟩ ∈ Gk → o = none → (s.find? k).isSome = false

private theorem NoneDeadOpt.sub {V : Ty → Type} {s₁ s₂ : Trie Unit} {Gk : Ctx K (OptArg V)}
    (hsub : TrieSub s₁ s₂) (hnd : NoneDeadOpt s₂ Gk) : NoneDeadOpt s₁ Gk := by
  intro t k o hm ho
  cases hmem : (s₁.find? k).isSome with
  | false => rfl
  | true =>
    have hmem2 := hsub k hmem
    have hf := hnd hm ho
    rw [hf] at hmem2
    cases hmem2

private theorem NoneDeadOpt.cons_some {V : Ty → Type} {s : Trie Unit} {Gk : Ctx K (OptArg V)}
    (hnd : NoneDeadOpt s Gk) {t : Ty} (k : Nat) (a : Arg V t) :
    NoneDeadOpt s (⟨t, k, some a⟩ :: Gk) := by
  intro _ _ _ hm ho
  cases hm with
  | head => cases ho
  | tail _ hm' => exact hnd hm' ho

private theorem NoneDeadOpt.append_some {V : Ty → Type} {s : Trie Unit} {Gk : Ctx K (OptArg V)}
    (hnd : NoneDeadOpt s Gk) :
    {ts : List Ty} → (ks : Tup K ts) → (as : Tup (Arg V) ts) →
    NoneDeadOpt s (Tup.zip ks (someArgsToOpt as) ++ Gk)
  | [], (), () => hnd
  | _ :: _, (k, ks), (a, as) =>
    NoneDeadOpt.cons_some (NoneDeadOpt.append_some hnd ks as) k a

private theorem NoneDeadOpt.append_someVars {V : Ty → Type} {s : Trie Unit} {Gk : Ctx K (OptArg V)}
    (hnd : NoneDeadOpt s Gk) :
    {ts : List Ty} → (ks : Tup K ts) → (xs : Tup V ts) →
    NoneDeadOpt s (Tup.zip ks (someVarsToOpt xs) ++ Gk)
  | [], (), () => hnd
  | _ :: _, (k, ks), (x, xs) =>
    NoneDeadOpt.cons_some (NoneDeadOpt.append_someVars hnd ks xs) k (.var x)

private theorem checkDeadMask_noneDeadOpt {lvl : Nat} {s : Trie Unit} {Gk : Ctx K (OptArg Val)} :
    (ts : List Ty) → (bs : List Bool) →
    checkDeadMask lvl s ts bs = true →
    ∀ (ys : Tup Val (filterTys ts bs)), NoneDeadOpt s Gk →
      NoneDeadOpt s (Tup.zip (Tup.levels ts lvl) (tupWiden ts bs ys) ++ Gk)
  | [], _, _, _, hnd => hnd
  | _ :: ts, [], hchk, ys, hnd => by
    dsimp only [checkDeadMask, List.headD, List.tail] at hchk
    simp only [Bool.and_eq_true] at hchk
    let p : Val _ × Tup Val (filterTys ts []) := ys
    rw [tupWiden_nil_eq ys p.1 p.2 rfl]
    exact NoneDeadOpt.cons_some (checkDeadMask_noneDeadOpt ts [] hchk.2 p.2 hnd) lvl (.var p.1)
  | _ :: ts, true :: bs, hchk, ys, hnd => by
    dsimp only [checkDeadMask, List.headD, List.tail] at hchk
    simp only [Bool.and_eq_true] at hchk
    let p : Val _ × Tup Val (filterTys ts bs) := ys
    rw [tupWiden_true_eq ys p.1 p.2 rfl]
    exact NoneDeadOpt.cons_some (checkDeadMask_noneDeadOpt ts bs hchk.2 p.2 hnd) lvl (.var p.1)
  | _ :: ts, false :: bs, hchk, ys, hnd => by
    dsimp only [checkDeadMask, List.headD, List.tail] at hchk
    simp only [Bool.and_eq_true] at hchk
    let p : Tup Val (filterTys ts bs) := ys
    rw [tupWiden_false_eq ys p rfl]
    intro hm ho
    cases hm with
    | head => simpa [Tup.levels] using hchk.1
    | tail _ hm' => exact checkDeadMask_noneDeadOpt ts bs hchk.2 p hnd hm' ho

/-- Every kept (`some a`) binder in `G` agrees in semantic value with its paired `Val`. -/
private def SomeValEq (G : Ctx (OptArg Val) Val) : Prop :=
  ∀ {t : Ty} {o : OptArg Val t} {v : Val t}, ⟨t, o, v⟩ ∈ G →
    ∀ a : Arg Val t, o = some a → a.val = v

private theorem SomeValEq.cons_some {G : Ctx (OptArg Val) Val} (hG : SomeValEq G)
    {t : Ty} {a : Arg Val t} {v : Val t} (ha : a.val = v) :
    SomeValEq (⟨t, some a, v⟩ :: G) := by
  intro _ _ _ hm a' hw
  cases hm with
  | head => injection hw with heq; subst heq; exact ha
  | tail _ hm' => exact hG hm' a' hw

private theorem SomeValEq.cons_none {G : Ctx (OptArg Val) Val} (hG : SomeValEq G)
    {t : Ty} (v : Val t) : SomeValEq (⟨t, none, v⟩ :: G) := by
  intro _ _ _ hm _ hw
  cases hm with
  | head => cases hw
  | tail _ hm' => exact hG hm' _ hw

private theorem SomeValEq.append_someVars {G : Ctx (OptArg Val) Val} (hG : SomeValEq G) :
    {ts : List Ty} → (xs : Tup Val ts) → SomeValEq (Tup.zip (someVarsToOpt xs) xs ++ G)
  | [], () => hG
  | _ :: _, (_, xs) => SomeValEq.cons_some (SomeValEq.append_someVars hG xs) rfl

private theorem SomeValEq.append_someArgs {G : Ctx (OptArg Val) Val} (hG : SomeValEq G) :
    {ts : List Ty} → {args : Tup (Arg Val) ts} → {xs : Tup Val ts} →
    vals args = xs → SomeValEq (Tup.zip (someArgsToOpt args) xs ++ G)
  | [], (), (), _ => hG
  | _ :: _, (a, args), (x, xs), h => by
    simp only [vals, Prod.mk.injEq] at h
    exact SomeValEq.cons_some (SomeValEq.append_someArgs hG h.2) h.1

private theorem SomeValEq.append_tupWiden_tupSelectVals
    {G : Ctx (OptArg Val) Val} (hG : SomeValEq G) :
    (ts : List Ty) → (bs : List Bool) → {ys xs : Tup Val ts} →
    ys = xs →
    SomeValEq (Tup.zip (tupWiden ts bs (tupSelectVals ts bs ys)) xs ++ G)
  | [], _, (), (), _ => hG
  | _ :: ts, [], (y, ys), (x, xs), h => by
    simp only [Prod.mk.injEq] at h
    rw [tupWiden_tupSelectVals_nil]
    exact SomeValEq.cons_some (SomeValEq.append_tupWiden_tupSelectVals hG ts [] h.2)
      (a := .var y) (v := x) h.1
  | _ :: ts, true :: bs, (y, ys), (x, xs), h => by
    simp only [Prod.mk.injEq] at h
    rw [tupWiden_tupSelectVals_true]
    exact SomeValEq.cons_some (SomeValEq.append_tupWiden_tupSelectVals hG ts bs h.2)
      (a := .var y) (v := x) h.1
  | _ :: ts, false :: bs, (y, ys), (x, xs), h => by
    simp only [Prod.mk.injEq] at h
    rw [tupWiden_tupSelectVals_false]
    exact SomeValEq.cons_none (SomeValEq.append_tupWiden_tupSelectVals hG ts bs h.2) x

private theorem flatOptArg_val_of_inSet {s : Trie Unit} {Gk : Ctx K (OptArg Val)}
    {G : Ctx (OptArg Val) Val} (hnd : NoneDeadOpt s Gk) (hG : SomeValEq G)
    {t : Ty} {ak : Arg K t} {a₁ : Arg (OptArg Val) t} {a₂ : Arg Val t}
    (hk : ArgRel Gk t ak a₁) (h12 : ArgRel G t a₁ a₂) (hin : ak.InSet s) :
    (flatOptArg a₁).val = a₂.val := by
  cases h12 with
  | imm _ => rfl
  | var hm12 =>
    cases hk with
    | var hmk =>
      rename_i o v k
      cases o with
      | some a => exact hG hm12 a rfl
      | none =>
        have hfalse := hnd hmk rfl
        have hkmem : (s.find? k).isSome = true := hin
        rw [hfalse] at hkmem
        cases hkmem

private theorem flatOptArgs_vals_of_inSet {s : Trie Unit} {Gk : Ctx K (OptArg Val)}
    {G : Ctx (OptArg Val) Val} (hnd : NoneDeadOpt s Gk) (hG : SomeValEq G) :
    {ts : List Ty} → {aks : Tup (Arg K) ts} → {as₁ : Tup (Arg (OptArg Val)) ts} →
    {as₂ : Tup (Arg Val) ts} →
    TRel (ArgRel Gk) aks as₁ → TRel (ArgRel G) as₁ as₂ → ArgsInSet s aks →
    vals (flatOptArgs as₁) = vals as₂
  | [], (), (), (), .nil, .nil, _ => rfl
  | _ :: _, (_, _), (_, _), (_, _), .cons hka hkas, .cons h12a h12as, ⟨ha, has⟩ =>
    Prod.ext (flatOptArg_val_of_inSet hnd hG hka h12a ha)
      (flatOptArgs_vals_of_inSet hnd hG hkas h12as has)

/-- Weakest-precondition invariant relating `RotL Val Cont rs` labels to source `Cont`s. -/
private def RotWpD (Γ : Env) {rs : List Ty} (Q : Post rs) (X : XPost)
    (D : Ctx (RotL Val Cont rs) Cont) : Prop :=
  ∀ p ∈ D, match p.2.1 with
    | .keep J => J = p.2.2
    | .dead => True
    | .expand f => ∀ (args : Tup (Arg Val) p.1) (m : Mem 64),
        p.2.2 (vals args) m → wp Γ Q X (f args) m

private theorem RotWpD.append {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {H D : Ctx (RotL Val Cont rs) Cont}
    (hH : RotWpD Γ Q X H) (hD : RotWpD Γ Q X D) : RotWpD Γ Q X (H ++ D) := fun p hp =>
  (List.mem_append.1 hp).elim (hH p) (hD p)

private theorem rotWpD_wrapKeepLabels (Γ : Env) {rs : List Ty} (Q : Post rs) (X : XPost) :
    {sig : List (List Ty)} → (Js : Tup Cont sig) →
    RotWpD Γ Q X (Tup.zip (wrapKeepLabels (V := Val) (rs := rs) Js) Js)
  | [], (), _, hp => nomatch hp
  | _ :: _, (_, Js), p, hp => by
    cases hp with
    | head => rfl
    | tail _ hp => exact rotWpD_wrapKeepLabels Γ Q X Js p hp

private theorem validDk_exitLabels {rs : List Ty} (ts : List Ty) :
    ValidDk (Tup.zip (false, ()) (exitLabels (V := Val) (L := Cont) (rs := rs) ts)) := by
  intro p hp htrue
  cases hp with
  | head => cases htrue
  | tail _ hp => nomatch hp

private theorem rotWpD_exitLabels (Γ : Env) {rs : List Ty} (Q : Post rs) (X : XPost) (ts : List Ty)
    (Js : Tup Cont [ts]) :
    RotWpD Γ Q X (Tup.zip (exitLabels (V := Val) (L := Cont) (rs := rs) ts) Js) := by
  intro p hp
  cases hp with
  | head => trivial
  | tail _ hp => nomatch hp

/-- Diagonal invariant on `K`-to-`K` relational contexts used to relate `bs true` and `bs false`. -/
private def DiagK (Gk : Ctx K K) : Prop :=
  ∀ p ∈ Gk, p.2.1 = p.2.2

private theorem DiagK.cons_eq {Gk : Ctx K K} (h : DiagK Gk) {t : Ty} (k : Nat) :
    DiagK (⟨t, k, k⟩ :: Gk) := by
  intro p hp
  cases hp with
  | head => rfl
  | tail _ hp' => exact h p hp'

private theorem DiagK.append_zip_eq {Gk : Ctx K K} (h : DiagK Gk) :
    {ts : List Ty} → (ks : Tup K ts) → DiagK (Tup.zip ks ks ++ Gk)
  | [], () => h
  | _ :: _, (k, ks) => (DiagK.append_zip_eq h ks).cons_eq k

private theorem ArgRel.diag_eq {Gk : Ctx K K} (h : DiagK Gk) {t : Ty} {a₁ a₂ : Arg K t} :
    ArgRel Gk t a₁ a₂ → a₁ = a₂
  | .var hm => by have := h _ hm; dsimp only at this; rw [this]
  | .imm _ => rfl

private theorem TRel.diag_eq {Gk : Ctx K K} (h : DiagK Gk) :
    {ts : List Ty} → {as₁ as₂ : Tup (Arg K) ts} → TRel (ArgRel Gk) as₁ as₂ → as₁ = as₂
  | [], (), (), .nil => rfl
  | _ :: _, (_, _), (_, _), .cons ha has =>
    Prod.ext (ArgRel.diag_eq h ha) (TRel.diag_eq h has)

private theorem validateLeafB_get {rs : List Ty} :
    {sig : List (List Ty)} → {bsk : Blocks K BoolL rs sig} → {nv : Nat} → {sb : Trie Unit} →
    validateLeaf.validateLeafB bsk nv = some sb →
    ∀ {ts} (i : Member ts sig),
      ∃ s_i, validateLeaf (bsk.get i (Tup.levels ts nv)) (nv + ts.length) = some s_i ∧
        TrieSub s_i sb
  | _, .cons _ _, _, _, hval, _, .here => by
    dsimp only [validateLeaf.validateLeafB] at hval
    rcases Option.bind_eq_some_iff.1 hval with ⟨s₁, hs₁, hrest⟩
    rcases Option.bind_eq_some_iff.1 hrest with ⟨s₂, _, heq⟩
    cases heq
    exact ⟨s₁, hs₁, TrieSub.union_left s₁ s₂⟩
  | _, .cons (ts := ts') _ bs, nv, _, hval, _, .there i => by
    dsimp only [validateLeaf.validateLeafB] at hval
    rcases Option.bind_eq_some_iff.1 hval with ⟨s₁, _, hrest⟩
    rcases Option.bind_eq_some_iff.1 hrest with ⟨s₂, hs₂, heq⟩
    cases heq
    obtain ⟨si, hsi, hsub⟩ := validateLeafB_get hs₂ i
    exact ⟨si, hsi, hsub.trans (TrieSub.union_right s₁ s₂)⟩

private theorem validateHdr_diag_eq {rs : List Ty} :
    (hdr : HdrPlan) → {nv : Nat} →
    {Gk : Ctx K K} → {Dk : Ctx BoolL BoolL} → {ek₁ ek₂ : Expr K BoolL rs} →
    DiagK Gk → Wf Gk Dk ek₁ ek₂ →
    {sh₁ sh₂ : Trie Unit} → {armT₁ armE₁ armT₂ armE₂ : Expr K BoolL rs} → {nv₁ nv₂ : Nat} →
    validateHdr hdr ek₁ nv = some (sh₁, armT₁, armE₁, nv₁) →
    validateHdr hdr ek₂ nv = some (sh₂, armT₂, armE₂, nv₂) →
    sh₁ = sh₂ ∧ nv₁ = nv₂ ∧
      ∃ Gk' : Ctx K K, DiagK Gk' ∧ Wf Gk' Dk armT₁ armT₂ ∧ Wf Gk' Dk armE₁ armE₂
  | [], nv, Gk, Dk, _, _, hdiag, hwf, _, _, _, _, _, _, _, _, h1, h2 => by
    cases hwf with
    | jnz hc ht he =>
      dsimp only [validateHdr] at h1 h2; simp only [pure, Option.some.injEq, Prod.mk.injEq] at h1 h2
      rcases h1 with ⟨rfl, rfl, rfl, rfl⟩
      rcases h2 with ⟨rfl, rfl, rfl, rfl⟩
      rw [ArgRel.diag_eq hdiag hc]
      exact ⟨rfl, rfl, Gk, hdiag, ht, he⟩
    | let_ _ _ | load _ _ _ | store _ _ _ | call _ _ _ | jump _ _ | ret _
    | exit _ _ | hlt | group _ _ =>
      dsimp only [validateHdr] at h1; cases h1
  | .let_ dts :: ss, nv, Gk, Dk, _, _, hdiag, hwf, _, _, _, _, _, _, _, _, h1, h2 => by
    cases hwf with
    | @let_ _ _ dts' op₁ op₂ _ _ hop hk =>
      dsimp only [validateHdr] at h1 h2
      cases hdec : tysDecEq dts dts' with
      | isFalse => simp [hdec] at h1
      | isTrue heq =>
        subst heq
        simp only [tysDecEq_self_isTrue dts] at h1 h2
        rcases Option.bind_eq_some_iff.1 h1 with ⟨⟨s₁, t₁, e₁, n₁⟩, h1', heq1⟩
        rcases Option.bind_eq_some_iff.1 h2 with ⟨⟨s₂, t₂, e₂, n₂⟩, h2', heq2⟩
        cases heq1; cases heq2
        cases hop with | mk _ hargs =>
        have harg_eq := TRel.diag_eq hdiag hargs
        obtain ⟨rfl, rfl, Gk', hdiag', ht', he'⟩ :=
          validateHdr_diag_eq ss (DiagK.append_zip_eq hdiag (Tup.levels dts nv))
            (hk _ _) h1' h2'
        rw [harg_eq]
        exact ⟨rfl, rfl, Gk', hdiag', ht', he'⟩
    | load _ _ _ | store _ _ _ | call _ _ _ | jnz _ _ _ | jump _ _ | ret _
    | exit _ _ | hlt | group _ _ =>
      dsimp only [validateHdr] at h1; cases h1
  | .load t :: ss, nv, Gk, Dk, _, _, hdiag, hwf, _, _, _, _, _, _, _, _, h1, h2 => by
    cases hwf with
    | @load _ _ t' a₁ a₂ _ _ ha hk =>
      dsimp only [validateHdr] at h1 h2
      cases hdec : tyDecEq t t' with
      | isFalse => simp [hdec] at h1
      | isTrue heq =>
        subst heq
        simp only [tyDecEq_self_isTrue t] at h1 h2
        rcases Option.bind_eq_some_iff.1 h1 with ⟨⟨s₁, t₁, e₁, n₁⟩, h1', heq1⟩
        rcases Option.bind_eq_some_iff.1 h2 with ⟨⟨s₂, t₂, e₂, n₂⟩, h2', heq2⟩
        cases heq1; cases heq2
        obtain ⟨rfl, rfl, Gk', hdiag', ht', he'⟩ :=
          validateHdr_diag_eq ss (DiagK.cons_eq hdiag nv) (hk nv nv) h1' h2'
        rw [ArgRel.diag_eq hdiag ha]
        exact ⟨rfl, rfl, Gk', hdiag', ht', he'⟩
    | let_ _ _ | store _ _ _ | call _ _ _ | jnz _ _ _ | jump _ _ | ret _
    | exit _ _ | hlt | group _ _ =>
      dsimp only [validateHdr] at h1; cases h1

/-! ## Weakest-precondition soundness (`flatExpr_wp`, `hdrEmit_wp`, `hdrPeel_wf_src`) -/

private theorem TrieSub.addArgsSet {ts : List Ty} (as : Tup (Arg K) ts) (s : Trie Unit) :
    TrieSub s (LoopRotate.addArgsSet as s) :=
  TrieSub.addArgKeys as s

/-- `flatExpr` preserves `wp` whenever `validateLeaf` succeeds. -/
private theorem flatExpr_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {G : Ctx (OptArg Val) Val} {D : Ctx (RotL Val Cont rs) Cont}
    {e₁ : Expr (OptArg Val) (RotL Val Cont rs) rs} {e₂ : Expr Val Cont rs}
    (hwf : Wf G D e₁ e₂) :
    ∀ {Gk : Ctx K (OptArg Val)} {Dk : Ctx BoolL (RotL Val Cont rs)}
      {ek : Expr K BoolL rs} {nv : Nat} {s : Trie Unit},
      Wf Gk Dk ek e₁ → validateLeaf ek nv = some s →
      NoneDeadOpt s Gk → SomeValEq G →
      ValidDk Dk → RotWpD Γ Q X D →
      ∀ m, wp Γ Q X e₂ m → wp Γ Q X (flatExpr e₁) m := by
  induction hwf using Wf.induct with
  | let_ hop _ ih =>
    intro Gk Dk ek nv s hwk hval hnd hG hDk hD m hw2
    rcases hwk.rhs_let with ⟨opk, kk, rfl, hopk, hkk⟩
    dsimp only [validateLeaf] at hval
    rcases Option.bind_eq_some_iff.1 hval with ⟨sk, hvk, hret⟩
    cases hret
    cases hop with | mk code hargs =>
    cases hopk with | mk _ hargsk =>
    dsimp only [flatExpr]; simp only [flatOptOp, wp, Op.wp] at hw2 ⊢
    rw [flatOptArgs_vals_of_inSet hnd hG hargsk hargs (ArgsInSet.addArgKeys _ _)]
    refine OpCode.wp_mono code _ (fun r hr => ?_) hw2
    exact ih (someVarsToOpt r) r (hkk (Tup.levels _ nv) (someVarsToOpt r)) hvk
      (NoneDeadOpt.append_someVars (NoneDeadOpt.sub (TrieSub.addArgsSet _ _) hnd) _ _)
      (SomeValEq.append_someVars hG r) hDk hD m hr
  | load t ha _ ih =>
    intro Gk Dk ek nv s hwk hval hnd hG hDk hD m ⟨v, hv, hw2⟩
    rcases hwk.rhs_load with ⟨ak, kk, rfl, hak, hkk⟩
    dsimp only [validateLeaf] at hval
    rcases Option.bind_eq_some_iff.1 hval with ⟨sk, hvk, hret⟩
    cases hret
    dsimp only [flatExpr]; simp only [wp]
    rw [flatOptArg_val_of_inSet hnd hG hak ha (Arg.InSet.addArgKey _ _)]
    exact ⟨v, hv, ih (some (.var v)) v (hkk nv (some (.var v))) hvk
      (NoneDeadOpt.cons_some (NoneDeadOpt.sub (TrieSub.addArgKey _ _) hnd) nv (.var v))
      (SomeValEq.cons_some hG (a := .var v) rfl) hDk hD m hw2⟩
  | store hv ha _ ih =>
    intro Gk Dk ek nv s hwk hval hnd hG hDk hD m ⟨hok, hw2⟩
    rcases hwk.rhs_store with ⟨vk, ak, kk, rfl, hvk, hak, hkk⟩
    dsimp only [validateLeaf] at hval
    rcases Option.bind_eq_some_iff.1 hval with ⟨sk, hvk', hret⟩
    cases hret
    dsimp only [flatExpr]; simp only [wp]
    have hv_in : Arg.InSet (addArgKey vk (addArgKey ak sk)) vk := Arg.InSet.addArgKey _ _
    have ha_in : Arg.InSet (addArgKey vk (addArgKey ak sk)) ak :=
      (Arg.InSet.addArgKey _ _).mono (TrieSub.addArgKey _ _)
    rw [flatOptArg_val_of_inSet hnd hG hvk hv hv_in,
      flatOptArg_val_of_inSet hnd hG hak ha ha_in]
    have hsub : TrieSub sk (addArgKey vk (addArgKey ak sk)) :=
      (TrieSub.addArgKey ak sk).trans (TrieSub.addArgKey vk _)
    exact ⟨hok, ih hkk hvk' (NoneDeadOpt.sub hsub hnd) hG hDk hD _ hw2⟩
  | call f hargs _ ih =>
    intro Gk Dk ek nv s hwk hval hnd hG hDk hD m ⟨P, E, hΓ, hP, hE⟩
    rcases hwk.rhs_call with ⟨argsk, kk, rfl, hargsk, hkk⟩
    dsimp only [validateLeaf] at hval
    rcases Option.bind_eq_some_iff.1 hval with ⟨sk, hvk, hret⟩
    cases hret
    dsimp only [flatExpr]; simp only [wp]
    rw [flatOptArgs_vals_of_inSet hnd hG hargsk hargs (ArgsInSet.addArgKeys _ _)]
    have hsub := TrieSub.addArgsSet argsk sk
    exact ⟨P, E, hΓ, fun r m' hp =>
      ih (someVarsToOpt r) r (hkk (Tup.levels _ nv) (someVarsToOpt r)) hvk
        (NoneDeadOpt.append_someVars (NoneDeadOpt.sub hsub hnd) _ _)
        (SomeValEq.append_someVars hG r) hDk hD m' (hP r m' hp), hE⟩
  | jnz hc _ _ iht ihe =>
    intro Gk Dk ek nv s hwk hval hnd hG hDk hD m hw2
    rcases hwk.rhs_jnz with ⟨ck, tk, ek', rfl, hck, htk, hek⟩
    dsimp only [validateLeaf] at hval
    rcases Option.bind_eq_some_iff.1 hval with ⟨st, hvt, hrest⟩
    rcases Option.bind_eq_some_iff.1 hrest with ⟨se, hve, hret⟩
    cases hret
    dsimp only [flatExpr]; simp only [wp] at hw2 ⊢
    rw [flatOptArg_val_of_inSet hnd hG hck hc (Arg.InSet.addArgKey _ _)]
    have hsubT : TrieSub st (addArgKey ck (trieUnion st se)) :=
      (TrieSub.union_left st se).trans (TrieSub.addArgKey _ _)
    have hsubE : TrieSub se (addArgKey ck (trieUnion st se)) :=
      (TrieSub.union_right st se).trans (TrieSub.addArgKey _ _)
    exact ⟨fun h => iht htk hvt (NoneDeadOpt.sub hsubT hnd) hG hDk hD m (hw2.1 h),
      fun h => ihe hek hve (NoneDeadOpt.sub hsubE hnd) hG hDk hD m (hw2.2 h)⟩
  | @jump _ _ _ j₁ _ _ _ hj hargs =>
    intro Gk Dk ek nv s hwk hval hnd hG hDk hD m hw2
    rcases hwk.rhs_jump with ⟨lb, argsk, rfl, hjk, hargsk⟩
    dsimp only [validateLeaf] at hval
    cases hlb : lb with
    | false => simp [hlb] at hval
    | true =>
      simp only [hlb, ↓reduceIte, pure, Option.some.injEq] at hval
      subst hval
      have hlive : rotLIsLive j₁ = true := hDk _ hjk hlb
      have hvals := flatOptArgs_vals_of_inSet hnd hG hargsk hargs (ArgsInSet.addArgKeys _ _)
      have hd := hD _ hj
      cases j₁ with
      | keep J =>
        dsimp only [flatExpr]; simp only [wp] at hw2 ⊢
        dsimp only at hd
        rw [hvals, hd]
        exact hw2
      | dead => simp [rotLIsLive] at hlive
      | expand fn =>
        dsimp only [flatExpr]
        dsimp only at hd
        exact hd _ m (by rw [hvals]; exact hw2)
  | ret hvs =>
    intro Gk Dk ek nv s hwk hval hnd hG _ _ m hw2
    rcases hwk.rhs_ret with ⟨vsk, rfl, hvsk⟩
    dsimp only [validateLeaf] at hval; simp only [pure, Option.some.injEq] at hval
    subst hval
    dsimp only [flatExpr]; simp only [wp] at hw2 ⊢
    rwa [flatOptArgs_vals_of_inSet hnd hG hvsk hvs (ArgsInSet.addArgKeys _ _)]
  | exit f hargs =>
    intro Gk Dk ek nv s hwk hval hnd hG _ _ m hw2
    rcases hwk.rhs_exit with ⟨argsk, rfl, hargsk⟩
    dsimp only [validateLeaf] at hval; simp only [pure, Option.some.injEq] at hval
    subst hval
    dsimp only [flatExpr]; simp only [wp] at hw2 ⊢
    rwa [flatOptArgs_vals_of_inSet hnd hG hargsk hargs (ArgsInSet.addArgKeys _ _)]
  | hlt =>
    intro _ _ _ _ _ hwk _ _ _ _ _ _ hw2
    rcases hwk.rhs_hlt with rfl
    exact hw2
  | @group G D sig b₁ b₂ k₁ k₂ _ _ ihb ihk =>
    intro Gk Dk ek nv s hwk hval hnd hG hDk hD m hw2
    rcases hwk.rhs_group with ⟨bk, kk, rfl, hbk, hkk⟩
    dsimp only [validateLeaf] at hval
    rcases Option.bind_eq_some_iff.1 hval with ⟨sb, hvb, hrest⟩
    rcases Option.bind_eq_some_iff.1 hrest with ⟨sk, hvk, hret⟩
    cases hret
    dsimp only [flatExpr]; simp only [wp]
    intro Js_out hcl_out
    have hDk' := ValidDk.append (validDk_wrapKeepLabels Js_out) hDk
    have hD' := RotWpD.append (rotWpD_wrapKeepLabels Γ Q X Js_out) hD
    have hndB : NoneDeadOpt sb Gk := NoneDeadOpt.sub (TrieSub.union_left sb sk) hnd
    have hndK : NoneDeadOpt sk Gk := NoneDeadOpt.sub (TrieSub.union_right sb sk) hnd
    have hcl₂ : Closed Γ Q X (b₂ Js_out) Js_out := by
      rw [closed_iff] at hcl_out ⊢
      intro ts i xs m' hw
      simp only [flatBlocks_get] at hcl_out
      obtain ⟨si, hsi, hsubi⟩ := validateLeafB_get hvb i
      exact hcl_out i xs m'
        (ihb (wrapKeepLabels Js_out) Js_out i (someVarsToOpt xs) xs
          ((hbk (trueLabels sig) (wrapKeepLabels Js_out)).get i (Tup.levels ts nv)
            (someVarsToOpt xs))
          hsi (NoneDeadOpt.append_someVars (NoneDeadOpt.sub hsubi hndB) _ _)
          (SomeValEq.append_someVars hG xs) hDk' hD' m' hw)
    exact ihk (wrapKeepLabels Js_out) Js_out
      (hkk (trueLabels sig) (wrapKeepLabels Js_out))
      hvk hndK hG hDk' hD' m (hw2 Js_out hcl₂)

/-- Navigate `e_src : Expr Val Cont rs` down header `hdr` using step values `hv : HdrVals hdr`,
returning the chosen post-`.jnz` arm (`cont` if `wantCont = true`, `exit` if `false`). -/
private def hdrSrcBranch {rs : List Ty} (dir wantCont : Bool) :
    (hdr : HdrPlan) → HdrVals hdr → Expr Val Cont rs → Option (Expr Val Cont rs)
  | [], (), .jnz _ armT armE => some (if wantCont == dir then armT else armE)
  | .let_ dts :: ss, (ys, rest), .let_ (ts := dts') _ k =>
    match tysDecEq dts dts' with
    | isTrue h => hdrSrcBranch dir wantCont ss rest (k (h ▸ ys))
    | isFalse _ => none
  | .load t :: ss, (y, rest), .load t' _ k =>
    match tyDecEq t t' with
    | isTrue h => hdrSrcBranch dir wantCont ss rest (k (h ▸ y.1))
    | isFalse _ => none
  | _, _, _ => none

private theorem hdrEmit_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} (dir : Bool)
    {tailC tailX : List Ty} :
    (hdr : HdrPlan) → (cMs xMs : List (List Bool)) → {nv : Nat} →
    {Gk : Ctx K (OptArg Val)} → {Gk_diag : Ctx K K} →
    {Dk : Ctx BoolL (RotL Val Cont rs)} → {Dk_diag : Ctx BoolL BoolL} →
    {G : Ctx (OptArg Val) Val} → {D : Ctx (RotL Val Cont rs) Cont} →
    {ek : Expr K BoolL rs} →
    {e_emit : Expr (OptArg Val) (RotL Val Cont rs) rs} →
    {e_src : Expr Val Cont rs} →
    {sh : Trie Unit} → {armTk armEk : Expr K BoolL rs} → {nv' : Nat} →
    validateHdr hdr ek nv = some (sh, armTk, armEk, nv') →
    Wf Gk Dk ek e_emit → Wf Gk_diag Dk_diag ek ek → Wf G D e_emit e_src →
    NoneDeadOpt sh Gk → SomeValEq G → DiagK Gk_diag →
    {tc_args : Tup (Arg Val) tailC} → {tc_vals : Tup Val tailC} →
    {tx_args : Tup (Arg Val) tailX} → {tx_vals : Tup Val tailX} →
    vals tc_args = tc_vals → vals tx_args = tx_vals →
    {kC : Tup (Arg Val) (stepMasksSig hdr cMs tailC) → Expr Val Cont rs} →
    {kX : Expr (OptArg Val) (RotL Val Cont rs) rs →
      Tup (Arg Val) (stepMasksSig hdr xMs tailX) → Expr Val Cont rs} →
    {m₀ : Mem 64} → wp Γ Q X e_src m₀ →
    (∀ (hv : HdrVals hdr) (m' : Mem 64) (armC_src : Expr Val Cont rs)
      (rotArgs : Tup (Arg Val) (stepMasksSig hdr cMs tailC)),
      hdrSrcBranch dir true hdr hv e_src = some armC_src →
      wp Γ Q X armC_src m' → vals rotArgs = hdrSelect hdr cMs hv tc_vals →
      wp Γ Q X (kC rotArgs) m') →
    (∀ (hv : HdrVals hdr) (m' : Mem 64)
      (Gk_leaf : Ctx K (OptArg Val)) (Gk_diag_leaf : Ctx K K) (G_leaf : Ctx (OptArg Val) Val)
      (armX_emit : Expr (OptArg Val) (RotL Val Cont rs) rs) (armX_src : Expr Val Cont rs)
      (exitArgs : Tup (Arg Val) (stepMasksSig hdr xMs tailX)),
      (∀ s, NoneDeadOpt s Gk → NoneDeadOpt s Gk_leaf) →
      SomeValEq G_leaf → DiagK Gk_diag_leaf →
      Wf Gk_leaf Dk (if dir then armEk else armTk) armX_emit →
      Wf Gk_diag_leaf Dk_diag (if dir then armEk else armTk) (if dir then armEk else armTk) →
      Wf G_leaf D armX_emit armX_src →
      hdrSrcBranch dir false hdr hv e_src = some armX_src →
      wp Γ Q X armX_src m' → vals exitArgs = hdrSelect hdr xMs hv tx_vals →
      wp Γ Q X (kX armX_emit exitArgs) m') →
    wp Γ Q X (hdrEmit dir tc_args tx_args hdr cMs xMs e_emit kC kX) m₀
  | [], cMs, xMs, nv, Gk, Gk_diag, Dk, Dk_diag, G, D, ek, e_emit, e_src,
      sh, armTk, armEk, nv', hval, hwk, hwk_diag, hwf, hnd, hG, hdiag,
      tc_args, tc_vals, tx_args, tx_vals, htc, htx, kC, kX, m₀, hw2, hC, hX => by
    cases hwf with
    | @jnz _ _ c₁ c₂ t₁ t₂ e₁' e₂' hc ht he =>
      rcases hwk.rhs_jnz with ⟨ck, tk, ek', rfl, hck, htk, hek⟩
      rcases hwk_diag.jnz_inv with ⟨_, htkd, hekd⟩
      dsimp only [validateHdr] at hval; simp only [pure, Option.some.injEq, Prod.mk.injEq] at hval
      rcases hval with ⟨rfl, rfl, rfl, rfl⟩
      have hcval : (flatOptArg c₁).val = c₂.val :=
        flatOptArg_val_of_inSet hnd hG hck hc (Arg.InSet.addArgKey _ _)
      simp only [wp] at hw2
      cases dir with
      | false =>
        dsimp only [hdrEmit]; simp only [wp, Bool.false_eq_true, ↓reduceIte]
        rw [hcval]
        refine ⟨fun hcT => ?_, fun hcF => ?_⟩
        · exact hX () m₀ Gk Gk_diag G t₁ t₂ tx_args (fun _ h => h) hG hdiag htk htkd ht
            rfl (hw2.1 hcT) htx
        · exact hC () m₀ e₂' tc_args rfl (hw2.2 hcF) htc
      | true =>
        dsimp only [hdrEmit]; simp only [wp, ↓reduceIte]
        rw [hcval]
        refine ⟨fun hcT => ?_, fun hcF => ?_⟩
        · exact hC () m₀ t₂ tc_args rfl (hw2.1 hcT) htc
        · exact hX () m₀ Gk Gk_diag G e₁' e₂' tx_args (fun _ h => h) hG hdiag hek hekd he
            rfl (hw2.2 hcF) htx
    | let_ _ _ | load _ _ _ | store _ _ _ | call _ _ _ | jump _ _ | ret _
    | exit _ _ | hlt | group _ _ =>
      cases hwk <;> (dsimp only [validateHdr] at hval; cases hval)
  | .let_ dts :: ss, cMs, xMs, nv, Gk, Gk_diag, Dk, Dk_diag, G, D, ek, e_emit, e_src,
      sh, armTk, armEk, nv', hval, hwk, hwk_diag, hwf, hnd, hG, hdiag,
      tc_args, tc_vals, tx_args, tx_vals, htc, htx, kC, kX, m₀, hw2, hC, hX => by
    cases hwf with
    | @let_ _ _ dts' op₁ op₂ ke₁ ke₂ hop hk =>
      rcases hwk.rhs_let with ⟨opk, kk, rfl, hopk, hkk⟩
      rcases hwk_diag.let_inv with ⟨_, hkkd⟩
      dsimp only [validateHdr] at hval
      cases hdec : tysDecEq dts dts' with
      | isFalse => simp [hdec] at hval
      | isTrue heq =>
        subst heq
        simp only [tysDecEq_self_isTrue dts] at hval
        rcases Option.bind_eq_some_iff.1 hval with ⟨⟨s', t', e', n'⟩, hv', heq⟩
        cases heq
        have hsub : TrieSub s' (addArgsSet opk.args s') := TrieSub.addArgsSet _ _
        cases hop with | mk code hargs =>
        cases hopk with | mk _ hargsk =>
        dsimp only [hdrEmit]; simp only [tysDecEq_self_isTrue dts, flatOptOp, wp, Op.wp] at hw2 ⊢
        have hvals := flatOptArgs_vals_of_inSet hnd hG hargsk hargs (ArgsInSet.addArgKeys _ _)
        rw [hvals]
        refine OpCode.wp_mono code _ (fun ys hys => ?_) hw2
        refine hdrEmit_wp dir ss cMs.tail xMs.tail (nv := nv + dts.length) hv'
          (hkk (Tup.levels dts nv) (someVarsToOpt ys))
          (hkkd (Tup.levels dts nv) (Tup.levels dts nv))
          (hk (someVarsToOpt ys) ys)
          (NoneDeadOpt.append_someVars (NoneDeadOpt.sub hsub hnd) _ _)
          (SomeValEq.append_someVars hG ys)
          (DiagK.append_zip_eq hdiag (Tup.levels dts nv)) htc htx hys ?_ ?_
        · intro hv_rest m' armC_src restArgs hbr hwC hrest_eq
          refine hC (ys, hv_rest) m' armC_src
            (tupAppend (tupSelectArgs dts (cMs.headD []) (toArgTup ys)) restArgs)
            ?_ hwC ?_
          · simpa [hdrSrcBranch, tysDecEq_self_isTrue dts] using hbr
          · rw [vals_tupAppend, vals_tupSelectArgs, toArgTup_vals, hrest_eq]; rfl
        · intro hv_rest m' Gk_l Gkd_l G_l armX_em armX_s restArgs hnd_l hG_l hdk_l hwk_l hwkd_l
            hwf_l hbr hwX hrest_eq
          refine hX (ys, hv_rest) m' Gk_l Gkd_l G_l armX_em armX_s
            (tupAppend (tupSelectArgs dts (xMs.headD []) (toArgTup ys)) restArgs)
            (fun s hs => hnd_l s (NoneDeadOpt.append_someVars hs _ _)) hG_l hdk_l hwk_l hwkd_l
            hwf_l ?_ hwX ?_
          · simpa [hdrSrcBranch, tysDecEq_self_isTrue dts] using hbr
          · rw [vals_tupAppend, vals_tupSelectArgs, toArgTup_vals, hrest_eq]; rfl
    | load _ _ _ | store _ _ _ | call _ _ _ | jnz _ _ _ | jump _ _ | ret _
    | exit _ _ | hlt | group _ _ =>
      cases hwk <;> (dsimp only [validateHdr] at hval; cases hval)
  | .load t :: ss, cMs, xMs, nv, Gk, Gk_diag, Dk, Dk_diag, G, D, ek, e_emit, e_src,
      sh, armTk, armEk, nv', hval, hwk, hwk_diag, hwf, hnd, hG, hdiag,
      tc_args, tc_vals, tx_args, tx_vals, htc, htx, kC, kX, m₀, hw2, hC, hX => by
    cases hwf with
    | @load _ _ t' a₁ a₂ ke₁ ke₂ ha hk =>
      rcases hwk.rhs_load with ⟨ak, kk, rfl, hak, hkk⟩
      rcases hwk_diag.load_inv with ⟨_, hkkd⟩
      dsimp only [validateHdr] at hval
      cases hdec : tyDecEq t t' with
      | isFalse => simp [hdec] at hval
      | isTrue heq =>
        subst heq
        simp only [tyDecEq_self_isTrue t] at hval
        rcases Option.bind_eq_some_iff.1 hval with ⟨⟨s', t', e', n'⟩, hv', heq⟩
        cases heq
        rcases hw2 with ⟨v, hv_ld, hys⟩
        dsimp only [hdrEmit]; simp only [tyDecEq_self_isTrue t, wp]
        rw [flatOptArg_val_of_inSet hnd hG hak ha (Arg.InSet.addArgKey _ _)]
        have hsub : TrieSub s' (addArgKey ak s') := TrieSub.addArgKey _ _
        refine ⟨v, hv_ld, hdrEmit_wp dir ss cMs.tail xMs.tail (nv := nv + 1) hv'
          (hkk nv (some (.var v))) (hkkd nv nv) (hk (some (.var v)) v)
          (NoneDeadOpt.cons_some (NoneDeadOpt.sub hsub hnd) nv (.var v))
          (SomeValEq.cons_some hG (v := v) rfl)
          (DiagK.cons_eq hdiag nv) htc htx hys ?_ ?_⟩
        · intro hv_rest m' armC_src restArgs hbr hwC hrest_eq
          refine hC ((v, ()), hv_rest) m' armC_src
            (tupAppend (tupSelectArgs [t] (cMs.headD []) (.var v, ())) restArgs)
            ?_ hwC ?_
          · simpa [hdrSrcBranch, tyDecEq_self_isTrue t] using hbr
          · rw [vals_tupAppend, vals_tupSelectArgs]
            simpa [hdrSelect, vals] using
              congrArg (tupAppend (tupSelectVals [t] (cMs.headD []) (v, ()))) hrest_eq
        · intro hv_rest m' Gk_l Gkd_l G_l armX_em armX_s restArgs hnd_l hG_l hdk_l hwk_l hwkd_l
            hwf_l hbr hwX hrest_eq
          refine hX ((v, ()), hv_rest) m' Gk_l Gkd_l G_l armX_em armX_s
            (tupAppend (tupSelectArgs [t] (xMs.headD []) (.var v, ())) restArgs)
            (fun s hs => hnd_l s (NoneDeadOpt.cons_some hs nv (.var v)))
            hG_l hdk_l hwk_l hwkd_l hwf_l ?_ hwX ?_
          · simpa [hdrSrcBranch, tyDecEq_self_isTrue t] using hbr
          · rw [vals_tupAppend, vals_tupSelectArgs]
            simpa [hdrSelect, vals] using
              congrArg (tupAppend (tupSelectVals [t] (xMs.headD []) (v, ()))) hrest_eq
    | let_ _ _ | store _ _ _ | call _ _ _ | jnz _ _ _ | jump _ _ | ret _
    | exit _ _ | hlt | group _ _ =>
      cases hwk <;> (dsimp only [validateHdr] at hval; cases hval)

private theorem hdrPeel_wf_src {rs : List Ty} {tail : List Ty} (dir wantCont : Bool) :
    (hdr : HdrPlan) → (ms : List (List Bool)) → {nv : Nat} → {s_dead : Trie Unit} →
    {Gk : Ctx K (OptArg Val)} → {Gk_diag : Ctx K K} →
    {Dk : Ctx BoolL (RotL Val Cont rs)} → {Dk_diag : Ctx BoolL BoolL} →
    {G : Ctx (OptArg Val) Val} → {D : Ctx (RotL Val Cont rs) Cont} →
    {ek : Expr K BoolL rs} →
    {e_peel : Expr (OptArg Val) (RotL Val Cont rs) rs} →
    {e_src arm_src : Expr Val Cont rs} →
    {sh : Trie Unit} → {armTk armEk : Expr K BoolL rs} → {nv' : Nat} →
    validateHdr hdr ek nv = some (sh, armTk, armEk, nv') →
    checkDeadStepMasks nv s_dead hdr ms = true →
    Wf Gk Dk ek e_peel → Wf Gk_diag Dk_diag ek ek → Wf G D e_peel e_src →
    NoneDeadOpt s_dead Gk → SomeValEq G → DiagK Gk_diag →
    (hv : HdrVals hdr) → (tl : Tup Val tail) →
    hdrSrcBranch dir wantCont hdr hv e_src = some arm_src →
    ∃ (Gk_out : Ctx K (OptArg Val)) (Gk_diag_out : Ctx K K) (G_out : Ctx (OptArg Val) Val),
      NoneDeadOpt s_dead Gk_out ∧ SomeValEq G_out ∧ DiagK Gk_diag_out ∧
      Wf Gk_out Dk (if wantCont == dir then armTk else armEk)
        (hdrPeel dir wantCont hdr ms (hdrSelect hdr ms hv tl) e_peel) ∧
      Wf Gk_diag_out Dk_diag (if wantCont == dir then armTk else armEk)
        (if wantCont == dir then armTk else armEk) ∧
      Wf G_out D (hdrPeel dir wantCont hdr ms (hdrSelect hdr ms hv tl) e_peel) arm_src
  | [], ms, nv, s_dead, Gk, Gk_diag, Dk, Dk_diag, G, D, ek, e_peel, e_src, arm_src,
      sh, armTk, armEk, nv', hval, _, hwk, hwk_diag, hwf, hnd, hG, hdiag, (), tl, hbr => by
    cases hwf with
    | jnz _ ht he =>
      rcases hwk.rhs_jnz with ⟨_, tk, ek', rfl, _, htk, hek⟩
      rcases hwk_diag.jnz_inv with ⟨_, htkd, hekd⟩
      dsimp only [validateHdr] at hval; simp only [pure, Option.some.injEq, Prod.mk.injEq] at hval
      rcases hval with ⟨rfl, rfl, rfl, rfl⟩
      simp only [hdrSrcBranch, Option.some.injEq] at hbr
      subst hbr
      refine ⟨Gk, Gk_diag, G, hnd, hG, hdiag, ?_⟩
      cases hwd : wantCont == dir
      · dsimp only [hdrPeel]
        simp only [hwd, Bool.false_eq_true, ↓reduceIte, hek, hekd, he, and_self]
      · dsimp only [hdrPeel]; simp only [hwd, ↓reduceIte, htk, htkd, ht, and_self]
    | let_ _ _ | load _ _ _ | store _ _ _ | call _ _ _ | jump _ _ | ret _
    | exit _ _ | hlt | group _ _ =>
      cases hwk <;> (dsimp only [validateHdr] at hval; cases hval)
  | .let_ dts :: ss, ms, nv, s_dead, Gk, Gk_diag, Dk, Dk_diag, G, D, ek, e_peel, e_src, arm_src,
      sh, armTk, armEk, nv', hval, hchk, hwk, hwk_diag, hwf, hnd, hG, hdiag,
      (ys, rest_hv), tl, hbr => by
    cases hwf with
    | @let_ _ _ dts' _ _ k₁ k₂ _ hk =>
      rcases hwk.rhs_let with ⟨_, kk, rfl, _, hkk⟩
      rcases hwk_diag.let_inv with ⟨_, hkkd⟩
      dsimp only [validateHdr] at hval
      cases hdec : tysDecEq dts dts' with
      | isFalse => simp [hdec] at hval
      | isTrue heq =>
        subst heq
        simp only [tysDecEq_self_isTrue dts] at hval
        rcases Option.bind_eq_some_iff.1 hval with ⟨⟨s', t', e', n'⟩, hv', heq⟩
        cases heq
        dsimp only [checkDeadStepMasks] at hchk; simp only [Bool.and_eq_true] at hchk
        dsimp only [hdrSelect, hdrPeel, hdrSrcBranch] at hbr ⊢
        simp only [tysDecEq_self_isTrue dts, tupSplit_tupAppend] at hbr ⊢
        let stepLive := tupSelectVals dts (ms.headD []) ys
        let ysOpt := tupWiden dts (ms.headD []) stepLive
        exact hdrPeel_wf_src dir wantCont ss ms.tail hv' hchk.2
          (hkk (Tup.levels dts nv) ysOpt) (hkkd (Tup.levels dts nv) (Tup.levels dts nv))
          (hk ysOpt ys)
          (checkDeadMask_noneDeadOpt dts (ms.headD []) hchk.1 stepLive hnd)
          (SomeValEq.append_tupWiden_tupSelectVals hG dts (ms.headD []) rfl)
          (DiagK.append_zip_eq hdiag (Tup.levels dts nv))
          rest_hv tl hbr
    | load _ _ _ | store _ _ _ | call _ _ _ | jnz _ _ _ | jump _ _ | ret _
    | exit _ _ | hlt | group _ _ =>
      cases hwk <;> (dsimp only [validateHdr] at hval; cases hval)
  | .load t :: ss, ms, nv, s_dead, Gk, Gk_diag, Dk, Dk_diag, G, D, ek, e_peel, e_src, arm_src,
      sh, armTk, armEk, nv', hval, hchk, hwk, hwk_diag, hwf, hnd, hG, hdiag,
      ((v, ()), rest_hv), tl, hbr => by
    cases hwf with
    | @load _ _ t' _ _ k₁ k₂ _ hk =>
      rcases hwk.rhs_load with ⟨_, kk, rfl, _, hkk⟩
      rcases hwk_diag.load_inv with ⟨_, hkkd⟩
      dsimp only [validateHdr] at hval
      cases hdec : tyDecEq t t' with
      | isFalse => simp [hdec] at hval
      | isTrue heq =>
        subst heq
        simp only [tyDecEq_self_isTrue t] at hval
        rcases Option.bind_eq_some_iff.1 hval with ⟨⟨s', t', e', n'⟩, hv', heq⟩
        cases heq
        dsimp only [checkDeadStepMasks] at hchk; simp only [Bool.and_eq_true] at hchk
        dsimp only [hdrSelect, hdrPeel, hdrSrcBranch] at hbr ⊢
        simp only [tyDecEq_self_isTrue t, tupSplit_tupAppend] at hbr ⊢
        let stepLive := tupSelectVals [t] (ms.headD []) (v, ())
        let y1 := (tupWiden [t] (ms.headD []) stepLive).1
        have hnd_next : NoneDeadOpt s_dead (⟨t, nv, y1⟩ :: Gk) := by
          intro _ _ _ hm ho
          exact checkDeadMask_noneDeadOpt [t] (ms.headD []) hchk.1 stepLive hnd hm ho
        have hG_next : SomeValEq (⟨t, y1, v⟩ :: G) := by
          intro _ _ _ hm
          exact SomeValEq.append_tupWiden_tupSelectVals hG [t] (ms.headD []) (ys := (v, ())) rfl hm
        exact hdrPeel_wf_src dir wantCont ss ms.tail hv' hchk.2
          (hkk nv y1) (hkkd nv nv) (hk y1 v)
          hnd_next hG_next (DiagK.cons_eq hdiag nv) rest_hv tl hbr
    | let_ _ _ | store _ _ _ | call _ _ _ | jnz _ _ _ | jump _ _ | ret _
    | exit _ _ | hlt | group _ _ =>
      cases hwk <;> (dsimp only [validateHdr] at hval; cases hval)

mutual
/-- `rewriteRot` refines weakest-precondition semantics whenever `validateRotPlan` accepts. -/
private theorem rewriteRot_wp : (plan : RotPlan) →
    ∀ {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
      {Gk : Ctx K (OptArg Val)} {Gk_diag : Ctx K K}
      {Dk : Ctx BoolL (RotL Val Cont rs)} {Dk_diag : Ctx BoolL BoolL}
      {G : Ctx (OptArg Val) Val} {D : Ctx (RotL Val Cont rs) Cont}
      {ek : Expr K BoolL rs} {e₁ : Expr (OptArg Val) (RotL Val Cont rs) rs}
      {e₂ : Expr Val Cont rs} {nv : Nat} {s : Trie Unit},
      Wf Gk Dk ek e₁ → Wf Gk_diag Dk_diag ek ek → Wf G D e₁ e₂ →
      validateRotPlan plan ek nv = some s →
      NoneDeadOpt s Gk → SomeValEq G → DiagK Gk_diag →
      ValidDk Dk → RotWpD Γ Q X D →
      ∀ m, wp Γ Q X e₂ m → wp Γ Q X (rewriteRot plan e₁) m
  | .leaf => fun hwk _ hwf hval hnd hG _ hDk hD m hw2 => by
    dsimp only [rewriteRot]
    exact flatExpr_wp hwf hwk hval hnd hG hDk hD m hw2
  | .letP p => fun hwk hwk_diag hwf hval hnd hG hdiag hDk hD m hw2 => by
    cases hwf with
    | @let_ _ _ ts op₁ op₂ k₁ k₂ hop hk =>
      rcases hwk.rhs_let with ⟨opk, kk, rfl, hopk, hkk⟩
      rcases hwk_diag.let_inv with ⟨_, hkkd⟩
      dsimp only [validateRotPlan] at hval
      rcases Option.bind_eq_some_iff.1 hval with ⟨sk, hvk, hret⟩
      cases hret
      cases hop with | mk code hargs =>
      cases hopk with | mk _ hargsk =>
      dsimp only [rewriteRot]; simp only [flatOptOp, wp, Op.wp] at hw2 ⊢
      rw [flatOptArgs_vals_of_inSet hnd hG hargsk hargs (ArgsInSet.addArgKeys _ _)]
      refine OpCode.wp_mono code _ (fun r hr => ?_) hw2
      exact rewriteRot_wp p (hkk (Tup.levels ts _) (someVarsToOpt r))
        (hkkd (Tup.levels ts _) (Tup.levels ts _)) (hk (someVarsToOpt r) r) hvk
        (NoneDeadOpt.append_someVars (NoneDeadOpt.sub (TrieSub.addArgsSet _ _) hnd) _ _)
        (SomeValEq.append_someVars hG r)
        (DiagK.append_zip_eq hdiag _) hDk hD m hr
    | load _ _ _ | store _ _ _ | call _ _ _ | jnz _ _ _ | jump _ _ | ret _
    | exit _ _ | hlt | group _ _ =>
      cases hwk <;> (dsimp only [validateRotPlan] at hval; cases hval)
  | .loadP p => fun hwk hwk_diag hwf hval hnd hG hdiag hDk hD m hw2 => by
    cases hwf with
    | load t ha hk =>
      rcases hwk.rhs_load with ⟨ak, kk, rfl, hak, hkk⟩
      rcases hwk_diag.load_inv with ⟨_, hkkd⟩
      dsimp only [validateRotPlan] at hval
      rcases Option.bind_eq_some_iff.1 hval with ⟨sk, hvk, hret⟩
      cases hret
      rcases hw2 with ⟨v, hv_ld, hw2⟩
      dsimp only [rewriteRot]; simp only [wp]
      rw [flatOptArg_val_of_inSet hnd hG hak ha (Arg.InSet.addArgKey _ _)]
      exact ⟨v, hv_ld, rewriteRot_wp p (hkk _ (some (.var v))) (hkkd _ _)
        (hk (some (.var v)) v) hvk
        (NoneDeadOpt.cons_some (NoneDeadOpt.sub (TrieSub.addArgKey _ _) hnd) _ (.var v))
        (SomeValEq.cons_some hG (v := v) rfl) (DiagK.cons_eq hdiag _) hDk hD m hw2⟩
    | let_ _ _ | store _ _ _ | call _ _ _ | jnz _ _ _ | jump _ _ | ret _
    | exit _ _ | hlt | group _ _ =>
      cases hwk <;> (dsimp only [validateRotPlan] at hval; cases hval)
  | .storeP p => fun hwk hwk_diag hwf hval hnd hG hdiag hDk hD m hw2 => by
    cases hwf with
    | store hv ha hk =>
      rcases hwk.rhs_store with ⟨vk, ak, kk, rfl, hvk, hak, hkk⟩
      rcases hwk_diag.store_inv with ⟨_, _, hkkd⟩
      dsimp only [validateRotPlan] at hval
      rcases Option.bind_eq_some_iff.1 hval with ⟨sk, hvk', hret⟩
      cases hret
      rcases hw2 with ⟨hok, hw2⟩
      dsimp only [rewriteRot]; simp only [wp]
      have hv_in : Arg.InSet (addArgKey vk (addArgKey ak sk)) vk := Arg.InSet.addArgKey _ _
      have ha_in : Arg.InSet (addArgKey vk (addArgKey ak sk)) ak :=
        (Arg.InSet.addArgKey _ _).mono (TrieSub.addArgKey _ _)
      rw [flatOptArg_val_of_inSet hnd hG hvk hv hv_in,
        flatOptArg_val_of_inSet hnd hG hak ha ha_in]
      have hsub : TrieSub sk (addArgKey vk (addArgKey ak sk)) :=
        (TrieSub.addArgKey ak sk).trans (TrieSub.addArgKey vk _)
      exact ⟨hok, rewriteRot_wp p hkk hkkd hk hvk' (NoneDeadOpt.sub hsub hnd)
        hG hdiag hDk hD _ hw2⟩
    | let_ _ _ | load _ _ _ | call _ _ _ | jnz _ _ _ | jump _ _ | ret _
    | exit _ _ | hlt | group _ _ =>
      cases hwk <;> (dsimp only [validateRotPlan] at hval; cases hval)
  | .callP p => fun hwk hwk_diag hwf hval hnd hG hdiag hDk hD m hw2 => by
    cases hwf with
    | @call _ _ f as bs args₁ args₂ k₁ k₂ hargs hk =>
      rcases hwk.rhs_call with ⟨argsk, kk, rfl, hargsk, hkk⟩
      rcases hwk_diag.call_inv with ⟨_, hkkd⟩
      dsimp only [validateRotPlan] at hval
      rcases Option.bind_eq_some_iff.1 hval with ⟨sk, hvk, hret⟩
      cases hret
      rcases hw2 with ⟨P, E, hΓ, hP, hE⟩
      dsimp only [rewriteRot]; simp only [wp]
      rw [flatOptArgs_vals_of_inSet hnd hG hargsk hargs (ArgsInSet.addArgKeys _ _)]
      have hsub := TrieSub.addArgsSet argsk sk
      exact ⟨P, E, hΓ, fun r m' hp =>
        rewriteRot_wp p (hkk (Tup.levels bs _) (someVarsToOpt r))
          (hkkd (Tup.levels bs _) (Tup.levels bs _)) (hk (someVarsToOpt r) r) hvk
          (NoneDeadOpt.append_someVars (NoneDeadOpt.sub hsub hnd) _ _)
          (SomeValEq.append_someVars hG r) (DiagK.append_zip_eq hdiag _)
          hDk hD m' (hP r m' hp), hE⟩
    | let_ _ _ | load _ _ _ | store _ _ _ | jnz _ _ _ | jump _ _ | ret _
    | exit _ _ | hlt | group _ _ =>
      cases hwk <;> (dsimp only [validateRotPlan] at hval; cases hval)
  | .jnzP tp ep => fun hwk hwk_diag hwf hval hnd hG hdiag hDk hD m hw2 => by
    cases hwf with
    | jnz hc ht he =>
      rcases hwk.rhs_jnz with ⟨ck, tk, ek', rfl, hck, htk, hek⟩
      rcases hwk_diag.jnz_inv with ⟨_, htkd, hekd⟩
      dsimp only [validateRotPlan] at hval
      rcases Option.bind_eq_some_iff.1 hval with ⟨st, hvt, hrest⟩
      rcases Option.bind_eq_some_iff.1 hrest with ⟨se, hve, hret⟩
      cases hret
      dsimp only [rewriteRot]; simp only [wp] at hw2 ⊢
      rw [flatOptArg_val_of_inSet hnd hG hck hc (Arg.InSet.addArgKey _ _)]
      have hsubT : TrieSub st (addArgKey ck (trieUnion st se)) :=
        (TrieSub.union_left st se).trans (TrieSub.addArgKey ck _)
      have hsubE : TrieSub se (addArgKey ck (trieUnion st se)) :=
        (TrieSub.union_right st se).trans (TrieSub.addArgKey ck _)
      exact ⟨fun h => rewriteRot_wp tp htk htkd ht hvt (NoneDeadOpt.sub hsubT hnd)
          hG hdiag hDk hD m (hw2.1 h),
        fun h => rewriteRot_wp ep hek hekd he hve (NoneDeadOpt.sub hsubE hnd)
          hG hdiag hDk hD m (hw2.2 h)⟩
    | let_ _ _ | load _ _ _ | store _ _ _ | call _ _ _ | jump _ _ | ret _
    | exit _ _ | hlt | group _ _ =>
      cases hwk <;> (dsimp only [validateRotPlan] at hval; cases hval)
  | .groupKeep bsP kP => fun hwk hwk_diag hwf hval hnd hG hdiag hDk hD m hw2 => by
    cases hwf with
    | @group _ _ sig b₁ b₂ k₁ k₂ hb hk =>
      rcases hwk.rhs_group with ⟨bk, kk, rfl, hbk, hkk⟩
      rcases hwk_diag.group_inv with ⟨hbkd, hkkd⟩
      dsimp only [validateRotPlan] at hval
      rcases Option.bind_eq_some_iff.1 hval with ⟨sb, hvb, hrest⟩
      rcases Option.bind_eq_some_iff.1 hrest with ⟨sk, hvk, hret⟩
      cases hret
      dsimp only [rewriteRot]; simp only [wp]
      intro Js_out hcl_out
      have hDk' := ValidDk.append (validDk_wrapKeepLabels Js_out) hDk
      have hD' := RotWpD.append (rotWpD_wrapKeepLabels _ _ _ Js_out) hD
      have hcl₂ := rewriteKeepB_wp bsP
        (hbk (trueLabels sig) (wrapKeepLabels Js_out))
        (hbkd (trueLabels sig) (trueLabels sig))
        (hb (wrapKeepLabels Js_out) Js_out)
        hvb (NoneDeadOpt.sub (TrieSub.union_left sb sk) hnd) hG hdiag hDk' hD' hcl_out
      exact rewriteRot_wp kP (hkk (trueLabels sig) (wrapKeepLabels Js_out))
        (hkkd (trueLabels sig) (trueLabels sig))
        (hk (wrapKeepLabels Js_out) Js_out) hvk
        (NoneDeadOpt.sub (TrieSub.union_right sb sk) hnd) hG hdiag hDk' hD' m (hw2 Js_out hcl₂)
    | let_ _ _ | load _ _ _ | store _ _ _ | call _ _ _ | jnz _ _ _ | jump _ _ | ret _
    | exit _ _ | hlt =>
      cases hwk <;> (dsimp only [validateRotPlan] at hval; cases hval)
  | .groupRot dir hdr contMasks exitMode contP exitP entryP =>
      fun hwk hwk_diag hwf hval hnd hG hdiag hDk hD m hw2 => by
    suffices ∀ {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
        {Gk : Ctx K (OptArg Val)} {Gk_diag : Ctx K K}
        {Dk : Ctx BoolL (RotL Val Cont rs)} {Dk_diag : Ctx BoolL BoolL}
        {G : Ctx (OptArg Val) Val} {D : Ctx (RotL Val Cont rs) Cont}
        {ek : Expr K BoolL rs} {e₁ : Expr (OptArg Val) (RotL Val Cont rs) rs}
        {e₂ : Expr Val Cont rs} {nv : Nat} {s : Trie Unit},
        Wf Gk Dk ek e₁ → Wf Gk_diag Dk_diag ek ek → Wf G D e₁ e₂ →
        validateRotPlan (.groupRot dir hdr contMasks exitMode contP exitP entryP)
          ek nv = some s →
        NoneDeadOpt s Gk → SomeValEq G → DiagK Gk_diag →
        ValidDk Dk → RotWpD Γ Q X D →
        ∀ m, wp Γ Q X e₂ m →
          wp Γ Q X
            (rewriteRot (.groupRot dir hdr contMasks exitMode contP exitP entryP) e₁) m by
      exact this hwk hwk_diag hwf hval hnd hG hdiag hDk hD m hw2
    intro Γ rs Q X Gk Gk_diag Dk Dk_diag G D ek e₁ e₂ nv s
      hwk hwk_diag hwf hval hnd hG hdiag hDk hD m hw2
    cases hwf with
    | @group _ _ sig b₁ b₂ k₁ k₂ hb hk =>
      cases sig with
      | nil => cases hwk <;> (dsimp only [validateRotPlan] at hval; cases hval)
      | cons ts sig' =>
        cases sig' with
        | cons _ _ => cases hwk <;> (dsimp only [validateRotPlan] at hval; cases hval)
        | nil =>
          rcases hwk.rhs_group with ⟨bk, kk, rfl, hbk, hkk⟩
          rcases hwk_diag.group_inv with ⟨hbkd, hkkd⟩
          dsimp only [validateRotPlan] at hval
          rcases Option.bind_eq_some_iff.1 hval with ⟨⟨sh, armT, armE, n1⟩, hvT, hval⟩
          rcases Option.bind_eq_some_iff.1 hval with ⟨⟨shF, armTF, armEF, n2⟩, hvF, hval⟩
          rcases Option.bind_eq_some_iff.1 hval with ⟨sc, hvC, hval⟩
          rcases Option.bind_eq_some_iff.1 hval with ⟨sx, hvX, hval⟩
          rcases Option.bind_eq_some_iff.1 hval with ⟨se, hvE, hval⟩
          cases hchkC : checkDeadStepMasks (nv + ts.length) sc hdr contMasks with
          | false => simp [hchkC] at hval
          | true =>
            simp only [hchkC, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hval
            let xsLvls := Tup.levels ts nv
            have hdiagHdr := validateHdr_diag_eq hdr
              (DiagK.append_zip_eq hdiag xsLvls)
              ((hbkd (true, ()) (false, ())).get .here xsLvls xsLvls)
              hvT hvF
            have hsh_eq : sh = shF := hdiagHdr.1
            have hDiagT := (hbkd (true, ()) (true, ())).get .here xsLvls xsLvls
            have hDiagF := (hbkd (false, ()) (false, ())).get .here xsLvls xsLvls
            cases exitMode with
            | inline =>
              simp only [pure, Option.some.injEq] at hval
              subst hval
              have hnd_shF : NoneDeadOpt shF Gk := by
                rw [← hsh_eq]
                exact NoneDeadOpt.sub (TrieSub.union_left _ _) hnd
              have hnd_sc : NoneDeadOpt sc Gk :=
                NoneDeadOpt.sub ((TrieSub.union_left _ _).trans (TrieSub.union_right _ _)) hnd
              have hnd_sx : NoneDeadOpt sx Gk :=
                NoneDeadOpt.sub
                  (((TrieSub.union_left _ _).trans (TrieSub.union_right _ _)).trans
                    (TrieSub.union_right _ _)) hnd
              have hnd_se : NoneDeadOpt se Gk :=
                NoneDeadOpt.sub
                  (((TrieSub.union_right _ _).trans (TrieSub.union_right _ _)).trans
                    (TrieSub.union_right _ _)) hnd
              dsimp only [rewriteRot]; simp only [wp]
              intro (J_rot, ()) hcl_rot
              simp only [Closed, and_true] at hcl_rot
              let mk : Tup (Arg Val) ts → Expr Val Cont _ := fun args =>
                hdrEmit (tailC := ts) (tailX := ts) dir args args hdr contMasks []
                  ((b₁ (exitLabels ts)).get .here (someArgsToOpt args))
                  (fun rotArgs => .jump J_rot rotArgs)
                  (fun exitExpr _ => rewriteRot exitP exitExpr)
              let J_src : Cont ts := fun vs m₀ =>
                ∀ (args : Tup (Arg Val) ts), vals args = vs → wp Γ Q X (mk args) m₀
              have hDkT : ValidDk (Tup.zip (as := [ts]) (true, ()) (RotL.expand mk, ()) ++ Dk) := by
                intro p hp htrue
                cases hp with
                | head => rfl
                | tail _ hp' => exact hDk p hp' htrue
              have hDT : RotWpD Γ Q X
                  (Tup.zip (as := [ts]) (RotL.expand mk, ()) (J_src, ()) ++ D) := by
                intro p hp
                cases hp with
                | head => exact fun args m' hj => hj args rfl
                | tail _ hp' => exact hD p hp'
              have hcl_src : Closed Γ Q X (b₂ (J_src, ())) (J_src, ()) := by
                rw [closed_iff]
                intro _ i xs m₀ hw
                cases i with
                | there i => exact nomatch i
                | here =>
                  intro args hargs
                  refine hdrEmit_wp dir hdr contMasks [] hvF
                    ((hbk (false, ()) (exitLabels ts)).get .here xsLvls (someArgsToOpt args))
                    hDiagF
                    ((hb (exitLabels ts) (J_src, ())).get .here (someArgsToOpt args) xs)
                    (NoneDeadOpt.append_some hnd_shF xsLvls args)
                    (SomeValEq.append_someArgs hG hargs)
                    (DiagK.append_zip_eq hdiag xsLvls) hargs hargs hw ?_ ?_
                  · intro hv m' armC_src rotArgs hbr hwC hrot_eq
                    apply hcl_rot (vals rotArgs) m'
                    have hxs_split : splitTail hdr contMasks (vals rotArgs) = xs := by
                      rw [hrot_eq, splitTail_hdrSelect]
                    rw [hxs_split, hrot_eq]
                    obtain ⟨Gk_o, Gkd_o, G_o, hnd_o, hG_o, hdiag_o, hwk_o, hwkd_o, hwf_o⟩ :=
                      hdrPeel_wf_src dir true hdr contMasks hvT hchkC
                        ((hbk (true, ()) (.expand mk, ())).get .here xsLvls (someVarsToOpt xs))
                        hDiagT
                        ((hb (.expand mk, ()) (J_src, ())).get .here (someVarsToOpt xs) xs)
                        (NoneDeadOpt.append_someVars hnd_sc xsLvls xs)
                        (SomeValEq.append_someVars hG xs)
                        (DiagK.append_zip_eq hdiag xsLvls) hv xs hbr
                    have harm_eq : (if true == dir then armT else armE) =
                        (if dir then armT else armE) := by cases dir <;> rfl
                    rw [harm_eq] at hwk_o hwkd_o
                    exact rewriteRot_wp contP hwk_o hwkd_o hwf_o hvC hnd_o hG_o hdiag_o
                      hDkT hDT m' hwC
                  · intro hv m' Gk_l Gkd_l G_l armX_em armX_s _ hnd_l hG_l hdiag_l
                      hwk_l hwkd_l hwf_l _ hwX _
                    exact rewriteRot_wp exitP hwk_l hwkd_l hwf_l hvX
                      (hnd_l sx (NoneDeadOpt.append_some hnd_sx xsLvls args)) hG_l
                      hdiag_l (ValidDk.append (validDk_exitLabels ts) hDk)
                      (RotWpD.append (rotWpD_exitLabels _ _ _ ts (J_src, ())) hD) m' hwX
              exact rewriteRot_wp entryP (hkk (true, ()) (.expand mk, ()))
                (hkkd (true, ()) (true, ())) (hk (.expand mk, ()) (J_src, ())) hvE
                hnd_se hG hdiag hDkT hDT m (hw2 (J_src, ()) hcl_src)
            | wrap xsMask hMasks =>
              cases hchkX : checkDeadMask nv sx ts xsMask &&
                  checkDeadStepMasks (nv + ts.length) sx hdr hMasks with
              | false => simp [hchkX] at hval
              | true =>
                simp only [hchkX, ↓reduceIte, pure, Option.some.injEq] at hval
                subst hval
                simp only [Bool.and_eq_true] at hchkX
                have hnd_shF : NoneDeadOpt shF Gk := by
                  rw [← hsh_eq]
                  exact NoneDeadOpt.sub (TrieSub.union_left _ _) hnd
                have hnd_sc : NoneDeadOpt sc Gk :=
                  NoneDeadOpt.sub ((TrieSub.union_left _ _).trans (TrieSub.union_right _ _)) hnd
                have hnd_sx : NoneDeadOpt sx Gk :=
                  NoneDeadOpt.sub
                    (((TrieSub.union_left _ _).trans (TrieSub.union_right _ _)).trans
                      (TrieSub.union_right _ _)) hnd
                have hnd_se : NoneDeadOpt se Gk :=
                  NoneDeadOpt.sub
                    (((TrieSub.union_right _ _).trans (TrieSub.union_right _ _)).trans
                      (TrieSub.union_right _ _)) hnd
                dsimp only [rewriteRot]; simp only [wp]
                intro (J_exit, ()) hcl_exit (J_rot, ()) hcl_rot
                simp only [Closed, and_true] at hcl_exit hcl_rot
                let mk : Tup (Arg Val) ts → Expr Val Cont _ := fun args =>
                  hdrEmit (tailC := ts) (tailX := filterTys ts xsMask)
                    dir args (tupSelectArgs ts xsMask args) hdr contMasks hMasks
                    ((b₁ (exitLabels ts)).get .here (someArgsToOpt args))
                    (fun rotArgs => .jump J_rot rotArgs)
                    (fun _ exitArgs => .jump J_exit exitArgs)
                let J_src : Cont ts := fun vs m₀ =>
                  ∀ (args : Tup (Arg Val) ts), vals args = vs → wp Γ Q X (mk args) m₀
                have hDkT : ValidDk
                    (Tup.zip (as := [ts]) (true, ()) (RotL.expand mk, ()) ++ Dk) := by
                  intro p hp htrue
                  cases hp with
                  | head => rfl
                  | tail _ hp' => exact hDk p hp' htrue
                have hDT : RotWpD Γ Q X
                    (Tup.zip (as := [ts]) (RotL.expand mk, ()) (J_src, ()) ++ D) := by
                  intro p hp
                  cases hp with
                  | head => exact fun args m' hj => hj args rfl
                  | tail _ hp' => exact hD p hp'
                have hcl_src : Closed Γ Q X (b₂ (J_src, ())) (J_src, ()) := by
                  rw [closed_iff]
                  intro _ i xs m₀ hw
                  cases i with
                  | there i => exact nomatch i
                  | here =>
                    intro args hargs
                    refine hdrEmit_wp dir hdr contMasks hMasks hvF
                      ((hbk (false, ()) (exitLabels ts)).get .here xsLvls (someArgsToOpt args))
                      hDiagF
                      ((hb (exitLabels ts) (J_src, ())).get .here (someArgsToOpt args) xs)
                      (NoneDeadOpt.append_some hnd_shF xsLvls args)
                      (SomeValEq.append_someArgs hG hargs)
                      (DiagK.append_zip_eq hdiag xsLvls) hargs (vals_tupSelectArgs xsMask args)
                      hw ?_ ?_
                    · intro hv m' armC_src rotArgs hbr hwC hrot_eq
                      apply hcl_rot (vals rotArgs) m'
                      have hxs_split : splitTail hdr contMasks (vals rotArgs) = xs := by
                        rw [hrot_eq, splitTail_hdrSelect]
                      rw [hxs_split, hrot_eq]
                      obtain ⟨Gk_o, Gkd_o, G_o, hnd_o, hG_o, hdiag_o, hwk_o, hwkd_o, hwf_o⟩ :=
                        hdrPeel_wf_src dir true hdr contMasks hvT hchkC
                          ((hbk (true, ()) (.expand mk, ())).get .here xsLvls (someVarsToOpt xs))
                          hDiagT
                          ((hb (.expand mk, ()) (J_src, ())).get .here (someVarsToOpt xs) xs)
                          (NoneDeadOpt.append_someVars hnd_sc xsLvls xs)
                          (SomeValEq.append_someVars hG xs)
                          (DiagK.append_zip_eq hdiag xsLvls) hv xs hbr
                      have harm_eq : (if true == dir then armT else armE) =
                          (if dir then armT else armE) := by cases dir <;> rfl
                      rw [harm_eq] at hwk_o hwkd_o
                      exact rewriteRot_wp contP hwk_o hwkd_o hwf_o hvC hnd_o hG_o hdiag_o
                        hDkT hDT m' hwC
                    · intro hv m' _ _ _ _ armX_s exitArgs _ _ _ _ _ _ hbr hwX hexit_eq
                      apply hcl_exit (vals exitArgs) m'
                      have hexit_eq' : vals exitArgs =
                          hdrSelect hdr hMasks hv (tupSelectVals ts xsMask xs) := by
                        rw [hexit_eq, hargs]
                      have hxt_split : splitTail hdr hMasks (vals exitArgs) =
                          tupSelectVals ts xsMask xs := by
                        rw [hexit_eq', splitTail_hdrSelect]
                      rw [hxt_split, hexit_eq']
                      let xsOpt := tupWiden ts xsMask (tupSelectVals ts xsMask xs)
                      obtain ⟨Gk_o, Gkd_o, G_o, hnd_o, hG_o, hdiag_o, hwk_o, hwkd_o, hwf_o⟩ :=
                        hdrPeel_wf_src dir false hdr hMasks hvF hchkX.2
                          ((hbk (false, ()) (exitLabels ts)).get .here xsLvls xsOpt)
                          hDiagF
                          ((hb (exitLabels ts) (J_src, ())).get .here xsOpt xs)
                          (checkDeadMask_noneDeadOpt ts xsMask hchkX.1 _ hnd_sx)
                          (SomeValEq.append_tupWiden_tupSelectVals hG ts xsMask rfl)
                          (DiagK.append_zip_eq hdiag xsLvls)
                          hv (tupSelectVals ts xsMask xs) hbr
                      have harm_eq : (if false == dir then armTF else armEF) =
                          (if dir then armEF else armTF) := by cases dir <;> rfl
                      rw [harm_eq] at hwk_o hwkd_o
                      exact rewriteRot_wp exitP hwk_o hwkd_o hwf_o hvX hnd_o hG_o hdiag_o
                        (ValidDk.append (validDk_exitLabels ts) hDk)
                        (RotWpD.append (rotWpD_exitLabels _ _ _ ts (J_src, ())) hD) m' hwX
                exact rewriteRot_wp entryP (hkk (true, ()) (.expand mk, ()))
                  (hkkd (true, ()) (true, ())) (hk (.expand mk, ()) (J_src, ())) hvE
                  hnd_se hG hdiag hDkT hDT m (hw2 (J_src, ()) hcl_src)
    | let_ _ _ | load _ _ _ | store _ _ _ | call _ _ _ | jnz _ _ _ | jump _ _ | ret _
    | exit _ _ | hlt =>
      cases hwk <;> (dsimp only [validateRotPlan] at hval; cases hval)
where
  rewriteKeepB_wp : (ps : List RotPlan) →
      ∀ {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
        {Gk : Ctx K (OptArg Val)} {Gk_diag : Ctx K K}
        {Dk : Ctx BoolL (RotL Val Cont rs)} {Dk_diag : Ctx BoolL BoolL}
        {G : Ctx (OptArg Val) Val} {D : Ctx (RotL Val Cont rs) Cont}
        {sig : List (List Ty)}
        {bsk : Blocks K BoolL rs sig}
        {bs₁ : Blocks (OptArg Val) (RotL Val Cont rs) rs sig}
        {bs₂ : Blocks Val Cont rs sig}
        {Js : Tup Cont sig} {nv : Nat} {sb : Trie Unit},
        WfB Gk Dk bsk bs₁ → WfB Gk_diag Dk_diag bsk bsk → WfB G D bs₁ bs₂ →
        validateRotPlan.validateKeepB ps bsk nv = some sb →
        NoneDeadOpt sb Gk → SomeValEq G → DiagK Gk_diag →
        ValidDk Dk → RotWpD Γ Q X D →
        Closed Γ Q X (rewriteRot.rewriteKeepB ps bs₁) Js →
        Closed Γ Q X bs₂ Js
    | [] => fun hbk _ hb hval _ _ _ _ _ _ => by
      cases hbk with
      | nil => cases hb; trivial
      | cons _ _ => dsimp only [validateRotPlan.validateKeepB] at hval; cases hval
    | p :: ps => fun hbk hbkd hb hval hnd hG hdiag hDk hD hcl => by
      cases hbk with
      | nil => dsimp only [validateRotPlan.validateKeepB] at hval; cases hval
      | cons hbk1 hbk_rest =>
        cases hb with | cons hb1 hb_rest =>
        cases hbkd with | cons hbkd1 hbkd_rest =>
        dsimp only [validateRotPlan.validateKeepB] at hval
        rcases Option.bind_eq_some_iff.1 hval with ⟨s₁, hs₁, hrest⟩
        rcases Option.bind_eq_some_iff.1 hrest with ⟨s₂, hs₂, heq⟩
        cases heq
        dsimp only [rewriteRot.rewriteKeepB] at hcl ⊢; simp only [Closed] at hcl ⊢
        refine ⟨fun xs m hw => hcl.1 xs m ?_,
          rewriteKeepB_wp ps hbk_rest hbkd_rest hb_rest hs₂
            (NoneDeadOpt.sub (TrieSub.union_right s₁ s₂) hnd) hG hdiag hDk hD hcl.2⟩
        exact rewriteRot_wp p (hbk1 (Tup.levels _ _) (someVarsToOpt xs))
          (hbkd1 (Tup.levels _ _) (Tup.levels _ _)) (hb1 (someVarsToOpt xs) xs)
          hs₁ (NoneDeadOpt.append_someVars (NoneDeadOpt.sub (TrieSub.union_left s₁ s₂) hnd) _ _)
          (SomeValEq.append_someVars hG xs) (DiagK.append_zip_eq hdiag _) hDk hD m hw
end

/-! ## Well-scopedness (`callsOk`) preservation -/

private abbrev UnitV : Ty → Type := fun _ => Unit
private abbrev UnitL : List Ty → Type := fun _ => Unit

/-- Label invariant asserting every `.expand fn` produces `callsOk` bodies at all args. -/
private def RotCallsL (allowed : List SigEntry) (exits : List Sym) {rs : List Ty}
    (D : Ctx (RotL UnitV UnitL rs) UnitL) : Prop :=
  ∀ p ∈ D, match p.2.1 with
    | .expand fn => ∀ args, (fn args).callsOk allowed exits
    | .keep _ | .dead => True

private theorem RotCallsL.append {allowed : List SigEntry} {exits : List Sym} {rs : List Ty}
    {H D : Ctx (RotL UnitV UnitL rs) UnitL}
    (hH : RotCallsL allowed exits H) (hD : RotCallsL allowed exits D) :
    RotCallsL allowed exits (H ++ D) := fun p hp =>
  (List.mem_append.1 hp).elim (hH p) (hD p)

private theorem rotCallsL_wrapKeepLabels (allowed : List SigEntry) (exits : List Sym)
    {rs : List Ty} :
    {sig : List (List Ty)} → (Js : Tup UnitL sig) →
    RotCallsL allowed exits (Tup.zip (wrapKeepLabels (V := UnitV) (rs := rs) Js) Js)
  | [], (), _, hp => nomatch hp
  | _ :: _, ((), Js), p, hp => by
    cases hp with
    | head => trivial
    | tail _ hp => exact rotCallsL_wrapKeepLabels allowed exits Js p hp

private theorem rotCallsL_exitLabels (allowed : List SigEntry) (exits : List Sym) {rs : List Ty}
    (ts : List Ty) (Js : Tup UnitL [ts]) :
    RotCallsL allowed exits (Tup.zip (exitLabels (V := UnitV) (L := UnitL) (rs := rs) ts) Js) := by
  intro p hp
  cases hp with
  | head => trivial
  | tail _ hp => nomatch hp

private theorem flatBlocks_callsOk {allowed : List SigEntry} {exits : List Sym} {rs : List Ty} :
    {sig : List (List Ty)} →
    (bs₁ : Blocks (OptArg UnitV) (RotL UnitV UnitL rs) rs sig) →
    (bs₂ : Blocks UnitV UnitL rs sig) →
    (∀ {ts} (i : Member ts sig) xs₁ xs₂,
      (bs₂.get i xs₂).callsOk allowed exits →
      (flatExpr (bs₁.get i xs₁)).callsOk allowed exits) →
    bs₂.callsOk allowed exits →
    (flatExpr.flatBlocks bs₁).callsOk allowed exits
  | [], .nil, .nil, _, _ => trivial
  | _ :: _, .cons _ bs₁, .cons _ bs₂, hbi, hbs₂ => by
    dsimp only [flatExpr.flatBlocks]; simp only [Blocks.callsOk]
    dsimp only [Blocks.callsOk] at hbs₂
    exact ⟨hbi .here _ _ hbs₂.1, flatBlocks_callsOk bs₁ bs₂ (fun i => hbi (.there i)) hbs₂.2⟩

private theorem flatExpr_callsOk {allowed : List SigEntry} {exits : List Sym} {rs : List Ty}
    {G : Ctx (OptArg UnitV) UnitV} {D : Ctx (RotL UnitV UnitL rs) UnitL}
    {e₁ : Expr (OptArg UnitV) (RotL UnitV UnitL rs) rs} {e₂ : Expr UnitV UnitL rs}
    (hwf : Wf G D e₁ e₂) :
    RotCallsL allowed exits D → e₂.callsOk allowed exits →
    (flatExpr e₁).callsOk allowed exits := by
  induction hwf using Wf.induct with
  | let_ _ _ ih =>
    intro hD hc
    exact ih (someVarsToOpt (Tup.units _)) (Tup.units _) hD hc
  | load _ _ _ ih =>
    intro hD hc
    exact ih (some (.var ())) () hD hc
  | store _ _ _ ih =>
    intro hD hc
    exact ih hD hc
  | call _ _ _ ih =>
    intro hD ⟨hf, hc⟩
    exact ⟨hf, ih (someVarsToOpt (Tup.units _)) (Tup.units _) hD hc⟩
  | jnz _ _ _ iht ihe =>
    intro hD ⟨ht, he⟩
    exact ⟨iht hD ht, ihe hD he⟩
  | @jump _ _ _ j₁ _ _ _ hj _ =>
    intro hD _
    have hdj := hD _ hj
    dsimp only at hdj
    cases j₁ with
    | keep _ => trivial
    | dead => trivial
    | expand fn => exact hdj _
  | ret _ | exit _ _ | hlt => intro _ hc; exact hc
  | @group _ _ sig b₁ b₂ k₁ k₂ _ _ ihb ihk =>
    intro hD ⟨hb, hk⟩
    have hD' := (rotCallsL_wrapKeepLabels allowed exits (Tup.units sig)).append hD
    exact ⟨flatBlocks_callsOk (b₁ (wrapKeepLabels (Tup.units sig))) (b₂ (Tup.units sig))
        (fun i xs₁ xs₂ => ihb (wrapKeepLabels (Tup.units sig)) (Tup.units sig) i xs₁ xs₂ hD') hb,
      ihk (wrapKeepLabels (Tup.units sig)) (Tup.units sig) hD' hk⟩

private theorem hdrPeel_callsOk {allowed : List SigEntry} {exits : List Sym} {rs tail : List Ty}
    (dir wantCont : Bool) :
    (hdr : HdrPlan) → (ms : List (List Bool)) →
    (params : Tup UnitV (stepMasksSig hdr ms tail)) →
    {G : Ctx (OptArg UnitV) UnitV} → {D : Ctx (RotL UnitV UnitL rs) UnitL} →
    {e₁ : Expr (OptArg UnitV) (RotL UnitV UnitL rs) rs} → {e₂ : Expr UnitV UnitL rs} →
    Wf G D e₁ e₂ → e₂.callsOk allowed exits →
    ∃ G' e₂', Wf G' D (hdrPeel dir wantCont hdr ms params e₁) e₂' ∧ e₂'.callsOk allowed exits
  | [], _, _, G, _, _, _, hwf, hc => by
    cases hwf with
    | jnz _ ht he =>
      cases hwd : wantCont == dir
      · dsimp only [hdrPeel]
        exact ⟨_, _, by simp only [hwd, Bool.false_eq_true, ↓reduceIte]; exact he, hc.2⟩
      · dsimp only [hdrPeel]
        exact ⟨_, _, by simp only [hwd, ↓reduceIte]; exact ht, hc.1⟩
    | let_ _ _ | load _ _ _ | store _ _ _ | call _ _ _ | jump _ _ | ret _
    | exit _ _ | hlt | group _ _ =>
      exact ⟨G, .hlt, .hlt, trivial⟩
  | .let_ dts :: ss, ms, params, G, D, _, _, hwf, hc => by
    cases hwf with
    | @let_ _ _ dts' _ _ k₁ k₂ _ hk =>
      cases hdec : tysDecEq dts dts' with
      | isFalse hne =>
        have hne' : dts ≠ dts' := fun heq => hne heq
        obtain ⟨_, hfeq⟩ := tysDecEq_false_of_ne hne'
        dsimp only [hdrPeel]; simp only [hfeq]; exact ⟨G, .hlt, .hlt, trivial⟩
      | isTrue heq =>
        subst heq
        dsimp only [hdrPeel]; simp only [tysDecEq_self_isTrue dts]
        let (stepLive, rest) := tupSplit (filterTys dts (ms.headD [])) params
        exact hdrPeel_callsOk dir wantCont ss ms.tail rest
          (hk (tupWiden dts (ms.headD []) stepLive) (Tup.units dts)) hc
    | load _ _ _ | store _ _ _ | call _ _ _ | jnz _ _ _ | jump _ _ | ret _
    | exit _ _ | hlt | group _ _ =>
      exact ⟨G, .hlt, .hlt, trivial⟩
  | .load t :: ss, ms, params, G, D, _, _, hwf, hc => by
    cases hwf with
    | @load _ _ t' _ _ k₁ k₂ _ hk =>
      cases hdec : tyDecEq t t' with
      | isFalse hne =>
        have hne' : t ≠ t' := fun heq => hne heq
        obtain ⟨_, hfeq⟩ := tyDecEq_false_of_ne hne'
        dsimp only [hdrPeel]; simp only [hfeq]; exact ⟨G, .hlt, .hlt, trivial⟩
      | isTrue heq =>
        subst heq
        dsimp only [hdrPeel]; simp only [tyDecEq_self_isTrue t]
        let (stepLive, rest) := tupSplit (filterTys [t] (ms.headD [])) params
        exact hdrPeel_callsOk dir wantCont ss ms.tail rest
          (hk (tupWiden [t] (ms.headD []) stepLive).1 ()) hc
    | let_ _ _ | store _ _ _ | call _ _ _ | jnz _ _ _ | jump _ _ | ret _
    | exit _ _ | hlt | group _ _ =>
      exact ⟨G, .hlt, .hlt, trivial⟩

private theorem hdrEmit_callsOk {allowed : List SigEntry} {exits : List Sym}
    {rs tailC tailX : List Ty}
    (dir : Bool) (tc : Tup (Arg UnitV) tailC) (tx : Tup (Arg UnitV) tailX) :
    (hdr : HdrPlan) → (cMs xMs : List (List Bool)) →
    {G : Ctx (OptArg UnitV) UnitV} → {D : Ctx (RotL UnitV UnitL rs) UnitL} →
    {e₁ : Expr (OptArg UnitV) (RotL UnitV UnitL rs) rs} → {e₂ : Expr UnitV UnitL rs} →
    {kC : Tup (Arg UnitV) (stepMasksSig hdr cMs tailC) → Expr UnitV UnitL rs} →
    {kX : Expr (OptArg UnitV) (RotL UnitV UnitL rs) rs →
      Tup (Arg UnitV) (stepMasksSig hdr xMs tailX) → Expr UnitV UnitL rs} →
    Wf G D e₁ e₂ → e₂.callsOk allowed exits →
    (∀ a, (kC a).callsOk allowed exits) →
    (∀ G' ex₁ ex₂, Wf G' D ex₁ ex₂ → ex₂.callsOk allowed exits →
      ∀ a, (kX ex₁ a).callsOk allowed exits) →
    (hdrEmit dir tc tx hdr cMs xMs e₁ kC kX).callsOk allowed exits
  | [], _, _, _, _, _, _, _, _, hwf, hc, hkC, hkX => by
    cases hwf with
    | jnz _ ht he =>
      cases dir <;> dsimp only [hdrEmit]
      · exact ⟨hkX _ _ _ ht hc.1 tx, hkC tc⟩
      · exact ⟨hkC tc, hkX _ _ _ he hc.2 tx⟩
    | let_ _ _ | load _ _ _ | store _ _ _ | call _ _ _ | jump _ _ | ret _
    | exit _ _ | hlt | group _ _ =>
      trivial
  | .let_ dts :: ss, cMs, xMs, G, D, _, _, kC, kX, hwf, hc, hkC, hkX => by
    cases hwf with
    | @let_ _ _ dts' _ _ k₁ k₂ _ hk =>
      cases hdec : tysDecEq dts dts' with
      | isFalse hne =>
        have hne' : dts ≠ dts' := fun heq => hne heq
        obtain ⟨_, hfeq⟩ := tysDecEq_false_of_ne hne'
        dsimp only [hdrEmit]; simp only [hfeq]; trivial
      | isTrue heq =>
        subst heq
        dsimp only [hdrEmit]; simp only [tysDecEq_self_isTrue dts, Expr.callsOk]
        exact hdrEmit_callsOk dir tc tx ss cMs.tail xMs.tail
          (hk (someVarsToOpt (Tup.units dts)) (Tup.units dts)) hc
          (fun rest => hkC _) (fun G' ex₁ ex₂ hex hce rest => hkX G' ex₁ ex₂ hex hce _)
    | load _ _ _ | store _ _ _ | call _ _ _ | jnz _ _ _ | jump _ _ | ret _
    | exit _ _ | hlt | group _ _ =>
      trivial
  | .load t :: ss, cMs, xMs, G, D, _, _, kC, kX, hwf, hc, hkC, hkX => by
    cases hwf with
    | @load _ _ t' _ _ k₁ k₂ _ hk =>
      cases hdec : tyDecEq t t' with
      | isFalse hne =>
        have hne' : t ≠ t' := fun heq => hne heq
        obtain ⟨_, hfeq⟩ := tyDecEq_false_of_ne hne'
        dsimp only [hdrEmit]; simp only [hfeq]; trivial
      | isTrue heq =>
        subst heq
        dsimp only [hdrEmit]; simp only [tyDecEq_self_isTrue t, Expr.callsOk]
        exact hdrEmit_callsOk dir tc tx ss cMs.tail xMs.tail
          (hk (some (.var ())) ()) hc
          (fun rest => hkC _) (fun G' ex₁ ex₂ hex hce rest => hkX G' ex₁ ex₂ hex hce _)
    | let_ _ _ | store _ _ _ | call _ _ _ | jnz _ _ _ | jump _ _ | ret _
    | exit _ _ | hlt | group _ _ =>
      trivial

mutual
/-- `rewriteRot` preserves `Expr.callsOk` unconditionally when `e₁` and `e₂` are `Wf`-related. -/
private theorem rewriteRot_callsOk {allowed : List SigEntry} {exits : List Sym} : (plan : RotPlan) →
    ∀ {rs : List Ty} {G : Ctx (OptArg UnitV) UnitV} {D : Ctx (RotL UnitV UnitL rs) UnitL}
      {e₁ : Expr (OptArg UnitV) (RotL UnitV UnitL rs) rs} {e₂ : Expr UnitV UnitL rs},
      Wf G D e₁ e₂ → RotCallsL allowed exits D → e₂.callsOk allowed exits →
      (rewriteRot plan e₁).callsOk allowed exits
  | .leaf => fun hwf hD hc => by
    dsimp only [rewriteRot]
    exact flatExpr_callsOk hwf hD hc
  | .letP p => fun hwf hD hc => by
    cases hwf with
    | let_ _ hk =>
      dsimp only [rewriteRot]
      exact rewriteRot_callsOk p (hk _ (Tup.units _)) hD hc
    | load _ _ _ | store _ _ _ | call _ _ _ | jnz _ _ _ | jump _ _ | ret _
    | exit _ _ | hlt | group _ _ =>
      dsimp only [rewriteRot]; trivial
  | .loadP p => fun hwf hD hc => by
    cases hwf with
    | load _ _ hk =>
      dsimp only [rewriteRot]
      exact rewriteRot_callsOk p (hk _ ()) hD hc
    | let_ _ _ | store _ _ _ | call _ _ _ | jnz _ _ _ | jump _ _ | ret _
    | exit _ _ | hlt | group _ _ =>
      dsimp only [rewriteRot]; trivial
  | .storeP p => fun hwf hD hc => by
    cases hwf with
    | store _ _ hk =>
      dsimp only [rewriteRot]
      exact rewriteRot_callsOk p hk hD hc
    | let_ _ _ | load _ _ _ | call _ _ _ | jnz _ _ _ | jump _ _ | ret _
    | exit _ _ | hlt | group _ _ =>
      dsimp only [rewriteRot]; trivial
  | .callP p => fun hwf hD hc => by
    cases hwf with
    | call _ _ hk =>
      dsimp only [rewriteRot]
      exact ⟨hc.1, rewriteRot_callsOk p (hk _ (Tup.units _)) hD hc.2⟩
    | let_ _ _ | load _ _ _ | store _ _ _ | jnz _ _ _ | jump _ _ | ret _
    | exit _ _ | hlt | group _ _ =>
      dsimp only [rewriteRot]; trivial
  | .jnzP tp ep => fun hwf hD hc => by
    cases hwf with
    | jnz _ ht he =>
      dsimp only [rewriteRot]
      exact ⟨rewriteRot_callsOk tp ht hD hc.1, rewriteRot_callsOk ep he hD hc.2⟩
    | let_ _ _ | load _ _ _ | store _ _ _ | call _ _ _ | jump _ _ | ret _
    | exit _ _ | hlt | group _ _ =>
      dsimp only [rewriteRot]; trivial
  | .groupKeep bsP kP => fun hwf hD hc => by
    cases hwf with
    | @group _ _ sig b₁ b₂ k₁ k₂ hb hk =>
      dsimp only [rewriteRot]
      have hD' := (rotCallsL_wrapKeepLabels allowed exits (Tup.units sig)).append hD
      exact ⟨rewriteKeepB_callsOk bsP (b₁ (wrapKeepLabels (Tup.units sig)))
          (b₂ (Tup.units sig)) (hb (wrapKeepLabels (Tup.units sig)) (Tup.units sig)) hD' hc.1,
        rewriteRot_callsOk kP (hk (wrapKeepLabels (Tup.units sig)) (Tup.units sig)) hD' hc.2⟩
    | let_ _ _ | load _ _ _ | store _ _ _ | call _ _ _ | jnz _ _ _ | jump _ _ | ret _
    | exit _ _ | hlt =>
      dsimp only [rewriteRot]; trivial
  | .groupRot dir hdr contMasks exitMode contP exitP entryP => fun hwf hD hc => by
    suffices ∀ {rs : List Ty} {G : Ctx (OptArg UnitV) UnitV}
        {D : Ctx (RotL UnitV UnitL rs) UnitL}
        {e₁ : Expr (OptArg UnitV) (RotL UnitV UnitL rs) rs} {e₂ : Expr UnitV UnitL rs},
        Wf G D e₁ e₂ → RotCallsL allowed exits D → e₂.callsOk allowed exits →
        (rewriteRot (.groupRot dir hdr contMasks exitMode contP exitP entryP) e₁).callsOk
          allowed exits by
      exact this hwf hD hc
    intro rs G D e₁ e₂ hwf hD hc
    cases hwf with
    | @group _ _ sig b₁ b₂ k₁ k₂ hb hk =>
      cases sig with
      | nil => dsimp only [rewriteRot]; trivial
      | cons ts sig' =>
        cases sig' with
        | cons _ _ => dsimp only [rewriteRot]; trivial
        | nil =>
          have hbc : ((b₂ ((), ())).get .here (Tup.units ts)).callsOk allowed exits :=
            Blocks.callsOk_get hc.1 .here
          have hDex := (rotCallsL_exitLabels allowed exits ts ((), ())).append hD
          cases exitMode with
          | inline =>
            dsimp only [rewriteRot]
            dsimp only [Expr.callsOk, Blocks.callsOk]
            let mk : Tup (Arg UnitV) ts → Expr UnitV UnitL _ := fun args =>
              hdrEmit (tailC := ts) (tailX := ts) dir args args hdr contMasks []
                ((b₁ (exitLabels ts)).get .here (someArgsToOpt args))
                (fun rotArgs => .jump () rotArgs)
                (fun exitExpr _ => rewriteRot exitP exitExpr)
            have hmk : ∀ args, (mk args).callsOk allowed exits := fun args =>
              hdrEmit_callsOk dir args args hdr contMasks []
                ((hb (exitLabels ts) ((), ())).get .here (someArgsToOpt args) (Tup.units ts))
                hbc (fun _ => trivial)
                (fun _ _ _ hex hcex _ => rewriteRot_callsOk exitP hex hDex hcex)
            have hDc : RotCallsL allowed exits
                (Tup.zip (as := [ts]) (RotL.expand mk, ()) ((), ()) ++ D) := by
              intro p hp
              cases hp with
              | head => exact hmk
              | tail _ hp' => exact hD p hp'
            have hpeel := hdrPeel_callsOk (allowed := allowed) (exits := exits)
              (tail := ts) dir true hdr contMasks (Tup.units (rotSig hdr contMasks ts))
              ((hb (.expand mk, ()) ((), ())).get .here
                (someVarsToOpt (splitTail hdr contMasks
                  (Tup.units (rotSig hdr contMasks ts))))
                (Tup.units ts)) hbc
            rcases hpeel with ⟨_, _, hwf_p, hc_p⟩
            exact ⟨⟨rewriteRot_callsOk contP hwf_p hDc hc_p, trivial⟩,
              rewriteRot_callsOk entryP (hk (.expand mk, ()) ((), ())) hDc hc.2⟩
          | wrap xsMask hMasks =>
            dsimp only [rewriteRot]
            dsimp only [Expr.callsOk, Blocks.callsOk]
            let mk : Tup (Arg UnitV) ts → Expr UnitV UnitL _ := fun args =>
              hdrEmit (tailC := ts) (tailX := filterTys ts xsMask)
                dir args (tupSelectArgs ts xsMask args) hdr contMasks hMasks
                ((b₁ (exitLabels ts)).get .here (someArgsToOpt args))
                (fun rotArgs => .jump () rotArgs)
                (fun _ exitArgs => .jump () exitArgs)
            have hmk : ∀ args, (mk args).callsOk allowed exits := fun args =>
              hdrEmit_callsOk dir args (tupSelectArgs ts xsMask args) hdr contMasks hMasks
                ((hb (exitLabels ts) ((), ())).get .here (someArgsToOpt args) (Tup.units ts))
                hbc (fun _ => trivial) (fun _ _ _ _ _ _ => trivial)
            have hDc : RotCallsL allowed exits
                (Tup.zip (as := [ts]) (RotL.expand mk, ()) ((), ()) ++ D) := by
              intro p hp
              cases hp with
              | head => exact hmk
              | tail _ hp' => exact hD p hp'
            have hpeelX := hdrPeel_callsOk (allowed := allowed) (exits := exits)
              (tail := filterTys ts xsMask) dir false hdr hMasks
              (Tup.units (exitSig hdr hMasks xsMask ts))
              ((hb (exitLabels ts) ((), ())).get .here
                (tupWiden ts xsMask (splitTail hdr hMasks
                  (Tup.units (exitSig hdr hMasks xsMask ts))))
                (Tup.units ts)) hbc
            rcases hpeelX with ⟨_, _, hwf_px, hc_px⟩
            have hpeelC := hdrPeel_callsOk (allowed := allowed) (exits := exits)
              (tail := ts) dir true hdr contMasks (Tup.units (rotSig hdr contMasks ts))
              ((hb (.expand mk, ()) ((), ())).get .here
                (someVarsToOpt (splitTail hdr contMasks
                  (Tup.units (rotSig hdr contMasks ts))))
                (Tup.units ts)) hbc
            rcases hpeelC with ⟨_, _, hwf_pc, hc_pc⟩
            exact ⟨⟨rewriteRot_callsOk exitP hwf_px hDex hc_px, trivial⟩,
              ⟨rewriteRot_callsOk contP hwf_pc hDc hc_pc, trivial⟩,
              rewriteRot_callsOk entryP (hk (.expand mk, ()) ((), ())) hDc hc.2⟩
    | let_ _ _ | load _ _ _ | store _ _ _ | call _ _ _ | jnz _ _ _ | jump _ _ | ret _
    | exit _ _ | hlt =>
      dsimp only [rewriteRot]; trivial
where
  rewriteKeepB_callsOk : (ps : List RotPlan) →
      ∀ {rs : List Ty} {G : Ctx (OptArg UnitV) UnitV} {D : Ctx (RotL UnitV UnitL rs) UnitL}
        {sig : List (List Ty)}
        (bs₁ : Blocks (OptArg UnitV) (RotL UnitV UnitL rs) rs sig)
        (bs₂ : Blocks UnitV UnitL rs sig),
        WfB G D bs₁ bs₂ → RotCallsL allowed exits D → bs₂.callsOk allowed exits →
        (rewriteRot.rewriteKeepB ps bs₁).callsOk allowed exits
    | [] => fun bs₁ bs₂ hbs hD hcbs => by
      cases hbs with
      | nil => dsimp only [rewriteRot.rewriteKeepB, flatExpr.flatBlocks]; simp only [Blocks.callsOk]
      | cons hb hbs' =>
        dsimp only [rewriteRot.rewriteKeepB, flatExpr.flatBlocks]; simp only [Blocks.callsOk]
        refine ⟨flatExpr_callsOk (hb _ (Tup.units _)) hD hcbs.1, ?_⟩
        exact rewriteKeepB_callsOk [] _ _ hbs' hD hcbs.2
    | p :: ps => fun bs₁ bs₂ hbs hD hcbs => by
      cases hbs with
      | nil => dsimp only [rewriteRot.rewriteKeepB]; simp only [Blocks.callsOk]
      | cons hb hbs' =>
        dsimp only [rewriteRot.rewriteKeepB]; simp only [Blocks.callsOk]
        exact ⟨rewriteRot_callsOk p (hb _ (Tup.units _)) hD hcbs.1,
          rewriteKeepB_callsOk ps _ _ hbs' hD hcbs.2⟩
end

end RotImpl

open RotImpl LoopRotate

/-! ## Top-level `Func` and `Fn` theorems -/

/-- `Func.loopRotateWithPlan` preserves relational well-formedness `Func.Wf`. -/
theorem Func.loopRotateWithPlan_wf {as rs : List Ty} (plan : RotPlan) {f : Func as rs}
    (hf : f.Wf) : (Func.loopRotateWithPlan plan f).Wf := by
  unfold Func.loopRotateWithPlan
  split
  · intro V₁ V₂ L₁ L₂ xs₁ xs₂
    exact rewriteRot_wf plan
      (someVarsToOpt_optWfRel xs₁ xs₂) ((fun _ hp => by cases hp) : RotLRel _ ([] : Ctx L₁ L₂) [])
      (hf (OptArg V₁) (OptArg V₂) (RotL V₁ L₁ rs) (RotL V₂ L₂ rs)
        (someVarsToOpt xs₁) (someVarsToOpt xs₂))
  · exact hf

/-- `Func.loopRotate` preserves `Func.Wf` unconditionally (even without `f.Wf`). -/
theorem Func.loopRotate_wf_uncond {as rs : List Ty} (f : Func as rs)
    (cfg : RotConfig := defaultRotConfig) : (Func.loopRotate f cfg).Wf := by
  unfold Func.loopRotate
  dsimp only
  split
  · exact Func.loopRotateWithPlan_wf _ (Func.wf_of_denote (reifyFunc f) rfl)
  · exact Func.wf_of_denote (reifyFunc f) rfl

/-- `Func.loopRotate` preserves relational well-formedness `Func.Wf`. -/
theorem Func.loopRotate_wf {as rs : List Ty} {f : Func as rs} (_hf : f.Wf)
    (cfg : RotConfig := defaultRotConfig) : (Func.loopRotate f cfg).Wf :=
  Func.loopRotate_wf_uncond f cfg

/-- `Fn.loopRotate` preserves `Fn.Wf`. -/
theorem Fn.loopRotate_wf (fn : Fn) (cfg : RotConfig := defaultRotConfig) :
    (Fn.loopRotate fn cfg).Wf :=
  Func.loopRotate_wf_uncond fn.body cfg

/-- `Func.loopRotateWithPlan` refines weakest-precondition semantics for any well-formed `f`. -/
theorem Func.loopRotateWithPlan_spec {as rs : List Ty} (plan : RotPlan) {f : Func as rs}
    (hf : f.Wf) {Γ : Env} {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Func.spec Γ f xs m Q X) : Func.spec Γ (Func.loopRotateWithPlan plan f) xs m Q X := by
  unfold Func.loopRotateWithPlan
  split
  · rename_i s hval
    have hwk := hf K (OptArg Val) BoolL (RotL Val Cont rs) (Tup.levels as 0) (someVarsToOpt xs)
    have hwk_diag := hf K K BoolL BoolL (Tup.levels as 0) (Tup.levels as 0)
    have hwf := hf (OptArg Val) Val (RotL Val Cont rs) Cont (someVarsToOpt xs) xs
    have hnd : NoneDeadOpt s (Tup.zip (Tup.levels as 0) (someVarsToOpt xs)) := by
      have h : NoneDeadOpt s (Tup.zip (Tup.levels as 0) (someVarsToOpt xs) ++ []) :=
        NoneDeadOpt.append_someVars (s := s) (Gk := []) (fun hm _ => by cases hm)
          (Tup.levels as 0) xs
      rwa [List.append_nil] at h
    have hG : SomeValEq (Tup.zip (someVarsToOpt xs) xs) := by
      have h : SomeValEq (Tup.zip (someVarsToOpt xs) xs ++ []) :=
        SomeValEq.append_someVars (G := []) (fun hm _ _ => by cases hm) xs
      rwa [List.append_nil] at h
    have hdiag : DiagK (Tup.zip (Tup.levels as 0) (Tup.levels as 0)) := by
      have h : DiagK (Tup.zip (Tup.levels as 0) (Tup.levels as 0) ++ []) :=
        DiagK.append_zip_eq (Gk := []) (fun _ hp => by cases hp) (Tup.levels as 0)
      rwa [List.append_nil] at h
    exact rewriteRot_wp plan hwk hwk_diag hwf hval hnd hG hdiag
      (fun _ hp => by cases hp) (fun _ hp => by cases hp) m h
  · exact h

/-- `Func.loopRotate` refines `Func.spec` for any well-formed function `f`. -/
theorem Func.loopRotate_spec {as rs : List Ty} {f : Func as rs} (hf : f.Wf)
    (cfg : RotConfig := defaultRotConfig) {Γ : Env} {xs : Tup Val as} {m : Mem 64}
    {Q : Post rs} {X : XPost} (h : Func.spec Γ f xs m Q X) :
    Func.spec Γ (Func.loopRotate f cfg) xs m Q X := by
  unfold Func.loopRotate
  dsimp only
  split
  · exact Func.loopRotateWithPlan_spec _ (Func.renorm_wf f) (Func.renorm_spec hf h)
  · exact Func.renorm_spec hf h

/-- `Func.loopRotate` preserves `Func.wp` semantics for any well-formed function `f`. -/
theorem Func.loopRotate_correct {as rs : List Ty} {f : Func as rs} (hf : f.Wf)
    (cfg : RotConfig := defaultRotConfig) {Γ : Env} {xs : Tup Val as} {m : Mem 64}
    {Q : Post rs} {X : XPost} (h : Func.wp Γ f xs m Q X) :
    Func.wp Γ (Func.loopRotate f cfg) xs m Q X :=
  Func.loopRotate_spec hf cfg h

/-- `Fn.loopRotate` refines `Func.spec` for any well-formed `fn`. -/
theorem Fn.loopRotate_spec {fn : Fn} (hf : fn.Wf) (cfg : RotConfig := defaultRotConfig)
    {Γ : Env} {xs : Tup Val fn.as} {m : Mem 64} {Q : Post fn.rs} {X : XPost}
    (h : Func.spec Γ fn.body xs m Q X) : Func.spec Γ (Fn.loopRotate fn cfg).body xs m Q X :=
  Func.loopRotate_spec hf cfg h

private theorem denoteB_callsOk {allowed : List SigEntry} {exits : List Sym}
    {rs : List Ty} (nv nl : Nat) (vs : List ((_t : Ty) × Unit))
    (ls : List ((_ts : List Ty) × Unit)) :
    {sig : List (List Ty)} → {bs : Blocks K KL rs sig} →
    (∀ {ts} (i : Member ts sig),
      (denote (fun _ => Unit) (fun _ => Unit)
        (toTFlat (bs.get i (Tup.levels ts nv)) (nv + ts.length) nl)
        (pushTup (Tup.units ts) vs) ls).callsOk allowed exits) →
    (denoteB (fun _ => Unit) (fun _ => Unit) (toTBlocks bs nv nl) vs ls).callsOk allowed exits
  | _, .nil, _ => trivial
  | _, .cons _ _, h =>
    ⟨h .here, denoteB_callsOk nv nl vs ls fun i => h (.there i)⟩

private theorem denote_callsOk {allowed : List SigEntry} {exits : List Sym} {rs : List Ty}
    {G : Ctx K (fun _ => Unit)} {D : Ctx KL (fun _ => Unit)}
    {e₁ : Expr K KL rs} {e₂ : Expr (fun _ => Unit) (fun _ => Unit) rs}
    (hwf : Wf G D e₁ e₂) :
    ∀ (nv nl : Nat) (vs : List ((_t : Ty) × Unit)) (ls : List ((_ts : List Ty) × Unit)),
      e₂.callsOk allowed exits →
      (denote (fun _ => Unit) (fun _ => Unit) (toTFlat e₁ nv nl) vs ls).callsOk allowed exits := by
  induction hwf using Wf.induct with
  | @let_ _ _ ts op₁ _ _ _ _ _ ih =>
    intro nv nl vs ls hc
    simp only [toTFlat, denote]
    cases denoteArgs vs (idxArgs nv op₁.args) with
    | none => trivial
    | some _ => exact ih (Tup.levels ts nv) (Tup.units ts) (nv + ts.length) nl _ ls hc
  | load _ _ _ ih =>
    intro nv nl vs ls hc
    simp only [toTFlat, denote]
    cases denoteArg vs (idxArg nv _) with
    | none => trivial
    | some _ => exact ih nv () (nv + 1) nl _ ls hc
  | store _ _ _ ih =>
    intro nv nl vs ls hc
    simp only [toTFlat, denote]
    cases denoteArg vs _ <;> cases denoteArg vs _ <;> first | trivial | exact ih nv nl vs ls hc
  | call _ _ _ ih =>
    intro nv nl vs ls ⟨hf, hc⟩
    simp only [toTFlat, denote]
    cases denoteArgs vs _ with
    | none => trivial
    | some _ => exact ⟨hf, ih (Tup.levels _ nv) (Tup.units _) (nv + _) nl _ ls hc⟩
  | jnz _ _ _ iht ihe =>
    intro nv nl vs ls ⟨ht, he⟩
    simp only [toTFlat, denote]
    cases denoteArg vs _ with
    | none => trivial
    | some _ => exact ⟨iht nv nl vs ls ht, ihe nv nl vs ls he⟩
  | jump _ _ =>
    intro nv nl vs ls _
    simp only [toTFlat, denote]
    cases lookupL ls _ _ <;> cases denoteArgs vs _ <;> trivial
  | ret _ | exit _ _ =>
    intro nv nl vs ls _
    simp only [toTFlat, denote]
    cases denoteArgs vs _ <;> trivial
  | hlt => intro _ _ _ _ _; trivial
  | @group _ _ sig b₁ b₂ k₁ k₂ _ _ ihb ihk =>
    intro nv nl vs ls ⟨hb, hk⟩
    simp only [toTFlat, denote, Expr.callsOk]
    refine ⟨denoteB_callsOk nv (nl + sig.length) vs _ fun i => ?_,
            ihk (Tup.levels sig nl) (Tup.units sig) nv (nl + sig.length) vs _ hk⟩
    exact ihb (Tup.levels sig nl) (Tup.units sig) i (Tup.levels _ nv) (Tup.units _)
      (nv + _) (nl + sig.length) _ _ (Blocks.callsOk_get hb i)

private theorem denoteFunc_reify_callsOk {allowed : List SigEntry} {exits : List Sym}
    {as rs : List Ty} {f : Func as rs} (hf : f.Wf)
    (hc : (f (fun _ => Unit) (fun _ => Unit) (Tup.units as)).callsOk allowed exits) :
    ((denoteFunc (reifyFunc f)) UnitV UnitL (Tup.units as)).callsOk allowed exits := by
  simpa [denoteFunc, reifyFunc] using
    denote_callsOk (hf K UnitV KL UnitL (Tup.levels as 0) (Tup.units as))
      as.length 0 (pushTup (Tup.units as) []) [] hc

/-- `Func.loopRotateWithPlan` preserves `Expr.callsOk` for any well-formed `f`. -/
theorem Func.loopRotateWithPlan_callsOk {allowed : List SigEntry} {exits : List Sym}
    {as rs : List Ty} (plan : RotPlan) {f : Func as rs} (hf : f.Wf)
    (hc : (f (fun _ => Unit) (fun _ => Unit) (Tup.units as)).callsOk allowed exits) :
    ((Func.loopRotateWithPlan plan f) (fun _ => Unit) (fun _ => Unit) (Tup.units as)).callsOk
      allowed exits := by
  unfold Func.loopRotateWithPlan
  cases hval : validateRotPlan plan (f K BoolL (Tup.levels as 0)) as.length with
  | some s =>
    exact rewriteRot_callsOk plan
      (hf (OptArg UnitV) UnitV (RotL UnitV UnitL rs) UnitL
        (someVarsToOpt (Tup.units as)) (Tup.units as))
      (fun _ hp => by cases hp) hc
  | none =>
    exact hc

/-- `Func.loopRotate` preserves `Expr.callsOk` for any well-formed `f`. -/
theorem Func.loopRotate_callsOk {allowed : List SigEntry} {exits : List Sym}
    {as rs : List Ty} {f : Func as rs} (hf : f.Wf) (cfg : RotConfig := defaultRotConfig)
    (hc : (f (fun _ => Unit) (fun _ => Unit) (Tup.units as)).callsOk allowed exits) :
    ((Func.loopRotate f cfg) (fun _ => Unit) (fun _ => Unit) (Tup.units as)).callsOk
      allowed exits := by
  unfold Func.loopRotate
  cases hrot : (buildRotPlan (as := as) cfg (reifyFunc f)).hasRot with
  | true =>
    simp only [↓reduceIte]
    exact Func.loopRotateWithPlan_callsOk _ (Func.wf_of_denote (reifyFunc f) rfl)
      (denoteFunc_reify_callsOk hf hc)
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact denoteFunc_reify_callsOk hf hc

/-- `Fn.loopRotate` preserves `Fn.callsOk` for any well-formed `fn`. -/
theorem Fn.loopRotate_callsOk {allowed : List SigEntry} {exits : List Sym}
    {fn : Fn} (hf : fn.Wf) (cfg : RotConfig := defaultRotConfig)
    (hc : fn.callsOk allowed exits) : (Fn.loopRotate fn cfg).callsOk allowed exits :=
  Func.loopRotate_callsOk hf cfg hc

end LeanQbe.T

