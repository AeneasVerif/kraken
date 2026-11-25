module

public import LeanQbe.T.LoopRotate
import LeanQbe.T.OptUtilLemmas
import LeanQbe.T.FlatLemmas
import LeanQbe.T.PassEnvKit
import LeanQbe.T.PassFlatKit
public import LeanQbe.T.Module

/-! # Correctness Proofs for `LeanQbe.T.LoopRotate`
Proves `*_wf`, `*_spec` / `Func.loopRotate_correct`, and `*_callsOk` for `LoopRotate`
(`flatExpr_*`, `rewriteRot_*`, `Func.loopRotateWithPlan_*`, `Func.loopRotate_*`, `Fn.loopRotate_*`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T

open PassFlatKit (DiagCtx OptDeadCtx SomeValCtx)

namespace RotImpl

open LoopRotate

/-! ## Decidable equality and tuple plumbing helpers -/

private theorem tysDecEq_self_isTrue (dts : List Ty) : tysDecEq dts dts = isTrue rfl := by
  cases h : tysDecEq dts dts with | isTrue _ => rfl | isFalse hne => exact absurd rfl hne
private theorem tyDecEq_self_isTrue (t : Ty) : tyDecEq t t = isTrue rfl := by
  cases h : tyDecEq t t with | isTrue _ => rfl | isFalse hne => exact absurd rfl hne

/-- Heterogeneous-tuple concatenation preserves `vals` pointwise. -/
private theorem vals_tupAppend : {as bs : List Ty} → (x : Tup (Arg Val) as) →
    (y : Tup (Arg Val) bs) → vals (tupAppend x y) = tupAppend (vals x) (vals y)
  | [], _, (), _ => rfl | _ :: _, _, (_, x), y => Prod.ext rfl (vals_tupAppend x y)

/-- `tupSplit` is the exact inverse of `tupAppend`. -/
private theorem tupSplit_tupAppend {f : Ty → Type} : {as bs : List Ty} → (xs : Tup f as) →
    (ys : Tup f bs) → tupSplit as (tupAppend xs ys) = (xs, ys)
  | [], _, (), _ => rfl
  | _ :: _, _, (_, x), ys => by dsimp only [tupAppend, tupSplit]; rw [tupSplit_tupAppend x ys]

private theorem tupSplit_mem_left {f₁ f₂ : Ty → Type} {G : Ctx f₁ f₂} : (as : List Ty) →
    {bs : List Ty} → {xs₁ : Tup f₁ (as ++ bs)} → {xs₂ : Tup f₂ (as ++ bs)} →
    (∀ p ∈ Tup.zip xs₁ xs₂, p ∈ G) → ∀ p ∈ Tup.zip (tupSplit as xs₁).1 (tupSplit as xs₂).1, p ∈ G
  | [], _, _, _, _, _, hp => nomatch hp
  | _ :: as, _, (_, _), (_, _), hmem, p, hp => by
    rcases List.mem_cons.1 hp with rfl | hp
    · exact hmem _ List.mem_cons_self
    · exact tupSplit_mem_left as (fun _ hq => hmem _ (List.mem_cons_of_mem _ hq)) _ hp

private theorem tupSplit_mem_right {f₁ f₂ : Ty → Type} {G : Ctx f₁ f₂} : (as : List Ty) →
    {bs : List Ty} → {xs₁ : Tup f₁ (as ++ bs)} → {xs₂ : Tup f₂ (as ++ bs)} →
    (∀ p ∈ Tup.zip xs₁ xs₂, p ∈ G) → ∀ p ∈ Tup.zip (tupSplit as xs₁).2 (tupSplit as xs₂).2, p ∈ G
  | [], _, _, _, hmem, p, hp => hmem p hp
  | _ :: as, _, (_, _), (_, _), hmem, p, hp =>
    tupSplit_mem_right as (fun _ hq => hmem _ (List.mem_cons_of_mem _ hq)) p hp

private theorem splitTail_mem {V₁ V₂ : Ty → Type} {G : Ctx V₁ V₂} {tail : List Ty} :
    (hdr : HdrPlan) → (ms : List (List Bool)) → {xs₁ : Tup V₁ (stepMasksSig hdr ms tail)} →
    {xs₂ : Tup V₂ (stepMasksSig hdr ms tail)} → (∀ p ∈ Tup.zip xs₁ xs₂, p ∈ G) →
    ∀ p ∈ Tup.zip (splitTail hdr ms xs₁) (splitTail hdr ms xs₂), p ∈ G
  | [], _, _, _, hmem, p, hp => hmem p hp
  | _ :: ss, ms, _, _, hmem, p, hp => splitTail_mem ss ms.tail (tupSplit_mem_right _ hmem) p hp

private theorem tupAppend_argRel {V₁ V₂ : Ty → Type} {G : Ctx V₁ V₂} : {as bs : List Ty} →
    {x₁ : Tup (Arg V₁) as} → {x₂ : Tup (Arg V₂) as} → {y₁ : Tup (Arg V₁) bs} →
    {y₂ : Tup (Arg V₂) bs} → TRel (ArgRel G) x₁ x₂ → TRel (ArgRel G) y₁ y₂ →
    TRel (ArgRel G) (tupAppend x₁ y₁) (tupAppend x₂ y₂)
  | [], _, (), (), _, _, .nil, hy => hy
  | _ :: _, _, (_, _), (_, _), _, _, .cons hx hxs, hy => .cons hx (tupAppend_argRel hxs hy)

private theorem eq_mpr_of_heq {α β : Sort _} (h : α = β) (x : β) (y : α) (hx : HEq x y) :
    Eq.mpr h x = y := by cases h; exact eq_of_heq hx

private theorem tupWiden_pair_cast {V : Ty → Type} {t : Ty} {ts : List Ty} {bs₁ bs₂ : List Bool}
    (hb : bs₁ = bs₂) {α : Type} (h : α = (V t × Tup V (filterTys ts bs₁)))
    (x : α) (y : V t) (ys : Tup V (filterTys ts bs₂)) (hx : HEq x (y, ys)) :
    (some (Arg.var (Eq.mp h x).1), tupWiden ts bs₁ (Eq.mp h x).2) =
      (some (Arg.var y), tupWiden ts bs₂ ys) := by
  subst hb; have hxy : Eq.mp h x = (y, ys) := eq_of_heq ((cast_heq h x).trans hx); rw [hxy]

private theorem tupWiden_tail_cast {V : Ty → Type} {t : Ty} {ts : List Ty} {bs₁ bs₂ : List Bool}
    (hb : bs₁ = bs₂) {α : Type} (h : α = Tup V (filterTys ts bs₁))
    (x : α) (ys : Tup V (filterTys ts bs₂)) (hx : HEq x ys) :
    ((none : OptArg V t), tupWiden ts bs₁ (Eq.mp h x)) = (none, tupWiden ts bs₂ ys) := by
  subst hb; have hxy : Eq.mp h x = ys := eq_of_heq ((cast_heq h x).trans hx); rw [hxy]

private theorem tupSelectArgs_nil_mask {V : Ty → Type} {t : Ty} {ts : List Ty}
    (a : Arg V t) (as : Tup (Arg V) ts) :
    tupSelectArgs (t :: ts) [] (a, as) = (a, tupSelectArgs ts [] as) := by
  dsimp only [tupSelectArgs]; split; exact eq_mpr_of_heq _ _ _ .rfl; contradiction
private theorem tupSelectArgs_true {V : Ty → Type} {t : Ty} {ts : List Ty} {bs : List Bool}
    (a : Arg V t) (as : Tup (Arg V) ts) :
    tupSelectArgs (t :: ts) (true :: bs) (a, as) = (a, tupSelectArgs ts bs as) := by
  dsimp only [tupSelectArgs]; split; exact eq_mpr_of_heq _ _ _ .rfl; contradiction
private theorem tupSelectArgs_false {V : Ty → Type} {t : Ty} {ts : List Ty} {bs : List Bool}
    (a : Arg V t) (as : Tup (Arg V) ts) :
    tupSelectArgs (t :: ts) (false :: bs) (a, as) = tupSelectArgs ts bs as := by
  dsimp only [tupSelectArgs]; split; contradiction; exact eq_mpr_of_heq _ _ _ .rfl

private theorem tupSelectArgs_argRel {V₁ V₂ : Ty → Type} {G : Ctx V₁ V₂} :
    (ts : List Ty) → (bs : List Bool) → {xs₁ : Tup (Arg V₁) ts} → {xs₂ : Tup (Arg V₂) ts} →
    TRel (ArgRel G) xs₁ xs₂ → TRel (ArgRel G) (tupSelectArgs ts bs xs₁) (tupSelectArgs ts bs xs₂)
  | [], _, (), (), .nil => .nil
  | _ :: ts, [], (_, _), (_, _), .cons hx hxs => by
    rw [tupSelectArgs_nil_mask, tupSelectArgs_nil_mask]
    exact .cons hx (tupSelectArgs_argRel ts [] hxs)
  | _ :: ts, true :: bs, (_, _), (_, _), .cons hx hxs => by
    rw [tupSelectArgs_true, tupSelectArgs_true]; exact .cons hx (tupSelectArgs_argRel ts bs hxs)
  | _ :: ts, false :: bs, (_, _), (_, _), .cons _ hxs => by
    rw [tupSelectArgs_false, tupSelectArgs_false]; exact tupSelectArgs_argRel ts bs hxs

/-- Semantic counterpart of `tupSelectArgs` on `Val` tuples. -/
private def tupSelectVals : (ts : List Ty) → (bs : List Bool) →
    Tup Val ts → Tup Val (filterTys ts bs)
  | [], _, () => ()
  | _ :: ts, bs, (v, vs) =>
    if h : bs.headD true = true then by
      dsimp only [filterTys]; simpa only [h, ↓reduceIte] using (v, tupSelectVals ts bs.tail vs)
    else by
      dsimp only [filterTys]
      simpa only [h, Bool.false_eq_true, ↓reduceIte] using tupSelectVals ts bs.tail vs

private theorem tupSelectVals_nil_mask {t : Ty} {ts : List Ty} (v : Val t) (vs : Tup Val ts) :
    tupSelectVals (t :: ts) [] (v, vs) = (v, tupSelectVals ts [] vs) := by
  dsimp only [tupSelectVals]; split; exact eq_mpr_of_heq _ _ _ .rfl; contradiction
private theorem tupSelectVals_true {t : Ty} {ts : List Ty} {bs : List Bool}
    (v : Val t) (vs : Tup Val ts) :
    tupSelectVals (t :: ts) (true :: bs) (v, vs) = (v, tupSelectVals ts bs vs) := by
  dsimp only [tupSelectVals]; split; exact eq_mpr_of_heq _ _ _ .rfl; contradiction
private theorem tupSelectVals_false {t : Ty} {ts : List Ty} {bs : List Bool}
    (v : Val t) (vs : Tup Val ts) :
    tupSelectVals (t :: ts) (false :: bs) (v, vs) = tupSelectVals ts bs vs := by
  dsimp only [tupSelectVals]; split; contradiction; exact eq_mpr_of_heq _ _ _ .rfl

private theorem tupWiden_nil_eq {V : Ty → Type} {t : Ty} {ts : List Ty}
    (xs : Tup V (filterTys (t :: ts) [])) (y : V t) (ys : Tup V (filterTys ts []))
    (h : xs = (y, ys)) : tupWiden (t :: ts) [] xs = (some (.var y), tupWiden ts [] ys) := by
  subst h; dsimp only [tupWiden]; split; exact tupWiden_pair_cast rfl _ _ y ys .rfl; contradiction
private theorem tupWiden_true_eq {V : Ty → Type} {t : Ty} {ts : List Ty} {bs : List Bool}
    (xs : Tup V (filterTys (t :: ts) (true :: bs))) (y : V t) (ys : Tup V (filterTys ts bs))
    (h : xs = (y, ys)) :
    tupWiden (t :: ts) (true :: bs) xs = (some (.var y), tupWiden ts bs ys) := by
  subst h; dsimp only [tupWiden]; split; exact tupWiden_pair_cast rfl _ _ y ys .rfl; contradiction
private theorem tupWiden_false_eq {V : Ty → Type} {t : Ty} {ts : List Ty} {bs : List Bool}
    (xs : Tup V (filterTys (t :: ts) (false :: bs))) (ys : Tup V (filterTys ts bs)) (h : xs = ys) :
    tupWiden (t :: ts) (false :: bs) xs = (none, tupWiden ts bs ys) := by
  subst h; dsimp only [tupWiden]; split; contradiction; exact tupWiden_tail_cast rfl _ _ _ .rfl

private theorem vals_tupSelectArgs : {ts : List Ty} → (bs : List Bool) → (args : Tup (Arg Val) ts) →
    vals (tupSelectArgs ts bs args) = tupSelectVals ts bs (vals args)
  | [], _, () => rfl
  | _ :: _, [], (_, args) => by
    rw [tupSelectArgs_nil_mask, tupSelectVals_nil_mask]
    exact Prod.ext rfl (vals_tupSelectArgs [] args)
  | _ :: _, true :: bs, (_, args) => by
    rw [tupSelectArgs_true, tupSelectVals_true]; exact Prod.ext rfl (vals_tupSelectArgs bs args)
  | _ :: _, false :: bs, (_, args) => by
    rw [tupSelectArgs_false, tupSelectVals_false]; exact vals_tupSelectArgs bs args

/-- Heterogeneous tuple of `HdrStep` output values produced while evaluating `hdr`. -/
@[reducible] private def HdrVals : HdrPlan → Type
  | [] => Unit | s :: ss => Tup Val s.tys × HdrVals ss

/-- Select masked header values concatenated with `tl`, matching `hdrEmit`'s argument order. -/
private def hdrSelect {tail : List Ty} : (hdr : HdrPlan) → (ms : List (List Bool)) → HdrVals hdr →
    Tup Val tail → Tup Val (stepMasksSig hdr ms tail)
  | [], _, (), tl => tl
  | s :: ss, ms, (ys, rest), tl =>
    tupAppend (tupSelectVals s.tys (ms.headD []) ys) (hdrSelect ss ms.tail rest tl)

private theorem splitTail_hdrSelect {tail : List Ty} : (hdr : HdrPlan) → (ms : List (List Bool)) →
    (hv : HdrVals hdr) → (tl : Tup Val tail) → splitTail hdr ms (hdrSelect hdr ms hv tl) = tl
  | [], _, (), _ => rfl
  | _ :: ss, ms, (_, rest), tl => by
    dsimp only [hdrSelect, splitTail]; rw [tupSplit_tupAppend]
    exact splitTail_hdrSelect ss ms.tail rest tl

/-! ## Relational invariants (`OptWfRel`, `RotLRel`) and `rewriteRot_wf` -/

/-- Binder invariant for `OptArg` contexts: both dropped (`none, none`) or both kept (`some`). -/
private abbrev OptWfRel {V₁ V₂ : Ty → Type}
    (G' : Ctx V₁ V₂) (G : Ctx (OptArg V₁) (OptArg V₂)) : Prop :=
  CtxPred (fun _ o₁ o₂ =>
    (o₁ = none ∧ o₂ = none) ∨ ∃ a₁ a₂, o₁ = some a₁ ∧ o₂ = some a₂ ∧ ArgRel G' _ a₁ a₂) G

private theorem OptWfRel.weaken {V₁ V₂ : Ty → Type} {G₁ G₂ : Ctx V₁ V₂}
    {G : Ctx (OptArg V₁) (OptArg V₂)} (hG : ∀ p ∈ G₁, p ∈ G₂) (h : OptWfRel G₁ G) : OptWfRel G₂ G :=
  CtxPred.mono (fun hr => hr.elim Or.inl fun ⟨a₁, a₂, h1, h2, ha⟩ =>
    Or.inr ⟨a₁, a₂, h1, h2, ha.weaken hG⟩) h

private theorem OptWfRel.cons_var {V₁ V₂ : Ty → Type} {G' : Ctx V₁ V₂}
    {G : Ctx (OptArg V₁) (OptArg V₂)} (hG : OptWfRel G' G) {t : Ty} (v₁ : V₁ t) (v₂ : V₂ t) :
    OptWfRel (⟨t, v₁, v₂⟩ :: G') (⟨t, some (.var v₁), some (.var v₂)⟩ :: G) :=
  CtxPred.cons (Or.inr ⟨.var v₁, .var v₂, rfl, rfl, .var List.mem_cons_self⟩)
    (hG.weaken fun _ hp => List.mem_cons_of_mem _ hp)

private theorem someVarsToOpt_optWfRel {V₁ V₂ : Ty → Type} : {ts : List Ty} → (x₁ : Tup V₁ ts) →
    (x₂ : Tup V₂ ts) → OptWfRel (Tup.zip x₁ x₂) (Tup.zip (someVarsToOpt x₁) (someVarsToOpt x₂))
  | [], (), () => CtxPred.nil _
  | _ :: _, (x₁, xs₁), (x₂, xs₂) => CtxPred.cons (Or.inr ⟨.var x₁, .var x₂, rfl, rfl,
      .var List.mem_cons_self⟩) ((someVarsToOpt_optWfRel xs₁ xs₂).weaken fun _ hp =>
        List.mem_cons_of_mem _ hp)

private theorem OptWfRel.append_someVars {V₁ V₂ : Ty → Type} {G' : Ctx V₁ V₂}
    {G : Ctx (OptArg V₁) (OptArg V₂)} (hG : OptWfRel G' G) {ts : List Ty} (xs₁ : Tup V₁ ts)
    (xs₂ : Tup V₂ ts) :
    OptWfRel (Tup.zip xs₁ xs₂ ++ G') (Tup.zip (someVarsToOpt xs₁) (someVarsToOpt xs₂) ++ G) :=
  CtxPred.append ((someVarsToOpt_optWfRel xs₁ xs₂).weaken fun _ hp => List.mem_append_left _ hp)
    (hG.weaken fun _ hp => List.mem_append_right _ hp)

private theorem someArgsToOpt_optWfRel {V₁ V₂ : Ty → Type} {G' : Ctx V₁ V₂} : {ts : List Ty} →
    {a₁ : Tup (Arg V₁) ts} → {a₂ : Tup (Arg V₂) ts} → TRel (ArgRel G') a₁ a₂ →
    OptWfRel G' (Tup.zip (someArgsToOpt a₁) (someArgsToOpt a₂))
  | [], (), (), .nil => CtxPred.nil _
  | _ :: _, (_, _), (_, _), .cons ha has =>
    CtxPred.cons (Or.inr ⟨_, _, rfl, rfl, ha⟩) (someArgsToOpt_optWfRel has)

private theorem tupWiden_optWfRel {V₁ V₂ : Ty → Type} {G' : Ctx V₁ V₂} :
    (ts : List Ty) → (bs : List Bool) →
    {ys₁ : Tup V₁ (filterTys ts bs)} → {ys₂ : Tup V₂ (filterTys ts bs)} →
    (∀ p ∈ Tup.zip ys₁ ys₂, p ∈ G') →
    OptWfRel G' (Tup.zip (tupWiden ts bs ys₁) (tupWiden ts bs ys₂))
  | [], _, _, _, _ => CtxPred.nil _
  | _ :: ts, [], ys₁, ys₂, hmem => by
    let p₁ : V₁ _ × _ := ys₁; let p₂ : V₂ _ × _ := ys₂
    rw [tupWiden_nil_eq ys₁ p₁.1 p₁.2 rfl, tupWiden_nil_eq ys₂ p₂.1 p₂.2 rfl]
    exact CtxPred.cons (Or.inr ⟨_, _, rfl, rfl, .var (hmem _ List.mem_cons_self)⟩)
      (tupWiden_optWfRel ts [] (fun _ hp => hmem _ (List.mem_cons_of_mem _ hp)))
  | _ :: ts, true :: bs, ys₁, ys₂, hmem => by
    let p₁ : V₁ _ × _ := ys₁; let p₂ : V₂ _ × _ := ys₂
    rw [tupWiden_true_eq ys₁ p₁.1 p₁.2 rfl, tupWiden_true_eq ys₂ p₂.1 p₂.2 rfl]
    exact CtxPred.cons (Or.inr ⟨_, _, rfl, rfl, .var (hmem _ List.mem_cons_self)⟩)
      (tupWiden_optWfRel ts bs (fun _ hp => hmem _ (List.mem_cons_of_mem _ hp)))
  | _ :: ts, false :: bs, ys₁, ys₂, hmem => by
    let p₁ : Tup V₁ _ := ys₁; let p₂ : Tup V₂ _ := ys₂
    rw [tupWiden_false_eq ys₁ p₁ rfl, tupWiden_false_eq ys₂ p₂ rfl]
    exact CtxPred.cons (Or.inl ⟨rfl, rfl⟩) (tupWiden_optWfRel ts bs hmem)

private theorem flatOptArg_argRel {V₁ V₂ : Ty → Type} {G' : Ctx V₁ V₂}
    {G : Ctx (OptArg V₁) (OptArg V₂)} (hG : OptWfRel G' G)
    {t : Ty} {a₁ : Arg (OptArg V₁) t} {a₂ : Arg (OptArg V₂) t} :
    ArgRel G t a₁ a₂ → ArgRel G' t (flatOptArg a₁) (flatOptArg a₂)
  | .var hm =>
    (CtxPred.mem hG hm).elim (fun ⟨h1, h2⟩ => h1 ▸ h2 ▸ .imm default)
      fun ⟨_, _, h1, h2, ha⟩ => h1 ▸ h2 ▸ ha
  | .imm c => .imm c

private theorem flatOptArgs_trel {V₁ V₂ : Ty → Type} {G' : Ctx V₁ V₂}
    {G : Ctx (OptArg V₁) (OptArg V₂)} (hG : OptWfRel G' G) {ts : List Ty}
    {a₁ : Tup (Arg (OptArg V₁)) ts} {a₂ : Tup (Arg (OptArg V₂)) ts} :
    TRel (ArgRel G) a₁ a₂ → TRel (ArgRel G') (flatOptArgs a₁) (flatOptArgs a₂) :=
  TRel.tupMapArg_rel (fun _ => flatOptArg) (fun _ => flatOptArg) (flatOptArg_argRel hG)

private theorem flatOptOp_opRel {V₁ V₂ : Ty → Type} {G' : Ctx V₁ V₂}
    {G : Ctx (OptArg V₁) (OptArg V₂)} (hG : OptWfRel G' G) {rs : List Ty} {op₁ : Op (OptArg V₁) rs}
    {op₂ : Op (OptArg V₂) rs} : OpRel G op₁ op₂ → OpRel G' (flatOptOp op₁) (flatOptOp op₂)
  | .mk code hargs => .mk code (flatOptArgs_trel hG hargs)

/-- Label relation pairing `RotL` entries across target contexts `(G', D')`. -/
private inductive RotLRelEntry {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    (G' : Ctx V₁ V₂) (D' : Ctx L₁ L₂) : {ts : List Ty} → RotL V₁ L₁ rs ts → RotL V₂ L₂ rs ts → Prop
  | keep {ts l₁ l₂} : ⟨ts, l₁, l₂⟩ ∈ D' → RotLRelEntry G' D' (.keep l₁) (.keep l₂)
  | dead {ts} : RotLRelEntry G' D' (ts := ts) .dead .dead
  | expand {ts} {f₁ : Tup (Arg V₁) ts → Expr V₁ L₁ rs} {f₂ : Tup (Arg V₂) ts → Expr V₂ L₂ rs} :
      (∀ {G'' D''}, (∀ p ∈ G', p ∈ G'') → (∀ p ∈ D', p ∈ D'') →
        ∀ a₁ a₂, TRel (ArgRel G'') a₁ a₂ → Wf G'' D'' (f₁ a₁) (f₂ a₂)) →
      RotLRelEntry G' D' (.expand f₁) (.expand f₂)
  | expandOrKeep {ts} {f₁ : Tup (Arg V₁) ts → Expr V₁ L₁ rs} {f₂ : Tup (Arg V₂) ts → Expr V₂ L₂ rs}
      {lHdr₁ lHdr₂} : ⟨ts, lHdr₁, lHdr₂⟩ ∈ D' →
      (∀ {G'' D''}, (∀ p ∈ G', p ∈ G'') → (∀ p ∈ D', p ∈ D'') →
        ∀ a₁ a₂, TRel (ArgRel G'') a₁ a₂ → Wf G'' D'' (f₁ a₁) (f₂ a₂)) →
      RotLRelEntry G' D' (.expandOrKeep f₁ lHdr₁) (.expandOrKeep f₂ lHdr₂)

private theorem RotLRelEntry.weaken {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G₁ G₂ : Ctx V₁ V₂} {D₁ D₂ : Ctx L₁ L₂} (hG : ∀ p ∈ G₁, p ∈ G₂) (hD : ∀ p ∈ D₁, p ∈ D₂)
    {ts : List Ty} {l₁ : RotL V₁ L₁ rs ts} {l₂ : RotL V₂ L₂ rs ts} :
    RotLRelEntry G₁ D₁ l₁ l₂ → RotLRelEntry G₂ D₂ l₁ l₂
  | .keep h => .keep (hD _ h)
  | .dead => .dead
  | .expand hb => .expand fun hG' hD' => hb (fun _ h => hG' _ (hG _ h)) (fun _ h => hD' _ (hD _ h))
  | .expandOrKeep hl hb => .expandOrKeep (hD _ hl)
    fun hG' hD' => hb (fun _ h => hG' _ (hG _ h)) (fun _ h => hD' _ (hD _ h))

/-- Context-wide `RotLRelEntry` invariant. -/
private abbrev RotLRel {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    (G' : Ctx V₁ V₂) (D' : Ctx L₁ L₂) (D : Ctx (RotL V₁ L₁ rs) (RotL V₂ L₂ rs)) : Prop :=
  CtxPred (fun _ l₁ l₂ => RotLRelEntry G' D' l₁ l₂) D

private theorem RotLRel.weaken {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G₁ G₂ : Ctx V₁ V₂} {D₁ D₂ : Ctx L₁ L₂} {D : Ctx (RotL V₁ L₁ rs) (RotL V₂ L₂ rs)}
    (hG : ∀ p ∈ G₁, p ∈ G₂) (hD : ∀ p ∈ D₁, p ∈ D₂) (h : RotLRel G₁ D₁ D) : RotLRel G₂ D₂ D :=
  CtxPred.mono (fun hr => hr.weaken hG hD) h

private theorem wrapKeepLabels_rel {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G' : Ctx V₁ V₂} {D' : Ctx L₁ L₂} : {sig : List (List Ty)} → (J₁ : Tup L₁ sig) →
    (J₂ : Tup L₂ sig) → RotLRel G' (Tup.zip J₁ J₂ ++ D')
      (Tup.zip (wrapKeepLabels (V := V₁) (rs := rs) J₁) (wrapKeepLabels (V := V₂) (rs := rs) J₂))
  | [], (), () => CtxPred.nil _
  | _ :: _, (_, j₁), (_, j₂) => CtxPred.cons (.keep List.mem_cons_self)
    ((wrapKeepLabels_rel j₁ j₂).weaken (fun _ h => h) fun _ h => List.mem_cons_of_mem _ h)

private theorem exitLabels_rel {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G' : Ctx V₁ V₂} {D' : Ctx L₁ L₂} (ts : List Ty) : RotLRel G' D'
      (Tup.zip (exitLabels (V := V₁) (L := L₁) (rs := rs) ts) (exitLabels (V := V₂) ts)) :=
  CtxPred.cons .dead (CtxPred.nil _)

private theorem flatBlocks_get {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    {sig : List (List Ty)} → {bs : Blocks (OptArg V) (RotL V L rs) rs sig} → {ts : List Ty} →
    (i : Member ts sig) → (xs : Tup V ts) →
    (flatExpr.flatBlocks bs).get i xs = flatExpr (bs.get i (someVarsToOpt xs))
  | _, .cons _ _, _, .here, _ => rfl
  | _, .cons _ _, _, .there i, xs => flatBlocks_get i xs

/-- `flatExpr` preserves relational well-formedness `Wf`. -/
private theorem flatExpr_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx (OptArg V₁) (OptArg V₂)} {D : Ctx (RotL V₁ L₁ rs) (RotL V₂ L₂ rs)}
    {e₁ : Expr (OptArg V₁) (RotL V₁ L₁ rs) rs} {e₂ : Expr (OptArg V₂) (RotL V₂ L₂ rs) rs}
    (hwf : Wf G D e₁ e₂) : ∀ {G' : Ctx V₁ V₂} {D' : Ctx L₁ L₂},
      OptWfRel G' G → RotLRel G' D' D → Wf G' D' (flatExpr e₁) (flatExpr e₂) := by
  induction hwf using Wf.induct with
  | let_ hop _ ih =>
    exact fun hG hD => .let_ (flatOptOp_opRel hG hop) fun x₁ x₂ => ih (someVarsToOpt x₁)
      (someVarsToOpt x₂) (OptWfRel.append_someVars hG x₁ x₂)
      (RotLRel.weaken (fun _ hp => List.mem_append_right _ hp) (fun _ h => h) hD)
  | load t ha _ ih =>
    exact fun hG hD => .load t (flatOptArg_argRel hG ha) fun v₁ v₂ => ih (some (.var v₁))
      (some (.var v₂)) (OptWfRel.cons_var hG v₁ v₂)
      (RotLRel.weaken (fun _ hp => List.mem_cons_of_mem _ hp) (fun _ h => h) hD)
  | store hv ha _ ih =>
    exact fun hG hD => .store (flatOptArg_argRel hG hv) (flatOptArg_argRel hG ha) (ih hG hD)
  | call f hargs _ ih =>
    exact fun hG hD => .call f (flatOptArgs_trel hG hargs) fun x₁ x₂ => ih (someVarsToOpt x₁)
      (someVarsToOpt x₂) (OptWfRel.append_someVars hG x₁ x₂)
      (RotLRel.weaken (fun _ hp => List.mem_append_right _ hp) (fun _ h => h) hD)
  | jnz hc _ _ iht ihe => exact fun hG hD => .jnz (flatOptArg_argRel hG hc) (iht hG hD) (ihe hG hD)
  | jump hj hargs =>
    intro _ _ hG hD
    cases CtxPred.mem hD hj with
    | keep hj' => exact .jump hj' (flatOptArgs_trel hG hargs)
    | dead => exact .hlt
    | expand hf | expandOrKeep _ hf =>
      exact hf (fun _ h => h) (fun _ h => h) _ _ (flatOptArgs_trel hG hargs)
  | ret hvs => exact fun hG _ => .ret (flatOptArgs_trel hG hvs)
  | exit f hargs => exact fun hG _ => .exit f (flatOptArgs_trel hG hargs)
  | hlt => exact fun _ _ => .hlt
  | @group _ _ sig _ _ _ _ _ _ ihb ihk =>
    intro G' D' hG hD
    let mkD (Js₁ : Tup L₁ sig) (Js₂ : Tup L₂ sig) := CtxPred.append (wrapKeepLabels_rel Js₁ Js₂)
      (RotLRel.weaken (fun _ h => h) (fun _ h => List.mem_append_right _ h) hD)
    refine .group (fun Js₁ Js₂ => WfB.of_get fun i xs₁ xs₂ => ?_)
      (fun Js₁ Js₂ => ihk (wrapKeepLabels Js₁) (wrapKeepLabels Js₂) hG (mkD Js₁ Js₂))
    rw [flatBlocks_get, flatBlocks_get]; exact ihb _ _ i (someVarsToOpt xs₁) (someVarsToOpt xs₂)
      (OptWfRel.append_someVars hG xs₁ xs₂) (RotLRel.weaken (fun _ h => List.mem_append_right _ h)
        (fun _ h => h) (mkD Js₁ Js₂))

private theorem hdrPeel_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs tail : List Ty}
    {G' : Ctx V₁ V₂} (dir wantCont : Bool) : (hdr : HdrPlan) → (ms : List (List Bool)) →
    {p₁ : Tup V₁ (stepMasksSig hdr ms tail)} → {p₂ : Tup V₂ (stepMasksSig hdr ms tail)} →
    {G : Ctx (OptArg V₁) (OptArg V₂)} → {D : Ctx (RotL V₁ L₁ rs) (RotL V₂ L₂ rs)} →
    {e₁ : Expr (OptArg V₁) (RotL V₁ L₁ rs) rs} → {e₂ : Expr (OptArg V₂) (RotL V₂ L₂ rs) rs} →
    (∀ p ∈ Tup.zip p₁ p₂, p ∈ G') → OptWfRel G' G → Wf G D e₁ e₂ → ∃ G_out, OptWfRel G' G_out ∧
    Wf G_out D (hdrPeel dir wantCont hdr ms p₁ e₁) (hdrPeel dir wantCont hdr ms p₂ e₂)
  | [], _, _, _, _, _, _, _, _, hG, hwf => by
    cases hwf with
    | jnz _ ht he =>
      refine ⟨_, hG, ?_⟩
      cases hwd : wantCont == dir <;> (dsimp only [hdrPeel]; simp [hwd, ht, he])
    | _ => exact ⟨_, hG, .hlt⟩
  | .let_ dts :: ss, ms, p₁, p₂, _, _, _, _, hpar, hG, hwf => by
    cases hwf with
    | @let_ _ _ dts' _ _ _ _ _ hk =>
      cases hdec : tysDecEq dts dts' with
      | isFalse => dsimp only [hdrPeel]; simp only [hdec]; exact ⟨_, hG, .hlt⟩
      | isTrue heq =>
        subst heq; dsimp only [hdrPeel]; simp only [tysDecEq_self_isTrue dts]
        exact hdrPeel_wf dir wantCont ss ms.tail (tupSplit_mem_right _ hpar) (CtxPred.append
          (tupWiden_optWfRel dts (ms.headD []) (tupSplit_mem_left (filterTys dts _) hpar)) hG)
          (hk (tupWiden _ _ (tupSplit _ p₁).1) (tupWiden _ _ (tupSplit _ p₂).1))
    | _ => exact ⟨_, hG, .hlt⟩
  | .load t :: ss, ms, p₁, p₂, _, _, _, _, hpar, hG, hwf => by
    cases hwf with
    | @load _ _ t' _ _ _ _ _ hk =>
      cases hdec : tyDecEq t t' with
      | isFalse => dsimp only [hdrPeel]; simp only [hdec]; exact ⟨_, hG, .hlt⟩
      | isTrue heq =>
        subst heq; dsimp only [hdrPeel]; simp only [tyDecEq_self_isTrue t]
        have hL := tupSplit_mem_left (filterTys [t] (ms.headD [])) hpar
        exact hdrPeel_wf dir wantCont ss ms.tail (tupSplit_mem_right _ hpar) (CtxPred.cons
          (CtxPred.mem (tupWiden_optWfRel [t] _ hL) List.mem_cons_self) hG)
          (hk (tupWiden [t] _ (tupSplit _ p₁).1).1 (tupWiden [t] _ (tupSplit _ p₂).1).1)
    | _ => exact ⟨_, hG, .hlt⟩

private theorem hdrEmit_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs tailC tailX : List Ty}
    {D' : Ctx L₁ L₂} (dir : Bool) : (hdr : HdrPlan) → (cMs xMs : List (List Bool)) →
    {G' : Ctx V₁ V₂} → {G : Ctx (OptArg V₁) (OptArg V₂)} →
    {D : Ctx (RotL V₁ L₁ rs) (RotL V₂ L₂ rs)} →
    {e₁ : Expr (OptArg V₁) (RotL V₁ L₁ rs) rs} → {e₂ : Expr (OptArg V₂) (RotL V₂ L₂ rs) rs} →
    {tc₁ : Tup (Arg V₁) tailC} → {tc₂ : Tup (Arg V₂) tailC} →
    {tx₁ : Tup (Arg V₁) tailX} → {tx₂ : Tup (Arg V₂) tailX} →
    {kC₁ : Tup (Arg V₁) (stepMasksSig hdr cMs tailC) → Expr V₁ L₁ rs} →
    {kC₂ : Tup (Arg V₂) (stepMasksSig hdr cMs tailC) → Expr V₂ L₂ rs} →
    {kX₁ : Expr (OptArg V₁) (RotL V₁ L₁ rs) rs →
      Tup (Arg V₁) (stepMasksSig hdr xMs tailX) → Expr V₁ L₁ rs} →
    {kX₂ : Expr (OptArg V₂) (RotL V₂ L₂ rs) rs →
      Tup (Arg V₂) (stepMasksSig hdr xMs tailX) → Expr V₂ L₂ rs} →
    OptWfRel G' G → RotLRel G' D' D → Wf G D e₁ e₂ → TRel (ArgRel G') tc₁ tc₂ →
    TRel (ArgRel G') tx₁ tx₂ →
    (∀ {G''}, (∀ p ∈ G', p ∈ G'') →
      ∀ {a₁ a₂}, TRel (ArgRel G'') a₁ a₂ → Wf G'' D' (kC₁ a₁) (kC₂ a₂)) →
    (∀ {G'' Gx Dx}, (∀ p ∈ G', p ∈ G'') → OptWfRel G'' Gx → RotLRel G'' D' Dx →
      ∀ {ex₁ ex₂}, Wf Gx Dx ex₁ ex₂ →
      ∀ {a₁ a₂}, TRel (ArgRel G'') a₁ a₂ → Wf G'' D' (kX₁ ex₁ a₁) (kX₂ ex₂ a₂)) →
    Wf G' D' (hdrEmit dir tc₁ tx₁ hdr cMs xMs e₁ kC₁ kX₁)
      (hdrEmit dir tc₂ tx₂ hdr cMs xMs e₂ kC₂ kX₂)
  | [], _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hG, hD, hwf, htc, htx, hkC, hkX => by
    cases hwf with
    | jnz hc ht he =>
      cases dir <;> dsimp only [hdrEmit]
      · exact .jnz (flatOptArg_argRel hG hc) (hkX (fun _ h => h) hG hD ht htx)
          (hkC (fun _ h => h) htc)
      · exact .jnz (flatOptArg_argRel hG hc) (hkC (fun _ h => h) htc)
          (hkX (fun _ h => h) hG hD he htx)
    | _ => exact .hlt
  | .let_ dts :: ss, cMs, xMs, G', _, _, _, _, _, _, _, _, _, _, _, _,
      hG, hD, hwf, htc, htx, hkC, hkX => by
    cases hwf with
    | @let_ _ _ dts' _ _ _ _ hop hk =>
      cases hdec : tysDecEq dts dts' with
      | isFalse => dsimp only [hdrEmit]; simp only [hdec]; exact .hlt
      | isTrue heq =>
        subst heq; dsimp only [hdrEmit]; simp only [tysDecEq_self_isTrue dts]
        refine .let_ (flatOptOp_opRel hG hop) fun ys₁ ys₂ => ?_
        have hsub : ∀ p ∈ G', p ∈ Tup.zip ys₁ ys₂ ++ G' := fun _ hp => List.mem_append_right _ hp
        refine hdrEmit_wf dir ss cMs.tail xMs.tail (OptWfRel.append_someVars hG ys₁ ys₂)
          (RotLRel.weaken hsub (fun _ h => h) hD) (hk (someVarsToOpt ys₁) (someVarsToOpt ys₂))
          (htc.argRel_weaken hsub) (htx.argRel_weaken hsub) (fun hG'' _ _ ha => hkC
            (fun _ hp => hG'' _ (hsub _ hp)) (tupAppend_argRel (tupSelectArgs_argRel dts _
              ((toArgTup_trel ys₁ ys₂).argRel_weaken fun _ hp => hG'' _
                (List.mem_append_left _ hp))) ha))
          fun hG'' hGx hDx _ _ hex _ _ ha => hkX (fun _ hp => hG'' _ (hsub _ hp)) hGx hDx hex
            (tupAppend_argRel (tupSelectArgs_argRel dts _ ((toArgTup_trel ys₁ ys₂).argRel_weaken
              fun _ hp => hG'' _ (List.mem_append_left _ hp))) ha)
    | _ => exact .hlt
  | .load t :: ss, cMs, xMs, G', _, _, _, _, _, _, _, _, _, _, _, _,
      hG, hD, hwf, htc, htx, hkC, hkX => by
    cases hwf with
    | @load _ _ t' _ _ _ _ ha hk =>
      cases hdec : tyDecEq t t' with
      | isFalse => dsimp only [hdrEmit]; simp only [hdec]; exact .hlt
      | isTrue heq =>
        subst heq; dsimp only [hdrEmit]; simp only [tyDecEq_self_isTrue t]
        refine .load t (flatOptArg_argRel hG ha) fun v₁ v₂ => ?_
        have hsub : ∀ p ∈ G', p ∈ ⟨t, v₁, v₂⟩ :: G' := fun _ hp => List.mem_cons_of_mem _ hp
        refine hdrEmit_wf dir ss cMs.tail xMs.tail (OptWfRel.cons_var hG v₁ v₂)
          (RotLRel.weaken hsub (fun _ h => h) hD) (hk (some (.var v₁)) (some (.var v₂)))
          (htc.argRel_weaken hsub) (htx.argRel_weaken hsub) (fun hG'' _ _ ha => hkC
            (fun _ hp => hG'' _ (hsub _ hp)) (tupAppend_argRel (tupSelectArgs_argRel [t] _
              (.cons (.var (hG'' _ List.mem_cons_self)) .nil)) ha))
          fun hG'' hGx hDx _ _ hex _ _ ha => hkX (fun _ hp => hG'' _ (hsub _ hp)) hGx hDx hex
            (tupAppend_argRel (tupSelectArgs_argRel [t] _
              (.cons (.var (hG'' _ List.mem_cons_self)) .nil)) ha)
    | _ => exact .hlt

mutual
private theorem rewriteRotWith_wf : (allowHdr : Bool) → (plan : RotPlan) →
    ∀ {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty} {G' : Ctx V₁ V₂}
      {D' : Ctx L₁ L₂} {G : Ctx (OptArg V₁) (OptArg V₂)}
      {D : Ctx (RotL V₁ L₁ rs) (RotL V₂ L₂ rs)} {e₁ : Expr (OptArg V₁) (RotL V₁ L₁ rs) rs}
      {e₂ : Expr (OptArg V₂) (RotL V₂ L₂ rs) rs}, OptWfRel G' G → RotLRel G' D' D →
      Wf G D e₁ e₂ → Wf G' D' (rewriteRotWith allowHdr plan e₁) (rewriteRotWith allowHdr plan e₂)
  | _, .leaf => fun hG hD hwf => by dsimp only [rewriteRotWith]; exact flatExpr_wf hwf hG hD
  | allowHdr, .letP p => fun hG hD hwf => by
    cases hwf with
    | let_ hop hk =>
      dsimp only [rewriteRotWith]; exact .let_ (flatOptOp_opRel hG hop) fun x₁ x₂ =>
        rewriteRotWith_wf allowHdr p (OptWfRel.append_someVars hG x₁ x₂)
          (RotLRel.weaken (fun _ hp => List.mem_append_right _ hp) (fun _ h => h) hD) (hk _ _)
    | _ => dsimp only [rewriteRotWith]; exact .hlt
  | allowHdr, .loadP p => fun hG hD hwf => by
    cases hwf with
    | load t ha hk =>
      dsimp only [rewriteRotWith]; exact .load t (flatOptArg_argRel hG ha) fun v₁ v₂ =>
        rewriteRotWith_wf allowHdr p (OptWfRel.cons_var hG v₁ v₂)
          (RotLRel.weaken (fun _ hp => List.mem_cons_of_mem _ hp) (fun _ h => h) hD) (hk _ _)
    | _ => dsimp only [rewriteRotWith]; exact .hlt
  | allowHdr, .storeP p => fun hG hD hwf => by
    cases hwf with
    | store hv ha hk =>
      dsimp only [rewriteRotWith]; exact .store (flatOptArg_argRel hG hv)
        (flatOptArg_argRel hG ha) (rewriteRotWith_wf allowHdr p hG hD hk)
    | _ => dsimp only [rewriteRotWith]; exact .hlt
  | allowHdr, .callP p => fun hG hD hwf => by
    cases hwf with
    | call f hargs hk =>
      dsimp only [rewriteRotWith]; exact .call f (flatOptArgs_trel hG hargs) fun x₁ x₂ =>
        rewriteRotWith_wf allowHdr p (OptWfRel.append_someVars hG x₁ x₂)
          (RotLRel.weaken (fun _ hp => List.mem_append_right _ hp) (fun _ h => h) hD) (hk _ _)
    | _ => dsimp only [rewriteRotWith]; exact .hlt
  | allowHdr, .jnzP tp ep => fun hG hD hwf => by
    cases hwf with
    | jnz hc ht he =>
      dsimp only [rewriteRotWith]; exact .jnz (flatOptArg_argRel hG hc)
        (rewriteRotWith_wf allowHdr tp hG hD ht) (rewriteRotWith_wf allowHdr ep hG hD he)
    | jump hj hargs =>
      cases allowHdr <;> (cases tp <;> cases ep <;> dsimp only [rewriteRotWith])
      all_goals first | exact .hlt | (cases CtxPred.mem hD hj with
        | keep hj' | expandOrKeep hj' _ => exact .jump hj' (flatOptArgs_trel hG hargs)
        | expand hf => exact hf (fun _ h => h) (fun _ h => h) _ _ (flatOptArgs_trel hG hargs)
        | dead => exact .hlt)
    | _ =>
      dsimp only [rewriteRotWith]
      cases allowHdr <;> first | exact .hlt | (cases tp <;> cases ep <;> exact .hlt)
  | allowHdr, .groupKeep bsP kP => fun hG hD hwf => by
    cases hwf with
    | @group _ _ sig b₁ b₂ _ _ hb hk =>
      dsimp only [rewriteRotWith]
      refine .group (fun Js₁ Js₂ => ?_) (fun Js₁ Js₂ => ?_)
      · exact rewriteKeepB_wf allowHdr bsP hG (CtxPred.append (wrapKeepLabels_rel Js₁ Js₂)
          (RotLRel.weaken (fun _ h => h) (fun _ h => List.mem_append_right _ h) hD)) (hb _ _)
      · exact rewriteRotWith_wf allowHdr kP hG (CtxPred.append (wrapKeepLabels_rel Js₁ Js₂)
          (RotLRel.weaken (fun _ h => h) (fun _ h => List.mem_append_right _ h) hD)) (hk _ _)
    | _ => dsimp only [rewriteRotWith]; exact .hlt
  | allowHdr, .groupRot dir hdr contMasks exitMode contP exitP entryP => fun hG hD hwf => by
    suffices H : ∀ {V₁ V₂ L₁ L₂ rs} {G' : Ctx V₁ V₂} {D' : Ctx L₁ L₂} {G : Ctx (OptArg V₁)
        (OptArg V₂)} {D : Ctx (RotL V₁ L₁ rs) (RotL V₂ L₂ rs)} {e₁ e₂}, OptWfRel G' G →
        RotLRel G' D' D → Wf G D e₁ e₂ → Wf G' D' (rewriteRotWith allowHdr
          (.groupRot dir hdr contMasks exitMode contP exitP entryP) e₁) (rewriteRotWith allowHdr
          (.groupRot dir hdr contMasks exitMode contP exitP entryP) e₂) from H hG hD hwf
    intro V₁ V₂ L₁ L₂ rs G' D' G D e₁ e₂ hG hD hwf
    cases hwf with
    | @group _ _ sig bs₁ bs₂ k₁ k₂ hb hk =>
      cases sig with
      | nil => dsimp only [rewriteRotWith]; exact .hlt
      | cons ts sig' =>
        cases sig' with
        | cons _ _ => dsimp only [rewriteRotWith]; exact .hlt
        | nil =>
          let rotGrp {V : Ty → Type} {L : List Ty → Type}
              (bs : Tup (RotL V L rs) [ts] → Blocks (OptArg V) (RotL V L rs) rs [ts])
              (k : Tup (RotL V L rs) [ts] → Expr (OptArg V) (RotL V L rs) rs)
              (mk : L (rotSig hdr contMasks ts) → Tup (Arg V) ts → Expr V L rs) : Expr V L rs :=
            if isPartialMasks hdr contMasks then .group (sig := [rotSig hdr contMasks ts, ts])
                (fun (J_rot, J_hdr, ()) => .cons (fun p => rewriteRotWith true contP
                  (rotBodyExpr dir hdr contMasks bs (.expandOrKeep (mk J_rot) J_hdr) p))
                  (.cons (fun h => mk J_rot (toArgTup h)) .nil))
                (fun (J_rot, _, ()) => rewriteRotWith allowHdr entryP (k (.expand (mk J_rot), ())))
            else .group (sig := [rotSig hdr contMasks ts])
                (fun (J_rot, ()) => .cons (fun p => rewriteRotWith allowHdr contP
                  (rotBodyExpr dir hdr contMasks bs (.expand (mk J_rot)) p)) .nil)
                (fun (J_rot, ()) => rewriteRotWith allowHdr entryP (k (.expand (mk J_rot), ())))
          have emitLoop : ∀ {D_out : Ctx L₁ L₂}, (∀ q ∈ D', q ∈ D_out) →
              ∀ (mk₁ : L₁ (rotSig hdr contMasks ts) → Tup (Arg V₁) ts → Expr V₁ L₁ rs)
                (mk₂ : L₂ (rotSig hdr contMasks ts) → Tup (Arg V₂) ts → Expr V₂ L₂ rs),
              (∀ {G'' D''} J₁ J₂, (∀ q ∈ G', q ∈ G'') → (∀ q ∈ D_out, q ∈ D'') →
                ⟨rotSig hdr contMasks ts, J₁, J₂⟩ ∈ D'' →
                ∀ a₁ a₂, TRel (ArgRel G'') a₁ a₂ → Wf G'' D'' (mk₁ J₁ a₁) (mk₂ J₂ a₂)) →
              Wf G' D_out (rotGrp bs₁ k₁ mk₁) (rotGrp bs₂ k₂ mk₂) := by
            intro D_out hDxSub mk₁ mk₂ hmk
            have hDx := RotLRel.weaken (fun _ h => h) hDxSub hD
            have mkK {D''} (J₁ : L₁ _) (J₂ : L₂ _) (hD'sub : ∀ q ∈ D_out, q ∈ D'')
                (hRotMem : ⟨rotSig hdr contMasks ts, J₁, J₂⟩ ∈ D'') :
                Wf G' D'' (rewriteRotWith allowHdr entryP (k₁ (.expand (mk₁ J₁), ())))
                  (rewriteRotWith allowHdr entryP (k₂ (.expand (mk₂ J₂), ()))) := by
              have hDk' : RotLRel G' D''
                  (Tup.zip (as := [ts]) (.expand (mk₁ J₁), ()) (.expand (mk₂ J₂), ()) ++ D) := by
                intro q hq
                cases hq with
                | head =>
                  exact .expand fun hG'' hD'' =>
                    hmk J₁ J₂ hG'' (fun _ h => hD'' _ (hD'sub _ h)) (hD'' _ hRotMem)
                | tail _ hq => exact RotLRel.weaken (fun _ h => h) hD'sub hDx q hq
              exact rewriteRotWith_wf allowHdr entryP hG hDk'
                (hk (.expand (mk₁ J₁), ()) (.expand (mk₂ J₂), ()))
            have mkB {D''} (allow' : Bool) (j₁ : RotL V₁ L₁ rs ts) (j₂ : RotL V₂ L₂ rs ts)
                (hj : ∀ G'' (p₁ : Tup V₁ (rotSig hdr contMasks ts)) p₂, (∀ q ∈ G', q ∈ G'') →
                  (∀ q ∈ Tup.zip p₁ p₂, q ∈ G'') →
                  RotLRel G'' D'' (Tup.zip (as := [ts]) (j₁, ()) (j₂, ()) ++ D)) p₁ p₂ :
                Wf (Tup.zip p₁ p₂ ++ G') D''
                  (rewriteRotWith allow' contP (rotBodyExpr dir hdr contMasks bs₁ j₁ p₁))
                  (rewriteRotWith allow' contP (rotBodyExpr dir hdr contMasks bs₂ j₂ p₂)) := by
              let G'' := Tup.zip p₁ p₂ ++ G'
              have hG'sub : ∀ q ∈ G', q ∈ G'' := fun _ hq => List.mem_append_right _ hq
              have hpMem : ∀ q ∈ Tup.zip p₁ p₂, q ∈ G'' := fun _ hq => List.mem_append_left _ hq
              obtain ⟨_, hG_peel, hpeel⟩ := hdrPeel_wf dir true hdr contMasks hpMem
                (CtxPred.append (OptWfRel.weaken (splitTail_mem hdr contMasks hpMem)
                  (someVarsToOpt_optWfRel _ _)) (OptWfRel.weaken hG'sub hG))
                ((hb (j₁, ()) (j₂, ())).get .here (someVarsToOpt (splitTail hdr contMasks p₁))
                  (someVarsToOpt (splitTail hdr contMasks p₂)))
              exact rewriteRotWith_wf allow' contP hG_peel (hj _ p₁ p₂ hG'sub hpMem) hpeel
            dsimp only [rotGrp]; cases isPartialMasks hdr contMasks with
            | false =>
              simp only [Bool.false_eq_true, ite_false]
              exact .group (fun (J₁, ()) (J₂, ()) => WfB.cons (fun p₁ p₂ => mkB allowHdr _ _
                (fun _ _ _ hG' _ q hq => by
                  have hsub : ∀ q ∈ D_out, q ∈ ⟨rotSig hdr contMasks ts, J₁, J₂⟩ :: D_out :=
                    fun _ h => List.mem_cons_of_mem _ h
                  rcases List.mem_cons.1 hq with rfl | hq
                  · exact .expand fun hG'' hD'' => hmk J₁ J₂ (fun _ h => hG'' _ (hG' _ h))
                      (fun _ h => hD'' _ (hsub _ h)) (hD'' _ List.mem_cons_self)
                  · exact RotLRel.weaken hG' hsub hDx q hq) p₁ p₂) .nil)
                (fun (J₁, ()) (J₂, ()) =>
                  mkK J₁ J₂ (fun _ h => List.mem_cons_of_mem _ h) List.mem_cons_self)
            | true =>
              simp only [ite_true]
              let hsub {J₁ : L₁ (rotSig hdr contMasks ts)} {J₂ : L₂ (rotSig hdr contMasks ts)}
                  {H₁ : L₁ ts} {H₂ : L₂ ts} : ∀ q ∈ D_out,
                  q ∈ ⟨rotSig hdr contMasks ts, J₁, J₂⟩ :: ⟨ts, H₁, H₂⟩ :: D_out :=
                fun _ h => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)
              exact .group (fun (J₁, H₁, ()) (J₂, H₂, ()) => WfB.cons (fun p₁ p₂ => mkB true _ _
                (fun _ _ _ hG' _ q hq => by
                  rcases List.mem_cons.1 hq with rfl | hq
                  · exact .expandOrKeep (List.mem_cons_of_mem _ List.mem_cons_self)
                      fun hG'' hD'' => hmk J₁ J₂ (fun _ h => hG'' _ (hG' _ h))
                        (fun _ h => hD'' _ (hsub _ h)) (hD'' _ List.mem_cons_self)
                  · exact RotLRel.weaken hG' hsub hDx q hq) p₁ p₂)
                (WfB.cons (fun hp₁ hp₂ => hmk J₁ J₂ (fun _ h => List.mem_append_right _ h) hsub
                  List.mem_cons_self _ _ ((toArgTup_trel hp₁ hp₂).argRel_weaken fun _ h =>
                    List.mem_append_left _ h)) .nil))
                (fun (J₁, _, ()) (J₂, _, ()) => mkK J₁ J₂ hsub List.mem_cons_self)
          cases exitMode with
          | inline =>
            dsimp only [rewriteRotWith]
            let mk {V L} (bs : Tup (RotL V L rs) [ts] → Blocks (OptArg V) (RotL V L rs) rs [ts])
                (J : L _) (args : Tup (Arg V) ts) := hdrEmit (tailC := ts) (tailX := ts) dir args
              args hdr contMasks [] ((bs (exitLabels ts)).get .here (someArgsToOpt args))
              (fun rotArgs => .jump J rotArgs) (fun ex _ => rewriteRotWith allowHdr exitP ex)
            refine emitLoop (fun _ h => h) (mk bs₁) (mk bs₂) fun _ _ hGsub hDsub hRotMem _ _ ha =>
              hdrEmit_wf dir hdr contMasks [] (CtxPred.append (someArgsToOpt_optWfRel ha)
                (OptWfRel.weaken hGsub hG)) (CtxPred.append (exitLabels_rel ts) (RotLRel.weaken
                hGsub hDsub hD)) ((hb (exitLabels ts) (exitLabels ts)).get .here _ _) ha ha
                (@fun _ _ _ _ hrot => Wf.jump hRotMem hrot)
                (@fun _ _ _ _ hGx hDx _ _ hex _ _ _ => rewriteRotWith_wf allowHdr exitP hGx hDx hex)
          | wrap xsMask hMasks =>
            dsimp only [rewriteRotWith]
            refine .group (fun (J_exit₁, ()) (J_exit₂, ()) => WfB.cons (fun x₁ x₂ => ?_) .nil)
              (fun (J_exit₁, ()) (J_exit₂, ()) => ?_)
            · let G'' := Tup.zip x₁ x₂ ++ G'
              have hG'sub : ∀ q ∈ G', q ∈ G'' := fun _ hq => List.mem_append_right _ hq
              have hxMem : ∀ q ∈ Tup.zip x₁ x₂, q ∈ G'' := fun _ hq => List.mem_append_left _ hq
              obtain ⟨_, hG_peel, hpeel⟩ := hdrPeel_wf dir false hdr hMasks hxMem (CtxPred.append
                (tupWiden_optWfRel ts xsMask (splitTail_mem hdr hMasks hxMem)) (OptWfRel.weaken
                hG'sub hG)) ((hb (exitLabels ts) (exitLabels ts)).get .here (tupWiden ts xsMask
                (splitTail hdr hMasks x₁)) (tupWiden ts xsMask (splitTail hdr hMasks x₂)))
              exact rewriteRotWith_wf allowHdr exitP hG_peel (CtxPred.append (exitLabels_rel ts)
                (RotLRel.weaken hG'sub (fun _ hq => List.mem_append_right _ hq) hD)) hpeel
            · have hDexSub :
                  ∀ q ∈ D', q ∈ ⟨exitSig hdr hMasks xsMask ts, J_exit₁, J_exit₂⟩ :: D' :=
                fun _ hq => List.mem_cons_of_mem _ hq
              let mk {V L} (bs : Tup (RotL V L rs) [ts] → Blocks (OptArg V) (RotL V L rs) rs [ts])
                  (Jx : L _) (J : L _) (args : Tup (Arg V) ts) := hdrEmit (tailC := ts)
                (tailX := filterTys ts xsMask) dir args (tupSelectArgs ts xsMask args) hdr
                contMasks hMasks ((bs (exitLabels ts)).get .here (someArgsToOpt args))
                (fun rotArgs => .jump J rotArgs) (fun _ exArgs => .jump Jx exArgs)
              refine emitLoop hDexSub (mk bs₁ J_exit₁) (mk bs₂ J_exit₂) fun _ _ hGsub hDsub
                  hRotMem _ _ ha => hdrEmit_wf dir hdr contMasks hMasks (CtxPred.append
                  (someArgsToOpt_optWfRel ha) (OptWfRel.weaken hGsub hG)) (CtxPred.append
                  (exitLabels_rel ts) (RotLRel.weaken hGsub (fun _ h => hDsub _ (hDexSub _ h)) hD))
                ((hb (exitLabels ts) (exitLabels ts)).get .here _ _) ha (tupSelectArgs_argRel ts
                xsMask ha) (@fun _ _ _ _ hrot => Wf.jump hRotMem hrot)
                (@fun _ _ _ _ _ _ _ _ _ _ _ hex => Wf.jump (hDsub _ List.mem_cons_self) hex)
    | _ => dsimp only [rewriteRotWith]; exact .hlt
where
  rewriteKeepB_wf : (allowHdr : Bool) → (ps : List RotPlan) →
      ∀ {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty} {G' : Ctx V₁ V₂}
        {D' : Ctx L₁ L₂} {G : Ctx (OptArg V₁) (OptArg V₂)}
        {D : Ctx (RotL V₁ L₁ rs) (RotL V₂ L₂ rs)} {sig : List (List Ty)}
        {bs₁ : Blocks (OptArg V₁) (RotL V₁ L₁ rs) rs sig}
        {bs₂ : Blocks (OptArg V₂) (RotL V₂ L₂ rs) rs sig}, OptWfRel G' G → RotLRel G' D' D →
        WfB G D bs₁ bs₂ → WfB G' D' (rewriteRotWith.rewriteKeepB allowHdr ps bs₁)
          (rewriteRotWith.rewriteKeepB allowHdr ps bs₂)
    | allowHdr, [] => fun hG hD hbs => by
      cases hbs with
      | nil => dsimp only [rewriteRotWith.rewriteKeepB, flatExpr.flatBlocks]; exact .nil
      | cons hb hbs' =>
        dsimp only [rewriteRotWith.rewriteKeepB, flatExpr.flatBlocks]
        refine .cons (fun xs₁ xs₂ => ?_) (rewriteKeepB_wf allowHdr [] hG hD hbs')
        exact flatExpr_wf (hb (someVarsToOpt xs₁) (someVarsToOpt xs₂))
          (OptWfRel.append_someVars hG xs₁ xs₂)
          (RotLRel.weaken (fun _ hp => List.mem_append_right _ hp) (fun _ h => h) hD)
    | allowHdr, p :: ps => fun hG hD hbs => by
      cases hbs with
      | nil => dsimp only [rewriteRotWith.rewriteKeepB]; exact .nil
      | cons hb hbs' =>
        dsimp only [rewriteRotWith.rewriteKeepB]
        refine .cons (fun xs₁ xs₂ => ?_) (rewriteKeepB_wf allowHdr ps hG hD hbs')
        exact rewriteRotWith_wf allowHdr p (OptWfRel.append_someVars hG xs₁ xs₂)
          (RotLRel.weaken (fun _ hp => List.mem_append_right _ hp) (fun _ h => h) hD)
          (hb (someVarsToOpt xs₁) (someVarsToOpt xs₂))
end

private theorem rewriteRot_wf (plan : RotPlan) {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type}
    {rs : List Ty} {G' : Ctx V₁ V₂} {D' : Ctx L₁ L₂} {G : Ctx (OptArg V₁) (OptArg V₂)}
    {D : Ctx (RotL V₁ L₁ rs) (RotL V₂ L₂ rs)} {e₁ : Expr (OptArg V₁) (RotL V₁ L₁ rs) rs}
    {e₂ : Expr (OptArg V₂) (RotL V₂ L₂ rs) rs} (hG : OptWfRel G' G) (hD : RotLRel G' D' D)
    (hwf : Wf G D e₁ e₂) : Wf G' D' (rewriteRot plan e₁) (rewriteRot plan e₂) :=
  rewriteRotWith_wf false plan hG hD hwf

/-! ## Weakest-precondition invariants (`NoneDeadOpt`, `SomeValEq`, `ValidDk`, `RotWpD`) -/

/-- Whether a `RotL` label is live (not `.dead`). -/
private def rotLIsLive {V : Ty → Type} {L : List Ty → Type} {rs ts : List Ty} :
    RotL V L rs ts → Bool
  | .dead => false | _ => true

/-- Every `true` label in `Dk` pairs with a live (`keep` or `expand`) `RotL` label. -/
private abbrev ValidDk {rs : List Ty} (Dk : Ctx BoolL (RotL Val Cont rs)) : Prop :=
  CtxPred (fun _ b j => b = true → rotLIsLive j = true) Dk

private theorem validDk_wrapKeepLabels {rs : List Ty} :
    {sig : List (List Ty)} → (Js : Tup Cont sig) →
    ValidDk (Tup.zip (trueLabels sig) (wrapKeepLabels (V := Val) (rs := rs) Js))
  | [], () => CtxPred.nil _
  | _ :: _, (_, Js) => CtxPred.cons (fun _ => rfl) (validDk_wrapKeepLabels Js)

/-- Every dropped (`none`) binder level in `Gk` is absent from liveness trie `s`. -/
private abbrev NoneDeadOpt {V : Ty → Type} (s : Trie Unit) (Gk : Ctx K (OptArg V)) : Prop :=
  CtxPred (fun _ k o => o = none → (s.find? k).isSome = false) Gk

private theorem NoneDeadOpt.sub {V : Ty → Type} {s₁ s₂ : Trie Unit} {Gk : Ctx K (OptArg V)}
    (hsub : TrieSub s₁ s₂) (hnd : NoneDeadOpt s₂ Gk) : NoneDeadOpt s₁ Gk :=
  CtxPred.mono (fun h ho => Bool.eq_false_iff.mpr fun hm => by
    have h2 := hsub _ hm; rw [h ho] at h2; cases h2) hnd

private theorem NoneDeadOpt.cons_some {V : Ty → Type} {s : Trie Unit} {Gk : Ctx K (OptArg V)}
    (hnd : NoneDeadOpt s Gk) {t : Ty} (k : Nat) (a : Arg V t) :
    NoneDeadOpt s (⟨t, k, some a⟩ :: Gk) := CtxPred.cons (fun h => by cases h) hnd

private theorem NoneDeadOpt.append_some {V : Ty → Type} {s : Trie Unit} {Gk : Ctx K (OptArg V)}
    (hnd : NoneDeadOpt s Gk) : {ts : List Ty} → (ks : Tup K ts) → (as : Tup (Arg V) ts) →
    NoneDeadOpt s (Tup.zip ks (someArgsToOpt as) ++ Gk)
  | [], (), () => hnd
  | _ :: _, (k, ks), (a, as) => (NoneDeadOpt.append_some hnd ks as).cons_some k a

private theorem NoneDeadOpt.append_someVars {V : Ty → Type} {s : Trie Unit} {Gk : Ctx K (OptArg V)}
    (hnd : NoneDeadOpt s Gk) : {ts : List Ty} → (ks : Tup K ts) → (xs : Tup V ts) →
    NoneDeadOpt s (Tup.zip ks (someVarsToOpt xs) ++ Gk)
  | [], (), () => hnd
  | _ :: _, (k, ks), (x, xs) => (NoneDeadOpt.append_someVars hnd ks xs).cons_some k (.var x)

private theorem checkDeadMask_noneDeadOpt {lvl : Nat} {s : Trie Unit} {Gk : Ctx K (OptArg Val)} :
    (ts : List Ty) → (bs : List Bool) → checkDeadMask lvl s ts bs = true →
    ∀ ys : Tup Val (filterTys ts bs),
      NoneDeadOpt s Gk → NoneDeadOpt s (Tup.zip (Tup.levels ts lvl) (tupWiden ts bs ys) ++ Gk)
  | [], _, _, _, hnd => hnd
  | _ :: ts, [], hchk, ys, hnd => by
    simp only [checkDeadMask, List.headD, List.tail, Bool.and_eq_true] at hchk
    let p : Val _ × _ := ys; rw [tupWiden_nil_eq ys p.1 p.2 rfl]
    exact (checkDeadMask_noneDeadOpt ts [] hchk.2 p.2 hnd).cons_some lvl (.var p.1)
  | _ :: ts, true :: bs, hchk, ys, hnd => by
    simp only [checkDeadMask, List.headD, List.tail, Bool.and_eq_true] at hchk
    let p : Val _ × _ := ys; rw [tupWiden_true_eq ys p.1 p.2 rfl]
    exact (checkDeadMask_noneDeadOpt ts bs hchk.2 p.2 hnd).cons_some lvl (.var p.1)
  | _ :: ts, false :: bs, hchk, ys, hnd => by
    simp only [checkDeadMask, List.headD, List.tail, Bool.and_eq_true] at hchk
    let p : Tup Val _ := ys; rw [tupWiden_false_eq ys p rfl]
    exact CtxPred.cons (fun _ => by simpa [Tup.levels] using hchk.1)
      (checkDeadMask_noneDeadOpt ts bs hchk.2 p hnd)

/-- Every kept (`some a`) binder in `G` agrees in semantic value with its paired `Val`. -/
private abbrev SomeValEq (G : Ctx (OptArg Val) Val) : Prop :=
  SomeValCtx (fun _ a v => a.val = v) G

private theorem SomeValEq.append_someVars {G : Ctx (OptArg Val) Val} (hG : SomeValEq G) :
    {ts : List Ty} → (xs : Tup Val ts) → SomeValEq (Tup.zip (someVarsToOpt xs) xs ++ G)
  | [], () => hG
  | _ :: _, (_, xs) => SomeValCtx.cons_some rfl (SomeValEq.append_someVars hG xs)

private theorem SomeValEq.append_someArgs {G : Ctx (OptArg Val) Val} (hG : SomeValEq G) :
    {ts : List Ty} → {args : Tup (Arg Val) ts} → {xs : Tup Val ts} →
    vals args = xs → SomeValEq (Tup.zip (someArgsToOpt args) xs ++ G)
  | [], (), (), _ => hG
  | _ :: _, (_, _), (_, _), h => by
    simp only [vals, Prod.mk.injEq] at h
    exact SomeValCtx.cons_some h.1 (SomeValEq.append_someArgs hG h.2)

private theorem SomeValEq.append_tupWiden_tupSelectVals {G : Ctx (OptArg Val) Val}
    (hG : SomeValEq G) : (ts : List Ty) → (bs : List Bool) → {ys xs : Tup Val ts} → ys = xs →
    SomeValEq (Tup.zip (tupWiden ts bs (tupSelectVals ts bs ys)) xs ++ G)
  | [], _, (), (), _ => hG
  | _ :: ts, [], (y, _), (_, _), h => by
    simp only [Prod.mk.injEq] at h; rw [tupWiden_nil_eq _ _ _ (tupSelectVals_nil_mask y _)]
    exact SomeValCtx.cons_some (a := .var y) h.1
      (SomeValEq.append_tupWiden_tupSelectVals hG ts [] h.2)
  | _ :: ts, true :: bs, (y, _), (_, _), h => by
    simp only [Prod.mk.injEq] at h; rw [tupWiden_true_eq _ _ _ (tupSelectVals_true y _)]
    exact SomeValCtx.cons_some (a := .var y) h.1
      (SomeValEq.append_tupWiden_tupSelectVals hG ts bs h.2)
  | _ :: ts, false :: bs, (_, _), (_, _), h => by
    simp only [Prod.mk.injEq] at h; rw [tupWiden_false_eq _ _ (tupSelectVals_false _ _)]
    exact SomeValCtx.cons_none (SomeValEq.append_tupWiden_tupSelectVals hG ts bs h.2)

private theorem flatOptArg_val_of_inSet {s : Trie Unit} {Gk : Ctx K (OptArg Val)}
    {G : Ctx (OptArg Val) Val} (hnd : NoneDeadOpt s Gk) (hG : SomeValEq G)
    {t : Ty} {ak : Arg K t} {a₁ : Arg (OptArg Val) t} {a₂ : Arg Val t}
    (hk : ArgRel Gk t ak a₁) (h12 : ArgRel G t a₁ a₂) (hin : ak.InSet s) :
    (flatOptArg a₁).val = a₂.val := by
  cases h12 with
  | imm _ => rfl
  | var hm12 =>
    cases hk with | var hmk =>
    rename_i o _ k; cases o with
    | some _ => exact CtxPred.mem hG hm12 _ rfl
    | none =>
      have hfalse := CtxPred.mem hnd hmk rfl; have hkmem : (s.find? k).isSome = true := hin
      rw [hfalse] at hkmem; cases hkmem

private theorem flatOptArgs_vals_of_inSet {s : Trie Unit} {Gk : Ctx K (OptArg Val)}
    {G : Ctx (OptArg Val) Val} (hnd : NoneDeadOpt s Gk) (hG : SomeValEq G) : {ts : List Ty} →
    {aks : Tup (Arg K) ts} → {as₁ : Tup (Arg (OptArg Val)) ts} → {as₂ : Tup (Arg Val) ts} →
    TRel (ArgRel Gk) aks as₁ → TRel (ArgRel G) as₁ as₂ → ArgsInSet s aks →
    vals (flatOptArgs as₁) = vals as₂
  | [], (), (), (), .nil, .nil, _ => rfl
  | _ :: _, (_, _), (_, _), (_, _), .cons hka hkas, .cons h12a h12as, ⟨ha, has⟩ =>
    Prod.ext (flatOptArg_val_of_inSet hnd hG hka h12a ha)
      (flatOptArgs_vals_of_inSet hnd hG hkas h12as has)

/-- Weakest-precondition invariant relating `RotL Val Cont rs` labels to source `Cont`s. -/
private abbrev RotWpD (Γ : Env) {rs : List Ty} (Q : Post rs) (X : XPost)
    (D : Ctx (RotL Val Cont rs) Cont) : Prop :=
  CtxPred (fun _ l J => match l with
    | .keep J' => J' = J
    | .dead => True
    | .expand f => ∀ (args : Tup (Arg Val) _) (m : Mem 64), J (vals args) m → wp Γ Q X (f args) m
    | .expandOrKeep f lHdr =>
        (∀ (args : Tup (Arg Val) _) (m : Mem 64), J (vals args) m → wp Γ Q X (f args) m) ∧
        (∀ vs (m : Mem 64), J vs m → lHdr vs m)) D

private theorem rotWpD_wrapKeepLabels (Γ : Env) {rs : List Ty} (Q : Post rs) (X : XPost) :
    {sig : List (List Ty)} → (Js : Tup Cont sig) →
    RotWpD Γ Q X (Tup.zip (wrapKeepLabels (V := Val) (rs := rs) Js) Js)
  | [], () => CtxPred.nil _
  | _ :: _, (_, Js) => CtxPred.cons rfl (rotWpD_wrapKeepLabels Γ Q X Js)

/-- Diagonal invariant on `K`-to-`K` relational contexts used to relate `bs true` and `bs false`. -/
private abbrev DiagK (Gk : Ctx K K) : Prop := DiagCtx Gk

private theorem validateLeafB_get {rs : List Ty} :
    {sig : List (List Ty)} → {bsk : Blocks K BoolL rs sig} → {nv : Nat} → {sb : Trie Unit} →
    validateLeaf.validateLeafB bsk nv = some sb → ∀ {ts} (i : Member ts sig),
      ∃ s_i, validateLeaf (bsk.get i (Tup.levels ts nv)) (nv + ts.length) = some s_i ∧
        TrieSub s_i sb
  | _, .cons _ _, _, _, hval, _, .here => by
    dsimp only [validateLeaf.validateLeafB] at hval
    rcases Option.bind_eq_some_iff.1 hval with ⟨s₁, hs₁, hr⟩
    rcases Option.bind_eq_some_iff.1 hr with ⟨s₂, _, ⟨⟩⟩; exact ⟨s₁, hs₁, TrieSub.union_left s₁ s₂⟩
  | _, .cons _ _, _, _, hval, _, .there i => by
    dsimp only [validateLeaf.validateLeafB] at hval
    rcases Option.bind_eq_some_iff.1 hval with ⟨s₁, _, hr⟩
    rcases Option.bind_eq_some_iff.1 hr with ⟨s₂, hs₂, ⟨⟩⟩
    obtain ⟨si, hsi, hsub⟩ := validateLeafB_get hs₂ i
    exact ⟨si, hsi, hsub.trans (TrieSub.union_right s₁ s₂)⟩

private theorem validateHdr_diag_eq {rs : List Ty} : (hdr : HdrPlan) → {nv : Nat} → {Gk : Ctx K K} →
    {Dk : Ctx BoolL BoolL} → {ek₁ ek₂ : Expr K BoolL rs} → DiagK Gk → Wf Gk Dk ek₁ ek₂ →
    {sh₁ sh₂ : Trie Unit} → {armT₁ armE₁ armT₂ armE₂ : Expr K BoolL rs} → {nv₁ nv₂ : Nat} →
    validateHdr hdr ek₁ nv = some (sh₁, armT₁, armE₁, nv₁) →
    validateHdr hdr ek₂ nv = some (sh₂, armT₂, armE₂, nv₂) →
    sh₁ = sh₂ ∧ nv₁ = nv₂ ∧ ∃ Gk', DiagK Gk' ∧ Wf Gk' Dk armT₁ armT₂ ∧ Wf Gk' Dk armE₁ armE₂
  | [], _, Gk, _, _, _, hdiag, hwf, _, _, _, _, _, _, _, _, h1, h2 => by
    cases hwf with
    | jnz hc ht he =>
      dsimp only [validateHdr] at h1 h2; simp only [pure, Option.some.injEq, Prod.mk.injEq] at h1 h2
      rcases h1 with ⟨rfl, rfl, rfl, rfl⟩; rcases h2 with ⟨rfl, rfl, rfl, rfl⟩
      rw [hdiag.argRel_eq hc]; exact ⟨rfl, rfl, Gk, hdiag, ht, he⟩
    | _ => dsimp only [validateHdr] at h1; cases h1
  | .let_ dts :: ss, nv, _, _, _, _, hdiag, hwf, _, _, _, _, _, _, _, _, h1, h2 => by
    cases hwf with
    | @let_ _ _ dts' _ _ _ _ hop hk =>
      dsimp only [validateHdr] at h1 h2
      cases hdec : tysDecEq dts dts' with
      | isFalse => simp [hdec] at h1
      | isTrue heq =>
        subst heq; simp only [tysDecEq_self_isTrue dts] at h1 h2
        rcases Option.bind_eq_some_iff.1 h1 with ⟨⟨_, _, _, _⟩, h1', ⟨⟩⟩
        rcases Option.bind_eq_some_iff.1 h2 with ⟨⟨_, _, _, _⟩, h2', ⟨⟩⟩
        cases hop with | mk _ hargs =>
        obtain ⟨rfl, rfl, Gk', hdiag', ht', he'⟩ := validateHdr_diag_eq ss
          (DiagCtx.append (DiagCtx.zip_self (Tup.levels dts nv)) hdiag) (hk _ _) h1' h2'
        rw [hdiag.trel_eq hargs]; exact ⟨rfl, rfl, Gk', hdiag', ht', he'⟩
    | _ => dsimp only [validateHdr] at h1; cases h1
  | .load t :: ss, nv, _, _, _, _, hdiag, hwf, _, _, _, _, _, _, _, _, h1, h2 => by
    cases hwf with
    | @load _ _ t' _ _ _ _ ha hk =>
      dsimp only [validateHdr] at h1 h2
      cases hdec : tyDecEq t t' with
      | isFalse => simp [hdec] at h1
      | isTrue heq =>
        subst heq; simp only [tyDecEq_self_isTrue t] at h1 h2
        rcases Option.bind_eq_some_iff.1 h1 with ⟨⟨_, _, _, _⟩, h1', ⟨⟩⟩
        rcases Option.bind_eq_some_iff.1 h2 with ⟨⟨_, _, _, _⟩, h2', ⟨⟩⟩
        obtain ⟨rfl, rfl, Gk', hdiag', ht', he'⟩ :=
          validateHdr_diag_eq ss hdiag.cons (hk nv nv) h1' h2'
        rw [hdiag.argRel_eq ha]; exact ⟨rfl, rfl, Gk', hdiag', ht', he'⟩
    | _ => dsimp only [validateHdr] at h1; cases h1

/-! ## Weakest-precondition soundness (`flatExpr_wp`, `hdrEmit_wp`, `hdrPeel_wf_src`) -/

/-- `flatExpr` preserves `wp` whenever `validateLeaf` succeeds. -/
private theorem flatExpr_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {G : Ctx (OptArg Val) Val} {D : Ctx (RotL Val Cont rs) Cont}
    {e₁ : Expr (OptArg Val) (RotL Val Cont rs) rs} {e₂ : Expr Val Cont rs} (hwf : Wf G D e₁ e₂) :
    ∀ {Gk : Ctx K (OptArg Val)} {Dk : Ctx BoolL (RotL Val Cont rs)} {ek : Expr K BoolL rs}
      {nv : Nat} {s : Trie Unit}, Wf Gk Dk ek e₁ → validateLeaf ek nv = some s →
      NoneDeadOpt s Gk → SomeValEq G → ValidDk Dk → RotWpD Γ Q X D →
      ∀ m, wp Γ Q X e₂ m → wp Γ Q X (flatExpr e₁) m := by
  induction hwf using Wf.induct with
  | let_ hop _ ih =>
    intro _ _ _ _ _ hwk hval hnd hG hDk hD m hw2
    rcases hwk.rhs_let with ⟨_, _, rfl, hopk, hkk⟩; dsimp only [validateLeaf] at hval
    rcases Option.bind_eq_some_iff.1 hval with ⟨sk, hvk, ⟨⟩⟩
    cases hop with | mk code hargs => cases hopk with | mk _ hargsk =>
    dsimp only [flatExpr]; simp only [flatOptOp, wp, Op.wp] at hw2 ⊢
    rw [flatOptArgs_vals_of_inSet hnd hG hargsk hargs (ArgsInSet.addArgKeys _ _)]
    exact OpCode.wp_mono code _ (fun r hr => ih _ r (hkk _ _) hvk (NoneDeadOpt.append_someVars
      (NoneDeadOpt.sub (TrieSub.addArgKeys _ _) hnd) _ _) (SomeValEq.append_someVars hG r)
      hDk hD m hr) hw2
  | load t ha _ ih =>
    intro _ _ _ _ _ hwk hval hnd hG hDk hD m ⟨v, hv, hw2⟩
    rcases hwk.rhs_load with ⟨_, _, rfl, hak, hkk⟩; dsimp only [validateLeaf] at hval
    rcases Option.bind_eq_some_iff.1 hval with ⟨sk, hvk, ⟨⟩⟩; dsimp only [flatExpr]; simp only [wp]
    rw [flatOptArg_val_of_inSet hnd hG hak ha (Arg.InSet.addArgKey _ _)]
    exact ⟨v, hv, ih _ v (hkk _ _) hvk (NoneDeadOpt.cons_some (NoneDeadOpt.sub
      (TrieSub.addArgKey _ _) hnd) _ (.var v)) (SomeValCtx.cons_some (a := .var v) rfl hG)
      hDk hD m hw2⟩
  | store hv ha _ ih =>
    intro _ _ _ _ _ hwk hval hnd hG hDk hD _ ⟨hok, hw2⟩
    rcases hwk.rhs_store with ⟨vk, ak, _, rfl, hvk, hak, hkk⟩; dsimp only [validateLeaf] at hval
    rcases Option.bind_eq_some_iff.1 hval with ⟨sk, hvk', ⟨⟩⟩; dsimp only [flatExpr]; simp only [wp]
    rw [flatOptArg_val_of_inSet hnd hG hvk hv (Arg.InSet.addArgKey _ _), flatOptArg_val_of_inSet
      hnd hG hak ha ((Arg.InSet.addArgKey _ _).mono (TrieSub.addArgKey _ _))]
    exact ⟨hok, ih hkk hvk' (NoneDeadOpt.sub
      ((TrieSub.addArgKey ak sk).trans (TrieSub.addArgKey vk _)) hnd) hG hDk hD _ hw2⟩
  | call f hargs _ ih =>
    intro _ _ _ _ _ hwk hval hnd hG hDk hD _ ⟨P, E, hΓ, hP, hE⟩
    rcases hwk.rhs_call with ⟨argsk, _, rfl, hargsk, hkk⟩; dsimp only [validateLeaf] at hval
    rcases Option.bind_eq_some_iff.1 hval with ⟨sk, hvk, ⟨⟩⟩; dsimp only [flatExpr]; simp only [wp]
    rw [flatOptArgs_vals_of_inSet hnd hG hargsk hargs (ArgsInSet.addArgKeys _ _)]
    exact ⟨P, E, hΓ, fun r m' hp => ih _ r (hkk _ _) hvk (NoneDeadOpt.append_someVars
      (NoneDeadOpt.sub (TrieSub.addArgKeys argsk sk) hnd) _ _) (SomeValEq.append_someVars hG r)
      hDk hD m' (hP r m' hp), hE⟩
  | jnz hc _ _ iht ihe =>
    intro _ _ _ _ _ hwk hval hnd hG hDk hD m hw2
    rcases hwk.rhs_jnz with ⟨ck, _, _, rfl, hck, htk, hek⟩; dsimp only [validateLeaf] at hval
    rcases Option.bind_eq_some_iff.1 hval with ⟨st, hvt, hr⟩
    rcases Option.bind_eq_some_iff.1 hr with ⟨se, hve, ⟨⟩⟩
    dsimp only [flatExpr]; simp only [wp] at hw2 ⊢
    rw [flatOptArg_val_of_inSet hnd hG hck hc (Arg.InSet.addArgKey _ _)]
    exact ⟨fun h => iht htk hvt (NoneDeadOpt.sub ((TrieSub.union_left st se).trans
        (TrieSub.addArgKey ck _)) hnd) hG hDk hD m (hw2.1 h), fun h => ihe hek hve
      (NoneDeadOpt.sub ((TrieSub.union_right st se).trans (TrieSub.addArgKey ck _)) hnd)
      hG hDk hD m (hw2.2 h)⟩
  | @jump _ _ _ j₁ _ _ _ hj hargs =>
    intro _ _ _ _ _ hwk hval hnd hG hDk hD m hw2
    rcases hwk.rhs_jump with ⟨lb, argsk, rfl, hjk, hargsk⟩; dsimp only [validateLeaf] at hval
    cases hlb : lb with
    | false => simp [hlb] at hval
    | true =>
      simp only [hlb, ↓reduceIte, pure, Option.some.injEq] at hval; subst hval
      have hlive : rotLIsLive j₁ = true := CtxPred.mem hDk hjk hlb
      have hvals := flatOptArgs_vals_of_inSet hnd hG hargsk hargs (ArgsInSet.addArgKeys _ _)
      have hd := CtxPred.mem hD hj
      cases j₁ with
      | keep J => dsimp only [flatExpr]; simp only [wp] at hw2 ⊢; rw [hvals, hd]; exact hw2
      | dead => simp [rotLIsLive] at hlive
      | expand fn => dsimp only [flatExpr]; exact hd _ m (hvals ▸ hw2)
      | expandOrKeep fn _ => dsimp only [flatExpr]; exact hd.1 _ m (hvals ▸ hw2)
  | ret hvs =>
    intro _ _ _ _ _ hwk hval hnd hG _ _ _ hw2
    rcases hwk.rhs_ret with ⟨vsk, rfl, hvsk⟩; dsimp only [validateLeaf] at hval
    simp only [pure, Option.some.injEq] at hval; subst hval; dsimp only [flatExpr]
    simp only [wp] at hw2 ⊢
    rwa [flatOptArgs_vals_of_inSet hnd hG hvsk hvs (ArgsInSet.addArgKeys _ _)]
  | exit f hargs =>
    intro _ _ _ _ _ hwk hval hnd hG _ _ _ hw2
    rcases hwk.rhs_exit with ⟨argsk, rfl, hargsk⟩; dsimp only [validateLeaf] at hval
    simp only [pure, Option.some.injEq] at hval; subst hval; dsimp only [flatExpr]
    simp only [wp] at hw2 ⊢
    rwa [flatOptArgs_vals_of_inSet hnd hG hargsk hargs (ArgsInSet.addArgKeys _ _)]
  | hlt => intro _ _ _ _ _ hwk _ _ _ _ _ _ hw2; rcases hwk.rhs_hlt with rfl; exact hw2
  | @group _ _ sig _ b₂ _ _ _ _ ihb ihk =>
    intro _ _ _ nv _ hwk hval hnd hG hDk hD m hw2
    rcases hwk.rhs_group with ⟨bk, kk, rfl, hbk, hkk⟩; dsimp only [validateLeaf] at hval
    rcases Option.bind_eq_some_iff.1 hval with ⟨sb, hvb, hr⟩
    rcases Option.bind_eq_some_iff.1 hr with ⟨sk, hvk, ⟨⟩⟩
    dsimp only [flatExpr]; simp only [wp]; intro Js_out hcl_out
    have hDk' := CtxPred.append (validDk_wrapKeepLabels Js_out) hDk
    have hD' := CtxPred.append (rotWpD_wrapKeepLabels Γ Q X Js_out) hD
    have hcl₂ : Closed Γ Q X (b₂ Js_out) Js_out := by
      rw [closed_iff] at hcl_out ⊢; intro ts i xs m' hw; simp only [flatBlocks_get] at hcl_out
      obtain ⟨si, hsi, hsubi⟩ := validateLeafB_get hvb i
      exact hcl_out i xs m' (ihb (wrapKeepLabels Js_out) Js_out i _ xs
        ((hbk (trueLabels sig) _).get i (Tup.levels ts nv) _) hsi (NoneDeadOpt.append_someVars
          (NoneDeadOpt.sub hsubi (NoneDeadOpt.sub (TrieSub.union_left sb sk) hnd)) _ _)
        (SomeValEq.append_someVars hG xs) hDk' hD' m' hw)
    exact ihk (wrapKeepLabels Js_out) Js_out (hkk (trueLabels sig) _) hvk
      (NoneDeadOpt.sub (TrieSub.union_right sb sk) hnd) hG hDk' hD' m (hw2 Js_out hcl₂)

/-- Step down header `hdr` using `hv`, returning the chosen post-`.jnz` arm. -/
private def hdrSrcBranch {rs : List Ty} (dir wantCont : Bool) :
    (hdr : HdrPlan) → HdrVals hdr → Expr Val Cont rs → Option (Expr Val Cont rs)
  | [], (), .jnz _ armT armE => some (if wantCont == dir then armT else armE)
  | .let_ dts :: ss, (ys, rest), .let_ (ts := dts') _ k => match tysDecEq dts dts' with
    | isTrue h => hdrSrcBranch dir wantCont ss rest (k (h ▸ ys)) | isFalse _ => none
  | .load t :: ss, (y, rest), .load t' _ k => match tyDecEq t t' with
    | isTrue h => hdrSrcBranch dir wantCont ss rest (k (h ▸ y.1)) | isFalse _ => none
  | _, _, _ => none

private theorem hdrEmit_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} (dir : Bool)
    {tailC tailX : List Ty} : (hdr : HdrPlan) → (cMs xMs : List (List Bool)) → {nv : Nat} →
    {Gk : Ctx K (OptArg Val)} → {Gk_diag : Ctx K K} → {Dk : Ctx BoolL (RotL Val Cont rs)} →
    {Dk_diag : Ctx BoolL BoolL} → {G : Ctx (OptArg Val) Val} → {D : Ctx (RotL Val Cont rs) Cont} →
    {ek : Expr K BoolL rs} → {e_emit : Expr (OptArg Val) (RotL Val Cont rs) rs} →
    {e_src : Expr Val Cont rs} → {sh : Trie Unit} → {armTk armEk : Expr K BoolL rs} →
    {nv' : Nat} → validateHdr hdr ek nv = some (sh, armTk, armEk, nv') →
    Wf Gk Dk ek e_emit → Wf Gk_diag Dk_diag ek ek → Wf G D e_emit e_src →
    NoneDeadOpt sh Gk → SomeValEq G → DiagK Gk_diag →
    {tc_args : Tup (Arg Val) tailC} → {tc_vals : Tup Val tailC} → {tx_args : Tup (Arg Val) tailX} →
    {tx_vals : Tup Val tailX} → vals tc_args = tc_vals → vals tx_args = tx_vals →
    {kC : Tup (Arg Val) (stepMasksSig hdr cMs tailC) → Expr Val Cont rs} →
    {kX : Expr (OptArg Val) (RotL Val Cont rs) rs →
      Tup (Arg Val) (stepMasksSig hdr xMs tailX) → Expr Val Cont rs} →
    {m₀ : Mem 64} → wp Γ Q X e_src m₀ →
    (∀ hv m' armC_src (rotArgs : Tup (Arg Val) (stepMasksSig hdr cMs tailC)),
      hdrSrcBranch dir true hdr hv e_src = some armC_src →
      wp Γ Q X armC_src m' → vals rotArgs = hdrSelect hdr cMs hv tc_vals →
      wp Γ Q X (kC rotArgs) m') →
    (∀ hv m' Gk_leaf Gk_diag_leaf G_leaf armX_emit armX_src
      (exitArgs : Tup (Arg Val) (stepMasksSig hdr xMs tailX)),
      (∀ s, NoneDeadOpt s Gk → NoneDeadOpt s Gk_leaf) →
      SomeValEq G_leaf → DiagK Gk_diag_leaf →
      Wf Gk_leaf Dk (if dir then armEk else armTk) armX_emit →
      Wf Gk_diag_leaf Dk_diag (if dir then armEk else armTk) (if dir then armEk else armTk) →
      Wf G_leaf D armX_emit armX_src → hdrSrcBranch dir false hdr hv e_src = some armX_src →
      wp Γ Q X armX_src m' → vals exitArgs = hdrSelect hdr xMs hv tx_vals →
      wp Γ Q X (kX armX_emit exitArgs) m') →
    wp Γ Q X (hdrEmit dir tc_args tx_args hdr cMs xMs e_emit kC kX) m₀
  | [], _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hval, hwk, hwk_diag, hwf, hnd, hG, hdiag,
      _, _, tx_args, _, htc, htx, _, _, m₀, hw2, hC, hX => by
    cases hwf with
    | @jnz _ _ c₁ _ t₁ t₂ e₁' e₂' hc ht he =>
      rcases hwk.rhs_jnz with ⟨ck, tk, ek', rfl, hck, htk, hek⟩
      rcases hwk_diag.jnz_inv with ⟨_, htkd, hekd⟩; dsimp only [validateHdr] at hval
      simp only [pure, Option.some.injEq, Prod.mk.injEq] at hval
      rcases hval with ⟨rfl, rfl, rfl, rfl⟩; simp only [wp] at hw2
      cases dir <;> dsimp only [hdrEmit] <;>
        (simp only [wp, Bool.false_eq_true, ↓reduceIte]
         rw [flatOptArg_val_of_inSet hnd hG hck hc (Arg.InSet.addArgKey _ _)])
      · exact ⟨fun h => hX () m₀ _ _ _ t₁ t₂ tx_args (fun _ h => h) hG hdiag htk htkd ht
          rfl (hw2.1 h) htx, fun h => hC () m₀ e₂' _ rfl (hw2.2 h) htc⟩
      · exact ⟨fun h => hC () m₀ t₂ _ rfl (hw2.1 h) htc, fun h =>
          hX () m₀ _ _ _ e₁' e₂' tx_args (fun _ h => h) hG hdiag hek hekd he rfl (hw2.2 h) htx⟩
    | _ => cases hwk <;> (dsimp only [validateHdr] at hval; cases hval)
  | .let_ dts :: ss, cMs, xMs, nv, _, _, _, _, _, _, _, _, _, _, _, _, _, hval, hwk, hwk_diag,
      hwf, hnd, hG, hdiag, _, _, _, _, htc, htx, _, _, _, hw2, hC, hX => by
    cases hwf with
    | @let_ _ _ dts' op₁ _ _ _ hop hk =>
      rcases hwk.rhs_let with ⟨opk, kk, rfl, hopk, hkk⟩; rcases hwk_diag.let_inv with ⟨_, hkkd⟩
      dsimp only [validateHdr] at hval
      cases hdec : tysDecEq dts dts' with
      | isFalse => simp [hdec] at hval
      | isTrue heq =>
        subst heq; simp only [tysDecEq_self_isTrue dts] at hval
        rcases Option.bind_eq_some_iff.1 hval with ⟨⟨_, _, _, _⟩, hv', ⟨⟩⟩
        cases hop with | mk code hargs => cases hopk with | mk _ hargsk =>
        dsimp only [hdrEmit]; simp only [tysDecEq_self_isTrue dts, flatOptOp, wp, Op.wp] at hw2 ⊢
        rw [flatOptArgs_vals_of_inSet hnd hG hargsk hargs (ArgsInSet.addArgKeys _ _)]
        refine OpCode.wp_mono code _ (fun ys hys => hdrEmit_wp dir ss cMs.tail xMs.tail
          (nv := nv + dts.length) hv' (hkk _ _) (hkkd _ _) (hk _ ys)
          (NoneDeadOpt.append_someVars (NoneDeadOpt.sub (TrieSub.addArgKeys _ _) hnd) _ _)
          (SomeValEq.append_someVars hG ys) (DiagCtx.append (DiagCtx.zip_self _) hdiag)
          htc htx hys (fun _ _ _ _ hbr hwC hrest => hC (ys, _) _ _
            (tupAppend (tupSelectArgs dts _ (toArgTup ys)) _)
            (by simpa [hdrSrcBranch, tysDecEq_self_isTrue dts] using hbr) hwC
            (by rw [vals_tupAppend, vals_tupSelectArgs, toArgTup_vals, hrest]; rfl))
          fun _ _ _ _ _ _ _ _ hnd_l hG_l hdk_l hwk_l hwkd_l hwf_l hbr hwX hrest => hX (ys, _) _ _
            _ _ _ _ (tupAppend (tupSelectArgs dts _ (toArgTup ys)) _) (fun s hs => hnd_l s
              (NoneDeadOpt.append_someVars hs _ _)) hG_l hdk_l hwk_l hwkd_l hwf_l
            (by simpa [hdrSrcBranch, tysDecEq_self_isTrue dts] using hbr) hwX
            (by rw [vals_tupAppend, vals_tupSelectArgs, toArgTup_vals, hrest]; rfl)) hw2
    | _ => cases hwk <;> (dsimp only [validateHdr] at hval; cases hval)
  | .load t :: ss, cMs, xMs, nv, _, _, _, _, _, _, _, _, _, _, _, _, _, hval, hwk, hwk_diag,
      hwf, hnd, hG, hdiag, _, _, _, _, htc, htx, _, _, _, hw2, hC, hX => by
    cases hwf with
    | @load _ _ t' _ _ _ _ ha hk =>
      rcases hwk.rhs_load with ⟨ak, kk, rfl, hak, hkk⟩; rcases hwk_diag.load_inv with ⟨_, hkkd⟩
      dsimp only [validateHdr] at hval
      cases hdec : tyDecEq t t' with
      | isFalse => simp [hdec] at hval
      | isTrue heq =>
        subst heq; simp only [tyDecEq_self_isTrue t] at hval
        rcases Option.bind_eq_some_iff.1 hval with ⟨⟨_, _, _, _⟩, hv', ⟨⟩⟩
        rcases hw2 with ⟨v, hv_ld, hys⟩; dsimp only [hdrEmit]; simp only [tyDecEq_self_isTrue t, wp]
        rw [flatOptArg_val_of_inSet hnd hG hak ha (Arg.InSet.addArgKey _ _)]
        refine ⟨v, hv_ld, hdrEmit_wp dir ss cMs.tail xMs.tail (nv := nv + 1) hv' (hkk nv _)
          (hkkd nv nv) (hk _ v) (NoneDeadOpt.cons_some (NoneDeadOpt.sub
            (TrieSub.addArgKey _ _) hnd) nv (.var v)) (SomeValCtx.cons_some (v := v) rfl hG)
          hdiag.cons htc htx hys (fun _ _ _ _ hbr hwC hrest => hC ((v, ()), _) _ _
            (tupAppend (tupSelectArgs [t] _ (.var v, ())) _)
            (by simpa [hdrSrcBranch, tyDecEq_self_isTrue t] using hbr) hwC
            (by rw [vals_tupAppend, vals_tupSelectArgs]; simpa [hdrSelect, vals] using
                  congrArg (tupAppend (tupSelectVals [t] (cMs.headD []) (v, ()))) hrest))
          fun _ _ _ _ _ _ _ _ hnd_l hG_l hdk_l hwk_l hwkd_l hwf_l hbr hwX hrest =>
            hX ((v, ()), _) _ _ _ _ _ _ (tupAppend (tupSelectArgs [t] _ (.var v, ())) _)
              (fun s hs => hnd_l s (NoneDeadOpt.cons_some hs nv (.var v))) hG_l hdk_l hwk_l hwkd_l
              hwf_l (by simpa [hdrSrcBranch, tyDecEq_self_isTrue t] using hbr) hwX
              (by rw [vals_tupAppend, vals_tupSelectArgs]; simpa [hdrSelect, vals] using
                    congrArg (tupAppend (tupSelectVals [t] (xMs.headD []) (v, ()))) hrest)⟩
    | _ => cases hwk <;> (dsimp only [validateHdr] at hval; cases hval)

private theorem hdrPeel_wf_src {rs tail : List Ty} (dir wantCont : Bool) : (hdr : HdrPlan) →
    (ms : List (List Bool)) → {nv : Nat} → {s_dead : Trie Unit} → {Gk : Ctx K (OptArg Val)} →
    {Gk_diag : Ctx K K} → {Dk : Ctx BoolL (RotL Val Cont rs)} → {Dk_diag : Ctx BoolL BoolL} →
    {G : Ctx (OptArg Val) Val} → {D : Ctx (RotL Val Cont rs) Cont} → {ek : Expr K BoolL rs} →
    {e_peel : Expr (OptArg Val) (RotL Val Cont rs) rs} → {e_src arm_src : Expr Val Cont rs} →
    {sh : Trie Unit} → {armTk armEk : Expr K BoolL rs} → {nv' : Nat} →
    validateHdr hdr ek nv = some (sh, armTk, armEk, nv') →
    checkDeadStepMasks nv s_dead hdr ms = true →
    Wf Gk Dk ek e_peel → Wf Gk_diag Dk_diag ek ek → Wf G D e_peel e_src → NoneDeadOpt s_dead Gk →
    SomeValEq G → DiagK Gk_diag → (hv : HdrVals hdr) → (tl : Tup Val tail) →
    hdrSrcBranch dir wantCont hdr hv e_src = some arm_src →
    ∃ (Gk_out : Ctx K (OptArg Val)) (Gk_diag_out : Ctx K K) (G_out : Ctx (OptArg Val) Val),
      NoneDeadOpt s_dead Gk_out ∧ SomeValEq G_out ∧ DiagK Gk_diag_out ∧
      Wf Gk_out Dk (if wantCont == dir then armTk else armEk)
        (hdrPeel dir wantCont hdr ms (hdrSelect hdr ms hv tl) e_peel) ∧
      Wf Gk_diag_out Dk_diag (if wantCont == dir then armTk else armEk)
        (if wantCont == dir then armTk else armEk) ∧
      Wf G_out D (hdrPeel dir wantCont hdr ms (hdrSelect hdr ms hv tl) e_peel) arm_src
  | [], _, _, _, Gk, Gk_diag, _, _, G, _, _, _, _, _, _, _, _, _, hval, _,
      hwk, hwk_diag, hwf, hnd, hG, hdiag, (), _, hbr => by
    cases hwf with
    | jnz _ ht he =>
      rcases hwk.rhs_jnz with ⟨_, _, _, rfl, _, htk, hek⟩
      rcases hwk_diag.jnz_inv with ⟨_, htkd, hekd⟩; dsimp only [validateHdr] at hval
      simp only [pure, Option.some.injEq, Prod.mk.injEq] at hval
      rcases hval with ⟨rfl, rfl, rfl, rfl⟩
      simp only [hdrSrcBranch, Option.some.injEq] at hbr; subst hbr
      refine ⟨Gk, Gk_diag, G, hnd, hG, hdiag, ?_⟩
      cases hwd : wantCont == dir <;> dsimp only [hdrPeel]
      · simp only [hwd, Bool.false_eq_true, ↓reduceIte, hek, hekd, he, and_self]
      · simp only [hwd, ↓reduceIte, htk, htkd, ht, and_self]
    | _ => cases hwk <;> (dsimp only [validateHdr] at hval; cases hval)
  | .let_ dts :: ss, ms, nv, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hval, hchk,
      hwk, hwk_diag, hwf, hnd, hG, hdiag, (ys, rest_hv), tl, hbr => by
    cases hwf with
    | @let_ _ _ dts' _ _ _ _ _ hk =>
      rcases hwk.rhs_let with ⟨_, kk, rfl, _, hkk⟩; rcases hwk_diag.let_inv with ⟨_, hkkd⟩
      dsimp only [validateHdr] at hval
      cases hdec : tysDecEq dts dts' with
      | isFalse => simp [hdec] at hval
      | isTrue heq =>
        subst heq; simp only [tysDecEq_self_isTrue dts] at hval
        rcases Option.bind_eq_some_iff.1 hval with ⟨⟨_, _, _, _⟩, hv', ⟨⟩⟩
        dsimp only [checkDeadStepMasks, hdrSelect, hdrPeel, hdrSrcBranch] at hchk hbr ⊢
        simp only [Bool.and_eq_true] at hchk
        simp only [tysDecEq_self_isTrue dts, tupSplit_tupAppend] at hbr ⊢
        exact hdrPeel_wf_src dir wantCont ss ms.tail hv' hchk.2 (hkk _ _) (hkkd _ _) (hk _ ys)
          (checkDeadMask_noneDeadOpt dts _ hchk.1 _ hnd)
          (SomeValEq.append_tupWiden_tupSelectVals hG dts _ rfl)
          (DiagCtx.append (DiagCtx.zip_self _) hdiag) rest_hv tl hbr
    | _ => cases hwk <;> (dsimp only [validateHdr] at hval; cases hval)
  | .load t :: ss, ms, nv, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hval, hchk,
      hwk, hwk_diag, hwf, hnd, hG, hdiag, ((v, ()), rest_hv), tl, hbr => by
    cases hwf with
    | @load _ _ t' _ _ _ _ _ hk =>
      rcases hwk.rhs_load with ⟨_, kk, rfl, _, hkk⟩; rcases hwk_diag.load_inv with ⟨_, hkkd⟩
      dsimp only [validateHdr] at hval
      cases hdec : tyDecEq t t' with
      | isFalse => simp [hdec] at hval
      | isTrue heq =>
        subst heq; simp only [tyDecEq_self_isTrue t] at hval
        rcases Option.bind_eq_some_iff.1 hval with ⟨⟨_, _, _, _⟩, hv', ⟨⟩⟩
        dsimp only [checkDeadStepMasks, hdrSelect, hdrPeel, hdrSrcBranch] at hchk hbr ⊢
        simp only [Bool.and_eq_true] at hchk
        simp only [tyDecEq_self_isTrue t, tupSplit_tupAppend] at hbr ⊢
        exact hdrPeel_wf_src dir wantCont ss ms.tail hv' hchk.2 (hkk nv _) (hkkd nv nv) (hk _ v)
          (checkDeadMask_noneDeadOpt [t] _ hchk.1 _ hnd) (SomeValEq.append_tupWiden_tupSelectVals
            hG [t] _ (ys := (v, ())) rfl) hdiag.cons rest_hv tl hbr
    | _ => cases hwk <;> (dsimp only [validateHdr] at hval; cases hval)

mutual
/-- `rewriteRotWith` refines `wp` whenever `validateRotPlanWith` accepts. -/
private theorem rewriteRotWith_wp : (allowHdr : Bool) → (plan : RotPlan) →
    ∀ {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {Gk : Ctx K (OptArg Val)}
      {Gk_diag : Ctx K K} {Dk : Ctx BoolL (RotL Val Cont rs)} {Dk_diag : Ctx BoolL BoolL}
      {G : Ctx (OptArg Val) Val} {D : Ctx (RotL Val Cont rs) Cont} {ek : Expr K BoolL rs}
      {e₁ : Expr (OptArg Val) (RotL Val Cont rs) rs} {e₂ : Expr Val Cont rs} {nv : Nat}
      {s : Trie Unit}, Wf Gk Dk ek e₁ → Wf Gk_diag Dk_diag ek ek → Wf G D e₁ e₂ →
      validateRotPlanWith allowHdr plan ek nv = some s → NoneDeadOpt s Gk → SomeValEq G →
      DiagK Gk_diag → ValidDk Dk → RotWpD Γ Q X D → ∀ m, wp Γ Q X e₂ m →
      wp Γ Q X (rewriteRotWith allowHdr plan e₁) m
  | _, .leaf => fun hwk _ hwf hval hnd hG _ hDk hD m hw2 => by
    dsimp only [rewriteRotWith]; exact flatExpr_wp hwf hwk hval hnd hG hDk hD m hw2
  | allowHdr, .letP p => fun hwk hwk_diag hwf hval hnd hG hdiag hDk hD m hw2 => by
    cases hwf with
    | @let_ _ _ _ _ _ _ _ hop hk =>
      rcases hwk.rhs_let with ⟨_, _, rfl, hopk, hkk⟩; rcases hwk_diag.let_inv with ⟨_, hkkd⟩
      dsimp only [validateRotPlanWith] at hval
      rcases Option.bind_eq_some_iff.1 hval with ⟨_, hvk, ⟨⟩⟩
      cases hop with | mk code hargs => cases hopk with | mk _ hargsk =>
      dsimp only [rewriteRotWith]; simp only [flatOptOp, wp, Op.wp] at hw2 ⊢
      rw [flatOptArgs_vals_of_inSet hnd hG hargsk hargs (ArgsInSet.addArgKeys _ _)]
      exact OpCode.wp_mono code _ (fun r hr => rewriteRotWith_wp allowHdr p (hkk _ _) (hkkd _ _)
        (hk _ r) hvk (NoneDeadOpt.append_someVars (NoneDeadOpt.sub (TrieSub.addArgKeys _ _) hnd)
          _ _) (SomeValEq.append_someVars hG r) (DiagCtx.append (DiagCtx.zip_self _) hdiag)
        hDk hD m hr) hw2
    | _ => cases hwk <;> (dsimp only [validateRotPlanWith] at hval; cases hval)
  | allowHdr, .loadP p => fun hwk hwk_diag hwf hval hnd hG hdiag hDk hD m hw2 => by
    cases hwf with
    | load _ ha hk =>
      rcases hwk.rhs_load with ⟨_, _, rfl, hak, hkk⟩; rcases hwk_diag.load_inv with ⟨_, hkkd⟩
      dsimp only [validateRotPlanWith] at hval
      rcases Option.bind_eq_some_iff.1 hval with ⟨_, hvk, ⟨⟩⟩
      rcases hw2 with ⟨v, hv_ld, hw2⟩; dsimp only [rewriteRotWith]; simp only [wp]
      rw [flatOptArg_val_of_inSet hnd hG hak ha (Arg.InSet.addArgKey _ _)]
      exact ⟨v, hv_ld, rewriteRotWith_wp allowHdr p (hkk _ _) (hkkd _ _) (hk _ v) hvk
        (NoneDeadOpt.cons_some (NoneDeadOpt.sub (TrieSub.addArgKey _ _) hnd) _ (.var v))
        (SomeValCtx.cons_some (v := v) rfl hG) hdiag.cons hDk hD m hw2⟩
    | _ => cases hwk <;> (dsimp only [validateRotPlanWith] at hval; cases hval)
  | allowHdr, .storeP p => fun hwk hwk_diag hwf hval hnd hG hdiag hDk hD _ hw2 => by
    cases hwf with
    | store hv ha hk =>
      rcases hwk.rhs_store with ⟨vk, ak, _, rfl, hvk, hak, hkk⟩
      rcases hwk_diag.store_inv with ⟨_, _, hkkd⟩; dsimp only [validateRotPlanWith] at hval
      rcases Option.bind_eq_some_iff.1 hval with ⟨sk, hvk', ⟨⟩⟩; rcases hw2 with ⟨hok, hw2⟩
      dsimp only [rewriteRotWith]; simp only [wp]
      rw [flatOptArg_val_of_inSet hnd hG hvk hv (Arg.InSet.addArgKey _ _), flatOptArg_val_of_inSet
        hnd hG hak ha ((Arg.InSet.addArgKey _ _).mono (TrieSub.addArgKey _ _))]
      exact ⟨hok, rewriteRotWith_wp allowHdr p hkk hkkd hk hvk' (NoneDeadOpt.sub
        ((TrieSub.addArgKey ak sk).trans (TrieSub.addArgKey vk _)) hnd) hG hdiag hDk hD _ hw2⟩
    | _ => cases hwk <;> (dsimp only [validateRotPlanWith] at hval; cases hval)
  | allowHdr, .callP p => fun hwk hwk_diag hwf hval hnd hG hdiag hDk hD _ hw2 => by
    cases hwf with
    | @call _ _ _ _ _ _ _ _ _ hargs hk =>
      rcases hwk.rhs_call with ⟨argsk, _, rfl, hargsk, hkk⟩
      rcases hwk_diag.call_inv with ⟨_, hkkd⟩; dsimp only [validateRotPlanWith] at hval
      rcases Option.bind_eq_some_iff.1 hval with ⟨sk, hvk, ⟨⟩⟩
      rcases hw2 with ⟨P, E, hΓ, hP, hE⟩; dsimp only [rewriteRotWith]; simp only [wp]
      rw [flatOptArgs_vals_of_inSet hnd hG hargsk hargs (ArgsInSet.addArgKeys _ _)]
      exact ⟨P, E, hΓ, fun r m' hp => rewriteRotWith_wp allowHdr p (hkk _ _) (hkkd _ _) (hk _ r)
        hvk (NoneDeadOpt.append_someVars (NoneDeadOpt.sub (TrieSub.addArgKeys argsk sk) hnd) _ _)
        (SomeValEq.append_someVars hG r) (DiagCtx.append (DiagCtx.zip_self _) hdiag) hDk hD m'
        (hP r m' hp), hE⟩
    | _ => cases hwk <;> (dsimp only [validateRotPlanWith] at hval; cases hval)
  | allowHdr, .jnzP tp ep => fun hwk hwk_diag hwf hval hnd hG hdiag hDk hD m hw2 => by
    cases hwf with
    | jnz hc ht he =>
      rcases hwk.rhs_jnz with ⟨ck, _, _, rfl, hck, htk, hek⟩; rcases hwk_diag.jnz_inv with ⟨_, htkd,
        hekd⟩; dsimp only [validateRotPlanWith] at hval
      rcases Option.bind_eq_some_iff.1 hval with ⟨st, hvt, hr⟩
      rcases Option.bind_eq_some_iff.1 hr with ⟨se, hve, ⟨⟩⟩
      dsimp only [rewriteRotWith]; simp only [wp] at hw2 ⊢
      rw [flatOptArg_val_of_inSet hnd hG hck hc (Arg.InSet.addArgKey _ _)]
      exact ⟨fun h => rewriteRotWith_wp allowHdr tp htk htkd ht hvt (NoneDeadOpt.sub
          ((TrieSub.union_left st se).trans (TrieSub.addArgKey ck _)) hnd) hG hdiag hDk hD m
          (hw2.1 h), fun h => rewriteRotWith_wp allowHdr ep hek hekd he hve (NoneDeadOpt.sub
          ((TrieSub.union_right st se).trans (TrieSub.addArgKey ck _)) hnd) hG hdiag hDk hD m
          (hw2.2 h)⟩
    | @jump _ _ _ j₁ _ _ _ hj hargs =>
      rcases hwk.rhs_jump with ⟨lb, argsk, rfl, hjk, hargsk⟩; cases allowHdr
      · cases tp <;> cases ep <;> (dsimp only [validateRotPlanWith] at hval; cases hval)
      · cases tp <;> cases ep <;> dsimp only [validateRotPlanWith] at hval
        all_goals first | cases hval | (cases hlb : lb with | false => simp [hlb] at hval | true =>
          simp only [hlb, Bool.and_true, ↓reduceIte, pure, Option.some.injEq] at hval; subst hval
          have hlive : rotLIsLive j₁ = true := CtxPred.mem hDk hjk hlb
          have hvals := flatOptArgs_vals_of_inSet hnd hG hargsk hargs (ArgsInSet.addArgKeys _ _)
          have hd := CtxPred.mem hD hj; cases j₁ with
          | keep _ =>
            dsimp only [rewriteRotWith]; simp only [wp] at hw2 ⊢; rw [hvals, hd]; exact hw2
          | dead => simp [rotLIsLive] at hlive
          | expand _ => dsimp only [rewriteRotWith]; exact hd _ m (hvals ▸ hw2)
          | expandOrKeep _ _ =>
            dsimp only [rewriteRotWith]; simp only [wp] at hw2 ⊢; rw [hvals]; exact hd.2 _ m hw2)
    | _ => cases hwk <;> (dsimp only [validateRotPlanWith] at hval; cases hval)
  | allowHdr, .groupKeep bsP kP => fun hwk hwk_diag hwf hval hnd hG hdiag hDk hD m hw2 => by
    cases hwf with
    | @group _ _ sig _ _ _ _ hb hk =>
      rcases hwk.rhs_group with ⟨bk, kk, rfl, hbk, hkk⟩; rcases hwk_diag.group_inv with ⟨hbkd, hkkd⟩
      dsimp only [validateRotPlanWith] at hval
      rcases Option.bind_eq_some_iff.1 hval with ⟨sb, hvb, hr⟩
      rcases Option.bind_eq_some_iff.1 hr with ⟨sk, hvk, ⟨⟩⟩
      dsimp only [rewriteRotWith]; simp only [wp]; intro Js_out hcl_out
      have hDk' := CtxPred.append (validDk_wrapKeepLabels Js_out) hDk
      have hD' := CtxPred.append (rotWpD_wrapKeepLabels _ _ _ Js_out) hD
      have hcl₂ := rewriteKeepB_wp allowHdr bsP (hbk (trueLabels sig) _) (hbkd _ _) (hb _ Js_out)
        hvb (NoneDeadOpt.sub (TrieSub.union_left sb sk) hnd) hG hdiag hDk' hD' hcl_out
      exact rewriteRotWith_wp allowHdr kP (hkk (trueLabels sig) _) (hkkd _ _) (hk _ Js_out) hvk
        (NoneDeadOpt.sub (TrieSub.union_right sb sk) hnd) hG hdiag hDk' hD' m (hw2 Js_out hcl₂)
    | _ => cases hwk <;> (dsimp only [validateRotPlanWith] at hval; cases hval)
  | allowHdr, .groupRot dir hdr contMasks exitMode contP exitP entryP =>
      fun hwk hwk_diag hwf hval hnd hG hdiag hDk hD m hw2 => by
    suffices H : ∀ {Γ rs Q X} {Gk : Ctx K (OptArg Val)} {Gk_diag : Ctx K K}
        {Dk : Ctx BoolL (RotL Val Cont rs)} {Dk_diag : Ctx BoolL BoolL} {G : Ctx (OptArg Val) Val}
        {D : Ctx (RotL Val Cont rs) Cont} {ek e₁ e₂ nv s}, Wf Gk Dk ek e₁ →
        Wf Gk_diag Dk_diag ek ek → Wf G D e₁ e₂ → validateRotPlanWith allowHdr
          (.groupRot dir hdr contMasks exitMode contP exitP entryP) ek nv = some s →
        NoneDeadOpt s Gk → SomeValEq G → DiagK Gk_diag → ValidDk Dk → RotWpD Γ Q X D →
        wp Γ Q X e₂ m → wp Γ Q X (rewriteRotWith allowHdr
          (.groupRot dir hdr contMasks exitMode contP exitP entryP) e₁) m from
      H hwk hwk_diag hwf hval hnd hG hdiag hDk hD hw2
    intro Γ rs Q X Gk Gk_diag Dk Dk_diag G D ek e₁ e₂ nv s
      hwk hwk_diag hwf hval hnd hG hdiag hDk hD hw2
    cases hwf with
    | @group _ _ sig b₁ b₂ k₁ k₂ hb hk =>
      cases sig with
      | nil => cases hwk <;> (dsimp only [validateRotPlanWith] at hval; cases hval)
      | cons ts sig' =>
        cases sig' with
        | cons _ _ => cases hwk <;> (dsimp only [validateRotPlanWith] at hval; cases hval)
        | nil =>
          rcases hwk.rhs_group with ⟨bk, kk, rfl, hbk, hkk⟩; rcases hwk_diag.group_inv with
            ⟨hbkd, hkkd⟩; dsimp only [validateRotPlanWith] at hval
          rcases Option.bind_eq_some_iff.1 hval with ⟨⟨sh, armT, armE, _⟩, hvT, hval⟩
          rcases Option.bind_eq_some_iff.1 hval with ⟨⟨shF, armTF, armEF, _⟩, hvF, hval⟩
          rcases Option.bind_eq_some_iff.1 hval with ⟨sc, hvC, hval⟩
          rcases Option.bind_eq_some_iff.1 hval with ⟨sx, hvX, hval⟩
          rcases Option.bind_eq_some_iff.1 hval with ⟨se, hvE, hval⟩
          cases hchkC : checkDeadStepMasks (nv + ts.length) sc hdr contMasks with
          | false => simp [hchkC] at hval
          | true =>
            simp only [hchkC, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hval
            let xsLvls := Tup.levels ts nv
            have hsh_eq := (validateHdr_diag_eq hdr (DiagCtx.append (DiagCtx.zip_self xsLvls)
              hdiag) ((hbkd (true, ()) (false, ())).get .here xsLvls xsLvls) hvT hvF).1
            have hDiagT := (hbkd (true, ()) (true, ())).get .here xsLvls xsLvls
            have hDiagF := (hbkd (false, ()) (false, ())).get .here xsLvls xsLvls
            have mkNds (heq : trieUnion sh (trieUnion sc (trieUnion sx se)) = s) :
                NoneDeadOpt shF Gk ∧ NoneDeadOpt sc Gk ∧ NoneDeadOpt sx Gk ∧ NoneDeadOpt se Gk := by
              subst heq; let ul := TrieSub.union_left; let ur := TrieSub.union_right
              exact ⟨hsh_eq ▸ NoneDeadOpt.sub (ul _ _) hnd, NoneDeadOpt.sub ((ul _ _).trans
                (ur _ _)) hnd, NoneDeadOpt.sub (((ul _ _).trans (ur _ _)).trans (ur _ _)) hnd,
                NoneDeadOpt.sub (((ur _ _).trans (ur _ _)).trans (ur _ _)) hnd⟩
            let rotPost (J_rot : Cont (rotSig hdr contMasks ts)) jLbl : Prop :=
              ∀ p m', wp Γ Q X (rewriteRotWith (if isPartialMasks hdr contMasks then true
                else allowHdr) contP (rotBodyExpr dir hdr contMasks b₁ jLbl p)) m' → J_rot p m'
            let mkJSrc (mkFn : Cont (rotSig hdr contMasks ts) → Tup (Arg Val) ts →
                Expr Val Cont rs) (J_rot : Cont (rotSig hdr contMasks ts)) : Cont ts :=
              fun vs m₀ => ∀ args, vals args = vs → wp Γ Q X (mkFn J_rot args) m₀
            have finishGroup (mkFn : Cont (rotSig hdr contMasks ts) → Tup (Arg Val) ts →
                  Expr Val Cont rs) (hnd_se : NoneDeadOpt se Gk)
                (mkClSrc : ∀ J_rot jLbl,
                  ValidDk (Tup.zip (as := [ts]) (true, ()) (jLbl, ()) ++ Dk) →
                  RotWpD Γ Q X (Tup.zip (as := [ts]) (jLbl, ()) (mkJSrc mkFn J_rot, ()) ++ D) →
                  rotPost J_rot jLbl →
                  Closed Γ Q X (b₂ (mkJSrc mkFn J_rot, ())) (mkJSrc mkFn J_rot, ())) :
                wp Γ Q X (if isPartialMasks hdr contMasks then
                    Expr.group (sig := [rotSig hdr contMasks ts, ts]) (fun (J_rot, J_hdr, ()) =>
                        .cons (fun p => rewriteRotWith true contP (rotBodyExpr dir hdr contMasks
                          b₁ (.expandOrKeep (mkFn J_rot) J_hdr) p))
                          (.cons (fun h => mkFn J_rot (toArgTup h)) .nil))
                      (fun (J_rot, _, ()) =>
                        rewriteRotWith allowHdr entryP (k₁ (.expand (mkFn J_rot), ())))
                  else Expr.group (sig := [rotSig hdr contMasks ts]) (fun (J_rot, ()) =>
                        .cons (fun p => rewriteRotWith allowHdr contP
                          (rotBodyExpr dir hdr contMasks b₁ (.expand (mkFn J_rot)) p)) .nil)
                      (fun (J_rot, ()) =>
                        rewriteRotWith allowHdr entryP (k₁ (.expand (mkFn J_rot), ())))) m := by
              have mkDk (jLbl : RotL Val Cont rs ts) (hlive : rotLIsLive jLbl = true) :
                  ValidDk (Tup.zip (as := [ts]) (true, ()) (jLbl, ()) ++ Dk) := fun p hp ht => by
                cases hp with | head => exact hlive | tail _ hp' => exact hDk p hp' ht
              have mkDT (J_rot : Cont (rotSig hdr contMasks ts)) :
                  RotWpD Γ Q X (Tup.zip (as := [ts]) (.expand (mkFn J_rot), ())
                    (mkJSrc mkFn J_rot, ()) ++ D) := fun p hp => by
                cases hp with | head => exact fun _ _ hj => hj _ rfl | tail _ hp' => exact hD p hp'
              have mkE (J_rot : Cont (rotSig hdr contMasks ts)) (jLbl : RotL Val Cont rs ts)
                  (hDC : RotWpD Γ Q X (Tup.zip (as := [ts]) (jLbl, ())
                    (mkJSrc mkFn J_rot, ()) ++ D))
                  (hDkT : ValidDk (Tup.zip (as := [ts]) (true, ()) (jLbl, ()) ++ Dk))
                  (hcl : rotPost J_rot jLbl) :=
                rewriteRotWith_wp allowHdr entryP (hkk _ _) (hkkd _ _)
                  (hk (.expand (mkFn J_rot), ()) (mkJSrc mkFn J_rot, ())) hvE hnd_se hG hdiag
                  (mkDk _ rfl) (mkDT J_rot) m (hw2 _ (mkClSrc J_rot _ hDkT hDC hcl))
              cases hpart : isPartialMasks hdr contMasks <;>
                simp only [Bool.false_eq_true, ↓reduceIte, wp]
              · intro (J_rot, ()) hcl_rot; simp only [Closed, and_true] at hcl_rot
                exact mkE J_rot (.expand (mkFn J_rot)) (mkDT J_rot) (mkDk _ rfl)
                  fun p m' hp => hcl_rot p m' (by simpa [hpart] using hp)
              · intro (J_rot, J_hdr, ()) hcl_both; simp only [Closed, and_true] at hcl_both
                refine mkE J_rot (.expandOrKeep (mkFn J_rot) J_hdr) (fun p hp => by
                  cases hp with
                  | head =>
                    exact ⟨fun _ _ hj => hj _ rfl,
                      fun _ _ hj => hcl_both.2 _ _ (hj (toArgTup _) (toArgTup_vals _))⟩
                  | tail _ hp' => exact hD p hp') (mkDk _ rfl)
                  fun p m' hp => hcl_both.1 p m' (by simpa [hpart] using hp)
            have rotBack (J_rot : Cont (rotSig hdr contMasks ts)) jLbl (J_src : Cont ts)
                (hDkT : ValidDk (Tup.zip (as := [ts]) (true, ()) (jLbl, ()) ++ Dk))
                (hDT : RotWpD Γ Q X (Tup.zip (as := [ts]) (jLbl, ()) (J_src, ()) ++ D))
                (hcl_rot : rotPost J_rot jLbl) (xs : Tup Val ts) (hnd_sc : NoneDeadOpt sc Gk)
                {hv m' armC_src rotArgs}
                (hbr : hdrSrcBranch dir true hdr hv ((b₂ (J_src, ())).get .here xs) = some armC_src)
                (hwC : wp Γ Q X armC_src m')
                (hrot_eq : vals rotArgs = hdrSelect hdr contMasks hv xs) :
                J_rot (vals rotArgs) m' := by
              apply hcl_rot (vals rotArgs) m'
              obtain ⟨_, _, _, hnd_o, hG_o, hdiag_o, hwk_o, hwkd_o, hwf_o⟩ := hdrPeel_wf_src dir
                true hdr contMasks hvT hchkC ((hbk (true, ()) (jLbl, ())).get .here xsLvls _)
                hDiagT ((hb (jLbl, ()) (J_src, ())).get .here _ xs) (NoneDeadOpt.append_someVars
                  hnd_sc xsLvls xs) (SomeValEq.append_someVars hG xs)
                (DiagCtx.append (DiagCtx.zip_self xsLvls) hdiag) hv xs hbr
              have harm_eq : (if true == dir then armT else armE) = (if dir then armT else armE) :=
                by cases dir <;> rfl
              rw [harm_eq] at hwk_o hwkd_o
              cases hpart : isPartialMasks hdr contMasks <;> simp only [Bool.false_eq_true,
                ↓reduceIte, rotBodyExpr, hrot_eq, splitTail_hdrSelect]
              · exact rewriteRotWith_wp allowHdr contP hwk_o hwkd_o hwf_o
                  (by simpa [hpart] using hvC) hnd_o hG_o hdiag_o hDkT hDT m' hwC
              · exact rewriteRotWith_wp true contP hwk_o hwkd_o hwf_o
                  (by simpa [hpart] using hvC) hnd_o hG_o hdiag_o hDkT hDT m' hwC
            cases exitMode with
            | inline =>
              simp only [pure, Option.some.injEq] at hval
              obtain ⟨hnd_shF, hnd_sc, hnd_sx, hnd_se⟩ := mkNds hval; dsimp only [rewriteRotWith]
              let mkFn : Cont (rotSig hdr contMasks ts) → Tup (Arg Val) ts → Expr Val Cont rs :=
                fun J_rot args => hdrEmit (tailC := ts) (tailX := ts) dir args args hdr contMasks
                  [] ((b₁ (exitLabels ts)).get .here (someArgsToOpt args))
                  (fun rotArgs => .jump J_rot rotArgs)
                  (fun ex _ => rewriteRotWith allowHdr exitP ex)
              refine finishGroup mkFn hnd_se fun J_rot jLbl hDkT hDT hcl_rot => ?_
              rw [closed_iff]; intro _ i xs _ hw; cases i with
              | there i => exact nomatch i
              | here =>
                intro args hargs
                refine hdrEmit_wp dir hdr contMasks [] hvF ((hbk (false, ()) _).get .here xsLvls _)
                  hDiagF ((hb _ (mkJSrc mkFn J_rot, ())).get .here _ xs)
                  (NoneDeadOpt.append_some hnd_shF xsLvls args) (SomeValEq.append_someArgs hG hargs)
                  (DiagCtx.append (DiagCtx.zip_self xsLvls) hdiag) hargs hargs hw
                  (fun hv m' _ _ hbr hwC hrot_eq =>
                    rotBack J_rot jLbl _ hDkT hDT hcl_rot xs hnd_sc hbr hwC hrot_eq)
                  fun _ m' _ _ _ _ _ _ hnd_l hG_l hdiag_l hwk_l hwkd_l hwf_l _ hwX _ =>
                    rewriteRotWith_wp allowHdr exitP hwk_l hwkd_l hwf_l hvX
                      (hnd_l sx (NoneDeadOpt.append_some hnd_sx xsLvls args)) hG_l hdiag_l
                      (CtxPred.append (CtxPred.cons (fun h => by cases h) (CtxPred.nil _)) hDk)
                      (CtxPred.append (CtxPred.cons trivial (CtxPred.nil _)) hD) m' hwX
            | wrap xsMask hMasks =>
              cases hchkX : checkDeadMask nv sx ts xsMask &&
                  checkDeadStepMasks (nv + ts.length) sx hdr hMasks with
              | false => simp [hchkX] at hval
              | true =>
                simp only [hchkX, ↓reduceIte, pure, Option.some.injEq] at hval
                obtain ⟨hnd_shF, hnd_sc, hnd_sx, hnd_se⟩ := mkNds hval
                simp only [Bool.and_eq_true] at hchkX; dsimp only [rewriteRotWith]; simp only [wp]
                intro (J_exit, ()) hcl_exit; simp only [Closed, and_true] at hcl_exit
                let mkFn : Cont (rotSig hdr contMasks ts) → Tup (Arg Val) ts → Expr Val Cont rs :=
                  fun J_rot args => hdrEmit (tailC := ts) (tailX := filterTys ts xsMask) dir args
                    (tupSelectArgs ts xsMask args) hdr contMasks hMasks
                    ((b₁ (exitLabels ts)).get .here (someArgsToOpt args))
                    (fun rotArgs => .jump J_rot rotArgs) (fun _ exArgs => .jump J_exit exArgs)
                refine finishGroup mkFn hnd_se fun J_rot jLbl hDkT hDT hcl_rot => ?_
                rw [closed_iff]; intro _ i xs _ hw; cases i with
                | there i => exact nomatch i
                | here =>
                  intro args hargs
                  refine hdrEmit_wp dir hdr contMasks hMasks hvF ((hbk (false, ()) _).get .here
                    xsLvls _) hDiagF ((hb _ (mkJSrc mkFn J_rot, ())).get .here _ xs)
                    (NoneDeadOpt.append_some hnd_shF xsLvls args)
                    (SomeValEq.append_someArgs hG hargs)
                    (DiagCtx.append (DiagCtx.zip_self xsLvls) hdiag) hargs
                    (vals_tupSelectArgs xsMask args) hw
                    (fun hv m' _ _ hbr hwC hrot_eq =>
                      rotBack J_rot jLbl _ hDkT hDT hcl_rot xs hnd_sc hbr hwC hrot_eq) ?_
                  intro hv m' _ _ _ _ _ exitArgs _ _ _ _ _ _ hbr hwX hexit_eq
                  apply hcl_exit (vals exitArgs) m'
                  have hexit_eq' : vals exitArgs = hdrSelect hdr hMasks hv
                      (tupSelectVals ts xsMask xs) := by rw [hexit_eq, hargs]
                  rw [show splitTail hdr hMasks (vals exitArgs) = tupSelectVals ts xsMask xs by
                    rw [hexit_eq', splitTail_hdrSelect], hexit_eq']
                  let xsOpt := tupWiden ts xsMask (tupSelectVals ts xsMask xs)
                  obtain ⟨_, _, _, hnd_o, hG_o, hdiag_o, hwk_o, hwkd_o, hwf_o⟩ := hdrPeel_wf_src dir
                    false hdr hMasks hvF hchkX.2 ((hbk (false, ()) _).get .here xsLvls xsOpt) hDiagF
                    ((hb _ (mkJSrc mkFn J_rot, ())).get .here xsOpt xs)
                    (checkDeadMask_noneDeadOpt ts xsMask hchkX.1 _ hnd_sx)
                    (SomeValEq.append_tupWiden_tupSelectVals hG ts xsMask rfl)
                    (DiagCtx.append (DiagCtx.zip_self xsLvls) hdiag) hv _ hbr
                  have harm_eq : (if false == dir then armTF else armEF) =
                      (if dir then armEF else armTF) := by cases dir <;> rfl
                  rw [harm_eq] at hwk_o hwkd_o
                  exact rewriteRotWith_wp allowHdr exitP hwk_o hwkd_o hwf_o hvX hnd_o hG_o hdiag_o
                    (CtxPred.append (CtxPred.cons (fun h => by cases h) (CtxPred.nil _)) hDk)
                    (CtxPred.append (CtxPred.cons trivial (CtxPred.nil _)) hD) m' hwX
    | _ => cases hwk <;> (dsimp only [validateRotPlanWith] at hval; cases hval)
where
  rewriteKeepB_wp : (allowHdr : Bool) → (ps : List RotPlan) →
      ∀ {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {Gk : Ctx K (OptArg Val)}
        {Gk_diag : Ctx K K} {Dk : Ctx BoolL (RotL Val Cont rs)} {Dk_diag : Ctx BoolL BoolL}
        {G : Ctx (OptArg Val) Val} {D : Ctx (RotL Val Cont rs) Cont} {sig : List (List Ty)}
        {bsk : Blocks K BoolL rs sig} {bs₁ : Blocks (OptArg Val) (RotL Val Cont rs) rs sig}
        {bs₂ : Blocks Val Cont rs sig} {Js : Tup Cont sig} {nv : Nat} {sb : Trie Unit},
        WfB Gk Dk bsk bs₁ → WfB Gk_diag Dk_diag bsk bsk → WfB G D bs₁ bs₂ →
        validateRotPlanWith.validateKeepB allowHdr ps bsk nv = some sb → NoneDeadOpt sb Gk →
        SomeValEq G → DiagK Gk_diag → ValidDk Dk → RotWpD Γ Q X D →
        Closed Γ Q X (rewriteRotWith.rewriteKeepB allowHdr ps bs₁) Js → Closed Γ Q X bs₂ Js
    | _, [] => fun hbk _ hb hval _ _ _ _ _ _ => by
      cases hbk with
      | nil => cases hb; trivial
      | cons _ _ => dsimp only [validateRotPlanWith.validateKeepB] at hval; cases hval
    | allowHdr, p :: ps => fun hbk hbkd hb hval hnd hG hdiag hDk hD hcl => by
      cases hbk with
      | nil => dsimp only [validateRotPlanWith.validateKeepB] at hval; cases hval
      | cons hbk1 hbk_rest =>
        cases hb with | cons hb1 hb_rest => cases hbkd with | cons hbkd1 hbkd_rest =>
        dsimp only [validateRotPlanWith.validateKeepB] at hval
        rcases Option.bind_eq_some_iff.1 hval with ⟨s₁, hs₁, hr⟩
        rcases Option.bind_eq_some_iff.1 hr with ⟨s₂, hs₂, ⟨⟩⟩
        dsimp only [rewriteRotWith.rewriteKeepB] at hcl ⊢; simp only [Closed] at hcl ⊢
        exact ⟨fun xs m hw => hcl.1 xs m (rewriteRotWith_wp allowHdr p (hbk1 _ _) (hbkd1 _ _)
            (hb1 _ xs) hs₁ (NoneDeadOpt.append_someVars (NoneDeadOpt.sub
              (TrieSub.union_left s₁ s₂) hnd) _ _) (SomeValEq.append_someVars hG xs)
            (DiagCtx.append (DiagCtx.zip_self _) hdiag) hDk hD m hw),
          rewriteKeepB_wp allowHdr ps hbk_rest hbkd_rest hb_rest hs₂
            (NoneDeadOpt.sub (TrieSub.union_right s₁ s₂) hnd) hG hdiag hDk hD hcl.2⟩
end

private theorem rewriteRot_wp (plan : RotPlan) {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {Gk : Ctx K (OptArg Val)} {Gk_diag : Ctx K K} {Dk : Ctx BoolL (RotL Val Cont rs)}
    {Dk_diag : Ctx BoolL BoolL} {G : Ctx (OptArg Val) Val} {D : Ctx (RotL Val Cont rs) Cont}
    {ek : Expr K BoolL rs} {e₁ : Expr (OptArg Val) (RotL Val Cont rs) rs} {e₂ : Expr Val Cont rs}
    {nv : Nat} {s : Trie Unit} (hwk : Wf Gk Dk ek e₁) (hwk_diag : Wf Gk_diag Dk_diag ek ek)
    (hwf : Wf G D e₁ e₂) (hval : validateRotPlan plan ek nv = some s) (hnd : NoneDeadOpt s Gk)
    (hG : SomeValEq G) (hdiag : DiagK Gk_diag) (hDk : ValidDk Dk) (hD : RotWpD Γ Q X D) :
    ∀ m, wp Γ Q X e₂ m → wp Γ Q X (rewriteRot plan e₁) m :=
  rewriteRotWith_wp false plan hwk hwk_diag hwf hval hnd hG hdiag hDk hD

/-! ## Well-scopedness (`callsOk`) preservation -/

private abbrev UnitV : Ty → Type := fun _ => Unit
private abbrev UnitL : List Ty → Type := fun _ => Unit

/-- Label invariant asserting every `.expand fn` produces `callsOk` bodies at all args. -/
private abbrev RotCallsL (allowed : List SigEntry) (exits : List Sym) {rs : List Ty}
    (D : Ctx (RotL UnitV UnitL rs) UnitL) : Prop := CtxPred (fun _ l _ => match l with
  | .expand fn | .expandOrKeep fn _ => ∀ args, (fn args).callsOk allowed exits
  | .keep _ | .dead => True) D

private theorem rotCallsL_wrapKeepLabels (allowed : List SigEntry) (exits : List Sym)
    {rs : List Ty} : {sig : List (List Ty)} → (Js : Tup UnitL sig) →
    RotCallsL allowed exits (Tup.zip (wrapKeepLabels (V := UnitV) (rs := rs) Js) Js)
  | [], () => CtxPred.nil _
  | _ :: _, ((), Js) => CtxPred.cons trivial (rotCallsL_wrapKeepLabels allowed exits Js)

private theorem rotCallsL_exitLabels (allowed : List SigEntry) (exits : List Sym) {rs : List Ty}
    (ts : List Ty) (Js : Tup UnitL [ts]) : RotCallsL allowed exits
      (Tup.zip (exitLabels (V := UnitV) (L := UnitL) (rs := rs) ts) Js) :=
  CtxPred.cons trivial (CtxPred.nil _)

private theorem flatBlocks_callsOk {allowed : List SigEntry} {exits : List Sym} {rs : List Ty} :
    {sig : List (List Ty)} → (bs₁ : Blocks (OptArg UnitV) (RotL UnitV UnitL rs) rs sig) →
    (bs₂ : Blocks UnitV UnitL rs sig) → (∀ {ts} (i : Member ts sig) x₁ x₂,
      (bs₂.get i x₂).callsOk allowed exits → (flatExpr (bs₁.get i x₁)).callsOk allowed exits) →
    bs₂.callsOk allowed exits → (flatExpr.flatBlocks bs₁).callsOk allowed exits
  | [], .nil, .nil, _, _ => trivial
  | _ :: _, .cons _ bs₁, .cons _ bs₂, hbi, hbs₂ => by
    dsimp only [flatExpr.flatBlocks, Blocks.callsOk] at hbs₂ ⊢
    exact ⟨hbi .here _ _ hbs₂.1, flatBlocks_callsOk bs₁ bs₂ (fun i => hbi (.there i)) hbs₂.2⟩

private theorem flatExpr_callsOk {allowed : List SigEntry} {exits : List Sym} {rs : List Ty}
    {G : Ctx (OptArg UnitV) UnitV} {D : Ctx (RotL UnitV UnitL rs) UnitL}
    {e₁ : Expr (OptArg UnitV) (RotL UnitV UnitL rs) rs} {e₂ : Expr UnitV UnitL rs}
    (hwf : Wf G D e₁ e₂) :
    RotCallsL allowed exits D → e₂.callsOk allowed exits → (flatExpr e₁).callsOk allowed exits := by
  induction hwf using Wf.induct with
  | let_ _ _ ih => exact fun hD hc => ih _ _ hD hc
  | store _ _ _ ih => exact fun hD hc => ih hD hc
  | load _ _ _ ih => exact fun hD hc => ih (some (.var ())) () hD hc
  | call _ _ _ ih => exact fun hD ⟨hf, hc⟩ => ⟨hf, ih _ _ hD hc⟩
  | jnz _ _ _ iht ihe => exact fun hD ⟨ht, he⟩ => ⟨iht hD ht, ihe hD he⟩
  | @jump _ _ _ j₁ _ _ _ hj _ =>
    intro hD _
    cases j₁ with
    | keep _ | dead => trivial
    | expand _ | expandOrKeep _ _ => exact CtxPred.mem hD hj _
  | ret _ | exit _ _ | hlt => exact fun _ hc => hc
  | @group _ _ sig b₁ b₂ _ _ _ _ ihb ihk =>
    intro hD ⟨hb, hk⟩
    have hD' := CtxPred.append (rotCallsL_wrapKeepLabels allowed exits (Tup.units sig)) hD
    exact ⟨flatBlocks_callsOk (b₁ _) (b₂ _) (fun i x₁ x₂ => ihb _ _ i x₁ x₂ hD') hb,
      ihk _ _ hD' hk⟩

private theorem hdrPeel_callsOk {allowed : List SigEntry} {exits : List Sym} {rs tail : List Ty}
    (dir wantCont : Bool) : (hdr : HdrPlan) → (ms : List (List Bool)) →
    (params : Tup UnitV (stepMasksSig hdr ms tail)) → {G : Ctx (OptArg UnitV) UnitV} →
    {D : Ctx (RotL UnitV UnitL rs) UnitL} → {e₁ : Expr (OptArg UnitV) (RotL UnitV UnitL rs) rs} →
    {e₂ : Expr UnitV UnitL rs} → Wf G D e₁ e₂ → e₂.callsOk allowed exits →
    ∃ G' e₂', Wf G' D (hdrPeel dir wantCont hdr ms params e₁) e₂' ∧ e₂'.callsOk allowed exits
  | [], _, _, G, _, _, _, hwf, hc => by
    cases hwf with
    | jnz _ ht he =>
      cases hwd : wantCont == dir <;> dsimp only [hdrPeel]
      · exact ⟨_, _, by simp only [hwd, Bool.false_eq_true, ↓reduceIte]; exact he, hc.2⟩
      · exact ⟨_, _, by simp only [hwd, ↓reduceIte]; exact ht, hc.1⟩
    | _ => exact ⟨G, .hlt, .hlt, trivial⟩
  | .let_ dts :: ss, ms, params, G, _, _, _, hwf, hc => by
    cases hwf with
    | @let_ _ _ dts' _ _ _ _ _ hk =>
      cases hdec : tysDecEq dts dts' with
      | isFalse => dsimp only [hdrPeel]; simp only [hdec]; exact ⟨G, .hlt, .hlt, trivial⟩
      | isTrue heq =>
        subst heq; dsimp only [hdrPeel]; simp only [tysDecEq_self_isTrue dts]
        let p := tupSplit (filterTys dts (ms.headD [])) params
        exact hdrPeel_callsOk dir wantCont ss ms.tail p.2 (hk (tupWiden _ _ p.1) _) hc
    | _ => exact ⟨G, .hlt, .hlt, trivial⟩
  | .load t :: ss, ms, params, G, _, _, _, hwf, hc => by
    cases hwf with
    | @load _ _ t' _ _ _ _ _ hk =>
      cases hdec : tyDecEq t t' with
      | isFalse => dsimp only [hdrPeel]; simp only [hdec]; exact ⟨G, .hlt, .hlt, trivial⟩
      | isTrue heq =>
        subst heq; dsimp only [hdrPeel]; simp only [tyDecEq_self_isTrue t]
        let p := tupSplit (filterTys [t] (ms.headD [])) params
        exact hdrPeel_callsOk dir wantCont ss ms.tail p.2 (hk (tupWiden _ _ p.1).1 ()) hc
    | _ => exact ⟨G, .hlt, .hlt, trivial⟩

private theorem hdrEmit_callsOk {allowed : List SigEntry} {exits : List Sym}
    {rs tailC tailX : List Ty} (dir : Bool) (tc : Tup (Arg UnitV) tailC)
    (tx : Tup (Arg UnitV) tailX) : (hdr : HdrPlan) → (cMs xMs : List (List Bool)) →
    {G : Ctx (OptArg UnitV) UnitV} → {D : Ctx (RotL UnitV UnitL rs) UnitL} →
    {e₁ : Expr (OptArg UnitV) (RotL UnitV UnitL rs) rs} → {e₂ : Expr UnitV UnitL rs} →
    {kC : Tup (Arg UnitV) (stepMasksSig hdr cMs tailC) → Expr UnitV UnitL rs} →
    {kX : Expr (OptArg UnitV) (RotL UnitV UnitL rs) rs →
      Tup (Arg UnitV) (stepMasksSig hdr xMs tailX) → Expr UnitV UnitL rs} →
    Wf G D e₁ e₂ → e₂.callsOk allowed exits → (∀ a, (kC a).callsOk allowed exits) →
    (∀ G' ex₁ ex₂, Wf G' D ex₁ ex₂ → ex₂.callsOk allowed exits →
      ∀ a, (kX ex₁ a).callsOk allowed exits) →
    (hdrEmit dir tc tx hdr cMs xMs e₁ kC kX).callsOk allowed exits
  | [], _, _, _, _, _, _, _, _, hwf, hc, hkC, hkX => by
    cases hwf with
    | jnz _ ht he =>
      cases dir <;> dsimp only [hdrEmit]
      · exact ⟨hkX _ _ _ ht hc.1 tx, hkC tc⟩
      · exact ⟨hkC tc, hkX _ _ _ he hc.2 tx⟩
    | _ => trivial
  | .let_ dts :: ss, cMs, xMs, _, _, _, _, _, _, hwf, hc, hkC, hkX => by
    cases hwf with
    | @let_ _ _ dts' _ _ _ _ _ hk =>
      cases hdec : tysDecEq dts dts' with
      | isFalse => dsimp only [hdrEmit]; simp only [hdec]; trivial
      | isTrue heq =>
        subst heq; dsimp only [hdrEmit]; simp only [tysDecEq_self_isTrue dts, Expr.callsOk]
        exact hdrEmit_callsOk dir tc tx ss cMs.tail xMs.tail (hk _ (Tup.units dts)) hc
          (fun _ => hkC _) (fun _ _ _ hex hce _ => hkX _ _ _ hex hce _)
    | _ => trivial
  | .load t :: ss, cMs, xMs, _, _, _, _, _, _, hwf, hc, hkC, hkX => by
    cases hwf with
    | @load _ _ t' _ _ _ _ _ hk =>
      cases hdec : tyDecEq t t' with
      | isFalse => dsimp only [hdrEmit]; simp only [hdec]; trivial
      | isTrue heq =>
        subst heq; dsimp only [hdrEmit]; simp only [tyDecEq_self_isTrue t, Expr.callsOk]
        exact hdrEmit_callsOk dir tc tx ss cMs.tail xMs.tail (hk _ ()) hc
          (fun _ => hkC _) (fun _ _ _ hex hce _ => hkX _ _ _ hex hce _)
    | _ => trivial

mutual
/-- `rewriteRotWith` preserves `Expr.callsOk` unconditionally when `e₁`, `e₂` are `Wf`-related. -/
private theorem rewriteRotWith_callsOk {allowed : List SigEntry} {exits : List Sym} :
    (allowHdr : Bool) → (plan : RotPlan) →
    ∀ {rs : List Ty} {G : Ctx (OptArg UnitV) UnitV} {D : Ctx (RotL UnitV UnitL rs) UnitL}
      {e₁ : Expr (OptArg UnitV) (RotL UnitV UnitL rs) rs} {e₂ : Expr UnitV UnitL rs},
      Wf G D e₁ e₂ → RotCallsL allowed exits D → e₂.callsOk allowed exits →
      (rewriteRotWith allowHdr plan e₁).callsOk allowed exits
  | _, .leaf => fun hwf hD hc => by dsimp only [rewriteRotWith]; exact flatExpr_callsOk hwf hD hc
  | allowHdr, .letP p => fun hwf hD hc => by
    cases hwf with
    | let_ _ hk => dsimp [rewriteRotWith]; exact rewriteRotWith_callsOk allowHdr p (hk _ _) hD hc
    | _ => dsimp only [rewriteRotWith]; trivial
  | allowHdr, .loadP p => fun hwf hD hc => by
    cases hwf with
    | load _ _ hk =>
      dsimp only [rewriteRotWith]; exact rewriteRotWith_callsOk allowHdr p (hk _ ()) hD hc
    | _ => dsimp only [rewriteRotWith]; trivial
  | allowHdr, .storeP p => fun hwf hD hc => by
    cases hwf with
    | store _ _ hk => dsimp only [rewriteRotWith]; exact rewriteRotWith_callsOk allowHdr p hk hD hc
    | _ => dsimp only [rewriteRotWith]; trivial
  | allowHdr, .callP p => fun hwf hD hc => by
    cases hwf with
    | call _ _ hk =>
      dsimp only [rewriteRotWith]; exact ⟨hc.1, rewriteRotWith_callsOk allowHdr p (hk _ _) hD hc.2⟩
    | _ => dsimp only [rewriteRotWith]; trivial
  | allowHdr, .jnzP tp ep => fun hwf hD hc => by
    cases hwf with
    | jnz _ ht he =>
      dsimp only [rewriteRotWith]; exact ⟨rewriteRotWith_callsOk allowHdr tp ht hD hc.1,
        rewriteRotWith_callsOk allowHdr ep he hD hc.2⟩
    | @jump _ _ _ j₁ _ _ _ hj _ =>
      cases allowHdr <;> (cases tp <;> cases ep <;> dsimp only [rewriteRotWith])
      all_goals first | trivial | (have hdj := CtxPred.mem hD hj; cases j₁ with
        | expandOrKeep _ _ | keep _ | dead => trivial | expand _ => exact hdj _)
    | _ => dsimp only [rewriteRotWith]; cases allowHdr <;> first | trivial |
        (cases tp <;> cases ep <;> trivial)
  | allowHdr, .groupKeep bsP kP => fun hwf hD hc => by
    cases hwf with
    | @group _ _ sig b₁ b₂ _ _ hb hk =>
      dsimp only [rewriteRotWith]
      have hD' := CtxPred.append (rotCallsL_wrapKeepLabels allowed exits (Tup.units sig)) hD
      exact ⟨rewriteKeepB_callsOk allowHdr bsP (b₁ _) (b₂ _) (hb _ (Tup.units sig)) hD' hc.1,
        rewriteRotWith_callsOk allowHdr kP (hk _ (Tup.units sig)) hD' hc.2⟩
    | _ => dsimp only [rewriteRotWith]; trivial
  | allowHdr, .groupRot dir hdr contMasks exitMode contP exitP entryP => fun hwf hD hc => by
    cases hwf with
    | @group _ _ sig b₁ b₂ k₁ k₂ hb hk =>
      cases sig with
      | nil => dsimp only [rewriteRotWith]; trivial
      | cons ts sig' =>
        cases sig' with
        | cons _ _ => dsimp only [rewriteRotWith]; trivial
        | nil =>
          have hbc : ((b₂ ((), ())).get .here (Tup.units ts)).callsOk allowed exits :=
            Blocks.callsOk_get hc.1 .here
          have hDex := CtxPred.append (rotCallsL_exitLabels allowed exits ts ((), ())) hD
          have emitLoopCalls (mk : Tup (Arg UnitV) ts → Expr UnitV UnitL _)
              (hmk : ∀ args, (mk args).callsOk allowed exits) :
              (if isPartialMasks hdr contMasks then
                Expr.group (sig := [rotSig hdr contMasks ts, ts])
                  (fun (_, J_hdr, _) => .cons (fun rotParams => rewriteRotWith true contP
                    (rotBodyExpr dir hdr contMasks b₁ (.expandOrKeep mk J_hdr) rotParams))
                    (.cons (fun hdrParams => mk (toArgTup hdrParams)) .nil))
                  (fun _ => rewriteRotWith allowHdr entryP (k₁ (.expand mk, ())))
              else Expr.group (sig := [rotSig hdr contMasks ts])
                  (fun _ => .cons (fun rotParams => rewriteRotWith allowHdr contP
                    (rotBodyExpr dir hdr contMasks b₁ (.expand mk) rotParams)) .nil)
                  (fun _ => rewriteRotWith allowHdr entryP (k₁ (.expand mk, ())))).callsOk
                allowed exits := by
            have mkDc {D₀ : Ctx (RotL UnitV UnitL _) UnitL} (hD₀ : RotCallsL allowed exits D₀)
                (j : RotL UnitV UnitL _ ts) (hj : j = .expand mk ∨ j = .expandOrKeep mk ()) :
                RotCallsL allowed exits (Tup.zip (as := [ts]) (j, ()) ((), ()) ++ D₀) := by
              intro p hp
              cases hp with
              | head => rcases hj with rfl | rfl <;> exact hmk
              | tail _ hp' => exact hD₀ p hp'
            have mkPeel (j : RotL UnitV UnitL _ ts) := hdrPeel_callsOk (allowed := allowed)
              (exits := exits) (tail := ts) dir true hdr contMasks (Tup.units _) ((hb (j, ())
                ((), ())).get .here (someVarsToOpt (splitTail hdr contMasks (Tup.units _)))
                (Tup.units ts)) hbc
            have hK := rewriteRotWith_callsOk allowHdr entryP (hk (.expand mk, ()) ((), ()))
              (mkDc hD (.expand mk) (.inl rfl)) hc.2
            cases isPartialMasks hdr contMasks
            · simp only [Bool.false_eq_true, ↓reduceIte, Expr.callsOk, Blocks.callsOk]
              rcases mkPeel (.expand mk) with ⟨_, _, hwf_p, hc_p⟩
              exact ⟨⟨rewriteRotWith_callsOk allowHdr contP hwf_p (mkDc hD _ (.inl rfl)) hc_p,
                trivial⟩, hK⟩
            · simp only [↓reduceIte, Expr.callsOk, Blocks.callsOk]
              rcases mkPeel (.expandOrKeep mk ()) with ⟨_, _, hwf_p, hc_p⟩
              exact ⟨⟨rewriteRotWith_callsOk true contP hwf_p (mkDc hD _ (.inr rfl)) hc_p,
                hmk (toArgTup (Tup.units ts)), trivial⟩, hK⟩
          cases exitMode with
          | inline =>
            dsimp only [rewriteRotWith]
            let mk : Tup (Arg UnitV) ts → Expr UnitV UnitL _ := fun args => hdrEmit (tailC := ts)
              (tailX := ts) dir args args hdr contMasks [] ((b₁ (exitLabels ts)).get .here
              (someArgsToOpt args)) (fun r => .jump () r)
              (fun ex _ => rewriteRotWith allowHdr exitP ex)
            exact emitLoopCalls mk fun args => hdrEmit_callsOk dir args args hdr contMasks []
              ((hb (exitLabels ts) ((), ())).get .here _ _) hbc (fun _ => trivial)
              (fun _ _ _ hex hcex _ => rewriteRotWith_callsOk allowHdr exitP hex hDex hcex)
          | wrap xsMask hMasks =>
            dsimp only [rewriteRotWith, Expr.callsOk, Blocks.callsOk]
            rcases hdrPeel_callsOk (allowed := allowed) (exits := exits)
              (tail := filterTys ts xsMask) dir false hdr hMasks (Tup.units _) ((hb (exitLabels ts)
              ((), ())).get .here (tupWiden ts xsMask (splitTail hdr hMasks (Tup.units _)))
              (Tup.units ts)) hbc with ⟨_, _, hwf_px, hc_px⟩
            let mk : Tup (Arg UnitV) ts → Expr UnitV UnitL _ := fun args => hdrEmit (tailC := ts)
              (tailX := filterTys ts xsMask) dir args (tupSelectArgs ts xsMask args) hdr contMasks
              hMasks ((b₁ (exitLabels ts)).get .here (someArgsToOpt args)) (fun r => .jump () r)
              (fun _ e => .jump () e)
            refine ⟨⟨rewriteRotWith_callsOk allowHdr exitP hwf_px hDex hc_px, trivial⟩,
              emitLoopCalls mk fun args => hdrEmit_callsOk dir args (tupSelectArgs ts xsMask args)
                hdr contMasks hMasks ((hb (exitLabels ts) ((), ())).get .here _ _) hbc
                (fun _ => trivial) (fun _ _ _ _ _ _ => trivial)⟩
    | _ => dsimp only [rewriteRotWith]; trivial
where
  rewriteKeepB_callsOk : (allowHdr : Bool) → (ps : List RotPlan) →
      ∀ {rs : List Ty} {G : Ctx (OptArg UnitV) UnitV} {D : Ctx (RotL UnitV UnitL rs) UnitL}
        {sig : List (List Ty)} (bs₁ : Blocks (OptArg UnitV) (RotL UnitV UnitL rs) rs sig)
        (bs₂ : Blocks UnitV UnitL rs sig), WfB G D bs₁ bs₂ → RotCallsL allowed exits D →
        bs₂.callsOk allowed exits →
        (rewriteRotWith.rewriteKeepB allowHdr ps bs₁).callsOk allowed exits
    | allowHdr, [] => fun bs₁ bs₂ hbs hD hcbs => by
      cases hbs with
      | nil => dsimp only [rewriteRotWith.rewriteKeepB, flatExpr.flatBlocks]; simp [Blocks.callsOk]
      | cons hb hbs' =>
        dsimp only [rewriteRotWith.rewriteKeepB, flatExpr.flatBlocks]; simp only [Blocks.callsOk]
        exact ⟨flatExpr_callsOk (hb _ (Tup.units _)) hD hcbs.1,
          rewriteKeepB_callsOk allowHdr [] _ _ hbs' hD hcbs.2⟩
    | allowHdr, p :: ps => fun bs₁ bs₂ hbs hD hcbs => by
      cases hbs with
      | nil => dsimp only [rewriteRotWith.rewriteKeepB]; simp only [Blocks.callsOk]
      | cons hb hbs' =>
        dsimp only [rewriteRotWith.rewriteKeepB]; simp only [Blocks.callsOk]
        exact ⟨rewriteRotWith_callsOk allowHdr p (hb _ (Tup.units _)) hD hcbs.1,
          rewriteKeepB_callsOk allowHdr ps _ _ hbs' hD hcbs.2⟩
end

private theorem rewriteRot_callsOk {allowed : List SigEntry} {exits : List Sym} (plan : RotPlan)
    {rs : List Ty} {G : Ctx (OptArg UnitV) UnitV} {D : Ctx (RotL UnitV UnitL rs) UnitL}
    {e₁ : Expr (OptArg UnitV) (RotL UnitV UnitL rs) rs} {e₂ : Expr UnitV UnitL rs}
    (hwf : Wf G D e₁ e₂) (hD : RotCallsL allowed exits D) (hc : e₂.callsOk allowed exits) :
    (rewriteRot plan e₁).callsOk allowed exits := rewriteRotWith_callsOk false plan hwf hD hc

end RotImpl

open RotImpl LoopRotate

/-! ## Top-level `Func` and `Fn` theorems -/

/-- `Func.loopRotateWithPlan` preserves relational well-formedness `Func.Wf`. -/
theorem Func.loopRotateWithPlan_wf {as rs : List Ty} (plan : RotPlan) {f : Func as rs}
    (hf : f.Wf) : (Func.loopRotateWithPlan plan f).Wf := by
  unfold Func.loopRotateWithPlan; split
  · intro _ _ _ _ xs₁ xs₂
    exact rewriteRot_wf plan (someVarsToOpt_optWfRel xs₁ xs₂) (CtxPred.nil _) (hf _ _ _ _ _ _)
  · exact hf

/-- `Func.loopRotate` preserves `Func.Wf` unconditionally (even without `f.Wf`). -/
theorem Func.loopRotate_wf_uncond {as rs : List Ty} (f : Func as rs)
    (cfg : RotConfig := defaultRotConfig) : (Func.loopRotate f cfg).Wf := by
  unfold Func.loopRotate; dsimp only; split
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
  unfold Func.loopRotateWithPlan; split
  · exact rewriteRot_wp plan (hf K (OptArg Val) BoolL _ _ _) (hf K K BoolL BoolL _ _)
      (hf (OptArg Val) Val _ Cont (someVarsToOpt xs) xs) ‹_›
      (by simpa using NoneDeadOpt.append_someVars (CtxPred.nil _) (Tup.levels as 0) xs)
      (by simpa using SomeValEq.append_someVars PassFlatKit.SomeValCtx.nil xs)
      (PassFlatKit.DiagCtx.zip_self _) (fun _ hp => by cases hp) (fun _ hp => by cases hp) m h
  · exact h

/-- `Func.loopRotate` refines `Func.spec` for any well-formed function `f`. -/
theorem Func.loopRotate_spec {as rs : List Ty} {f : Func as rs} (hf : f.Wf)
    (cfg : RotConfig := defaultRotConfig) {Γ : Env} {xs : Tup Val as} {m : Mem 64}
    {Q : Post rs} {X : XPost} (h : Func.spec Γ f xs m Q X) :
    Func.spec Γ (Func.loopRotate f cfg) xs m Q X := by
  unfold Func.loopRotate; dsimp only; split
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

/-- `Func.loopRotateWithPlan` preserves `Expr.callsOk` for any well-formed `f`. -/
theorem Func.loopRotateWithPlan_callsOk {allowed : List SigEntry} {exits : List Sym}
    {as rs : List Ty} (plan : RotPlan) {f : Func as rs} (hf : f.Wf)
    (hc : (f (fun _ => Unit) (fun _ => Unit) (Tup.units as)).callsOk allowed exits) :
    ((Func.loopRotateWithPlan plan f) (fun _ => Unit) (fun _ => Unit) (Tup.units as)).callsOk
      allowed exits := by
  unfold Func.loopRotateWithPlan
  cases validateRotPlan plan (f K BoolL (Tup.levels as 0)) as.length with
  | some _ => exact rewriteRot_callsOk plan (hf (OptArg UnitV) UnitV (RotL UnitV UnitL rs) UnitL
      (someVarsToOpt (Tup.units as)) (Tup.units as)) (fun _ hp => by cases hp) hc
  | none => exact hc

/-- `Func.loopRotate` preserves `Expr.callsOk` for any well-formed `f`. -/
theorem Func.loopRotate_callsOk {allowed : List SigEntry} {exits : List Sym}
    {as rs : List Ty} {f : Func as rs} (hf : f.Wf) (cfg : RotConfig := defaultRotConfig)
    (hc : (f (fun _ => Unit) (fun _ => Unit) (Tup.units as)).callsOk allowed exits) :
    ((Func.loopRotate f cfg) (fun _ => Unit) (fun _ => Unit) (Tup.units as)).callsOk
      allowed exits := by
  unfold Func.loopRotate
  have hRen := (PassFlatKit.Func.renorm_callsOk hf (allowed := allowed) (exits := exits)).2 hc
  split
  · exact Func.loopRotateWithPlan_callsOk _ (Func.wf_of_denote _ rfl) hRen
  · exact hRen

/-- `Fn.loopRotate` preserves `Fn.callsOk` for any well-formed `fn`. -/
theorem Fn.loopRotate_callsOk {allowed : List SigEntry} {exits : List Sym}
    {fn : Fn} (hf : fn.Wf) (cfg : RotConfig := defaultRotConfig)
    (hc : fn.callsOk allowed exits) : (Fn.loopRotate fn cfg).callsOk allowed exits :=
  Func.loopRotate_callsOk hf cfg hc

end LeanQbe.T

