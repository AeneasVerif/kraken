module

public import LeanQbe.T.OptFlatLoop
public import LeanQbe.T.OptFlatLoopLemmas0
import LeanQbe.T.OptFlatLoopLemmas1
import LeanQbe.T.FlatDirectLemmas
import LeanQbe.T.PassFlatKit
import LeanQbe.T.OptFlatSimKit
import LeanQbe.T.LoopRotateLemmas

/-!
# Loop-Rotation Rewriter Equivalence Proofs (`loopRotateFlat_eq`)

Proves exact `=` correspondence (`std3` axioms only) between native `TFlat`
`OptFlatLoop.loopRotateFlat` and `Func.loopRotate`. Re-exports `OptFlatLoopLemmas0` (`licmFlat`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T
namespace OptFlatLoop

open OptFlatPlanKit
open OptFlatSimKit
open LoopRotate

/-! ## 1. Zero-Shift Label Match Relation & `flatExprFlat` Equivalence -/

private def RotLFlatMatch {rs : List Ty} :
    (ts : List Ty) → RotLFlat rs ts → RotL K KL rs ts → Prop
  | _, .keep l₁, .keep l₂ => l₁ = l₂
  | _, .expand f₁, .expand f₂ =>
    ∀ (od ld : Nat) (args : Tup (Arg K) _),
      f₁ od ld args = toTFlat (f₂ args) od ld
  | _, .expandOrKeep f₁ l₁, .expandOrKeep f₂ l₂ =>
    l₁ = l₂ ∧
    ∀ (od ld : Nat) (args : Tup (Arg K) _),
      f₁ od ld args = toTFlat (f₂ args) od ld
  | _, .dead, .dead => True
  | _, _, _ => False

private theorem wrapKeepLabelsFlat_rel {rs : List Ty} :
    {sig : List (List Ty)} → (ls : Tup KL sig) →
    TRel (RotLFlatMatch (rs := rs)) (wrapKeepLabelsFlat ls) (wrapKeepLabels ls)
  | [], () => TRel.nil
  | _ :: _, (_, ls) => TRel.cons rfl (wrapKeepLabelsFlat_rel ls)

private theorem flatExprFlat_both {rs : List Ty} :
    (∀ (tf : TFlat rs) {Γ Δ vs ls inVD outVD inLD outLD inVE inLE} (_ : Unit),
      CtxTypes Γ vs → CtxTypes Δ ls → TrieCtxMatch inVD inVE vs →
      (CtxTypes Δ ls ∧ TrieRelMatch (RotLFlatMatch (rs := rs)) inLD inLE ls) →
      tf.wfCheck Γ Δ = true →
      toTFlat (flatExpr (denote (OptArg K) (RotL K KL rs) tf vs ls)) outVD outLD =
        flatExprFlat tf inVD inVE inLD inLE outVD outLD) ∧
    (∀ {sig : List (List Ty)} (tb : TBlocks rs sig)
      {Γ Δ vs ls inVD outVD inLD outLD inVE inLE} (_ : Unit),
      CtxTypes Γ vs → CtxTypes Δ ls → TrieCtxMatch inVD inVE vs →
      (CtxTypes Δ ls ∧ TrieRelMatch (RotLFlatMatch (rs := rs)) inLD inLE ls) →
      tb.wfCheck Γ Δ = true →
      toTBlocks (flatExpr.flatBlocks (denoteB (OptArg K) (RotL K KL rs) tb vs ls)) outVD outLD =
        flatBlocksFlat tb inVD inVE inLD inLE outVD outLD) := by
  refine relSim_mutual
    (LR := fun Δ inLD inLE ls =>
      CtxTypes Δ ls ∧ TrieRelMatch (RotLFlatMatch (rs := rs)) inLD inLE ls) ⟨
    @fun ts _ _ _ _ _ outVD _ _ _ _ _ op k hΓ _ hm hlr hwf ih => by
      obtain ⟨ha, hk⟩ := wf_let hwf
      have hargs := denoteArgs_eq_some_resolveEnvArgs hΓ hm op.args ha
      dsimp only [denote, flatExprFlat]; rw [hargs]; dsimp only [flatExpr, flatOptOp, toTFlat]
      exact congrArg (TFlat.let_ _)
        (ih () (CtxTypes.push _ hΓ)
          (trieCtxMatch_insertTupEnv hm (someVarsToOpt (Tup.levels ts outVD))) hlr hk),
    @fun _ _ _ _ _ outVD _ _ _ _ _ t a k hΓ _ hm hlr hwf ih => by
      obtain ⟨ha, hk⟩ := wf_load hwf
      have ha' := denoteArg_eq_some_resolveEnvArg hΓ hm a ha
      dsimp only [denote, flatExprFlat]; rw [ha']; dsimp only [flatExpr, toTFlat]
      exact congrArg (TFlat.load t _) (ih () (.cons hΓ) (hm.cons t (some (.var outVD))) hlr hk),
    fun _ v a k hΓ _ hm hlr hwf ih => by
      obtain ⟨hv, ha, hk⟩ := wf_store hwf
      have hv' := denoteArg_eq_some_resolveEnvArg hΓ hm v hv
      have ha' := denoteArg_eq_some_resolveEnvArg hΓ hm a ha
      dsimp only [denote, flatExprFlat]; rw [hv', ha']; dsimp only [flatExpr, toTFlat]
      exact congrArg (TFlat.store _ _) (ih () hΓ hm hlr hk),
    @fun _ _ _ _ _ _ outVD _ _ _ _ _ f bs args k hΓ _ hm hlr hwf ih => by
      obtain ⟨ha, hk⟩ := wf_call hwf
      have hargs := denoteArgs_eq_some_resolveEnvArgs hΓ hm args ha
      dsimp only [denote, flatExprFlat]; rw [hargs]; dsimp only [flatExpr, toTFlat]
      exact congrArg (TFlat.call f bs _)
        (ih () (CtxTypes.push _ hΓ)
          (trieCtxMatch_insertTupEnv hm (someVarsToOpt (Tup.levels bs outVD))) hlr hk),
    fun _ c t e hΓ _ hm _ hwf iht ihe => by
      obtain ⟨hc, ht, he⟩ := wf_jnz hwf
      have hca := denoteArg_eq_some_resolveEnvArg hΓ hm c hc
      dsimp only [denote, flatExprFlat]; rw [hca]; dsimp only [flatExpr, toTFlat]
      exact congr (congrArg (TFlat.jnz _) (iht () ht)) (ihe () he),
    @fun _ _ _ _ _ _ outVD _ outLD _ _ _ j args hΓ _ hm hlr hwf => by
      obtain ⟨hj, ha⟩ := wf_jump hwf
      obtain ⟨w₁, w₂, hres, hlk, hmrel⟩ := hlr.2.resolveLabel_rel hlr.1 hj
      have hargs := denoteArgs_eq_some_resolveEnvArgs hΓ hm args ha
      dsimp only [denote, flatExprFlat]; rw [hlk, hargs, hres]
      cases w₁ <;> cases w₂ <;> simp only [RotLFlatMatch] at hmrel
      · subst hmrel; rfl
      · exact (hmrel outVD outLD _).symm
      · exact (hmrel.2 outVD outLD _).symm
      · rfl,
    fun _ vs' hΓ _ hm _ hwf => by
      have hvs := denoteArgs_eq_some_resolveEnvArgs hΓ hm vs' hwf
      dsimp only [denote, flatExprFlat]; rw [hvs]; rfl,
    fun _ _ args hΓ _ hm _ hwf => by
      have hargs := denoteArgs_eq_some_resolveEnvArgs hΓ hm args hwf
      dsimp only [denote, flatExprFlat]; rw [hargs]; rfl,
    fun _ _ _ _ _ _ => rfl,
    @fun sig _ Δ _ ls _ outVD _ outLD _ _ _ bodies k _ hΔ _ hlr hwf ihB ihK => by
      obtain ⟨hb, hk⟩ := wf_group hwf
      dsimp only [denote, flatExprFlat, flatExpr, toTFlat]
      have hlr' : CtxTypes (pushTypes sig Δ) (pushTup (wrapKeepLabels (Tup.levels sig outLD)) ls) ∧
          TrieRelMatch (RotLFlatMatch (rs := rs)) (_ + sig.length)
            (insertTupEnv _ _ (wrapKeepLabelsFlat (Tup.levels sig outLD)))
            (pushTup (wrapKeepLabels (Tup.levels sig outLD)) ls) :=
        ⟨ctxTypes_pushTup_rev _ hΔ, hlr.2.pushTup (wrapKeepLabelsFlat_rel (Tup.levels sig outLD))⟩
      rw [ihB (outLD' := outLD + sig.length) () (ctxTypes_pushTup_rev _ hΔ) hlr' hb,
        ihK (outLD' := outLD + sig.length) () (ctxTypes_pushTup_rev _ hΔ) hlr' hk],
    fun _ _ _ _ _ _ => rfl,
    @fun ts _ _ _ _ _ _ outVD _ outLD _ _ _ b bs hΓ _ hm hlr hwf ihb ihbs => by
      obtain ⟨hb, hbs⟩ := wf_cons hwf
      dsimp only [denoteB, flatBlocksFlat, flatExpr.flatBlocks, toTBlocks]
      exact congr (congrArg TBlocks.cons
        (ihb (outVD' := outVD + ts.length) (outLD' := outLD) () (CtxTypes.push _ hΓ)
          (trieCtxMatch_insertTupEnv hm (someVarsToOpt (Tup.levels ts outVD))) hlr hb))
        (ihbs () hbs)⟩

/-! ## 2. Header Peel & Emit Equivalence (`hdrPeelFlat`, `hdrEmitFlat`) -/

private theorem hdr_inj_eq {rs : List Ty} {sh2 sh : Trie Unit} {tF2 eF2 tF eF : TFlat rs}
    {nv2 nv' : Nat} (h : some (sh2, tF2, eF2, nv2) = some (sh, tF, eF, nv')) :
    tF2 = tF ∧ eF2 = eF ∧ nv2 = nv' := by
  injection h with h0
  exact ⟨congrArg (·.2.1) h0, congrArg (·.2.2.1) h0, congrArg (·.2.2.2) h0⟩

private theorem validateHdrFlat_let_some {rs dts dts' : List Ty} {ss : HdrPlan}
    {op : Op K dts'} {k : TFlat rs} {nv : Nat} {sh : Trie Unit} {tF eF : TFlat rs} {nv' : Nat}
    (hvh : validateHdrFlat (.let_ dts :: ss) (.let_ op k) nv = some (sh, tF, eF, nv')) :
    ∃ (heq : dts = dts') (sh2 : Trie Unit),
      isSafeHdrOp op.code = true ∧
      validateHdrFlat ss k (nv + dts.length) = some (sh2, tF, eF, nv') ∧
      (tysDecEq dts dts' = isTrue heq) := by
  dsimp only [validateHdrFlat] at hvh
  cases hdec : tysDecEq dts dts' with
  | isFalse _ => rw [hdec] at hvh; contradiction
  | isTrue heq =>
    subst heq; rw [hdec] at hvh; dsimp only at hvh
    cases hsafe : isSafeHdrOp op.code with
    | false => simp [hsafe] at hvh
    | true =>
      simp only [hsafe, ↓reduceIte] at hvh
      cases hvh2 : validateHdrFlat ss k (nv + dts.length) with
      | none => rw [hvh2] at hvh; contradiction
      | some val =>
        rcases val with ⟨sh2, tF2, eF2, nv2⟩; rw [hvh2] at hvh
        rcases hdr_inj_eq hvh with ⟨rfl, rfl, rfl⟩
        exact ⟨rfl, sh2, rfl, rfl, rfl⟩

private theorem validateHdrFlat_load_some {rs : List Ty} {t t' : Ty} {ss : HdrPlan}
    {a : Arg K i64} {k : TFlat rs} {nv : Nat} {sh : Trie Unit} {tF eF : TFlat rs} {nv' : Nat}
    (hvh : validateHdrFlat (.load t :: ss) (.load t' a k) nv = some (sh, tF, eF, nv')) :
    ∃ (heq : t = t') (sh2 : Trie Unit),
      validateHdrFlat ss k (nv + 1) = some (sh2, tF, eF, nv') ∧ (tyDecEq t t' = isTrue heq) := by
  dsimp only [validateHdrFlat] at hvh
  cases hdec : tyDecEq t t' with
  | isFalse _ => rw [hdec] at hvh; contradiction
  | isTrue heq =>
    subst heq; rw [hdec] at hvh; dsimp only at hvh
    cases hvh2 : validateHdrFlat ss k (nv + 1) with
    | none => rw [hvh2] at hvh; contradiction
    | some val =>
      rcases val with ⟨sh2, tF2, eF2, nv2⟩; rw [hvh2] at hvh
      rcases hdr_inj_eq hvh with ⟨rfl, rfl, rfl⟩
      exact ⟨rfl, sh2, rfl, rfl⟩

private theorem hdrPeelFlat_of_validateHdr {rs tail : List Ty} (dir wantCont : Bool) :
    (hdr : HdrPlan) → (ms : List (List Bool)) →
    (params : Tup K (stepMasksSig hdr ms tail)) →
    (b : TFlat rs) → {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × OptArg K t)} →
    {nv inVD : Nat} → {inVE : Trie ((t : Ty) × OptArg K t)} →
    {sh : Trie Unit} → {tF eF : TFlat rs} → {nv' : Nat} →
    validateHdrFlat hdr b nv = some (sh, tF, eF, nv') →
    CtxTypes Γ vs → TrieCtxMatch inVD inVE vs → b.wfCheck Γ Δ = true →
    ∃ (iv' : Nat) (ie' : Trie ((t : Ty) × OptArg K t)) (Γ' : List Ty)
      (vs' : List ((t : Ty) × OptArg K t)),
      iv' = inVD + hdrStepCount hdr ∧
      hdrPeelFlat dir wantCont hdr ms params b inVD inVE =
        some (if wantCont == dir then tF else eF, iv', ie') ∧
      CtxTypes Γ' vs' ∧ TrieCtxMatch iv' ie' vs' ∧
      (if wantCont == dir then tF else eF).wfCheck Γ' Δ = true ∧
      (∀ (ls : List ((ts : List Ty) × RotL K KL rs ts)), CtxTypes Δ ls →
        hdrPeel dir wantCont hdr ms params (denote (OptArg K) (RotL K KL rs) b vs ls) =
          denote (OptArg K) (RotL K KL rs) (if wantCont == dir then tF else eF) vs' ls)
  | [], _, _, b, Γ, _, vs, _, inVD, inVE, _, _, _, _, hvh, hΓ, hm, hwf => by
    cases b with
    | jnz c _ _ =>
      obtain ⟨hc, ht, he⟩ := wf_jnz hwf
      dsimp only [validateHdrFlat] at hvh; cases hvh
      refine ⟨inVD, inVE, Γ, vs, rfl, rfl, hΓ, hm,
        (by cases wantCont == dir <;> first | exact ht | exact he), ?_⟩
      intro ls _
      have hca := denoteArg_eq_some_resolveEnvArg hΓ hm c hc
      dsimp only [denote]; rw [hca]; dsimp only [hdrPeel]; cases wantCont == dir <;> rfl
    | _ => dsimp only [validateHdrFlat] at hvh; contradiction
  | .let_ dts :: ss, ms, params, b, Γ, Δ, vs, nv, inVD, inVE, _, tF, eF, nv',
      hvh, hΓ, hm, hwf => by
    cases b with
    | let_ op k =>
      obtain ⟨ha, hk⟩ := wf_let hwf
      obtain ⟨heq, _, _, hvh2, hdec⟩ := validateHdrFlat_let_some hvh
      subst heq
      let hsp := LoopRotate.tupSplit (filterTys dts (ms.headD [])) params
      obtain ⟨iv', ie', Γ', vs', hiv', hpeel, hΓ', hm', hwf', hden⟩ :=
        hdrPeelFlat_of_validateHdr dir wantCont ss ms.tail hsp.2 k
          (Γ := pushTypes dts Γ) (Δ := Δ)
          (vs := pushTup (tupWiden dts (ms.headD []) hsp.1) vs)
          (nv := nv + dts.length) (inVD := inVD + dts.length)
          (inVE := insertTupEnv inVD inVE (tupWiden dts (ms.headD []) hsp.1))
          hvh2 (CtxTypes.push _ hΓ) (trieCtxMatch_insertTupEnv hm _) hk
      refine ⟨iv', ie', Γ', vs', ?_, ?_, hΓ', hm', hwf', ?_⟩
      · dsimp only [hdrStepCount, HdrStep.tys] at hiv' ⊢; omega
      · dsimp only [hdrPeelFlat]; rw [hdec]; exact hpeel
      · intro ls hΔ
        have hargs := denoteArgs_eq_some_resolveEnvArgs hΓ hm op.args ha
        dsimp only [denote]; rw [hargs]; dsimp only [hdrPeel]; rw [hdec]; dsimp only
        exact hden ls hΔ
    | _ => dsimp only [validateHdrFlat] at hvh; contradiction
  | .load t :: ss, ms, params, b, Γ, Δ, vs, nv, inVD, inVE, _, tF, eF, nv',
      hvh, hΓ, hm, hwf => by
    cases b with
    | load t' a k =>
      obtain ⟨ha, hk⟩ := wf_load hwf
      obtain ⟨heq, _, hvh2, hdec⟩ := validateHdrFlat_load_some hvh
      subst heq
      let hsp := LoopRotate.tupSplit (filterTys [t] (ms.headD [])) params
      let y1 : OptArg K t := (tupWiden [t] (ms.headD []) hsp.1).1
      obtain ⟨iv', ie', Γ', vs', hiv', hpeel, hΓ', hm', hwf', hden⟩ :=
        hdrPeelFlat_of_validateHdr dir wantCont ss ms.tail hsp.2 k
          (Γ := t :: Γ) (Δ := Δ) (vs := ⟨t, y1⟩ :: vs)
          (nv := nv + 1) (inVD := inVD + 1) (inVE := inVE.insert inVD ⟨t, y1⟩)
          hvh2 (.cons hΓ) (hm.cons t y1) hk
      refine ⟨iv', ie', Γ', vs', ?_, ?_, hΓ', hm', hwf', ?_⟩
      · simp only [hdrStepCount, HdrStep.tys, List.length_cons, List.length_nil] at hiv' ⊢; omega
      · dsimp only [hdrPeelFlat]; rw [hdec]; exact hpeel
      · intro ls hΔ
        have ha' := denoteArg_eq_some_resolveEnvArg hΓ hm a ha
        dsimp only [denote]; rw [ha']; dsimp only [hdrPeel]; rw [hdec]; dsimp only
        exact hden ls hΔ
    | _ => dsimp only [validateHdrFlat] at hvh; contradiction

private theorem hdrEmitFlat_eq {rs tailC tailX : List Ty} (dir : Bool)
    (tailCArgs : Tup (Arg K) tailC) (tailXArgs : Tup (Arg K) tailX) :
    (hdr : HdrPlan) → (cMs xMs : List (List Bool)) →
    (b : TFlat rs) → {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × OptArg K t)} → {ls : List ((ts : List Ty) × RotL K KL rs ts)} →
    {inVD outVD outLD nv : Nat} → {inVE : Trie ((t : Ty) × OptArg K t)} →
    {sh : Trie Unit} → {tF eF : TFlat rs} → {nv' : Nat} →
    validateHdrFlat hdr b nv = some (sh, tF, eF, nv') →
    CtxTypes Γ vs → TrieCtxMatch inVD inVE vs → CtxTypes Δ ls → b.wfCheck Γ Δ = true →
    (kC : Tup (Arg K) (stepMasksSig hdr cMs tailC) → Expr K KL rs) →
    (kCFlat : Nat → Tup (Arg K) (stepMasksSig hdr cMs tailC) → TFlat rs) →
    (∀ (od : Nat) (cargs : Tup (Arg K) (stepMasksSig hdr cMs tailC)),
      toTFlat (kC cargs) od outLD = kCFlat od cargs) →
    (kX : Expr (OptArg K) (RotL K KL rs) rs →
      Tup (Arg K) (stepMasksSig hdr xMs tailX) → Expr K KL rs) →
    (kXFlat : TFlat rs → Nat → Trie ((t : Ty) × OptArg K t) → Nat →
      Tup (Arg K) (stepMasksSig hdr xMs tailX) → TFlat rs) →
    (∀ (iv' : Nat) (ie' : Trie ((t : Ty) × OptArg K t)) (Γ' : List Ty)
      (vs' : List ((t : Ty) × OptArg K t)) (od : Nat)
      (xargs : Tup (Arg K) (stepMasksSig hdr xMs tailX)),
      iv' = inVD + hdrStepCount hdr →
      CtxTypes Γ' vs' → TrieCtxMatch iv' ie' vs' →
      (if dir then eF else tF).wfCheck Γ' Δ = true →
      toTFlat (kX (denote (OptArg K) (RotL K KL rs) (if dir then eF else tF) vs' ls) xargs)
        od outLD =
        kXFlat (if dir then eF else tF) iv' ie' od xargs) →
    toTFlat (hdrEmit dir tailCArgs tailXArgs hdr cMs xMs
      (denote (OptArg K) (RotL K KL rs) b vs ls) kC kX) outVD outLD =
      hdrEmitFlat dir tailCArgs tailXArgs hdr cMs xMs b inVD inVE outVD outLD kCFlat kXFlat
  | [], _, _, b, Γ, _, vs, _, inVD, outVD, _, _, inVE,
      _, _, _, _, hvh, hΓ, hm, _, hwf, _, _, hkC, _, _, hkX => by
    cases b with
    | jnz c _ _ =>
      obtain ⟨hc, ht, he⟩ := wf_jnz hwf
      dsimp only [validateHdrFlat] at hvh; cases hvh
      have hca := denoteArg_eq_some_resolveEnvArg hΓ hm c hc
      dsimp only [denote, hdrEmitFlat]; rw [hca]; dsimp only [hdrEmit]
      cases dir <;> simp only [Bool.false_eq_true, ↓reduceIte, toTFlat]
      · exact congr (congrArg (TFlat.jnz _) (hkX inVD inVE Γ vs outVD tailXArgs rfl hΓ hm ht))
          (hkC outVD tailCArgs)
      · exact congr (congrArg (TFlat.jnz _) (hkC outVD tailCArgs))
          (hkX inVD inVE Γ vs outVD tailXArgs rfl hΓ hm he)
    | _ => dsimp only [validateHdrFlat] at hvh; contradiction
  | .let_ dts :: ss, cMs, xMs, b, Γ, Δ, vs, _, inVD, outVD, _, nv, inVE, _, tF, eF, nv',
      hvh, hΓ, hm, hΔ, hwf, kC, kCFlat, hkC, kX, kXFlat, hkX => by
    cases b with
    | let_ op k =>
      obtain ⟨ha, hk⟩ := wf_let hwf
      obtain ⟨heq, _, _, hvh2, hdec⟩ := validateHdrFlat_let_some hvh
      subst heq
      have hargs := denoteArgs_eq_some_resolveEnvArgs hΓ hm op.args ha
      dsimp only [denote, hdrEmitFlat]; rw [hargs]; dsimp only [hdrEmit]; rw [hdec]
      dsimp only [flatOptOp, toTFlat]
      let selC := tupSelectArgs dts (cMs.headD []) (toArgTup (Tup.levels dts outVD))
      let selX := tupSelectArgs dts (xMs.headD []) (toArgTup (Tup.levels dts outVD))
      exact congrArg (TFlat.let_ _) (hdrEmitFlat_eq dir tailCArgs tailXArgs ss cMs.tail xMs.tail k
        hvh2 (CtxTypes.push _ hΓ)
        (trieCtxMatch_insertTupEnv hm (someVarsToOpt (Tup.levels dts outVD))) hΔ hk
        (fun rest => kC (LoopRotate.tupAppend selC rest))
        (fun od rest => kCFlat od (LoopRotate.tupAppend selC rest)) (fun od _ => hkC od _)
        (fun ex rest => kX ex (LoopRotate.tupAppend selX rest))
        (fun ex iv ie od rest => kXFlat ex iv ie od (LoopRotate.tupAppend selX rest))
        (fun iv' ie' Γ' vs' od _ hiv' hΓ' hm' hwf' => hkX iv' ie' Γ' vs' od _
          (by dsimp only [hdrStepCount, HdrStep.tys] at hiv' ⊢; omega) hΓ' hm' hwf'))
    | _ => dsimp only [validateHdrFlat] at hvh; contradiction
  | .load t :: ss, cMs, xMs, b, Γ, Δ, vs, _, inVD, outVD, _, nv, inVE, _, tF, eF, nv',
      hvh, hΓ, hm, hΔ, hwf, kC, kCFlat, hkC, kX, kXFlat, hkX => by
    cases b with
    | load t' a k =>
      obtain ⟨ha, hk⟩ := wf_load hwf
      obtain ⟨heq, _, hvh2, hdec⟩ := validateHdrFlat_load_some hvh
      subst heq
      have ha' := denoteArg_eq_some_resolveEnvArg hΓ hm a ha
      dsimp only [denote, hdrEmitFlat]; rw [ha']; dsimp only [hdrEmit]; rw [hdec]
      dsimp only [toTFlat]
      let selC := tupSelectArgs [t] (cMs.headD []) ((.var outVD : Arg K t), ())
      let selX := tupSelectArgs [t] (xMs.headD []) ((.var outVD : Arg K t), ())
      exact congrArg (TFlat.load t _) (hdrEmitFlat_eq dir tailCArgs tailXArgs ss cMs.tail xMs.tail k
        hvh2 (.cons hΓ) (hm.cons t (some (.var outVD))) hΔ hk
        (fun rest => kC (LoopRotate.tupAppend selC rest))
        (fun od rest => kCFlat od (LoopRotate.tupAppend selC rest)) (fun od _ => hkC od _)
        (fun ex rest => kX ex (LoopRotate.tupAppend selX rest))
        (fun ex iv ie od rest => kXFlat ex iv ie od (LoopRotate.tupAppend selX rest))
        (fun iv' ie' Γ' vs' od _ hiv' hΓ' hm' hwf' => hkX iv' ie' Γ' vs' od _
          (by simp only [hdrStepCount, HdrStep.tys, List.length_cons, List.length_nil] at hiv' ⊢
              omega)
          hΓ' hm' hwf'))
    | _ => dsimp only [validateHdrFlat] at hvh; contradiction

/-! ## 3. Main `rewriteRotWithFlat` Equivalence & `loopRotateFlat_eq` -/

private abbrev ValEx (allowHdr : Bool) (p : RotPlan) {rs : List Ty}
    (tf : TFlat rs) (nv inLD : Nat) : Prop :=
  ∃ inLEb, (validateRotPlanWithFlat allowHdr p tf nv inLD inLEb).isSome

private abbrev ValExB (allowHdr : Bool) (ps : List RotPlan) {rs : List Ty}
    {sig : List (List Ty)} (tb : TBlocks rs sig) (nv inLD : Nat) : Prop :=
  ∃ inLEb, (validateRotPlanWithFlat.validateKeepBFlat allowHdr ps tb nv inLD inLEb).isSome

private theorem isSome_bind {α β : Type} {x : Option α} {f : α → Option β}
    (h : (Option.bind x f).isSome) : x.isSome := by
  cases x with | none => simp at h | some _ => rfl

private theorem isSome_bind2 {α β γ : Type} {x : Option α} {y : Option β}
    {f : α → β → Option γ} (h : (Option.bind x (fun a => Option.bind y (f a))).isSome) :
    y.isSome := by
  cases hx : x with
  | none => simp [hx] at h
  | some a =>
    rw [hx] at h; dsimp only [Option.bind] at h
    exact isSome_bind h

private theorem valEx_groupRot {rs ts : List Ty} {allowHdr dir : Bool} {hdr : HdrPlan}
    {contMasks : List (List Bool)} {exitMode : ExitMode} {contP exitP entryP : RotPlan}
    {b k : TFlat rs} {inVD inLD : Nat} {inLEb : Trie ((ts : List Ty) × BoolL ts)}
    {sh : Trie Unit} {armT armE : TFlat rs} {nv' : Nat}
    (hvh : validateHdrFlat hdr b (inVD + ts.length) = some (sh, armT, armE, nv'))
    (hval : (validateRotPlanWithFlat allowHdr
        (.groupRot dir hdr contMasks exitMode contP exitP entryP)
        (@TFlat.group rs [ts] (.cons (ts := ts) b .nil) k) inVD inLD inLEb).isSome) :
    ValEx (allowHdr || isPartialMasks hdr contMasks) contP (if dir then armT else armE)
        (inVD + ts.length + hdrStepCount hdr) (inLD + 1) ∧
      ValEx allowHdr exitP (if dir then armE else armT)
        (inVD + ts.length + hdrStepCount hdr) (inLD + 1) ∧
      ValEx allowHdr entryP k inVD (inLD + 1) := by
  dsimp only [validateRotPlanWithFlat] at hval; rw [hvh] at hval
  simp only [Bind.bind, Option.bind] at hval
  cases hsc : validateRotPlanWithFlat (allowHdr || isPartialMasks hdr contMasks) contP
      (if dir then armT else armE) (inVD + ts.length + hdrStepCount hdr) (inLD + 1)
      (inLEb.insert inLD ⟨ts, true⟩) with
  | none => rw [hsc] at hval; contradiction
  | some _ =>
    rw [hsc] at hval; dsimp only at hval
    cases hsx : validateRotPlanWithFlat allowHdr exitP (if dir then armE else armT)
        (inVD + ts.length + hdrStepCount hdr) (inLD + 1) (inLEb.insert inLD ⟨ts, false⟩) with
    | none => rw [hsx] at hval; contradiction
    | some _ =>
      rw [hsx] at hval; dsimp only at hval
      refine ⟨⟨_, by rw [hsc]; rfl⟩, ⟨_, by rw [hsx]; rfl⟩, ⟨inLEb.insert inLD ⟨ts, true⟩, ?_⟩⟩
      cases hse : validateRotPlanWithFlat allowHdr entryP k inVD (inLD + 1)
          (inLEb.insert inLD ⟨ts, true⟩) with
      | none => rw [hse] at hval; contradiction
      | some _ => rfl

local macro "rot_miss" : tactic =>
  `(tactic| (dsimp only [validateRotPlanWithFlat] at *; contradiction))

mutual
private theorem rewriteRotWithFlat_eq {rs : List Ty} (allowHdr : Bool) :
    (plan : RotPlan) → (tf : TFlat rs) → {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × OptArg K t)} → {ls : List ((ts : List Ty) × RotL K KL rs ts)} →
    {inVD inLD outVD outLD : Nat} →
    {inVE : Trie ((t : Ty) × OptArg K t)} →
    {inLE : Trie ((ts : List Ty) × RotLFlat rs ts)} →
    ValEx allowHdr plan tf inVD inLD →
    CtxTypes Γ vs → TrieCtxMatch inVD inVE vs →
    CtxTypes Δ ls → TrieRelMatch (RotLFlatMatch (rs := rs)) inLD inLE ls →
    tf.wfCheck Γ Δ = true →
    toTFlat (rewriteRotWith allowHdr plan (denote (OptArg K) (RotL K KL rs) tf vs ls))
        outVD outLD =
      rewriteRotWithFlat allowHdr plan tf inVD inVE inLD inLE outVD outLD
  | .leaf, tf, Γ, Δ, vs, ls, _, _, _, _, _, _, _, hΓ, hm, hΔ, hrl, hwf => by
    rw [rewriteRotWith.eq_1]
    exact flatExprFlat_both.1 tf () hΓ hΔ hm ⟨hΔ, hrl⟩ hwf
  | .letP p, tf, Γ, Δ, vs, ls, inVD, inLD, outVD, outLD, inVE, inLE,
      hval, hΓ, hm, hΔ, hrl, hwf => by
    rcases hval with ⟨inLEb, hval⟩
    cases tf with
    | let_ op k =>
      rename_i ts
      obtain ⟨ha, hk⟩ := wf_let hwf
      dsimp only [validateRotPlanWithFlat] at hval
      have hval' : ValEx allowHdr p k (inVD + ts.length) inLD := ⟨inLEb, isSome_bind hval⟩
      dsimp only [denote, rewriteRotWithFlat]
      rw [denoteArgs_eq_some_resolveEnvArgs hΓ hm op.args ha, rewriteRotWith.eq_2]
      dsimp only [flatOptOp, toTFlat]
      exact congrArg (TFlat.let_ _) (rewriteRotWithFlat_eq allowHdr p k hval' (CtxTypes.push _ hΓ)
        (trieCtxMatch_insertTupEnv hm (someVarsToOpt (Tup.levels ts outVD))) hΔ hrl hk)
    | _ => rot_miss
  | .loadP p, tf, Γ, Δ, vs, ls, inVD, inLD, outVD, outLD, inVE, inLE,
      hval, hΓ, hm, hΔ, hrl, hwf => by
    rcases hval with ⟨inLEb, hval⟩
    cases tf with
    | load t a k =>
      obtain ⟨ha, hk⟩ := wf_load hwf
      dsimp only [validateRotPlanWithFlat] at hval
      have hval' : ValEx allowHdr p k (inVD + 1) inLD := ⟨inLEb, isSome_bind hval⟩
      dsimp only [denote, rewriteRotWithFlat]
      rw [denoteArg_eq_some_resolveEnvArg hΓ hm a ha, rewriteRotWith.eq_3]; dsimp only [toTFlat]
      exact congrArg (TFlat.load t _) (rewriteRotWithFlat_eq allowHdr p k hval' (.cons hΓ)
        (hm.cons t (some (.var outVD))) hΔ hrl hk)
    | _ => rot_miss
  | .storeP p, tf, Γ, Δ, vs, ls, inVD, inLD, outVD, outLD, inVE, inLE,
      hval, hΓ, hm, hΔ, hrl, hwf => by
    rcases hval with ⟨inLEb, hval⟩
    cases tf with
    | store v a k =>
      obtain ⟨hv, ha, hk⟩ := wf_store hwf
      dsimp only [validateRotPlanWithFlat] at hval
      have hval' : ValEx allowHdr p k inVD inLD := ⟨inLEb, isSome_bind hval⟩
      dsimp only [denote, rewriteRotWithFlat]
      rw [denoteArg_eq_some_resolveEnvArg hΓ hm v hv,
        denoteArg_eq_some_resolveEnvArg hΓ hm a ha, rewriteRotWith.eq_4]
      dsimp only [toTFlat]
      exact congrArg (TFlat.store _ _) (rewriteRotWithFlat_eq allowHdr p k hval' hΓ hm hΔ hrl hk)
    | _ => rot_miss
  | .callP p, tf, Γ, Δ, vs, ls, inVD, inLD, outVD, outLD, inVE, inLE,
      hval, hΓ, hm, hΔ, hrl, hwf => by
    rcases hval with ⟨inLEb, hval⟩
    cases tf with
    | call f bs args k =>
      obtain ⟨ha, hk⟩ := wf_call hwf
      dsimp only [validateRotPlanWithFlat] at hval
      have hval' : ValEx allowHdr p k (inVD + bs.length) inLD := ⟨inLEb, isSome_bind hval⟩
      dsimp only [denote, rewriteRotWithFlat]
      rw [denoteArgs_eq_some_resolveEnvArgs hΓ hm args ha, rewriteRotWith.eq_5]
      dsimp only [toTFlat]
      exact congrArg (TFlat.call f bs _)
        (rewriteRotWithFlat_eq allowHdr p k hval' (CtxTypes.push _ hΓ)
          (trieCtxMatch_insertTupEnv hm (someVarsToOpt (Tup.levels bs outVD))) hΔ hrl hk)
    | _ => rot_miss
  | .jnzP tp ep, tf, Γ, Δ, vs, ls, inVD, inLD, outVD, outLD, inVE, inLE,
      hval, hΓ, hm, hΔ, hrl, hwf => by
    rcases hval with ⟨inLEb, hval⟩
    cases tf with
    | jnz c t e =>
      obtain ⟨hc, ht, he⟩ := wf_jnz hwf
      dsimp only [validateRotPlanWithFlat] at hval
      have htval : ValEx allowHdr tp t inVD inLD := ⟨inLEb, isSome_bind hval⟩
      have heval : ValEx allowHdr ep e inVD inLD := ⟨inLEb, isSome_bind2 hval⟩
      dsimp only [denote, rewriteRotWithFlat]
      rw [denoteArg_eq_some_resolveEnvArg hΓ hm c hc, rewriteRotWith.eq_6]; dsimp only [toTFlat]
      exact congr
        (congrArg (TFlat.jnz _) (rewriteRotWithFlat_eq allowHdr tp t htval hΓ hm hΔ hrl ht))
        (rewriteRotWithFlat_eq allowHdr ep e heval hΓ hm hΔ hrl he)
    | jump j args =>
      cases tp with
      | leaf =>
        cases ep with
        | leaf =>
          obtain ⟨hj, ha⟩ := wf_jump hwf
          obtain ⟨w₁, w₂, hres, hlk, hmrel⟩ := hrl.resolveLabel_rel hΔ hj
          dsimp only [denote, rewriteRotWithFlat]
          rw [hlk, denoteArgs_eq_some_resolveEnvArgs hΓ hm args ha]
          cases allowHdr
          · dsimp only [ite_false]; rw [rewriteRotWith.eq_def]; rfl
          · dsimp only [ite_true]; rw [hres]
            cases w₁ <;> cases w₂ <;> simp only [RotLFlatMatch] at hmrel
            · subst hmrel; rw [rewriteRotWith.eq_9]; rfl
            · rw [rewriteRotWith.eq_8]; exact (hmrel outVD outLD _).symm
            · rcases hmrel with ⟨rfl, _⟩; rw [rewriteRotWith.eq_7]; rfl
            · rw [rewriteRotWith.eq_10]; rfl
        | _ => rot_miss
      | _ => rot_miss
    | _ => rot_miss
  | .groupKeep bsP kP, tf, Γ, Δ, vs, ls, inVD, inLD, outVD, outLD,
      inVE, inLE, hval, hΓ, hm, hΔ, hrl, hwf => by
    rcases hval with ⟨inLEb, hval⟩
    cases tf with
    | group bs k =>
      rename_i sig
      obtain ⟨hb, hk⟩ := wf_group hwf
      dsimp only [validateRotPlanWithFlat] at hval
      have hbsval : ValExB allowHdr bsP bs inVD (inLD + sig.length) := ⟨_, isSome_bind hval⟩
      have hkval : ValEx allowHdr kP k inVD (inLD + sig.length) := ⟨_, isSome_bind2 hval⟩
      dsimp only [denote, rewriteRotWithFlat]; rw [rewriteRotWith.eq_11]; dsimp only [toTFlat]
      have hrl' : TrieRelMatch (RotLFlatMatch (rs := rs)) (inLD + sig.length)
          (insertTupEnv inLD inLE (wrapKeepLabelsFlat (Tup.levels sig outLD)))
          (pushTup (wrapKeepLabels (Tup.levels sig outLD)) ls) :=
        hrl.pushTup (wrapKeepLabelsFlat_rel (Tup.levels sig outLD))
      rw [rewriteKeepBFlat_eq allowHdr bsP bs hbsval hΓ hm (CtxTypes.push _ hΔ) hrl' hb,
        rewriteRotWithFlat_eq allowHdr kP k hkval hΓ hm (CtxTypes.push _ hΔ) hrl' hk]
    | _ => rot_miss
  | .groupRot dir hdr contMasks exitMode contP exitP entryP, tf,
      Γ, Δ, vs, ls, inVD, inLD, outVD, outLD, inVE, inLE, hval, hΓ, hm, hΔ, hrl, hwf => by
    rcases hval with ⟨inLEb, hval⟩
    cases tf with
    | group bs k =>
      rename_i sig
      cases sig with
      | nil => cases bs; dsimp only [validateRotPlanWithFlat] at hval; contradiction
      | cons ts sig' =>
        cases sig' with
        | cons _ _ =>
          cases bs; rename_i bs'; cases bs'
          dsimp only [validateRotPlanWithFlat] at hval; contradiction
        | nil =>
          cases bs with
          | cons b bs' =>
            cases bs'
            obtain ⟨hb0, hk0⟩ := wf_group hwf; obtain ⟨hb1, _⟩ := wf_cons hb0
            cases hvh : validateHdrFlat hdr b (inVD + ts.length) with
            | none => dsimp only [validateRotPlanWithFlat] at hval; rw [hvh] at hval; contradiction
            | some val =>
              rcases val with ⟨sh, armT, armE, nv'⟩
              obtain ⟨hsc_val, hsx_val, hse_val⟩ := valEx_groupRot hvh hval
              let hrl_dead : TrieRelMatch (RotLFlatMatch (rs := rs)) (inLD + 1)
                  (inLE.insert inLD ⟨ts, .dead⟩) (⟨ts, .dead⟩ :: ls) := hrl.cons trivial
              let hΔ_b : CtxTypes (ts :: Δ) (⟨ts, RotL.dead⟩ :: ls) :=
                CtxTypes.cons (v := RotL.dead) hΔ
              let emitLoopOk (outLD_l : Nat)
                  (mkHdrCont : KL (rotSig hdr contMasks ts) → Tup (Arg K) ts → Expr K KL rs)
                  (mkHdrContFlat : Nat → Nat → Nat → Tup (Arg K) ts → TFlat rs)
                  (hmk : ∀ J_rot curVD curLD args,
                    mkHdrContFlat J_rot curVD curLD args =
                      toTFlat (mkHdrCont J_rot args) curVD curLD) :
                  toTFlat
                    (if isPartialMasks hdr contMasks = true then
                      Expr.group (sig := [rotSig hdr contMasks ts, ts])
                        (fun Js =>
                          Blocks.cons
                            (fun rotParams => rewriteRotWith true contP
                              (rotBodyExpr dir hdr contMasks
                                (fun Js' => Blocks.cons (fun xs => denote _ _ b (pushTup xs vs)
                                  (⟨ts, Js'.1⟩ :: ls)) .nil)
                                (RotL.expandOrKeep (mkHdrCont Js.1) Js.2.1) rotParams))
                            (Blocks.cons
                              (fun hdrParams => mkHdrCont Js.1 (toArgTup hdrParams)) .nil))
                        (fun Js =>
                          rewriteRotWith allowHdr entryP
                            (denote _ _ k vs (⟨ts, RotL.expand (mkHdrCont Js.1)⟩ :: ls)))
                    else
                      Expr.group (sig := [rotSig hdr contMasks ts])
                        (fun Js =>
                          Blocks.cons
                            (fun rotParams => rewriteRotWith allowHdr contP
                              (rotBodyExpr dir hdr contMasks
                                (fun Js' => Blocks.cons (fun xs => denote _ _ b (pushTup xs vs)
                                  (⟨ts, Js'.1⟩ :: ls)) .nil)
                                (RotL.expand (mkHdrCont Js.1)) rotParams))
                            .nil)
                        (fun Js =>
                          rewriteRotWith allowHdr entryP
                            (denote _ _ k vs (⟨ts, RotL.expand (mkHdrCont Js.1)⟩ :: ls))))
                    outVD outLD_l =
                  (if isPartialMasks hdr contMasks then
                    let J_rot := outLD_l
                    let J_hdr := outLD_l + 1
                    let outLD' := outLD_l + 2
                    let rotParams := Tup.levels (rotSig hdr contMasks ts) outVD
                    let outVD_b0 := outVD + (rotSig hdr contMasks ts).length
                    let xs := splitTail hdr contMasks rotParams
                    let b0 := match hdrPeelFlat dir true hdr contMasks rotParams b
                        (inVD + ts.length) (insertTupEnv inVD inVE (someVarsToOpt xs)) with
                      | some (arm, iv', ie') =>
                        rewriteRotWithFlat true contP arm iv' ie'
                          (inLD + 1)
                          (inLE.insert inLD ⟨ts, .expandOrKeep (mkHdrContFlat J_rot) J_hdr⟩)
                          outVD_b0 outLD'
                      | none => .hlt
                    let hdrParams := Tup.levels ts outVD
                    let b1 := mkHdrContFlat J_rot (outVD + ts.length) outLD' (toArgTup hdrParams)
                    .group (sig := [rotSig hdr contMasks ts, ts]) (.cons b0 (.cons b1 .nil))
                      (rewriteRotWithFlat allowHdr entryP k inVD inVE
                        (inLD + 1) (inLE.insert inLD ⟨ts, .expand (mkHdrContFlat J_rot)⟩)
                        outVD outLD')
                  else
                    let J_rot := outLD_l
                    let outLD' := outLD_l + 1
                    let rotParams := Tup.levels (rotSig hdr contMasks ts) outVD
                    let outVD_b0 := outVD + (rotSig hdr contMasks ts).length
                    let xs := splitTail hdr contMasks rotParams
                    let b0 := match hdrPeelFlat dir true hdr contMasks rotParams b
                        (inVD + ts.length) (insertTupEnv inVD inVE (someVarsToOpt xs)) with
                      | some (arm, iv', ie') =>
                        rewriteRotWithFlat allowHdr contP arm iv' ie'
                          (inLD + 1) (inLE.insert inLD ⟨ts, .expand (mkHdrContFlat J_rot)⟩)
                          outVD_b0 outLD'
                      | none => .hlt
                    .group (sig := [rotSig hdr contMasks ts]) (.cons b0 .nil)
                      (rewriteRotWithFlat allowHdr entryP k inVD inVE
                        (inLD + 1) (inLE.insert inLD ⟨ts, .expand (mkHdrContFlat J_rot)⟩)
                        outVD outLD')) := by
                let rotParams := Tup.levels (rotSig hdr contMasks ts) outVD
                let xs := splitTail hdr contMasks rotParams
                have hpeel := hdrPeelFlat_of_validateHdr dir true hdr contMasks rotParams b
                  (Γ := pushTypes ts Γ) (Δ := [ts] ++ Δ)
                  (vs := pushTup (someVarsToOpt xs) vs) (inVD := inVD + ts.length)
                  (inVE := insertTupEnv inVD inVE (someVarsToOpt xs))
                  hvh (CtxTypes.push _ hΓ) (trieCtxMatch_insertTupEnv hm _) hb1
                rcases hpeel with ⟨iv', ie', Γ', vs', hiv', hpeel_eq, hΓ', hm', hwf', hpeel_den⟩
                subst hiv'
                have htrue_eq : (true == dir) = dir := by cases dir <;> rfl
                simp only [htrue_eq] at hpeel_eq hwf' hpeel_den
                split
                · rename_i hpart
                  dsimp only [toTFlat, toTBlocks, Tup.levels, pushTup]
                  have hlen2 : [rotSig hdr contMasks ts, ts].length = 2 := rfl
                  rw [hlen2, hpeel_eq]; simp only [rotBodyExpr, Blocks.get]
                  let J_rot := outLD_l; let J_hdr := outLD_l + 1; let outLD' := outLD_l + 2
                  have hlbl_ek : TrieRelMatch (RotLFlatMatch (rs := rs)) (inLD + 1)
                      (inLE.insert inLD ⟨ts, .expandOrKeep (mkHdrContFlat J_rot) J_hdr⟩)
                      (⟨ts, RotL.expandOrKeep (mkHdrCont J_rot) J_hdr⟩ :: ls) :=
                    hrl.cons ⟨rfl, hmk J_rot⟩
                  have hlbl_ex : TrieRelMatch (RotLFlatMatch (rs := rs)) (inLD + 1)
                      (inLE.insert inLD ⟨ts, .expand (mkHdrContFlat J_rot)⟩)
                      (⟨ts, RotL.expand (mkHdrCont J_rot)⟩ :: ls) := hrl.cons (hmk J_rot)
                  have hsc_val' : ValEx true contP (if dir then armT else armE)
                      (inVD + ts.length + hdrStepCount hdr) (inLD + 1) := by
                    simpa [hpart] using hsc_val
                  have hb0 := rewriteRotWithFlat_eq true contP _ hsc_val' hΓ' hm'
                    (CtxTypes.cons (v := RotL.expandOrKeep (mkHdrCont J_rot) J_hdr) hΔ)
                    hlbl_ek hwf'
                    (outVD := outVD + (rotSig hdr contMasks ts).length) (outLD := outLD')
                  have hden0 := hpeel_den
                    (⟨ts, RotL.expandOrKeep (mkHdrCont J_rot) J_hdr⟩ :: ls)
                    (CtxTypes.cons (v := RotL.expandOrKeep (mkHdrCont J_rot) J_hdr) hΔ)
                  have hk := rewriteRotWithFlat_eq allowHdr entryP k hse_val hΓ hm
                    (CtxTypes.cons (v := RotL.expand (mkHdrCont J_rot)) hΔ)
                    hlbl_ex hk0 (outVD := outVD) (outLD := outLD')
                  have hb1' : toTFlat (mkHdrCont J_rot (toArgTup (Tup.levels ts outVD)))
                      (outVD + ts.length) outLD' =
                      mkHdrContFlat J_rot (outVD + ts.length) outLD'
                        (toArgTup (Tup.levels ts outVD)) :=
                    (hmk J_rot (outVD + ts.length) outLD' _).symm
                  dsimp only [J_rot, J_hdr, outLD', rotParams, xs] at hden0 hb0 hb1' hk
                  rw [hden0, hb0, hb1', hk]
                · rename_i hpart
                  dsimp only [toTFlat, toTBlocks, Tup.levels, pushTup]
                  have hlen1 : [rotSig hdr contMasks ts].length = 1 := rfl
                  rw [hlen1, hpeel_eq]; simp only [rotBodyExpr, Blocks.get]
                  let J_rot := outLD_l; let outLD' := outLD_l + 1
                  have hlbl_ex : TrieRelMatch (RotLFlatMatch (rs := rs)) (inLD + 1)
                      (inLE.insert inLD ⟨ts, .expand (mkHdrContFlat J_rot)⟩)
                      (⟨ts, RotL.expand (mkHdrCont J_rot)⟩ :: ls) := hrl.cons (hmk J_rot)
                  have hpartF : isPartialMasks hdr contMasks = false := by
                    cases hm0 : isPartialMasks hdr contMasks <;> simp_all
                  have hsc_val' : ValEx allowHdr contP (if dir then armT else armE)
                      (inVD + ts.length + hdrStepCount hdr) (inLD + 1) := by
                    simpa [hpartF, Bool.or_false] using hsc_val
                  have hb0 := rewriteRotWithFlat_eq allowHdr contP _ hsc_val' hΓ' hm'
                    (CtxTypes.cons (v := RotL.expand (mkHdrCont J_rot)) hΔ)
                    hlbl_ex hwf' (outVD := outVD + (rotSig hdr contMasks ts).length)
                    (outLD := outLD')
                  have hden0 := hpeel_den (⟨ts, RotL.expand (mkHdrCont J_rot)⟩ :: ls)
                    (CtxTypes.cons (v := RotL.expand (mkHdrCont J_rot)) hΔ)
                  have hk := rewriteRotWithFlat_eq allowHdr entryP k hse_val hΓ hm
                    (CtxTypes.cons (v := RotL.expand (mkHdrCont J_rot)) hΔ)
                    hlbl_ex hk0 (outVD := outVD) (outLD := outLD')
                  dsimp only [J_rot, outLD', rotParams, xs] at hden0 hb0 hk
                  rw [hden0, hb0, hk]
              cases exitMode with
              | inline =>
                dsimp only [denote, denoteB, rewriteRotWithFlat]
                rw [rewriteRotWith.eq_12]; simp only [Blocks.get, exitLabels, pushTup]
                refine emitLoopOk outLD
                  (fun J_rot args => hdrEmit dir args args hdr contMasks []
                    (denote (OptArg K) (RotL K KL rs) b (pushTup (someArgsToOpt args) vs)
                      (⟨ts, RotL.dead⟩ :: ls))
                    (fun rotArgs => Expr.jump J_rot rotArgs)
                    (fun exitExpr _ => rewriteRotWith allowHdr exitP exitExpr))
                  (fun J_rot curVD curLD args =>
                    hdrEmitFlat dir args args hdr contMasks [] b (inVD + ts.length)
                      (insertTupEnv inVD inVE (someArgsToOpt args)) curVD curLD
                      (fun od rotArgs => TFlat.jump (idxLabel curLD J_rot) (idxArgs od rotArgs))
                      (fun ex iv ie od _ => rewriteRotWithFlat allowHdr exitP ex iv ie
                        (inLD + 1) (inLE.insert inLD ⟨ts, .dead⟩) od curLD)) ?_
                intro J_rot curVD curLD args
                symm
                refine hdrEmitFlat_eq dir args args hdr contMasks [] b hvh (CtxTypes.push _ hΓ)
                  (trieCtxMatch_insertTupEnv hm _) hΔ_b hb1 _ _ (fun _ _ => rfl) _ _ ?_
                intro iv' ie' Γ' vs' od _ hiv' hΓ' hm' hwf'; subst hiv'
                exact rewriteRotWithFlat_eq allowHdr exitP _ hsx_val hΓ' hm' hΔ_b hrl_dead hwf'
              | wrap xsMask hMasks =>
                dsimp only [denote, denoteB, rewriteRotWithFlat]
                rw [rewriteRotWith.eq_13]; dsimp only [toTFlat, toTBlocks, Tup.levels]
                let J_exit := outLD
                let exitParams := Tup.levels (exitSig hdr hMasks xsMask ts) outVD
                let xsTail := splitTail hdr hMasks exitParams
                let xsOpt := tupWiden ts xsMask xsTail
                have hpeel := hdrPeelFlat_of_validateHdr dir false hdr hMasks exitParams b
                  (Γ := pushTypes ts Γ) (Δ := [ts] ++ Δ)
                  (vs := pushTup xsOpt vs) (inVD := inVD + ts.length)
                  (inVE := insertTupEnv inVD inVE xsOpt)
                  hvh (CtxTypes.push _ hΓ) (trieCtxMatch_insertTupEnv hm _) hb1
                rcases hpeel with ⟨iv', ie', Γ', vs', hiv', hpeel_eq, hΓ', hm', hwf', hpeel_den⟩
                subst hiv'
                have hfalse_eq : (false == dir) = !dir := by cases dir <;> rfl
                have hif_eq : (if !dir then armT else armE) = (if dir then armE else armT) := by
                  cases dir <;> rfl
                simp only [hfalse_eq, hif_eq] at hpeel_eq hwf' hpeel_den
                rw [hpeel_eq]; simp only [Blocks.get, exitLabels, pushTup]
                have hden_ex := hpeel_den (⟨ts, RotL.dead⟩ :: ls) hΔ_b
                have hex_rw := rewriteRotWithFlat_eq allowHdr exitP _ hsx_val hΓ' hm' hΔ_b
                  hrl_dead hwf' (outVD := outVD + (exitSig hdr hMasks xsMask ts).length)
                  (outLD := outLD + 1)
                have heloop := emitLoopOk (outLD + 1)
                  (fun J_rot args => hdrEmit dir args (tupSelectArgs ts xsMask args) hdr
                    contMasks hMasks
                    (denote (OptArg K) (RotL K KL rs) b (pushTup (someArgsToOpt args) vs)
                      (⟨ts, RotL.dead⟩ :: ls))
                    (fun rotArgs => Expr.jump J_rot rotArgs)
                    (fun _ exArgs => Expr.jump J_exit exArgs))
                  (fun J_rot curVD curLD args =>
                    hdrEmitFlat (tailC := ts) (tailX := filterTys ts xsMask)
                      dir args (tupSelectArgs ts xsMask args) hdr contMasks hMasks b
                      (inVD + ts.length) (insertTupEnv inVD inVE (someArgsToOpt args))
                      curVD curLD
                      (fun od rotArgs => TFlat.jump (idxLabel curLD J_rot) (idxArgs od rotArgs))
                      (fun _ _ _ od exArgs =>
                        TFlat.jump (idxLabel curLD J_exit) (idxArgs od exArgs))) ?_
                · exact congr (congrArg TFlat.group
                    (congrArg (TBlocks.cons · .nil) (hden_ex ▸ hex_rw))) heloop
                · intro J_rot curVD curLD args
                  symm
                  exact hdrEmitFlat_eq dir args (tupSelectArgs ts xsMask args) hdr contMasks
                    hMasks b hvh (CtxTypes.push _ hΓ) (trieCtxMatch_insertTupEnv hm _) hΔ_b hb1
                    _ _ (fun _ _ => rfl) _ _ (fun _ _ _ _ _ _ _ _ _ _ => rfl)
    | _ => dsimp only [validateRotPlanWithFlat] at hval; contradiction

private theorem rewriteKeepBFlat_eq {rs : List Ty} (allowHdr : Bool) :
    (ps : List RotPlan) → {sig : List (List Ty)} → (tb : TBlocks rs sig) →
    {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × OptArg K t)} → {ls : List ((ts : List Ty) × RotL K KL rs ts)} →
    {inVD inLD outVD outLD : Nat} →
    {inVE : Trie ((t : Ty) × OptArg K t)} →
    {inLE : Trie ((ts : List Ty) × RotLFlat rs ts)} →
    ValExB allowHdr ps tb inVD inLD →
    CtxTypes Γ vs → TrieCtxMatch inVD inVE vs →
    CtxTypes Δ ls → TrieRelMatch (RotLFlatMatch (rs := rs)) inLD inLE ls →
    tb.wfCheck Γ Δ = true →
    toTBlocks (rewriteRotWith.rewriteKeepB allowHdr ps
        (denoteB (OptArg K) (RotL K KL rs) tb vs ls)) outVD outLD =
      rewriteRotWithFlat.rewriteKeepBFlat allowHdr ps tb inVD inVE inLD inLE outVD outLD
  | [], _, tb, _, _, _, _, _, _, _, _, _, _, _, hΓ, hm, hΔ, hrl, hwf => by
    rw [rewriteRotWith.rewriteKeepB.eq_1]
    exact flatExprFlat_both.2 tb () hΓ hΔ hm ⟨hΔ, hrl⟩ hwf
  | _ :: _, _, .nil, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by
    dsimp only [denoteB, rewriteRotWithFlat.rewriteKeepBFlat]
    rw [rewriteRotWith.rewriteKeepB.eq_3]; rfl
  | p :: ps, _, .cons (ts := ts) b bs, Γ, Δ, vs, ls, inVD, inLD, outVD, outLD, inVE, inLE,
      hval, hΓ, hm, hΔ, hrl, hwf => by
    obtain ⟨hb, hbs⟩ := wf_cons hwf
    rcases hval with ⟨inLEb, hval⟩
    dsimp only [validateRotPlanWithFlat.validateKeepBFlat] at hval
    have hp_val : ValEx allowHdr p b (inVD + ts.length) inLD := ⟨inLEb, isSome_bind hval⟩
    have hps_val : ValExB allowHdr ps bs inVD inLD := ⟨inLEb, isSome_bind2 hval⟩
    dsimp only [denoteB, rewriteRotWithFlat.rewriteKeepBFlat, toTBlocks]
    rw [rewriteRotWith.rewriteKeepB.eq_2]
    exact congr (congrArg TBlocks.cons
      (rewriteRotWithFlat_eq allowHdr p b hp_val (CtxTypes.push _ hΓ)
        (trieCtxMatch_insertTupEnv hm (someVarsToOpt (Tup.levels ts outVD))) hΔ hrl hb))
      (rewriteKeepBFlat_eq allowHdr ps bs hps_val hΓ hm hΔ hrl hbs)
end

/-- `loopRotateFlat as tf cfg = reifyFunc (Func.loopRotate (denoteFunc tf) cfg)`
under `wfCheck = true`. -/
theorem loopRotateFlat_eq {as rs : List Ty} (tf : TFlat rs)
    (cfg : LoopRotate.RotConfig := LoopRotate.defaultRotConfig)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    loopRotateFlat as tf cfg = reifyFunc (Func.loopRotate (denoteFunc (as := as) tf) cfg) := by
  dsimp only [loopRotateFlat, Func.loopRotate]
  have hr : reifyFunc (denoteFunc (as := as) tf) = tf := reifyFunc_denoteFunc_eq tf hwf
  rw [hr]
  split
  · dsimp only [Func.loopRotateWithPlan]
    have hval := validateRotPlanWithFlat_eq false (LoopRotate.buildRotPlan (as := as) cfg tf) tf
      (CtxTypes.push _ .nil) (CtxLevels.pushTup CtxLevels.nil) .nil .empty hwf
    simp only [pushTup_length, List.length_nil, Nat.zero_add] at hval
    change validateRotPlan (LoopRotate.buildRotPlan (as := as) cfg tf)
      (denoteFunc (as := as) tf K BoolL (Tup.levels as 0)) as.length =
      validateRotPlanFlat (LoopRotate.buildRotPlan (as := as) cfg tf) tf as.length at hval
    rw [hval]
    split
    · rename_i _ hsome
      rw [hsome]
      dsimp only [reifyFunc, denoteFunc, rewriteRot]
      have hvalEx : ValEx false (LoopRotate.buildRotPlan (as := as) cfg tf) tf as.length 0 :=
        ⟨.empty, by dsimp only [validateRotPlanFlat] at hsome; rw [hsome]; rfl⟩
      have hm0 :=
        trieCtxMatch_insertTupEnv (W := OptArg K) .empty (someVarsToOpt (Tup.levels as 0))
      rw [Nat.zero_add] at hm0
      have hrw := rewriteRotWithFlat_eq false (LoopRotate.buildRotPlan (as := as) cfg tf) tf
        hvalEx (CtxTypes.push _ .nil) hm0 .nil (.empty _) hwf (outVD := as.length) (outLD := 0)
      simpa using hrw.symm
    · rename_i _ hnone; rw [hnone]; exact hr.symm
  · exact hr.symm

/-- `denoteFunc (loopRotateFlat as tf cfg) = Func.loopRotate (denoteFunc tf) cfg`
under `wfCheck = true`. -/
theorem denoteFunc_loopRotateFlat {as rs : List Ty} (tf : TFlat rs)
    (cfg : LoopRotate.RotConfig := LoopRotate.defaultRotConfig)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    denoteFunc (as := as) (loopRotateFlat as tf cfg) =
      Func.loopRotate (denoteFunc (as := as) tf) cfg :=
  denoteFunc_of_flat_eq (flat := fun tf => loopRotateFlat as tf cfg)
    (phoas := fun f => Func.loopRotate f cfg) (fun hf => Func.loopRotate_wf hf cfg) tf hwf
    (loopRotateFlat_eq tf cfg hwf)

/-- `loopRotateFlat` preserves `wfCheck`. -/
theorem loopRotateFlat_wfCheck {as rs : List Ty} (tf : TFlat rs)
    (cfg : LoopRotate.RotConfig := LoopRotate.defaultRotConfig)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    (loopRotateFlat as tf cfg).wfCheck (pushTypes as []) [] = true :=
  wfCheck_of_flat_eq (flat := fun tf => loopRotateFlat as tf cfg)
    (phoas := fun f => Func.loopRotate f cfg) (fun hf => Func.loopRotate_wf hf cfg) tf hwf
    (loopRotateFlat_eq tf cfg hwf)

/-- `(loopRotateFlatFn f cfg).toFn = ⟨f.name, f.as, f.rs, Func.loopRotate f.toFn.body cfg⟩`
under `wfCheck = true`. -/
theorem loopRotateFlatFn_toFn (f : TFlatFn) (hwf : f.wfCheck = true)
    (cfg : LoopRotate.RotConfig := LoopRotate.defaultRotConfig) :
    (loopRotateFlatFn f cfg).toFn = ⟨f.name, f.as, f.rs, Func.loopRotate f.toFn.body cfg⟩ := by
  dsimp only [TFlatFn.toFn, loopRotateFlatFn]; rw [denoteFunc_loopRotateFlat f.body cfg hwf]

/-- `loopRotateFlatFn` preserves `TFlatFn.wfCheck`. -/
theorem loopRotateFlatFn_wfCheck (f : TFlatFn) (hwf : f.wfCheck = true)
    (cfg : LoopRotate.RotConfig := LoopRotate.defaultRotConfig) :
    (loopRotateFlatFn f cfg).wfCheck = true :=
  loopRotateFlat_wfCheck f.body cfg hwf

end OptFlatLoop
end LeanQbe.T