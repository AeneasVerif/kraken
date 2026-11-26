module

public import LeanQbe.T.OptFlatLoop
public import LeanQbe.T.OptFlatLoopLemmas0
import LeanQbe.T.OptFlatLoopLemmas1
import LeanQbe.T.FlatDirectLemmas
import LeanQbe.T.PassFlatKit
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

mutual
private theorem flatExprFlat_eq {rs : List Ty} :
    (tf : TFlat rs) → {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × OptArg K t)} → {ls : List ((ts : List Ty) × RotL K KL rs ts)} →
    {inVD inLD outVD outLD : Nat} →
    {inVE : Trie ((t : Ty) × OptArg K t)} →
    {inLE : Trie ((ts : List Ty) × RotLFlat rs ts)} →
    CtxTypes Γ vs → TrieCtxMatch inVD inVE vs →
    CtxTypes Δ ls → TrieRelMatch (RotLFlatMatch (rs := rs)) inLD inLE ls →
    tf.wfCheck Γ Δ = true →
    toTFlat (flatExpr (denote (OptArg K) (RotL K KL rs) tf vs ls)) outVD outLD =
      flatExprFlat tf inVD inVE inLD inLE outVD outLD
  | .let_ (ts := ts) op k, Γ, Δ, vs, ls, inVD, inLD, outVD, outLD, inVE, inLE,
      hΓ, hm, hΔ, hrl, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    have hargs := denoteArgs_eq_some_resolveEnvArgs hΓ hm op.args hwf.1
    dsimp only [denote, flatExprFlat]
    rw [hargs]
    dsimp only [flatExpr, flatOptOp, toTFlat]
    refine congrArg (TFlat.let_ _) ?_
    exact flatExprFlat_eq k (CtxTypes.push _ hΓ)
      (trieCtxMatch_insertTupEnv hm (someVarsToOpt (Tup.levels ts outVD)))
      hΔ hrl hwf.2
  | .load t a k, Γ, Δ, vs, ls, inVD, inLD, outVD, outLD, inVE, inLE,
      hΓ, hm, hΔ, hrl, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    have ha := denoteArg_eq_some_resolveEnvArg hΓ hm a hwf.1
    dsimp only [denote, flatExprFlat]
    rw [ha]
    dsimp only [flatExpr, toTFlat]
    refine congrArg (TFlat.load t _) ?_
    exact flatExprFlat_eq k (.cons hΓ) (hm.cons t (some (.var outVD))) hΔ hrl hwf.2
  | .store v a k, Γ, Δ, vs, ls, inVD, inLD, outVD, outLD, inVE, inLE,
      hΓ, hm, hΔ, hrl, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    have hv := denoteArg_eq_some_resolveEnvArg hΓ hm v hwf.1.1
    have ha := denoteArg_eq_some_resolveEnvArg hΓ hm a hwf.1.2
    dsimp only [denote, flatExprFlat]
    rw [hv, ha]
    dsimp only [flatExpr, toTFlat]
    exact congrArg (TFlat.store _ _) (flatExprFlat_eq k hΓ hm hΔ hrl hwf.2)
  | .ret vs', Γ, _, vs, ls, inVD, _, outVD, outLD, inVE, _, hΓ, hm, _, _, hwf => by
    have hvs := denoteArgs_eq_some_resolveEnvArgs hΓ hm vs' hwf
    dsimp only [denote, flatExprFlat]
    rw [hvs]
    rfl
  | .exit f args, Γ, _, vs, ls, inVD, _, outVD, outLD, inVE, _, hΓ, hm, _, _, hwf => by
    have hargs := denoteArgs_eq_some_resolveEnvArgs hΓ hm args hwf
    dsimp only [denote, flatExprFlat]
    rw [hargs]
    rfl
  | .hlt, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => rfl
  | .call f bs args k, Γ, Δ, vs, ls, inVD, inLD, outVD, outLD, inVE, inLE,
      hΓ, hm, hΔ, hrl, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    have hargs := denoteArgs_eq_some_resolveEnvArgs hΓ hm args hwf.1
    dsimp only [denote, flatExprFlat]
    rw [hargs]
    dsimp only [flatExpr, toTFlat]
    refine congrArg (TFlat.call f bs _) ?_
    exact flatExprFlat_eq k (CtxTypes.push _ hΓ)
      (trieCtxMatch_insertTupEnv hm (someVarsToOpt (Tup.levels bs outVD)))
      hΔ hrl hwf.2
  | .jnz c t e, Γ, Δ, vs, ls, inVD, inLD, outVD, outLD, inVE, inLE,
      hΓ, hm, hΔ, hrl, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    have hc := denoteArg_eq_some_resolveEnvArg hΓ hm c hwf.1.1
    dsimp only [denote, flatExprFlat]
    rw [hc]
    dsimp only [flatExpr, toTFlat]
    exact congr (congrArg (TFlat.jnz _) (flatExprFlat_eq t hΓ hm hΔ hrl hwf.1.2))
      (flatExprFlat_eq e hΓ hm hΔ hrl hwf.2)
  | .jump (ts := ts) j args, Γ, Δ, vs, ls, inVD, inLD, outVD, outLD, inVE, inLE,
      hΓ, hm, hΔ, hrl, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨w₁, w₂, hres, hlk, hmrel⟩ := hrl.resolveLabel_rel hΔ hwf.1
    have hargs := denoteArgs_eq_some_resolveEnvArgs hΓ hm args hwf.2
    dsimp only [denote, flatExprFlat]
    rw [hlk, hargs, hres]
    cases w₁ <;> cases w₂ <;> simp only [RotLFlatMatch] at hmrel
    · subst hmrel; rfl
    · exact (hmrel outVD outLD _).symm
    · exact (hmrel.2 outVD outLD _).symm
    · rfl
  | .group (sig := sig) bs k, Γ, Δ, vs, ls, inVD, inLD, outVD, outLD, inVE, inLE,
      hΓ, hm, hΔ, hrl, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denote, flatExprFlat, flatExpr, toTFlat]
    have hrl' : TrieRelMatch (RotLFlatMatch (rs := rs)) (inLD + sig.length)
        (insertTupEnv inLD inLE (wrapKeepLabelsFlat (Tup.levels sig outLD)))
        (pushTup (wrapKeepLabels (Tup.levels sig outLD)) ls) :=
      hrl.pushTup (wrapKeepLabelsFlat_rel (Tup.levels sig outLD))
    rw [flatBlocksFlat_eq bs hΓ hm (CtxTypes.push _ hΔ) hrl' hwf.1,
      flatExprFlat_eq k hΓ hm (CtxTypes.push _ hΔ) hrl' hwf.2]

private theorem flatBlocksFlat_eq {rs : List Ty} :
    {sig : List (List Ty)} → (tb : TBlocks rs sig) →
    {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × OptArg K t)} → {ls : List ((ts : List Ty) × RotL K KL rs ts)} →
    {inVD inLD outVD outLD : Nat} →
    {inVE : Trie ((t : Ty) × OptArg K t)} →
    {inLE : Trie ((ts : List Ty) × RotLFlat rs ts)} →
    CtxTypes Γ vs → TrieCtxMatch inVD inVE vs →
    CtxTypes Δ ls → TrieRelMatch (RotLFlatMatch (rs := rs)) inLD inLE ls →
    tb.wfCheck Γ Δ = true →
    toTBlocks (flatExpr.flatBlocks (denoteB (OptArg K) (RotL K KL rs) tb vs ls)) outVD outLD =
      flatBlocksFlat tb inVD inVE inLD inLE outVD outLD
  | _, .nil, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => rfl
  | _, .cons (ts := ts) b bs, Γ, Δ, vs, ls, inVD, inLD, outVD, outLD, inVE, inLE,
      hΓ, hm, hΔ, hrl, hwf => by
    dsimp only [TBlocks.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denoteB, flatBlocksFlat, flatExpr.flatBlocks, toTBlocks]
    refine congr (congrArg TBlocks.cons ?_) ?_
    · exact flatExprFlat_eq b (CtxTypes.push _ hΓ)
        (trieCtxMatch_insertTupEnv hm (someVarsToOpt (Tup.levels ts outVD)))
        hΔ hrl hwf.1
    · exact flatBlocksFlat_eq bs hΓ hm hΔ hrl hwf.2
end

/-! ## 2. Header Peel & Emit Equivalence (`hdrPeelFlat`, `hdrEmitFlat`) -/

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
  | [], ms, params, b, Γ, Δ, vs, nv, inVD, inVE, sh, tF, eF, nv',
      hvh, hΓ, hm, hwf => by
    cases b with
    | jnz c armT armE =>
      dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
      dsimp only [validateHdrFlat] at hvh
      cases hvh
      refine ⟨inVD, inVE, Γ, vs, rfl, rfl, hΓ, hm, (by cases wantCont == dir <;> simp [hwf]), ?_⟩
      intro ls _
      have hc := denoteArg_eq_some_resolveEnvArg hΓ hm c hwf.1.1
      dsimp only [denote]
      rw [hc]
      dsimp only [hdrPeel]
      cases wantCont == dir <;> rfl
    | _ => dsimp only [validateHdrFlat] at hvh; contradiction
  | .let_ dts :: ss, ms, params, b, Γ, Δ, vs, nv, inVD, inVE,
      sh, tF, eF, nv', hvh, hΓ, hm, hwf => by
    cases b with
    | let_ op k =>
      rename_i dts'
      dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
      dsimp only [validateHdrFlat] at hvh
      cases hdec : tysDecEq dts dts' with
      | isFalse _ => rw [hdec] at hvh; contradiction
      | isTrue heq =>
        subst heq
        rw [hdec] at hvh; dsimp only at hvh
        cases hvh2 : validateHdrFlat ss k (nv + dts.length) with
        | none => rw [hvh2] at hvh; contradiction
        | some val =>
          rcases val with ⟨sh2, tF2, eF2, nv2⟩
          rw [hvh2] at hvh
          have h_eq : tF2 = tF ∧ eF2 = eF ∧ nv2 = nv' := by
            injection hvh with h0
            exact ⟨congrArg (·.2.1) h0, congrArg (·.2.2.1) h0, congrArg (·.2.2.2) h0⟩
          rcases h_eq with ⟨rfl, rfl, rfl⟩
          let hsp := LoopRotate.tupSplit (filterTys dts (ms.headD [])) params
          have ih := hdrPeelFlat_of_validateHdr dir wantCont ss ms.tail hsp.2 k
            (Γ := pushTypes dts Γ) (Δ := Δ)
            (vs := pushTup (tupWiden dts (ms.headD []) hsp.1) vs)
            (nv := nv + dts.length)
            (inVD := inVD + dts.length)
            (inVE := insertTupEnv inVD inVE (tupWiden dts (ms.headD []) hsp.1))
            hvh2 (CtxTypes.push _ hΓ) (trieCtxMatch_insertTupEnv hm _) hwf.2
          rcases ih with ⟨iv', ie', Γ', vs', hiv', hpeel, hΓ', hm', hwf', hden⟩
          refine ⟨iv', ie', Γ', vs', ?_, ?_, hΓ', hm', hwf', ?_⟩
          · dsimp only [hdrStepCount, HdrStep.tys] at hiv' ⊢; omega
          · dsimp only [hdrPeelFlat]; rw [hdec]; dsimp only; exact hpeel
          · intro ls hΔ
            have hargs := denoteArgs_eq_some_resolveEnvArgs hΓ hm op.args hwf.1
            dsimp only [denote]
            rw [hargs]
            dsimp only [hdrPeel]
            rw [hdec]; dsimp only
            exact hden ls hΔ
    | _ => dsimp only [validateHdrFlat] at hvh; contradiction
  | .load t :: ss, ms, params, b, Γ, Δ, vs, nv, inVD, inVE,
      sh, tF, eF, nv', hvh, hΓ, hm, hwf => by
    cases b with
    | load t' a k =>
      dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
      dsimp only [validateHdrFlat] at hvh
      cases hdec : tyDecEq t t' with
      | isFalse _ => rw [hdec] at hvh; contradiction
      | isTrue heq =>
        subst heq
        rw [hdec] at hvh; dsimp only at hvh
        cases hvh2 : validateHdrFlat ss k (nv + 1) with
        | none => rw [hvh2] at hvh; contradiction
        | some val =>
          rcases val with ⟨sh2, tF2, eF2, nv2⟩
          rw [hvh2] at hvh
          have h_eq : tF2 = tF ∧ eF2 = eF ∧ nv2 = nv' := by
            injection hvh with h0
            exact ⟨congrArg (·.2.1) h0, congrArg (·.2.2.1) h0, congrArg (·.2.2.2) h0⟩
          rcases h_eq with ⟨rfl, rfl, rfl⟩
          let hsp := LoopRotate.tupSplit (filterTys [t] (ms.headD [])) params
          let y1 : OptArg K t := (tupWiden [t] (ms.headD []) hsp.1).1
          have ih := hdrPeelFlat_of_validateHdr dir wantCont ss ms.tail hsp.2 k
            (Γ := t :: Γ) (Δ := Δ) (vs := ⟨t, y1⟩ :: vs)
            (nv := nv + 1) (inVD := inVD + 1) (inVE := inVE.insert inVD ⟨t, y1⟩)
            hvh2 (.cons hΓ) (hm.cons t y1) hwf.2
          rcases ih with ⟨iv', ie', Γ', vs', hiv', hpeel, hΓ', hm', hwf', hden⟩
          refine ⟨iv', ie', Γ', vs', ?_, ?_, hΓ', hm', hwf', ?_⟩
          · simp only [hdrStepCount, HdrStep.tys, List.length_cons, List.length_nil] at hiv' ⊢
            omega
          · dsimp only [hdrPeelFlat]; rw [hdec]; dsimp only; exact hpeel
          · intro ls hΔ
            have ha := denoteArg_eq_some_resolveEnvArg hΓ hm a hwf.1
            dsimp only [denote]
            rw [ha]
            dsimp only [hdrPeel]
            rw [hdec]; dsimp only
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
  | [], _, _, b, Γ, Δ, vs, ls, inVD, outVD, outLD, nv, inVE,
      sh, tF, eF, nv', hvh, hΓ, hm, _, hwf, kC, kCFlat, hkC, kX, kXFlat, hkX => by
    cases b with
    | jnz c armT armE =>
      dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
      dsimp only [validateHdrFlat] at hvh
      cases hvh
      have hc := denoteArg_eq_some_resolveEnvArg hΓ hm c hwf.1.1
      dsimp only [denote, hdrEmitFlat]
      rw [hc]
      dsimp only [hdrEmit]
      cases dir
      · simp only [Bool.false_eq_true, ↓reduceIte, toTFlat]
        exact congr (congrArg (TFlat.jnz _) (hkX inVD inVE Γ vs outVD tailXArgs rfl hΓ hm hwf.1.2))
          (hkC outVD tailCArgs)
      · simp only [↓reduceIte, toTFlat]
        exact congr (congrArg (TFlat.jnz _) (hkC outVD tailCArgs))
          (hkX inVD inVE Γ vs outVD tailXArgs rfl hΓ hm hwf.2)
    | _ => dsimp only [validateHdrFlat] at hvh; contradiction
  | .let_ dts :: ss, cMs, xMs, b, Γ, Δ, vs, ls,
      inVD, outVD, outLD, nv, inVE, sh, tF, eF, nv',
      hvh, hΓ, hm, hΔ, hwf, kC, kCFlat, hkC, kX, kXFlat, hkX => by
    cases b with
    | let_ op k =>
      rename_i dts'
      dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
      dsimp only [validateHdrFlat] at hvh
      cases hdec : tysDecEq dts dts' with
      | isFalse _ => rw [hdec] at hvh; contradiction
      | isTrue heq =>
        subst heq
        rw [hdec] at hvh; dsimp only at hvh
        cases hvh2 : validateHdrFlat ss k (nv + dts.length) with
        | none => rw [hvh2] at hvh; contradiction
        | some val =>
          rcases val with ⟨sh2, tF2, eF2, nv2⟩
          rw [hvh2] at hvh
          have h_eq : tF2 = tF ∧ eF2 = eF ∧ nv2 = nv' := by
            injection hvh with h0
            exact ⟨congrArg (·.2.1) h0, congrArg (·.2.2.1) h0, congrArg (·.2.2.2) h0⟩
          rcases h_eq with ⟨rfl, rfl, rfl⟩
          have hargs := denoteArgs_eq_some_resolveEnvArgs hΓ hm op.args hwf.1
          dsimp only [denote, hdrEmitFlat]
          rw [hargs]
          dsimp only [hdrEmit]
          rw [hdec]
          dsimp only [flatOptOp, toTFlat]
          refine congrArg (TFlat.let_ _) ?_
          exact hdrEmitFlat_eq dir tailCArgs tailXArgs ss cMs.tail xMs.tail k
            hvh2 (CtxTypes.push _ hΓ)
            (trieCtxMatch_insertTupEnv hm (someVarsToOpt (Tup.levels dts outVD)))
            hΔ hwf.2
            (fun rest => kC (LoopRotate.tupAppend
              (tupSelectArgs dts (cMs.headD []) (toArgTup (Tup.levels dts outVD))) rest))
            (fun od rest => kCFlat od (LoopRotate.tupAppend
              (tupSelectArgs dts (cMs.headD []) (toArgTup (Tup.levels dts outVD))) rest))
            (fun od rest => hkC od _)
            (fun ex rest => kX ex (LoopRotate.tupAppend
              (tupSelectArgs dts (xMs.headD []) (toArgTup (Tup.levels dts outVD))) rest))
            (fun ex iv ie od rest => kXFlat ex iv ie od (LoopRotate.tupAppend
              (tupSelectArgs dts (xMs.headD []) (toArgTup (Tup.levels dts outVD))) rest))
            (fun iv' ie' Γ' vs' od rest hiv' hΓ' hm' hwf' => hkX iv' ie' Γ' vs' od _
              (by dsimp only [hdrStepCount, HdrStep.tys] at hiv' ⊢; omega) hΓ' hm' hwf')
    | _ => dsimp only [validateHdrFlat] at hvh; contradiction
  | .load t :: ss, cMs, xMs, b, Γ, Δ, vs, ls,
      inVD, outVD, outLD, nv, inVE, sh, tF, eF, nv',
      hvh, hΓ, hm, hΔ, hwf, kC, kCFlat, hkC, kX, kXFlat, hkX => by
    cases b with
    | load t' a k =>
      dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
      dsimp only [validateHdrFlat] at hvh
      cases hdec : tyDecEq t t' with
      | isFalse _ => rw [hdec] at hvh; contradiction
      | isTrue heq =>
        subst heq
        rw [hdec] at hvh; dsimp only at hvh
        cases hvh2 : validateHdrFlat ss k (nv + 1) with
        | none => rw [hvh2] at hvh; contradiction
        | some val =>
          rcases val with ⟨sh2, tF2, eF2, nv2⟩
          rw [hvh2] at hvh
          have h_eq : tF2 = tF ∧ eF2 = eF ∧ nv2 = nv' := by
            injection hvh with h0
            exact ⟨congrArg (·.2.1) h0, congrArg (·.2.2.1) h0, congrArg (·.2.2.2) h0⟩
          rcases h_eq with ⟨rfl, rfl, rfl⟩
          have ha := denoteArg_eq_some_resolveEnvArg hΓ hm a hwf.1
          dsimp only [denote, hdrEmitFlat]
          rw [ha]
          dsimp only [hdrEmit]
          rw [hdec]
          dsimp only [toTFlat]
          refine congrArg (TFlat.load t _) ?_
          exact hdrEmitFlat_eq dir tailCArgs tailXArgs ss cMs.tail xMs.tail k
            hvh2 (.cons hΓ) (hm.cons t (some (.var outVD))) hΔ hwf.2
            (fun rest => kC (LoopRotate.tupAppend
              (tupSelectArgs [t] (cMs.headD []) (.var outVD, ())) rest))
            (fun od rest => kCFlat od (LoopRotate.tupAppend
              (tupSelectArgs [t] (cMs.headD []) (.var outVD, ())) rest))
            (fun od rest => hkC od _)
            (fun ex rest => kX ex (LoopRotate.tupAppend
              (tupSelectArgs [t] (xMs.headD []) (.var outVD, ())) rest))
            (fun ex iv ie od rest => kXFlat ex iv ie od (LoopRotate.tupAppend
              (tupSelectArgs [t] (xMs.headD []) (.var outVD, ())) rest))
            (fun iv' ie' Γ' vs' od rest hiv' hΓ' hm' hwf' => hkX iv' ie' Γ' vs' od _
              (by
                simp only [hdrStepCount, HdrStep.tys, List.length_cons, List.length_nil]
                  at hiv' ⊢
                omega)
              hΓ' hm' hwf')
    | _ => dsimp only [validateHdrFlat] at hvh; contradiction

/-! ## 3. Main `rewriteRotWithFlat` Equivalence & `loopRotateFlat_eq` -/

private abbrev ValEx (allowHdr : Bool) (p : RotPlan) {rs : List Ty}
    (tf : TFlat rs) (nv inLD : Nat) : Prop :=
  ∃ inLEb, (validateRotPlanWithFlat allowHdr p tf nv inLD inLEb).isSome

private abbrev ValExB (allowHdr : Bool) (ps : List RotPlan) {rs : List Ty}
    {sig : List (List Ty)} (tb : TBlocks rs sig) (nv inLD : Nat) : Prop :=
  ∃ inLEb, (validateRotPlanWithFlat.validateKeepBFlat allowHdr ps tb nv inLD inLEb).isSome

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
  | .leaf, tf, Γ, Δ, vs, ls, inVD, inLD, outVD, outLD, inVE, inLE, _, hΓ, hm, hΔ, hrl, hwf => by
    rw [rewriteRotWith.eq_1]
    exact flatExprFlat_eq tf hΓ hm hΔ hrl hwf
  | .letP p, tf, Γ, Δ, vs, ls, inVD, inLD, outVD, outLD, inVE, inLE,
      hval, hΓ, hm, hΔ, hrl, hwf => by
    rcases hval with ⟨inLEb, hval⟩
    cases tf with
    | let_ op k =>
      rename_i ts
      dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
      dsimp only [validateRotPlanWithFlat] at hval
      simp only [Bind.bind, Option.bind] at hval
      have hval' : ValEx allowHdr p k (inVD + ts.length) inLD := by
        refine ⟨inLEb, ?_⟩
        cases hsub : validateRotPlanWithFlat allowHdr p k (inVD + ts.length) inLD inLEb
        · rw [hsub] at hval; contradiction
        · rfl
      have hargs := denoteArgs_eq_some_resolveEnvArgs hΓ hm op.args hwf.1
      dsimp only [denote, rewriteRotWithFlat]
      rw [hargs]
      rw [rewriteRotWith.eq_2]
      dsimp only [flatOptOp, toTFlat]
      refine congrArg (TFlat.let_ _) ?_
      exact rewriteRotWithFlat_eq allowHdr p k hval' (CtxTypes.push _ hΓ)
        (trieCtxMatch_insertTupEnv hm (someVarsToOpt (Tup.levels ts outVD)))
        hΔ hrl hwf.2
    | _ => dsimp only [validateRotPlanWithFlat] at hval; contradiction
  | .loadP p, tf, Γ, Δ, vs, ls, inVD, inLD, outVD, outLD, inVE, inLE,
      hval, hΓ, hm, hΔ, hrl, hwf => by
    rcases hval with ⟨inLEb, hval⟩
    cases tf with
    | load t a k =>
      dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
      dsimp only [validateRotPlanWithFlat] at hval
      simp only [Bind.bind, Option.bind] at hval
      have hval' : ValEx allowHdr p k (inVD + 1) inLD := by
        refine ⟨inLEb, ?_⟩
        cases hsub : validateRotPlanWithFlat allowHdr p k (inVD + 1) inLD inLEb
        · rw [hsub] at hval; contradiction
        · rfl
      have ha := denoteArg_eq_some_resolveEnvArg hΓ hm a hwf.1
      dsimp only [denote, rewriteRotWithFlat]
      rw [ha]
      rw [rewriteRotWith.eq_3]
      dsimp only [toTFlat]
      refine congrArg (TFlat.load t _) ?_
      exact rewriteRotWithFlat_eq allowHdr p k hval' (.cons hΓ) (hm.cons t (some (.var outVD)))
        hΔ hrl hwf.2
    | _ => dsimp only [validateRotPlanWithFlat] at hval; contradiction
  | .storeP p, tf, Γ, Δ, vs, ls, inVD, inLD, outVD, outLD, inVE, inLE,
      hval, hΓ, hm, hΔ, hrl, hwf => by
    rcases hval with ⟨inLEb, hval⟩
    cases tf with
    | store v a k =>
      dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
      dsimp only [validateRotPlanWithFlat] at hval
      simp only [Bind.bind, Option.bind] at hval
      have hval' : ValEx allowHdr p k inVD inLD := by
        refine ⟨inLEb, ?_⟩
        cases hsub : validateRotPlanWithFlat allowHdr p k inVD inLD inLEb
        · rw [hsub] at hval; contradiction
        · rfl
      have hv := denoteArg_eq_some_resolveEnvArg hΓ hm v hwf.1.1
      have ha := denoteArg_eq_some_resolveEnvArg hΓ hm a hwf.1.2
      dsimp only [denote, rewriteRotWithFlat]
      rw [hv, ha]
      rw [rewriteRotWith.eq_4]
      dsimp only [toTFlat]
      exact congrArg (TFlat.store _ _)
        (rewriteRotWithFlat_eq allowHdr p k hval' hΓ hm hΔ hrl hwf.2)
    | _ => dsimp only [validateRotPlanWithFlat] at hval; contradiction
  | .callP p, tf, Γ, Δ, vs, ls, inVD, inLD, outVD, outLD, inVE, inLE,
      hval, hΓ, hm, hΔ, hrl, hwf => by
    rcases hval with ⟨inLEb, hval⟩
    cases tf with
    | call f bs args k =>
      dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
      dsimp only [validateRotPlanWithFlat] at hval
      simp only [Bind.bind, Option.bind] at hval
      have hval' : ValEx allowHdr p k (inVD + bs.length) inLD := by
        refine ⟨inLEb, ?_⟩
        cases hsub : validateRotPlanWithFlat allowHdr p k (inVD + bs.length) inLD inLEb
        · rw [hsub] at hval; contradiction
        · rfl
      have hargs := denoteArgs_eq_some_resolveEnvArgs hΓ hm args hwf.1
      dsimp only [denote, rewriteRotWithFlat]
      rw [hargs]
      rw [rewriteRotWith.eq_5]
      dsimp only [toTFlat]
      refine congrArg (TFlat.call f bs _) ?_
      exact rewriteRotWithFlat_eq allowHdr p k hval' (CtxTypes.push _ hΓ)
        (trieCtxMatch_insertTupEnv hm (someVarsToOpt (Tup.levels bs outVD)))
        hΔ hrl hwf.2
    | _ => dsimp only [validateRotPlanWithFlat] at hval; contradiction
  | .jnzP tp ep, tf, Γ, Δ, vs, ls, inVD, inLD, outVD, outLD, inVE, inLE,
      hval, hΓ, hm, hΔ, hrl, hwf => by
    rcases hval with ⟨inLEb, hval⟩
    cases tf with
    | jnz c t e =>
      dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
      dsimp only [validateRotPlanWithFlat] at hval
      simp only [Bind.bind, Option.bind] at hval
      have htval : ValEx allowHdr tp t inVD inLD := by
        refine ⟨inLEb, ?_⟩
        cases hsub : validateRotPlanWithFlat allowHdr tp t inVD inLD inLEb
        · rw [hsub] at hval; contradiction
        · rfl
      have heval : ValEx allowHdr ep e inVD inLD := by
        refine ⟨inLEb, ?_⟩
        cases hsub1 : validateRotPlanWithFlat allowHdr tp t inVD inLD inLEb
        · rw [hsub1] at hval; contradiction
        · rw [hsub1] at hval; dsimp only at hval
          cases hsub2 : validateRotPlanWithFlat allowHdr ep e inVD inLD inLEb
          · rw [hsub2] at hval; contradiction
          · rfl
      have hc := denoteArg_eq_some_resolveEnvArg hΓ hm c hwf.1.1
      dsimp only [denote, rewriteRotWithFlat]
      rw [hc]
      rw [rewriteRotWith.eq_6]
      dsimp only [toTFlat]
      exact congr (congrArg (TFlat.jnz _)
        (rewriteRotWithFlat_eq allowHdr tp t htval hΓ hm hΔ hrl hwf.1.2))
        (rewriteRotWithFlat_eq allowHdr ep e heval hΓ hm hΔ hrl hwf.2)
    | jump j args =>
      rename_i ts
      cases tp with
      | leaf =>
        cases ep with
        | leaf =>
          dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
          obtain ⟨w₁, w₂, hres, hlk, hmrel⟩ := hrl.resolveLabel_rel hΔ hwf.1
          have hargs := denoteArgs_eq_some_resolveEnvArgs hΓ hm args hwf.2
          dsimp only [denote, rewriteRotWithFlat]
          rw [hlk, hargs]
          cases allowHdr
          · dsimp only [ite_false]
            rw [rewriteRotWith.eq_def]
            rfl
          · dsimp only [ite_true]
            rw [hres]
            cases w₁ <;> cases w₂ <;> simp only [RotLFlatMatch] at hmrel
            · subst hmrel; rw [rewriteRotWith.eq_9]; rfl
            · rw [rewriteRotWith.eq_8]; exact (hmrel outVD outLD _).symm
            · rcases hmrel with ⟨rfl, _⟩; rw [rewriteRotWith.eq_7]; rfl
            · rw [rewriteRotWith.eq_10]; rfl
        | _ => dsimp only [validateRotPlanWithFlat] at hval; contradiction
      | _ => dsimp only [validateRotPlanWithFlat] at hval; contradiction
    | _ => dsimp only [validateRotPlanWithFlat] at hval; contradiction
  | .groupKeep bsP kP, tf, Γ, Δ, vs, ls, inVD, inLD, outVD, outLD,
      inVE, inLE, hval, hΓ, hm, hΔ, hrl, hwf => by
    rcases hval with ⟨inLEb, hval⟩
    cases tf with
    | group bs k =>
      rename_i sig
      dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
      dsimp only [validateRotPlanWithFlat] at hval
      simp only [Bind.bind, Option.bind] at hval
      have hbsval : ValExB allowHdr bsP bs inVD (inLD + sig.length) := by
        refine ⟨insertTupEnv inLD inLEb (trueLabels sig), ?_⟩
        cases hsub : validateRotPlanWithFlat.validateKeepBFlat allowHdr bsP bs inVD
            (inLD + sig.length) (insertTupEnv inLD inLEb (trueLabels sig))
        · rw [hsub] at hval; contradiction
        · rfl
      have hkval : ValEx allowHdr kP k inVD (inLD + sig.length) := by
        refine ⟨insertTupEnv inLD inLEb (trueLabels sig), ?_⟩
        cases hsub1 : validateRotPlanWithFlat.validateKeepBFlat allowHdr bsP bs inVD
            (inLD + sig.length) (insertTupEnv inLD inLEb (trueLabels sig))
        · rw [hsub1] at hval; contradiction
        · rw [hsub1] at hval; dsimp only at hval
          cases hsub2 : validateRotPlanWithFlat allowHdr kP k inVD (inLD + sig.length)
              (insertTupEnv inLD inLEb (trueLabels sig))
          · rw [hsub2] at hval; contradiction
          · rfl
      dsimp only [denote, rewriteRotWithFlat]
      rw [rewriteRotWith.eq_11]
      dsimp only [toTFlat]
      have hrl' : TrieRelMatch (RotLFlatMatch (rs := rs)) (inLD + sig.length)
          (insertTupEnv inLD inLE (wrapKeepLabelsFlat (Tup.levels sig outLD)))
          (pushTup (wrapKeepLabels (Tup.levels sig outLD)) ls) :=
        hrl.pushTup (wrapKeepLabelsFlat_rel (Tup.levels sig outLD))
      rw [rewriteKeepBFlat_eq allowHdr bsP bs hbsval hΓ hm (CtxTypes.push _ hΔ) hrl' hwf.1,
        rewriteRotWithFlat_eq allowHdr kP k hkval hΓ hm (CtxTypes.push _ hΔ) hrl' hwf.2]
    | _ => dsimp only [validateRotPlanWithFlat] at hval; contradiction
  | .groupRot dir hdr contMasks exitMode contP exitP entryP, tf,
      Γ, Δ, vs, ls, inVD, inLD, outVD, outLD, inVE, inLE, hval, hΓ, hm, hΔ, hrl, hwf => by
    rcases hval with ⟨inLEb, hval⟩
    cases tf with
    | group bs k =>
      rename_i sig
      cases sig with
      | nil =>
        cases bs
        dsimp only [validateRotPlanWithFlat] at hval; contradiction
      | cons ts sig' =>
        cases sig' with
        | cons _ _ =>
          cases bs
          rename_i bs'
          cases bs'
          dsimp only [validateRotPlanWithFlat] at hval; contradiction
        | nil =>
          cases bs with
          | cons b bs' =>
            cases bs'
            dsimp only [TFlat.wfCheck, TBlocks.wfCheck] at hwf
            simp only [Bool.and_eq_true] at hwf
            dsimp only [validateRotPlanWithFlat] at hval
            cases hvh : validateHdrFlat hdr b (inVD + ts.length) with
            | none => rw [hvh] at hval; contradiction
            | some val =>
              rcases val with ⟨sh, armT, armE, nv'⟩
              rw [hvh] at hval; simp only [Bind.bind, Option.bind] at hval
              let armCont := if dir then armT else armE
              let armExit := if dir then armE else armT
              let isPart := isPartialMasks hdr contMasks
              have hsc_val : ValEx (allowHdr || isPart) contP armCont
                  (inVD + ts.length + hdrStepCount hdr) (inLD + 1) := by
                refine ⟨inLEb.insert inLD ⟨ts, true⟩, ?_⟩
                cases hsub : validateRotPlanWithFlat (allowHdr || isPart) contP armCont
                    (inVD + ts.length + hdrStepCount hdr) (inLD + 1)
                    (inLEb.insert inLD ⟨ts, true⟩) with
                | none => rw [hsub] at hval; contradiction
                | some _ => rfl
              have hsx_val : ValEx allowHdr exitP armExit
                  (inVD + ts.length + hdrStepCount hdr) (inLD + 1) := by
                refine ⟨inLEb.insert inLD ⟨ts, false⟩, ?_⟩
                cases hsub1 : validateRotPlanWithFlat (allowHdr || isPart) contP armCont
                    (inVD + ts.length + hdrStepCount hdr) (inLD + 1)
                    (inLEb.insert inLD ⟨ts, true⟩) with
                | none => rw [hsub1] at hval; contradiction
                | some _ =>
                  rw [hsub1] at hval; dsimp only at hval
                  cases hsub2 : validateRotPlanWithFlat allowHdr exitP armExit
                      (inVD + ts.length + hdrStepCount hdr) (inLD + 1)
                      (inLEb.insert inLD ⟨ts, false⟩) with
                  | none => rw [hsub2] at hval; contradiction
                  | some _ => rfl
              have hse_val : ValEx allowHdr entryP k inVD (inLD + 1) := by
                refine ⟨inLEb.insert inLD ⟨ts, true⟩, ?_⟩
                cases hsub1 : validateRotPlanWithFlat (allowHdr || isPart) contP armCont
                    (inVD + ts.length + hdrStepCount hdr) (inLD + 1)
                    (inLEb.insert inLD ⟨ts, true⟩) with
                | none => rw [hsub1] at hval; contradiction
                | some _ =>
                  rw [hsub1] at hval; dsimp only at hval
                  cases hsub2 : validateRotPlanWithFlat allowHdr exitP armExit
                      (inVD + ts.length + hdrStepCount hdr) (inLD + 1)
                      (inLEb.insert inLD ⟨ts, false⟩) with
                  | none => rw [hsub2] at hval; contradiction
                  | some _ =>
                    rw [hsub2] at hval; dsimp only at hval
                    cases hsub3 : validateRotPlanWithFlat allowHdr entryP k inVD (inLD + 1)
                        (inLEb.insert inLD ⟨ts, true⟩) with
                    | none => rw [hsub3] at hval; contradiction
                    | some _ => rfl
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
                split
                · rename_i hpart
                  dsimp only [toTFlat, toTBlocks, Tup.levels, pushTup]
                  have hlen2 : [rotSig hdr contMasks ts, ts].length = 2 := rfl
                  rw [hlen2]
                  let J_rot := outLD_l
                  let J_hdr := outLD_l + 1
                  let outLD' := outLD_l + 2
                  let rotParams := Tup.levels (rotSig hdr contMasks ts) outVD
                  let xs := splitTail hdr contMasks rotParams
                  have hpeel := hdrPeelFlat_of_validateHdr dir true hdr contMasks rotParams b
                    (Γ := pushTypes ts Γ) (Δ := [ts] ++ Δ)
                    (vs := pushTup (someVarsToOpt xs) vs)
                    (inVD := inVD + ts.length)
                    (inVE := insertTupEnv inVD inVE (someVarsToOpt xs))
                    hvh (CtxTypes.push _ hΓ) (trieCtxMatch_insertTupEnv hm _) hwf.1.1
                  rcases hpeel with ⟨iv', ie', Γ', vs', hiv', hpeel_eq, hΓ', hm', hwf', hpeel_den⟩
                  subst hiv'
                  have htrue_eq : (true == dir) = dir := by cases dir <;> rfl
                  simp only [htrue_eq] at hpeel_eq hwf' hpeel_den
                  rw [hpeel_eq]
                  simp only [rotBodyExpr, Blocks.get]
                  have hlbl_ek : TrieRelMatch (RotLFlatMatch (rs := rs)) (inLD + 1)
                      (inLE.insert inLD ⟨ts, .expandOrKeep (mkHdrContFlat J_rot) J_hdr⟩)
                      (⟨ts, RotL.expandOrKeep (mkHdrCont J_rot) J_hdr⟩ :: ls) :=
                    hrl.cons ⟨rfl, hmk J_rot⟩
                  have hlbl_ex : TrieRelMatch (RotLFlatMatch (rs := rs)) (inLD + 1)
                      (inLE.insert inLD ⟨ts, .expand (mkHdrContFlat J_rot)⟩)
                      (⟨ts, RotL.expand (mkHdrCont J_rot)⟩ :: ls) :=
                    hrl.cons (hmk J_rot)
                  have hsc_val' : ValEx true contP armCont
                      (inVD + ts.length + hdrStepCount hdr) (inLD + 1) := by
                    simpa [isPart, hpart] using hsc_val
                  have hb0 := rewriteRotWithFlat_eq true contP armCont hsc_val' hΓ' hm'
                    (CtxTypes.cons (v := RotL.expandOrKeep (mkHdrCont J_rot) J_hdr) hΔ)
                    hlbl_ek hwf'
                    (outVD := outVD + (rotSig hdr contMasks ts).length) (outLD := outLD')
                  have hden0 := hpeel_den
                    (⟨ts, RotL.expandOrKeep (mkHdrCont J_rot) J_hdr⟩ :: ls)
                    (CtxTypes.cons (v := RotL.expandOrKeep (mkHdrCont J_rot) J_hdr) hΔ)
                  have hk0 := rewriteRotWithFlat_eq allowHdr entryP k hse_val hΓ hm
                    (CtxTypes.cons (v := RotL.expand (mkHdrCont J_rot)) hΔ)
                    hlbl_ex hwf.2 (outVD := outVD) (outLD := outLD')
                  have hb1 : toTFlat (mkHdrCont J_rot (toArgTup (Tup.levels ts outVD)))
                      (outVD + ts.length) outLD' =
                      mkHdrContFlat J_rot (outVD + ts.length) outLD'
                        (toArgTup (Tup.levels ts outVD)) :=
                    (hmk J_rot (outVD + ts.length) outLD' _).symm
                  dsimp only [armCont] at hb0
                  dsimp only [J_rot, J_hdr, outLD', rotParams, xs] at hden0 hb0 hb1 hk0
                  rw [hden0, hb0, hb1, hk0]
                · rename_i hpart
                  dsimp only [toTFlat, toTBlocks, Tup.levels, pushTup]
                  have hlen1 : [rotSig hdr contMasks ts].length = 1 := rfl
                  rw [hlen1]
                  let J_rot := outLD_l
                  let outLD' := outLD_l + 1
                  let rotParams := Tup.levels (rotSig hdr contMasks ts) outVD
                  let xs := splitTail hdr contMasks rotParams
                  have hpeel := hdrPeelFlat_of_validateHdr dir true hdr contMasks rotParams b
                    (Γ := pushTypes ts Γ) (Δ := [ts] ++ Δ)
                    (vs := pushTup (someVarsToOpt xs) vs)
                    (inVD := inVD + ts.length)
                    (inVE := insertTupEnv inVD inVE (someVarsToOpt xs))
                    hvh (CtxTypes.push _ hΓ) (trieCtxMatch_insertTupEnv hm _) hwf.1.1
                  rcases hpeel with ⟨iv', ie', Γ', vs', hiv', hpeel_eq, hΓ', hm', hwf', hpeel_den⟩
                  subst hiv'
                  have htrue_eq : (true == dir) = dir := by cases dir <;> rfl
                  simp only [htrue_eq] at hpeel_eq hwf' hpeel_den
                  rw [hpeel_eq]
                  simp only [rotBodyExpr, Blocks.get]
                  have hlbl_ex : TrieRelMatch (RotLFlatMatch (rs := rs)) (inLD + 1)
                      (inLE.insert inLD ⟨ts, .expand (mkHdrContFlat J_rot)⟩)
                      (⟨ts, RotL.expand (mkHdrCont J_rot)⟩ :: ls) :=
                    hrl.cons (hmk J_rot)
                  have hpartF : isPartialMasks hdr contMasks = false := by
                    cases hm0 : isPartialMasks hdr contMasks
                    · rfl
                    · exact absurd hm0 hpart
                  have hsc_val' : ValEx allowHdr contP armCont
                      (inVD + ts.length + hdrStepCount hdr) (inLD + 1) := by
                    simpa [isPart, hpartF, Bool.or_false] using hsc_val
                  have hb0 := rewriteRotWithFlat_eq allowHdr contP armCont hsc_val' hΓ' hm'
                    (CtxTypes.cons (v := RotL.expand (mkHdrCont J_rot)) hΔ)
                    hlbl_ex hwf'
                    (outVD := outVD + (rotSig hdr contMasks ts).length) (outLD := outLD')
                  have hden0 := hpeel_den
                    (⟨ts, RotL.expand (mkHdrCont J_rot)⟩ :: ls)
                    (CtxTypes.cons (v := RotL.expand (mkHdrCont J_rot)) hΔ)
                  have hk0 := rewriteRotWithFlat_eq allowHdr entryP k hse_val hΓ hm
                    (CtxTypes.cons (v := RotL.expand (mkHdrCont J_rot)) hΔ)
                    hlbl_ex hwf.2 (outVD := outVD) (outLD := outLD')
                  dsimp only [armCont] at hb0
                  dsimp only [J_rot, outLD', rotParams, xs] at hden0 hb0 hk0
                  rw [hden0, hb0, hk0]
              cases exitMode with
              | inline =>
                dsimp only [denote, denoteB, rewriteRotWithFlat]
                rw [rewriteRotWith.eq_12]
                simp only [Blocks.get, exitLabels, pushTup]
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
                        (inLD + 1) (inLE.insert inLD ⟨ts, .dead⟩) od curLD))
                  ?_
                intro J_rot curVD curLD args
                refine (hdrEmitFlat_eq dir args args hdr contMasks [] b hvh (CtxTypes.push _ hΓ)
                  (trieCtxMatch_insertTupEnv hm _) hΔ_b hwf.1.1 _ _ ?_ _ _ ?_).symm
                · intro _ _; rfl
                · intro iv' ie' Γ' vs' od _ hiv' hΓ' hm' hwf'
                  subst hiv'
                  have h_f : (if dir then armE else armT) = armExit := rfl
                  rw [h_f] at hwf' ⊢
                  exact rewriteRotWithFlat_eq allowHdr exitP armExit hsx_val hΓ' hm' hΔ_b
                    hrl_dead hwf'
              | wrap xsMask hMasks =>
                dsimp only [denote, denoteB, rewriteRotWithFlat]
                rw [rewriteRotWith.eq_13]
                dsimp only [toTFlat, toTBlocks, Tup.levels]
                let J_exit := outLD
                let exitParams := Tup.levels (exitSig hdr hMasks xsMask ts) outVD
                let xsTail := splitTail hdr hMasks exitParams
                let xsOpt := tupWiden ts xsMask xsTail
                have hpeel := hdrPeelFlat_of_validateHdr dir false hdr hMasks exitParams b
                  (Γ := pushTypes ts Γ) (Δ := [ts] ++ Δ)
                  (vs := pushTup xsOpt vs)
                  (inVD := inVD + ts.length) (inVE := insertTupEnv inVD inVE xsOpt)
                  hvh (CtxTypes.push _ hΓ) (trieCtxMatch_insertTupEnv hm _) hwf.1.1
                rcases hpeel with ⟨iv', ie', Γ', vs', hiv', hpeel_eq, hΓ', hm', hwf', hpeel_den⟩
                subst hiv'
                have hfalse_eq : (false == dir) = !dir := by cases dir <;> rfl
                have hif_eq : (if !dir then armT else armE) = armExit := by cases dir <;> rfl
                simp only [hfalse_eq, hif_eq] at hpeel_eq hwf' hpeel_den
                rw [hpeel_eq]
                simp only [Blocks.get, exitLabels, pushTup]
                have hden_ex := hpeel_den (⟨ts, RotL.dead⟩ :: ls) hΔ_b
                have hex_rw := rewriteRotWithFlat_eq allowHdr exitP armExit hsx_val hΓ' hm' hΔ_b
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
                        TFlat.jump (idxLabel curLD J_exit) (idxArgs od exArgs)))
                  ?_
                · exact congr (congrArg TFlat.group
                    (congrArg (TBlocks.cons · .nil) (hden_ex ▸ hex_rw))) heloop
                · intro J_rot curVD curLD args
                  refine (hdrEmitFlat_eq dir args (tupSelectArgs ts xsMask args) hdr contMasks
                    hMasks b hvh (CtxTypes.push _ hΓ) (trieCtxMatch_insertTupEnv hm _) hΔ_b hwf.1.1
                    (fun rotArgs => Expr.jump J_rot rotArgs)
                    (fun od rotArgs => TFlat.jump (idxLabel curLD J_rot) (idxArgs od rotArgs))
                    (fun _ _ => rfl)
                    (fun _ exArgs => Expr.jump J_exit exArgs)
                    (fun _ _ _ od exArgs =>
                      TFlat.jump (idxLabel curLD J_exit) (idxArgs od exArgs))
                    (fun _ _ _ _ _ _ _ _ _ _ => rfl)).symm
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
    exact flatBlocksFlat_eq tb hΓ hm hΔ hrl hwf
  | _ :: _, _, .nil, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by
    dsimp only [denoteB, rewriteRotWithFlat.rewriteKeepBFlat]
    rw [rewriteRotWith.rewriteKeepB.eq_3]
    rfl
  | p :: ps, _, .cons (ts := ts) b bs, Γ, Δ, vs, ls, inVD, inLD, outVD, outLD, inVE, inLE,
      hval, hΓ, hm, hΔ, hrl, hwf => by
    dsimp only [TBlocks.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    rcases hval with ⟨inLEb, hval⟩
    dsimp only [validateRotPlanWithFlat.validateKeepBFlat] at hval
    have hp_val : ValEx allowHdr p b (inVD + ts.length) inLD := by
      refine ⟨inLEb, ?_⟩
      cases hsub : validateRotPlanWithFlat allowHdr p b (inVD + ts.length) inLD inLEb with
      | none => rw [hsub] at hval; contradiction
      | some _ => rfl
    have hps_val : ValExB allowHdr ps bs inVD inLD := by
      refine ⟨inLEb, ?_⟩
      cases hsub1 : validateRotPlanWithFlat allowHdr p b (inVD + ts.length) inLD inLEb with
      | none => rw [hsub1] at hval; contradiction
      | some _ =>
        rw [hsub1] at hval; simp only [Bind.bind, Option.bind] at hval
        cases hsub2 : validateRotPlanWithFlat.validateKeepBFlat allowHdr ps bs inVD inLD inLEb with
        | none => rw [hsub2] at hval; contradiction
        | some _ => rfl
    dsimp only [denoteB, rewriteRotWithFlat.rewriteKeepBFlat, toTBlocks]
    rw [rewriteRotWith.rewriteKeepB.eq_2]
    refine congr (congrArg TBlocks.cons ?_) ?_
    · exact rewriteRotWithFlat_eq allowHdr p b hp_val (CtxTypes.push _ hΓ)
        (trieCtxMatch_insertTupEnv hm (someVarsToOpt (Tup.levels ts outVD)))
        hΔ hrl hwf.1
    · exact rewriteKeepBFlat_eq allowHdr ps bs hps_val hΓ hm hΔ hrl hwf.2
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
      (CtxTypes.push _ .nil) (CtxLevels.pushTup CtxLevels.nil) .nil
      (.empty) hwf
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
        hvalEx (CtxTypes.push _ .nil) hm0
        .nil (.empty _) hwf (outVD := as.length) (outLD := 0)
      simpa using hrw.symm
    · rename_i _ hnone
      rw [hnone]
      exact hr.symm
  · exact hr.symm

/-- `denoteFunc (loopRotateFlat as tf cfg) = Func.loopRotate (denoteFunc tf) cfg`
under `wfCheck = true`. -/
theorem denoteFunc_loopRotateFlat {as rs : List Ty} (tf : TFlat rs)
    (cfg : LoopRotate.RotConfig := LoopRotate.defaultRotConfig)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    denoteFunc (as := as) (loopRotateFlat as tf cfg) =
      Func.loopRotate (denoteFunc (as := as) tf) cfg := by
  rw [loopRotateFlat_eq tf cfg hwf]
  exact Func.renorm_eq_self (Func.loopRotate_wf (Func.wf_of_denote (as := as) tf rfl) cfg)

/-- `loopRotateFlat` preserves `wfCheck`. -/
theorem loopRotateFlat_wfCheck {as rs : List Ty} (tf : TFlat rs)
    (cfg : LoopRotate.RotConfig := LoopRotate.defaultRotConfig)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    (loopRotateFlat as tf cfg).wfCheck (pushTypes as []) [] = true := by
  rw [loopRotateFlat_eq tf cfg hwf]
  exact PassFlatKit.reifyFunc_wfCheck
    (Func.loopRotate_wf (Func.wf_of_denote (as := as) tf rfl) cfg)

/-- `(loopRotateFlatFn f cfg).toFn = ⟨f.name, f.as, f.rs, Func.loopRotate f.toFn.body cfg⟩`
under `wfCheck = true`. -/
theorem loopRotateFlatFn_toFn (f : TFlatFn) (hwf : f.wfCheck = true)
    (cfg : LoopRotate.RotConfig := LoopRotate.defaultRotConfig) :
    (loopRotateFlatFn f cfg).toFn = ⟨f.name, f.as, f.rs, Func.loopRotate f.toFn.body cfg⟩ := by
  dsimp only [loopRotateFlatFn, TFlatFn.toFn]
  rw [denoteFunc_loopRotateFlat f.body cfg hwf]

/-- `loopRotateFlatFn` preserves `TFlatFn.wfCheck`. -/
theorem loopRotateFlatFn_wfCheck (f : TFlatFn) (hwf : f.wfCheck = true)
    (cfg : LoopRotate.RotConfig := LoopRotate.defaultRotConfig) :
    (loopRotateFlatFn f cfg).wfCheck = true :=
  loopRotateFlat_wfCheck f.body cfg hwf

end OptFlatLoop
end LeanQbe.T
