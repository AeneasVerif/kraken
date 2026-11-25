module

public import LeanQbe.T.Opt
public import LeanQbe.T.Wf
public import LeanQbe.T.WP
public import LeanQbe.T.FlatLemmas
public import LeanQbe.T.GvnLemmas
public import LeanQbe.T.InlineLemmas
import LeanQbe.T.OptUtilLemmas
import LeanQbe.T.WfLemmas
import LeanQbe.T.WPLemmas
import LeanQbe.T.FoldLemmas
import LeanQbe.T.CanonLemmas
import LeanQbe.T.CopyLemmas
import LeanQbe.T.DceLemmas
import LeanQbe.T.DceParamLemmas
import LeanQbe.T.DivConstLemmas
import LeanQbe.T.MemLoadLemmas
import LeanQbe.T.PeelLemmas
import LeanQbe.T.IfOptLemmas
import LeanQbe.T.SimplifyGroupPlanLemmas
import LeanQbe.T.LicmLemmas
import LeanQbe.T.AddrRangeOptLemmas
import LeanQbe.T.LoopRotateLemmas
import LeanQbe.T.CondThreadOptLemmas
import LeanQbe.T.ZeroPeelLemmas
import LeanQbe.T.AssumeBitsLemmas

/-!
# Correctness of the Staged Typed-IR Mid-End Pipeline

Composes relational well-formedness (`*_wf`) and WP refinement (`*_spec`) across `Func.opt`,
`Func.earlyOpt`, `Func.lateOpt`, `Fn.renorm`, and `Module.optInline`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T

/-- The legacy mid-end pipeline preserves well-formedness across every pass. -/
theorem Func.opt_wf {as rs : List Ty} {f : Func as rs} (hf : f.Wf) : (Func.opt f).Wf :=
  Func.dceP_wf (Func.fold_wf (Func.copy_wf (Func.gvn_wf (Func.copy_wf (Func.fold_wf hf)))))

/-- The legacy mid-end pipeline refines function contracts across every pass. -/
theorem Func.opt_spec {as rs : List Ty} {f : Func as rs} (hf : f.Wf) {Γ : Env}
    {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Func.spec Γ f xs m Q X) : Func.spec Γ (Func.opt f) xs m Q X := by
  have hf1 := Func.fold_wf hf
  have hs1 := Func.fold_spec hf h
  have hf2 := Func.copy_wf hf1
  have hs2 := Func.copy_spec hf1 hs1
  have hf3 := Func.gvn_wf hf2
  have hs3 := Func.gvn_spec hf2 hs2
  have hf4 := Func.copy_wf hf3
  have hs4 := Func.copy_spec hf3 hs3
  have hf5 := Func.fold_wf hf4
  have hs5 := Func.fold_spec hf4 hs4
  exact Func.dceP_spec hf5 hs5

/-- `Func.simplifyGroupFast` preserves well-formedness. -/
theorem Func.simplifyGroupFast_wf {as rs : List Ty} (f : Func as rs) :
    (Func.simplifyGroupFast f).Wf := by
  rw [Func.simplifyGroupFast_eq]
  dsimp only
  by_cases h : hasSimpGroup (tflatLoops (reifyFunc f) ≤ 1) (reifyFunc f) <;>
    simp only [h, ↓reduceIte, Bool.false_eq_true]
  · exact Func.renorm_wf _
  · exact Func.renorm_wf f

/-- `Func.simplifyGroupFast` refines function contracts. -/
theorem Func.simplifyGroupFast_spec {as rs : List Ty} {f : Func as rs} (hf : f.Wf) {Γ : Env}
    {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Func.spec Γ f xs m Q X) : Func.spec Γ (Func.simplifyGroupFast f) xs m Q X := by
  have hwf := Func.renorm_wf f
  have hsp := Func.renorm_spec hf h
  rw [Func.simplifyGroupFast_eq]
  dsimp only
  by_cases hc : hasSimpGroup (tflatLoops (reifyFunc f) ≤ 1) (reifyFunc f) <;>
    simp only [hc, ↓reduceIte, Bool.false_eq_true]
  · exact Func.renorm_spec (Func.simplifyGroupPlan_wf hwf) (Func.simplifyGroupPlan_spec hwf hsp)
  · exact hsp

/-- `Func.peelFast` preserves well-formedness. -/
theorem Func.peelFast_wf {as rs : List Ty} (f : Func as rs) (budget : Nat := 24) :
    (Func.peelFast f budget).Wf := by
  rw [Func.peelFast_eq f budget]
  dsimp only
  by_cases h : (tflatLoops (reifyFunc f) ≤ 1 && tflatSize (reifyFunc f) ≤ 40) = true <;>
    simp only [h, ↓reduceIte, Bool.false_eq_true]
  · exact Func.renorm_wf _
  · exact Func.renorm_wf f

/-- `Func.peelFast` refines function contracts. -/
theorem Func.peelFast_spec {as rs : List Ty} {f : Func as rs} (hf : f.Wf) {Γ : Env}
    {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost} (budget : Nat := 24)
    (h : Func.spec Γ f xs m Q X) : Func.spec Γ (Func.peelFast f budget) xs m Q X := by
  have hwf := Func.renorm_wf f
  have hsp := Func.renorm_spec hf h
  rw [Func.peelFast_eq f budget]
  dsimp only
  by_cases hc : (tflatLoops (reifyFunc f) ≤ 1 && tflatSize (reifyFunc f) ≤ 40) = true <;>
    simp only [hc, ↓reduceIte, Bool.false_eq_true]
  · exact Func.renorm_spec (Func.peel_wf hwf budget) (Func.peel_spec hwf budget hsp)
  · exact hsp

theorem Blocks.mergeRets_get {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (exit_lbl : L rs) :
    {sig : List (List Ty)} → {bs : Blocks V L rs sig} →
    {ts : List Ty} → (i : Member ts sig) → (xs : Tup V ts) →
    (bs.mergeRets exit_lbl).get i xs = (bs.get i xs).mergeRets exit_lbl
  | _, .cons _ _, _, .here, _ => rfl
  | _, .cons _ _, _, .there i, xs => Blocks.mergeRets_get exit_lbl i xs

theorem Expr.mergeRets_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {exit₁ : L₁ rs} {exit₂ : L₂ rs}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} (hexit : ⟨rs, exit₁, exit₂⟩ ∈ D)
    {e₁ : Expr V₁ L₁ rs} {e₂ : Expr V₂ L₂ rs}
    (hwf : Wf G D e₁ e₂) :
    Wf G D (e₁.mergeRets exit₁) (e₂.mergeRets exit₂) := by
  induction hwf using Wf.induct with
  | let_ hop _ ih =>
    exact .let_ hop fun xs₁ xs₂ => ih xs₁ xs₂ hexit
  | load t ha _ ih =>
    exact .load t ha fun v₁ v₂ => ih v₁ v₂ hexit
  | store hv ha _ ih =>
    exact .store hv ha (ih hexit)
  | call f hargs _ ih =>
    exact .call f hargs fun xs₁ xs₂ => ih xs₁ xs₂ hexit
  | jnz hc _ _ iht ihe =>
    exact .jnz hc (iht hexit) (ihe hexit)
  | jump hj hargs =>
    exact .jump hj hargs
  | ret hvs =>
    exact .jump hexit hvs
  | exit f hargs =>
    exact .exit f hargs
  | hlt =>
    exact .hlt
  | group _ _ ihb ihk =>
    refine .group (fun Js₁ Js₂ => WfB.of_get fun i xs₁ xs₂ => ?_) (fun Js₁ Js₂ => ?_)
    · simp only [Blocks.mergeRets_get]
      exact ihb Js₁ Js₂ i xs₁ xs₂ (List.mem_append_right _ hexit)
    · exact ihk Js₁ Js₂ (List.mem_append_right _ hexit)

/-- `Func.mergeRets` preserves well-formedness. -/
theorem Func.mergeRets_wf {as rs : List Ty} {f : Func as rs} (hf : f.Wf) :
    (Func.mergeRets f).Wf := by
  rw [Func.mergeRets_eq]
  dsimp only
  by_cases hc : tflatRets (reifyFunc f) ≥ 2 <;> simp only [hc, ↓reduceIte]
  · intro V₁ V₂ L₁ L₂ xs₁ xs₂
    dsimp only
    refine .group (sig := [rs])
      (fun (_, ()) (_, ()) => .cons (fun r₁ r₂ => ?_) .nil)
      (fun (exit₁, ()) (exit₂, ()) => ?_)
    · exact .ret (TRel.toArgTup_mem r₁ r₂)
    · have hf_weaken := (hf V₁ V₂ L₁ L₂ xs₁ xs₂).weaken_D
        (D' := [⟨rs, exit₁, exit₂⟩]) (by intro _ hp; nomatch hp)
      exact Expr.mergeRets_wf (List.mem_singleton_self _) hf_weaken
  · exact hf

theorem Expr.mergeRets_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {exit_lbl : Cont rs} (hexit : ∀ vs m, Q vs m → exit_lbl vs m)
    (e : Expr Val Cont rs) : ∀ m, wp Γ Q X e m → wp Γ Q X (e.mergeRets exit_lbl) m := by
  induction e using Expr.induct with
  | let_ op k ih =>
    intro m h
    dsimp only [Expr.mergeRets, wp] at h ⊢
    exact Op.wp_mono (fun r => ih r m) h
  | load t a k ih =>
    intro m ⟨v, hv, h⟩
    dsimp only [Expr.mergeRets, wp]
    exact ⟨v, hv, ih v m h⟩
  | store v a k ih =>
    intro m ⟨hok, h⟩
    dsimp only [Expr.mergeRets, wp]
    exact ⟨hok, ih (storeMem m _ a.val v.val) h⟩
  | call f args k ih =>
    intro m ⟨P, E, hG, hP, hE⟩
    dsimp only [Expr.mergeRets, wp]
    exact ⟨P, E, hG, fun r m' hr => ih r m' (hP r m' hr), hE⟩
  | jnz c t e iht ihe =>
    intro m h
    dsimp only [Expr.mergeRets, wp]
    exact ⟨fun hc => iht m (h.1 hc), fun hc => ihe m (h.2 hc)⟩
  | jump j args =>
    intro m h
    exact h
  | ret vs =>
    intro m h
    dsimp only [Expr.mergeRets, wp] at h ⊢
    exact hexit (vals vs) m h
  | exit f args =>
    intro m h
    exact h
  | hlt =>
    intro m h
    exact h
  | group bodies k ihb ihk =>
    intro m h Js hc
    dsimp only [Expr.mergeRets, wp]
    refine ihk Js m (h Js ?_)
    rw [closed_iff] at hc ⊢
    intro ts i xs m' hb
    have hc' := hc i xs m'
    dsimp only at hc'
    rw [Blocks.mergeRets_get] at hc'
    exact hc' (ihb Js i xs m' hb)

/-- `Func.mergeRets` refines function contracts. -/
theorem Func.mergeRets_spec {as rs : List Ty} {f : Func as rs} (_hf : f.Wf) {Γ : Env}
    {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Func.spec Γ f xs m Q X) : Func.spec Γ (Func.mergeRets f) xs m Q X := by
  rw [Func.mergeRets_eq]
  dsimp only
  by_cases hc : tflatRets (reifyFunc f) ≥ 2 <;> simp only [hc, ↓reduceIte]
  · dsimp only [Func.spec, Func.wp, wp]
    intro (exit_lbl, ()) hClosed
    dsimp only [Closed] at hClosed
    have hexit : ∀ vs m', Q vs m' → exit_lbl vs m' := by
      intro vs m' hq
      have h1 := hClosed.1 vs m'
      change (Q (vals (toArgTup vs)) m' → exit_lbl vs m') at h1
      rw [toArgTup_vals] at h1
      exact h1 hq
    exact Expr.mergeRets_wp hexit (f Val Cont xs) m h
  · exact h

/-- `Func.earlyCore` preserves well-formedness. -/
theorem Func.earlyCore_wf {as rs : List Ty} {f : Func as rs} (hf : f.Wf) :
    (Func.earlyCore f).Wf := by
  rw [Func.earlyCore_eq]
  exact Func.fold_wf (Func.copy_wf (Func.gvn_wf (Func.copy_wf
    (Func.canon_wf (Func.fold_wf hf)))))

/-- `Func.earlyCore` refines function contracts. -/
theorem Func.earlyCore_spec {as rs : List Ty} {f : Func as rs} (hf : f.Wf) {Γ : Env}
    {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Func.spec Γ f xs m Q X) : Func.spec Γ (Func.earlyCore f) xs m Q X := by
  rw [Func.earlyCore_eq]
  have hf1 := Func.fold_wf hf
  have hs1 := Func.fold_spec hf h
  have hf2 := Func.canon_wf hf1
  have hs2 := Func.canon_spec hf1 hs1
  have hf3 := Func.copy_wf hf2
  have hs3 := Func.copy_spec hf2 hs2
  have hf4 := Func.gvn_wf hf3
  have hs4 := Func.gvn_spec hf3 hs3
  have hf5 := Func.copy_wf hf4
  have hs5 := Func.copy_spec hf4 hs4
  exact Func.fold_spec hf5 hs5

/-- Pre-`Legal` mid-end (`Func.earlyOpt`) preserves well-formedness. -/
theorem Func.earlyOpt_wf {as rs : List Ty} {f : Func as rs} (_hf : f.Wf) :
    (Func.earlyOpt f).Wf := by
  rw [Func.earlyOpt_eq]
  exact Func.renorm_wf _

private theorem renorm_spec' {as rs : List Ty} {Γ : Env} {f : Func as rs} (h : f.Wf)
    {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (hw : Func.spec Γ f xs m Q X) :
    Func.spec Γ (Func.renorm f) xs m Q X :=
  Func.renorm_spec h hw

private theorem earlyOpt_tail_spec {as rs : List Ty} {g : Func as rs} (hg : g.Wf) {Γ : Env}
    {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Func.spec Γ g xs m Q X) :
    Func.spec Γ (Func.renorm (Func.dceP (Func.fold (Func.copy
      (Func.zeroPeelWith { peelBudget := 24 } g))))) xs m Q X := by
  have hf10 := Func.zeroPeelWith_wf { peelBudget := 24 } hg
  have hs10 := Func.zeroPeelWith_spec { peelBudget := 24 } hg h
  have hf11 := Func.copy_wf hf10
  have hs11 := Func.copy_spec hf10 hs10
  have hf12 := Func.fold_wf hf11
  have hs12 := Func.fold_spec hf11 hs11
  have hf13 := Func.dceP_wf hf12
  have hs13 := Func.dceP_spec hf12 hs12
  exact renorm_spec' hf13 hs13

/-- Pre-`Legal` mid-end (`Func.earlyOpt`) refines function contracts across every pass. -/
theorem Func.earlyOpt_spec {as rs : List Ty} {f : Func as rs} (hf : f.Wf) {Γ : Env}
    {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Func.spec Γ f xs m Q X) : Func.spec Γ (Func.earlyOpt f) xs m Q X := by
  rw [Func.earlyOpt_eq]
  apply earlyOpt_tail_spec (Func.peelFast_wf _ 24)
  apply Func.peelFast_spec (Func.simplifyGroupFast_wf _) 24
  apply Func.simplifyGroupFast_spec (Func.ifOpt_wf (Func.earlyCore_wf hf))
  apply Func.ifOpt_spec (Func.earlyCore_wf hf)
  exact Func.earlyCore_spec hf h

/-- `Func.lateCorePre` preserves well-formedness. -/
theorem Func.lateCorePre_wf {as rs : List Ty} {f : Func as rs} (hf : f.Wf) :
    (Func.lateCorePre f).Wf := by
  rw [Func.lateCorePre_eq]
  exact Func.copy_wf (Func.divConst_wf (Func.canon_wf (Func.fold_wf hf)))

/-- `Func.lateCorePre` refines function contracts. -/
theorem Func.lateCorePre_spec {as rs : List Ty} {f : Func as rs} (hf : f.Wf) {Γ : Env}
    {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Func.spec Γ f xs m Q X) : Func.spec Γ (Func.lateCorePre f) xs m Q X := by
  rw [Func.lateCorePre_eq]
  have hf1 := Func.fold_wf hf
  have hs1 := Func.fold_spec hf h
  have hf2 := Func.canon_wf hf1
  have hs2 := Func.canon_spec hf1 hs1
  have hf3 := Func.divConst_wf hf2
  have hs3 := Func.divConst_spec hf2 hs2
  exact Func.copy_spec hf3 hs3

/-- `Func.lateCorePost` preserves well-formedness. -/
theorem Func.lateCorePost_wf {as rs : List Ty} {f : Func as rs} (hf : f.Wf) :
    (Func.lateCorePost f).Wf := by
  rw [Func.lateCorePost_eq]
  exact Func.fold_wf (Func.assumeBits_wf (Func.gvn_wf (Func.memLoad_wf hf)))

/-- `Func.lateCorePost` refines function contracts. -/
theorem Func.lateCorePost_spec {as rs : List Ty} {f : Func as rs} (hf : f.Wf) {Γ : Env}
    {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Func.spec Γ f xs m Q X) : Func.spec Γ (Func.lateCorePost f) xs m Q X := by
  rw [Func.lateCorePost_eq]
  have hf5 := Func.memLoad_wf hf
  have hs5 := Func.memLoad_spec hf h
  have hf6 := Func.gvn_wf hf5
  have hs6 := Func.gvn_spec hf5 hs5
  have hf7 := Func.assumeBits_wf hf6
  have hs7 := Func.assumeBits_spec hf6 hs6
  exact Func.fold_spec hf7 hs7

/-- `Func.lateCore` preserves well-formedness. -/
theorem Func.lateCore_wf {as rs : List Ty} {f : Func as rs} (_hf : f.Wf) :
    (Func.lateCore f).Wf := by
  rw [Func.lateCore_eq]
  exact Func.fold_wf (Func.assumeBits_wf (Func.gvn_wf (Func.memLoad_wf (Func.renorm_wf _))))

/-- `Func.lateCore` refines function contracts. -/
theorem Func.lateCore_spec {as rs : List Ty} {f : Func as rs} (hf : f.Wf) {Γ : Env}
    {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Func.spec Γ f xs m Q X) : Func.spec Γ (Func.lateCore f) xs m Q X := by
  have h1 := Func.lateCorePre_wf hf
  have hs1 := Func.lateCorePre_spec hf h
  have h1r := Func.renorm_wf (Func.lateCorePre f)
  have hs1r := Func.renorm_spec h1 hs1
  have h2 := Func.lateCorePost_spec h1r hs1r
  rw [Func.lateCorePre_eq, Func.lateCorePost_eq] at h2
  rw [Func.lateCore_eq]
  exact h2

/-- `Func.lateCfgPre` preserves well-formedness. -/
theorem Func.lateCfgPre_wf {as rs : List Ty} {f : Func as rs} (_hf : f.Wf) :
    (Func.lateCfgPre f).Wf := by
  rw [Func.lateCfgPre_eq]
  exact Func.gvn_wf (Func.addrRangeOpt_wf (Func.fold_wf (Func.assumeElim_wf
    (Func.deadLoadElim_wf (Func.simplifyGroupFast_wf (Func.ifOptBits f))))))

/-- `Func.lateCfgPre` refines function contracts. -/
theorem Func.lateCfgPre_spec {as rs : List Ty} {f : Func as rs} (hf : f.Wf) {Γ : Env}
    {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Func.spec Γ f xs m Q X) : Func.spec Γ (Func.lateCfgPre f) xs m Q X := by
  rw [Func.lateCfgPre_eq]
  have hf1 := Func.ifOptBits_wf hf
  have hs1 := Func.ifOptBits_spec hf h
  have hf2 := Func.simplifyGroupFast_wf (Func.ifOptBits f)
  have hs2 := Func.simplifyGroupFast_spec hf1 hs1
  have hf3 := Func.deadLoadElim_wf hf2
  have hs3 := Func.deadLoadElim_spec hf2 hs2
  have hf4 := Func.assumeElim_wf hf3
  have hs4 := Func.assumeElim_spec hf3 hs3
  have hf5 := Func.fold_wf hf4
  have hs5 := Func.fold_spec hf4 hs4
  have hf6 := Func.addrRangeOpt_wf hf5
  have hs6 := Func.addrRangeOpt_spec hf5 hs5
  exact Func.gvn_spec hf6 hs6

/-- `Func.lateCfgPost` preserves well-formedness. -/
theorem Func.lateCfgPost_wf {as rs : List Ty} {f : Func as rs} (hf : f.Wf) :
    (Func.lateCfgPost f).Wf := by
  rw [Func.lateCfgPost_eq]
  exact Func.dceP_wf (Func.licm_wf hf)

/-- `Func.lateCfgPost` refines function contracts. -/
theorem Func.lateCfgPost_spec {as rs : List Ty} {f : Func as rs} (hf : f.Wf) {Γ : Env}
    {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Func.spec Γ f xs m Q X) : Func.spec Γ (Func.lateCfgPost f) xs m Q X := by
  rw [Func.lateCfgPost_eq]
  exact Func.dceP_spec (Func.licm_wf hf) (Func.licm_spec hf h)

/-- `Func.lateLoopRotate` preserves well-formedness. -/
theorem Func.lateLoopRotate_wf {as rs : List Ty} {f : Func as rs} (hf : f.Wf) :
    (Func.lateLoopRotate f).Wf := by
  rw [Func.lateLoopRotate_eq]
  exact Func.loopRotate_wf (Func.lateCfgPost_wf hf)

/-- `Func.lateLoopRotate` refines function contracts. -/
theorem Func.lateLoopRotate_spec {as rs : List Ty} {f : Func as rs} (hf : f.Wf) {Γ : Env}
    {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Func.spec Γ f xs m Q X) : Func.spec Γ (Func.lateLoopRotate f) xs m Q X := by
  rw [Func.lateLoopRotate_eq]
  have hcfg := Func.lateCfgPost_wf hf
  have hscfg := Func.lateCfgPost_spec hf h
  exact Func.loopRotate_spec hcfg LoopRotate.defaultRotConfig hscfg

/-- `Func.lateCfg` preserves well-formedness. -/
theorem Func.lateCfg_wf {as rs : List Ty} {f : Func as rs} (_hf : f.Wf) :
    (Func.lateCfg f).Wf := by
  rw [Func.lateCfg_def]
  exact Func.lateCfgPost_wf (Func.renorm_wf _)

/-- `Func.lateCfg` refines function contracts. -/
theorem Func.lateCfg_spec {as rs : List Ty} {f : Func as rs} (hf : f.Wf) {Γ : Env}
    {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Func.spec Γ f xs m Q X) : Func.spec Γ (Func.lateCfg f) xs m Q X := by
  rw [Func.lateCfg_def]
  have h1r := Func.renorm_wf f
  have hs1r := Func.renorm_spec hf h
  have h2 := Func.lateCfgPre_wf h1r
  have hs2 := Func.lateCfgPre_spec h1r hs1r
  have h2r := Func.renorm_wf (Func.lateCfgPre (Func.renorm f))
  have hs2r := Func.renorm_spec h2 hs2
  exact Func.lateCfgPost_spec h2r hs2r

/-- `Func.lateCondThread` preserves well-formedness. -/
theorem Func.lateCondThread_wf {as rs : List Ty} {f : Func as rs} (_hf : f.Wf) :
    (Func.lateCondThread f).Wf := by
  rw [Func.lateCondThread_eq]
  exact Func.mergeRets_wf (Func.dceP_wf (Func.fold_wf (Func.condThreadLateOpt_wf f)))

/-- `Func.lateCondThread` refines function contracts. -/
theorem Func.lateCondThread_spec {as rs : List Ty} {f : Func as rs} (hf : f.Wf) {Γ : Env}
    {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Func.spec Γ f xs m Q X) : Func.spec Γ (Func.lateCondThread f) xs m Q X := by
  rw [Func.lateCondThread_eq]
  have hct_wf := Func.condThreadLateOpt_wf f
  have hct_sp := Func.condThreadLateOpt_spec hf h
  have hfd_wf := Func.fold_wf hct_wf
  have hfd_sp := Func.fold_spec hct_wf hct_sp
  have hdp_wf := Func.dceP_wf hfd_wf
  have hdp_sp := Func.dceP_spec hfd_wf hfd_sp
  exact Func.mergeRets_spec hdp_wf hdp_sp

/-- Post-`Legal` mid-end (`Func.lateOpt`) preserves well-formedness. -/
theorem Func.lateOpt_wf {as rs : List Ty} {f : Func as rs} (_hf : f.Wf) :
    (Func.lateOpt f).Wf := by
  rw [Func.lateOpt_eq]
  exact Func.renorm_wf _

/-- Post-`Legal` mid-end (`Func.lateOpt`) refines function contracts across every pass. -/
theorem Func.lateOpt_spec {as rs : List Ty} {f : Func as rs} (hf : f.Wf) {Γ : Env}
    {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Func.spec Γ f xs m Q X) : Func.spec Γ (Func.lateOpt f) xs m Q X := by
  rw [Func.lateOpt_eq]
  apply Func.renorm_spec (Func.mergeRets_wf (Func.renorm_wf _))
  apply Func.mergeRets_spec (Func.renorm_wf _)
  apply Func.renorm_spec (Func.dceP_wf (Func.fold_wf (Func.renorm_wf _)))
  apply Func.dceP_spec (Func.fold_wf (Func.renorm_wf _))
  apply Func.fold_spec (Func.renorm_wf _)
  apply Func.renorm_spec (Func.condThreadLateOpt_wf _)
  apply Func.condThreadLateOpt_spec (Func.renorm_wf _)
  apply Func.renorm_spec (Func.lateLoopRotate_wf (Func.renorm_wf _))
  apply Func.lateLoopRotate_spec (Func.renorm_wf _)
  apply Func.renorm_spec (Func.lateCfgPost_wf (Func.renorm_wf _))
  apply Func.lateCfgPost_spec (Func.renorm_wf _)
  apply Func.renorm_spec (Func.lateCfgPre_wf (Func.renorm_wf _))
  apply Func.lateCfgPre_spec (Func.renorm_wf _)
  apply Func.renorm_spec (Func.lateCorePost_wf (Func.renorm_wf _))
  apply Func.lateCorePost_spec (Func.renorm_wf _)
  apply Func.renorm_spec (Func.lateCorePre_wf hf)
  exact Func.lateCorePre_spec hf h

/-- `Fn.renorm` unconditionally produces a well-formed function body. -/
theorem Fn.renorm_wf (fn : Fn) : (Fn.renorm fn).Wf :=
  Func.renorm_wf fn.body

/-- `Fn.renorm` refines function contracts for any well-formed function. -/
theorem Fn.renorm_spec {fn : Fn} (hf : fn.Wf) {Γ : Env}
    {xs : Tup Val fn.as} {m : Mem 64} {Q : Post fn.rs} {X : XPost}
    (h : Func.spec Γ fn.body xs m Q X) : Func.spec Γ (Fn.renorm fn).body xs m Q X :=
  Func.renorm_spec hf h

private theorem denoteB_toTBlocks_callsOk {allowed : List SigEntry} {exits : List Sym}
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
      ⟨h .here, denoteB_toTBlocks_callsOk nv nl vs ls fun i => h (.there i)⟩

/-- Reification-denotation round-trip preserves `Expr.callsOk` unconditionally under `Wf`. -/
theorem denote_toTFlat_callsOk {allowed : List SigEntry} {exits : List Sym} {rs : List Ty}
    {G : Ctx K (fun _ => Unit)} {D : Ctx KL (fun _ => Unit)}
    {e₁ : Expr K KL rs} {e₂ : Expr (fun _ => Unit) (fun _ => Unit) rs}
    (hwf : Wf G D e₁ e₂) :
    ∀ (nv nl : Nat) (vs : List ((_t : Ty) × Unit)) (ls : List ((_ts : List Ty) × Unit)),
      e₂.callsOk allowed exits →
      (denote (fun _ => Unit) (fun _ => Unit) (toTFlat e₁ nv nl) vs ls).callsOk allowed exits := by
  induction hwf using Wf.induct with
  | @let_ G D ts op₁ op₂ k₁ k₂ _ _ ih =>
    intro nv nl vs ls hc
    dsimp only [toTFlat, denote]
    cases denoteArgs vs (idxArgs nv op₁.args) with
    | none => trivial
    | some _ => exact ih (Tup.levels ts nv) (Tup.units ts) (nv + ts.length) nl _ ls hc
  | load _ _ _ ih =>
    intro nv nl vs ls hc
    dsimp only [toTFlat, denote]
    cases denoteArg vs (idxArg nv _) with
    | none => trivial
    | some _ => exact ih nv () (nv + 1) nl _ ls hc
  | store _ _ _ ih =>
    intro nv nl vs ls hc
    dsimp only [toTFlat, denote]
    cases denoteArg vs _ <;> cases denoteArg vs _ <;> first | trivial | exact ih nv nl vs ls hc
  | call _ _ _ ih =>
    intro nv nl vs ls ⟨hf, hc⟩
    dsimp only [toTFlat, denote]
    cases denoteArgs vs _ with
    | none => trivial
    | some _ =>
      exact ⟨hf, ih (Tup.levels _ nv) (Tup.units _) (nv + _) nl _ ls hc⟩
  | jnz _ _ _ iht ihe =>
    intro nv nl vs ls ⟨ht, he⟩
    dsimp only [toTFlat, denote]
    cases denoteArg vs _ with
    | none => trivial
    | some _ => exact ⟨iht nv nl vs ls ht, ihe nv nl vs ls he⟩
  | jump _ _ =>
    intro nv nl vs ls _
    dsimp only [toTFlat, denote]
    cases lookupL ls _ _ <;> cases denoteArgs vs _ <;> trivial
  | ret _ =>
    intro nv nl vs ls _
    dsimp only [toTFlat, denote]
    cases denoteArgs vs _ <;> trivial
  | exit _ _ =>
    intro nv nl vs ls hf
    dsimp only [toTFlat, denote]
    cases denoteArgs vs _ <;> trivial
  | hlt => intro _ _ _ _ _; trivial
  | @group _ _ sig b₁ b₂ k₁ k₂ _ _ ihb ihk =>
    intro nv nl vs ls ⟨hb, hk⟩
    dsimp only [toTFlat, denote, Expr.callsOk]
    refine ⟨denoteB_toTBlocks_callsOk nv (nl + sig.length) vs _ fun i => ?_,
            ihk (Tup.levels sig nl) (Tup.units sig) nv (nl + sig.length) vs _ hk⟩
    exact ihb (Tup.levels sig nl) (Tup.units sig) i (Tup.levels _ nv) (Tup.units _)
      (nv + _) (nl + sig.length) _ _ (Blocks.callsOk_get hb i)

/-- `Func.renorm` preserves `callsOk` when the function body is `Wf`. -/
theorem Func.renorm_callsOk {allowed : List SigEntry} {exits : List Sym}
    {as rs : List Ty} {f : Func as rs} (hf : f.Wf)
    (hc : (f (fun _ => Unit) (fun _ => Unit) (Tup.units as)).callsOk allowed exits) :
    ((denoteFunc (reifyFunc f)) (fun _ => Unit) (fun _ => Unit) (Tup.units as)).callsOk
      allowed exits := by
  simpa [denoteFunc, reifyFunc] using
    denote_toTFlat_callsOk
      (hf K (fun _ => Unit) KL (fun _ => Unit) (Tup.levels as 0) (Tup.units as))
      as.length 0 (pushTup (Tup.units as) []) [] hc

private theorem map_eq_append_split {α : Type _} {β : Type _} (f : α → β) :
    ∀ (l : List α) (pre : List β) (a : β) (post : List β),
      l.map f = pre ++ a :: post →
      ∃ pre₀ a₀ post₀, l = pre₀ ++ a₀ :: post₀ ∧
        pre = pre₀.map f ∧ a = f a₀ ∧ post = post₀.map f
  | [], [], _, _, h => by simp at h
  | [], _ :: _, _, _, h => by simp at h
  | x :: xs, [], a, post, h => by
    simp only [List.map_cons, List.nil_append, List.cons.injEq] at h
    exact ⟨[], x, xs, rfl, rfl, h.1.symm, h.2.symm⟩
  | x :: xs, p :: ps, a, post, h => by
    simp only [List.map_cons, List.cons_append, List.cons.injEq] at h
    obtain ⟨pre₀, a₀, post₀, hl, hpre, ha, hpost⟩ := map_eq_append_split f xs ps a post h.2
    exact ⟨x :: pre₀, a₀, post₀, by simp [hl], by simp [h.1, hpre], ha, hpost⟩

/-- Module correctness theorem for `Module.optInline`: acyclic inlining followed by AST
renormalization preserves `ModuleOk Γ`. -/
theorem Module.optInline_ok {Γ : Env} {M : Module} (maxSize : Nat := 40) :
    ModuleOk Γ M → ModuleOk Γ (M.optInline maxSize) := fun hM => by
  have hInl : ModuleOk Γ (M.inline maxSize) := Module.inline_ok maxSize hM
  refine ⟨?_, fun pre fn post hsplit => ?_⟩
  · have hnames : (M.optInline maxSize).names = (M.inline maxSize).names := by
      simp [Module.optInline, Module.names, List.map_map, Function.comp_def, Fn.renorm]
    show (M.optInline maxSize).names.Nodup
    exact hnames ▸ hInl.nodup
  · dsimp only [Module.optInline] at hsplit
    obtain ⟨pre₀, fn₀, post₀, hl, hpre, rfl, _⟩ :=
      map_eq_append_split Fn.renorm (M.inline maxSize).fns pre fn post hsplit
    obtain ⟨hwf₀, hcalls₀, hspec₀⟩ := hInl.fnsOk pre₀ fn₀ post₀ hl
    have hsig : pre.map Fn.sig = pre₀.map Fn.sig := by
      rw [hpre, List.map_map]
      congr 1
    refine ⟨Fn.renorm_wf fn₀, ?_, fun xs m Q X hg => Fn.renorm_spec hwf₀ (hspec₀ xs m Q X hg)⟩
    dsimp only [Module.optInline, Module.inline] at hcalls₀ ⊢
    simpa [Fn.callsOk, Fn.renorm, hsig] using Func.renorm_callsOk hwf₀ hcalls₀

end LeanQbe.T
