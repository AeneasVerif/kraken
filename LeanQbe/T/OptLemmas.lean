module

public import LeanQbe.T.Opt
public import LeanQbe.T.Wf
public import LeanQbe.T.WP
public import LeanQbe.T.FlatLemmas
public import LeanQbe.T.GvnLemmas
public import LeanQbe.T.InlineLemmas
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
import LeanQbe.T.LoopRotateLemmas

/-!
# Correctness of the Staged Typed-IR Mid-End Pipeline (`T6`, `O-M1`, `O-M2`)

Composes relational well-formedness (`*_wf`) and WP refinement (`*_spec`) across `Func.opt`,
`Func.earlyOpt`, `Func.lateOpt`, `Fn.renorm`, and `Module.optInline`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T

/-- The legacy `T6` mid-end pipeline preserves well-formedness across every pass. -/
theorem Func.opt_wf {as rs : List Ty} {f : Func as rs} (hf : f.Wf) : (Func.opt f).Wf :=
  Func.dceP_wf (Func.fold_wf (Func.copy_wf (Func.gvn_wf (Func.copy_wf (Func.fold_wf hf)))))

/-- The legacy `T6` mid-end pipeline refines function contracts across every pass. -/
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
  dsimp only [Func.simplifyGroupFast]
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
  dsimp only [Func.simplifyGroupFast]
  by_cases hc : hasSimpGroup (tflatLoops (reifyFunc f) ≤ 1) (reifyFunc f) <;>
    simp only [hc, ↓reduceIte, Bool.false_eq_true]
  · exact Func.renorm_spec (Func.simplifyGroupPlan_wf hwf) (Func.simplifyGroupPlan_spec hwf hsp)
  · exact hsp

/-- `Func.peelFast` preserves well-formedness. -/
theorem Func.peelFast_wf {as rs : List Ty} (f : Func as rs) (budget : Nat := 24) :
    (Func.peelFast f budget).Wf := by
  dsimp only [Func.peelFast]
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
  dsimp only [Func.peelFast]
  by_cases hc : (tflatLoops (reifyFunc f) ≤ 1 && tflatSize (reifyFunc f) ≤ 40) = true <;>
    simp only [hc, ↓reduceIte, Bool.false_eq_true]
  · exact Func.renorm_spec (Func.peel_wf hwf budget) (Func.peel_spec hwf budget hsp)
  · exact hsp

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

/-- Stage 1 (`Func.earlyOpt`) preserves well-formedness. -/
theorem Func.earlyOpt_wf {as rs : List Ty} {f : Func as rs} (_hf : f.Wf) :
    (Func.earlyOpt f).Wf := by
  rw [Func.earlyOpt_eq]
  exact Func.renorm_wf _

/-- Stage 1 (`Func.earlyOpt`) refines function contracts across every pre-`Legal` pass. -/
theorem Func.earlyOpt_spec {as rs : List Ty} {f : Func as rs} (hf : f.Wf) {Γ : Env}
    {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Func.spec Γ f xs m Q X) : Func.spec Γ (Func.earlyOpt f) xs m Q X := by
  rw [Func.earlyOpt_eq]
  have hfc := Func.earlyCore_wf hf
  have hsc := Func.earlyCore_spec hf h
  let f8 := Func.simplifyGroupFast (Func.earlyCore f)
  have hf8 := Func.simplifyGroupFast_wf (Func.earlyCore f)
  have hs8 := Func.simplifyGroupFast_spec hfc hsc
  let f9 := Func.peelFast f8 24
  have hf9 := Func.peelFast_wf f8 24
  have hs9 := Func.peelFast_spec hf8 24 hs8
  have hf10 := Func.dceP_wf hf9
  have hs10 := Func.dceP_spec hf9 hs9
  exact Func.renorm_spec hf10 hs10

/-- `Func.lateCore` preserves well-formedness. -/
theorem Func.lateCore_wf {as rs : List Ty} {f : Func as rs} (_hf : f.Wf) :
    (Func.lateCore f).Wf := by
  rw [Func.lateCore_eq]
  exact Func.fold_wf (Func.gvn_wf (Func.memLoad_wf (Func.renorm_wf _)))

/-- `Func.lateCore` refines function contracts. -/
theorem Func.lateCore_spec {as rs : List Ty} {f : Func as rs} (hf : f.Wf) {Γ : Env}
    {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Func.spec Γ f xs m Q X) : Func.spec Γ (Func.lateCore f) xs m Q X := by
  rw [Func.lateCore_eq]
  have hf1 := Func.fold_wf hf
  have hs1 := Func.fold_spec hf h
  have hf2 := Func.canon_wf hf1
  have hs2 := Func.canon_spec hf1 hs1
  have hf3 := Func.divConst_wf hf2
  have hs3 := Func.divConst_spec hf2 hs2
  let f4 := Func.copy (Func.divConst (Func.canon (Func.fold f)))
  have hf4 := Func.copy_wf hf3
  have hs4 := Func.copy_spec hf3 hs3
  have hf4r := Func.renorm_wf f4
  have hs4r := Func.renorm_spec hf4 hs4
  have hf5 := Func.memLoad_wf hf4r
  have hs5 := Func.memLoad_spec hf4r hs4r
  have hf6 := Func.gvn_wf hf5
  have hs6 := Func.gvn_spec hf5 hs5
  exact Func.fold_spec hf6 hs6

/-- `Func.lateCfg` preserves well-formedness. -/
theorem Func.lateCfg_wf {as rs : List Ty} {f : Func as rs} (_hf : f.Wf) :
    (Func.lateCfg f).Wf := by
  rw [Func.lateCfg_eq]
  exact Func.dceP_wf (Func.licm_wf (Func.renorm_wf _))

/-- `Func.lateCfg` refines function contracts. -/
theorem Func.lateCfg_spec {as rs : List Ty} {f : Func as rs} (hf : f.Wf) {Γ : Env}
    {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Func.spec Γ f xs m Q X) : Func.spec Γ (Func.lateCfg f) xs m Q X := by
  rw [Func.lateCfg_eq]
  have hf0 := Func.renorm_wf f
  have hs0 := Func.renorm_spec hf h
  have hf2 := Func.ifOptBits_wf hf0
  have hs2 := Func.ifOptBits_spec hf0 hs0
  have hf3 := Func.simplifyGroupFast_wf (Func.ifOptBits (Func.renorm f))
  have hs3 := Func.simplifyGroupFast_spec hf2 hs2
  have hf4 := Func.deadLoadElim_wf hf3
  have hs4 := Func.deadLoadElim_spec hf3 hs3
  have hf5 := Func.assumeElim_wf hf4
  have hs5 := Func.assumeElim_spec hf4 hs4
  have hf5r := Func.renorm_wf
    (Func.assumeElim (Func.deadLoadElim (Func.simplifyGroupFast (Func.ifOptBits (Func.renorm f)))))
  have hs5r := Func.renorm_spec hf5 hs5
  have hf6 := Func.licm_wf hf5r
  have hs6 := Func.licm_spec hf5r hs5r
  exact Func.dceP_spec hf6 hs6

/-- Stage 2 (`Func.lateOpt`) preserves well-formedness. -/
theorem Func.lateOpt_wf {as rs : List Ty} {f : Func as rs} (_hf : f.Wf) :
    (Func.lateOpt f).Wf := by
  rw [Func.lateOpt_eq]
  exact Func.renorm_wf _

/-- Stage 2 (`Func.lateOpt`) refines function contracts across every post-`Legal` pass. -/
theorem Func.lateOpt_spec {as rs : List Ty} {f : Func as rs} (hf : f.Wf) {Γ : Env}
    {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Func.spec Γ f xs m Q X) : Func.spec Γ (Func.lateOpt f) xs m Q X := by
  rw [Func.lateOpt_eq]
  have hcore := Func.lateCore_wf hf
  have hscore := Func.lateCore_spec hf h
  have hcfg := Func.lateCfg_wf hcore
  have hscfg := Func.lateCfg_spec hcore hscore
  exact Func.renorm_spec (Func.loopRotate_wf hcfg)
    (Func.loopRotate_spec hcfg LoopRotate.defaultRotConfig hscfg)

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
    ((Func.renorm f) (fun _ => Unit) (fun _ => Unit) (Tup.units as)).callsOk allowed exits := by
  simpa [Func.renorm, denoteFunc, reifyFunc] using
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
