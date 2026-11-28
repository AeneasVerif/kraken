/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.InlinePlanSeg
public import LeanQbe.T.MainInline
import LeanQbe.T.InlineLemmas
import LeanQbe.T.OptLemmas

/-!
# Correctness & End-to-End Compilation Soundness of `Module.inlinePlan` (`InlinePlanLemmas`)

Additive leaf mirroring `InlineLemmas.lean` and `MainInline.lean` for untrusted per-caller
`InlPlan` inlining (`Module.inlinePlan`), reusing existing `Fn.inline_wf`, `Fn.inline_spec`,
`inline_callsOk`, and `Fn.renorm_*` with zero new axioms (`<= std3`):

* `selectPlanCands_mem`, `inlineFnsPlan_preserve`.
* `Module.inlinePlan_{sigs, names, namesNodup, externs, exits, fns_length}` and
  `Env.ofModule_inlinePlan`.
* `Module.inlinePlan_ok`, `Module.inlinePlan_checkAcyclic`, `Module.inlinePlan_acyclic`,
  `Module.inlinePlan_wf`, `Module.inlinePlan_callsOk`, `Module.inlinePlan_spec`,
  `Module.inlinePlan_supportsSource`.
* `compileModuleInlinePlan`, `compile_sound_inlinePlan`, and `Compiled.fnSpec_*_inlinePlan`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T

/-! ## 1. Compilation wrapper and signature / name / length preservation -/

/-- Stack-checked module compilation after verified `Module.inlinePlan plan`. -/
@[expose] def compileModuleInlinePlan (I : Isa) (lt : LegalTarget) (raBytes : Nat)
    (extCallees : List (SigEntry × Nat)) (exits : List Sym) (nX : Nat)
    (M : Module) (hints : List I.Hints) (plan : InlPlan) :
    Except String (List I.Directive × List (Sym × Nat)) :=
  compileModule I lt raBytes extCallees exits nX (M.inlinePlan plan).fns hints

theorem selectPlanCands_mem (plan : InlPlan) (cands : List Fn) (caller : Sym) :
    ∀ g ∈ selectPlanCands plan cands caller, g ∈ cands := by
  intro g hg
  dsimp only [selectPlanCands] at hg
  obtain ⟨nm, _, hlook⟩ := List.mem_filterMap.mp hg
  exact (lookupFnByName_mem hlook).1

theorem inlineFnsPlan_map_sig (plan : InlPlan) :
    ∀ (cands fns : List Fn), (inlineFnsPlan plan cands fns).map Fn.sig = fns.map Fn.sig
  | _, [] => rfl
  | cands, fn :: rest => by
      dsimp only [inlineFnsPlan, Fn.renorm, Fn.inline, Fn.sig]
      simp only [List.map_cons]
      exact congrArg (_ :: ·) (inlineFnsPlan_map_sig plan _ rest)

theorem inlineFnsPlan_length (plan : InlPlan) (cands fns : List Fn) :
    (inlineFnsPlan plan cands fns).length = fns.length := by
  have h := congrArg List.length (inlineFnsPlan_map_name plan cands fns)
  simpa only [List.length_map] using h

theorem Module.inlinePlan_sigs (M : Module) (plan : InlPlan) :
    (M.inlinePlan plan).sigs = M.sigs := by
  simp only [Module.sigs, Module.inlinePlan, inlineFnsPlan_map_sig]

theorem Module.inlinePlan_names (M : Module) (plan : InlPlan) :
    (M.inlinePlan plan).names = M.names := by
  simp only [Module.names, Module.inlinePlan, inlineFnsPlan_map_name]

theorem Module.inlinePlan_namesNodup (M : Module) (plan : InlPlan) :
    (M.inlinePlan plan).namesNodup ↔ M.namesNodup := by
  simp only [Module.namesNodup, Module.inlinePlan_names]

theorem Module.inlinePlan_externs (M : Module) (plan : InlPlan) :
    (M.inlinePlan plan).externs = M.externs := rfl

theorem Module.inlinePlan_exits (M : Module) (plan : InlPlan) :
    (M.inlinePlan plan).exits = M.exits := rfl

theorem Module.inlinePlan_fns_length (M : Module) (plan : InlPlan) :
    (M.inlinePlan plan).fns.length = M.fns.length :=
  inlineFnsPlan_length plan [] M.fns

theorem Env.ofModule_inlinePlan (M : Module) (Γ : Env) (plan : InlPlan) :
    Env.ofModule (M.inlinePlan plan) Γ = Env.ofModule M Γ := by
  simp [Env.ofModule, Module.inlinePlan_sigs]

/-! ## 2. Inductive preservation and `ModuleOk` soundness -/

theorem inlineFnsPlan_preserve (P : Fn → Prop) (plan : InlPlan)
    (hStep : ∀ (cands : List Fn) (fn : Fn),
      (∀ c ∈ cands, P c) → P fn → P (fn.inline cands).renorm) :
    ∀ (cands rest : List Fn),
      (∀ c ∈ cands, P c) → (∀ f ∈ rest, P f) →
      ∀ f ∈ inlineFnsPlan plan cands rest, P f
  | _, [], _, _, _, hf => by dsimp only [inlineFnsPlan] at hf; cases hf
  | cands, fn :: rest, hcands, hrest, f, hf => by
      dsimp only [inlineFnsPlan] at hf
      let cs := selectPlanCands plan cands fn.name
      have hfn' : P (fn.inline cs).renorm :=
        hStep cs fn (fun c hc => hcands c (selectPlanCands_mem plan cands fn.name c hc))
          (hrest fn List.mem_cons_self)
      rcases List.mem_cons.mp hf with rfl | htl
      · exact hfn'
      · have hcands' : ∀ c ∈ (fn.inline cs).renorm :: cands, P c := fun c hc => by
          rcases List.mem_cons.mp hc with rfl | hc'
          · exact hfn'
          · exact hcands c hc'
        exact inlineFnsPlan_preserve P plan hStep _ rest hcands'
          (fun g hg => hrest g (List.mem_cons_of_mem _ hg)) f htl

private theorem inlineFnsPlan_ok {Γ : Env} (plan : InlPlan)
    (extSigs : List SigEntry) (exits : List Sym) :
    ∀ (seenSigs : List SigEntry) (cands rest : List Fn),
      CandsWpOk Γ cands →
      CandsCallsOk (seenSigs ++ extSigs) exits cands →
      (∀ pre fn post, rest = pre ++ fn :: post →
        fn.Wf ∧ fn.callsOk ((seenSigs ++ pre.map Fn.sig) ++ extSigs) exits ∧
        ∀ xs m Q X, Γ fn.name fn.as fn.rs xs m Q X → Func.wp Γ fn.body xs m Q X) →
      ∀ pre' fn' post',
        inlineFnsPlan plan cands rest = pre' ++ fn' :: post' →
        fn'.Wf ∧ fn'.callsOk ((seenSigs ++ pre'.map Fn.sig) ++ extSigs) exits ∧
        ∀ xs m Q X, Γ fn'.name fn'.as fn'.rs xs m Q X → Func.wp Γ fn'.body xs m Q X
  | _, _, [], _, _, _, pre', _, _, hsplit => by
      cases pre' <;> (dsimp only [inlineFnsPlan] at hsplit; simp at hsplit)
  | seenSigs, cands, fn :: rest, hwp, hcalls, hrest, pre', fn', post', hsplit => by
      have ⟨hfn_wf, hfn_calls, hfn_spec⟩ := hrest [] fn rest rfl
      simp only [List.map_nil, List.append_nil] at hfn_calls
      let cs := selectPlanCands plan cands fn.name
      have hsubFn : ∀ g ∈ cs, g ∈ cands := selectPlanCands_mem plan cands fn.name
      have hwpFn : CandsWpOk Γ cs := fun g hg => hwp g (hsubFn g hg)
      have hcallsFn : CandsCallsOk (seenSigs ++ extSigs) exits cs :=
        fun g hg => hcalls g (hsubFn g hg)
      let fn0 := fn.inline cs
      have hfn0_wf : fn0.Wf := Func.inline_wf hwpFn.wfOk hfn_wf
      have hfn0_calls : fn0.callsOk (seenSigs ++ extSigs) exits :=
        inline_callsOk hcallsFn _ hfn_calls
      have hfn0_spec : ∀ xs m Q X, Γ fn0.name fn0.as fn0.rs xs m Q X →
          Func.wp Γ fn0.body xs m Q X :=
        fun xs m Q X hg => Func.inline_spec hwpFn fn.body (hfn_spec xs m Q X hg)
      let fnR := fn0.renorm
      have hfnR_wf : fnR.Wf := Fn.renorm_wf fn0
      have hfnR_calls : fnR.callsOk (seenSigs ++ extSigs) exits :=
        Func.renorm_callsOk hfn0_wf hfn0_calls
      have hfnR_spec : ∀ xs m Q X, Γ fnR.name fnR.as fnR.rs xs m Q X →
          Func.wp Γ fnR.body xs m Q X :=
        fun xs m Q X hg => Fn.renorm_spec hfn0_wf (hfn0_spec xs m Q X hg)
      have hwp' : CandsWpOk Γ (fnR :: cands) := by
        intro g hg
        rcases List.mem_cons.mp hg with rfl | hg
        · exact ⟨hfnR_wf, hfnR_spec⟩
        · exact hwp g hg
      have hsub : ∀ s ∈ seenSigs ++ extSigs, s ∈ (seenSigs ++ [fn.sig]) ++ extSigs := by
        intro s hs
        rcases List.mem_append.mp hs with hs | hs
        · exact List.mem_append_left _ (List.mem_append_left _ hs)
        · exact List.mem_append_right _ hs
      have hcalls' : CandsCallsOk ((seenSigs ++ [fn.sig]) ++ extSigs) exits (fnR :: cands) := by
        intro g hg
        rcases List.mem_cons.mp hg with rfl | hg
        · exact ⟨hfnR_wf, Fn.callsOk_mono hsub hfnR_calls⟩
        · exact ⟨(hcalls g hg).1, Fn.callsOk_mono hsub (hcalls g hg).2⟩
      have hrest' : ∀ pre fn2 post, rest = pre ++ fn2 :: post →
          fn2.Wf ∧
          fn2.callsOk (((seenSigs ++ [fn.sig]) ++ pre.map Fn.sig) ++ extSigs) exits ∧
          ∀ xs m Q X, Γ fn2.name fn2.as fn2.rs xs m Q X → Func.wp Γ fn2.body xs m Q X := by
        intro pre fn2 post hsp
        have h := hrest (fn :: pre) fn2 post (by simp [hsp])
        simpa [List.append_assoc] using h
      cases pre' with
      | nil =>
          dsimp only [inlineFnsPlan] at hsplit
          simp only [List.nil_append, List.cons.injEq] at hsplit
          rcases hsplit with ⟨rfl, _⟩
          simpa [List.append_nil] using And.intro hfnR_wf (And.intro hfnR_calls hfnR_spec)
      | cons hd tl =>
          dsimp only [inlineFnsPlan] at hsplit
          simp only [List.cons_append, List.cons.injEq] at hsplit
          rcases hsplit with ⟨rfl, htl⟩
          have hsig : (fn.inline (selectPlanCands plan cands fn.name)).renorm.sig = fn.sig := rfl
          have ih := inlineFnsPlan_ok plan extSigs exits
            (seenSigs ++ [fn.sig]) (fnR :: cands) rest hwp' hcalls' hrest' tl fn' post' htl
          simpa [hsig, List.append_assoc] using ih

/-- Main module correctness theorem: plan-driven inlining preserves `ModuleOk Γ` for ANY plan. -/
theorem Module.inlinePlan_ok {Γ : Env} {M : Module} (plan : InlPlan) :
    ModuleOk Γ M → ModuleOk Γ (M.inlinePlan plan) := fun hM => by
  refine ⟨(Module.inlinePlan_namesNodup M plan).mpr hM.nodup, fun pre fn post hsplit => ?_⟩
  exact inlineFnsPlan_ok plan (M.externs.map Extern.sig) M.exits [] [] M.fns
    (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun pre0 fn0 post0 hsp0 => by simpa using hM.fnsOk pre0 fn0 post0 hsp0)
    pre fn post hsplit

private theorem checkAcyclic_of_moduleOk {Γ : Env} {M : Module} (hM : ModuleOk Γ M) :
    M.checkAcyclic = true := by
  simp only [Module.checkAcyclic, Bool.and_eq_true]
  exact ⟨listNodup_iff.mpr hM.nodup,
    checkFnsCallsOk_of_forall _ _ [] _ fun p fn q hsp => by simpa using (hM.fnsOk p fn q hsp).2.1⟩

private theorem inlinePlan_moduleOk_bot {M : Module} (plan : InlPlan)
    (hchk : M.checkAcyclic = true) (hwf : ∀ f ∈ M.fns, f.Wf) :
    ModuleOk (fun _ _ _ _ _ _ _ => False) (M.inlinePlan plan) :=
  Module.inlinePlan_ok plan
    (Module.moduleOk_of_checkAcyclic (Γ := fun _ _ _ _ _ _ _ => False) hchk hwf
      (fun _ _ _ _ _ _ => False.elim))

/-- `Module.inlinePlan` preserves `Module.checkAcyclic` when all source functions are `Wf`. -/
theorem Module.inlinePlan_checkAcyclic {M : Module} (plan : InlPlan)
    (hchk : M.checkAcyclic = true) (hwf : ∀ f ∈ M.fns, f.Wf) :
    (M.inlinePlan plan).checkAcyclic = true :=
  checkAcyclic_of_moduleOk (inlinePlan_moduleOk_bot plan hchk hwf)

/-- Alias for `Module.inlinePlan_checkAcyclic`. -/
theorem Module.inlinePlan_acyclic {M : Module} (plan : InlPlan)
    (hchk : M.checkAcyclic = true) (hwf : ∀ f ∈ M.fns, f.Wf) :
    (M.inlinePlan plan).checkAcyclic = true :=
  Module.inlinePlan_checkAcyclic plan hchk hwf

/-- `Module.inlinePlan` preserves `Fn.Wf` for every function in an acyclic module. -/
theorem Module.inlinePlan_wf {M : Module} (plan : InlPlan)
    (hchk : M.checkAcyclic = true) (hwf : ∀ f ∈ M.fns, f.Wf) :
    ∀ f ∈ (M.inlinePlan plan).fns, f.Wf := fun f hf =>
  let ⟨pre, post, hsp⟩ := List.mem_iff_append.mp hf
  ((inlinePlan_moduleOk_bot plan hchk hwf).fnsOk pre f post hsp).1

/-- `Module.inlinePlan` preserves `Fn.callsOk` along the acyclic module function list. -/
theorem Module.inlinePlan_callsOk {M : Module} (plan : InlPlan)
    (hchk : M.checkAcyclic = true) (hwf : ∀ f ∈ M.fns, f.Wf) :
    ∀ pre fn post, (M.inlinePlan plan).fns = pre ++ fn :: post →
      fn.callsOk (pre.map Fn.sig ++ M.externs.map Extern.sig) M.exits := fun pre fn post hsp =>
  ((inlinePlan_moduleOk_bot plan hchk hwf).fnsOk pre fn post hsp).2.1

/-- `Module.inlinePlan` preserves `Func.wp` contracts for every function in `M`. -/
theorem Module.inlinePlan_spec {Γ : Env} {M : Module} (plan : InlPlan)
    (hM : ModuleOk Γ M) :
    ∀ f ∈ (M.inlinePlan plan).fns, ∀ xs m Q X,
      Γ f.name f.as f.rs xs m Q X → Func.wp Γ f.body xs m Q X := fun f hf =>
  let ⟨pre, post, hsp⟩ := List.mem_iff_append.mp hf
  ((Module.inlinePlan_ok plan hM).fnsOk pre f post hsp).2.2

/-! ## 3. `supportsSource` preservation for `Module.inlinePlan` -/

private theorem bool_and_keep_left {a b d : Bool} (h : (a && b) = true)
    (hd : b = true → d = true) : (a && d) = true := by
  rw [Bool.and_eq_true] at h ⊢; exact ⟨h.1, hd h.2⟩

private theorem bool_and_both {a b c d : Bool} (h : (a && b) = true)
    (hc : a = true → c = true) (hd : b = true → d = true) : (c && d) = true := by
  rw [Bool.and_eq_true] at h ⊢; exact ⟨hc h.1, hd h.2⟩

private theorem tblocks_supportsSource_get (target : LegalTarget) {rs : List Ty} :
    ∀ {sig : List (List Ty)} (bs : Blocks K KL rs sig) {nv nl : Nat},
      (toTBlocks bs nv nl).supportsSource target = true →
      ∀ {ts} (i : Member ts sig),
        ts.all target.supportsTy = true ∧
        (toTFlat (bs.get i (Tup.levels ts nv)) (nv + ts.length) nl).supportsSource
          target = true
  | _, .cons _ _, _, _, hs, _, .here => by
      dsimp only [toTBlocks, TBlocks.supportsSource] at hs
      rw [Bool.and_eq_true, Bool.and_eq_true] at hs; exact hs.1
  | _, .cons _ bs, _, _, hs, _, .there i => by
      dsimp only [toTBlocks, TBlocks.supportsSource] at hs
      rw [Bool.and_eq_true] at hs; exact tblocks_supportsSource_get target bs hs.2 i

private theorem tblocks_supportsSource_of_get (target : LegalTarget) {rs : List Ty} :
    ∀ {sig : List (List Ty)} (bs : Blocks K KL rs sig) (nv nl : Nat),
      (∀ {ts} (i : Member ts sig),
        ts.all target.supportsTy = true ∧
        (toTFlat (bs.get i (Tup.levels ts nv)) (nv + ts.length) nl).supportsSource
          target = true) →
      (toTBlocks bs nv nl).supportsSource target = true
  | _, .nil, _, _, _ => rfl
  | _, .cons _ bs, nv, nl, h => by
      dsimp only [toTBlocks, TBlocks.supportsSource]
      rw [Bool.and_eq_true, Bool.and_eq_true]
      exact ⟨h .here, tblocks_supportsSource_of_get target bs nv nl fun i => h (.there i)⟩

private theorem spliceRet_supportsSource (target : LegalTarget) {calleeRs callerRs : List Ty}
    {j₁ : KL calleeRs} {G : Ctx (Arg K) K} {D : Ctx KL KL}
    {e₁ : Expr (Arg K) KL calleeRs} {e₂ : Expr K KL calleeRs} (hwf : Wf G D e₁ e₂) :
    ∀ nv₁ nl₁ nv₂ nl₂, (toTFlat e₂ nv₂ nl₂).supportsSource target = true →
      (toTFlat (spliceRet (callerRs := callerRs) j₁ e₁) nv₁ nl₁).supportsSource
        target = true := by
  induction hwf using Wf.induct with
  | let_ hop _ ih =>
      intro _ _ _ _ hs; cases hop
      dsimp only [spliceRet, flattenOp, toTFlat, TFlat.supportsSource] at hs ⊢
      exact bool_and_keep_left hs (ih _ _ _ _ _ _)
  | load _ _ _ ih =>
      intro _ _ _ _ hs
      dsimp only [spliceRet, toTFlat, TFlat.supportsSource] at hs ⊢
      exact bool_and_keep_left hs (ih _ _ _ _ _ _)
  | store _ _ _ ih =>
      intro _ _ _ _ hs
      dsimp only [spliceRet, toTFlat, TFlat.supportsSource] at hs ⊢
      exact bool_and_keep_left hs (ih _ _ _ _)
  | call _ _ _ ih =>
      intro _ _ _ _ hs
      dsimp only [spliceRet, toTFlat, TFlat.supportsSource] at hs ⊢
      exact bool_and_keep_left hs (ih _ _ _ _ _ _)
  | jnz _ _ _ iht ihe =>
      intro _ _ _ _ hs
      dsimp only [spliceRet, toTFlat, TFlat.supportsSource] at hs ⊢
      exact bool_and_both hs (iht _ _ _ _) (ihe _ _ _ _)
  | jump _ _ | ret _ | exit _ _ => intro _ _ _ _ hs; exact hs
  | hlt => intro _ _ _ _ _; rfl
  | @group _ _ sig _ b₂ _ _ _ _ ihb ihk =>
      intro nv₁ nl₁ nv₂ nl₂ hs
      dsimp only [spliceRet, toTFlat, TFlat.supportsSource] at hs ⊢
      rw [Bool.and_eq_true, Bool.and_eq_true] at hs ⊢
      refine ⟨⟨hs.1.1, tblocks_supportsSource_of_get target _ nv₁ (nl₁ + sig.length) fun i => ?_⟩,
        ihk (Tup.levels sig nl₁) (Tup.levels sig nl₂) nv₁ (nl₁ + sig.length) nv₂
          (nl₂ + sig.length) hs.2⟩
      have hg := tblocks_supportsSource_get target (b₂ (Tup.levels sig nl₂)) hs.1.2 i
      rw [spliceRetB_get]
      exact ⟨hg.1, ihb (Tup.levels sig nl₁) (Tup.levels sig nl₂) i (toArgTup _) (Tup.levels _ nv₂)
        (nv₁ + _) (nl₁ + sig.length) (nv₂ + _) (nl₂ + sig.length) hg.2⟩

private theorem inlineExpr_supportsSource (target : LegalTarget) {cands : List Fn}
    (hcands : ∀ fn ∈ cands, fn.Wf ∧ fn.body.supportsSource target = true) {rs : List Ty}
    {G : Ctx K K} {D : Ctx KL KL} {e₁ e₂ : Expr K KL rs} (hwf : Wf G D e₁ e₂) :
    ∀ nv₁ nl₁ nv₂ nl₂, (toTFlat e₂ nv₂ nl₂).supportsSource target = true →
      (toTFlat (inlineExpr cands e₁) nv₁ nl₁).supportsSource target = true := by
  induction hwf using Wf.induct with
  | let_ hop _ ih =>
      intro _ _ _ _ hs; cases hop
      dsimp only [inlineExpr, toTFlat, TFlat.supportsSource] at hs ⊢
      exact bool_and_keep_left hs (ih _ _ _ _ _ _)
  | load _ _ _ ih =>
      intro _ _ _ _ hs
      dsimp only [inlineExpr, toTFlat, TFlat.supportsSource] at hs ⊢
      exact bool_and_keep_left hs (ih _ _ _ _ _ _)
  | store _ _ _ ih =>
      intro _ _ _ _ hs
      dsimp only [inlineExpr, toTFlat, TFlat.supportsSource] at hs ⊢
      exact bool_and_keep_left hs (ih _ _ _ _)
  | @call _ _ f as bs args₁ _ _ _ _ _ ih =>
      intro nv₁ nl₁ nv₂ nl₂ hs
      dsimp only [toTFlat, TFlat.supportsSource] at hs
      rw [Bool.and_eq_true, Bool.and_eq_true] at hs
      rw [inlineExpr_call]
      cases hlook : lookupCallee cands f as bs with
      | none =>
          dsimp only [toTFlat, TFlat.supportsSource]
          rw [Bool.and_eq_true, Bool.and_eq_true]; exact ⟨hs.1, ih _ _ _ _ _ _ hs.2⟩
      | some _ =>
          obtain ⟨fn, hfn, _, ha, hr, rfl⟩ := lookupCallee_mem hlook
          subst ha; subst hr
          obtain ⟨hwf_fn, hsupp_fn⟩ := hcands fn hfn
          dsimp only [Func.supportsSource] at hsupp_fn; rw [Bool.and_eq_true] at hsupp_fn
          dsimp only [toTFlat, toTBlocks, TFlat.supportsSource, TBlocks.supportsSource, List.all]
          simp only [Bool.and_true, Bool.and_eq_true]
          exact ⟨⟨hs.1.2, ⟨hs.1.2, ih (Tup.levels fn.rs nv₁) (Tup.levels fn.rs nv₂)
            (nv₁ + fn.rs.length) (nl₁ + 1) (nv₂ + fn.rs.length) nl₂ hs.2⟩⟩,
            spliceRet_supportsSource target
              (hwf_fn (Arg K) K KL KL args₁ (Tup.levels fn.as 0))
              nv₁ (nl₁ + 1) fn.as.length 0 hsupp_fn.2⟩
  | jnz _ _ _ iht ihe =>
      intro _ _ _ _ hs
      dsimp only [inlineExpr, toTFlat, TFlat.supportsSource] at hs ⊢
      exact bool_and_both hs (iht _ _ _ _) (ihe _ _ _ _)
  | jump _ _ | ret _ | exit _ _ => intro _ _ _ _ hs; exact hs
  | hlt => intro _ _ _ _ _; rfl
  | @group _ _ sig _ b₂ _ _ _ _ ihb ihk =>
      intro nv₁ nl₁ nv₂ nl₂ hs
      dsimp only [inlineExpr, toTFlat, TFlat.supportsSource] at hs ⊢
      rw [Bool.and_eq_true, Bool.and_eq_true] at hs ⊢
      refine ⟨⟨hs.1.1, tblocks_supportsSource_of_get target _ nv₁ (nl₁ + sig.length) fun i => ?_⟩,
        ihk (Tup.levels sig nl₁) (Tup.levels sig nl₂) nv₁ (nl₁ + sig.length) nv₂
          (nl₂ + sig.length) hs.2⟩
      have hg := tblocks_supportsSource_get target (b₂ (Tup.levels sig nl₂)) hs.1.2 i
      rw [inlineBlocks_get]
      exact ⟨hg.1, ihb (Tup.levels sig nl₁) (Tup.levels sig nl₂) i (Tup.levels _ nv₁)
        (Tup.levels _ nv₂) (nv₁ + _) (nl₁ + sig.length) (nv₂ + _) (nl₂ + sig.length) hg.2⟩

private theorem toTFlat_denote_supportsSource (target : LegalTarget) :
    {rs : List Ty} → (tf : TFlat rs) → tf.supportsSource target = true →
    ∀ (vs : List ((t : Ty) × K t)) (ls : List ((ts : List Ty) × KL ts)) (nv nl : Nat),
      (toTFlat (denote K KL tf vs ls) nv nl).supportsSource target = true
  | _, .let_ op k, hs, vs, ls, _, nl => by
      dsimp only [TFlat.supportsSource, denote] at hs ⊢
      cases denoteArgs vs op.args <;> first
        | rfl
        | exact bool_and_keep_left hs fun h => toTFlat_denote_supportsSource target k h _ ls _ nl
  | _, .load _ a k, hs, vs, ls, _, nl => by
      dsimp only [TFlat.supportsSource, denote] at hs ⊢
      cases denoteArg vs a <;> first
        | rfl
        | exact bool_and_keep_left hs fun h => toTFlat_denote_supportsSource target k h _ ls _ nl
  | _, .store v a k, hs, vs, ls, nv, nl => by
      dsimp only [TFlat.supportsSource, denote] at hs ⊢
      cases denoteArg vs v
      · rfl
      · cases denoteArg vs a <;> first
          | rfl
          | exact bool_and_keep_left hs fun h =>
              toTFlat_denote_supportsSource target k h vs ls nv nl
  | _, .call _ _ args k, hs, vs, ls, _, nl => by
      dsimp only [TFlat.supportsSource, denote] at hs ⊢
      cases denoteArgs vs args <;> first
        | rfl
        | exact bool_and_keep_left hs fun h => toTFlat_denote_supportsSource target k h _ ls _ nl
  | _, .jnz c t e, hs, vs, ls, nv, nl => by
      dsimp only [TFlat.supportsSource, denote] at hs ⊢
      cases denoteArg vs c <;> first
        | rfl
        | exact bool_and_both hs
            (fun h => toTFlat_denote_supportsSource target t h vs ls nv nl)
            (fun h => toTFlat_denote_supportsSource target e h vs ls nv nl)
  | _, .jump j args, hs, vs, ls, _, _ => by
      dsimp only [denote]
      cases lookupL ls _ j
      · rfl
      · cases denoteArgs vs args <;> first | rfl | exact hs
  | _, .ret vs', hs, vs, _, _, _ => by
      dsimp only [denote]; cases denoteArgs vs vs' <;> first | rfl | exact hs
  | _, .exit _ args, hs, vs, _, _, _ => by
      dsimp only [denote]; cases denoteArgs vs args <;> first | rfl | exact hs
  | _, .hlt, _, _, _, _, _ => rfl
  | _, .group (sig := sig) bodies k, hs, vs, ls, nv, nl => by
      dsimp only [TFlat.supportsSource, denote, toTFlat] at hs ⊢
      rw [Bool.and_eq_true, Bool.and_eq_true] at hs ⊢
      exact ⟨⟨hs.1.1, tblocks_supportsSource_of_get target _ nv (nl + sig.length) fun i =>
        toTBlocks_denote_supportsSource target bodies hs.1.2 vs _ nv (nl + sig.length) i⟩,
        toTFlat_denote_supportsSource target k hs.2 vs _ nv (nl + sig.length)⟩
where
  toTBlocks_denote_supportsSource (target : LegalTarget) {rs : List Ty} :
      {sig : List (List Ty)} → (bs : TBlocks rs sig) → bs.supportsSource target = true →
      ∀ (vs : List ((t : Ty) × K t)) (ls : List ((ts : List Ty) × KL ts)) (nv nl : Nat)
        {ts} (i : Member ts sig),
        ts.all target.supportsTy = true ∧
        (toTFlat ((denoteB K KL bs vs ls).get i (Tup.levels ts nv)) (nv + ts.length)
          nl).supportsSource target = true
    | _, .cons b bs, hs, vs, ls, nv, nl, _, .here => by
        dsimp only [TBlocks.supportsSource] at hs; rw [Bool.and_eq_true, Bool.and_eq_true] at hs
        exact ⟨hs.1.1, toTFlat_denote_supportsSource target b hs.1.2 _ ls _ nl⟩
    | _, .cons _ bs, hs, vs, ls, nv, nl, _, .there i => by
        dsimp only [TBlocks.supportsSource] at hs; rw [Bool.and_eq_true] at hs
        exact toTBlocks_denote_supportsSource target bs hs.2 vs ls nv nl i

private theorem Func.renorm_supportsSource (target : LegalTarget) {as rs : List Ty}
    (f : Func as rs) (hsupp : f.supportsSource target = true) :
    (Func.renorm f).supportsSource target = true := by
  dsimp only [Func.supportsSource] at hsupp ⊢
  rw [Bool.and_eq_true] at hsupp ⊢
  exact ⟨hsupp.1, toTFlat_denote_supportsSource target (reifyFunc f) hsupp.2 _ _ _ _⟩

/-- `Module.inlinePlan` preserves `Func.supportsSource lt` for every function in `M`. -/
theorem Module.inlinePlan_supportsSource (lt : LegalTarget) {M : Module}
    (plan : InlPlan) (hwf : ∀ f ∈ M.fns, f.Wf)
    (hsupp : ∀ f ∈ M.fns, f.body.supportsSource lt = true) :
    ∀ f ∈ (M.inlinePlan plan).fns, f.body.supportsSource lt = true := by
  have hP := inlineFnsPlan_preserve
    (fun fn => fn.Wf ∧ fn.body.supportsSource lt = true) plan
    (fun cands fn hc hfn => by
      refine ⟨Fn.renorm_wf _, Func.renorm_supportsSource lt _ ?_⟩
      dsimp only [Fn.inline, Func.supportsSource] at hfn ⊢
      rw [Bool.and_eq_true] at hfn ⊢
      exact ⟨hfn.2.1, inlineExpr_supportsSource lt hc
        (hfn.1 K K KL KL (Tup.levels fn.as 0) (Tup.levels fn.as 0))
        fn.as.length 0 fn.as.length 0 hfn.2.2⟩)
    [] M.fns (fun _ h => nomatch h) (fun f hf => ⟨hwf f hf, hsupp f hf⟩)
  intro f hf
  exact (hP f hf).2

/-! ## 4. End-to-end compilation soundness & `Compiled.fnSpec_*_inlinePlan` -/

private theorem inlinePlan_compile_hyps {M : Module} {Γ : Env} (plan : InlPlan)
    (hacyc : M.checkAcyclic = true) (hwf : ∀ f ∈ M.fns, f.Wf)
    (hwp : ∀ f ∈ M.fns, ∀ xs m Q X, Γ f.name f.as f.rs xs m Q X → Func.wp Γ f.body xs m Q X) :
    (M.inlinePlan plan).checkAcyclic = true ∧
    (∀ f ∈ (M.inlinePlan plan).fns, f.Wf) ∧
    (∀ f ∈ (M.inlinePlan plan).fns, ∀ xs m Q X,
      Γ f.name f.as f.rs xs m Q X → Func.wp Γ f.body xs m Q X) ∧
    (M.inlinePlan plan).fns.map Fn.name = M.fns.map Fn.name ∧
    (M.inlinePlan plan).fns.map Fn.sig = M.fns.map Fn.sig := by
  have hm' := Module.inlinePlan_ok plan (Module.moduleOk_of_checkAcyclic hacyc hwf hwp)
  refine ⟨checkAcyclic_of_moduleOk hm', fun f hf => ?_, fun f hf => ?_, ?_, ?_⟩
  · obtain ⟨pre, post, hsp⟩ := List.mem_iff_append.mp hf
    exact (hm'.fnsOk pre f post hsp).1
  · obtain ⟨pre, post, hsp⟩ := List.mem_iff_append.mp hf
    exact (hm'.fnsOk pre f post hsp).2.2
  · exact inlineFnsPlan_map_name plan [] M.fns
  · exact inlineFnsPlan_map_sig plan [] M.fns

private theorem fn_sig_mem_of_map_eq {l₁ l₂ : List Fn} (hsigs : l₁.map Fn.sig = l₂.map Fn.sig)
    {f₁ : Fn} (hf₁ : f₁ ∈ l₁) :
    ∃ f₂ ∈ l₂, f₂.name = f₁.name ∧ f₂.as = f₁.as ∧ f₂.rs = f₁.rs := by
  obtain ⟨f₂, hf₂, h⟩ := List.mem_map.mp (hsigs ▸ List.mem_map_of_mem hf₁)
  simp only [Fn.sig, Prod.mk.injEq] at h
  exact ⟨f₂, hf₂, h.1, h.2.1, h.2.2⟩

/-- End-to-end compilation soundness after verified `Module.inlinePlan plan`, exposing source
module hypotheses `M` and source-level specifications under `Env.ofModule M Γ`. -/
theorem compile_sound_inlinePlan (T : Target) (host : T.mach.Host) (lt : LegalTarget)
    (M : Module) (Γ : Env) (extCallees : List (SigEntry × Nat)) (exits : List Sym)
    (nX : Nat) (plan : InlPlan) (hints : List T.toIsa.Hints) (code : List T.Directive)
    (bounds : List (Sym × Nat)) (k₀ : Nat)
    (hcm : compileModuleInlinePlan T.toIsa lt T.frame.raBytes extCallees exits nX M hints
        plan = .ok (code, bounds))
    (hc : code.IsInfixAt (T.mach.prog host) k₀) (hu : T.LabelsUnique host) :
    InlModHyps lt M (M.inlinePlan plan) Γ
      (InlExtHyps T host lt M Γ extCallees exits nX
        (∀ p ∈ bounds, ∃ f ∈ M.fns, p.1 = f.name ∧
          InlOutSpec T host lt M Γ p.1 f p.2 nX)) := by
  intro hacyc hwf hsupp hwp hext hext_uniq hexits p hp
  obtain ⟨hacyc', hwf', hwp', hnames, hsigs⟩ := inlinePlan_compile_hyps plan hacyc hwf hwp
  obtain ⟨f', hf', hnm, hdef, hspec⟩ :=
    compile_sound T host lt (M.inlinePlan plan) Γ extCallees exits nX hints code bounds
      k₀ hcm hc hu hacyc' hwf' hsupp hwp'
      (by simpa [Env.ofModule_inlinePlan] using hext)
      ⟨hext_uniq.1, by simpa [hnames] using hext_uniq.2⟩ hexits p hp
  obtain ⟨f, hf, hfnm, hfas, hfrs⟩ := fn_sig_mem_of_map_eq hsigs hf'
  refine ⟨f, hf, hnm.trans hfnm.symm, hdef, ?_⟩
  rw [Env.ofModule_inlinePlan M Γ plan, ← hfas, ← hfrs] at hspec
  exact hspec

namespace Compiled

variable {T : Target} {lt : LegalTarget} {extCallees : List (SigEntry × Nat)}
  {exits : List Sym} {nX : Nat} {fs : List Fn} {hints : List T.toIsa.Hints} {maxBound : Nat}

/-- `Compiled` linking theorem after verified `Module.inlinePlan plan`, proving source
`mod : Module` specifications over any host containing `M.code`. -/
theorem fnSpec_inlinePlan (M : Compiled T lt extCallees exits nX fs hints maxBound)
    (mod : Module) (plan : InlPlan) (hfs : (mod.inlinePlan plan).fns = fs)
    (h : T.mach.Host) (Γ : Env) (k₀ : Nat)
    (hc : M.code.IsInfixAt (T.mach.prog h) k₀) (hu : T.LabelsUnique h) :
    InlModHyps lt mod (mod.inlinePlan plan) Γ
      (InlExtHyps T h lt mod Γ extCallees exits nX
        (∀ {f : Fn} (_hf : f ∈ mod.fns),
          InlOutSpec T h lt mod Γ f.name f (M.bound f.name) nX)) := by
  intro hacyc hwf hsupp hwp hext hext_uniq hexits f hf
  obtain ⟨hacyc', hwf', hwp', hnames, hsigs⟩ := inlinePlan_compile_hyps plan hacyc hwf hwp
  obtain ⟨f', hf', hfnm, hfas, hfrs⟩ := fn_sig_mem_of_map_eq hsigs.symm hf
  obtain ⟨hdef, hspec⟩ := M.fnSpec (mod.inlinePlan plan) hfs h Γ k₀ hc hu
    hacyc' hwf' hsupp hwp' (by simpa [Env.ofModule_inlinePlan] using hext)
    ⟨hext_uniq.1, by simpa [hnames] using hext_uniq.2⟩ hexits hf'
  rw [hfnm] at hdef hspec
  rw [hfas, hfrs, Env.ofModule_inlinePlan mod Γ plan] at hspec
  exact ⟨hdef, hspec⟩

/-- `Module.inlinePlan` specialization of `fnSpec_host` for `M.host` when `extCallees = []`. -/
theorem fnSpec_host_inlinePlan (M : Compiled T lt [] exits nX fs hints maxBound)
    (mod : Module) (plan : InlPlan) (hfs : (mod.inlinePlan plan).fns = fs) (Γ : Env) :
    InlModHyps lt mod (mod.inlinePlan plan) Γ
      (∀ {f : Fn} (_hf : f ∈ mod.fns),
        InlOutSpec T M.host lt mod Γ f.name f (M.bound f.name) nX) :=
  fun hacyc hwf hsupp hwp {_f} hf =>
    M.fnSpec_inlinePlan mod plan hfs M.host Γ 0 M.code_infix_host M.labelsUnique hacyc hwf
      hsupp hwp (fun _ h => nomatch h) ⟨(fun _ h => nomatch h), (fun _ h => nomatch h)⟩
      (fun _ hg => M.defined_exit_host hg) hf

/-- `Module.inlinePlan` empty-extern, empty-exit `FnSpec` wrapper over any host `h`. -/
theorem fnSpec_noExit_id_inlinePlan (M : Compiled T lt [] [] nX fs hints maxBound)
    (mod : Module) (plan : InlPlan) (hfs : (mod.inlinePlan plan).fns = fs)
    (h : T.mach.Host) (Γ : Env) (k₀ : Nat)
    (hc : M.code.IsInfixAt (T.mach.prog h) k₀) (hu : T.LabelsUnique h) :
    InlModHyps lt mod (mod.inlinePlan plan) Γ
      (∀ {f : Fn} (_hf : f ∈ mod.fns)
        (_has : lt.legalSig f.as = f.as) (_hrs : lt.legalSig f.rs = f.rs)
        (_hnoex : InlNoExit Γ f),
        T.Defined h f.name ∧ T.FnSpec h f.name (Γ f.name f.as f.rs) (M.bound f.name) nX) := by
  intro hacyc hwf hsupp hwp f hf has hrs hnoex
  obtain ⟨hdef, hspec⟩ := M.fnSpec_inlinePlan mod plan hfs h Γ k₀ hc hu hacyc hwf hsupp hwp
    (fun _ h => nomatch h) ⟨(fun _ h => nomatch h), (fun _ h => nomatch h)⟩
    (fun _ h => nomatch h) hf
  exact ⟨hdef, fnSpec_of_legalEnv_legalSig_eq_noExit has hrs
    (List.mem_append_left _ (List.mem_map_of_mem hf)) hnoex hspec⟩

end Compiled

end LeanQbe.T
