module

public import LeanQbe.T.MainLemmas
import LeanQbe.T.OptLemmas

/-!
# Verified `Module.optInline` Compilation Bridge

Standalone wrappers and end-to-end soundness theorems composing `Module.optInline`
(`Module.inline` + `Fn.renorm`) with `compile`, `compileModule`, `compile_sound`, and `Compiled`,
exposing source-module hypotheses and source-level specifications without modifying `Main.lean`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T

/-- Run acyclic policy-driven inlining on `M` and renormalize every function body. -/
@[expose] def Module.optInlinePolicy (M : Module) (policy : InlinePolicy := {}) : Module :=
  let M' := M.inlinePolicy policy
  { M' with fns := M'.fns.map Fn.renorm }

theorem Module.optInline_eq_optInlinePolicy (M : Module) (maxSize : Nat := 40) :
    M.optInline maxSize = M.optInlinePolicy (InlinePolicy.const maxSize) :=
  rfl

/-- Stack-checked module compilation after verified `Module.optInlinePolicy policy`. -/
@[expose] def compileModuleOptInlinePolicy (I : Isa) (lt : LegalTarget) (raBytes : Nat)
    (extCallees : List (SigEntry × Nat)) (exits : List Sym) (nX : Nat)
    (M : Module) (hints : List I.Hints) (policy : InlinePolicy := {}) :
    Except String (List I.Directive × List (Sym × Nat)) :=
  compileModule I lt raBytes extCallees exits nX (M.optInlinePolicy policy).fns hints

/-- Stack-checked module compilation after verified `Module.optInline maxSize`. -/
@[expose] def compileModuleOptInline (I : Isa) (lt : LegalTarget) (raBytes : Nat)
    (extCallees : List (SigEntry × Nat)) (exits : List Sym) (nX : Nat)
    (M : Module) (hints : List I.Hints) (maxSize : Nat := 40) :
    Except String (List I.Directive × List (Sym × Nat)) :=
  compileModule I lt raBytes extCallees exits nX (M.optInline maxSize).fns hints

theorem Module.optInlinePolicy_sigs (M : Module) (policy : InlinePolicy := {}) :
    (M.optInlinePolicy policy).sigs = M.sigs := by
  rw [← Module.inlinePolicy_sigs M policy]
  simp [Module.optInlinePolicy, Module.sigs, Fn.renorm, Fn.sig, List.map_map, Function.comp_def]

theorem Module.optInlinePolicy_names (M : Module) (policy : InlinePolicy := {}) :
    (M.optInlinePolicy policy).names = M.names := by
  rw [← Module.inlinePolicy_names M policy]
  simp [Module.optInlinePolicy, Module.names, Fn.renorm, List.map_map, Function.comp_def]

theorem Module.optInlinePolicy_namesNodup (M : Module) (policy : InlinePolicy := {}) :
    (M.optInlinePolicy policy).namesNodup ↔ M.namesNodup := by
  simp only [Module.namesNodup, Module.optInlinePolicy_names]

theorem Module.optInlinePolicy_externs (M : Module) (policy : InlinePolicy := {}) :
    (M.optInlinePolicy policy).externs = M.externs :=
  rfl

theorem Module.optInlinePolicy_exits (M : Module) (policy : InlinePolicy := {}) :
    (M.optInlinePolicy policy).exits = M.exits :=
  rfl

theorem Env.ofModule_optInlinePolicy (M : Module) (Γ : Env) (policy : InlinePolicy := {}) :
    Env.ofModule (M.optInlinePolicy policy) Γ = Env.ofModule M Γ := by
  simp [Env.ofModule, Module.optInlinePolicy_sigs]

theorem Module.optInline_sigs (M : Module) (maxSize : Nat) :
    (M.optInline maxSize).sigs = M.sigs :=
  Module.optInlinePolicy_sigs M (InlinePolicy.const maxSize)

theorem Module.optInline_names (M : Module) (maxSize : Nat) :
    (M.optInline maxSize).names = M.names :=
  Module.optInlinePolicy_names M (InlinePolicy.const maxSize)

theorem Module.optInline_namesNodup (M : Module) (maxSize : Nat) :
    (M.optInline maxSize).namesNodup ↔ M.namesNodup :=
  Module.optInlinePolicy_namesNodup M (InlinePolicy.const maxSize)

theorem Module.optInline_externs (M : Module) (maxSize : Nat) :
    (M.optInline maxSize).externs = M.externs :=
  rfl

theorem Module.optInline_exits (M : Module) (maxSize : Nat) :
    (M.optInline maxSize).exits = M.exits :=
  rfl

theorem Env.ofModule_optInline (M : Module) (Γ : Env) (maxSize : Nat) :
    Env.ofModule (M.optInline maxSize) Γ = Env.ofModule M Γ :=
  Env.ofModule_optInlinePolicy M Γ (InlinePolicy.const maxSize)

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

/-- Module correctness theorem for `Module.optInlinePolicy`: policy-driven acyclic inlining
followed by AST renormalization preserves `ModuleOk Γ`. -/
theorem Module.optInlinePolicy_ok {Γ : Env} {M : Module} (policy : InlinePolicy := {}) :
    ModuleOk Γ M → ModuleOk Γ (M.optInlinePolicy policy) := fun hM => by
  have hInl : ModuleOk Γ (M.inlinePolicy policy) := Module.inlinePolicy_ok policy hM
  refine ⟨?_, fun pre fn post hsplit => ?_⟩
  · have hnames : (M.optInlinePolicy policy).names = (M.inlinePolicy policy).names := by
      simp [Module.optInlinePolicy, Module.names, List.map_map, Function.comp_def, Fn.renorm]
    show (M.optInlinePolicy policy).names.Nodup
    exact hnames ▸ hInl.nodup
  · dsimp only [Module.optInlinePolicy] at hsplit
    obtain ⟨pre₀, fn₀, post₀, hl, hpre, rfl, _⟩ :=
      map_eq_append_split Fn.renorm (M.inlinePolicy policy).fns pre fn post hsplit
    obtain ⟨hwf₀, hcalls₀, hspec₀⟩ := hInl.fnsOk pre₀ fn₀ post₀ hl
    have hsig : pre.map Fn.sig = pre₀.map Fn.sig := by
      rw [hpre, List.map_map]
      congr 1
    refine ⟨Fn.renorm_wf fn₀, ?_, fun xs m Q X hg => Fn.renorm_spec hwf₀ (hspec₀ xs m Q X hg)⟩
    dsimp only [Module.optInlinePolicy, Module.inlinePolicy] at hcalls₀ ⊢
    simpa [Fn.callsOk, Fn.renorm, hsig] using Func.renorm_callsOk hwf₀ hcalls₀

private theorem checkAcyclic_of_moduleOk {Γ : Env} {M : Module} (hM : ModuleOk Γ M) :
    M.checkAcyclic = true := by
  simp only [Module.checkAcyclic, Bool.and_eq_true]
  refine ⟨listNodup_iff.mpr hM.nodup,
    checkFnsCallsOk_of_forall _ _ [] _ fun pre fn post hsp => ?_⟩
  simpa using (hM.fnsOk pre fn post hsp).2.1

private theorem optInlinePolicy_moduleOk_bot {M : Module} (policy : InlinePolicy)
    (hchk : M.checkAcyclic = true) (hwf : ∀ f ∈ M.fns, f.Wf) :
    ModuleOk (fun _ _ _ _ _ _ _ => False) (M.optInlinePolicy policy) :=
  Module.optInlinePolicy_ok policy
    (Module.moduleOk_of_checkAcyclic (Γ := fun _ _ _ _ _ _ _ => False) hchk hwf
      (fun _ _ _ _ _ _ => False.elim))

/-- `Module.optInlinePolicy` preserves `Module.checkAcyclic` when all source functions are `Wf`. -/
theorem Module.optInlinePolicy_checkAcyclic {M : Module} (policy : InlinePolicy := {})
    (hchk : M.checkAcyclic = true) (hwf : ∀ f ∈ M.fns, f.Wf) :
    (M.optInlinePolicy policy).checkAcyclic = true :=
  checkAcyclic_of_moduleOk (optInlinePolicy_moduleOk_bot policy hchk hwf)

/-- Alias for `Module.optInlinePolicy_checkAcyclic`. -/
theorem Module.optInlinePolicy_acyclic {M : Module} (policy : InlinePolicy := {})
    (hchk : M.checkAcyclic = true) (hwf : ∀ f ∈ M.fns, f.Wf) :
    (M.optInlinePolicy policy).checkAcyclic = true :=
  Module.optInlinePolicy_checkAcyclic policy hchk hwf

/-- `Module.optInlinePolicy` preserves `Fn.Wf` for every function in an acyclic module. -/
theorem Module.optInlinePolicy_wf {M : Module} (policy : InlinePolicy := {})
    (hchk : M.checkAcyclic = true) (hwf : ∀ f ∈ M.fns, f.Wf) :
    ∀ f ∈ (M.optInlinePolicy policy).fns, f.Wf := by
  have hm := optInlinePolicy_moduleOk_bot policy hchk hwf
  intro f hf
  obtain ⟨pre, post, hsp⟩ := List.mem_iff_append.mp hf
  exact (hm.fnsOk pre f post hsp).1

/-- `Module.optInlinePolicy` preserves `Fn.callsOk` along the acyclic module function list. -/
theorem Module.optInlinePolicy_callsOk {M : Module} (policy : InlinePolicy := {})
    (hchk : M.checkAcyclic = true) (hwf : ∀ f ∈ M.fns, f.Wf) :
    ∀ pre fn post, (M.optInlinePolicy policy).fns = pre ++ fn :: post →
      fn.callsOk (pre.map Fn.sig ++ M.externs.map Extern.sig) M.exits := by
  have hm := optInlinePolicy_moduleOk_bot policy hchk hwf
  intro pre fn post hsp
  exact (hm.fnsOk pre fn post hsp).2.1

/-- `Module.optInlinePolicy` preserves `Func.wp` contracts for every function in an acyclic
module. -/
theorem Module.optInlinePolicy_spec {Γ : Env} {M : Module} (policy : InlinePolicy := {})
    (hM : ModuleOk Γ M) :
    ∀ f ∈ (M.optInlinePolicy policy).fns, ∀ xs m Q X,
      Γ f.name f.as f.rs xs m Q X → Func.wp Γ f.body xs m Q X := by
  have hm := Module.optInlinePolicy_ok policy hM
  intro f hf
  obtain ⟨pre, post, hsp⟩ := List.mem_iff_append.mp hf
  exact (hm.fnsOk pre f post hsp).2.2

private theorem tblocks_supportsSource_get (target : LegalTarget) {rs : List Ty} :
    ∀ {sig : List (List Ty)} (bs : Blocks K KL rs sig) {nv nl : Nat},
      (toTBlocks bs nv nl).supportsSource target = true →
      ∀ {ts} (i : Member ts sig),
        ts.all target.supportsTy = true ∧
        (toTFlat (bs.get i (Tup.levels ts nv)) (nv + ts.length) nl).supportsSource target = true
  | _, .cons _ _, _, _, hs, _, .here => by
      dsimp only [toTBlocks, TBlocks.supportsSource] at hs
      rw [Bool.and_eq_true, Bool.and_eq_true] at hs
      exact ⟨hs.1.1, hs.1.2⟩
  | _, .cons _ bs, _, _, hs, _, .there i => by
      dsimp only [toTBlocks, TBlocks.supportsSource] at hs
      rw [Bool.and_eq_true] at hs
      exact tblocks_supportsSource_get target bs hs.2 i

private theorem tblocks_supportsSource_of_get (target : LegalTarget) {rs : List Ty} :
    ∀ {sig : List (List Ty)} (bs : Blocks K KL rs sig) (nv nl : Nat),
      (∀ {ts} (i : Member ts sig),
        ts.all target.supportsTy = true ∧
        (toTFlat (bs.get i (Tup.levels ts nv)) (nv + ts.length) nl).supportsSource target = true) →
      (toTBlocks bs nv nl).supportsSource target = true
  | _, .nil, _, _, _ => rfl
  | _, .cons _ bs, nv, nl, h => by
      dsimp only [toTBlocks, TBlocks.supportsSource]
      rw [Bool.and_eq_true, Bool.and_eq_true]
      have h0 := h .here
      exact ⟨⟨h0.1, h0.2⟩, tblocks_supportsSource_of_get target bs nv nl fun i => h (.there i)⟩

private theorem spliceRet_supportsSource (target : LegalTarget) {calleeRs callerRs : List Ty}
    {j₁ : KL calleeRs}
    {G : Ctx (Arg K) K} {D : Ctx KL KL}
    {e₁ : Expr (Arg K) KL calleeRs} {e₂ : Expr K KL calleeRs}
    (hwf : Wf G D e₁ e₂) :
    ∀ nv₁ nl₁ nv₂ nl₂,
      (toTFlat e₂ nv₂ nl₂).supportsSource target = true →
      (toTFlat (spliceRet (callerRs := callerRs) j₁ e₁) nv₁ nl₁).supportsSource target = true := by
  induction hwf using Wf.induct with
  | let_ hop _ ih =>
      intro nv₁ nl₁ nv₂ nl₂ hs
      cases hop with
      | mk code _ =>
          dsimp only [spliceRet, flattenOp, toTFlat, TFlat.supportsSource] at hs ⊢
          rw [Bool.and_eq_true] at hs ⊢
          exact ⟨hs.1, ih _ _ _ _ _ _ hs.2⟩
  | load t _ _ ih =>
      intro nv₁ nl₁ nv₂ nl₂ hs
      dsimp only [spliceRet, toTFlat, TFlat.supportsSource] at hs ⊢
      rw [Bool.and_eq_true] at hs ⊢
      exact ⟨hs.1, ih _ _ _ _ _ _ hs.2⟩
  | store _ _ _ ih =>
      intro nv₁ nl₁ nv₂ nl₂ hs
      dsimp only [spliceRet, toTFlat, TFlat.supportsSource] at hs ⊢
      rw [Bool.and_eq_true] at hs ⊢
      exact ⟨hs.1, ih _ _ _ _ hs.2⟩
  | call f _ _ ih =>
      intro nv₁ nl₁ nv₂ nl₂ hs
      dsimp only [spliceRet, toTFlat, TFlat.supportsSource] at hs ⊢
      rw [Bool.and_eq_true] at hs ⊢
      exact ⟨hs.1, ih _ _ _ _ _ _ hs.2⟩
  | jnz _ _ _ iht ihe =>
      intro nv₁ nl₁ nv₂ nl₂ hs
      dsimp only [spliceRet, toTFlat, TFlat.supportsSource] at hs ⊢
      rw [Bool.and_eq_true] at hs ⊢
      exact ⟨iht _ _ _ _ hs.1, ihe _ _ _ _ hs.2⟩
  | jump _ _ =>
      intro _ _ _ _ hs
      exact hs
  | ret _ =>
      intro _ _ _ _ hs
      exact hs
  | exit _ _ =>
      intro _ _ _ _ hs
      exact hs
  | hlt =>
      intro _ _ _ _ _
      rfl
  | @group _ _ sig b₁ b₂ _ _ _ _ ihb ihk =>
      intro nv₁ nl₁ nv₂ nl₂ hs
      dsimp only [spliceRet, toTFlat, TFlat.supportsSource] at hs ⊢
      rw [Bool.and_eq_true, Bool.and_eq_true] at hs ⊢
      refine ⟨⟨hs.1.1, tblocks_supportsSource_of_get target _ nv₁ (nl₁ + sig.length) fun i => ?_⟩,
        ihk (Tup.levels sig nl₁) (Tup.levels sig nl₂) nv₁ (nl₁ + sig.length) nv₂
          (nl₂ + sig.length) hs.2⟩
      have hget := tblocks_supportsSource_get target (b₂ (Tup.levels sig nl₂)) hs.1.2 i
      refine ⟨hget.1, ?_⟩
      rw [spliceRetB_get]
      exact ihb (Tup.levels sig nl₁) (Tup.levels sig nl₂) i (toArgTup _) (Tup.levels _ nv₂)
        (nv₁ + _) (nl₁ + sig.length) (nv₂ + _) (nl₂ + sig.length) hget.2

private def CandsSupportsSource (target : LegalTarget) (cands : List Fn) : Prop :=
  ∀ fn ∈ cands, fn.Wf ∧ fn.body.supportsSource target = true

private theorem inlineExpr_supportsSource (target : LegalTarget) {cands : List Fn}
    (hcands : CandsSupportsSource target cands) {rs : List Ty}
    {G : Ctx K K} {D : Ctx KL KL} {e₁ e₂ : Expr K KL rs} (hwf : Wf G D e₁ e₂) :
    ∀ nv₁ nl₁ nv₂ nl₂, (toTFlat e₂ nv₂ nl₂).supportsSource target = true →
      (toTFlat (inlineExpr cands e₁) nv₁ nl₁).supportsSource target = true := by
  induction hwf using Wf.induct with
  | let_ hop _ ih =>
      intro nv₁ nl₁ nv₂ nl₂ hs
      cases hop with
      | mk code _ =>
          dsimp only [inlineExpr, toTFlat, TFlat.supportsSource] at hs ⊢
          rw [Bool.and_eq_true] at hs ⊢
          exact ⟨hs.1, ih _ _ _ _ _ _ hs.2⟩
  | load t _ _ ih =>
      intro nv₁ nl₁ nv₂ nl₂ hs
      dsimp only [inlineExpr, toTFlat, TFlat.supportsSource] at hs ⊢
      rw [Bool.and_eq_true] at hs ⊢
      exact ⟨hs.1, ih _ _ _ _ _ _ hs.2⟩
  | store _ _ _ ih =>
      intro nv₁ nl₁ nv₂ nl₂ hs
      dsimp only [inlineExpr, toTFlat, TFlat.supportsSource] at hs ⊢
      rw [Bool.and_eq_true] at hs ⊢
      exact ⟨hs.1, ih _ _ _ _ hs.2⟩
  | @call _ _ f as bs args₁ _ _ _ _ _ ih =>
      intro nv₁ nl₁ nv₂ nl₂ hs
      dsimp only [toTFlat, TFlat.supportsSource] at hs
      rw [Bool.and_eq_true, Bool.and_eq_true] at hs
      rw [inlineExpr_call]
      cases hlook : lookupCallee cands f as bs with
      | none =>
          dsimp only [toTFlat, TFlat.supportsSource]
          rw [Bool.and_eq_true, Bool.and_eq_true]
          exact ⟨hs.1, ih _ _ _ _ _ _ hs.2⟩
      | some callee =>
          obtain ⟨fn, hfn, _, ha, hr, rfl⟩ := lookupCallee_mem hlook
          subst ha; subst hr
          obtain ⟨hwf_fn, hsupp_fn⟩ := hcands fn hfn
          dsimp only [Func.supportsSource] at hsupp_fn
          rw [Bool.and_eq_true] at hsupp_fn
          dsimp only [toTFlat, toTBlocks, TFlat.supportsSource, TBlocks.supportsSource, List.all]
          simp only [Bool.and_true, Bool.and_eq_true]
          refine ⟨⟨hs.1.2, ⟨hs.1.2, ih (Tup.levels fn.rs nv₁) (Tup.levels fn.rs nv₂)
            (nv₁ + fn.rs.length) (nl₁ + 1) (nv₂ + fn.rs.length) nl₂ hs.2⟩⟩, ?_⟩
          exact spliceRet_supportsSource target
            (hwf_fn (Arg K) K KL KL args₁ (Tup.levels fn.as 0))
            nv₁ (nl₁ + 1) fn.as.length 0 hsupp_fn.2
  | jnz _ _ _ iht ihe =>
      intro nv₁ nl₁ nv₂ nl₂ hs
      dsimp only [inlineExpr, toTFlat, TFlat.supportsSource] at hs ⊢
      rw [Bool.and_eq_true] at hs ⊢
      exact ⟨iht _ _ _ _ hs.1, ihe _ _ _ _ hs.2⟩
  | jump _ _ =>
      intro _ _ _ _ hs
      exact hs
  | ret _ =>
      intro _ _ _ _ hs
      exact hs
  | exit _ _ =>
      intro _ _ _ _ hs
      exact hs
  | hlt =>
      intro _ _ _ _ _
      rfl
  | @group _ _ sig _ b₂ _ _ _ _ ihb ihk =>
      intro nv₁ nl₁ nv₂ nl₂ hs
      dsimp only [inlineExpr, toTFlat, TFlat.supportsSource] at hs ⊢
      rw [Bool.and_eq_true, Bool.and_eq_true] at hs ⊢
      refine ⟨⟨hs.1.1, tblocks_supportsSource_of_get target _ nv₁ (nl₁ + sig.length) fun i => ?_⟩,
        ihk (Tup.levels sig nl₁) (Tup.levels sig nl₂) nv₁ (nl₁ + sig.length) nv₂
          (nl₂ + sig.length) hs.2⟩
      have hget := tblocks_supportsSource_get target (b₂ (Tup.levels sig nl₂)) hs.1.2 i
      rw [inlineBlocks_get]
      exact ⟨hget.1, ihb (Tup.levels sig nl₁) (Tup.levels sig nl₂) i (Tup.levels _ nv₁)
        (Tup.levels _ nv₂) (nv₁ + _) (nl₁ + sig.length) (nv₂ + _) (nl₂ + sig.length) hget.2⟩

private theorem toTFlat_denote_supportsSource (target : LegalTarget) :
    {rs : List Ty} → (tf : TFlat rs) → tf.supportsSource target = true →
    ∀ (vs : List ((t : Ty) × K t)) (ls : List ((ts : List Ty) × KL ts)) (nv nl : Nat),
      (toTFlat (denote K KL tf vs ls) nv nl).supportsSource target = true
  | _, .let_ op k, hs, vs, ls, nv, nl => by
      dsimp only [TFlat.supportsSource] at hs
      rw [Bool.and_eq_true] at hs
      dsimp only [denote]
      cases denoteArgs vs op.args with
      | none => rfl
      | some _ =>
          dsimp only [toTFlat, TFlat.supportsSource]
          rw [Bool.and_eq_true]
          exact ⟨hs.1, toTFlat_denote_supportsSource target k hs.2 _ ls _ nl⟩
  | _, .load t a k, hs, vs, ls, nv, nl => by
      dsimp only [TFlat.supportsSource] at hs
      rw [Bool.and_eq_true] at hs
      dsimp only [denote]
      cases denoteArg vs a with
      | none => rfl
      | some _ =>
          dsimp only [toTFlat, TFlat.supportsSource]
          rw [Bool.and_eq_true]
          exact ⟨hs.1, toTFlat_denote_supportsSource target k hs.2 _ ls _ nl⟩
  | _, .store v a k, hs, vs, ls, nv, nl => by
      dsimp only [TFlat.supportsSource] at hs
      rw [Bool.and_eq_true] at hs
      dsimp only [denote]
      cases denoteArg vs v with
      | none => rfl
      | some _ =>
          cases denoteArg vs a with
          | none => rfl
          | some _ =>
              dsimp only [toTFlat, TFlat.supportsSource]
              rw [Bool.and_eq_true]
              exact ⟨hs.1, toTFlat_denote_supportsSource target k hs.2 vs ls nv nl⟩
  | _, .call f bs args k, hs, vs, ls, nv, nl => by
      dsimp only [TFlat.supportsSource] at hs
      rw [Bool.and_eq_true] at hs
      dsimp only [denote]
      cases denoteArgs vs args with
      | none => rfl
      | some _ =>
          dsimp only [toTFlat, TFlat.supportsSource]
          rw [Bool.and_eq_true]
          exact ⟨hs.1, toTFlat_denote_supportsSource target k hs.2 _ ls _ nl⟩
  | _, .jnz c t e, hs, vs, ls, nv, nl => by
      dsimp only [TFlat.supportsSource] at hs
      rw [Bool.and_eq_true] at hs
      dsimp only [denote]
      cases denoteArg vs c with
      | none => rfl
      | some _ =>
          dsimp only [toTFlat, TFlat.supportsSource]
          rw [Bool.and_eq_true]
          exact ⟨toTFlat_denote_supportsSource target t hs.1 vs ls nv nl,
                 toTFlat_denote_supportsSource target e hs.2 vs ls nv nl⟩
  | _, .jump j args, hs, vs, ls, nv, nl => by
      dsimp only [denote]
      cases lookupL ls _ j with
      | none => rfl
      | some _ =>
          cases denoteArgs vs args with
          | none => rfl
          | some _ => exact hs
  | _, .ret vs', hs, vs, _, _, _ => by
      dsimp only [denote]
      cases denoteArgs vs vs' with
      | none => rfl
      | some _ => exact hs
  | _, .exit f args, hs, vs, _, _, _ => by
      dsimp only [denote]
      cases denoteArgs vs args with
      | none => rfl
      | some _ => exact hs
  | _, .hlt, _, _, _, _, _ => rfl
  | _, .group (sig := sig) bodies k, hs, vs, ls, nv, nl => by
      dsimp only [TFlat.supportsSource] at hs
      rw [Bool.and_eq_true, Bool.and_eq_true] at hs
      dsimp only [denote, toTFlat, TFlat.supportsSource]
      rw [Bool.and_eq_true, Bool.and_eq_true]
      refine ⟨⟨hs.1.1, tblocks_supportsSource_of_get target _ nv (nl + sig.length) fun i => ?_⟩,
        toTFlat_denote_supportsSource target k hs.2 vs _ nv (nl + sig.length)⟩
      exact toTBlocks_denote_supportsSource target bodies hs.1.2 vs _ nv (nl + sig.length) i
where
  toTBlocks_denote_supportsSource (target : LegalTarget) {rs : List Ty} :
      {sig : List (List Ty)} → (bs : TBlocks rs sig) → bs.supportsSource target = true →
      ∀ (vs : List ((t : Ty) × K t)) (ls : List ((ts : List Ty) × KL ts)) (nv nl : Nat)
        {ts} (i : Member ts sig),
        ts.all target.supportsTy = true ∧
        (toTFlat ((denoteB K KL bs vs ls).get i (Tup.levels ts nv)) (nv + ts.length)
          nl).supportsSource target = true
    | _, .cons b bs, hs, vs, ls, nv, nl, _, .here => by
        dsimp only [TBlocks.supportsSource] at hs
        rw [Bool.and_eq_true, Bool.and_eq_true] at hs
        exact ⟨hs.1.1, toTFlat_denote_supportsSource target b hs.1.2 _ ls _ nl⟩
    | _, .cons _ bs, hs, vs, ls, nv, nl, _, .there i => by
        dsimp only [TBlocks.supportsSource] at hs
        rw [Bool.and_eq_true] at hs
        exact toTBlocks_denote_supportsSource target bs hs.2 vs ls nv nl i

private theorem Func.renorm_supportsSource (target : LegalTarget) {as rs : List Ty}
    (f : Func as rs) (hsupp : f.supportsSource target = true) :
    (Func.renorm f).supportsSource target = true := by
  dsimp only [Func.supportsSource] at hsupp ⊢
  rw [Bool.and_eq_true] at hsupp ⊢
  refine ⟨hsupp.1, ?_⟩
  exact toTFlat_denote_supportsSource target (reifyFunc f) hsupp.2 _ _ _ _

/-- `Module.inlinePolicy` preserves `Func.supportsSource lt` for every function in `M`. -/
theorem Module.inlinePolicy_supportsSource (lt : LegalTarget) {M : Module}
    (policy : InlinePolicy := {}) (hwf : ∀ f ∈ M.fns, f.Wf)
    (hsupp : ∀ f ∈ M.fns, f.body.supportsSource lt = true) :
    ∀ f ∈ (M.inlinePolicy policy).fns, f.body.supportsSource lt = true := by
  have hP := inlineFnsPolicy_preserve
    (fun fn => fn.Wf ∧ fn.body.supportsSource lt = true)
    policy (if policy.singleSiteMax > 0 || policy.maxTotalDup > 0 then fnsCallSites M.fns else [])
    (if policy.requireLoopSite then fnsLoopCallSites M.fns else [])
    (M.externs.map Extern.sig) M.exits
    (fun cands fn hc hfn => by
      refine ⟨Fn.inline_wf (fun c hc' => (hc c hc').1) hfn.1, ?_⟩
      dsimp only [Func.supportsSource] at hfn ⊢
      rw [Bool.and_eq_true] at hfn ⊢
      exact ⟨hfn.2.1, inlineExpr_supportsSource lt hc
        (hfn.1 K K KL KL (Tup.levels fn.as 0) (Tup.levels fn.as 0))
        fn.as.length 0 fn.as.length 0 hfn.2.2⟩)
    [] [] M.fns (fun _ h => nomatch h) (fun f hf => ⟨hwf f hf, hsupp f hf⟩)
  intro f hf
  exact (hP f hf).2

/-- `Module.optInlinePolicy` preserves `Func.supportsSource lt` for every function in `M`. -/
theorem Module.optInlinePolicy_supportsSource (lt : LegalTarget) {M : Module}
    (policy : InlinePolicy := {}) (hwf : ∀ f ∈ M.fns, f.Wf)
    (hsupp : ∀ f ∈ M.fns, f.body.supportsSource lt = true) :
    ∀ f ∈ (M.optInlinePolicy policy).fns, f.body.supportsSource lt = true := by
  have hInl := Module.inlinePolicy_supportsSource lt policy hwf hsupp
  intro f hf
  dsimp only [Module.optInlinePolicy] at hf
  obtain ⟨f₀, hf₀, rfl⟩ := List.mem_map.mp hf
  exact Func.renorm_supportsSource lt f₀.body (hInl f₀ hf₀)

/-- `Module.optInline` preserves `Module.checkAcyclic` when all source functions are `Wf`. -/
theorem Module.optInline_checkAcyclic {M : Module} (maxSize : Nat)
    (hchk : M.checkAcyclic = true) (hwf : ∀ f ∈ M.fns, f.Wf) :
    (M.optInline maxSize).checkAcyclic = true :=
  Module.optInlinePolicy_checkAcyclic (InlinePolicy.const maxSize) hchk hwf

/-- `Module.optInline` preserves `Fn.Wf` for every function in an acyclic module. -/
theorem Module.optInline_wf {M : Module} (maxSize : Nat)
    (hchk : M.checkAcyclic = true) (hwf : ∀ f ∈ M.fns, f.Wf) :
    ∀ f ∈ (M.optInline maxSize).fns, f.Wf :=
  Module.optInlinePolicy_wf (InlinePolicy.const maxSize) hchk hwf

private theorem optInlinePolicy_compile_hyps {M : Module} {Γ : Env} (policy : InlinePolicy)
    (hacyc : M.checkAcyclic = true) (hwf : ∀ f ∈ M.fns, f.Wf)
    (hwp : ∀ f ∈ M.fns, ∀ xs m Q X, Γ f.name f.as f.rs xs m Q X → Func.wp Γ f.body xs m Q X) :
    (M.optInlinePolicy policy).checkAcyclic = true ∧
    (∀ f ∈ (M.optInlinePolicy policy).fns, f.Wf) ∧
    (∀ f ∈ (M.optInlinePolicy policy).fns, ∀ xs m Q X,
      Γ f.name f.as f.rs xs m Q X → Func.wp Γ f.body xs m Q X) ∧
    (M.optInlinePolicy policy).fns.map Fn.name = M.fns.map Fn.name ∧
    (M.optInlinePolicy policy).fns.map Fn.sig = M.fns.map Fn.sig := by
  have hm' := Module.optInlinePolicy_ok policy (Module.moduleOk_of_checkAcyclic hacyc hwf hwp)
  refine ⟨checkAcyclic_of_moduleOk hm', fun f hf => ?_, fun f hf => ?_, ?_, ?_⟩
  · obtain ⟨pre, post, hsp⟩ := List.mem_iff_append.mp hf
    exact (hm'.fnsOk pre f post hsp).1
  · obtain ⟨pre, post, hsp⟩ := List.mem_iff_append.mp hf
    exact (hm'.fnsOk pre f post hsp).2.2
  · have h := Module.optInlinePolicy_names M policy
    simp only [Module.names, Module.optInlinePolicy_externs] at h
    exact List.append_cancel_right h
  · have h := Module.optInlinePolicy_sigs M policy
    simp only [Module.sigs, Module.optInlinePolicy_externs] at h
    exact List.append_cancel_right h

/-- Bundled source-module well-formedness, support, and `Func.wp` hypotheses after inlining. -/
abbrev InlModHyps (lt : LegalTarget) (m₁ m₂ : Module) (Γ : Env) (rest : Prop) : Prop :=
  ∀ (_hacyc : m₁.checkAcyclic = true) (_hwf : ∀ f ∈ m₁.fns, f.Wf)
    (_hsupp : ∀ f ∈ m₂.fns, (f.earlyOpt).body.supportsSource lt = true)
    (_hwp : ∀ f ∈ m₁.fns, ∀ xs m Q X,
      Γ f.name f.as f.rs xs m Q X → Func.wp Γ f.body xs m Q X),
    rest

/-- Bundled external-callee and exit hypotheses for inline compilation soundness. -/
abbrev InlExtHyps (T : Target) (h : T.mach.Host) (lt : LegalTarget) (m₁ : Module) (Γ : Env)
    (ext : List (SigEntry × Nat)) (exits : List Sym) (nX : Nat) (rest : Prop) : Prop :=
  ∀ (_hext : ∀ p ∈ ext,
      T.FnSpec h p.1.1 (legalEnv lt (Env.ofModule m₁ Γ) p.1.1 p.1.2.1 p.1.2.2) p.2 nX)
    (_hext_uniq : (∀ p ∈ ext, ∀ q ∈ ext, p.1.1 = q.1.1 → p.2 = q.2) ∧
      (∀ p ∈ ext, p.1.1 ∉ m₁.fns.map Fn.name))
    (_hexits : ∀ g ∈ exits, T.Defined h g),
    rest

/-- Post-compilation `Defined ∧ FnSpec` target guarantee under source module `Env.ofModule m₁ Γ`. -/
abbrev InlOutSpec (T : Target) (h : T.mach.Host) (lt : LegalTarget) (m₁ : Module) (Γ : Env)
    (nm : Sym) (f : Fn) (b nX : Nat) : Prop :=
  T.Defined h nm ∧ T.FnSpec h nm
    (legalEnv lt (Env.ofModule m₁ Γ) nm (lt.legalSig f.as) (lt.legalSig f.rs)) b nX

/-- End-to-end compilation soundness after verified `Module.optInlinePolicy policy`, exposing
source module hypotheses `M` and source-level specifications under `Env.ofModule M Γ`. -/
theorem compile_sound_optInlinePolicy (T : Target) (host : T.mach.Host) (lt : LegalTarget)
    (M : Module) (Γ : Env) (extCallees : List (SigEntry × Nat)) (exits : List Sym)
    (nX : Nat) (policy : InlinePolicy) (hints : List T.toIsa.Hints) (code : List T.Directive)
    (bounds : List (Sym × Nat)) (k₀ : Nat)
    (hcm : compileModuleOptInlinePolicy T.toIsa lt T.frame.raBytes extCallees exits nX M hints
        policy = .ok (code, bounds))
    (hc : code.IsInfixAt (T.mach.prog host) k₀) (hu : T.LabelsUnique host) :
    InlModHyps lt M (M.optInlinePolicy policy) Γ
      (InlExtHyps T host lt M Γ extCallees exits nX
        (∀ p ∈ bounds, ∃ f ∈ M.fns, p.1 = f.name ∧
          InlOutSpec T host lt M Γ p.1 f p.2 nX)) := by
  intro hacyc hwf hsupp hwp hext hext_uniq hexits p hp
  obtain ⟨hacyc', hwf', hwp', hnames, hsigs⟩ :=
    optInlinePolicy_compile_hyps policy hacyc hwf hwp
  obtain ⟨f', hf', hnm, hdef, hspec⟩ :=
    compile_sound T host lt (M.optInlinePolicy policy) Γ extCallees exits nX hints code bounds
      k₀ hcm hc hu hacyc' hwf' hsupp hwp'
      (by simpa [Env.ofModule_optInlinePolicy] using hext)
      ⟨hext_uniq.1, by simpa [hnames] using hext_uniq.2⟩ hexits p hp
  have hsigMem : f'.sig ∈ M.fns.map Fn.sig := hsigs ▸ List.mem_map_of_mem hf'
  obtain ⟨f, hf, hsigEq⟩ := List.mem_map.mp hsigMem
  simp only [Fn.sig, Prod.mk.injEq] at hsigEq
  rcases hsigEq with ⟨hfnm, hfas, hfrs⟩
  refine ⟨f, hf, hnm.trans hfnm.symm, hdef, ?_⟩
  rw [Env.ofModule_optInlinePolicy M Γ policy, ← hfas, ← hfrs] at hspec
  exact hspec

/-- Alias for `compile_sound_optInlinePolicy`. -/
abbrev optInlinePolicy_sound := @compile_sound_optInlinePolicy

/-- End-to-end compilation soundness after verified `Module.optInline maxSize`, exposing source
module hypotheses `M` and source-level specifications under `Env.ofModule M Γ`. -/
theorem compile_sound_optInline (T : Target) (host : T.mach.Host) (lt : LegalTarget)
    (M : Module) (Γ : Env) (extCallees : List (SigEntry × Nat)) (exits : List Sym)
    (nX maxSize : Nat) (hints : List T.toIsa.Hints) (code : List T.Directive)
    (bounds : List (Sym × Nat)) (k₀ : Nat)
    (hcm : compileModuleOptInline T.toIsa lt T.frame.raBytes extCallees exits nX M hints
        maxSize = .ok (code, bounds))
    (hc : code.IsInfixAt (T.mach.prog host) k₀) (hu : T.LabelsUnique host) :
    InlModHyps lt M (M.optInline maxSize) Γ
      (InlExtHyps T host lt M Γ extCallees exits nX
        (∀ p ∈ bounds, ∃ f ∈ M.fns, p.1 = f.name ∧
          InlOutSpec T host lt M Γ p.1 f p.2 nX)) :=
  fun hacyc hwf hsupp hwp hext hext_uniq hexits =>
    compile_sound_optInlinePolicy T host lt M Γ extCallees exits nX (InlinePolicy.const maxSize)
      hints code bounds k₀ hcm hc hu hacyc hwf hsupp hwp hext hext_uniq hexits

namespace Compiled

variable {T : Target} {lt : LegalTarget} {extCallees : List (SigEntry × Nat)}
  {exits : List Sym} {nX : Nat} {fs : List Fn} {hints : List T.toIsa.Hints} {maxBound : Nat}

/-- `Compiled` linking theorem after verified `Module.optInlinePolicy policy`, proving source
`mod : Module` specifications over any host containing `M.code`. -/
theorem fnSpec_optInlinePolicy (M : Compiled T lt extCallees exits nX fs hints maxBound)
    (mod : Module) (policy : InlinePolicy) (hfs : (mod.optInlinePolicy policy).fns = fs)
    (h : T.mach.Host) (Γ : Env) (k₀ : Nat)
    (hc : M.code.IsInfixAt (T.mach.prog h) k₀) (hu : T.LabelsUnique h) :
    InlModHyps lt mod (mod.optInlinePolicy policy) Γ
      (InlExtHyps T h lt mod Γ extCallees exits nX
        (∀ {f : Fn} (_hf : f ∈ mod.fns),
          InlOutSpec T h lt mod Γ f.name f (M.bound f.name) nX)) := by
  intro hacyc hwf hsupp hwp hext hext_uniq hexits f hf
  obtain ⟨hacyc', hwf', hwp', hnames, hsigs⟩ :=
    optInlinePolicy_compile_hyps policy hacyc hwf hwp
  have hsigMem : f.sig ∈ (mod.optInlinePolicy policy).fns.map Fn.sig := by
    rw [hsigs]; exact List.mem_map_of_mem hf
  obtain ⟨f', hf', hsigEq⟩ := List.mem_map.mp hsigMem
  simp only [Fn.sig, Prod.mk.injEq] at hsigEq
  rcases hsigEq with ⟨hfnm, hfas, hfrs⟩
  obtain ⟨hdef, hspec⟩ := M.fnSpec (mod.optInlinePolicy policy) hfs h Γ k₀ hc hu
    hacyc' hwf' hsupp hwp' (by simpa [Env.ofModule_optInlinePolicy] using hext)
    ⟨hext_uniq.1, by simpa [hnames] using hext_uniq.2⟩ hexits hf'
  rw [hfnm] at hdef hspec
  rw [hfas, hfrs, Env.ofModule_optInlinePolicy mod Γ policy] at hspec
  exact ⟨hdef, hspec⟩

/-- `Module.optInlinePolicy` specialization of `fnSpec_host` for `M.host` when
`extCallees = []`. -/
theorem fnSpec_host_optInlinePolicy (M : Compiled T lt [] exits nX fs hints maxBound)
    (mod : Module) (policy : InlinePolicy) (hfs : (mod.optInlinePolicy policy).fns = fs)
    (Γ : Env) :
    InlModHyps lt mod (mod.optInlinePolicy policy) Γ
      (∀ {f : Fn} (_hf : f ∈ mod.fns),
        InlOutSpec T M.host lt mod Γ f.name f (M.bound f.name) nX) :=
  fun hacyc hwf hsupp hwp {_f} hf =>
    M.fnSpec_optInlinePolicy mod policy hfs M.host Γ 0 M.code_infix_host M.labelsUnique hacyc hwf
      hsupp hwp (fun _ h => nomatch h) ⟨(fun _ h => nomatch h), (fun _ h => nomatch h)⟩
      (fun _ hg => M.defined_exit_host hg) hf

/-- `Module.optInlinePolicy` empty-extern, empty-exit `FnSpec` wrapper over any host `h`. -/
theorem fnSpec_noExit_id_optInlinePolicy (M : Compiled T lt [] [] nX fs hints maxBound)
    (mod : Module) (policy : InlinePolicy) (hfs : (mod.optInlinePolicy policy).fns = fs)
    (h : T.mach.Host) (Γ : Env) (k₀ : Nat)
    (hc : M.code.IsInfixAt (T.mach.prog h) k₀) (hu : T.LabelsUnique h) :
    InlModHyps lt mod (mod.optInlinePolicy policy) Γ
      (∀ {f : Fn} (_hf : f ∈ mod.fns)
        (_has : lt.legalSig f.as = f.as) (_hrs : lt.legalSig f.rs = f.rs)
        (_hnoex : ∀ args m Q X X', Γ f.name f.as f.rs args m Q X → Γ f.name f.as f.rs args m Q X'),
        T.Defined h f.name ∧ T.FnSpec h f.name (Γ f.name f.as f.rs) (M.bound f.name) nX) := by
  intro hacyc hwf hsupp hwp f hf has hrs hnoex
  obtain ⟨hdef, hspec⟩ := M.fnSpec_optInlinePolicy mod policy hfs h Γ k₀ hc hu hacyc hwf hsupp hwp
    (fun _ h => nomatch h) ⟨(fun _ h => nomatch h), (fun _ h => nomatch h)⟩
    (fun _ h => nomatch h) hf
  exact ⟨hdef, fnSpec_of_legalEnv_legalSig_eq_noExit has hrs
    (List.mem_append_left _ (List.mem_map_of_mem hf)) hnoex hspec⟩

/-- `Compiled` linking theorem after verified `Module.optInline maxSize`, proving source
`mod : Module` specifications over any host containing `M.code`. -/
theorem fnSpec_optInline (M : Compiled T lt extCallees exits nX fs hints maxBound)
    (mod : Module) (maxSize : Nat) (hfs : (mod.optInline maxSize).fns = fs)
    (h : T.mach.Host) (Γ : Env) (k₀ : Nat)
    (hc : M.code.IsInfixAt (T.mach.prog h) k₀) (hu : T.LabelsUnique h) :
    InlModHyps lt mod (mod.optInline maxSize) Γ
      (InlExtHyps T h lt mod Γ extCallees exits nX
        (∀ {f : Fn} (_hf : f ∈ mod.fns),
          InlOutSpec T h lt mod Γ f.name f (M.bound f.name) nX)) :=
  fun hacyc hwf hsupp hwp hext hext_uniq hexits {_f} hf =>
    M.fnSpec_optInlinePolicy mod (InlinePolicy.const maxSize) hfs h Γ k₀ hc hu hacyc hwf hsupp hwp
      hext hext_uniq hexits hf

/-- `Module.optInline` specialization of `fnSpec_host` for `M.host` when `extCallees = []`. -/
theorem fnSpec_host_optInline (M : Compiled T lt [] exits nX fs hints maxBound)
    (mod : Module) (maxSize : Nat) (hfs : (mod.optInline maxSize).fns = fs) (Γ : Env) :
    InlModHyps lt mod (mod.optInline maxSize) Γ
      (∀ {f : Fn} (_hf : f ∈ mod.fns),
        InlOutSpec T M.host lt mod Γ f.name f (M.bound f.name) nX) :=
  fun hacyc hwf hsupp hwp {_f} hf =>
    M.fnSpec_host_optInlinePolicy mod (InlinePolicy.const maxSize) hfs Γ hacyc hwf hsupp hwp hf

/-- `Module.optInline` empty-extern, empty-exit `FnSpec` wrapper over any host `h`. -/
theorem fnSpec_noExit_id_optInline (M : Compiled T lt [] [] nX fs hints maxBound)
    (mod : Module) (maxSize : Nat) (hfs : (mod.optInline maxSize).fns = fs)
    (h : T.mach.Host) (Γ : Env) (k₀ : Nat)
    (hc : M.code.IsInfixAt (T.mach.prog h) k₀) (hu : T.LabelsUnique h) :
    InlModHyps lt mod (mod.optInline maxSize) Γ
      (∀ {f : Fn} (_hf : f ∈ mod.fns)
        (_has : lt.legalSig f.as = f.as) (_hrs : lt.legalSig f.rs = f.rs)
        (_hnoex : ∀ args m Q X X', Γ f.name f.as f.rs args m Q X → Γ f.name f.as f.rs args m Q X'),
        T.Defined h f.name ∧ T.FnSpec h f.name (Γ f.name f.as f.rs) (M.bound f.name) nX) :=
  fun hacyc hwf hsupp hwp {_f} hf has hrs hnoex =>
    M.fnSpec_noExit_id_optInlinePolicy mod (InlinePolicy.const maxSize) hfs h Γ k₀ hc hu hacyc hwf
      hsupp hwp hf has hrs hnoex

end Compiled

end LeanQbe.T
