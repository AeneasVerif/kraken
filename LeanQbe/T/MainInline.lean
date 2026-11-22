module

public import LeanQbe.T.MainLemmas
import LeanQbe.T.OptLemmas

/-!
# Verified `Module.optInline` Compilation Bridge (`C3`)

Standalone wrappers and end-to-end soundness theorems composing `Module.optInline`
(`Module.inline` + `Fn.renorm`) with `compile`, `compileModule`, `compile_sound`, and `Compiled`,
exposing source-module hypotheses and source-level specifications without modifying `Main.lean`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

/-- Run acyclic policy-driven inlining on `M` and renormalize every function body. -/
def Module.optInlinePolicy (M : Module) (policy : InlinePolicy := {}) : Module :=
  let M' := M.inlinePolicy policy
  { M' with fns := M'.fns.map Fn.renorm }

theorem Module.optInline_eq_optInlinePolicy (M : Module) (maxSize : Nat := 40) :
    M.optInline maxSize = M.optInlinePolicy (InlinePolicy.const maxSize) :=
  rfl

/-- Compile a module after verified policy-driven inlining and AST renormalization
(`Module.optInlinePolicy policy`), using externally supplied hints for
`(M.optInlinePolicy policy).fns`. -/
def compileOptInlinePolicy (I : Isa) (lt : LegalTarget) (M : Module) (hints : List I.Hints)
    (policy : InlinePolicy := {}) : Except String (List I.Directive) :=
  compile I lt (M.optInlinePolicy policy).fns hints

/-- Stack-checked module compilation after verified `Module.optInlinePolicy policy`. -/
def compileModuleOptInlinePolicy (I : Isa) (lt : LegalTarget) (raBytes : Nat)
    (extCallees : List (SigEntry × Nat)) (exits : List Sym) (nX : Nat)
    (M : Module) (hints : List I.Hints) (policy : InlinePolicy := {}) :
    Except String (List I.Directive × List (Sym × Nat)) :=
  compileModule I lt raBytes extCallees exits nX (M.optInlinePolicy policy).fns hints

/-- Compile a module after verified acyclic small-callee inlining and AST renormalization
(`Module.optInline maxSize`), using externally supplied hints for `(M.optInline maxSize).fns`. -/
def compileOptInline (I : Isa) (lt : LegalTarget) (M : Module) (hints : List I.Hints)
    (maxSize : Nat := 40) : Except String (List I.Directive) :=
  compile I lt (M.optInline maxSize).fns hints

/-- Stack-checked module compilation after verified `Module.optInline maxSize`. -/
def compileModuleOptInline (I : Isa) (lt : LegalTarget) (raBytes : Nat)
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

private theorem checkFnsCallsOk_of_forall_inline (exits : List Sym) (extSigs : List SigEntry) :
    ∀ (seenSigs : List SigEntry) (rest : List Fn),
    (∀ pre fn post, rest = pre ++ fn :: post →
      fn.callsOk ((seenSigs ++ pre.map Fn.sig) ++ extSigs) exits) →
    Module.checkFnsCallsOk exits extSigs seenSigs rest = true
  | _, [], _ => rfl
  | seenSigs, fn :: rest, h => by
      have hhd := h [] fn rest rfl
      simp only [List.map_nil, List.append_nil] at hhd
      have htl := checkFnsCallsOk_of_forall_inline exits extSigs (seenSigs ++ [fn.sig]) rest
        fun pre f post hsp => by
          simpa [List.append_assoc] using h (fn :: pre) f post (by simp [hsp])
      simp only [Module.checkFnsCallsOk, Bool.and_eq_true]
      exact ⟨Expr.checkCallsOk_of_callsOk _ hhd, htl⟩

private theorem checkAcyclic_of_moduleOk {Γ : Env} {M : Module} (hM : ModuleOk Γ M) :
    M.checkAcyclic = true := by
  simp only [Module.checkAcyclic, Bool.and_eq_true]
  refine ⟨listNodup_iff.mpr hM.nodup,
    checkFnsCallsOk_of_forall_inline _ _ [] _ fun pre fn post hsp => ?_⟩
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

/-- `Module.optInlinePolicy` preserves `Fn.Wf` for every function in an acyclic module. -/
theorem Module.optInlinePolicy_wf {M : Module} (policy : InlinePolicy := {})
    (hchk : M.checkAcyclic = true) (hwf : ∀ f ∈ M.fns, f.Wf) :
    ∀ f ∈ (M.optInlinePolicy policy).fns, f.Wf := by
  have hm := optInlinePolicy_moduleOk_bot policy hchk hwf
  intro f hf
  obtain ⟨pre, post, hsp⟩ := List.mem_iff_append.mp hf
  exact (hm.fnsOk pre f post hsp).1

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

/-- End-to-end compilation soundness after verified `Module.optInlinePolicy policy`, exposing
source module hypotheses `M` and source-level specifications under `Env.ofModule M Γ`. -/
theorem compile_sound_optInlinePolicy (T : Target) (host : T.mach.Host) (lt : LegalTarget)
    (M : Module) (Γ : Env) (extCallees : List (SigEntry × Nat)) (exits : List Sym)
    (nX : Nat) (policy : InlinePolicy) (hints : List T.toIsa.Hints) (code : List T.Directive)
    (bounds : List (Sym × Nat)) (k₀ : Nat)
    (hcm : compileModuleOptInlinePolicy T.toIsa lt T.frame.raBytes extCallees exits nX M hints
        policy = .ok (code, bounds))
    (hc : code.IsInfixAt (T.mach.prog host) k₀) (hu : T.LabelsUnique host)
    (hacyc : M.checkAcyclic = true) (hwf : ∀ f ∈ M.fns, f.Wf)
    (hsupp : ∀ f ∈ (M.optInlinePolicy policy).fns, (f.earlyOpt).body.supportsSource lt = true)
    (hwp : ∀ f ∈ M.fns, ∀ xs m Q X,
      Γ f.name f.as f.rs xs m Q X → Func.wp Γ f.body xs m Q X)
    (hext : ∀ p ∈ extCallees,
      T.FnSpec host p.1.1 (legalEnv lt (Env.ofModule M Γ) p.1.1 p.1.2.1 p.1.2.2) p.2 nX)
    (hext_uniq : (∀ p ∈ extCallees, ∀ q ∈ extCallees, p.1.1 = q.1.1 → p.2 = q.2) ∧
      (∀ p ∈ extCallees, p.1.1 ∉ M.fns.map Fn.name))
    (hexits : ∀ g ∈ exits, T.Defined host g) :
    ∀ p ∈ bounds, ∃ f ∈ M.fns, p.1 = f.name ∧ T.Defined host p.1 ∧
      T.FnSpec host p.1
        (legalEnv lt (Env.ofModule M Γ) p.1 (lt.legalSig f.as) (lt.legalSig f.rs))
        p.2 nX := by
  obtain ⟨hacyc', hwf', hwp', hnames, hsigs⟩ :=
    optInlinePolicy_compile_hyps policy hacyc hwf hwp
  intro p hp
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
theorem optInlinePolicy_sound (T : Target) (host : T.mach.Host) (lt : LegalTarget)
    (M : Module) (Γ : Env) (extCallees : List (SigEntry × Nat)) (exits : List Sym)
    (nX : Nat) (policy : InlinePolicy) (hints : List T.toIsa.Hints) (code : List T.Directive)
    (bounds : List (Sym × Nat)) (k₀ : Nat)
    (hcm : compileModuleOptInlinePolicy T.toIsa lt T.frame.raBytes extCallees exits nX M hints
        policy = .ok (code, bounds))
    (hc : code.IsInfixAt (T.mach.prog host) k₀) (hu : T.LabelsUnique host)
    (hacyc : M.checkAcyclic = true) (hwf : ∀ f ∈ M.fns, f.Wf)
    (hsupp : ∀ f ∈ (M.optInlinePolicy policy).fns, (f.earlyOpt).body.supportsSource lt = true)
    (hwp : ∀ f ∈ M.fns, ∀ xs m Q X,
      Γ f.name f.as f.rs xs m Q X → Func.wp Γ f.body xs m Q X)
    (hext : ∀ p ∈ extCallees,
      T.FnSpec host p.1.1 (legalEnv lt (Env.ofModule M Γ) p.1.1 p.1.2.1 p.1.2.2) p.2 nX)
    (hext_uniq : (∀ p ∈ extCallees, ∀ q ∈ extCallees, p.1.1 = q.1.1 → p.2 = q.2) ∧
      (∀ p ∈ extCallees, p.1.1 ∉ M.fns.map Fn.name))
    (hexits : ∀ g ∈ exits, T.Defined host g) :
    ∀ p ∈ bounds, ∃ f ∈ M.fns, p.1 = f.name ∧ T.Defined host p.1 ∧
      T.FnSpec host p.1
        (legalEnv lt (Env.ofModule M Γ) p.1 (lt.legalSig f.as) (lt.legalSig f.rs))
        p.2 nX :=
  compile_sound_optInlinePolicy T host lt M Γ extCallees exits nX policy hints code bounds k₀
    hcm hc hu hacyc hwf hsupp hwp hext hext_uniq hexits

/-- End-to-end compilation soundness after verified `Module.optInline maxSize`, exposing source
module hypotheses `M` and source-level specifications under `Env.ofModule M Γ`. -/
theorem compile_sound_optInline (T : Target) (host : T.mach.Host) (lt : LegalTarget)
    (M : Module) (Γ : Env) (extCallees : List (SigEntry × Nat)) (exits : List Sym)
    (nX maxSize : Nat) (hints : List T.toIsa.Hints) (code : List T.Directive)
    (bounds : List (Sym × Nat)) (k₀ : Nat)
    (hcm : compileModuleOptInline T.toIsa lt T.frame.raBytes extCallees exits nX M hints
        maxSize = .ok (code, bounds))
    (hc : code.IsInfixAt (T.mach.prog host) k₀) (hu : T.LabelsUnique host)
    (hacyc : M.checkAcyclic = true) (hwf : ∀ f ∈ M.fns, f.Wf)
    (hsupp : ∀ f ∈ (M.optInline maxSize).fns, (f.earlyOpt).body.supportsSource lt = true)
    (hwp : ∀ f ∈ M.fns, ∀ xs m Q X,
      Γ f.name f.as f.rs xs m Q X → Func.wp Γ f.body xs m Q X)
    (hext : ∀ p ∈ extCallees,
      T.FnSpec host p.1.1 (legalEnv lt (Env.ofModule M Γ) p.1.1 p.1.2.1 p.1.2.2) p.2 nX)
    (hext_uniq : (∀ p ∈ extCallees, ∀ q ∈ extCallees, p.1.1 = q.1.1 → p.2 = q.2) ∧
      (∀ p ∈ extCallees, p.1.1 ∉ M.fns.map Fn.name))
    (hexits : ∀ g ∈ exits, T.Defined host g) :
    ∀ p ∈ bounds, ∃ f ∈ M.fns, p.1 = f.name ∧ T.Defined host p.1 ∧
      T.FnSpec host p.1
        (legalEnv lt (Env.ofModule M Γ) p.1 (lt.legalSig f.as) (lt.legalSig f.rs))
        p.2 nX :=
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
    (hc : M.code.IsInfixAt (T.mach.prog h) k₀) (hu : T.LabelsUnique h)
    (hacyc : mod.checkAcyclic = true) (hwf : ∀ f ∈ mod.fns, f.Wf)
    (hsupp : ∀ f ∈ (mod.optInlinePolicy policy).fns, (f.earlyOpt).body.supportsSource lt = true)
    (hwp : ∀ f ∈ mod.fns, ∀ xs m Q X,
      Γ f.name f.as f.rs xs m Q X → Func.wp Γ f.body xs m Q X)
    (hext : ∀ p ∈ extCallees,
      T.FnSpec h p.1.1 (legalEnv lt (Env.ofModule mod Γ) p.1.1 p.1.2.1 p.1.2.2) p.2 nX)
    (hext_uniq : (∀ p ∈ extCallees, ∀ q ∈ extCallees, p.1.1 = q.1.1 → p.2 = q.2) ∧
      (∀ p ∈ extCallees, p.1.1 ∉ mod.fns.map Fn.name))
    (hexits : ∀ g ∈ exits, T.Defined h g) {f : Fn} (hf : f ∈ mod.fns) :
    T.Defined h f.name ∧ T.FnSpec h f.name
      (legalEnv lt (Env.ofModule mod Γ) f.name (lt.legalSig f.as) (lt.legalSig f.rs))
      (M.bound f.name) nX := by
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
    (Γ : Env) (hacyc : mod.checkAcyclic = true) (hwf : ∀ f ∈ mod.fns, f.Wf)
    (hsupp : ∀ f ∈ (mod.optInlinePolicy policy).fns, (f.earlyOpt).body.supportsSource lt = true)
    (hwp : ∀ f ∈ mod.fns, ∀ xs m Q X,
      Γ f.name f.as f.rs xs m Q X → Func.wp Γ f.body xs m Q X)
    {f : Fn} (hf : f ∈ mod.fns) :
    T.Defined M.host f.name ∧ T.FnSpec M.host f.name
      (legalEnv lt (Env.ofModule mod Γ) f.name (lt.legalSig f.as) (lt.legalSig f.rs))
      (M.bound f.name) nX :=
  M.fnSpec_optInlinePolicy mod policy hfs M.host Γ 0 M.code_infix_host M.labelsUnique hacyc hwf
    hsupp hwp (fun _ h => nomatch h) ⟨(fun _ h => nomatch h), (fun _ h => nomatch h)⟩
    (fun _ hg => M.defined_exit_host hg) hf

/-- `Module.optInlinePolicy` empty-extern, empty-exit `FnSpec` wrapper over any host `h`. -/
theorem fnSpec_noExit_id_optInlinePolicy (M : Compiled T lt [] [] nX fs hints maxBound)
    (mod : Module) (policy : InlinePolicy) (hfs : (mod.optInlinePolicy policy).fns = fs)
    (h : T.mach.Host) (Γ : Env) (k₀ : Nat)
    (hc : M.code.IsInfixAt (T.mach.prog h) k₀) (hu : T.LabelsUnique h)
    (hacyc : mod.checkAcyclic = true) (hwf : ∀ f ∈ mod.fns, f.Wf)
    (hsupp : ∀ f ∈ (mod.optInlinePolicy policy).fns, (f.earlyOpt).body.supportsSource lt = true)
    (hwp : ∀ f ∈ mod.fns, ∀ xs m Q X,
      Γ f.name f.as f.rs xs m Q X → Func.wp Γ f.body xs m Q X)
    {f : Fn} (hf : f ∈ mod.fns) (has : lt.legalSig f.as = f.as) (hrs : lt.legalSig f.rs = f.rs)
    (hnoex : ∀ args m Q X X', Γ f.name f.as f.rs args m Q X → Γ f.name f.as f.rs args m Q X') :
    T.Defined h f.name ∧ T.FnSpec h f.name (Γ f.name f.as f.rs) (M.bound f.name) nX := by
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
    (hc : M.code.IsInfixAt (T.mach.prog h) k₀) (hu : T.LabelsUnique h)
    (hacyc : mod.checkAcyclic = true) (hwf : ∀ f ∈ mod.fns, f.Wf)
    (hsupp : ∀ f ∈ (mod.optInline maxSize).fns, (f.earlyOpt).body.supportsSource lt = true)
    (hwp : ∀ f ∈ mod.fns, ∀ xs m Q X,
      Γ f.name f.as f.rs xs m Q X → Func.wp Γ f.body xs m Q X)
    (hext : ∀ p ∈ extCallees,
      T.FnSpec h p.1.1 (legalEnv lt (Env.ofModule mod Γ) p.1.1 p.1.2.1 p.1.2.2) p.2 nX)
    (hext_uniq : (∀ p ∈ extCallees, ∀ q ∈ extCallees, p.1.1 = q.1.1 → p.2 = q.2) ∧
      (∀ p ∈ extCallees, p.1.1 ∉ mod.fns.map Fn.name))
    (hexits : ∀ g ∈ exits, T.Defined h g) {f : Fn} (hf : f ∈ mod.fns) :
    T.Defined h f.name ∧ T.FnSpec h f.name
      (legalEnv lt (Env.ofModule mod Γ) f.name (lt.legalSig f.as) (lt.legalSig f.rs))
      (M.bound f.name) nX :=
  M.fnSpec_optInlinePolicy mod (InlinePolicy.const maxSize) hfs h Γ k₀ hc hu hacyc hwf hsupp hwp
    hext hext_uniq hexits hf

/-- `Module.optInline` specialization of `fnSpec_host` for `M.host` when `extCallees = []`. -/
theorem fnSpec_host_optInline (M : Compiled T lt [] exits nX fs hints maxBound)
    (mod : Module) (maxSize : Nat) (hfs : (mod.optInline maxSize).fns = fs) (Γ : Env)
    (hacyc : mod.checkAcyclic = true) (hwf : ∀ f ∈ mod.fns, f.Wf)
    (hsupp : ∀ f ∈ (mod.optInline maxSize).fns, (f.earlyOpt).body.supportsSource lt = true)
    (hwp : ∀ f ∈ mod.fns, ∀ xs m Q X,
      Γ f.name f.as f.rs xs m Q X → Func.wp Γ f.body xs m Q X)
    {f : Fn} (hf : f ∈ mod.fns) :
    T.Defined M.host f.name ∧ T.FnSpec M.host f.name
      (legalEnv lt (Env.ofModule mod Γ) f.name (lt.legalSig f.as) (lt.legalSig f.rs))
      (M.bound f.name) nX :=
  M.fnSpec_host_optInlinePolicy mod (InlinePolicy.const maxSize) hfs Γ hacyc hwf hsupp hwp hf

/-- `Module.optInline` empty-extern, empty-exit `FnSpec` wrapper over any host `h`. -/
theorem fnSpec_noExit_id_optInline (M : Compiled T lt [] [] nX fs hints maxBound)
    (mod : Module) (maxSize : Nat) (hfs : (mod.optInline maxSize).fns = fs)
    (h : T.mach.Host) (Γ : Env) (k₀ : Nat)
    (hc : M.code.IsInfixAt (T.mach.prog h) k₀) (hu : T.LabelsUnique h)
    (hacyc : mod.checkAcyclic = true) (hwf : ∀ f ∈ mod.fns, f.Wf)
    (hsupp : ∀ f ∈ (mod.optInline maxSize).fns, (f.earlyOpt).body.supportsSource lt = true)
    (hwp : ∀ f ∈ mod.fns, ∀ xs m Q X,
      Γ f.name f.as f.rs xs m Q X → Func.wp Γ f.body xs m Q X)
    {f : Fn} (hf : f ∈ mod.fns) (has : lt.legalSig f.as = f.as) (hrs : lt.legalSig f.rs = f.rs)
    (hnoex : ∀ args m Q X X', Γ f.name f.as f.rs args m Q X → Γ f.name f.as f.rs args m Q X') :
    T.Defined h f.name ∧ T.FnSpec h f.name (Γ f.name f.as f.rs) (M.bound f.name) nX :=
  M.fnSpec_noExit_id_optInlinePolicy mod (InlinePolicy.const maxSize) hfs h Γ k₀ hc hu hacyc hwf
    hsupp hwp hf has hrs hnoex

end Compiled

end LeanQbe.T
