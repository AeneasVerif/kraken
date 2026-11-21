module

public import LeanQbe.T.MainLemmas

/-!
# Verified `Module.optInline` Compilation Bridge (`C3`)

Standalone wrappers and end-to-end soundness theorems composing `Module.optInline`
(`Module.inline` + `Fn.renorm`) with `compile`, `compileModule`, `compile_sound`, and `Compiled`,
exposing source-module hypotheses and source-level specifications without modifying `Main.lean`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

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

theorem Module.optInline_sigs (M : Module) (maxSize : Nat) :
    (M.optInline maxSize).sigs = M.sigs := by
  rw [← Module.inline_sigs M maxSize]
  simp [Module.optInline, Module.sigs, Fn.renorm, Fn.sig, List.map_map, Function.comp_def]

theorem Module.optInline_names (M : Module) (maxSize : Nat) :
    (M.optInline maxSize).names = M.names := by
  rw [← Module.inline_names M maxSize]
  simp [Module.optInline, Module.names, Fn.renorm, List.map_map, Function.comp_def]

theorem Module.optInline_namesNodup (M : Module) (maxSize : Nat) :
    (M.optInline maxSize).namesNodup ↔ M.namesNodup := by
  simp only [Module.namesNodup, Module.optInline_names]

theorem Module.optInline_externs (M : Module) (maxSize : Nat) :
    (M.optInline maxSize).externs = M.externs :=
  rfl

theorem Module.optInline_exits (M : Module) (maxSize : Nat) :
    (M.optInline maxSize).exits = M.exits :=
  rfl

theorem Env.ofModule_optInline (M : Module) (Γ : Env) (maxSize : Nat) :
    Env.ofModule (M.optInline maxSize) Γ = Env.ofModule M Γ := by
  simp [Env.ofModule, Module.optInline_sigs]

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

private theorem optInline_moduleOk_bot {M : Module} (maxSize : Nat)
    (hchk : M.checkAcyclic = true) (hwf : ∀ f ∈ M.fns, f.Wf) :
    ModuleOk (fun _ _ _ _ _ _ _ => False) (M.optInline maxSize) :=
  Module.optInline_ok maxSize
    (Module.moduleOk_of_checkAcyclic (Γ := fun _ _ _ _ _ _ _ => False) hchk hwf
      (fun _ _ _ _ _ _ => False.elim))

/-- `Module.optInline` preserves `Module.checkAcyclic` when all source functions are `Wf`. -/
theorem Module.optInline_checkAcyclic {M : Module} (maxSize : Nat)
    (hchk : M.checkAcyclic = true) (hwf : ∀ f ∈ M.fns, f.Wf) :
    (M.optInline maxSize).checkAcyclic = true :=
  checkAcyclic_of_moduleOk (optInline_moduleOk_bot maxSize hchk hwf)

/-- `Module.optInline` preserves `Fn.Wf` for every function in an acyclic module. -/
theorem Module.optInline_wf {M : Module} (maxSize : Nat)
    (hchk : M.checkAcyclic = true) (hwf : ∀ f ∈ M.fns, f.Wf) :
    ∀ f ∈ (M.optInline maxSize).fns, f.Wf := by
  have hm := optInline_moduleOk_bot maxSize hchk hwf
  intro f hf
  obtain ⟨pre, post, hsp⟩ := List.mem_iff_append.mp hf
  exact (hm.fnsOk pre f post hsp).1

private theorem optInline_compile_hyps {M : Module} {Γ : Env} (maxSize : Nat)
    (hacyc : M.checkAcyclic = true) (hwf : ∀ f ∈ M.fns, f.Wf)
    (hwp : ∀ f ∈ M.fns, ∀ xs m Q X, Γ f.name f.as f.rs xs m Q X → Func.wp Γ f.body xs m Q X) :
    (M.optInline maxSize).checkAcyclic = true ∧
    (∀ f ∈ (M.optInline maxSize).fns, f.Wf) ∧
    (∀ f ∈ (M.optInline maxSize).fns, ∀ xs m Q X,
      Γ f.name f.as f.rs xs m Q X → Func.wp Γ f.body xs m Q X) ∧
    (M.optInline maxSize).fns.map Fn.name = M.fns.map Fn.name ∧
    (M.optInline maxSize).fns.map Fn.sig = M.fns.map Fn.sig := by
  have hm' := Module.optInline_ok maxSize (Module.moduleOk_of_checkAcyclic hacyc hwf hwp)
  refine ⟨checkAcyclic_of_moduleOk hm', fun f hf => ?_, fun f hf => ?_, ?_, ?_⟩
  · obtain ⟨pre, post, hsp⟩ := List.mem_iff_append.mp hf
    exact (hm'.fnsOk pre f post hsp).1
  · obtain ⟨pre, post, hsp⟩ := List.mem_iff_append.mp hf
    exact (hm'.fnsOk pre f post hsp).2.2
  · have h := Module.optInline_names M maxSize
    simp only [Module.names, Module.optInline_externs] at h
    exact List.append_cancel_right h
  · have h := Module.optInline_sigs M maxSize
    simp only [Module.sigs, Module.optInline_externs] at h
    exact List.append_cancel_right h

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
        p.2 nX := by
  obtain ⟨hacyc', hwf', hwp', hnames, hsigs⟩ := optInline_compile_hyps maxSize hacyc hwf hwp
  intro p hp
  obtain ⟨f', hf', hnm, hdef, hspec⟩ :=
    compile_sound T host lt (M.optInline maxSize) Γ extCallees exits nX hints code bounds k₀
      hcm hc hu hacyc' hwf' hsupp hwp' (by simpa [Env.ofModule_optInline] using hext)
      ⟨hext_uniq.1, by simpa [hnames] using hext_uniq.2⟩ hexits p hp
  have hsigMem : f'.sig ∈ M.fns.map Fn.sig := hsigs ▸ List.mem_map_of_mem hf'
  obtain ⟨f, hf, hsigEq⟩ := List.mem_map.mp hsigMem
  simp only [Fn.sig, Prod.mk.injEq] at hsigEq
  rcases hsigEq with ⟨hfnm, hfas, hfrs⟩
  refine ⟨f, hf, hnm.trans hfnm.symm, hdef, ?_⟩
  rw [Env.ofModule_optInline, ← hfas, ← hfrs] at hspec
  exact hspec

namespace Compiled

variable {T : Target} {lt : LegalTarget} {extCallees : List (SigEntry × Nat)}
  {exits : List Sym} {nX : Nat} {fs : List Fn} {hints : List T.toIsa.Hints} {maxBound : Nat}

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
      (M.bound f.name) nX := by
  obtain ⟨hacyc', hwf', hwp', hnames, hsigs⟩ := optInline_compile_hyps maxSize hacyc hwf hwp
  have hsigMem : f.sig ∈ (mod.optInline maxSize).fns.map Fn.sig := by
    rw [hsigs]; exact List.mem_map_of_mem hf
  obtain ⟨f', hf', hsigEq⟩ := List.mem_map.mp hsigMem
  simp only [Fn.sig, Prod.mk.injEq] at hsigEq
  rcases hsigEq with ⟨hfnm, hfas, hfrs⟩
  obtain ⟨hdef, hspec⟩ := M.fnSpec (mod.optInline maxSize) hfs h Γ k₀ hc hu
    hacyc' hwf' hsupp hwp' (by simpa [Env.ofModule_optInline] using hext)
    ⟨hext_uniq.1, by simpa [hnames] using hext_uniq.2⟩ hexits hf'
  rw [hfnm] at hdef hspec
  rw [hfas, hfrs, Env.ofModule_optInline] at hspec
  exact ⟨hdef, hspec⟩

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
  M.fnSpec_optInline mod maxSize hfs M.host Γ 0 M.code_infix_host M.labelsUnique hacyc hwf
    hsupp hwp (fun _ h => nomatch h) ⟨(fun _ h => nomatch h), (fun _ h => nomatch h)⟩
    (fun _ hg => M.defined_exit_host hg) hf

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
    T.Defined h f.name ∧ T.FnSpec h f.name (Γ f.name f.as f.rs) (M.bound f.name) nX := by
  obtain ⟨hdef, hspec⟩ := M.fnSpec_optInline mod maxSize hfs h Γ k₀ hc hu hacyc hwf hsupp hwp
    (fun _ h => nomatch h) ⟨(fun _ h => nomatch h), (fun _ h => nomatch h)⟩
    (fun _ h => nomatch h) hf
  exact ⟨hdef, fnSpec_of_legalEnv_legalSig_eq_noExit has hrs
    (List.mem_append_left _ (List.mem_map_of_mem hf)) hnoex hspec⟩

end Compiled

end LeanQbe.T
