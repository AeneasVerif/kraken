module

public import LeanQbe.T.OptLemmas
public import LeanQbe.T.LicmLemmas
public import LeanQbe.T.DceParamLemmas
public import LeanQbe.T.SimplifyGroupPlanLemmas
public import LeanQbe.T.LegalLemmas
public import LeanQbe.T.LegalCheck3
public import LeanQbe.T.RegaLemmas4
public import LeanQbe.T.AbiLemmas
public import LeanQbe.T.MainLemmas
public import LeanQbe.T.MainLink
public import LeanQbe.T.LinkRecLemmas
public import LeanQbe.T.SccLemmas
public import LeanQbe.T.LinkSccLemmas2
public import LeanQbe.T.LinkLfp
public import LeanQbe.T.Examples.LinkRec
meta import LeanQbe.T.Module
meta import LeanQbe.T.LinkRec
meta import LeanQbe.T.Examples.LinkRec

/-!
# Target-Independent Compiler, Multi-Chunk Linker, & Cyclic Recursion Audit

Self-contained correctness audit for the architecture-independent `LeanQbe.T` compiler pipeline,
compositional multi-chunk linker (`MainLink`), and measure-indexed cyclic/mutual-recursion
linking (`LinkRec`).

## What This Workstream Proves
1. **Mid-end optimization (`OptLemmas`, `LicmLemmas`, `DceParamLemmas`,
   `SimplifyGroupPlanLemmas`)**: `Func.earlyOpt`, `Func.lateOpt`, legacy `Func.opt`,
   `Func.licm`, `Func.dceP`, `Func.simplifyGroupPlan`, and acyclic inlining + renormalization
   (`Module.optInline`) preserve `Func.Wf`, refine `Func.spec`, and preserve `ModuleOk`.
2. **Type and opcode legalization (`LegalLemmas`, `LegalCheck3`)**: `Func.legal` / `Fn.legal`
   refine `Func.spec` into `legalEnv` / `legalPost` / `legalXPost` and guarantee target legality
   (`isLegal target = true`).
3. **Register allocation and lowering (`RegaLemmas4`)**: `Rega.lowerFn` translates any well-formed
   function into a machine-level `Target.FnSpec` over any abstract `Target` and host containing
   the emitted directives with unique labels.
4. **End-to-end compilation (`MainLemmas`)**: `compileFn_correct` and `compile_sound` compose
   `earlyOpt -> legal -> lateOpt -> Rega.lowerFn` across single functions and acyclic modules
   checked by `M.checkAcyclic = true`.
5. **Compositional O(N) multi-chunk linking (`MainLink`)**: `compileModule_append`,
   `linkCompiled_fnSpec`, and `linkCompiledList_fnSpec` stitch separately compiled `Compiled`
   chunks into a single linked host without re-running the compiler.
6. **Cyclic and mutual recursion (`LinkRecLemmas`, `Examples.LinkRec`)**: measure/fuel-indexed
   `ModuleRecOk`, `Env.sound_rec`, `Env.sound_rec_unfold`, `compileRec_sound`, and
   `link_rec_compiled` verify cyclic call graphs (`isEven`/`isOdd`, fuel-guarded `recSum` with
   `"out_of_fuel"` exit) up to a statically checked stack budget `baseBound + k * stepBound`.

## Inputs / Assumptions
* Source functions satisfy PHOAS well-formedness (`f.Wf`), source-support checks
  (`(f.earlyOpt).body.supportsSource lt = true`), and module call-graph checks (`checkAcyclic` or
  `checkCyclic`).
* Concrete machine targets supply verified `GprTarget`, `VecTarget`, `FrameTarget`, and
  `Rega.LabelClean` instances (audited separately in `CompilerAuditX64.lean` and
  `CompilerAuditArm64.lean`).

## Trusted Computing Base (TCB)
* Lean 4 kernel and its standard logical foundations (`propext`, `Classical.choice`, `Quot.sound`).
* Typed-IR weakest-precondition semantics (`LeanQbe.T.Semantics.wp`) and abstract `Target.FnSpec`
  machine interface (`LeanQbe.T.Abi`).
* Untrusted external register-allocation hint heuristics are **outside** the TCB: all hints are
  validated by the verified `Rega.lowerFn` checker inside Lean.
-/

set_option autoImplicit false

@[expose] public section

namespace CompilerAuditSpec

open LeanQbe.T
open LeanQbe.T.LinkRec

/-! ## 1. Mid-End Optimization & Inlining -/

theorem audit_early_opt {as rs : List Ty} {f : Func as rs} (hf : f.Wf) {Γ : Env}
    {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Func.spec Γ f xs m Q X) :
    Func.spec Γ (Func.earlyOpt f) xs m Q X :=
  Func.earlyOpt_spec hf h

theorem audit_late_opt {as rs : List Ty} {f : Func as rs} (hf : f.Wf) {Γ : Env}
    {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Func.spec Γ f xs m Q X) :
    Func.spec Γ (Func.lateOpt f) xs m Q X :=
  Func.lateOpt_spec hf h

theorem audit_opt_inline {Γ : Env} {M : Module} (maxSize : Nat := 40)
    (hM : ModuleOk Γ M) :
    ModuleOk Γ (M.optInline maxSize) :=
  Module.optInline_ok maxSize hM

theorem audit_licm_wf {as rs : List Ty} {f : Func as rs} (hf : f.Wf) :
    (Func.licm f).Wf :=
  Func.licm_wf hf

theorem audit_licm_spec {as rs : List Ty} {f : Func as rs} (hf : f.Wf) {Γ : Env}
    {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Func.spec Γ f xs m Q X) :
    Func.spec Γ (Func.licm f) xs m Q X :=
  Func.licm_spec hf h

theorem audit_licm_src (target : LegalTarget) {as rs : List Ty} {f : Func as rs}
    (hf : f.Wf) (hsupp : f.supportsSource target = true) :
    (Func.licm f).supportsSource target = true :=
  Func.licm_supportsSource target hf hsupp

theorem audit_dceP_wf {as rs : List Ty} {f : Func as rs} (hf : f.Wf) (rounds : Nat := 0) :
    (Func.dceP f rounds).Wf :=
  Func.dceP_wf hf rounds

theorem audit_dceP_spec {as rs : List Ty} {f : Func as rs} (hf : f.Wf) {Γ : Env}
    {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Func.spec Γ f xs m Q X) (rounds : Nat := 0) :
    Func.spec Γ (Func.dceP f rounds) xs m Q X :=
  Func.dceP_spec hf h rounds

theorem audit_dcePWith_spec (dl dld : Bool) (rounds : Nat := 0)
    {as rs : List Ty} {f : Func as rs} (hf : f.Wf) {Γ : Env}
    {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Func.spec Γ f xs m Q X) :
    Func.spec Γ (Func.dcePWith dl dld rounds f) xs m Q X :=
  Func.dcePWith_spec dl dld rounds hf h

theorem audit_sgp_wf {as rs : List Ty} {f : Func as rs} (hf : f.Wf) :
    (Func.simplifyGroupPlan f).Wf :=
  Func.simplifyGroupPlan_wf hf

theorem audit_sgp_spec {as rs : List Ty} {f : Func as rs} (hf : f.Wf) {Γ : Env}
    {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Func.spec Γ f xs m Q X) :
    Func.spec Γ (Func.simplifyGroupPlan f) xs m Q X :=
  Func.simplifyGroupPlan_spec hf h

theorem audit_sgp_plan_spec {as rs : List Ty} (plan : SgpImpl.SimpPlan)
    {f : Func as rs} (hf : f.Wf) {Γ : Env}
    {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Func.spec Γ f xs m Q X) :
    Func.spec Γ (Func.simplifyGroupWithPlan plan f) xs m Q X :=
  Func.simplifyGroupWithPlan_spec plan hf h

/-! ## 2. Legalization Correctness & Target Legality -/

theorem audit_legal_spec (target : LegalTarget) {as rs : List Ty} (f : Func as rs)
    (hf : f.Wf) (hsupp : f.supportsSource target = true)
    (Γ : Env) (xs : Tup Val as) (m : Mem 64) (Q : Post rs) (X : XPost)
    (h : Func.spec Γ f xs m Q X) :
    Func.spec (legalEnv target Γ) (f.legal target) (encodeTup target as xs) m
      (legalPost target Q) (legalXPost target X) :=
  Func.legal_spec target f hf hsupp Γ xs m Q X h

theorem audit_legal_ok (target : LegalTarget) {as rs : List Ty} (f : Func as rs)
    (hf : f.Wf) (hsupp : f.supportsSource target = true) :
    (f.legal target).isLegal target = true :=
  Func.legal_isLegal target f hf hsupp

/-! ## 3. Register Allocation Lowering & ABI Composition -/

theorem audit_lower_fn (T : Target) (host : T.mach.Host) (hints : T.toIsa.Hints)
    (E : Rega.Ext) (f : Fn) (Γ : Env) (n nX : Nat) (bound : Sym → Nat)
    {code : List T.Directive} {k₀ : Nat}
    (hwf : f.Wf) (hl : Rega.lowerFn T.toIsa hints E f = .ok code)
    (hc : code.IsInfixAt (T.mach.prog host) k₀) (hu : T.LabelsUnique host)
    (hfr : Rega.frame T hints ≤ n) (hn : n + T.frame.raBytes ≤ 2 ^ 64)
    (hcal : ∀ g as bs, (g, as, bs) ∈ E.callees →
      T.FnSpec host g (Γ g as bs) (bound g) nX ∧
      Rega.frame T hints + T.frame.raBytes + bound g ≤ n)
    (hex : ∀ g, g ∈ E.exits → T.Defined host g ∧ nX ≤ n) :
    T.FnSpec host f.name (Func.spec Γ f.body) n nX :=
  Rega.lowerFn_correct T host hints E f Γ n nX bound hwf hl hc hu hfr hn hcal hex

theorem audit_mono_stack (T : Target) {h : T.mach.Host} {sym : Sym} {as bs : List Ty}
    {spec : Spec as bs} {n n' nX : Nat}
    (hf : T.FnSpec h sym spec n nX) (hn : n ≤ n') (hn' : n' + T.frame.raBytes ≤ 2 ^ 64) :
    T.FnSpec h sym spec n' nX :=
  Target.FnSpec.mono_stack T hf hn hn'

theorem audit_abi_link (T : Target) {h : T.mach.Host} (Γ : Env)
    (sig : Sym → List Ty × List Ty) (bound : Sym → Nat) (nX : Nat) (fs : List Sym)
    (hstep : ∀ (pre : List Sym) (f : Sym) (post : List Sym), fs = pre ++ f :: post →
      (∀ g, g ∈ pre → T.FnSpec h g (Γ g (sig g).1 (sig g).2) (bound g) nX) →
      T.FnSpec h f (Γ f (sig f).1 (sig f).2) (bound f) nX) :
    ∀ f, f ∈ fs → T.FnSpec h f (Γ f (sig f).1 (sig f).2) (bound f) nX :=
  Target.link T Γ sig bound nX fs hstep

/-! ## 4. End-to-End Function & Acyclic Module Compilation -/

theorem audit_compile_fn (T : Target) (host : T.mach.Host) (lt : LegalTarget)
    (M : Module) (hnd : M.namesNodup) {f : Fn} (hf : f ∈ M.fns)
    (hints : T.toIsa.Hints) (Γ : Env) (n nX : Nat) (bound : Sym → Nat)
    {code : List T.Directive} {k₀ : Nat}
    (hwf : f.Wf) (hsupp : (f.earlyOpt).body.supportsSource lt = true)
    (hl : compileFn T.toIsa lt hints f = .ok code)
    (hc : code.IsInfixAt (T.mach.prog host) k₀) (hu : T.LabelsUnique host)
    (hfr : Rega.frame T hints ≤ n) (hn : n + T.frame.raBytes ≤ 2 ^ 64)
    (hsound : ∀ xs m P E',
      Env.ofModule M Γ f.name f.as f.rs xs m P E' →
      Func.wp (Env.ofModule M Γ) f.body xs m P E')
    (hcal : ∀ g as bs, (g, as, bs) ∈ (f.mid lt).ext.callees →
      T.FnSpec host g (legalEnv lt (Env.ofModule M Γ) g as bs) (bound g) nX ∧
      Rega.frame T hints + T.frame.raBytes + bound g ≤ n)
    (hex : ∀ g, g ∈ (f.mid lt).ext.exits → T.Defined host g ∧ nX ≤ n) :
    T.FnSpec host f.name
      (legalEnv lt (Env.ofModule M Γ) f.name (lt.legalSig f.as) (lt.legalSig f.rs)) n nX :=
  compileFn_correct T host lt M hnd hf hints Γ n nX bound
    hwf hsupp hl hc hu hfr hn hsound hcal hex

theorem audit_compile_mod (T : Target) (host : T.mach.Host) (lt : LegalTarget)
    (M : Module) (Γ : Env) (extCallees : List (SigEntry × Nat)) (exits : List Sym) (nX : Nat)
    (hints : List T.toIsa.Hints) (code : List T.Directive) (bounds : List (Sym × Nat))
    (k₀ : Nat)
    (hcm : compileModule T.toIsa lt T.frame.raBytes extCallees exits nX M.fns hints =
      .ok (code, bounds))
    (hc : code.IsInfixAt (T.mach.prog host) k₀) (hu : T.LabelsUnique host)
    (hacyc : M.checkAcyclic = true) (hwf : ∀ f ∈ M.fns, f.Wf)
    (hsupp : ∀ f ∈ M.fns, (f.earlyOpt).body.supportsSource lt = true)
    (hwp : ∀ f ∈ M.fns, ∀ xs m Q X, Γ f.name f.as f.rs xs m Q X → Func.wp Γ f.body xs m Q X)
    (hext : ∀ p ∈ extCallees,
      T.FnSpec host p.1.1 (legalEnv lt (Env.ofModule M Γ) p.1.1 p.1.2.1 p.1.2.2) p.2 nX)
    (hext_uniq : (∀ p ∈ extCallees, ∀ q ∈ extCallees, p.1.1 = q.1.1 → p.2 = q.2) ∧
      (∀ p ∈ extCallees, p.1.1 ∉ M.fns.map Fn.name))
    (hexits : ∀ g ∈ exits, T.Defined host g) :
    ∀ p ∈ bounds, ∃ f ∈ M.fns, p.1 = f.name ∧ T.Defined host p.1 ∧
      T.FnSpec host p.1
        (legalEnv lt (Env.ofModule M Γ) p.1 (lt.legalSig f.as) (lt.legalSig f.rs)) p.2 nX :=
  compile_sound T host lt M Γ extCallees exits nX hints code bounds k₀
    hcm hc hu hacyc hwf hsupp hwp hext hext_uniq hexits

/-! ## 5. Compositional Multi-Chunk Linker (`MainLink`) -/

theorem audit_mod_append {I : Isa} {lt : LegalTarget} {raBytes : Nat}
    {exits : List Sym} {nX : Nat}
    {ext₀ ext₂ : List (SigEntry × Nat)} {fs₁ : List Fn} {hints₁ : List I.Hints}
    {fs₂ : List Fn} {hints₂ : List I.Hints} {code₁ code₂ : List I.Directive}
    {bounds₁ bounds₂ : List (Sym × Nat)}
    (h₁ : compileModule I lt raBytes ext₀ exits nX fs₁ hints₁ = .ok (code₁, bounds₁))
    (h₂ : compileModule I lt raBytes ext₂ exits nX fs₂ hints₂ = .ok (code₂, bounds₂))
    (hnd : (fs₁.map Fn.name).Nodup)
    (hsig : ∀ g bg, lookupBound ext₂ g = some bg →
      lookupBound (sigBoundsOf lt fs₁ bounds₁ ++ ext₀) g = some bg) :
    compileModule I lt raBytes ext₀ exits nX (fs₁ ++ fs₂) (hints₁ ++ hints₂) =
      .ok (code₁ ++ code₂, bounds₁ ++ bounds₂) :=
  compileModule_append h₁ h₂ hnd hsig

theorem audit_link_two {T : Target} {L : TargetLayout T} {lt : LegalTarget}
    (hcl : Rega.LabelClean T.toIsa)
    {ext₀ : List (SigEntry × Nat)} {exits : List Sym} {nX : Nat}
    {fs₁ : List Fn} {hints₁ : List T.toIsa.Hints} {maxB₁ : Nat}
    {fs₂ : List Fn} {hints₂ : List T.toIsa.Hints} {maxB₂ : Nat}
    (M₁ : Compiled T lt ext₀ exits nX fs₁ hints₁ maxB₁)
    (M₂ : Compiled T lt (M₁.sigBounds ++ ext₀) exits nX fs₂ hints₂ maxB₂)
    (hchk : checkLink L M₁ M₂ = true)
    (mod : Module) (hfs : mod.fns = fs₁ ++ fs₂) (Γ : Env)
    (hacyc : mod.checkAcyclic = true) (hwf : ∀ f ∈ mod.fns, f.Wf)
    (hsupp : ∀ f ∈ mod.fns, (f.earlyOpt).body.supportsSource lt = true)
    (hwp : ∀ f ∈ mod.fns, ∀ xs m Q X,
      Γ f.name f.as f.rs xs m Q X → Func.wp Γ f.body xs m Q X)
    (hext : ∀ p ∈ ext₀,
      T.FnSpec (linkCompiled L hcl M₁ M₂ hchk).host p.1.1
        (legalEnv lt (Env.ofModule mod Γ) p.1.1 p.1.2.1 p.1.2.2) p.2 nX)
    (hext_uniq : (∀ p ∈ ext₀, ∀ q ∈ ext₀, p.1.1 = q.1.1 → p.2 = q.2) ∧
      (∀ p ∈ ext₀, p.1.1 ∉ mod.fns.map Fn.name))
    {f : Fn} (hf : f ∈ mod.fns) :
    T.Defined (linkCompiled L hcl M₁ M₂ hchk).host f.name ∧
      T.FnSpec (linkCompiled L hcl M₁ M₂ hchk).host f.name
        (legalEnv lt (Env.ofModule mod Γ) f.name (lt.legalSig f.as) (lt.legalSig f.rs))
        ((linkCompiled L hcl M₁ M₂ hchk).bound f.name) nX :=
  linkCompiled_fnSpec hcl M₁ M₂ hchk mod hfs Γ hacyc hwf hsupp hwp hext hext_uniq hf

theorem audit_link_list {T : Target} {L : TargetLayout T} {lt : LegalTarget}
    (hcl : Rega.LabelClean T.toIsa) {exits : List Sym} {nX : Nat}
    (ext₀ : List (SigEntry × Nat)) (chunks : List (CompiledChunk T lt exits nX))
    (hchk : checkLinkList L ext₀ chunks = true)
    (mod : Module) (hfs : mod.fns = chunksFns chunks) (Γ : Env)
    (hacyc : mod.checkAcyclic = true) (hwf : ∀ f ∈ mod.fns, f.Wf)
    (hsupp : ∀ f ∈ mod.fns, (f.earlyOpt).body.supportsSource lt = true)
    (hwp : ∀ f ∈ mod.fns, ∀ xs m Q X,
      Γ f.name f.as f.rs xs m Q X → Func.wp Γ f.body xs m Q X)
    (hext : ∀ p ∈ ext₀,
      T.FnSpec (linkCompiledList L hcl ext₀ chunks hchk).host p.1.1
        (legalEnv lt (Env.ofModule mod Γ) p.1.1 p.1.2.1 p.1.2.2) p.2 nX)
    (hext_uniq : (∀ p ∈ ext₀, ∀ q ∈ ext₀, p.1.1 = q.1.1 → p.2 = q.2) ∧
      (∀ p ∈ ext₀, p.1.1 ∉ mod.fns.map Fn.name))
    {f : Fn} (hf : f ∈ mod.fns) :
    T.Defined (linkCompiledList L hcl ext₀ chunks hchk).host f.name ∧
      T.FnSpec (linkCompiledList L hcl ext₀ chunks hchk).host f.name
        (legalEnv lt (Env.ofModule mod Γ) f.name (lt.legalSig f.as) (lt.legalSig f.rs))
        ((linkCompiledList L hcl ext₀ chunks hchk).bound f.name) nX :=
  linkCompiledList_fnSpec hcl ext₀ chunks hchk mod hfs Γ hacyc hwf hsupp hwp hext hext_uniq hf

/-! ## 6. Cyclic & Mutual Recursion (`LinkRec`) -/

theorem audit_rec_sound {Γrec : Nat → Env} {Γext : Env} {M : Module}
    (hM : ModuleRecOk Γrec Γext M) :
    ∀ (fn : Fn), fn ∈ M.fns → ∀ xs m Q X,
      Env.ofModuleRec M Γrec Γext fn.name fn.as fn.rs xs m Q X →
      Func.wp (Env.ofModuleRec M Γrec Γext) fn.body xs m Q X :=
  Env.sound_rec hM

theorem audit_rec_unfold {Γrec : Nat → Env} {Γext : Env} {M : Module}
    (hM : ModuleRecOk Γrec Γext M) :
    ∀ (k : Nat) (fn : Fn), fn ∈ M.fns → ∀ xs m Q X,
      Γrec k fn.name fn.as fn.rs xs m Q X →
      Env.unfoldRecAt M Γext k fn.name fn.as fn.rs xs m Q X :=
  Env.sound_rec_unfold hM

theorem audit_compile_rec (T : Target) (host : T.mach.Host) (lt : LegalTarget)
    (mod : Module) (Γrec : Nat → Env) (Γext : Env)
    (extCallees : List (SigEntry × Nat)) (exits : List Sym) (nX fuel maxBound : Nat)
    (hints : List T.toIsa.Hints) (code : List T.Directive) (baseBound stepBound k₀ : Nat)
    (hcm : compileModuleRec T.toIsa lt T.frame.raBytes extCallees exits nX fuel maxBound
      mod.fns hints = .ok (code, baseBound, stepBound))
    (hc : code.IsInfixAt (T.mach.prog host) k₀) (hu : T.LabelsUnique host)
    (hcyc : checkCyclic mod = true) (hwf : ∀ f ∈ mod.fns, f.Wf)
    (hsupp : ∀ f ∈ mod.fns, (f.earlyOpt).body.supportsSource lt = true)
    (hrec : ∀ k ≤ fuel, ∀ f ∈ mod.fns, ∀ xs m Q X,
      Γrec k f.name f.as f.rs xs m Q X →
      Func.wp (Env.stepRec (mod.fns.map Fn.sig) (mod.externs.map Extern.sig) Γrec Γext k)
        f.body xs m Q X)
    (hext : ∀ p ∈ extCallees,
      T.FnSpec host p.1.1
        (legalEnv lt (Env.restrict Γext (mod.externs.map Extern.sig)) p.1.1 p.1.2.1 p.1.2.2)
        p.2 nX)
    (hext_uniq : ∀ p ∈ extCallees, ∀ q ∈ extCallees, p.1.1 = q.1.1 → p.2 = q.2)
    (hexits : ∀ g ∈ exits, T.Defined host g) :
    ∀ k ≤ fuel, ∀ f ∈ mod.fns, T.Defined host f.name ∧
      T.FnSpec host f.name
        (legalEnv lt (Env.onlyFn f (Γrec k)) f.name (lt.legalSig f.as) (lt.legalSig f.rs))
        (baseBound + k * stepBound) nX :=
  compileRec_sound T host lt mod Γrec Γext extCallees exits nX fuel maxBound hints
    code baseBound stepBound k₀ hcm hc hu hcyc hwf hsupp hrec hext hext_uniq hexits

theorem audit_link_rec {T : Target} {lt : LegalTarget}
    {extCallees : List (SigEntry × Nat)} {exits : List Sym} {nX fuel : Nat}
    {fs : List Fn} {hints : List T.toIsa.Hints} {maxBound : Nat}
    (M : CompiledRec T lt extCallees exits nX fuel fs hints maxBound)
    (mod : Module) (hfs : mod.fns = fs) (h : T.mach.Host)
    (Γrec : Nat → Env) (Γext : Env) (k₀ : Nat)
    (hc : M.code.IsInfixAt (T.mach.prog h) k₀) (hu : T.LabelsUnique h)
    (hcyc : checkCyclic mod = true) (hwf : ∀ f ∈ mod.fns, f.Wf)
    (hsupp : ∀ f ∈ mod.fns, (f.earlyOpt).body.supportsSource lt = true)
    (hrec : ∀ k ≤ fuel, ∀ f ∈ mod.fns, ∀ xs m Q X,
      Γrec k f.name f.as f.rs xs m Q X →
      Func.wp (Env.stepRec (mod.fns.map Fn.sig) (mod.externs.map Extern.sig) Γrec Γext k)
        f.body xs m Q X)
    (hext : ∀ p ∈ extCallees,
      T.FnSpec h p.1.1
        (legalEnv lt (Env.restrict Γext (mod.externs.map Extern.sig)) p.1.1 p.1.2.1 p.1.2.2)
        p.2 nX)
    (hext_uniq : ∀ p ∈ extCallees, ∀ q ∈ extCallees, p.1.1 = q.1.1 → p.2 = q.2)
    (hexits : ∀ g ∈ exits, T.Defined h g) :
    ∀ k ≤ fuel, ∀ f ∈ mod.fns, T.Defined h f.name ∧
      T.FnSpec h f.name
        (legalEnv lt (Env.onlyFn f (Γrec k)) f.name (lt.legalSig f.as) (lt.legalSig f.rs))
        (M.boundAt k) nX :=
  link_rec_compiled M mod hfs h Γrec Γext k₀ hc hu hcyc hwf hsupp hrec hext hext_uniq hexits

theorem audit_even_odd_ok :
    ModuleRecOk evenOddRecEnv (fun _ _ _ _ _ _ _ => False) evenOddRecMod :=
  evenOddRecMod_moduleRecOk

theorem audit_rec_sum_ok :
    ModuleRecOk recSumRecEnv (fun _ _ _ _ _ _ _ => False) recSumMod :=
  recSumMod_moduleRecOk

/-! ## 7. Well-Founded SCC & LFP Linking (`SccLemmas`, `LinkSccLemmas2`, `LinkLfp`) -/

section SccLfpAudit

open LeanQbe.T
open LeanQbe.T.LinkRec
open LeanQbe.T.LinkScc

theorem audit_scc_order_sound {sccs : List (List Fn)} {extSigs : List SigEntry}
    {exits : List Sym} (h : checkSccOrder sccs extSigs exits = true) :
    (sccs.flatten.map Fn.name ++ extSigs.map Prod.fst).Nodup ∧
    ∀ (pre : List (List Fn)) (scc : List Fn) (post : List (List Fn)),
      sccs = pre ++ scc :: post →
      !scc.isEmpty = true ∧
      ∀ fn ∈ scc,
        fn.callsOk (pre.flatten.map Fn.sig ++ scc.map Fn.sig ++ extSigs) exits :=
  checkSccOrder_sound h

theorem audit_scc_acyclic {M : Module} (h : M.checkAcyclic = true) :
    checkSccOrder (M.fns.map fun f => [f]) (M.externs.map Extern.sig) M.exits = true :=
  checkSccOrder_of_acyclic h

theorem audit_link_scc {ι : Type} (idx : RecIdx ι) {T : Target} {lt : LegalTarget}
    {extCallees : List (SigEntry × Nat)} {exits : List Sym} {nX fuel : Nat}
    {fs : List Fn} {hints : List T.toIsa.Hints} {maxBound : Nat}
    (M : CompiledRec T lt extCallees exits nX fuel fs hints maxBound)
    (mod : Module) (hfs : mod.fns = fs) (h : T.mach.Host)
    (Γrec : ι → Env) (Γext : Env) (k₀ : Nat)
    (hc : M.code.IsInfixAt (T.mach.prog h) k₀) (hu : T.LabelsUnique h)
    (hM : ModuleSccOk idx Γrec Γext (M.stepBound != 0) mod)
    (hsupp : ∀ f ∈ mod.fns, (f.earlyOpt).body.supportsSource lt = true)
    (hext : ∀ p ∈ extCallees,
      T.FnSpec h p.1.1
        (legalEnv lt (Env.restrict Γext (mod.externs.map Extern.sig)) p.1.1 p.1.2.1 p.1.2.2)
        p.2 nX)
    (hext_uniq : ∀ p ∈ extCallees, ∀ q ∈ extCallees, p.1.1 = q.1.1 → p.2 = q.2)
    (hexits : ∀ g ∈ exits, T.Defined h g) (i : ι)
    (hbound : M.baseBound + idx.depth i * M.stepBound ≤ maxBound)
    (hra : M.baseBound + idx.depth i * M.stepBound + T.frame.raBytes ≤ 2 ^ 64) :
    ∀ f ∈ mod.fns, T.Defined h f.name ∧
      T.FnSpec h f.name
        (legalEnv lt (Env.onlyFn f (Γrec i)) f.name (lt.legalSig f.as) (lt.legalSig f.rs))
        (M.baseBound + idx.depth i * M.stepBound) nX :=
  link_scc_compiled idx M mod hfs h Γrec Γext k₀ hc hu hM hsupp hext hext_uniq hexits i hbound hra

theorem audit_scc_export_host {ι : Type} (idx : RecIdx ι) {T : Target} {lt : LegalTarget}
    {exits : List Sym} {nX fuel : Nat} {fs : List Fn} {hints : List T.toIsa.Hints}
    {maxBound : Nat}
    (M : CompiledRec T lt [] exits nX fuel fs hints maxBound)
    (mod : Module) (hfs : mod.fns = fs) (Γrec : ι → Env) (Γext : Env)
    (hM : ModuleSccOk idx Γrec Γext (M.stepBound != 0) mod)
    (hsupp : ∀ f ∈ mod.fns, (f.earlyOpt).body.supportsSource lt = true) :
    ∀ f ∈ mod.fns, T.Defined M.host f.name ∧
      T.FnSpec M.host f.name
        (legalEnv lt (Env.onlyFn f (Env.exportScc idx Γrec fuel)) f.name
          (lt.legalSig f.as) (lt.legalSig f.rs))
        (M.baseBound + fuel * M.stepBound) nX :=
  link_scc_export_host idx M mod hfs Γrec Γext hM hsupp

theorem audit_link_rec_of_scc {T : Target} {lt : LegalTarget}
    {extCallees : List (SigEntry × Nat)} {exits : List Sym} {nX fuel : Nat}
    {fs : List Fn} {hints : List T.toIsa.Hints} {maxBound : Nat}
    (M : CompiledRec T lt extCallees exits nX fuel fs hints maxBound)
    (mod : Module) (hfs : mod.fns = fs) (h : T.mach.Host)
    (Γrec : Nat → Env) (Γext : Env) (k₀ : Nat)
    (hc : M.code.IsInfixAt (T.mach.prog h) k₀) (hu : T.LabelsUnique h)
    (hcyc : checkCyclic mod = true) (hwf : ∀ f ∈ mod.fns, f.Wf)
    (hsupp : ∀ f ∈ mod.fns, (f.earlyOpt).body.supportsSource lt = true)
    (hrec : ∀ k ≤ fuel, ∀ f ∈ mod.fns, ∀ xs m Q X,
      Γrec k f.name f.as f.rs xs m Q X →
      Func.wp (Env.stepRec (mod.fns.map Fn.sig) (mod.externs.map Extern.sig) Γrec Γext k)
        f.body xs m Q X)
    (hext : ∀ p ∈ extCallees,
      T.FnSpec h p.1.1
        (legalEnv lt (Env.restrict Γext (mod.externs.map Extern.sig)) p.1.1 p.1.2.1 p.1.2.2)
        p.2 nX)
    (hext_uniq : ∀ p ∈ extCallees, ∀ q ∈ extCallees, p.1.1 = q.1.1 → p.2 = q.2)
    (hexits : ∀ g ∈ exits, T.Defined h g) :
    ∀ k ≤ fuel, ∀ f ∈ mod.fns, T.Defined h f.name ∧
      T.FnSpec h f.name
        (legalEnv lt (Env.onlyFn f (Γrec k)) f.name (lt.legalSig f.as) (lt.legalSig f.rs))
        (M.boundAt k) nX :=
  link_rec_of_scc M mod hfs h Γrec Γext k₀ hc hu hcyc hwf hsupp hrec hext hext_uniq hexits

theorem audit_scc_le_sem {ι : Type} {idx : RecIdx ι} {Γrec : ι → Env} {Γext : Env}
    {M : Module} (hM : ModuleSccOk idx Γrec Γext false M) :
    ∀ i, Env.le (Env.restrict (Γrec i) (M.fns.map Fn.sig)) (Env.semScc M Γext) :=
  moduleSccOk_le_semScc hM

theorem audit_scc_le_unfold {ι : Type} {idx : RecIdx ι} {Γrec : ι → Env} {Γext : Env}
    {M : Module} (hM : ModuleSccOk idx Γrec Γext true M) :
    ∀ i, Env.le (Env.restrict (Γrec i) (M.fns.map Fn.sig))
      (Env.unfoldRecAt M Γext (idx.depth i)) :=
  moduleSccOk_le_unfoldRecAt hM

theorem audit_link_scc_static {T : Target} {lt : LegalTarget}
    {extCallees : List (SigEntry × Nat)} {exits : List Sym} {nX fuel : Nat}
    {fs : List Fn} {hints : List T.toIsa.Hints} {maxBound : Nat}
    (M : CompiledRec T lt extCallees exits nX fuel fs hints maxBound)
    (mod : Module) (hfs : mod.fns = fs) (h : T.mach.Host)
    (Γext : Env) (k₀ : Nat)
    (hc : M.code.IsInfixAt (T.mach.prog h) k₀) (hu : T.LabelsUnique h)
    (hcyc : checkCyclic mod = true) (hwf : ∀ f ∈ mod.fns, f.Wf)
    (hsupp : ∀ f ∈ mod.fns, (f.earlyOpt).body.supportsSource lt = true)
    (hext : ∀ p ∈ extCallees,
      T.FnSpec h p.1.1
        (legalEnv lt (Env.restrict Γext (mod.externs.map Extern.sig)) p.1.1 p.1.2.1 p.1.2.2)
        p.2 nX)
    (hext_uniq : ∀ p ∈ extCallees, ∀ q ∈ extCallees, p.1.1 = q.1.1 → p.2 = q.2)
    (hexits : ∀ g ∈ exits, T.Defined h g) :
    ∀ d ≤ fuel, ∀ f ∈ mod.fns, T.Defined h f.name ∧
      T.FnSpec h f.name
        (legalEnv lt (Env.onlyFn f (Env.unfoldRecAt mod Γext d)) f.name
          (lt.legalSig f.as) (lt.legalSig f.rs))
        (M.baseBound + d * M.stepBound) nX :=
  link_scc_static M mod hfs h Γext k₀ hc hu hcyc hwf hsupp hext hext_uniq hexits

end SccLfpAudit

/-! ## 8. Concrete Sanity Checks (`#guard`) -/

#guard evenOddRecMod.checkAcyclic == false
#guard recSumMod.checkAcyclic == false
#guard checkCyclic evenOddRecMod == true
#guard checkCyclic recSumMod == true
#guard isEvenVal 4#64 == 1#64
#guard isOddVal 5#64 == 1#64
#guard recSumOutcome 3#64 5 == .inl 6#64
#guard recSumOutcome 5#64 2 == .inr 3#64

/-! ## 9. Logical Foundations Audit (`#print axioms`) -/

#print axioms audit_early_opt
#print axioms audit_late_opt
#print axioms audit_opt_inline
#print axioms audit_licm_wf
#print axioms audit_licm_spec
#print axioms audit_licm_src
#print axioms audit_dceP_wf
#print axioms audit_dceP_spec
#print axioms audit_dcePWith_spec
#print axioms audit_sgp_wf
#print axioms audit_sgp_spec
#print axioms audit_sgp_plan_spec
#print axioms audit_legal_spec
#print axioms audit_legal_ok
#print axioms audit_lower_fn
#print axioms audit_mono_stack
#print axioms audit_abi_link
#print axioms audit_compile_fn
#print axioms audit_compile_mod
#print axioms audit_mod_append
#print axioms audit_link_two
#print axioms audit_link_list
#print axioms audit_rec_sound
#print axioms audit_rec_unfold
#print axioms audit_compile_rec
#print axioms audit_link_rec
#print axioms audit_even_odd_ok
#print axioms audit_rec_sum_ok
#print axioms audit_scc_order_sound
#print axioms audit_scc_acyclic
#print axioms audit_link_scc
#print axioms audit_scc_export_host
#print axioms audit_link_rec_of_scc
#print axioms audit_scc_le_sem
#print axioms audit_scc_le_unfold
#print axioms audit_link_scc_static

end CompilerAuditSpec
