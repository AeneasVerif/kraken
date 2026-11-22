module

public import LeanQbe.T.MainCertProof
public import LeanQbe.T.MainInline
import LeanQbe.T.InlineLemmas
public meta import Lean
public meta import LeanQbe.T.MainInline
public meta import LeanQbe.T.MainCertElab
public meta import LeanQbe.T.MainLinkSplice

/-!
# Certified Inlined Compilation Bridge & `inline_mod!` Materializer (`MainCertInline`)

Bridges `MainInline.lean` (`Module.optInlinePolicy` / `Module.optInline`) directly to
`LinkedCert` (`MainCertCore` / `MainCertProof`):
* `LinkedCert.castFns`, `LinkedCert.castModule` (`LinkedCert.of_eq`): O(1) certificate
  transport across `mod₁.fns = mod₂.fns` / `mod₁ = mod₂` without re-checking any chunk.
* `LinkedCert.fnSpec_optInlinePolicy`, `LinkedCert.fnSpec_host_optInlinePolicy`,
  `LinkedCert.fnSpec_host_src_optInlinePolicy`,
  `LinkedCert.fnSpec_host_of_legalSigAll_optInlinePolicy`,
  `LinkedCert.fnSpec_noExit_id_optInlinePolicy`,
  `LinkedCert.fnSpec_noExit_of_legalSigAll_optInlinePolicy`,
  plus `optInline maxSize` convenience corollaries and `TargetInit` `Eventually` lifts
  (`eventually_fnSpec_optInlinePolicy`, `eventually_ret1_sep_i64_optInlinePolicy`,
  `eventually_ret1_i64_optInlinePolicy`, etc.).
* `inline_mod! <inlModName> <srcMod> <policy>`: evaluates `srcMod.optInlinePolicy policy` once
  in MetaM, emits `<inlModName> : Module` as a literal `denoteFunc`-backed `Module` (zero
  nested PHOAS closures or `inlinePolicy` overhead in downstream `compile_linked_chunks!` slices),
  and emits `<inlModName>.eq : <inlModName> = srcMod.optInlinePolicy policy` and
  `<inlModName>.fns_eq` once via `addKernelEqThm`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T

/-- Extract acyclicity, well-formedness, and `Func.wp` obligations from `ModuleOk Γ mod`. -/
theorem moduleOk_parts {Γ : Env} {mod : Module} (hM : ModuleOk Γ mod) :
    mod.checkAcyclic = true ∧
    (∀ f ∈ mod.fns, f.Wf) ∧
    (∀ f ∈ mod.fns, ∀ xs m Q X, Γ f.name f.as f.rs xs m Q X → Func.wp Γ f.body xs m Q X) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [Module.checkAcyclic, Bool.and_eq_true]
    exact ⟨listNodup_iff.mpr hM.nodup,
      checkFnsCallsOk_of_forall _ _ [] _ fun pre fn post hsp => by
        simpa using (hM.fnsOk pre fn post hsp).2.1⟩
  · intro f hf
    obtain ⟨pre, post, hsp⟩ := List.mem_iff_append.mp hf
    exact (hM.fnsOk pre f post hsp).1
  · intro f hf
    obtain ⟨pre, post, hsp⟩ := List.mem_iff_append.mp hf
    exact (hM.fnsOk pre f post hsp).2.2

namespace LinkedCert

variable {T : Target} {L : TargetLayout T} {lt : LegalTarget}
  {hcl : Rega.LabelClean T.toIsa} {mod mod₁ mod₂ : Module} {policy : InlinePolicy}
  {ext₀ : List (SigEntry × Nat)} {exits : List Sym} {nX maxBound : Nat}

/-- Transport a `LinkedCert` along `mod₁.fns = mod₂.fns` while keeping `chunks`, `compiled`,
`host`, `code`, `bounds`, and `bound` definitionally identical. -/
@[expose] noncomputable def castFns
    (cert : LinkedCert T L lt hcl mod₁ ext₀ exits nX maxBound)
    (h : mod₁.fns = mod₂.fns) :
    LinkedCert T L lt hcl mod₂ ext₀ exits nX maxBound where
  chunks := cert.chunks
  linkCheck := cert.linkCheck
  fns_eq := h.symm.trans cert.fns_eq
  supportsAll := fun f hf => cert.supportsAll f (h ▸ hf)
  maxBound_le := cert.maxBound_le

/-- Transport a `LinkedCert` along a module equality `h : mod₁ = mod₂` in O(1) without
re-checking any compiled chunk or link check. -/
@[expose] noncomputable def castModule
    (cert : LinkedCert T L lt hcl mod₁ ext₀ exits nX maxBound)
    (h : mod₁ = mod₂) :
    LinkedCert T L lt hcl mod₂ ext₀ exits nX maxBound :=
  cert.castFns (congrArg Module.fns h)

/-- Alias for `LinkedCert.castModule`. -/
noncomputable abbrev of_eq := @castModule

/-! ### `Module.optInlinePolicy` & `Module.optInline` `FnSpec` lifts -/

/-- Lift a `LinkedCert` over `mod.optInlinePolicy policy` and source `ModuleOk Γ mod` to
`T.Defined ∧ T.FnSpec` over any host `h` containing `cert.code` at `k₀`. -/
theorem fnSpec_optInlinePolicy
    (cert : LinkedCert T L lt hcl (mod.optInlinePolicy policy) ext₀ exits nX maxBound)
    (h : T.mach.Host) (Γ : Env) (k₀ : Nat)
    (hc : cert.code.IsInfixAt (T.mach.prog h) k₀) (hu : T.LabelsUnique h)
    (hM : ModuleOk Γ mod)
    (hext : ∀ p ∈ ext₀,
      T.FnSpec h p.1.1 (legalEnv lt (Env.ofModule mod Γ) p.1.1 p.1.2.1 p.1.2.2) p.2 nX)
    (hext_uniq : (∀ p ∈ ext₀, ∀ q ∈ ext₀, p.1.1 = q.1.1 → p.2 = q.2) ∧
      (∀ p ∈ ext₀, p.1.1 ∉ mod.fns.map Fn.name))
    (hexits : ∀ g ∈ exits, T.Defined h g) {f : Fn} (hf : f ∈ mod.fns) :
    T.Defined h f.name ∧ T.FnSpec h f.name
      (legalEnv lt (Env.ofModule mod Γ) f.name (lt.legalSig f.as) (lt.legalSig f.rs))
      (cert.bound f.name) nX := by
  have ⟨hacyc, hwf, hwp⟩ := moduleOk_parts hM
  exact cert.compiled.fnSpec_optInlinePolicy mod policy cert.fns_eq h Γ k₀ hc hu
    hacyc hwf cert.supportsAll hwp hext hext_uniq hexits hf

/-- Self-contained `Defined` + `FnSpec` on `cert.host` (`ext₀ = []`) for
`mod.optInlinePolicy policy` from source `ModuleOk Γ mod`. -/
theorem fnSpec_host_optInlinePolicy
    (cert : LinkedCert T L lt hcl (mod.optInlinePolicy policy) [] exits nX maxBound)
    (Γ : Env) (hM : ModuleOk Γ mod) {f : Fn} (hf : f ∈ mod.fns) :
    T.Defined cert.host f.name ∧ T.FnSpec cert.host f.name
      (legalEnv lt (Env.ofModule mod Γ) f.name (lt.legalSig f.as) (lt.legalSig f.rs))
      (cert.bound f.name) nX :=
  cert.fnSpec_optInlinePolicy cert.host Γ 0 cert.code_infix_host cert.labelsUnique hM
    (fun _ h => nomatch h) ⟨(fun _ h => nomatch h), (fun _ h => nomatch h)⟩
    (fun _ hg => cert.defined_exit_host hg) hf

/-- Source-level `Defined` + `FnSpec` on `cert.host` (`ext₀ = []`) for
`mod.optInlinePolicy policy` when `lt.legalSig` fixes `(f.as, f.rs)` and `Γ` ignores exits. -/
theorem fnSpec_host_src_optInlinePolicy
    (cert : LinkedCert T L lt hcl (mod.optInlinePolicy policy) [] exits nX maxBound)
    (Γ : Env) (hM : ModuleOk Γ mod) {f : Fn} (hf : f ∈ mod.fns)
    (has : lt.legalSig f.as = f.as) (hrs : lt.legalSig f.rs = f.rs)
    (hnoex : ∀ args m Q X X', Γ f.name f.as f.rs args m Q X → Γ f.name f.as f.rs args m Q X') :
    T.Defined cert.host f.name ∧
      T.FnSpec cert.host f.name (Γ f.name f.as f.rs) (cert.bound f.name) nX := by
  obtain ⟨hdef, hspec⟩ := cert.fnSpec_host_optInlinePolicy Γ hM hf
  exact ⟨hdef, fnSpec_of_legalEnv_legalSig_eq_noExit has hrs
    (List.mem_append_left _ (List.mem_map_of_mem hf)) hnoex hspec⟩

/-- Source-level `Defined` + `FnSpec` on `cert.host` (`ext₀ = []`) for
`mod.optInlinePolicy policy` given `LegalSigAll lt mod.fns`. -/
theorem fnSpec_host_of_legalSigAll_optInlinePolicy
    (cert : LinkedCert T L lt hcl (mod.optInlinePolicy policy) [] exits nX maxBound)
    (Γ : Env) (hM : ModuleOk Γ mod) (hleg : LegalSigAll lt mod.fns)
    {f : Fn} (hf : f ∈ mod.fns)
    (hnoex : ∀ args m Q X X', Γ f.name f.as f.rs args m Q X → Γ f.name f.as f.rs args m Q X') :
    T.Defined cert.host f.name ∧
      T.FnSpec cert.host f.name (Γ f.name f.as f.rs) (cert.bound f.name) nX :=
  have ⟨has, hrs⟩ := hleg f hf
  cert.fnSpec_host_src_optInlinePolicy Γ hM hf has hrs hnoex

/-- Arbitrary-host `FnSpec` over `mod.optInlinePolicy policy` (`ext₀ = []`, `exits = []`) from
source `ModuleOk Γ mod`. -/
theorem fnSpec_noExit_id_optInlinePolicy
    (cert : LinkedCert T L lt hcl (mod.optInlinePolicy policy) [] [] nX maxBound)
    (h : T.mach.Host) (Γ : Env) (k₀ : Nat)
    (hc : cert.code.IsInfixAt (T.mach.prog h) k₀) (hu : T.LabelsUnique h)
    (hM : ModuleOk Γ mod) {f : Fn} (hf : f ∈ mod.fns)
    (has : lt.legalSig f.as = f.as) (hrs : lt.legalSig f.rs = f.rs)
    (hnoex : ∀ args m Q X X', Γ f.name f.as f.rs args m Q X → Γ f.name f.as f.rs args m Q X') :
    T.Defined h f.name ∧ T.FnSpec h f.name (Γ f.name f.as f.rs) (cert.bound f.name) nX := by
  have ⟨hacyc, hwf, hwp⟩ := moduleOk_parts hM
  exact cert.compiled.fnSpec_noExit_id_optInlinePolicy mod policy cert.fns_eq h Γ k₀ hc hu
    hacyc hwf cert.supportsAll hwp hf has hrs hnoex

/-- Arbitrary-host `fnSpec_noExit_id_optInlinePolicy` specialized with `LegalSigAll lt mod.fns`. -/
theorem fnSpec_noExit_of_legalSigAll_optInlinePolicy
    (cert : LinkedCert T L lt hcl (mod.optInlinePolicy policy) [] [] nX maxBound)
    (h : T.mach.Host) (Γ : Env) (k₀ : Nat)
    (hc : cert.code.IsInfixAt (T.mach.prog h) k₀) (hu : T.LabelsUnique h)
    (hM : ModuleOk Γ mod) (hleg : LegalSigAll lt mod.fns) {f : Fn} (hf : f ∈ mod.fns)
    (hnoex : ∀ args m Q X X', Γ f.name f.as f.rs args m Q X → Γ f.name f.as f.rs args m Q X') :
    T.Defined h f.name ∧ T.FnSpec h f.name (Γ f.name f.as f.rs) (cert.bound f.name) nX :=
  have ⟨has, hrs⟩ := hleg f hf
  cert.fnSpec_noExit_id_optInlinePolicy h Γ k₀ hc hu hM hf has hrs hnoex

/-- `Module.optInline maxSize` convenience specialization of `fnSpec_optInlinePolicy`. -/
theorem fnSpec_optInline {maxSize : Nat}
    (cert : LinkedCert T L lt hcl (mod.optInline maxSize) ext₀ exits nX maxBound)
    (h : T.mach.Host) (Γ : Env) (k₀ : Nat)
    (hc : cert.code.IsInfixAt (T.mach.prog h) k₀) (hu : T.LabelsUnique h)
    (hM : ModuleOk Γ mod)
    (hext : ∀ p ∈ ext₀,
      T.FnSpec h p.1.1 (legalEnv lt (Env.ofModule mod Γ) p.1.1 p.1.2.1 p.1.2.2) p.2 nX)
    (hext_uniq : (∀ p ∈ ext₀, ∀ q ∈ ext₀, p.1.1 = q.1.1 → p.2 = q.2) ∧
      (∀ p ∈ ext₀, p.1.1 ∉ mod.fns.map Fn.name))
    (hexits : ∀ g ∈ exits, T.Defined h g) {f : Fn} (hf : f ∈ mod.fns) :
    T.Defined h f.name ∧ T.FnSpec h f.name
      (legalEnv lt (Env.ofModule mod Γ) f.name (lt.legalSig f.as) (lt.legalSig f.rs))
      (cert.bound f.name) nX :=
  cert.fnSpec_optInlinePolicy h Γ k₀ hc hu hM hext hext_uniq hexits hf

/-- `Module.optInline maxSize` convenience specialization of `fnSpec_host_optInlinePolicy`. -/
theorem fnSpec_host_optInline {maxSize : Nat}
    (cert : LinkedCert T L lt hcl (mod.optInline maxSize) [] exits nX maxBound)
    (Γ : Env) (hM : ModuleOk Γ mod) {f : Fn} (hf : f ∈ mod.fns) :
    T.Defined cert.host f.name ∧ T.FnSpec cert.host f.name
      (legalEnv lt (Env.ofModule mod Γ) f.name (lt.legalSig f.as) (lt.legalSig f.rs))
      (cert.bound f.name) nX :=
  cert.fnSpec_host_optInlinePolicy Γ hM hf

/-- `Module.optInline maxSize` convenience specialization of `fnSpec_noExit_id_optInlinePolicy`. -/
theorem fnSpec_noExit_id_optInline {maxSize : Nat}
    (cert : LinkedCert T L lt hcl (mod.optInline maxSize) [] [] nX maxBound)
    (h : T.mach.Host) (Γ : Env) (k₀ : Nat)
    (hc : cert.code.IsInfixAt (T.mach.prog h) k₀) (hu : T.LabelsUnique h)
    (hM : ModuleOk Γ mod) {f : Fn} (hf : f ∈ mod.fns)
    (has : lt.legalSig f.as = f.as) (hrs : lt.legalSig f.rs = f.rs)
    (hnoex : ∀ args m Q X X', Γ f.name f.as f.rs args m Q X → Γ f.name f.as f.rs args m Q X') :
    T.Defined h f.name ∧ T.FnSpec h f.name (Γ f.name f.as f.rs) (cert.bound f.name) nX :=
  cert.fnSpec_noExit_id_optInlinePolicy h Γ k₀ hc hu hM hf has hrs hnoex

/-- `Module.optInline maxSize` convenience specialization of
`fnSpec_noExit_of_legalSigAll_optInlinePolicy`. -/
theorem fnSpec_noExit_of_legalSigAll_optInline {maxSize : Nat}
    (cert : LinkedCert T L lt hcl (mod.optInline maxSize) [] [] nX maxBound)
    (h : T.mach.Host) (Γ : Env) (k₀ : Nat)
    (hc : cert.code.IsInfixAt (T.mach.prog h) k₀) (hu : T.LabelsUnique h)
    (hM : ModuleOk Γ mod) (hleg : LegalSigAll lt mod.fns) {f : Fn} (hf : f ∈ mod.fns)
    (hnoex : ∀ args m Q X X', Γ f.name f.as f.rs args m Q X → Γ f.name f.as f.rs args m Q X') :
    T.Defined h f.name ∧ T.FnSpec h f.name (Γ f.name f.as f.rs) (cert.bound f.name) nX :=
  cert.fnSpec_noExit_of_legalSigAll_optInlinePolicy h Γ k₀ hc hu hM hleg hf hnoex

/-! ### Concrete `TargetInit` `Eventually` lifts for `optInlinePolicy` / `optInline` -/

section ConcreteInit

variable {maxStack maxMem : Nat}

/-- End-to-end `Eventually` theorem from source `ModuleOk Γ mod` to execution in `cert.host`
of the inlined module `mod.optInlinePolicy policy` (`ext₀ = []`). -/
theorem eventually_fnSpec_optInlinePolicy
    (cert : LinkedCert T L lt hcl (mod.optInlinePolicy policy) [] exits nX maxBound)
    (I : TargetInit T maxStack maxMem) (Γ : Env) (hM : ModuleOk Γ mod)
    {f : Fn} (hf : f ∈ mod.fns) (has : lt.legalSig f.as = f.as) (hrs : lt.legalSig f.rs = f.rs)
    (hnoex : ∀ args m Q X X', Γ f.name f.as f.rs args m Q X → Γ f.name f.as f.rs args m Q X')
    (bsMem : List UInt8) (args : Tup Val f.as) (hbs : bsMem.length ≤ maxMem)
    (hargs : (T.toIsa.assignArgs f.as).isSome = true) {Q : Post f.rs} {X : XPost}
    (hspec : Γ f.name f.as f.rs args (bsMem.At 0x1000#64) Q X) {post : T.mach.State → Prop}
    (hpost : ∀ st,
      (T.mach.pc st = I.ra0 ∧ ∃ rets m', Q rets m' ∧ T.RetsIn rets (T.mach.data st) ∧
        (T.mach.mem (T.mach.data st) =⋆ Eq m' ⋆ T.Exit I.sp0 (cert.bound f.name) ⋆
          Std.ExtHashMap.emp)) ∨
      (∃ (sym' : Sym) (cs : List Ty) (xs : Tup Val cs) (m' : Mem 64), X sym' cs xs m' ∧
        T.mach.pc st = T.mach.labelAddr cert.host sym' ∧ T.ArgsIn xs (T.mach.data st)) → post st)
    (hbound : maxBound ≤ maxStack := by omega) :
    Eventually (T.mach.step cert.host) post
      (T.mach.mkState (I.initState (cert.bound f.name) bsMem args)
        (T.mach.labelAddr cert.host f.name)) :=
  cert.run_fnSpec I (cert.fnSpec_host_src_optInlinePolicy Γ hM hf has hrs hnoex).2
    bsMem args hbs hargs hspec hpost hbound

/-- End-to-end `Eventually` theorem for a non-exiting `i64`-returning `f ∈ mod.fns` on the
inlined `cert.host` establishing final heap postcondition `P`. -/
theorem eventually_ret1_sep_i64_optInlinePolicy
    (cert : LinkedCert T L lt hcl (mod.optInlinePolicy policy) [] exits nX maxBound)
    (I : TargetInit T maxStack maxMem) (Γ : Env) (hM : ModuleOk Γ mod)
    {f : Fn} (hf : f ∈ mod.fns) (hret : f.rs = [i64])
    (has : lt.legalSig f.as = f.as) (hrs : lt.legalSig f.rs = f.rs)
    (hnoex : ∀ args m Q X X', Γ f.name f.as f.rs args m Q X → Γ f.name f.as f.rs args m Q X')
    (bsMem : List UInt8) (args : Tup Val f.as) (v : Val i64) (P : Mem 64 → Prop)
    (hbs : bsMem.length ≤ maxMem) (hargs : (T.toIsa.assignArgs f.as).isSome = true)
    {Q : Post [i64]}
    (hspec : Γ f.name f.as [i64] args (bsMem.At 0x1000#64) Q (fun _ _ _ _ => False))
    (hQ : ∀ rets m', Q rets m' → rets = (v, ()) ∧ P m')
    (hbound : maxBound ≤ maxStack := by omega) :
    Eventually (T.mach.step cert.host)
      (fun st => T.mach.pc st = I.ra0 ∧ T.mach.getGpr (T.mach.data st) I.ret0 = v ∧
        (T.mach.mem (T.mach.data st) =⋆ P ⋆ T.Exit I.sp0 (cert.bound f.name) ⋆ Std.ExtHashMap.emp))
      (T.mach.mkState (I.initState (cert.bound f.name) bsMem args)
        (T.mach.labelAddr cert.host f.name)) := by
  have hfn := (cert.fnSpec_host_src_optInlinePolicy Γ hM hf has hrs hnoex).2
  rw [hret] at hfn
  exact cert.run_ret1_sep_i64 I hfn bsMem args v P hbs hargs hspec hQ hbound

/-- `LegalSigAll` specialization of `eventually_ret1_sep_i64_optInlinePolicy`. -/
theorem eventually_ret1_sep_i64_of_legalSigAll_optInlinePolicy
    (cert : LinkedCert T L lt hcl (mod.optInlinePolicy policy) [] exits nX maxBound)
    (I : TargetInit T maxStack maxMem) (Γ : Env) (hM : ModuleOk Γ mod)
    (hleg : LegalSigAll lt mod.fns) {f : Fn} (hf : f ∈ mod.fns) (hret : f.rs = [i64])
    (hnoex : ∀ args m Q X X', Γ f.name f.as f.rs args m Q X → Γ f.name f.as f.rs args m Q X')
    (bsMem : List UInt8) (args : Tup Val f.as) (v : Val i64) (P : Mem 64 → Prop)
    (hbs : bsMem.length ≤ maxMem) (hargs : (T.toIsa.assignArgs f.as).isSome = true)
    {Q : Post [i64]}
    (hspec : Γ f.name f.as [i64] args (bsMem.At 0x1000#64) Q (fun _ _ _ _ => False))
    (hQ : ∀ rets m', Q rets m' → rets = (v, ()) ∧ P m')
    (hbound : maxBound ≤ maxStack := by omega) :
    Eventually (T.mach.step cert.host)
      (fun st => T.mach.pc st = I.ra0 ∧ T.mach.getGpr (T.mach.data st) I.ret0 = v ∧
        (T.mach.mem (T.mach.data st) =⋆ P ⋆ T.Exit I.sp0 (cert.bound f.name) ⋆ Std.ExtHashMap.emp))
      (T.mach.mkState (I.initState (cert.bound f.name) bsMem args)
        (T.mach.labelAddr cert.host f.name)) :=
  have ⟨has, hrs⟩ := hleg f hf
  cert.eventually_ret1_sep_i64_optInlinePolicy I Γ hM hf hret has hrs hnoex
    bsMem args v P hbs hargs hspec hQ hbound

/-- End-to-end `Eventually` theorem for a non-exiting `i64`-returning `f ∈ mod.fns` on the
inlined `cert.host` projecting `I.ra0` and `I.ret0`. -/
theorem eventually_ret1_i64_optInlinePolicy
    (cert : LinkedCert T L lt hcl (mod.optInlinePolicy policy) [] exits nX maxBound)
    (I : TargetInit T maxStack maxMem) (Γ : Env) (hM : ModuleOk Γ mod)
    {f : Fn} (hf : f ∈ mod.fns) (hret : f.rs = [i64])
    (has : lt.legalSig f.as = f.as) (hrs : lt.legalSig f.rs = f.rs)
    (hnoex : ∀ args m Q X X', Γ f.name f.as f.rs args m Q X → Γ f.name f.as f.rs args m Q X')
    (bsMem : List UInt8) (args : Tup Val f.as) (v : Val i64)
    (hbs : bsMem.length ≤ maxMem) (hargs : (T.toIsa.assignArgs f.as).isSome = true)
    {Q : Post [i64]}
    (hspec : Γ f.name f.as [i64] args (bsMem.At 0x1000#64) Q (fun _ _ _ _ => False))
    (hQ : ∀ rets m', Q rets m' → rets = (v, ()))
    (hbound : maxBound ≤ maxStack := by omega) :
    Eventually (T.mach.step cert.host)
      (fun st => T.mach.pc st = I.ra0 ∧ T.mach.getGpr (T.mach.data st) I.ret0 = v)
      (T.mach.mkState (I.initState (cert.bound f.name) bsMem args)
        (T.mach.labelAddr cert.host f.name)) :=
  eventually_weaken _ _ _ _ (fun _ h => ⟨h.1, h.2.1⟩)
    (cert.eventually_ret1_sep_i64_optInlinePolicy I Γ hM hf hret has hrs hnoex
      bsMem args v (fun _ => True) hbs hargs hspec
      (fun rets m' hm' => ⟨hQ rets m' hm', trivial⟩) hbound)

/-- `Module.optInline maxSize` specialization of `eventually_ret1_sep_i64_optInlinePolicy`. -/
theorem eventually_ret1_sep_i64_optInline {maxSize : Nat}
    (cert : LinkedCert T L lt hcl (mod.optInline maxSize) [] exits nX maxBound)
    (I : TargetInit T maxStack maxMem) (Γ : Env) (hM : ModuleOk Γ mod)
    {f : Fn} (hf : f ∈ mod.fns) (hret : f.rs = [i64])
    (has : lt.legalSig f.as = f.as) (hrs : lt.legalSig f.rs = f.rs)
    (hnoex : ∀ args m Q X X', Γ f.name f.as f.rs args m Q X → Γ f.name f.as f.rs args m Q X')
    (bsMem : List UInt8) (args : Tup Val f.as) (v : Val i64) (P : Mem 64 → Prop)
    (hbs : bsMem.length ≤ maxMem) (hargs : (T.toIsa.assignArgs f.as).isSome = true)
    {Q : Post [i64]}
    (hspec : Γ f.name f.as [i64] args (bsMem.At 0x1000#64) Q (fun _ _ _ _ => False))
    (hQ : ∀ rets m', Q rets m' → rets = (v, ()) ∧ P m')
    (hbound : maxBound ≤ maxStack := by omega) :
    Eventually (T.mach.step cert.host)
      (fun st => T.mach.pc st = I.ra0 ∧ T.mach.getGpr (T.mach.data st) I.ret0 = v ∧
        (T.mach.mem (T.mach.data st) =⋆ P ⋆ T.Exit I.sp0 (cert.bound f.name) ⋆ Std.ExtHashMap.emp))
      (T.mach.mkState (I.initState (cert.bound f.name) bsMem args)
        (T.mach.labelAddr cert.host f.name)) :=
  cert.eventually_ret1_sep_i64_optInlinePolicy I Γ hM hf hret has hrs hnoex
    bsMem args v P hbs hargs hspec hQ hbound

end ConcreteInit

end LinkedCert

/-! ## `inline_mod!` Meta Materializer & Elaborator -/

meta section

open Lean Elab Command Meta

/-- `Type 0` materialized function payload extracted from `Module.inlinePolicy`. -/
structure MatFnData where
  name : Sym
  as : List Ty
  rs : List Ty
  flat : TFlat rs

/-- `Type 0` materialized module payload evaluated once in MetaM by `inline_mod!`. -/
structure MatModData where
  fns : List MatFnData
  externs : List Extern
  exits : List Sym

/-- Evaluate `M.inlinePolicy policy` and reify every function body once into `Type 0` `TFlat`. -/
def evalOptInlinePolicyData (M : Module) (policy : InlinePolicy) : MatModData :=
  let M' := M.inlinePolicy policy
  { fns := M'.fns.map fun fn => ⟨fn.name, fn.as, fn.rs, reifyFunc fn.body⟩
    externs := M'.externs
    exits := M'.exits }

private def mkListLit (u : Level) (ty : Lean.Expr) (elems : List Lean.Expr) : Lean.Expr :=
  elems.foldr
    (fun x acc => mkApp3 (Lean.mkConst ``List.cons [u]) ty x acc)
    (mkApp (Lean.mkConst ``List.nil [u]) ty)

private def listTyToExpr (ts : List Ty) : Lean.Expr :=
  mkListLit .zero (Lean.mkConst ``LeanQbe.T.Ty) (ts.map tyToExpr)

private def listListTyToExpr (tss : List (List Ty)) : Lean.Expr :=
  let listTy := mkApp (Lean.mkConst ``List [.zero]) (Lean.mkConst ``LeanQbe.T.Ty)
  mkListLit .zero listTy (tss.map listTyToExpr)

private def cmpOpToExpr : CmpOp → Lean.Expr
  | .eq => Lean.mkConst ``LeanQbe.T.CmpOp.eq
  | .ne => Lean.mkConst ``LeanQbe.T.CmpOp.ne
  | .ult => Lean.mkConst ``LeanQbe.T.CmpOp.ult
  | .ule => Lean.mkConst ``LeanQbe.T.CmpOp.ule
  | .ugt => Lean.mkConst ``LeanQbe.T.CmpOp.ugt
  | .uge => Lean.mkConst ``LeanQbe.T.CmpOp.uge
  | .slt => Lean.mkConst ``LeanQbe.T.CmpOp.slt
  | .sle => Lean.mkConst ``LeanQbe.T.CmpOp.sle
  | .sgt => Lean.mkConst ``LeanQbe.T.CmpOp.sgt
  | .sge => Lean.mkConst ``LeanQbe.T.CmpOp.sge

private def fcmpOpToExpr : FCmpOp → Lean.Expr
  | .eq => Lean.mkConst ``LeanQbe.T.FCmpOp.eq
  | .ne => Lean.mkConst ``LeanQbe.T.FCmpOp.ne
  | .lt => Lean.mkConst ``LeanQbe.T.FCmpOp.lt
  | .le => Lean.mkConst ``LeanQbe.T.FCmpOp.le
  | .gt => Lean.mkConst ``LeanQbe.T.FCmpOp.gt
  | .ge => Lean.mkConst ``LeanQbe.T.FCmpOp.ge
  | .ord => Lean.mkConst ``LeanQbe.T.FCmpOp.ord
  | .uno => Lean.mkConst ``LeanQbe.T.FCmpOp.uno

private def valToExpr : (t : Ty) → Val t → Lean.Expr
  | .bool, v => Lean.toExpr (v : Bool)
  | .bits n, v => @Lean.toExpr (BitVec n) _ v
  | .float f, v => @Lean.toExpr (BitVec f.width) _ v
  | .pair a b, v =>
    let ta := mkApp (Lean.mkConst ``LeanQbe.T.Val) (tyToExpr a)
    let tb := mkApp (Lean.mkConst ``LeanQbe.T.Val) (tyToExpr b)
    mkApp4 (Lean.mkConst ``Prod.mk [.zero, .zero]) ta tb (valToExpr a v.1) (valToExpr b v.2)

private def argKToExpr (t : Ty) : Arg K t → Lean.Expr
  | .var idx =>
    mkApp3 (Lean.mkConst ``LeanQbe.T.Arg.var) (Lean.mkConst ``LeanQbe.T.K)
      (tyToExpr t) (mkNatLit idx)
  | .imm c =>
    mkApp3 (Lean.mkConst ``LeanQbe.T.Arg.imm) (Lean.mkConst ``LeanQbe.T.K)
      (tyToExpr t) (valToExpr t c)

private def tupArgKToExpr : (ts : List Ty) → Tup (Arg K) ts → Lean.Expr
  | [], () => Lean.mkConst ``Unit.unit
  | t :: ts, (a, as) =>
    let kE := Lean.mkConst ``LeanQbe.T.K
    let ta := mkApp2 (Lean.mkConst ``LeanQbe.T.Arg) kE (tyToExpr t)
    let tb := mkApp3 (Lean.mkConst ``LeanQbe.T.Tup) (Lean.mkConst ``LeanQbe.T.Ty)
      (mkApp (Lean.mkConst ``LeanQbe.T.Arg) kE) (listTyToExpr ts)
    mkApp4 (Lean.mkConst ``Prod.mk [.zero, .zero]) ta tb (argKToExpr t a) (tupArgKToExpr ts as)

private def mkTyOpExpr (nm : Name) (t : Ty) : Lean.Expr :=
  mkApp (Lean.mkConst nm) (tyToExpr t)

private def mkNatOpExpr (nm : Name) (n : Nat) : Lean.Expr :=
  mkApp (Lean.mkConst nm) (mkNatLit n)

private def mkTyImmOpExpr (nm : Name) (t : Ty) (imm : BitVec 8) : Lean.Expr :=
  mkApp2 (Lean.mkConst nm) (tyToExpr t) (Lean.toExpr imm)

private def opCodeToExpr {sig rs : List Ty} : OpCode sig rs → Lean.Expr
  | .copy t => mkTyOpExpr ``LeanQbe.T.OpCode.copy t
  | .add t => mkTyOpExpr ``LeanQbe.T.OpCode.add t
  | .sub t => mkTyOpExpr ``LeanQbe.T.OpCode.sub t
  | .mul t => mkTyOpExpr ``LeanQbe.T.OpCode.mul t
  | .neg t => mkTyOpExpr ``LeanQbe.T.OpCode.neg t
  | .and t => mkTyOpExpr ``LeanQbe.T.OpCode.and t
  | .or t => mkTyOpExpr ``LeanQbe.T.OpCode.or t
  | .xor t => mkTyOpExpr ``LeanQbe.T.OpCode.xor t
  | .not t => mkTyOpExpr ``LeanQbe.T.OpCode.not t
  | .ternlog t imm => mkTyImmOpExpr ``LeanQbe.T.OpCode.ternlog t imm
  | .shl t => mkTyOpExpr ``LeanQbe.T.OpCode.shl t
  | .lshr t => mkTyOpExpr ``LeanQbe.T.OpCode.lshr t
  | .ashr t => mkTyOpExpr ``LeanQbe.T.OpCode.ashr t
  | .rotl t => mkTyOpExpr ``LeanQbe.T.OpCode.rotl t
  | .rotr t => mkTyOpExpr ``LeanQbe.T.OpCode.rotr t
  | .fshl n => mkNatOpExpr ``LeanQbe.T.OpCode.fshl n
  | .fshr n => mkNatOpExpr ``LeanQbe.T.OpCode.fshr n
  | .bswap t => mkTyOpExpr ``LeanQbe.T.OpCode.bswap t
  | .clz n => mkNatOpExpr ``LeanQbe.T.OpCode.clz n
  | .cls n => mkNatOpExpr ``LeanQbe.T.OpCode.cls n
  | .rbit n => mkNatOpExpr ``LeanQbe.T.OpCode.rbit n
  | .ctz n => mkNatOpExpr ``LeanQbe.T.OpCode.ctz n
  | .popcnt n => mkNatOpExpr ``LeanQbe.T.OpCode.popcnt n
  | .cmp o t m _ =>
    let me := tyToExpr m
    mkApp4 (Lean.mkConst ``LeanQbe.T.OpCode.cmp) (cmpOpToExpr o) (tyToExpr t) me
      (mkApp2 (Lean.mkConst ``Eq.refl [.one]) (Lean.mkConst ``LeanQbe.T.Ty) me)
  | .select t => mkTyOpExpr ``LeanQbe.T.OpCode.select t
  | .blend t m _ =>
    let me := tyToExpr m
    mkApp3 (Lean.mkConst ``LeanQbe.T.OpCode.blend) (tyToExpr t) me
      (mkApp2 (Lean.mkConst ``Eq.refl [.one]) (Lean.mkConst ``LeanQbe.T.Ty) me)
  | .zext m n => mkApp2 (Lean.mkConst ``LeanQbe.T.OpCode.zext) (mkNatLit m) (mkNatLit n)
  | .sext m n => mkApp2 (Lean.mkConst ``LeanQbe.T.OpCode.sext) (mkNatLit m) (mkNatLit n)
  | .trunc m n => mkApp2 (Lean.mkConst ``LeanQbe.T.OpCode.trunc) (mkNatLit m) (mkNatLit n)
  | .ofBool n => mkNatOpExpr ``LeanQbe.T.OpCode.ofBool n
  | .addc n => mkNatOpExpr ``LeanQbe.T.OpCode.addc n
  | .subb n => mkNatOpExpr ``LeanQbe.T.OpCode.subb n
  | .umulw n => mkNatOpExpr ``LeanQbe.T.OpCode.umulw n
  | .smulw n => mkNatOpExpr ``LeanQbe.T.OpCode.smulw n
  | .udiv n => mkNatOpExpr ``LeanQbe.T.OpCode.udiv n
  | .sdiv n => mkNatOpExpr ``LeanQbe.T.OpCode.sdiv n
  | .urem n => mkNatOpExpr ``LeanQbe.T.OpCode.urem n
  | .srem n => mkNatOpExpr ``LeanQbe.T.OpCode.srem n
  | .udiv0 n => mkNatOpExpr ``LeanQbe.T.OpCode.udiv0 n
  | .sdiv0 n => mkNatOpExpr ``LeanQbe.T.OpCode.sdiv0 n
  | .mkpair a b => mkApp2 (Lean.mkConst ``LeanQbe.T.OpCode.mkpair) (tyToExpr a) (tyToExpr b)
  | .unpair a b => mkApp2 (Lean.mkConst ``LeanQbe.T.OpCode.unpair) (tyToExpr a) (tyToExpr b)
  | .bitcast t u _ =>
    mkApp3 (Lean.mkConst ``LeanQbe.T.OpCode.bitcast) (tyToExpr t) (tyToExpr u)
      (mkApp2 (Lean.mkConst ``Eq.refl [.one]) (Lean.mkConst ``Nat) (mkNatLit t.size))
  | .shufd t imm => mkTyImmOpExpr ``LeanQbe.T.OpCode.shufd t imm
  | .shufb t => mkTyOpExpr ``LeanQbe.T.OpCode.shufb t
  | .alignr t imm => mkTyImmOpExpr ``LeanQbe.T.OpCode.alignr t imm
  | .blendw t imm => mkTyImmOpExpr ``LeanQbe.T.OpCode.blendw t imm
  | .sha256rnds2 => Lean.mkConst ``LeanQbe.T.OpCode.sha256rnds2
  | .sha256msg1 => Lean.mkConst ``LeanQbe.T.OpCode.sha256msg1
  | .sha256msg2 => Lean.mkConst ``LeanQbe.T.OpCode.sha256msg2
  | .fadd t => mkTyOpExpr ``LeanQbe.T.OpCode.fadd t
  | .fsub t => mkTyOpExpr ``LeanQbe.T.OpCode.fsub t
  | .fmul t => mkTyOpExpr ``LeanQbe.T.OpCode.fmul t
  | .fdiv t => mkTyOpExpr ``LeanQbe.T.OpCode.fdiv t
  | .ffma t => mkTyOpExpr ``LeanQbe.T.OpCode.ffma t
  | .fsqrt t => mkTyOpExpr ``LeanQbe.T.OpCode.fsqrt t
  | .fneg t => mkTyOpExpr ``LeanQbe.T.OpCode.fneg t
  | .fabs t => mkTyOpExpr ``LeanQbe.T.OpCode.fabs t
  | .fcmp o t m _ =>
    let me := tyToExpr m
    mkApp4 (Lean.mkConst ``LeanQbe.T.OpCode.fcmp) (fcmpOpToExpr o) (tyToExpr t) me
      (mkApp2 (Lean.mkConst ``Eq.refl [.one]) (Lean.mkConst ``LeanQbe.T.Ty) me)
  | .fptoui f n => mkApp2 (Lean.mkConst ``LeanQbe.T.OpCode.fptoui) (Lean.toExpr f) (mkNatLit n)
  | .fptosi f n => mkApp2 (Lean.mkConst ``LeanQbe.T.OpCode.fptosi) (Lean.toExpr f) (mkNatLit n)
  | .uitofp n f => mkApp2 (Lean.mkConst ``LeanQbe.T.OpCode.uitofp) (mkNatLit n) (Lean.toExpr f)
  | .sitofp n f => mkApp2 (Lean.mkConst ``LeanQbe.T.OpCode.sitofp) (mkNatLit n) (Lean.toExpr f)
  | .fcvt f g => mkApp2 (Lean.mkConst ``LeanQbe.T.OpCode.fcvt) (Lean.toExpr f) (Lean.toExpr g)

private def opKToExpr {rs : List Ty} (op : Op K rs) : Lean.Expr :=
  mkApp5 (Lean.mkConst ``LeanQbe.T.Op.mk) (Lean.mkConst ``LeanQbe.T.K)
    (listTyToExpr rs) (listTyToExpr op.sig) (opCodeToExpr op.code) (tupArgKToExpr op.sig op.args)

mutual
private def tflatToExpr (rs : List Ty) : TFlat rs → Lean.Expr
  | .let_ (ts := ts) op k =>
    mkApp4 (Lean.mkConst ``LeanQbe.T.TFlat.let_) (listTyToExpr rs) (listTyToExpr ts)
      (opKToExpr op) (tflatToExpr rs k)
  | .load t a k =>
    mkApp4 (Lean.mkConst ``LeanQbe.T.TFlat.load) (listTyToExpr rs) (tyToExpr t)
      (argKToExpr i64 a) (tflatToExpr rs k)
  | .store (t := t) v a k =>
    mkApp5 (Lean.mkConst ``LeanQbe.T.TFlat.store) (listTyToExpr rs) (tyToExpr t)
      (argKToExpr t v) (argKToExpr i64 a) (tflatToExpr rs k)
  | .call f (as := as) bs args k =>
    mkApp6 (Lean.mkConst ``LeanQbe.T.TFlat.call) (listTyToExpr rs) (Lean.toExpr f)
      (listTyToExpr as) (listTyToExpr bs) (tupArgKToExpr as args) (tflatToExpr rs k)
  | .jnz c t e =>
    mkApp4 (Lean.mkConst ``LeanQbe.T.TFlat.jnz) (listTyToExpr rs) (argKToExpr .bool c)
      (tflatToExpr rs t) (tflatToExpr rs e)
  | .jump (ts := ts) j args =>
    mkApp4 (Lean.mkConst ``LeanQbe.T.TFlat.jump) (listTyToExpr rs) (listTyToExpr ts)
      (mkNatLit j) (tupArgKToExpr ts args)
  | .ret vs =>
    mkApp2 (Lean.mkConst ``LeanQbe.T.TFlat.ret) (listTyToExpr rs) (tupArgKToExpr rs vs)
  | .exit f (as := as) args =>
    mkApp4 (Lean.mkConst ``LeanQbe.T.TFlat.exit) (listTyToExpr rs) (Lean.toExpr f)
      (listTyToExpr as) (tupArgKToExpr as args)
  | .hlt => mkApp (Lean.mkConst ``LeanQbe.T.TFlat.hlt) (listTyToExpr rs)
  | .group (sig := sig) bodies k =>
    mkApp4 (Lean.mkConst ``LeanQbe.T.TFlat.group) (listTyToExpr rs) (listListTyToExpr sig)
      (tblocksToExpr rs bodies) (tflatToExpr rs k)

private def tblocksToExpr (rs : List Ty) :
    {sig : List (List Ty)} → TBlocks rs sig → Lean.Expr
  | _, .nil => mkApp (Lean.mkConst ``LeanQbe.T.TBlocks.nil) (listTyToExpr rs)
  | _, .cons (ts := ts) (sig := sig') b bs =>
    mkApp5 (Lean.mkConst ``LeanQbe.T.TBlocks.cons) (listTyToExpr rs) (listTyToExpr ts)
      (listListTyToExpr sig') (tflatToExpr rs b) (tblocksToExpr rs bs)
end

private def matFnToExpr (f : MatFnData) : Lean.Expr :=
  let asE := listTyToExpr f.as
  let rsE := listTyToExpr f.rs
  let bodyE := mkApp3 (Lean.mkConst ``LeanQbe.T.denoteFunc) asE rsE (tflatToExpr f.rs f.flat)
  mkApp4 (Lean.mkConst ``LeanQbe.T.Fn.mk) (Lean.toExpr f.name) asE rsE bodyE

private def externToExpr (e : Extern) : Lean.Expr :=
  mkApp3 (Lean.mkConst ``LeanQbe.T.Extern.mk) (Lean.toExpr e.name)
    (listTyToExpr e.as) (listTyToExpr e.rs)

private def matModExpr (fnConsts : List Lean.Expr) (m : MatModData) : Lean.Expr :=
  let fnsE := mkListLit .one (Lean.mkConst ``LeanQbe.T.Fn) fnConsts
  let extsE := mkListLit .zero (Lean.mkConst ``LeanQbe.T.Extern) (m.externs.map externToExpr)
  let exitsE := mkListLit .zero (Lean.mkConst ``LeanQbe.T.Sym) (m.exits.map Lean.toExpr)
  mkApp3 (Lean.mkConst ``LeanQbe.T.Module.mk) fnsE extsE exitsE

/-- `inline_mod! inlModName srcMod policy` evaluates `srcMod.optInlinePolicy policy` once in
MetaM, emits per-function literal `denoteFunc`-backed `Fn` definitions assembled into
`inlModName : Module` (avoiding monolithic codegen recursion depth on large modules), and proves
`inlModName.eq : inlModName = srcMod.optInlinePolicy policy` and `inlModName.fns_eq` once via
`addKernelEqThm` so parallel `compile_linked_chunks!` slices incur zero repeated inlining. -/
scoped syntax "inline_mod! " ident term:arg term:arg : command

scoped elab_rules : command
  | `(inline_mod! $inlId $srcModT $policyT) => do
    let ns ← getCurrNamespace
    let inlNm := ns ++ inlId.getId
    let (matData, optInlE) ← liftTermElabM do
      let srcModE ← Term.elabTerm srcModT (some (Lean.mkConst ``LeanQbe.T.Module))
      let policyE ← Term.elabTerm policyT (some (Lean.mkConst ``LeanQbe.T.InlinePolicy))
      Term.synthesizeSyntheticMVarsNoPostponing
      let srcModE ← instantiateMVars srcModE
      let policyE ← instantiateMVars policyE
      let callE := mkApp2 (Lean.mkConst ``LeanQbe.T.evalOptInlinePolicyData) srcModE policyE
      let matData ← unsafe evalExpr MatModData (Lean.mkConst ``LeanQbe.T.MatModData) callE
      let optInlE ← instantiateMVars
        (mkApp2 (Lean.mkConst ``LeanQbe.T.Module.optInlinePolicy) srcModE policyE)
      return (matData, optInlE)
    let fnTy := Lean.mkConst ``LeanQbe.T.Fn
    let modTy := Lean.mkConst ``LeanQbe.T.Module
    liftCoreM do
      let mut fnConsts : List Lean.Expr := []
      let mut idx : Nat := 0
      for f in matData.fns do
        let fnNm := inlNm ++ `fn ++ Name.mkSimple s!"f{idx}"
        addCertDef fnNm fnTy (matFnToExpr f) true
        fnConsts := fnConsts ++ [Lean.mkConst fnNm]
        idx := idx + 1
      let modVal := matModExpr fnConsts matData
      addCertDef inlNm modTy modVal true
      addKernelEqThm (inlNm ++ `eq) modTy (Lean.mkConst inlNm) optInlE .one
    let (fnsEqTy, fnsEqProof) ← liftTermElabM do
      let proof ← mkAppM ``congrArg
        #[Lean.mkConst ``LeanQbe.T.Module.fns, Lean.mkConst (inlNm ++ `eq)]
      let ty ← inferType proof
      return (← instantiateMVars ty, ← instantiateMVars proof)
    liftCoreM <| addCertThm (inlNm ++ `fns_eq) fnsEqTy fnsEqProof

end

end LeanQbe.T
