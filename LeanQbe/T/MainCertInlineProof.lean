module

public import LeanQbe.T.MainCertProof
public import LeanQbe.T.MainInline
import LeanQbe.T.InlineLemmas
import LeanQbe.T.AbiLemmas

/-!
# Pure Proof Bridges for Inlined Compilation (`MainCertInlineProof`)

`Lean`-meta-free proof bridges connecting `MainInline.lean` (`Module.optInlinePolicy` /
`Module.optInline`) to `LinkedCert` (`MainCertCore` / `MainCertProof`) and raw
`compileModuleOptInlinePolicy`:
* `moduleOk_parts` and `LinkedCert.{castFns, castModule, of_eq}`;
* `LinkedCert.fnSpec_optInlinePolicy` family and concrete `TargetInit` `Eventually` lifts;
* `fnSpec_of_compileModuleOptInlinePolicy`, `fnSpec_maxB_of_compileModuleOptInlinePolicy`, and
  `run_ret1_sep_i64_at` (arbitrary host and stack bound `n ≤ maxStack`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T

/-- Extract acyclicity, well-formedness, and `Func.wp` obligations from `ModuleOk Γ mod`. -/
theorem moduleOk_parts {Γ : Env} {mod : Module} (hM : ModuleOk Γ mod) :
    mod.checkAcyclic = true ∧
    (∀ f ∈ mod.fns, f.Wf) ∧
    (∀ f ∈ mod.fns, ∀ xs m Q X, Γ f.name f.as f.rs xs m Q X → Func.wp Γ f.body xs m Q X) := by
  refine ⟨?_, fun f hf => ?_, fun f hf => ?_⟩
  · simp only [Module.checkAcyclic, Bool.and_eq_true]
    exact ⟨listNodup_iff.mpr hM.nodup, checkFnsCallsOk_of_forall _ _ [] _ fun p fn q hsp => by
      simpa using (hM.fnsOk p fn q hsp).2.1⟩
  · obtain ⟨p, q, hsp⟩ := List.mem_iff_append.mp hf; exact (hM.fnsOk p f q hsp).1
  · obtain ⟨p, q, hsp⟩ := List.mem_iff_append.mp hf; exact (hM.fnsOk p f q hsp).2.2

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

/-- Transport a `LinkedCert` along `h : mod₁ = mod₂` in O(1) without re-checking any chunk. -/
@[expose] noncomputable def castModule
    (cert : LinkedCert T L lt hcl mod₁ ext₀ exits nX maxBound) (h : mod₁ = mod₂) :
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
    InlOutSpec T h lt mod Γ f.name f (cert.bound f.name) nX := by
  have ⟨hacyc, hwf, hwp⟩ := moduleOk_parts hM
  exact cert.compiled.fnSpec_optInlinePolicy mod policy cert.fns_eq h Γ k₀ hc hu
    hacyc hwf cert.supportsAll hwp hext hext_uniq hexits hf

/-- Self-contained `Defined` + `FnSpec` on `cert.host` (`ext₀ = []`) for `optInlinePolicy`. -/
theorem fnSpec_host_optInlinePolicy
    (cert : LinkedCert T L lt hcl (mod.optInlinePolicy policy) [] exits nX maxBound)
    (Γ : Env) (hM : ModuleOk Γ mod) {f : Fn} (hf : f ∈ mod.fns) :
    InlOutSpec T cert.host lt mod Γ f.name f (cert.bound f.name) nX :=
  cert.fnSpec_optInlinePolicy cert.host Γ 0 cert.code_infix_host cert.labelsUnique hM
    (fun _ h => nomatch h) ⟨(fun _ h => nomatch h), (fun _ h => nomatch h)⟩
    (fun _ hg => cert.defined_exit_host hg) hf

/-- Source-level `Defined` + `FnSpec` on `cert.host` (`ext₀ = []`) when `lt.legalSig` fixes
`(f.as, f.rs)` and `Γ` ignores exits. -/
theorem fnSpec_host_src_optInlinePolicy
    (cert : LinkedCert T L lt hcl (mod.optInlinePolicy policy) [] exits nX maxBound)
    (Γ : Env) (hM : ModuleOk Γ mod) {f : Fn} (hf : f ∈ mod.fns)
    (has : lt.legalSig f.as = f.as) (hrs : lt.legalSig f.rs = f.rs) (hnoex : InlNoExit Γ f) :
    T.Defined cert.host f.name ∧
      T.FnSpec cert.host f.name (Γ f.name f.as f.rs) (cert.bound f.name) nX := by
  obtain ⟨hdef, hspec⟩ := cert.fnSpec_host_optInlinePolicy Γ hM hf
  exact ⟨hdef, fnSpec_of_legalEnv_legalSig_eq_noExit has hrs
    (List.mem_append_left _ (List.mem_map_of_mem hf)) hnoex hspec⟩

/-- `LegalSigAll` specialization of `fnSpec_host_src_optInlinePolicy`. -/
theorem fnSpec_host_of_legalSigAll_optInlinePolicy
    (cert : LinkedCert T L lt hcl (mod.optInlinePolicy policy) [] exits nX maxBound)
    (Γ : Env) (hM : ModuleOk Γ mod) (hleg : LegalSigAll lt mod.fns)
    {f : Fn} (hf : f ∈ mod.fns) (hnoex : InlNoExit Γ f) :
    T.Defined cert.host f.name ∧
      T.FnSpec cert.host f.name (Γ f.name f.as f.rs) (cert.bound f.name) nX :=
  have ⟨has, hrs⟩ := hleg f hf
  cert.fnSpec_host_src_optInlinePolicy Γ hM hf has hrs hnoex

/-- Arbitrary-host `FnSpec` over `mod.optInlinePolicy policy` (`ext₀ = []`, `exits = []`). -/
theorem fnSpec_noExit_id_optInlinePolicy
    (cert : LinkedCert T L lt hcl (mod.optInlinePolicy policy) [] [] nX maxBound)
    (h : T.mach.Host) (Γ : Env) (k₀ : Nat)
    (hc : cert.code.IsInfixAt (T.mach.prog h) k₀) (hu : T.LabelsUnique h)
    (hM : ModuleOk Γ mod) {f : Fn} (hf : f ∈ mod.fns)
    (has : lt.legalSig f.as = f.as) (hrs : lt.legalSig f.rs = f.rs) (hnoex : InlNoExit Γ f) :
    T.Defined h f.name ∧ T.FnSpec h f.name (Γ f.name f.as f.rs) (cert.bound f.name) nX := by
  have ⟨hacyc, hwf, hwp⟩ := moduleOk_parts hM
  exact cert.compiled.fnSpec_noExit_id_optInlinePolicy mod policy cert.fns_eq h Γ k₀ hc hu
    hacyc hwf cert.supportsAll hwp hf has hrs hnoex

/-- `LegalSigAll` specialization of `fnSpec_noExit_id_optInlinePolicy`. -/
theorem fnSpec_noExit_of_legalSigAll_optInlinePolicy
    (cert : LinkedCert T L lt hcl (mod.optInlinePolicy policy) [] [] nX maxBound)
    (h : T.mach.Host) (Γ : Env) (k₀ : Nat)
    (hc : cert.code.IsInfixAt (T.mach.prog h) k₀) (hu : T.LabelsUnique h)
    (hM : ModuleOk Γ mod) (hleg : LegalSigAll lt mod.fns) {f : Fn} (hf : f ∈ mod.fns)
    (hnoex : InlNoExit Γ f) :
    T.Defined h f.name ∧ T.FnSpec h f.name (Γ f.name f.as f.rs) (cert.bound f.name) nX :=
  have ⟨has, hrs⟩ := hleg f hf
  cert.fnSpec_noExit_id_optInlinePolicy h Γ k₀ hc hu hM hf has hrs hnoex

/-- `Module.optInline maxSize` specialization of `fnSpec_optInlinePolicy`. -/
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
    InlOutSpec T h lt mod Γ f.name f (cert.bound f.name) nX :=
  cert.fnSpec_optInlinePolicy h Γ k₀ hc hu hM hext hext_uniq hexits hf

/-- `Module.optInline maxSize` specialization of `fnSpec_host_optInlinePolicy`. -/
theorem fnSpec_host_optInline {maxSize : Nat}
    (cert : LinkedCert T L lt hcl (mod.optInline maxSize) [] exits nX maxBound)
    (Γ : Env) (hM : ModuleOk Γ mod) {f : Fn} (hf : f ∈ mod.fns) :
    InlOutSpec T cert.host lt mod Γ f.name f (cert.bound f.name) nX :=
  cert.fnSpec_host_optInlinePolicy Γ hM hf

/-- `Module.optInline maxSize` specialization of `fnSpec_noExit_id_optInlinePolicy`. -/
theorem fnSpec_noExit_id_optInline {maxSize : Nat}
    (cert : LinkedCert T L lt hcl (mod.optInline maxSize) [] [] nX maxBound)
    (h : T.mach.Host) (Γ : Env) (k₀ : Nat)
    (hc : cert.code.IsInfixAt (T.mach.prog h) k₀) (hu : T.LabelsUnique h)
    (hM : ModuleOk Γ mod) {f : Fn} (hf : f ∈ mod.fns)
    (has : lt.legalSig f.as = f.as) (hrs : lt.legalSig f.rs = f.rs) (hnoex : InlNoExit Γ f) :
    T.Defined h f.name ∧ T.FnSpec h f.name (Γ f.name f.as f.rs) (cert.bound f.name) nX :=
  cert.fnSpec_noExit_id_optInlinePolicy h Γ k₀ hc hu hM hf has hrs hnoex

/-- `Module.optInline maxSize` specialization of `fnSpec_noExit_of_legalSigAll_optInlinePolicy`. -/
theorem fnSpec_noExit_of_legalSigAll_optInline {maxSize : Nat}
    (cert : LinkedCert T L lt hcl (mod.optInline maxSize) [] [] nX maxBound)
    (h : T.mach.Host) (Γ : Env) (k₀ : Nat)
    (hc : cert.code.IsInfixAt (T.mach.prog h) k₀) (hu : T.LabelsUnique h)
    (hM : ModuleOk Γ mod) (hleg : LegalSigAll lt mod.fns) {f : Fn} (hf : f ∈ mod.fns)
    (hnoex : InlNoExit Γ f) :
    T.Defined h f.name ∧ T.FnSpec h f.name (Γ f.name f.as f.rs) (cert.bound f.name) nX :=
  cert.fnSpec_noExit_of_legalSigAll_optInlinePolicy h Γ k₀ hc hu hM hleg hf hnoex

/-! ### Concrete `TargetInit` `Eventually` lifts for `optInlinePolicy` / `optInline` -/

section ConcreteInit

variable {maxStack maxMem : Nat}

/-- Postcondition for non-exiting `i64`-returning `Eventually` lifts on `cert.host`. -/
abbrev InlRet1SepEv
    (cert : LinkedCert T L lt hcl mod [] exits nX maxBound)
    (I : TargetInit T maxStack maxMem) (f : Fn) (bsMem : List UInt8) (args : Tup Val f.as)
    (v : Val i64) (P : Mem 64 → Prop) : Prop :=
  Eventually (T.mach.step cert.host)
    (fun st => T.mach.pc st = I.ra0 ∧ T.mach.getGpr (T.mach.data st) I.ret0 = v ∧
      (T.mach.mem (T.mach.data st) =⋆ P ⋆ T.Exit I.sp0 (cert.bound f.name) ⋆
        Std.ExtHashMap.emp))
    (T.mach.mkState (I.initState (cert.bound f.name) bsMem args)
      (T.mach.labelAddr cert.host f.name))

/-- End-to-end `Eventually` theorem from source `ModuleOk Γ mod` to execution on `cert.host`. -/
theorem eventually_fnSpec_optInlinePolicy
    (cert : LinkedCert T L lt hcl (mod.optInlinePolicy policy) [] exits nX maxBound)
    (I : TargetInit T maxStack maxMem) (Γ : Env) (hM : ModuleOk Γ mod)
    {f : Fn} (hf : f ∈ mod.fns) (has : lt.legalSig f.as = f.as) (hrs : lt.legalSig f.rs = f.rs)
    (hnoex : InlNoExit Γ f) (bsMem : List UInt8) (args : Tup Val f.as)
    (hbs : bsMem.length ≤ maxMem) (hargs : (T.toIsa.assignArgs f.as).isSome = true)
    {Q : Post f.rs} {X : XPost} (hspec : Γ f.name f.as f.rs args (bsMem.At 0x1000#64) Q X)
    {post : T.mach.State → Prop}
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

/-- Non-exiting `i64`-returning `Eventually` theorem on `cert.host` establishing post `P`. -/
theorem eventually_ret1_sep_i64_optInlinePolicy
    (cert : LinkedCert T L lt hcl (mod.optInlinePolicy policy) [] exits nX maxBound)
    (I : TargetInit T maxStack maxMem) (Γ : Env) (hM : ModuleOk Γ mod)
    {f : Fn} (hf : f ∈ mod.fns) (hret : f.rs = [i64])
    (has : lt.legalSig f.as = f.as) (hrs : lt.legalSig f.rs = f.rs) (hnoex : InlNoExit Γ f)
    (bsMem : List UInt8) (args : Tup Val f.as) (v : Val i64) (P : Mem 64 → Prop)
    (hbs : bsMem.length ≤ maxMem) (hargs : (T.toIsa.assignArgs f.as).isSome = true)
    {Q : Post [i64]}
    (hspec : Γ f.name f.as [i64] args (bsMem.At 0x1000#64) Q (fun _ _ _ _ => False))
    (hQ : ∀ rets m', Q rets m' → rets = (v, ()) ∧ P m')
    (hbound : maxBound ≤ maxStack := by omega) :
    InlRet1SepEv cert I f bsMem args v P := by
  have hfn := (cert.fnSpec_host_src_optInlinePolicy Γ hM hf has hrs hnoex).2
  rw [hret] at hfn
  exact cert.run_ret1_sep_i64 I hfn bsMem args v P hbs hargs hspec hQ hbound

/-- `LegalSigAll` specialization of `eventually_ret1_sep_i64_optInlinePolicy`. -/
theorem eventually_ret1_sep_i64_of_legalSigAll_optInlinePolicy
    (cert : LinkedCert T L lt hcl (mod.optInlinePolicy policy) [] exits nX maxBound)
    (I : TargetInit T maxStack maxMem) (Γ : Env) (hM : ModuleOk Γ mod)
    (hleg : LegalSigAll lt mod.fns) {f : Fn} (hf : f ∈ mod.fns) (hret : f.rs = [i64])
    (hnoex : InlNoExit Γ f) (bsMem : List UInt8) (args : Tup Val f.as)
    (v : Val i64) (P : Mem 64 → Prop) (hbs : bsMem.length ≤ maxMem)
    (hargs : (T.toIsa.assignArgs f.as).isSome = true) {Q : Post [i64]}
    (hspec : Γ f.name f.as [i64] args (bsMem.At 0x1000#64) Q (fun _ _ _ _ => False))
    (hQ : ∀ rets m', Q rets m' → rets = (v, ()) ∧ P m')
    (hbound : maxBound ≤ maxStack := by omega) :
    InlRet1SepEv cert I f bsMem args v P :=
  have ⟨has, hrs⟩ := hleg f hf
  cert.eventually_ret1_sep_i64_optInlinePolicy I Γ hM hf hret has hrs hnoex
    bsMem args v P hbs hargs hspec hQ hbound

/-- Non-exiting `i64`-returning `Eventually` theorem projecting `I.ra0` and `I.ret0`. -/
theorem eventually_ret1_i64_optInlinePolicy
    (cert : LinkedCert T L lt hcl (mod.optInlinePolicy policy) [] exits nX maxBound)
    (I : TargetInit T maxStack maxMem) (Γ : Env) (hM : ModuleOk Γ mod)
    {f : Fn} (hf : f ∈ mod.fns) (hret : f.rs = [i64])
    (has : lt.legalSig f.as = f.as) (hrs : lt.legalSig f.rs = f.rs) (hnoex : InlNoExit Γ f)
    (bsMem : List UInt8) (args : Tup Val f.as) (v : Val i64) (hbs : bsMem.length ≤ maxMem)
    (hargs : (T.toIsa.assignArgs f.as).isSome = true) {Q : Post [i64]}
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
    (has : lt.legalSig f.as = f.as) (hrs : lt.legalSig f.rs = f.rs) (hnoex : InlNoExit Γ f)
    (bsMem : List UInt8) (args : Tup Val f.as) (v : Val i64) (P : Mem 64 → Prop)
    (hbs : bsMem.length ≤ maxMem) (hargs : (T.toIsa.assignArgs f.as).isSome = true)
    {Q : Post [i64]}
    (hspec : Γ f.name f.as [i64] args (bsMem.At 0x1000#64) Q (fun _ _ _ _ => False))
    (hQ : ∀ rets m', Q rets m' → rets = (v, ()) ∧ P m')
    (hbound : maxBound ≤ maxStack := by omega) :
    InlRet1SepEv cert I f bsMem args v P :=
  cert.eventually_ret1_sep_i64_optInlinePolicy I Γ hM hf hret has hrs hnoex
    bsMem args v P hbs hargs hspec hQ hbound

end ConcreteInit

end LinkedCert

/-! ### Raw `compileModuleOptInlinePolicy` & Fixed-Stack Execution Helpers -/

private theorem fn_mem_eq_of_nodup :
    ∀ {fs : List Fn} {f₁ f₂ : Fn},
      (fs.map Fn.name).Nodup → f₁ ∈ fs → f₂ ∈ fs → f₁.name = f₂.name → f₁ = f₂
  | [], _, _, _, h1, _, _ => nomatch h1
  | _ :: _, f₁, f₂, hnd, h1, h2, hnm => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp h1 with rfl | h1' <;> rcases List.mem_cons.mp h2 with rfl | h2'
    · rfl
    · exact absurd (hnm ▸ List.mem_map_of_mem h2') hnd.1
    · exact absurd (hnm.symm ▸ List.mem_map_of_mem h1') hnd.1
    · exact fn_mem_eq_of_nodup hnd.2 h1' h2' hnm

/-- Raw `compileModuleOptInlinePolicy` soundness bridge to `T.Defined ∧ T.FnSpec` over any
host `host` containing `code` at `k₀` (zero `LinkedCert` or `TargetLayout` dependency). -/
theorem fnSpec_of_compileModuleOptInlinePolicy
    {T : Target} {lt : LegalTarget} {M : Module} {Γ : Env} {policy : InlinePolicy}
    {hints : List T.toIsa.Hints} {code : List T.Directive} {bounds : List (Sym × Nat)}
    (host : T.mach.Host) (k₀ : Nat)
    (hcm : compileModuleOptInlinePolicy T.toIsa lt T.frame.raBytes [] [] 0
      M hints policy = .ok (code, bounds))
    (hc : code.IsInfixAt (T.mach.prog host) k₀) (hu : T.LabelsUnique host)
    (hM : ModuleOk Γ M) (hleg : LegalSigAll lt M.fns)
    {f : Fn} (hf : f ∈ M.fns) (hnoex : InlNoExit Γ f)
    {b : Nat} (hb : (f.name, b) ∈ bounds) :
    T.Defined host f.name ∧ T.FnSpec host f.name (Γ f.name f.as f.rs) b 0 := by
  have ⟨hacyc, hwf, hwp⟩ := moduleOk_parts hM
  have hsupp : ∀ g ∈ (M.optInlinePolicy policy).fns,
      (g.earlyOpt).body.supportsSource lt = true :=
    Compiled.compileModule_supportsSource hcm
  obtain ⟨f', hf', hnm, hdef, hspec⟩ :=
    compile_sound_optInlinePolicy T host lt M Γ [] [] 0 policy hints code bounds k₀
      hcm hc hu hacyc hwf hsupp hwp
      (fun _ h => nomatch h) ⟨(fun _ h => nomatch h), (fun _ h => nomatch h)⟩
      (fun _ h => nomatch h) (f.name, b) hb
  have hnd : (M.fns.map Fn.name).Nodup := (List.nodup_append.mp hM.nodup).1
  have heq : f' = f := fn_mem_eq_of_nodup hnd hf' hf hnm.symm
  subst heq
  have ⟨has, hrs⟩ := hleg f' hf'
  exact ⟨hdef, fnSpec_of_legalEnv_legalSig_eq_noExit has hrs
    (List.mem_append_left _ (List.mem_map_of_mem hf')) hnoex hspec⟩

/-- Fixed-`maxB` raw `compileModuleOptInlinePolicy` soundness bridge, discharging stack
monotonicity via `Target.FnSpec.mono_stack`. -/
theorem fnSpec_maxB_of_compileModuleOptInlinePolicy
    {T : Target} {lt : LegalTarget} {M : Module} {Γ : Env} {policy : InlinePolicy}
    {hints : List T.toIsa.Hints} {code : List T.Directive} {bounds : List (Sym × Nat)}
    {maxB : Nat} (host : T.mach.Host) (k₀ : Nat)
    (hcm : compileModuleOptInlinePolicy T.toIsa lt T.frame.raBytes [] [] 0
      M hints policy = .ok (code, bounds))
    (hc : code.IsInfixAt (T.mach.prog host) k₀) (hu : T.LabelsUnique host)
    (hM : ModuleOk Γ M) (hleg : LegalSigAll lt M.fns)
    {f : Fn} (hf : f ∈ M.fns) (hnoex : InlNoExit Γ f)
    (hble : ∀ p ∈ bounds, p.2 ≤ maxB) (hmax : maxB + T.frame.raBytes ≤ 2 ^ 64) :
    T.Defined host f.name ∧ T.FnSpec host f.name (Γ f.name f.as f.rs) maxB 0 := by
  have hbn : bounds.map Prod.fst = (M.optInlinePolicy policy).fns.map Fn.name :=
    compileModule_bounds_names hcm
  have hnm_eq : (M.optInlinePolicy policy).fns.map Fn.name = M.fns.map Fn.name := by
    have h := Module.optInlinePolicy_names M policy
    simp only [Module.names, Module.optInlinePolicy_externs] at h
    exact List.append_cancel_right h
  have hmem : f.name ∈ bounds.map Prod.fst :=
    hbn ▸ hnm_eq ▸ List.mem_map_of_mem hf
  obtain ⟨⟨_, b⟩, hb, hnm⟩ := List.mem_map.mp hmem
  dsimp only at hnm
  subst hnm
  obtain ⟨hdef, hspec⟩ :=
    fnSpec_of_compileModuleOptInlinePolicy host k₀ hcm hc hu hM hleg hf hnoex hb
  exact ⟨hdef, Target.FnSpec.mono_stack T hspec (hble (f.name, b) hb) hmax⟩

/-- Arbitrary-host, arbitrary-bound (`n ≤ maxStack`) closed execution helper for non-exiting
`i64`-returning functions. -/
theorem run_ret1_sep_i64_at
    {T : Target} {maxStack maxMem : Nat} (I : TargetInit T maxStack maxMem)
    (h : T.mach.Host) {nm : Sym} {as : List Ty} {spec : Spec as [i64]} {n nX : Nat}
    (hf : T.FnSpec h nm spec n nX) (hn : n ≤ maxStack)
    (bsMem : List UInt8) (args : Tup Val as) (v : Val i64) (P : Mem 64 → Prop)
    (hbs : bsMem.length ≤ maxMem) (hargs : (T.toIsa.assignArgs as).isSome = true)
    {Q : Post [i64]} (hspec : spec args (bsMem.At 0x1000#64) Q (fun _ _ _ _ => False))
    (hQ : ∀ rets m', Q rets m' → rets = (v, ()) ∧ P m') :
    Eventually (T.mach.step h)
      (fun st => T.mach.pc st = I.ra0 ∧ T.mach.getGpr (T.mach.data st) I.ret0 = v ∧
        (T.mach.mem (T.mach.data st) =⋆ P ⋆ T.Exit I.sp0 n ⋆ Std.ExtHashMap.emp))
      (T.mach.mkState (I.initState n bsMem args) (T.mach.labelAddr h nm)) := by
  have hmem := I.mem_entry n bsMem args hn hbs
  rw [← I.get_sp n bsMem args] at hmem
  refine eventually_weaken _ _ _ _ ?_
    (hf args (bsMem.At 0x1000#64) Q (fun _ _ _ _ => False) hspec
      (I.initState n bsMem args) I.ra0 Std.ExtHashMap.emp (I.argsIn n bsMem args hargs)
      (I.raReg n bsMem args) (by rw [I.get_sp]; exact I.spEntry) hmem)
  rintro st (⟨hpc, rets, m', hq, hrets, _, hm'⟩ | ⟨_, _, _, _, hx, _⟩)
  · obtain ⟨rfl, hP⟩ := hQ rets m' hq
    rw [I.get_sp] at hm'
    exact ⟨hpc, I.retsIn_singleton v _ hrets,
      sep_mono (fun _ => sep_mono (fun _ e => e ▸ hP)) hm'⟩
  · exact hx.elim

end LeanQbe.T
