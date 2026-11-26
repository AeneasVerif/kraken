module

public import LeanQbe.T.LeanLCNF.LcnfC0Full
public import LeanQbe.T.LeanLCNF.LcnfC0FullProof
public import LeanQbe.T.MainCertProof
public import LeanQbe.T.AbiLemmas

/-!
# Target-Generic Linking Kit for Verified Lean `LCNF` Programs (`LcnfC0LinkKit`)

Architecture-free (`0` `Amd64`/`Arm64`/`Kraken.X64`/`Kraken.AArch64` imports) compositional
linking harness connecting any Lean `LCNF` program lowered via `lcnf_of_lean!` +
`splice_lcnf_tflat!` with the unified 86-function pure-C0 runtime (`rtC0CoreMod`):

1. **Module & signature helpers**: `lcnfProgMod`, `linkLcnfWithRtC0_fns_eq`,
   `linkLcnfWithRtC0_fns_wf`, `linkLcnfWithRtC0_legalSigAll`, and
   `lcnfProgMod_disjoint_rt_of_nodup`.
2. **`ModuleOk` composition**: `linkRtC0Env progEnv` combining `rtC0CoreEnv` (for all runtime
   callees) with `progEnv` (for user declarations), `rtC0Core_fn_wp_linkEnv` transferring
   `rtC0CoreMod_fn_sound` along `callsOk`, and `linkLcnfWithRtC0_moduleOk`.
3. **Target-generic certificate & `FnSpec` bridge**: `linkRtC0Cert` wrapping
   `LinkedCert.append`, `linkRtC0Cert_fnSpec`, `linkRtC0Cert_fnSpec_of_spec`, and
   `linkRtC0Cert_rt_fnSpec` for any `T : Target`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.LeanLCNF

open LeanQbe.T
open LeanQbe.T.Frontend.C0 (TFlatFn)

/-! ## 1. Linked Module Shape, Well-Formedness, & Signature Legality -/

/-- Canonical list of all `86` runtime symbol names provided by `rtC0CoreMod`. -/
@[expose] def rtCoreFnNames : List Sym :=
  rtC0CoreMod.fns.map Fn.name

/-- Standalone user `Module` wrapping `tfs : List TFlatFn` with standard `rtExitSyms`. -/
@[expose] def lcnfProgMod (progTfs : List TFlatFn) : Module :=
  { fns := LeanLRC.tflatFnsToFns progTfs, externs := [], exits := rtExitSyms }

theorem linkLcnfWithRtC0_fns_eq (progTfs : List TFlatFn) :
    (linkLcnfWithRtC0 progTfs false).fns =
      rtC0CoreMod.fns ++ (lcnfProgMod progTfs).fns :=
  rfl

theorem linkLcnfWithRtC0_externs_eq (progTfs : List TFlatFn) :
    (linkLcnfWithRtC0 progTfs false).externs = [] :=
  rfl

theorem linkLcnfWithRtC0_exits_eq (progTfs : List TFlatFn) :
    (linkLcnfWithRtC0 progTfs false).exits = rtExitSyms :=
  rfl

theorem tflatFn_toFn_mem_progMod {progTfs : List TFlatFn} {tf : TFlatFn}
    (htf : tf ∈ progTfs) : tf.toFn ∈ (lcnfProgMod progTfs).fns :=
  List.mem_map_of_mem htf

theorem tflatFn_toFn_mem_linked {progTfs : List TFlatFn} {tf : TFlatFn}
    (htf : tf ∈ progTfs) : tf.toFn ∈ (linkLcnfWithRtC0 progTfs false).fns := by
  rw [linkLcnfWithRtC0_fns_eq]
  exact List.mem_append_right _ (tflatFn_toFn_mem_progMod htf)

theorem lcnfProgMod_fns_wf (progTfs : List TFlatFn) :
    ∀ f ∈ (lcnfProgMod progTfs).fns, f.Wf := by
  intro f hf
  obtain ⟨tf, _, rfl⟩ := List.mem_map.mp hf
  exact tf.toFn_wf

theorem linkLcnfWithRtC0_fns_wf (progTfs : List TFlatFn) :
    ∀ f ∈ (linkLcnfWithRtC0 progTfs false).fns, f.Wf := by
  intro f hf
  rw [linkLcnfWithRtC0_fns_eq, List.mem_append] at hf
  rcases hf with hrt | hprog
  · exact rtC0CoreMod_fns_wf f hrt
  · exact lcnfProgMod_fns_wf progTfs f hprog

theorem linkLcnfWithRtC0_legalSigAll (lt : LegalTarget) (progTfs : List TFlatFn)
    (hRt : checkLegalSigAll lt rtC0CoreMod.fns = true)
    (hProg : checkLegalSigAll lt (lcnfProgMod progTfs).fns = true) :
    LegalSigAll lt (linkLcnfWithRtC0 progTfs false).fns := by
  rw [linkLcnfWithRtC0_fns_eq]
  exact legalSigAll_append hRt (legalSigAll_of_check hProg)

theorem linkLcnfWithRtC0_nodup_of_checkAcyclic {progTfs : List TFlatFn}
    (hacyc : (linkLcnfWithRtC0 progTfs false).checkAcyclic = true) :
    (linkLcnfWithRtC0 progTfs false).namesNodup :=
  Module.namesNodup_of_checkNamesNodup ((Bool.and_eq_true _ _).mp hacyc).1

theorem lcnfProgMod_disjoint_rt_of_nodup {progTfs : List TFlatFn}
    (hnd : (linkLcnfWithRtC0 progTfs false).namesNodup) :
    ∀ f ∈ (lcnfProgMod progTfs).fns, f.name ∉ rtCoreFnNames := by
  intro f hf hmem
  have hnd' : ((rtC0CoreMod.fns ++ (lcnfProgMod progTfs).fns).map Fn.name).Nodup := by
    simpa [Module.namesNodup, Module.names, linkLcnfWithRtC0_fns_eq,
      linkLcnfWithRtC0_externs_eq] using hnd
  rw [List.map_append] at hnd'
  exact (List.nodup_append.mp hnd').2.2 f.name hmem f.name (List.mem_map_of_mem hf) rfl

/-! ## 2. Environment Composition (`linkRtC0Env`) & `ModuleOk` -/

/-- Partitioned combined specification environment: `rtC0CoreEnv` on all `rtC0CoreMod` symbols,
and `progEnv` on all remaining (user-program) symbols. -/
@[expose] def linkRtC0Env (progEnv : Env) : Env :=
  fun nm as rs xs m Q X =>
    if nm ∈ rtCoreFnNames then rtC0CoreEnv nm as rs xs m Q X
    else progEnv nm as rs xs m Q X

theorem linkRtC0Env_rt (progEnv : Env) {nm : Sym} (hmem : nm ∈ rtCoreFnNames)
    {as rs : List Ty} {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost} :
    linkRtC0Env progEnv nm as rs xs m Q X ↔ rtC0CoreEnv nm as rs xs m Q X := by
  simp only [linkRtC0Env, ite_eq_left hmem]

theorem linkRtC0Env_prog (progEnv : Env) {nm : Sym} (hmem : nm ∉ rtCoreFnNames)
    {as rs : List Ty} {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost} :
    linkRtC0Env progEnv nm as rs xs m Q X ↔ progEnv nm as rs xs m Q X := by
  simp only [linkRtC0Env, ite_eq_right hmem]

theorem linkRtC0Env_eq_or {progEnv : Env}
    (hRtOnly : ∀ nm as rs xs m Q X, rtC0CoreEnv nm as rs xs m Q X → nm ∈ rtCoreFnNames)
    (hProgOnly : ∀ nm as rs xs m Q X, progEnv nm as rs xs m Q X → nm ∉ rtCoreFnNames)
    {nm : Sym} {as rs : List Ty} {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost} :
    linkRtC0Env progEnv nm as rs xs m Q X ↔
      (rtC0CoreEnv nm as rs xs m Q X ∨ progEnv nm as rs xs m Q X) := by
  by_cases hmem : nm ∈ rtCoreFnNames
  · simp only [linkRtC0Env_rt progEnv hmem]
    exact ⟨Or.inl, fun h => h.elim id (fun hp => False.elim (hProgOnly _ _ _ _ _ _ _ hp hmem))⟩
  · simp only [linkRtC0Env_prog progEnv hmem]
    exact ⟨Or.inr, fun h => h.elim (fun hr => False.elim (hmem (hRtOnly _ _ _ _ _ _ _ hr))) id⟩

theorem linkRtC0Env_of_rt {progEnv : Env} {nm : Sym}
    (hmem : nm ∈ rtCoreFnNames := by decide)
    {as rs : List Ty} {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : rtC0CoreEnv nm as rs xs m Q X) :
    linkRtC0Env progEnv nm as rs xs m Q X :=
  (linkRtC0Env_rt progEnv hmem).mpr h

theorem linkRtC0Env_of_r1 {progEnv : Env} {nm : Sym}
    (hmem : nm ∈ rtCoreFnNames := by decide)
    {as rs : List Ty} {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : rtR1Env nm as rs xs m Q X) :
    linkRtC0Env progEnv nm as rs xs m Q X :=
  linkRtC0Env_of_rt hmem (rtR1Env_le_rtC0CoreEnv _ _ _ _ _ _ _ h)

theorem linkRtC0Env_of_r2 {progEnv : Env} {nm : Sym}
    (hmem : nm ∈ rtCoreFnNames := by decide)
    {as rs : List Ty} {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : rtR2Env nm as rs xs m Q X) :
    linkRtC0Env progEnv nm as rs xs m Q X :=
  linkRtC0Env_of_rt hmem (rtR2Env_le_rtC0CoreEnv _ _ _ _ _ _ _ h)

theorem linkRtC0Env_of_r2b {progEnv : Env} {nm : Sym}
    (hmem : nm ∈ rtCoreFnNames := by decide)
    {as rs : List Ty} {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : rtR2bEnv nm as rs xs m Q X) :
    linkRtC0Env progEnv nm as rs xs m Q X :=
  linkRtC0Env_of_rt hmem (rtR2bEnv_le_rtC0CoreEnv _ _ _ _ _ _ _ h)

/-- Any runtime function `fn ∈ rtC0CoreMod.fns` satisfies `Func.wp` against `linkRtC0Env progEnv`
via `wp_env_agree_of_callsOk`, since `rtC0CoreMod` is acyclic and `0`-extern closed. -/
theorem rtC0Core_fn_wp_linkEnv (progEnv : Env) {fn : Fn} (hfn : fn ∈ rtC0CoreMod.fns)
    {xs : Tup Val fn.as} {m : Mem 64} {Q : Post fn.rs} {X : XPost}
    (hpre : linkRtC0Env progEnv fn.name fn.as fn.rs xs m Q X) :
    Func.wp (linkRtC0Env progEnv) fn.body xs m Q X := by
  have hmemName : fn.name ∈ rtCoreFnNames := List.mem_map_of_mem hfn
  have hpreRt : rtC0CoreEnv fn.name fn.as fn.rs xs m Q X :=
    (linkRtC0Env_rt progEnv hmemName).mp hpre
  have hwpRt := rtC0CoreMod_fn_sound hfn hpreRt
  obtain ⟨pre, post, hsplit⟩ := List.mem_iff_append.mp hfn
  have hfnOk := rtC0CoreMod_moduleOk.fnsOk pre fn post hsplit
  refine wp_env_agree_of_callsOk
    (hfnOk.1 Val (fun _ => Unit) Cont (fun _ => Unit) xs (Tup.units fn.as))
    hfnOk.2.1 (fun g as bs hg => ?_) m hwpRt
  simp only [rtC0CoreMod, List.map_nil, List.append_nil] at hg
  obtain ⟨gf, hgf, hsig⟩ := List.mem_map.mp hg
  have hgName : g ∈ rtCoreFnNames := by
    have hgf' : gf ∈ rtC0CoreMod.fns := hsplit ▸ List.mem_append_left _ hgf
    have hnm : gf.name = g := congrArg Prod.fst hsig
    exact hnm ▸ List.mem_map_of_mem hgf'
  intro xs' m' P E hcall
  exact (linkRtC0Env_rt progEnv hgName).mpr hcall

/-- Whole-module `Func.wp` soundness across all functions in `linkLcnfWithRtC0 progTfs false`. -/
theorem linkLcnfWithRtC0_wp_all {progTfs : List TFlatFn} (progEnv : Env)
    (hacyc : (linkLcnfWithRtC0 progTfs false).checkAcyclic = true)
    (hprogWp : ∀ fn ∈ (lcnfProgMod progTfs).fns,
      ∀ xs m Q X, progEnv fn.name fn.as fn.rs xs m Q X →
        Func.wp (linkRtC0Env progEnv) fn.body xs m Q X) :
    ∀ fn ∈ (linkLcnfWithRtC0 progTfs false).fns,
      ∀ xs m Q X, linkRtC0Env progEnv fn.name fn.as fn.rs xs m Q X →
        Func.wp (linkRtC0Env progEnv) fn.body xs m Q X := by
  have hnd := linkLcnfWithRtC0_nodup_of_checkAcyclic hacyc
  have hdisj := lcnfProgMod_disjoint_rt_of_nodup hnd
  intro fn hfn xs m Q X hpre
  rw [linkLcnfWithRtC0_fns_eq, List.mem_append] at hfn
  rcases hfn with hrt | hprog
  · exact rtC0Core_fn_wp_linkEnv progEnv hrt hpre
  · have hnot := hdisj fn hprog
    exact hprogWp fn hprog xs m Q X ((linkRtC0Env_prog progEnv hnot).mp hpre)

/-- Compositional `ModuleOk` for `linkLcnfWithRtC0 progTfs false` under `linkRtC0Env progEnv`. -/
theorem linkLcnfWithRtC0_moduleOk {progTfs : List TFlatFn} (progEnv : Env)
    (hacyc : (linkLcnfWithRtC0 progTfs false).checkAcyclic = true)
    (hprogWp : ∀ fn ∈ (lcnfProgMod progTfs).fns,
      ∀ xs m Q X, progEnv fn.name fn.as fn.rs xs m Q X →
        Func.wp (linkRtC0Env progEnv) fn.body xs m Q X) :
    ModuleOk (linkRtC0Env progEnv) (linkLcnfWithRtC0 progTfs false) :=
  Module.moduleOk_of_checkAcyclic hacyc (linkLcnfWithRtC0_fns_wf progTfs)
    (linkLcnfWithRtC0_wp_all progEnv hacyc hprogWp)

/-! ## 3. Target-Generic `LinkedCert.append` & `Target.FnSpec` Bridge -/

/-- Append a compiled user `LinkedCert` onto any pre-verified `rtC0CoreMod` certificate over any
target `T : Target`. -/
@[expose] noncomputable def linkRtC0Cert
    {T : Target} {L : TargetLayout T} {lt : LegalTarget} {hcl : Rega.LabelClean T.toIsa}
    {progTfs : List TFlatFn} {rtExt : List (SigEntry × Nat)} {maxB₁ maxB₂ : Nat}
    (rtCert : LinkedCert T L lt hcl rtC0CoreMod [] rtExitSyms 64 maxB₁)
    (progCert : LinkedCert T L lt hcl (lcnfProgMod progTfs) rtExt rtExitSyms 64 maxB₂)
    (hchk : checkLinkList L [] (rtCert.chunks ++ progCert.chunks) = true) :
    LinkedCert T L lt hcl (linkLcnfWithRtC0 progTfs false) [] rtExitSyms 64
      (Nat.max maxB₁ maxB₂) :=
  rtCert.append progCert rfl hchk

/-- Source-signature `T.Defined` + `T.FnSpec` for any user function `f ∈ (lcnfProgMod progTfs).fns`
on a linked `linkLcnfWithRtC0 progTfs false` certificate. -/
theorem linkRtC0Cert_fnSpec
    {T : Target} {L : TargetLayout T} {lt : LegalTarget} {hcl : Rega.LabelClean T.toIsa}
    {progTfs : List TFlatFn} {maxB : Nat}
    (cert : LinkedCert T L lt hcl (linkLcnfWithRtC0 progTfs false) [] rtExitSyms 64 maxB)
    (progEnv : Env)
    (hacyc : (linkLcnfWithRtC0 progTfs false).checkAcyclic = true)
    (hleg : LegalSigAll lt (linkLcnfWithRtC0 progTfs false).fns)
    (hprogWp : ∀ fn ∈ (lcnfProgMod progTfs).fns,
      ∀ xs m Q X, progEnv fn.name fn.as fn.rs xs m Q X →
        Func.wp (linkRtC0Env progEnv) fn.body xs m Q X)
    {f : Fn} (hf : f ∈ (lcnfProgMod progTfs).fns)
    (hnoex : ∀ (args : Tup Val f.as) (m : Mem 64) (Q : Post f.rs) (X X' : XPost),
      progEnv f.name f.as f.rs args m Q X → progEnv f.name f.as f.rs args m Q X') :
    T.Defined cert.host f.name ∧
      T.FnSpec cert.host f.name (progEnv f.name f.as f.rs) (cert.bound f.name) 64 := by
  have hnd := linkLcnfWithRtC0_nodup_of_checkAcyclic hacyc
  have hnot := lcnfProgMod_disjoint_rt_of_nodup hnd f hf
  have hfLink : f ∈ (linkLcnfWithRtC0 progTfs false).fns := by
    rw [linkLcnfWithRtC0_fns_eq]
    exact List.mem_append_right _ hf
  have hres := cert.fnSpec_host_of_legalSigAll (linkRtC0Env progEnv) hacyc
    (linkLcnfWithRtC0_fns_wf progTfs) hleg (linkLcnfWithRtC0_wp_all progEnv hacyc hprogWp) hfLink
    (fun args m Q X X' h =>
      (linkRtC0Env_prog progEnv hnot).mpr
        (hnoex args m Q X X' ((linkRtC0Env_prog progEnv hnot).mp h)))
  refine ⟨hres.1, Target.FnSpec.of_spec T hres.2 fun args m Q X h => ?_⟩
  exact (linkRtC0Env_prog progEnv hnot).mpr h

/-- Specialization of `linkRtC0Cert_fnSpec` unwrapping `progEnv` into an explicit contract
`spec : Spec f.as f.rs`. -/
theorem linkRtC0Cert_fnSpec_of_spec
    {T : Target} {L : TargetLayout T} {lt : LegalTarget} {hcl : Rega.LabelClean T.toIsa}
    {progTfs : List TFlatFn} {maxB : Nat}
    (cert : LinkedCert T L lt hcl (linkLcnfWithRtC0 progTfs false) [] rtExitSyms 64 maxB)
    (progEnv : Env)
    (hacyc : (linkLcnfWithRtC0 progTfs false).checkAcyclic = true)
    (hleg : LegalSigAll lt (linkLcnfWithRtC0 progTfs false).fns)
    (hprogWp : ∀ fn ∈ (lcnfProgMod progTfs).fns,
      ∀ xs m Q X, progEnv fn.name fn.as fn.rs xs m Q X →
        Func.wp (linkRtC0Env progEnv) fn.body xs m Q X)
    {f : Fn} (hf : f ∈ (lcnfProgMod progTfs).fns)
    (hnoex : ∀ (args : Tup Val f.as) (m : Mem 64) (Q : Post f.rs) (X X' : XPost),
      progEnv f.name f.as f.rs args m Q X → progEnv f.name f.as f.rs args m Q X')
    {spec : Spec f.as f.rs}
    (hspec : ∀ args m Q X, spec args m Q X → progEnv f.name f.as f.rs args m Q X) :
    T.Defined cert.host f.name ∧
      T.FnSpec cert.host f.name spec (cert.bound f.name) 64 := by
  have ⟨hdef, hfn⟩ := linkRtC0Cert_fnSpec cert progEnv hacyc hleg hprogWp hf hnoex
  exact ⟨hdef, Target.FnSpec.of_spec T hfn hspec⟩

/-- Source-signature `T.Defined` + `T.FnSpec` for any runtime function `fn ∈ rtC0CoreMod.fns`
on a linked `linkLcnfWithRtC0 progTfs false` certificate. -/
theorem linkRtC0Cert_rt_fnSpec
    {T : Target} {L : TargetLayout T} {lt : LegalTarget} {hcl : Rega.LabelClean T.toIsa}
    {progTfs : List TFlatFn} {maxB : Nat}
    (cert : LinkedCert T L lt hcl (linkLcnfWithRtC0 progTfs false) [] rtExitSyms 64 maxB)
    (progEnv : Env)
    (hacyc : (linkLcnfWithRtC0 progTfs false).checkAcyclic = true)
    (hleg : LegalSigAll lt (linkLcnfWithRtC0 progTfs false).fns)
    (hprogWp : ∀ fn ∈ (lcnfProgMod progTfs).fns,
      ∀ xs m Q X, progEnv fn.name fn.as fn.rs xs m Q X →
        Func.wp (linkRtC0Env progEnv) fn.body xs m Q X)
    {fn : Fn} (hfn : fn ∈ rtC0CoreMod.fns)
    (hnoex : ∀ (args : Tup Val fn.as) (m : Mem 64) (Q : Post fn.rs) (X X' : XPost),
      rtC0CoreEnv fn.name fn.as fn.rs args m Q X →
        rtC0CoreEnv fn.name fn.as fn.rs args m Q X') :
    T.Defined cert.host fn.name ∧
      T.FnSpec cert.host fn.name (rtC0CoreEnv fn.name fn.as fn.rs) (cert.bound fn.name) 64 := by
  have hmem : fn.name ∈ rtCoreFnNames := List.mem_map_of_mem hfn
  have hfLink : fn ∈ (linkLcnfWithRtC0 progTfs false).fns := by
    rw [linkLcnfWithRtC0_fns_eq]
    exact List.mem_append_left _ hfn
  have hres := cert.fnSpec_host_of_legalSigAll (linkRtC0Env progEnv) hacyc
    (linkLcnfWithRtC0_fns_wf progTfs) hleg (linkLcnfWithRtC0_wp_all progEnv hacyc hprogWp) hfLink
    (fun args m Q X X' h =>
      (linkRtC0Env_rt progEnv hmem).mpr
        (hnoex args m Q X X' ((linkRtC0Env_rt progEnv hmem).mp h)))
  refine ⟨hres.1, Target.FnSpec.of_spec T hres.2 fun args m Q X h => ?_⟩
  exact (linkRtC0Env_rt progEnv hmem).mpr h

end LeanQbe.T.LeanLCNF
