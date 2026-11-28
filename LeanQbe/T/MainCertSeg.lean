/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.MainCertSlices
public import LeanQbe.T.MainCertFlat
public import LeanQbe.T.MainCertInlineProof
public import LeanQbe.T.InlinePlanLemmas

/-!
# Subsystem-Aligned Compilation Certificate Assembler (`MainCertSeg`)

Position-free, subsystem-aligned analogue of `MainCertSlices.lean` composing per-subsystem
(`seg_cert!`) and heavy-function (`fn_cert!`) compilation certificates via `List.append` with
zero positional `drop`/`take` offsets:

* `SegChunks`: position-free chunk bundle covering `fns : List Fn` with `fns = chunksFns chunks`
  and `chunksMaxBound chunks ≤ maxBound`.
* `SegChunks.{empty, ofCert, ofCompiled, append, ofList, allFns, allChunks}` plus append/list
  lemmas for `chunksFns`, `chunksMaxBound`, and `supportsAll`.
* `CheckedSegGroup` + `LinkedCert.ofSegs` + `LinkedCert.ofCheckedSegGroups`: O(1)-boilerplate
  whole-module `LinkedCert` assembly (flat or 2-level parallel `checkChunksExt` tree).
* `LinkedCert.fnSpec_*_inlinePlan` and `LinkedCert.eventually_*_inlinePlan`: end-to-end
  source-level soundness and `TargetInit` `Eventually` lifts over `Module.inlinePlan`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T

/-! ## 1. `SegChunks`: position-free subsystem chunk bundle -/

/-- Position-free bundle of compiled chunks covering `fns : List Fn` with stack bound
`chunksMaxBound chunks ≤ maxBound`. -/
structure SegChunks (T : Target) (lt : LegalTarget) (exits : List Sym)
    (nX maxBound : Nat) where
  fns : List Fn
  chunks : List (CompiledChunk T lt exits nX)
  fns_eq : fns = chunksFns chunks
  maxBound_le : chunksMaxBound chunks ≤ maxBound

namespace SegChunks

variable {T : Target} {lt : LegalTarget} {exits : List Sym} {nX maxBound : Nat}

/-- Empty `SegChunks` covering `[]`. -/
@[expose] def empty : SegChunks T lt exits nX maxBound where
  fns := []
  chunks := []
  fns_eq := rfl
  maxBound_le := chunksMaxBound_nil

/-- Wrap a single `Compiled` certificate into a 1-chunk `SegChunks`. -/
@[expose] noncomputable def ofCompiled {extK : List (SigEntry × Nat)}
    {fs : List Fn} {hints : List T.toIsa.Hints}
    (c : Compiled T lt extK exits nX fs hints maxBound) :
    SegChunks T lt exits nX maxBound where
  fns := fs
  chunks := [⟨extK, fs, hints, maxBound, c⟩]
  fns_eq := (List.append_nil fs).symm
  maxBound_le := chunksMaxBound_cons (Nat.le_refl maxBound) chunksMaxBound_nil

/-- Wrap a per-subsystem `LinkedCert` into a `SegChunks` (optionally rewriting `segMod.fns`). -/
@[expose] noncomputable def ofCert {L : TargetLayout T} {hcl : Rega.LabelClean T.toIsa}
    {segMod : Module} {extK : List (SigEntry × Nat)}
    (cert : LinkedCert T L lt hcl segMod extK exits nX maxBound)
    {fns : List Fn} (hfns : fns = segMod.fns := by rfl) :
    SegChunks T lt exits nX maxBound where
  fns := fns
  chunks := cert.chunks
  fns_eq := hfns.trans cert.fns_eq
  maxBound_le := cert.maxBound_le

/-- Concatenate two `SegChunks` without positional offsets. -/
@[expose] noncomputable def append
    (s₁ s₂ : SegChunks T lt exits nX maxBound) :
    SegChunks T lt exits nX maxBound where
  fns := s₁.fns ++ s₂.fns
  chunks := s₁.chunks ++ s₂.chunks
  fns_eq := by rw [s₁.fns_eq, s₂.fns_eq, chunksFns_append]
  maxBound_le := by
    rw [chunksMaxBound_append]
    exact Nat.max_le.mpr ⟨s₁.maxBound_le, s₂.maxBound_le⟩

/-- Right-associated concatenation of segment function lists (`s.fns ++ ...`). -/
@[expose] def allFns : List (SegChunks T lt exits nX maxBound) → List Fn
  | [] => []
  | s :: rest => s.fns ++ allFns rest

/-- Right-associated concatenation of segment chunk lists (`s.chunks ++ ...`). -/
@[expose] def allChunks :
    List (SegChunks T lt exits nX maxBound) → List (CompiledChunk T lt exits nX)
  | [] => []
  | s :: rest => s.chunks ++ allChunks rest

theorem allFns_append (ss₁ ss₂ : List (SegChunks T lt exits nX maxBound)) :
    allFns (ss₁ ++ ss₂) = allFns ss₁ ++ allFns ss₂ := by
  induction ss₁ with
  | nil => rfl
  | cons s rest ih =>
      dsimp only [List.cons_append, allFns]
      rw [ih, List.append_assoc]

theorem allChunks_append (ss₁ ss₂ : List (SegChunks T lt exits nX maxBound)) :
    allChunks (ss₁ ++ ss₂) = allChunks ss₁ ++ allChunks ss₂ := by
  induction ss₁ with
  | nil => rfl
  | cons s rest ih =>
      dsimp only [List.cons_append, allChunks]
      rw [ih, List.append_assoc]

theorem allFns_eq_chunksFns :
    ∀ (segs : List (SegChunks T lt exits nX maxBound)),
      allFns segs = chunksFns (allChunks segs)
  | [] => rfl
  | s :: rest => by
      dsimp only [allFns, allChunks]
      rw [chunksFns_append, s.fns_eq, allFns_eq_chunksFns rest]

theorem maxBound_allChunks :
    ∀ (segs : List (SegChunks T lt exits nX maxBound)),
      chunksMaxBound (allChunks segs) ≤ maxBound
  | [] => chunksMaxBound_nil
  | s :: rest => by
      dsimp only [allChunks]
      rw [chunksMaxBound_append]
      exact Nat.max_le.mpr ⟨s.maxBound_le, maxBound_allChunks rest⟩

theorem supportsAll_seg (s : SegChunks T lt exits nX maxBound) :
    ∀ f ∈ s.fns, (f.earlyOpt).body.supportsSource lt = true :=
  supportsAll_of_eq s.fns_eq (supportsAll_of_chunks s.chunks)

theorem supportsAll_allFns (segs : List (SegChunks T lt exits nX maxBound)) :
    ∀ f ∈ allFns segs, (f.earlyOpt).body.supportsSource lt = true :=
  supportsAll_of_eq (allFns_eq_chunksFns segs) (supportsAll_of_chunks (allChunks segs))

/-- Combine a list of `SegChunks` (e.g. a subsystem and its isolated heavy `fn_cert!` pieces)
into a single `SegChunks` with `fns := allFns segs`. -/
@[expose] noncomputable def ofList (segs : List (SegChunks T lt exits nX maxBound)) :
    SegChunks T lt exits nX maxBound where
  fns := allFns segs
  chunks := allChunks segs
  fns_eq := allFns_eq_chunksFns segs
  maxBound_le := maxBound_allChunks segs

/-- Transport `SegChunks.fns` along a definitional or proved equality `hfns : fns' = s.fns`. -/
@[expose] noncomputable def castFns (s : SegChunks T lt exits nX maxBound)
    {fns' : List Fn} (hfns : fns' = s.fns) :
    SegChunks T lt exits nX maxBound where
  fns := fns'
  chunks := s.chunks
  fns_eq := hfns.trans s.fns_eq
  maxBound_le := s.maxBound_le

end SegChunks

/-! ## 2. 2-Level Balanced `CheckedSegGroup` Tree -/

/-- Super-group pairing a `SegChunks` with its independently checked `checkChunksExt` witness
for 2-level parallel linking over subsystems. -/
structure CheckedSegGroup (T : Target) (lt : LegalTarget) (exits : List Sym)
    (nX maxBound : Nat) where
  seg : SegChunks T lt exits nX maxBound
  extIn : List (SigEntry × Nat)
  extOk : checkChunksExt extIn seg.chunks = true

namespace CheckedSegGroup

variable {T : Target} {lt : LegalTarget} {exits : List Sym} {nX maxBound : Nat}

/-- Definitional accumulator-threading predicate across `CheckedSegGroup`s. -/
@[expose] def chainedFrom (acc : List (SigEntry × Nat)) :
    List (CheckedSegGroup T lt exits nX maxBound) → Prop
  | [] => True
  | g :: rest =>
      g.extIn = acc ∧
      chainedFrom (chunksNextExt acc g.seg.chunks) rest

theorem checkChunksExt_allChunks :
    ∀ (groups : List (CheckedSegGroup T lt exits nX maxBound))
      (acc : List (SigEntry × Nat)),
      chainedFrom acc groups →
      checkChunksExt acc (SegChunks.allChunks (groups.map (·.seg))) = true
  | [], _, _ => rfl
  | g :: rest, acc, ⟨heq, hrest⟩ => by
      change checkChunksExt acc
        (g.seg.chunks ++ SegChunks.allChunks (rest.map (·.seg))) = true
      rw [checkChunksExt_append]
      simp only [Bool.and_eq_true]
      exact ⟨heq ▸ g.extOk, checkChunksExt_allChunks rest (chunksNextExt acc g.seg.chunks) hrest⟩

end CheckedSegGroup

/-! ## 3. `LinkedCert.ofSegs`, `ofCheckedSegGroups`, and `inlinePlan` Soundness Bridges -/

namespace LinkedCert

variable {T : Target} {L : TargetLayout T} {lt : LegalTarget}
  {hcl : Rega.LabelClean T.toIsa} {mod : Module} {plan : InlPlan}
  {ext₀ : List (SigEntry × Nat)} {exits : List Sym} {nX maxBound : Nat}

/-- Assemble a whole-module `LinkedCert` from subsystem `SegChunks` in `O(#segs)` with zero
positional indices. -/
@[expose] noncomputable def ofSegs
    (segs : List (SegChunks T lt exits nX maxBound))
    (hfns : mod.fns = SegChunks.allFns segs)
    (hlink : checkLinkList L ext₀ (SegChunks.allChunks segs) = true) :
    LinkedCert T L lt hcl mod ext₀ exits nX maxBound where
  chunks := SegChunks.allChunks segs
  linkCheck := hlink
  fns_eq := hfns.trans (SegChunks.allFns_eq_chunksFns segs)
  supportsAll := supportsAll_of_eq hfns (SegChunks.supportsAll_allFns segs)
  maxBound_le := SegChunks.maxBound_allChunks segs

/-- Assemble a whole-module `LinkedCert` from a 2-level list of `CheckedSegGroup`s whose
per-group `checkChunksExt` proofs run independently in parallel. -/
@[expose] noncomputable def ofCheckedSegGroups
    (groups : List (CheckedSegGroup T lt exits nX maxBound))
    (hfns : mod.fns = SegChunks.allFns (groups.map (·.seg)))
    (hchain : CheckedSegGroup.chainedFrom ext₀ groups)
    (hmeta : checkLinkMeta L (SegChunks.allChunks (groups.map (·.seg))) = true) :
    LinkedCert T L lt hcl mod ext₀ exits nX maxBound :=
  ofSegs (groups.map (·.seg)) hfns
    (checkLinkList_of_checkChunksExt
      (CheckedSegGroup.checkChunksExt_allChunks groups ext₀ hchain) hmeta)

/-- Lift a `LinkedCert` over `mod.inlinePlan plan` and source `ModuleOk Γ mod` to
`T.Defined ∧ T.FnSpec` over any host `h` containing `cert.code` at `k₀`. -/
theorem fnSpec_inlinePlan
    (cert : LinkedCert T L lt hcl (mod.inlinePlan plan) ext₀ exits nX maxBound)
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
  exact cert.compiled.fnSpec_inlinePlan mod plan cert.fns_eq h Γ k₀ hc hu
    hacyc hwf cert.supportsAll hwp hext hext_uniq hexits hf

/-- Self-contained `Defined` + `FnSpec` on `cert.host` (`ext₀ = []`) for `inlinePlan`. -/
theorem fnSpec_host_inlinePlan
    (cert : LinkedCert T L lt hcl (mod.inlinePlan plan) [] exits nX maxBound)
    (Γ : Env) (hM : ModuleOk Γ mod) {f : Fn} (hf : f ∈ mod.fns) :
    InlOutSpec T cert.host lt mod Γ f.name f (cert.bound f.name) nX :=
  cert.fnSpec_inlinePlan cert.host Γ 0 cert.code_infix_host cert.labelsUnique hM
    (fun _ h => nomatch h) ⟨(fun _ h => nomatch h), (fun _ h => nomatch h)⟩
    (fun _ hg => cert.defined_exit_host hg) hf

/-- Source-level `Defined` + `FnSpec` on `cert.host` (`ext₀ = []`) when `lt.legalSig` fixes
`(f.as, f.rs)` and `Γ` ignores exits. -/
theorem fnSpec_host_src_inlinePlan
    (cert : LinkedCert T L lt hcl (mod.inlinePlan plan) [] exits nX maxBound)
    (Γ : Env) (hM : ModuleOk Γ mod) {f : Fn} (hf : f ∈ mod.fns)
    (has : lt.legalSig f.as = f.as) (hrs : lt.legalSig f.rs = f.rs) (hnoex : InlNoExit Γ f) :
    T.Defined cert.host f.name ∧
      T.FnSpec cert.host f.name (Γ f.name f.as f.rs) (cert.bound f.name) nX := by
  obtain ⟨hdef, hspec⟩ := cert.fnSpec_host_inlinePlan Γ hM hf
  exact ⟨hdef, fnSpec_of_legalEnv_legalSig_eq_noExit has hrs
    (List.mem_append_left _ (List.mem_map_of_mem hf)) hnoex hspec⟩

/-- `LegalSigAll` specialization of `fnSpec_host_src_inlinePlan`. -/
theorem fnSpec_host_of_legalSigAll_inlinePlan
    (cert : LinkedCert T L lt hcl (mod.inlinePlan plan) [] exits nX maxBound)
    (Γ : Env) (hM : ModuleOk Γ mod) (hleg : LegalSigAll lt mod.fns)
    {f : Fn} (hf : f ∈ mod.fns) (hnoex : InlNoExit Γ f) :
    T.Defined cert.host f.name ∧
      T.FnSpec cert.host f.name (Γ f.name f.as f.rs) (cert.bound f.name) nX :=
  have ⟨has, hrs⟩ := hleg f hf
  cert.fnSpec_host_src_inlinePlan Γ hM hf has hrs hnoex

/-- Arbitrary-host `FnSpec` over `mod.inlinePlan plan` (`ext₀ = []`, `exits = []`). -/
theorem fnSpec_noExit_id_inlinePlan
    (cert : LinkedCert T L lt hcl (mod.inlinePlan plan) [] [] nX maxBound)
    (h : T.mach.Host) (Γ : Env) (k₀ : Nat)
    (hc : cert.code.IsInfixAt (T.mach.prog h) k₀) (hu : T.LabelsUnique h)
    (hM : ModuleOk Γ mod) {f : Fn} (hf : f ∈ mod.fns)
    (has : lt.legalSig f.as = f.as) (hrs : lt.legalSig f.rs = f.rs) (hnoex : InlNoExit Γ f) :
    T.Defined h f.name ∧ T.FnSpec h f.name (Γ f.name f.as f.rs) (cert.bound f.name) nX := by
  have ⟨hacyc, hwf, hwp⟩ := moduleOk_parts hM
  exact cert.compiled.fnSpec_noExit_id_inlinePlan mod plan cert.fns_eq h Γ k₀ hc hu
    hacyc hwf cert.supportsAll hwp hf has hrs hnoex

/-- `LegalSigAll` specialization of `fnSpec_noExit_id_inlinePlan`. -/
theorem fnSpec_noExit_of_legalSigAll_inlinePlan
    (cert : LinkedCert T L lt hcl (mod.inlinePlan plan) [] [] nX maxBound)
    (h : T.mach.Host) (Γ : Env) (k₀ : Nat)
    (hc : cert.code.IsInfixAt (T.mach.prog h) k₀) (hu : T.LabelsUnique h)
    (hM : ModuleOk Γ mod) (hleg : LegalSigAll lt mod.fns) {f : Fn} (hf : f ∈ mod.fns)
    (hnoex : InlNoExit Γ f) :
    T.Defined h f.name ∧ T.FnSpec h f.name (Γ f.name f.as f.rs) (cert.bound f.name) nX :=
  have ⟨has, hrs⟩ := hleg f hf
  cert.fnSpec_noExit_id_inlinePlan h Γ k₀ hc hu hM hf has hrs hnoex

section ConcreteInit

variable {maxStack maxMem : Nat}

/-- Non-exiting `i64`-returning `Eventually` theorem on `cert.host` for `mod.inlinePlan plan`. -/
theorem eventually_ret1_sep_i64_inlinePlan
    (cert : LinkedCert T L lt hcl (mod.inlinePlan plan) [] exits nX maxBound)
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
  have hfn := (cert.fnSpec_host_src_inlinePlan Γ hM hf has hrs hnoex).2
  rw [hret] at hfn
  exact cert.run_ret1_sep_i64 I hfn bsMem args v P hbs hargs hspec hQ hbound

/-- Non-exiting `i64`-returning `Eventually` theorem projecting `I.ra0` and `I.ret0`. -/
theorem eventually_ret1_i64_inlinePlan
    (cert : LinkedCert T L lt hcl (mod.inlinePlan plan) [] exits nX maxBound)
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
    (cert.eventually_ret1_sep_i64_inlinePlan I Γ hM hf hret has hrs hnoex
      bsMem args v (fun _ => True) hbs hargs hspec
      (fun rets m' hm' => ⟨hQ rets m' hm', trivial⟩) hbound)

end ConcreteInit

end LinkedCert

/-! ## 4. Staged Per-Pass `compileModuleFlat` Kernel Bridge Lemmas -/

/-- Zero-peel configuration used by `earlyOptFlat` (`peelBudget := 24`). -/
@[expose] def stagedZpCfg24 : ZeroPeelConfig := { peelBudget := 24 }

/-- Decompose `earlyOptFlat f` into two kernel-checkable pass stages (`t0` and `t1`). -/
theorem earlyOptFlat_eq {f : TFlatFn} {t0 t1 : TFlat f.rs}
    (h0 : OptFlatValue.foldFlat f.as (OptFlatValue.copyFlat f.as
      (OptFlatValue.gvnFlat f.as (OptFlatValue.copyFlat f.as
        (OptFlatValue.canonFlat f.as (OptFlatValue.foldFlat f.as f.body))))) = t0)
    (h1 : OptFlatCfg.dcePFlat f.as (OptFlatValue.foldFlat f.as (OptFlatValue.copyFlat f.as
      (TFlat.zeroPeelWith stagedZpCfg24
        (peelFastFlat f.as (simplifyGroupFastFlat f.as
          (OptFlatCfg.ifOptFlat false f.as t0)) 24)))) = t1) :
    earlyOptFlat f = ⟨f.name, f.as, f.rs, t1⟩ := by
  dsimp only [earlyOptFlat]
  dsimp only [stagedZpCfg24] at h1
  rw [h0, h1]

/-- Decompose `midStageFlat lt ef` into 13 kernel-checkable per-pass equalities. -/
theorem midStageFlat_eq {lt : LegalTarget} {ef : TFlatFn}
    {t0 t1 t2a t2b t2 t3a t3b t3 t4a t4 t5a t5b t5 : TFlat (lt.legalSig ef.rs)}
    (h0 : legalFlat lt (as := ef.as) ef.body = t0)
    (h1 : OptFlatValue.copyFlat (lt.legalSig ef.as) (OptFlatMem.divConstFlat (lt.legalSig ef.as)
      (OptFlatValue.canonFlat (lt.legalSig ef.as)
        (OptFlatValue.foldFlat (lt.legalSig ef.as) t0))) = t1)
    (h2a : OptFlatMem.memLoadFlat (lt.legalSig ef.as) t1 = t2a)
    (h2b : OptFlatValue.gvnFlat (lt.legalSig ef.as) t2a = t2b)
    (h2 : OptFlatValue.foldFlat (lt.legalSig ef.as)
      (OptFlatMem.assumeBitsFlat (lt.legalSig ef.as) t2b) = t2)
    (h3a : OptFlatValue.foldFlat (lt.legalSig ef.as) (assumeElimFlat
      (OptFlatCfg.deadLoadElimFlat (lt.legalSig ef.as)
        (simplifyGroupFastFlat (lt.legalSig ef.as)
          (OptFlatCfg.ifOptFlat true (lt.legalSig ef.as) t2)))) = t3a)
    (h3b : addrRangeOptFlatWith lt.foldAddrDisp (lt.legalSig ef.as) t3a = t3b)
    (h3 : OptFlatValue.gvnFlat (lt.legalSig ef.as) t3b = t3)
    (h4a : OptFlatCfg.dcePFlat (lt.legalSig ef.as) (licmFlat (lt.legalSig ef.as) t3) = t4a)
    (h4 : loopRotateFlat (lt.legalSig ef.as) t4a = t4)
    (h5a : pathCondOptFlat (lt.legalSig ef.as) t4 = t5a)
    (h5b : condThreadPassFlat (lt.legalSig ef.as) t5a = t5b)
    (h5 : mergeRetsFlat (tailDupFlat (lt.legalSig ef.as) (OptFlatCfg.dcePFlat (lt.legalSig ef.as)
      (OptFlatValue.foldFlat (lt.legalSig ef.as) t5b)) TailDup.defaultConfig) = t5) :
    midStageFlat lt ef = ⟨ef.name, lt.legalSig ef.as, lt.legalSig ef.rs, t5⟩ := by
  dsimp only [midStageFlat, condThreadLateOptFlat]
  dsimp only [TailDup.defaultConfig] at h5
  rw [h0, h1, h2a, h2b, h2, h3a, h3b, h3, h4a, h4, h5a, h5b, h5]

/-- Assemble a singleton `compileModuleFlat` certificate from staged per-stage equalities. -/
theorem compileModuleFlat_single
    {I : Isa} {lt : LegalTarget} {raBytes : Nat}
    {extCallees : List (SigEntry × Nat)} {exits : List Sym} {nX : Nat}
    {f ef mf : TFlatFn} {h : I.Hints} {ext : Rega.Ext}
    {code : List I.Directive} {b : Nat}
    (hwf : f.wfCheck = true)
    (hef : earlyOptFlat f = ef)
    (hsupp : ef.supportsSource lt = true)
    (hmf : midStageFlat lt ef = mf)
    (hext : TFlat.ext mf.body = ext)
    (hlow : Rega.lowerFlatFn I h ext mf = .ok code)
    (hbnd : checkAndBoundExt I raBytes exits nX extCallees h ext = some b) :
    compileModuleFlat I lt raBytes extCallees exits nX [f] [h] =
      .ok (code, [(f.name, b)]) := by
  dsimp only [compileModuleFlat]
  rw [hwf, hef, hsupp, hmf, hext, hlow, hbnd]
  simp

end LeanQbe.T
