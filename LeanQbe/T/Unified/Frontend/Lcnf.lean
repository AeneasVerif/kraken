module

public import LeanQbe.T.Unified.Driver
public import LeanQbe.T.Frontend.C0.ToFlat
public import LeanQbe.T.LeanLCNF.Lower1
public import LeanQbe.T.LeanLCNF.LcnfC0RtSpec
public import LeanQbe.T.LeanLRC.ToT
public import LeanQbe.T.Main
public import LeanQbe.T.MainLemmas
import LeanQbe.T.Unified.DriverLemmas
import LeanQbe.T.RegaLemmas
import LeanQbe.T.TargetLemmas
import LeanQbe.T.LeanLCNF.LcnfC0RtProof

/-!
# `LeanLCNF` Direct Frontend on `LeanQbe.T.Unified` (`Unified.Frontend.Lcnf`)

Arch-free `LeanQbe.T.Unified.Frontend` adapter for `LeanQbe.T.LeanLCNF` (`LcModule`, `lowerModule`,
`lcnfTModule`, `LeanLRC.tflatFnsToFns`, `LeanLRC.tflatFnsToFns_wf`, `rtR0Mod`, `rtC0Env`):

* `lcnfSrc` / `lcnfLower` / `lcnfCaps` / `lcnfFrontend`: pinned direct `Frontend` (`caps := {}`,
  `route (lcnfFrontend.caps _) = .direct`) with zero architecture imports (`Kraken.X64`,
  `Kraken.AArch64`, `LeanQbe.T.Amd64`, `LeanQbe.T.Arm64`-free).
* `lcnfModule : List TFlatFn → Module := LeanLCNF.lcnfTModule`, `lcnfFrontend_mapM`,
  `lcnfFrontend_mapM_wf`, `lcnfLcLower`, `lcnfTfsMid` / `lcnfModMid` (`_eq`, `_wf`, `_sound`).
* `lcnfTargetBackend`: shared arch-free `Unified.Backend` bridge over any `T : Target` (serving
  both `Amd64` and `Arm64` using only arch-free `Target`, `RegaLemmas`, `MainLemmas`, and
  `Unified.DriverLemmas`).
* End-to-end `unified lcnfFrontend` and `Compiled` theorems connecting `lcnfModule`, `Fn.mid`,
  `rtR0Mod`/`rtC0Env` (and general `ModuleOk Γ`), `Target.FnSpec`, and `TargetInit.run_fnSpec`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Unified

open LeanQbe.T
open LeanQbe.T.LeanLCNF

/-! ## 1. `lcnfSrc`, `lcnfFrontend`, and `lcnfModule` -/

/-- Package an `Env` and a function symbol into a per-function `SSpec`. -/
@[expose] def lcnfSSpec (Γ : Env) (nm : Sym) : SSpec where
  Γ := Γ
  C := Γ nm

theorem ssa_sat_lcnfSSpec (Γ : Env) (fn : Fn) :
    ssa.Sat fn (lcnfSSpec Γ fn.name) ↔
      ∀ xs m Q X, Γ fn.name fn.as fn.rs xs m Q X → Func.spec Γ fn.body xs m Q X :=
  Iff.rfl

/-- Source tier for `LeanLCNF` functions lowered via `lowerModule` (`Frontend.C0.TFlatFn`). -/
@[expose] def lcnfSrc : Tier.{0, 1} where
  Prog := Frontend.C0.TFlatFn
  Ok _ := True
  Spec := SSpec
  top := ssa.top
  Sat tf s := ssa.Sat tf.toFn s

/-- Checked lowering stage from `lcnfSrc` into `ssa` via `TFlatFn.toFn` (`TFlatFn.toFn_wf`). -/
@[expose] def lcnfLower : Stage lcnfSrc ssa where
  run tf := .ok tf.toFn
  tr _ s := s
  ok tf q _ h := by cases h; exact tf.toFn_wf
  sound tf q s _ h hs := by cases h; exact hs

/-- Pinned empty capability summary (`{}`) routing every `LeanLCNF` function directly. -/
@[expose] def lcnfCaps (_ : Frontend.C0.TFlatFn) : Caps := {}

/-- Pinned direct `Frontend` for `LeanLCNF` (`caps := fun _ => {}`). -/
@[expose] def lcnfFrontend : Frontend.{0, 1} :=
  ⟨lcnfSrc, lcnfCaps, lcnfLower⟩

theorem lcnfFrontend_caps (tf : Frontend.C0.TFlatFn) : lcnfFrontend.caps tf = {} :=
  rfl

theorem lcnfFrontend_direct (tf : Frontend.C0.TFlatFn) : route (lcnfFrontend.caps tf) = .direct :=
  rfl

theorem lcnfFrontend_unified_direct (Bs : Backends.{0}) (tf : Frontend.C0.TFlatFn) :
    pick Bs (route (lcnfFrontend.caps tf)) = Bs.direct :=
  rfl

theorem lcnfFrontend_unified_eq_legacy (t : LegalTarget) (B : Backend.{0})
    (tf : Frontend.C0.TFlatFn) :
    (unified lcnfFrontend t B).run tf = bindE (legacyMid t tf.toFn) B.lower :=
  rfl

/-- Construct the `LeanQbe.T.Module` of lowered `LeanLCNF` `TFlatFn`s (`LeanLCNF.lcnfTModule`). -/
@[expose] def lcnfModule : List Frontend.C0.TFlatFn → Module :=
  LeanLCNF.lcnfTModule

theorem lcnfModule_wf (tfs : List Frontend.C0.TFlatFn) :
    ∀ fn ∈ (lcnfModule tfs).fns, fn.Wf :=
  LeanLRC.tflatFnsToFns_wf tfs

/-- `lcnfFrontend.lower.mapM` produces `LeanLRC.tflatFnsToFns tfs` identically. -/
theorem lcnfFrontend_mapM (tfs : List Frontend.C0.TFlatFn) :
    lcnfFrontend.lower.mapM tfs = .ok (LeanLRC.tflatFnsToFns tfs) := by
  induction tfs with
  | nil => rfl
  | cons tf rest ih =>
    change bindE (lcnfFrontend.lower.mapM rest) (fun qs => .ok (tf.toFn :: qs)) =
      .ok (tf.toFn :: LeanLRC.tflatFnsToFns rest)
    rw [ih]
    rfl

theorem lcnfFrontend_mapM_wf (tfs : List Frontend.C0.TFlatFn) {fns : List Fn}
    (h : lcnfFrontend.lower.mapM tfs = .ok fns) : ∀ fn ∈ fns, fn.Wf := by
  rw [lcnfFrontend_mapM] at h
  cases h
  exact LeanLRC.tflatFnsToFns_wf tfs

/-- Lower a `LeanLCNF.LcModule` to well-formed `LeanQbe.T.Fn`s via `lowerModule` and
`lcnfFrontend.lower.mapM`. -/
@[expose] def lcnfLcLower (m : LcModule) : Except String (List Fn) :=
  bindE (lowerModule m) lcnfFrontend.lower.mapM

theorem lcnfLcLower_eq (m : LcModule) {fns : List Fn} (h : lcnfLcLower m = .ok fns) :
    ∃ tfs, lowerModule m = .ok tfs ∧ fns = (lcnfModule tfs).fns := by
  dsimp only [lcnfLcLower] at h
  obtain ⟨tfs, hm, htfs⟩ := bindE_ok h
  rw [lcnfFrontend_mapM] at htfs
  cases htfs
  exact ⟨tfs, hm, rfl⟩

theorem lcnfLcLower_wf (m : LcModule) {fns : List Fn} (h : lcnfLcLower m = .ok fns) :
    ∀ fn ∈ fns, fn.Wf := by
  dsimp only [lcnfLcLower] at h
  obtain ⟨tfs, _, htfs⟩ := bindE_ok h
  exact lcnfFrontend_mapM_wf tfs htfs

/-- Lift any `ModuleOk Γ (lcnfModule tfs)` to pointwise `lcnfSrc.Sat`. -/
theorem lcnfFrontend_moduleOk_sat {Γ : Env} {tfs : List Frontend.C0.TFlatFn}
    (hM : ModuleOk Γ (lcnfModule tfs)) {tf : Frontend.C0.TFlatFn} (htf : tf ∈ tfs) :
    lcnfSrc.Sat tf (lcnfSSpec (Env.ofModule (lcnfModule tfs) Γ) tf.name) := by
  have hMod := hM.ofModule
  have hmem : tf.toFn ∈ (lcnfModule tfs).fns := by
    dsimp only [lcnfModule, lcnfTModule, LeanLRC.tflatFnsToFns]
    exact List.mem_map.mpr ⟨tf, htf, rfl⟩
  obtain ⟨pre, post, hsp⟩ := List.mem_iff_append.mp hmem
  exact (hMod.fnsOk pre tf.toFn post hsp).2.2

/-! ## 2. Shared Mid-End Lifting (`lcnfTfsMid` & `lcnfModMid`) -/

/-- Route lowered `TFlatFn`s through `lcnfFrontend` and shared `midEnd t`. -/
@[expose] def lcnfTfsMid (t : LegalTarget) (tfs : List Frontend.C0.TFlatFn) :
    Except String (List Fn) :=
  (lcnfFrontend.lower ≫ midEnd t).mapM tfs

theorem lcnfTfsMid_eq (t : LegalTarget) :
    ∀ (tfs : List Frontend.C0.TFlatFn) {qs : List Fn},
      lcnfTfsMid t tfs = .ok qs → qs = (lcnfModule tfs).fns.map (·.mid t)
  | [], qs, h => by
    simp only [lcnfTfsMid, Stage.mapM] at h
    cases h
    rfl
  | tf :: rest, qs, h => by
    dsimp only [lcnfTfsMid] at h
    obtain ⟨q, qs', hq, hqs, rfl⟩ :=
      @Stage.mapM_cons_ok lcnfSrc ssa (lcnfFrontend.lower ≫ midEnd t) tf rest qs h
    dsimp only [Stage.comp, lcnfFrontend, lcnfLower, bindE, midEnd] at hq
    by_cases hs : (tf.toFn.earlyOpt).body.supportsSource t = true
    · simp only [hs, ↓reduceIte] at hq
      cases hq
      have ih := lcnfTfsMid_eq t rest hqs
      rw [ih]
      rfl
    · simp only [hs, Bool.false_eq_true, ↓reduceIte] at hq
      cases hq

theorem lcnfTfsMid_wf (t : LegalTarget) (tfs : List Frontend.C0.TFlatFn) {qs : List Fn}
    (h : lcnfTfsMid t tfs = .ok qs) : ∀ q ∈ qs, q.Wf := by
  intro q hq
  obtain ⟨_, _, _, hok, _⟩ := Stage.mapM_sound (lcnfFrontend.lower ≫ midEnd t)
    (fun _ => ssa.top) tfs qs (fun _ _ => trivial) (fun _ _ _ _ _ _ hF => False.elim hF) h q hq
  exact hok

theorem lcnfTfsMid_sound (t : LegalTarget) (tfs : List Frontend.C0.TFlatFn)
    (S : Frontend.C0.TFlatFn → SSpec) (qs : List Fn)
    (hsat : ∀ tf ∈ tfs, lcnfSrc.Sat tf (S tf))
    (h : lcnfTfsMid t tfs = .ok qs) :
    ∀ q ∈ qs, ∃ tf ∈ tfs, (lcnfFrontend.lower ≫ midEnd t).run tf = .ok q ∧
      ssa.Ok q ∧ ssa.Sat q ((lcnfFrontend.lower ≫ midEnd t).tr tf (S tf)) :=
  Stage.mapM_sound (lcnfFrontend.lower ≫ midEnd t) S tfs qs (fun _ _ => trivial) hsat h

/-- End-to-end `LcModule` lowering through `lowerModule`, `lcnfFrontend`, and shared `midEnd t`. -/
@[expose] def lcnfModMid (t : LegalTarget) (m : LcModule) : Except String (List Fn) :=
  bindE (lowerModule m) (lcnfFrontend.lower ≫ midEnd t).mapM

theorem lcnfModMid_eq (t : LegalTarget) (m : LcModule) {qs : List Fn}
    (h : lcnfModMid t m = .ok qs) :
    ∃ tfs, lowerModule m = .ok tfs ∧ qs = (lcnfModule tfs).fns.map (·.mid t) := by
  dsimp only [lcnfModMid] at h
  obtain ⟨tfs, hm, hmid⟩ := bindE_ok h
  exact ⟨tfs, hm, lcnfTfsMid_eq t tfs hmid⟩

theorem lcnfModMid_wf (t : LegalTarget) (m : LcModule) {qs : List Fn}
    (h : lcnfModMid t m = .ok qs) : ∀ q ∈ qs, q.Wf := by
  dsimp only [lcnfModMid] at h
  obtain ⟨tfs, _, hmid⟩ := bindE_ok h
  exact lcnfTfsMid_wf t tfs hmid

theorem lcnfModMid_sound (t : LegalTarget) (m : LcModule)
    (S : List Frontend.C0.TFlatFn → Frontend.C0.TFlatFn → SSpec) (qs : List Fn)
    (hsat : ∀ tfs, lowerModule m = .ok tfs → ∀ tf ∈ tfs, lcnfSrc.Sat tf (S tfs tf))
    (h : lcnfModMid t m = .ok qs) :
    ∃ tfs, lowerModule m = .ok tfs ∧
      ∀ q ∈ qs, ∃ tf ∈ tfs, (lcnfFrontend.lower ≫ midEnd t).run tf = .ok q ∧
        ssa.Ok q ∧ ssa.Sat q ((lcnfFrontend.lower ≫ midEnd t).tr tf (S tfs tf)) := by
  dsimp only [lcnfModMid] at h
  obtain ⟨tfs, hm, hmid⟩ := bindE_ok h
  exact ⟨tfs, hm, lcnfTfsMid_sound t tfs (S tfs) qs (hsat tfs hm) hmid⟩

theorem lcnfModMid_moduleOk_sound (t : LegalTarget) (m : LcModule) (Γ : Env) (qs : List Fn)
    (hM : ∀ tfs, lowerModule m = .ok tfs → ModuleOk Γ (lcnfModule tfs))
    (h : lcnfModMid t m = .ok qs) :
    ∃ tfs, lowerModule m = .ok tfs ∧
      ∀ q ∈ qs, ∃ tf ∈ tfs, (lcnfFrontend.lower ≫ midEnd t).run tf = .ok q ∧
        ssa.Ok q ∧
        ssa.Sat q ((lcnfFrontend.lower ≫ midEnd t).tr tf
          (lcnfSSpec (Env.ofModule (lcnfModule tfs) Γ) tf.name)) :=
  lcnfModMid_sound t m (fun tfs tf => lcnfSSpec (Env.ofModule (lcnfModule tfs) Γ) tf.name) qs
    (fun tfs hm _ htf => lcnfFrontend_moduleOk_sat (hM tfs hm) htf) h

/-! ## 3. Shared Arch-Free `Backend` Bridge (`lcnfTargetBackend`) & End-to-End Theorems -/

private theorem defined_of_lowerFn_loc {T : Target} {host : T.mach.Host}
    {hints : T.toIsa.Hints} {E : Rega.Ext} {f : Fn} {code : List T.Directive} {k₀ : Nat}
    (hl : Rega.lowerFn T.toIsa hints E f = .ok code)
    (hc : code.IsInfixAt (T.mach.prog host) k₀) : T.Defined host f.name := by
  unfold Rega.lowerFn at hl
  split at hl
  · cases hl
  · cases hal : T.toIsa.assignArgs f.as with
    | none => simp [hal] at hl
    | some argLocs =>
      cases hrl : T.toIsa.assignRets f.rs with
      | none => simp [hal, hrl] at hl
      | some _ =>
        simp only [hal, hrl] at hl
        cases hb : Rega.bindAbiParams T.toIsa argLocs 0
            { regs := [], slots := .empty, defs := .empty, vecWidths := .empty } with
        | none => simp [hb] at hl
        | some st0 =>
          simp only [hb] at hl
          cases hle : Rega.lowerExpr T.toIsa hints E f.name
              (f.body Rega.VNat Rega.LNat (Tup.levels f.as 0)) f.as.length 0 0 st0 none with
          | error _ => simp [hle] at hl
          | ok _ =>
            simp only [hle, Except.ok.injEq] at hl
            subst hl
            exact ⟨k₀, (List.IsInfixAt.cons hc).1⟩

/-- Host-level `Target.FnSpec` satisfaction for `ds` compiled from `fn : Fn` on `T : Target`
(arch-free: shared across `Amd64` and `Arm64`). -/
@[expose] def lcnfTargetHostSpec (T : Target) (hints : Fn → T.toIsa.Hints)
    (ds : List T.Directive) (s : SSpec) (fn : Fn) : Prop :=
  ∀ (h : T.mach.Host) (k₀ n nX : Nat) (bound : Sym → Nat),
    ds.IsInfixAt (T.mach.prog h) k₀ →
    T.LabelsUnique h →
    Rega.effFrame T.toIsa (hints fn) fn.ext ≤ n →
    n + T.frame.raBytes ≤ 2 ^ 64 →
    (∀ g as bs, (g, as, bs) ∈ fn.ext.callees →
      T.FnSpec h g (s.Γ g as bs) (bound g) nX ∧
      Rega.effFrame T.toIsa (hints fn) fn.ext + T.frame.raBytes + bound g ≤ n) →
    (∀ g, g ∈ fn.ext.exits → T.Defined h g ∧ nX ≤ n) →
    T.Defined h fn.name ∧ T.FnSpec h fn.name (s.C fn.as fn.rs) n nX

/-- Target-tier `MSat` for `lcnfTargetBackend T hints`: non-vacuous compilation witness paired
with universal host soundness for every matching `Fn`. -/
@[expose] def lcnfTargetMSat (T : Target) (hints : Fn → T.toIsa.Hints)
    (ds : List T.Directive) (s : SSpec) : Prop :=
  (∃ fn : Fn, fn.Wf ∧ Rega.lowerFn T.toIsa (hints fn) fn.ext fn = .ok ds ∧
    lcnfTargetHostSpec T hints ds s fn) ∧
  (∀ fn : Fn, fn.Wf → Rega.lowerFn T.toIsa (hints fn) fn.ext fn = .ok ds →
    ssa.Sat fn s → lcnfTargetHostSpec T hints ds s fn)

theorem lcnfTargetHostSpec_of_lower {T : Target} {hints : Fn → T.toIsa.Hints}
    {fn : Fn} {ds : List T.Directive} {s : SSpec}
    (hwf : fn.Wf) (hl : Rega.lowerFn T.toIsa (hints fn) fn.ext fn = .ok ds)
    (hsat : ssa.Sat fn s) : lcnfTargetHostSpec T hints ds s fn := by
  intro h k₀ n nX bound hinf hu hfr hn hcal hex
  refine ⟨defined_of_lowerFn_loc hl hinf, ?_⟩
  have hfn := Rega.lowerFn_correct T h (hints fn) fn.ext fn s.Γ n nX bound hwf hl hinf hu
    hfr hn hcal hex
  exact fun args m Q X hC => hfn args m Q X (hsat args m Q X hC)

/-- Shared arch-free `Unified.Backend` bridge over any `T : Target` (applicable to both `Amd64`
and `Arm64` using only arch-free `Target`, `RegaLemmas`, and `DriverLemmas`). -/
@[expose] def lcnfTargetBackend (T : Target) (hints : Fn → T.toIsa.Hints) : Backend.{0} where
  D := T.Directive
  MSat := lcnfTargetMSat T hints
  lower fn := Rega.lowerFn T.toIsa (hints fn) fn.ext fn
  correct fn _ _ hwf hl hsat :=
    ⟨⟨fn, hwf, hl, lcnfTargetHostSpec_of_lower hwf hl hsat⟩,
     fun _ hwf' hl' hsat' => lcnfTargetHostSpec_of_lower hwf' hl' hsat'⟩

/-- Convenience `Backends` table routing `.direct` to `lcnfTargetBackend T hints`. -/
@[expose] def lcnfBackends (T : Target) (hints : Fn → T.toIsa.Hints)
    (designB word : Backend.{0}) : Backends.{0} :=
  ⟨lcnfTargetBackend T hints, designB, word⟩

theorem lcnf_unified_sound (t : LegalTarget) (Bs : Backends.{0})
    (tf : Frontend.C0.TFlatFn) (s : SSpec)
    (ds : List (pick Bs (route (lcnfFrontend.caps tf))).D)
    (hrun : (unified lcnfFrontend t (pick Bs (route (lcnfFrontend.caps tf)))).run tf = .ok ds)
    (hs : lcnfSrc.Sat tf s) :
    Bs.direct.MSat ds ((unified lcnfFrontend t Bs.direct).tr tf s) :=
  (unified lcnfFrontend t Bs.direct).sound tf ds s trivial hrun hs

theorem lcnf_unified_moduleOk_sound {Γ : Env} {tfs : List Frontend.C0.TFlatFn}
    (t : LegalTarget) (B : Backend.{0}) (hM : ModuleOk Γ (lcnfModule tfs))
    {tf : Frontend.C0.TFlatFn} (htf : tf ∈ tfs) (ds : List B.D)
    (hrun : (unified lcnfFrontend t B).run tf = .ok ds) :
    B.MSat ds
      ((unified lcnfFrontend t B).tr tf (lcnfSSpec (Env.ofModule (lcnfModule tfs) Γ) tf.name)) :=
  (unified lcnfFrontend t B).sound tf ds
    (lcnfSSpec (Env.ofModule (lcnfModule tfs) Γ) tf.name) trivial hrun
    (lcnfFrontend_moduleOk_sat hM htf)

theorem lcnf_unified_target_hostSpec (T : Target) (t : LegalTarget) (hints : Fn → T.toIsa.Hints)
    (tf : Frontend.C0.TFlatFn) (s : SSpec) (ds : List T.Directive)
    (hrun : (unified lcnfFrontend t (lcnfTargetBackend T hints)).run tf = .ok ds)
    (hs : lcnfSrc.Sat tf s) :
    (tf.toFn.earlyOpt).body.supportsSource t = true ∧
      Rega.lowerFn T.toIsa (hints (tf.toFn.mid t)) (tf.toFn.mid t).ext (tf.toFn.mid t) = .ok ds ∧
      lcnfTargetHostSpec T hints ds (legalTr t tf.toFn s) (tf.toFn.mid t) := by
  have hrun' := hrun
  rw [unified_eq_legacy] at hrun'
  dsimp only [lcnfFrontend, lcnfLower, bindE, legacyMid, lcnfTargetBackend] at hrun'
  by_cases hsupp : (tf.toFn.earlyOpt).body.supportsSource t = true
  · simp only [hsupp, ↓reduceIte] at hrun'
    have hmsat := (unified lcnfFrontend t (lcnfTargetBackend T hints)).sound tf ds s trivial
      hrun hs
    have htr : (unified lcnfFrontend t (lcnfTargetBackend T hints)).tr tf s =
        legalTr t tf.toFn s := by
      dsimp only [unified, Stage.comp, Backend.stage, lcnfFrontend, lcnfLower]
      rw [midEnd_run t tf.toFn hsupp]
      rfl
    rw [htr] at hmsat
    have hmid_wf : (tf.toFn.mid t).Wf :=
      (lcnfFrontend.lower ≫ midEnd t).ok tf (tf.toFn.mid t) trivial
        (by dsimp only [Stage.comp, lcnfFrontend, lcnfLower, bindE]
            exact midEnd_run t tf.toFn hsupp)
    have hmid_sat : ssa.Sat (tf.toFn.mid t) (legalTr t tf.toFn s) :=
      (lcnfFrontend.lower ≫ midEnd t).sound tf (tf.toFn.mid t) s trivial
        (by dsimp only [Stage.comp, lcnfFrontend, lcnfLower, bindE]
            exact midEnd_run t tf.toFn hsupp) hs
    exact ⟨hsupp, hrun', hmsat.2 (tf.toFn.mid t) hmid_wf hrun' hmid_sat⟩
  · simp only [hsupp, Bool.false_eq_true, ↓reduceIte] at hrun'
    cases hrun'

theorem lcnf_unified_moduleOk_fnSpec (T : Target) (t : LegalTarget) (hints : Fn → T.toIsa.Hints)
    {Γ : Env} {tfs : List Frontend.C0.TFlatFn} (hM : ModuleOk Γ (lcnfModule tfs))
    {tf : Frontend.C0.TFlatFn} (htf : tf ∈ tfs) (ds : List T.Directive)
    (hrun : (unified lcnfFrontend t (lcnfTargetBackend T hints)).run tf = .ok ds)
    (h : T.mach.Host) (k₀ n nX : Nat) (bound : Sym → Nat)
    (hinf : ds.IsInfixAt (T.mach.prog h) k₀) (hu : T.LabelsUnique h)
    (hfr : Rega.effFrame T.toIsa (hints (tf.toFn.mid t)) (tf.toFn.mid t).ext ≤ n)
    (hn : n + T.frame.raBytes ≤ 2 ^ 64)
    (hcal : ∀ g as bs, (g, as, bs) ∈ (tf.toFn.mid t).ext.callees →
      T.FnSpec h g (legalEnv t (Env.ofModule (lcnfModule tfs) Γ) g as bs) (bound g) nX ∧
      Rega.effFrame T.toIsa (hints (tf.toFn.mid t)) (tf.toFn.mid t).ext +
        T.frame.raBytes + bound g ≤ n)
    (hex : ∀ g, g ∈ (tf.toFn.mid t).ext.exits → T.Defined h g ∧ nX ≤ n) :
    T.Defined h tf.name ∧
    T.FnSpec h tf.name
      (legalEnv t (Env.ofModule (lcnfModule tfs) Γ) tf.name (t.legalSig tf.as) (t.legalSig tf.rs))
      n nX := by
  let s₀ := lcnfSSpec (Env.ofModule (lcnfModule tfs) Γ) tf.name
  obtain ⟨_, _, hhost⟩ := lcnf_unified_target_hostSpec T t hints tf s₀ ds hrun
    (lcnfFrontend_moduleOk_sat hM htf)
  obtain ⟨hdef, hsp⟩ := hhost h k₀ n nX bound hinf hu hfr hn hcal hex
  refine ⟨hdef, fun args m Q X hleg s ra R hargs hra hspE hmemS => ?_⟩
  rcases hleg with ⟨as, bs, has, hbs, xs, P, E, hxs, hQ, hX, hEnv⟩
  have hMnd : (lcnfModule tfs).namesNodup := hM.nodup
  have hfn_mem : tf.toFn ∈ (lcnfModule tfs).fns := by
    dsimp only [lcnfModule, lcnfTModule, LeanLRC.tflatFnsToFns]
    exact List.mem_map.mpr ⟨tf, htf, rfl⟩
  have hsig : as = tf.as ∧ bs = tf.rs := by
    by_cases he : (as, bs) = (tf.toFn.as, tf.toFn.rs)
    · exact ⟨congrArg Prod.fst he, congrArg Prod.snd he⟩
    · exact absurd hEnv (Env.ofModule_empty_off_sig hMnd Γ hfn_mem he xs m P E)
  rcases hsig with ⟨rfl, rfl⟩
  have hxs' : encodeTup t tf.as xs = args := by simpa only [cast_eq] using hxs
  have hQ' : ∀ r m₁, legalPost t P r m₁ → Q r m₁ := by
    intro r m₁ hp
    have := hQ r m₁ hp
    rwa [cast_eq] at this
  have htr : (legalTr t tf.toFn s₀).C (t.legalSig tf.as) (t.legalSig tf.rs)
      args m (legalPost t P) (legalXPost t E) :=
    ⟨rfl, rfl, xs, P, E, hEnv, hxs', rfl, rfl⟩
  refine eventually_weaken _ _ _ _ ?_
    (hsp args m (legalPost t P) (legalXPost t E) htr s ra R hargs hra hspE hmemS)
  rintro st (⟨hpc, rets, m', hP', hrets, hrest, hm'⟩ | ⟨sym', cs, xs', m', hE', rest⟩)
  · exact Or.inl ⟨hpc, rets, m', hQ' rets m' hP', hrets, hrest, hm'⟩
  · exact Or.inr ⟨sym', cs, xs', m', hX sym' cs xs' m' hE', rest⟩

theorem lcnf_unified_moduleOk_fnSpec_src (T : Target) (t : LegalTarget)
    (hints : Fn → T.toIsa.Hints) {Γ : Env} {tfs : List Frontend.C0.TFlatFn}
    (hM : ModuleOk Γ (lcnfModule tfs)) {tf : Frontend.C0.TFlatFn} (htf : tf ∈ tfs)
    (ds : List T.Directive)
    (hrun : (unified lcnfFrontend t (lcnfTargetBackend T hints)).run tf = .ok ds)
    (h : T.mach.Host) (k₀ n nX : Nat) (bound : Sym → Nat)
    (hinf : ds.IsInfixAt (T.mach.prog h) k₀) (hu : T.LabelsUnique h)
    (hfr : Rega.effFrame T.toIsa (hints (tf.toFn.mid t)) (tf.toFn.mid t).ext ≤ n)
    (hn : n + T.frame.raBytes ≤ 2 ^ 64)
    (hcal : ∀ g as bs, (g, as, bs) ∈ (tf.toFn.mid t).ext.callees →
      T.FnSpec h g (legalEnv t (Env.ofModule (lcnfModule tfs) Γ) g as bs) (bound g) nX ∧
      Rega.effFrame T.toIsa (hints (tf.toFn.mid t)) (tf.toFn.mid t).ext +
        T.frame.raBytes + bound g ≤ n)
    (hex : ∀ g, g ∈ (tf.toFn.mid t).ext.exits → T.Defined h g ∧ nX ≤ n)
    (has : t.legalSig tf.as = tf.as) (hrs : t.legalSig tf.rs = tf.rs) :
    T.Defined h tf.name ∧
    T.FnSpec h tf.name
      (fun args m Q X => Γ tf.name tf.as tf.rs args m Q
        (fun g cs xs m' => X g (t.legalSig cs) (encodeTup t cs xs) m')) n nX := by
  obtain ⟨hdef, hsp⟩ :=
    lcnf_unified_moduleOk_fnSpec T t hints hM htf ds hrun h k₀ n nX bound hinf hu hfr hn hcal hex
  have hmem : (tf.name, tf.as, tf.rs) ∈ (lcnfModule tfs).sigs := by
    refine List.mem_append_left _ (List.mem_map.mpr ⟨tf.toFn, ?_, rfl⟩)
    dsimp only [lcnfModule, lcnfTModule, LeanLRC.tflatFnsToFns]
    exact List.mem_map.mpr ⟨tf, htf, rfl⟩
  exact ⟨hdef, fnSpec_of_legalEnv_legalSig_eq has hrs hmem hsp⟩

theorem lcnf_unified_moduleOk_fnSpec_noExit (T : Target) (t : LegalTarget)
    (hints : Fn → T.toIsa.Hints) {Γ : Env} {tfs : List Frontend.C0.TFlatFn}
    (hM : ModuleOk Γ (lcnfModule tfs)) {tf : Frontend.C0.TFlatFn} (htf : tf ∈ tfs)
    (ds : List T.Directive)
    (hrun : (unified lcnfFrontend t (lcnfTargetBackend T hints)).run tf = .ok ds)
    (h : T.mach.Host) (k₀ n nX : Nat) (bound : Sym → Nat)
    (hinf : ds.IsInfixAt (T.mach.prog h) k₀) (hu : T.LabelsUnique h)
    (hfr : Rega.effFrame T.toIsa (hints (tf.toFn.mid t)) (tf.toFn.mid t).ext ≤ n)
    (hn : n + T.frame.raBytes ≤ 2 ^ 64)
    (hcal : ∀ g as bs, (g, as, bs) ∈ (tf.toFn.mid t).ext.callees →
      T.FnSpec h g (legalEnv t (Env.ofModule (lcnfModule tfs) Γ) g as bs) (bound g) nX ∧
      Rega.effFrame T.toIsa (hints (tf.toFn.mid t)) (tf.toFn.mid t).ext +
        T.frame.raBytes + bound g ≤ n)
    (hex : ∀ g, g ∈ (tf.toFn.mid t).ext.exits → T.Defined h g ∧ nX ≤ n)
    (has : t.legalSig tf.as = tf.as) (hrs : t.legalSig tf.rs = tf.rs)
    (hnoex : ∀ args m Q X X',
      Γ tf.name tf.as tf.rs args m Q X → Γ tf.name tf.as tf.rs args m Q X') :
    T.Defined h tf.name ∧
    T.FnSpec h tf.name (Γ tf.name tf.as tf.rs) n nX := by
  obtain ⟨hdef, hsp⟩ :=
    lcnf_unified_moduleOk_fnSpec_src T t hints hM htf ds hrun h k₀ n nX bound hinf hu hfr hn hcal
      hex has hrs
  exact ⟨hdef, fun args m Q X hC => hsp args m Q X (hnoex args m Q X _ hC)⟩

/-! ## 4. End-to-End `Compiled` & `TargetInit.run_fnSpec` (`rtR0Mod` / `lcnfModule`) -/

/-- Compiled `rtR0Mod` functions satisfy `T.Defined` and `T.FnSpec` against `rtC0Env` on any
`T : Target` (`x64Target`, `armTarget`, etc.). -/
theorem lcnfRtR0_compiled_fnSpec {T : Target} {t : LegalTarget} {nX : Nat}
    {hints : List T.toIsa.Hints} {maxBound : Nat}
    (M : Compiled T t [] rtExitSyms nX rtR0Mod.fns hints maxBound)
    {fn : Fn} (hfn : fn ∈ rtR0Mod.fns) :
    T.Defined M.host fn.name ∧
    T.FnSpec M.host fn.name
      (legalEnv t (Env.ofModule rtR0Mod rtC0Env) fn.name (t.legalSig fn.as) (t.legalSig fn.rs))
      (M.bound fn.name) nX :=
  M.fnSpec_host rtR0Mod rfl rtC0Env rtR0Mod_checkAcyclic rtR0Mod_wf M.supportsSource
    (fun fn hmem xs m Q X hc =>
      let ⟨pre, post, hsp⟩ := List.mem_iff_append.mp hmem
      (rtR0Mod_ok.fnsOk pre fn post hsp).2.2 xs m Q X hc)
    hfn

/-- Source-signature transfer for compiled `rtR0Mod` functions (`t.legalSig` fixes `(as, rs)`). -/
theorem lcnfRtR0_compiled_fnSpec_src {T : Target} {t : LegalTarget} {nX : Nat}
    {hints : List T.toIsa.Hints} {maxBound : Nat}
    (M : Compiled T t [] rtExitSyms nX rtR0Mod.fns hints maxBound)
    {fn : Fn} (hfn : fn ∈ rtR0Mod.fns)
    (has : t.legalSig fn.as = fn.as) (hrs : t.legalSig fn.rs = fn.rs) :
    T.Defined M.host fn.name ∧
    T.FnSpec M.host fn.name
      (fun args m Q X => rtC0Env fn.name fn.as fn.rs args m Q
        (fun g cs xs m' => X g (t.legalSig cs) (encodeTup t cs xs) m'))
      (M.bound fn.name) nX := by
  obtain ⟨hdef, hsp⟩ := lcnfRtR0_compiled_fnSpec M hfn
  have hmem : (fn.name, fn.as, fn.rs) ∈ rtR0Mod.sigs :=
    List.mem_append_left _ (List.mem_map.mpr ⟨fn, hfn, rfl⟩)
  have hsrc := fnSpec_of_legalEnv_legalSig_eq has hrs hmem hsp
  refine ⟨hdef, fun args m Q X hC => hsrc args m Q X ?_⟩
  exact hC

/-- Concrete `TargetInit.run_fnSpec` execution theorem for compiled `rtR0Mod` functions. -/
theorem lcnfRtR0_compiled_run_fnSpec {T : Target} {maxStack maxMem : Nat}
    (I : TargetInit T maxStack maxMem) {t : LegalTarget} {nX : Nat}
    {hints : List T.toIsa.Hints} {maxBound : Nat}
    (M : Compiled T t [] rtExitSyms nX rtR0Mod.fns hints maxBound)
    {fn : Fn} (hfn : fn ∈ rtR0Mod.fns)
    (has : t.legalSig fn.as = fn.as) (hrs : t.legalSig fn.rs = fn.rs)
    (bsMem : List UInt8) (args : Tup Val fn.as) (hbs : bsMem.length ≤ maxMem)
    (hargs : (T.toIsa.assignArgs fn.as).isSome = true) {Q : Post fn.rs} {X : XPost}
    (hspec : rtC0Env fn.name fn.as fn.rs args (bsMem.At 0x1000#64) Q
      (fun g cs xs m' => X g (t.legalSig cs) (encodeTup t cs xs) m'))
    {post : T.mach.State → Prop}
    (hpost : ∀ st, (T.mach.pc st = I.ra0 ∧ ∃ rets m', Q rets m' ∧
        T.RetsIn rets (T.mach.data st) ∧
        (T.mach.mem (T.mach.data st) =⋆ Eq m' ⋆ T.Exit I.sp0 (M.bound fn.name) ⋆
          Std.ExtHashMap.emp)) ∨
      (∃ (sym' : Sym) (cs : List Ty) (xs : Tup Val cs) (m' : Mem 64), X sym' cs xs m' ∧
        T.mach.pc st = T.mach.labelAddr M.host sym' ∧ T.ArgsIn xs (T.mach.data st)) → post st)
    (hbound : maxBound ≤ maxStack := by omega) :
    Eventually (T.mach.step M.host) post
      (T.mach.mkState (I.initState (M.bound fn.name) bsMem args)
        (T.mach.labelAddr M.host fn.name)) :=
  I.run_fnSpec M (lcnfRtR0_compiled_fnSpec_src M hfn has hrs).2 bsMem args hbs hargs hspec hpost
    hbound

/-- Whole-module `Compiled` soundness for `lcnfModule tfs` (`lowerModule m = .ok tfs`) under
`ModuleOk Γ (lcnfModule tfs)` and `extCallees` runtime specs (e.g. from `rtC0Env`). -/
theorem lcnfModule_compiled_fnSpec {T : Target} {t : LegalTarget}
    {extCallees : List (SigEntry × Nat)} {exits : List Sym} {nX : Nat}
    {tfs : List Frontend.C0.TFlatFn} {hints : List T.toIsa.Hints} {maxBound : Nat}
    (M : Compiled T t extCallees exits nX (lcnfModule tfs).fns hints maxBound)
    (Γ : Env) (hacyc : (lcnfModule tfs).checkAcyclic = true)
    (hM : ModuleOk Γ (lcnfModule tfs))
    (hext : ∀ p ∈ extCallees,
      T.FnSpec M.host p.1.1 (legalEnv t (Env.ofModule (lcnfModule tfs) Γ) p.1.1 p.1.2.1 p.1.2.2)
        p.2 nX)
    (hext_uniq : (∀ p ∈ extCallees, ∀ q ∈ extCallees, p.1.1 = q.1.1 → p.2 = q.2) ∧
      (∀ p ∈ extCallees, p.1.1 ∉ (lcnfModule tfs).fns.map Fn.name))
    {tf : Frontend.C0.TFlatFn} (htf : tf ∈ tfs) :
    T.Defined M.host tf.name ∧
    T.FnSpec M.host tf.name
      (legalEnv t (Env.ofModule (lcnfModule tfs) Γ) tf.name (t.legalSig tf.as) (t.legalSig tf.rs))
      (M.bound tf.name) nX := by
  have hmem : tf.toFn ∈ (lcnfModule tfs).fns := by
    dsimp only [lcnfModule, lcnfTModule, LeanLRC.tflatFnsToFns]
    exact List.mem_map.mpr ⟨tf, htf, rfl⟩
  exact M.fnSpec (lcnfModule tfs) rfl M.host Γ 0 M.code_infix_host M.labelsUnique hacyc
    (lcnfModule_wf tfs) M.supportsSource
    (fun fn hfn xs m Q X hc =>
      let ⟨pre, post, hsp⟩ := List.mem_iff_append.mp hfn
      (hM.fnsOk pre fn post hsp).2.2 xs m Q X hc)
    hext hext_uniq (fun _ hg => M.defined_exit_host hg) hmem

/-- Source-signature transfer for `lcnfModule_compiled_fnSpec` (`t.legalSig` fixes `(tf.as,
tf.rs)`). -/
theorem lcnfModule_compiled_fnSpec_src {T : Target} {t : LegalTarget}
    {extCallees : List (SigEntry × Nat)} {exits : List Sym} {nX : Nat}
    {tfs : List Frontend.C0.TFlatFn} {hints : List T.toIsa.Hints} {maxBound : Nat}
    (M : Compiled T t extCallees exits nX (lcnfModule tfs).fns hints maxBound)
    (Γ : Env) (hacyc : (lcnfModule tfs).checkAcyclic = true)
    (hM : ModuleOk Γ (lcnfModule tfs))
    (hext : ∀ p ∈ extCallees,
      T.FnSpec M.host p.1.1 (legalEnv t (Env.ofModule (lcnfModule tfs) Γ) p.1.1 p.1.2.1 p.1.2.2)
        p.2 nX)
    (hext_uniq : (∀ p ∈ extCallees, ∀ q ∈ extCallees, p.1.1 = q.1.1 → p.2 = q.2) ∧
      (∀ p ∈ extCallees, p.1.1 ∉ (lcnfModule tfs).fns.map Fn.name))
    {tf : Frontend.C0.TFlatFn} (htf : tf ∈ tfs)
    (has : t.legalSig tf.as = tf.as) (hrs : t.legalSig tf.rs = tf.rs) :
    T.Defined M.host tf.name ∧
    T.FnSpec M.host tf.name
      (fun args m Q X => Γ tf.name tf.as tf.rs args m Q
        (fun g cs xs m' => X g (t.legalSig cs) (encodeTup t cs xs) m'))
      (M.bound tf.name) nX := by
  obtain ⟨hdef, hsp⟩ :=
    lcnfModule_compiled_fnSpec M Γ hacyc hM hext hext_uniq htf
  have hsig_mem : (tf.name, tf.as, tf.rs) ∈ (lcnfModule tfs).sigs := by
    refine List.mem_append_left _ (List.mem_map.mpr ⟨tf.toFn, ?_, rfl⟩)
    dsimp only [lcnfModule, lcnfTModule, LeanLRC.tflatFnsToFns]
    exact List.mem_map.mpr ⟨tf, htf, rfl⟩
  exact ⟨hdef, fnSpec_of_legalEnv_legalSig_eq has hrs hsig_mem hsp⟩

/-- End-to-end `TargetInit.run_fnSpec` theorem for any `LcModule` function lowered via
`lowerModule`, `lcnfFrontend`, `Fn.mid`, and `Compiled`. -/
theorem lcnfModule_compiled_run_fnSpec {T : Target} {maxStack maxMem : Nat}
    (I : TargetInit T maxStack maxMem) {t : LegalTarget}
    {extCallees : List (SigEntry × Nat)} {exits : List Sym} {nX : Nat}
    {tfs : List Frontend.C0.TFlatFn} {hints : List T.toIsa.Hints} {maxBound : Nat}
    (M : Compiled T t extCallees exits nX (lcnfModule tfs).fns hints maxBound)
    (Γ : Env) (hacyc : (lcnfModule tfs).checkAcyclic = true)
    (hM : ModuleOk Γ (lcnfModule tfs))
    (hext : ∀ p ∈ extCallees,
      T.FnSpec M.host p.1.1 (legalEnv t (Env.ofModule (lcnfModule tfs) Γ) p.1.1 p.1.2.1 p.1.2.2)
        p.2 nX)
    (hext_uniq : (∀ p ∈ extCallees, ∀ q ∈ extCallees, p.1.1 = q.1.1 → p.2 = q.2) ∧
      (∀ p ∈ extCallees, p.1.1 ∉ (lcnfModule tfs).fns.map Fn.name))
    {tf : Frontend.C0.TFlatFn} (htf : tf ∈ tfs)
    (has : t.legalSig tf.as = tf.as) (hrs : t.legalSig tf.rs = tf.rs)
    (bsMem : List UInt8) (args : Tup Val tf.as) (hbs : bsMem.length ≤ maxMem)
    (hargs : (T.toIsa.assignArgs tf.as).isSome = true) {Q : Post tf.rs} {X : XPost}
    (hspec : Γ tf.name tf.as tf.rs args (bsMem.At 0x1000#64) Q
      (fun g cs xs m' => X g (t.legalSig cs) (encodeTup t cs xs) m'))
    {post : T.mach.State → Prop}
    (hpost : ∀ st, (T.mach.pc st = I.ra0 ∧ ∃ rets m', Q rets m' ∧
        T.RetsIn rets (T.mach.data st) ∧
        (T.mach.mem (T.mach.data st) =⋆ Eq m' ⋆ T.Exit I.sp0 (M.bound tf.name) ⋆
          Std.ExtHashMap.emp)) ∨
      (∃ (sym' : Sym) (cs : List Ty) (xs : Tup Val cs) (m' : Mem 64), X sym' cs xs m' ∧
        T.mach.pc st = T.mach.labelAddr M.host sym' ∧ T.ArgsIn xs (T.mach.data st)) → post st)
    (hbound : maxBound ≤ maxStack := by omega) :
    Eventually (T.mach.step M.host) post
      (T.mach.mkState (I.initState (M.bound tf.name) bsMem args)
        (T.mach.labelAddr M.host tf.name)) :=
  I.run_fnSpec M
    (lcnfModule_compiled_fnSpec_src M Γ hacyc hM hext hext_uniq htf has hrs).2
    bsMem args hbs hargs hspec hpost hbound

end LeanQbe.T.Unified
