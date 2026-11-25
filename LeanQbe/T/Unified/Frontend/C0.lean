module

public import LeanQbe.T.Unified.Backend.Rega
public import LeanQbe.T.Frontend.C0.ToFlat
import LeanQbe.T.Unified.DriverLemmas
import LeanQbe.T.MainCertProof

/-!
# C0 Direct Frontends on `LeanQbe.T.Unified` (`Unified.Frontend.C0`)

Arch-free `LeanQbe.T.Unified.Frontend` adapters for both runtime C0 source compilation (with
`#include` header maps, macros, `offsetof`, `_Static_assert`, and `assertAsCheck`) and
elaborated C0 `Fn` modules (`c0_module!`, `kissat_c0!`, `FullM7Fidelity`, `FullFidelity`):

* `C0SourceInput` / `compileC0SourceWithHeaders`: parses and lowers C0 source passing `#include`
  `headers` and `assertAsCheck` into scope-checked `Frontend.C0.TFlatFn`s.
* `c0SourceSrc` / `c0SourceLower` / `c0SourceCaps` / `c0SourceFrontend`: pinned direct
  `Frontend.{0, 1}` over `Frontend.C0.TFlatFn` (`caps := {}`, `route = .direct`) with
  `c0SourceTfsMid`, `c0SourceModMid`, and `c0SourceCompile`.
* `c0FnSrc` / `c0FnLower` / `c0FnCaps` / `c0FnFrontend`: pinned direct `Frontend.{1, 1}` over
  elaborated `Fn` (`Ok := Fn.Wf`, `lower := id`) giving definitional `unified_eq_legacy` and
  `c0Fn_unified_rega_mapM_eq_compileModule_code`.
* `c0FnFrontend_moduleOk_sat` / `c0FnFrontend_ofTable_sat`: lifts any `ModuleOk` or `TableImpl`
  (`Env.ofTable_moduleOk`) proof directly to `c0FnSrc.Sat`, `unified`, `T.FnSpec`, and
  `TargetInit.run_fnSpec`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Unified

open LeanQbe.T

/-! ## 1. Header-Aware C0 Source Driver (`C0SourceInput`, `compileC0SourceWithHeaders`) -/

/-- C0 source compilation input exposing `#include` header maps, macros, `offsetof`,
`_Static_assert`, exit symbols, and `assertAsCheck` lowering. -/
structure C0SourceInput where
  src : String
  headers : Std.HashMap String String := {}
  exits : List Sym := ["c0_abort"]
  assertAsCheck : Bool := false

/-- Parse, lower, and scope-check a C0 source input (wiring `#include` `headers` and
`assertAsCheck`) into `Frontend.C0.TFlatFn`s. -/
@[expose] def compileC0SourceWithHeaders (inp : C0SourceInput) :
    Except String (List Frontend.C0.TFlatFn) := do
  let tu ← Frontend.C0.parseC0 inp.src inp.headers
  let lmod ← Frontend.C0.lowerTranslationUnit tu inp.assertAsCheck
  lmod.fns.mapM (Frontend.C0.lFnToTFlatFn inp.exits)

/-! ## 2. Runtime C0 Source Frontend (`c0SourceFrontend` over `Frontend.C0.TFlatFn`) -/

/-- Source tier for C0 functions lowered via `compileC0SourceWithHeaders` (`TFlatFn`). -/
@[expose] def c0SourceSrc : Tier.{0, 1} where
  Prog := Frontend.C0.TFlatFn
  Ok _ := True
  Spec := SSpec
  top := ssa.top
  Sat tf s := ssa.Sat tf.toFn s

/-- Checked lowering stage from `c0SourceSrc` into `ssa` via `TFlatFn.toFn` (`toFn_wf`). -/
@[expose] def c0SourceLower : Stage c0SourceSrc ssa where
  run tf := .ok tf.toFn
  tr _ s := s
  ok tf q _ h := by cases h; exact tf.toFn_wf
  sound tf q s _ h hs := by cases h; exact hs

/-- Pinned empty capability summary (`{}`) routing every C0 source function directly. -/
@[expose] def c0SourceCaps (_ : Frontend.C0.TFlatFn) : Caps := {}

/-- Pinned direct `Frontend` for runtime C0 `TFlatFn`s (`caps := fun _ => {}`). -/
@[expose] def c0SourceFrontend : Frontend.{0, 1} :=
  ⟨c0SourceSrc, c0SourceCaps, c0SourceLower⟩

theorem c0SourceFrontend_caps (tf : Frontend.C0.TFlatFn) :
    c0SourceFrontend.caps tf = {} :=
  rfl

theorem c0SourceFrontend_direct (tf : Frontend.C0.TFlatFn) :
    route (c0SourceFrontend.caps tf) = .direct :=
  rfl

theorem c0SourceFrontend_unified_direct (Bs : Backends.{0}) (tf : Frontend.C0.TFlatFn) :
    pick Bs (route (c0SourceFrontend.caps tf)) = Bs.direct :=
  rfl

theorem c0SourceFrontend_unified_eq_legacy (lt : LegalTarget) (B : Backend.{0})
    (tf : Frontend.C0.TFlatFn) :
    (unified c0SourceFrontend lt B).run tf = bindE (legacyMid lt tf.toFn) B.lower :=
  rfl

theorem c0SourceFrontend_unified_rega_eq_compileFn (T : Target) (lt : LegalTarget)
    (hints : Fn → T.toIsa.Hints) (tf : Frontend.C0.TFlatFn)
    (hsupp : (tf.toFn.earlyOpt).body.supportsSource lt = true) :
    (unified c0SourceFrontend lt (regaBackend T hints)).run tf =
      compileFn T.toIsa lt (hints (tf.toFn.mid lt)) tf.toFn :=
  unified_rega_eq_compileFn c0SourceFrontend T lt hints tf tf.toFn rfl hsupp

/-- Build a `LeanQbe.T.Module` from lowered C0 `TFlatFn`s and declared exit symbols. -/
@[expose] def c0SourceModule (exits : List Sym) (tfs : List Frontend.C0.TFlatFn) : Module :=
  { fns := tfs.map Frontend.C0.TFlatFn.toFn, externs := [], exits := exits }

theorem c0SourceModule_wf (exits : List Sym) (tfs : List Frontend.C0.TFlatFn) :
    ∀ fn ∈ (c0SourceModule exits tfs).fns, fn.Wf := by
  intro fn hfn
  rcases List.mem_map.mp hfn with ⟨tf, _, rfl⟩
  exact tf.toFn_wf

/-- `c0SourceFrontend.lower.mapM` produces `tfs.map TFlatFn.toFn` identically. -/
theorem c0SourceFrontend_mapM (tfs : List Frontend.C0.TFlatFn) :
    c0SourceFrontend.lower.mapM tfs = .ok (tfs.map Frontend.C0.TFlatFn.toFn) := by
  induction tfs with
  | nil => rfl
  | cons tf rest ih =>
    change bindE (c0SourceFrontend.lower.mapM rest) (fun qs => .ok (tf.toFn :: qs)) =
      .ok (tf.toFn :: rest.map Frontend.C0.TFlatFn.toFn)
    rw [ih]
    rfl

theorem c0SourceFrontend_mapM_wf (tfs : List Frontend.C0.TFlatFn) {fns : List Fn}
    (h : c0SourceFrontend.lower.mapM tfs = .ok fns) : ∀ fn ∈ fns, fn.Wf := by
  rw [c0SourceFrontend_mapM] at h
  cases h
  exact c0SourceModule_wf [] tfs

/-- Parse, lower, and reify a `C0SourceInput` into well-formed `LeanQbe.T.Fn`s. -/
@[expose] def c0SourceLowerInput (inp : C0SourceInput) : Except String (List Fn) :=
  bindE (compileC0SourceWithHeaders inp) c0SourceFrontend.lower.mapM

theorem c0SourceLowerInput_eq (inp : C0SourceInput) {fns : List Fn}
    (h : c0SourceLowerInput inp = .ok fns) :
    ∃ tfs, compileC0SourceWithHeaders inp = .ok tfs ∧
      fns = (c0SourceModule inp.exits tfs).fns := by
  dsimp only [c0SourceLowerInput] at h
  obtain ⟨tfs, hinp, htfs⟩ := bindE_ok h
  rw [c0SourceFrontend_mapM] at htfs
  cases htfs
  exact ⟨tfs, hinp, rfl⟩

theorem c0SourceLowerInput_wf (inp : C0SourceInput) {fns : List Fn}
    (h : c0SourceLowerInput inp = .ok fns) : ∀ fn ∈ fns, fn.Wf := by
  dsimp only [c0SourceLowerInput] at h
  obtain ⟨tfs, _, htfs⟩ := bindE_ok h
  exact c0SourceFrontend_mapM_wf tfs htfs

/-- Route lowered C0 `TFlatFn`s through `c0SourceFrontend` and shared `midEnd lt`. -/
@[expose] def c0SourceTfsMid (lt : LegalTarget) (tfs : List Frontend.C0.TFlatFn) :
    Except String (List Fn) :=
  (c0SourceFrontend.lower ≫ midEnd lt).mapM tfs

theorem c0SourceTfsMid_eq (lt : LegalTarget) :
    ∀ (tfs : List Frontend.C0.TFlatFn) {qs : List Fn},
      c0SourceTfsMid lt tfs = .ok qs →
        qs = (tfs.map Frontend.C0.TFlatFn.toFn).map (·.mid lt)
  | [], qs, h => by
    simp only [c0SourceTfsMid, Stage.mapM] at h
    cases h
    rfl
  | tf :: rest, qs, h => by
    dsimp only [c0SourceTfsMid] at h
    obtain ⟨q, qs', hq, hqs, rfl⟩ :=
      @Stage.mapM_cons_ok c0SourceSrc ssa (c0SourceFrontend.lower ≫ midEnd lt) tf rest qs h
    dsimp only [Stage.comp, c0SourceFrontend, c0SourceLower, bindE, midEnd] at hq
    by_cases hs : (tf.toFn.earlyOpt).body.supportsSource lt = true
    · simp only [hs, ↓reduceIte] at hq
      cases hq
      have ih := c0SourceTfsMid_eq lt rest hqs
      rw [ih]
      rfl
    · simp only [hs, Bool.false_eq_true, ↓reduceIte] at hq
      cases hq

theorem c0SourceTfsMid_wf (lt : LegalTarget) (tfs : List Frontend.C0.TFlatFn) {qs : List Fn}
    (h : c0SourceTfsMid lt tfs = .ok qs) : ∀ q ∈ qs, q.Wf := by
  intro q hq
  obtain ⟨_, _, _, hok, _⟩ := Stage.mapM_sound (c0SourceFrontend.lower ≫ midEnd lt)
    (fun _ => ssa.top) tfs qs (fun _ _ => trivial) (fun _ _ _ _ _ _ hF => False.elim hF) h q hq
  exact hok

theorem c0SourceTfsMid_sound (lt : LegalTarget) (tfs : List Frontend.C0.TFlatFn)
    (S : Frontend.C0.TFlatFn → SSpec) (qs : List Fn)
    (hsat : ∀ tf ∈ tfs, c0SourceSrc.Sat tf (S tf))
    (h : c0SourceTfsMid lt tfs = .ok qs) :
    ∀ q ∈ qs, ∃ tf ∈ tfs, (c0SourceFrontend.lower ≫ midEnd lt).run tf = .ok q ∧
      ssa.Ok q ∧ ssa.Sat q ((c0SourceFrontend.lower ≫ midEnd lt).tr tf (S tf)) :=
  Stage.mapM_sound (c0SourceFrontend.lower ≫ midEnd lt) S tfs qs (fun _ _ => trivial) hsat h

/-- End-to-end C0 source lowering through `compileC0SourceWithHeaders`, `c0SourceFrontend`,
and shared `midEnd lt`. -/
@[expose] def c0SourceModMid (lt : LegalTarget) (inp : C0SourceInput) :
    Except String (List Fn) :=
  bindE (compileC0SourceWithHeaders inp) (c0SourceFrontend.lower ≫ midEnd lt).mapM

theorem c0SourceModMid_eq (lt : LegalTarget) (inp : C0SourceInput) {qs : List Fn}
    (h : c0SourceModMid lt inp = .ok qs) :
    ∃ tfs, compileC0SourceWithHeaders inp = .ok tfs ∧
      qs = (c0SourceModule inp.exits tfs).fns.map (·.mid lt) := by
  dsimp only [c0SourceModMid] at h
  obtain ⟨tfs, hinp, hmid⟩ := bindE_ok h
  exact ⟨tfs, hinp, c0SourceTfsMid_eq lt tfs hmid⟩

theorem c0SourceModMid_wf (lt : LegalTarget) (inp : C0SourceInput) {qs : List Fn}
    (h : c0SourceModMid lt inp = .ok qs) : ∀ q ∈ qs, q.Wf := by
  dsimp only [c0SourceModMid] at h
  obtain ⟨tfs, _, hmid⟩ := bindE_ok h
  exact c0SourceTfsMid_wf lt tfs hmid

/-- End-to-end C0 source compilation through `compileC0SourceWithHeaders` and
`unified c0SourceFrontend lt (regaBackend T hints)`. -/
@[expose] def c0SourceCompile (T : Target) (lt : LegalTarget)
    (hints : Fn → T.toIsa.Hints) (inp : C0SourceInput) :
    Except String (List (List T.Directive)) :=
  bindE (compileC0SourceWithHeaders inp)
    (unified c0SourceFrontend lt (regaBackend T hints)).mapM

/-- Lift any `ModuleOk Γ (c0SourceModule exits tfs)` to pointwise `c0SourceSrc.Sat`. -/
theorem c0SourceFrontend_moduleOk_sat {Γ : Env} {exits : List Sym}
    {tfs : List Frontend.C0.TFlatFn} (hM : ModuleOk Γ (c0SourceModule exits tfs))
    {tf : Frontend.C0.TFlatFn} (htf : tf ∈ tfs) :
    c0SourceSrc.Sat tf (fnSSpec (Env.ofModule (c0SourceModule exits tfs) Γ) tf.name) := by
  have hMod := hM.ofModule
  have hmem : tf.toFn ∈ (c0SourceModule exits tfs).fns :=
    List.mem_map.mpr ⟨tf, htf, rfl⟩
  obtain ⟨pre, post, hsp⟩ := List.mem_iff_append.mp hmem
  exact (hMod.fnsOk pre tf.toFn post hsp).2.2

/-- Lift any `TableImpl` on `c0SourceModule exits tfs` via `Env.ofTable_moduleOk`. -/
theorem c0SourceFrontend_ofTable_sat {tbl : List SpecEntry} {exits : List Sym}
    {tfs : List Frontend.C0.TFlatFn}
    (hchk : (c0SourceModule exits tfs).checkAcyclic = true)
    (hwf : AllFns Fn.Wf (c0SourceModule exits tfs).fns)
    (hok : TableImpl (Env.ofTable tbl) (c0SourceModule exits tfs).fns tbl)
    {tf : Frontend.C0.TFlatFn} (htf : tf ∈ tfs) :
    c0SourceSrc.Sat tf
      (fnSSpec (Env.ofModule (c0SourceModule exits tfs) (Env.ofTable tbl)) tf.name) :=
  c0SourceFrontend_moduleOk_sat (Env.ofTable_moduleOk hchk hwf hok) htf

/-- Module-level byte-identity connecting `unified c0SourceFrontend lt (regaBackend T hfn)` to
`compileModule` over `tfs.map TFlatFn.toFn`. -/
theorem c0Source_unified_rega_mapM_eq_compileModule_code (T : Target) (lt : LegalTarget)
    (extCallees : List (SigEntry × Nat)) (exits : List Sym) (nX : Nat)
    (tfs : List Frontend.C0.TFlatFn) (hints : List T.toIsa.Hints) (hfn : Fn → T.toIsa.Hints)
    (hh : ∀ i (hi : i < tfs.length) (hj : i < hints.length),
      hfn (((tfs[i]'hi).toFn).mid lt) = hints[i]'hj)
    {code : List T.Directive} {bounds : List (Sym × Nat)}
    (hcm : compileModule T.toIsa lt T.frame.raBytes extCallees exits nX
      (tfs.map Frontend.C0.TFlatFn.toFn) hints = .ok (code, bounds)) :
    ∃ perFn, (unified c0SourceFrontend lt (regaBackend T hfn)).mapM tfs = .ok perFn ∧
      perFn.flatten = code := by
  have hmapEq : ∀ xs : List Frontend.C0.TFlatFn,
      (unified c0SourceFrontend lt (regaBackend T hfn)).mapM xs =
        (midEnd lt ≫ (regaBackend T hfn).stage).mapM (xs.map Frontend.C0.TFlatFn.toFn) := by
    intro xs
    induction xs with
    | nil => rfl
    | cons x rest ih =>
      show bindE ((midEnd lt ≫ (regaBackend T hfn).stage).run x.toFn)
          (fun q => bindE ((unified c0SourceFrontend lt (regaBackend T hfn)).mapM rest)
            (fun qs => .ok (q :: qs))) =
        bindE ((midEnd lt ≫ (regaBackend T hfn).stage).run x.toFn)
          (fun q => bindE ((midEnd lt ≫ (regaBackend T hfn).stage).mapM
            (rest.map Frontend.C0.TFlatFn.toFn)) (fun qs => .ok (q :: qs)))
      cases (midEnd lt ≫ (regaBackend T hfn).stage).run x.toFn with
      | error _ => rfl
      | ok _ =>
        dsimp only [bindE]
        rw [ih]
  rw [hmapEq]
  refine rega_mapM_eq_compileModule_code T lt extCallees exits nX
    (tfs.map Frontend.C0.TFlatFn.toFn) hints hfn ?_ hcm
  intro i hi hj
  rw [List.getElem_map]
  exact hh i (by simpa using hi) hj

/-! ## 3. Elaborated C0 `Fn` Frontend (`c0FnFrontend` for `c0_module!` / Kissat Modules) -/

/-- Source tier for already-elaborated C0 `Fn` modules (`m7FidelityModule`, `fidBaseModule`,
`KissatPlain`, etc.) with `Ok := Fn.Wf`. -/
@[expose] def c0FnSrc : Tier.{1, 1} where
  Prog := Fn
  Ok := Fn.Wf
  Spec := SSpec
  top := ssa.top
  Sat := ssa.Sat

/-- Identity checked stage from `c0FnSrc` into `ssa`. -/
@[expose] def c0FnLower : Stage c0FnSrc ssa where
  run fn := .ok fn
  tr _ s := s
  ok _ _ hp h := by cases h; exact hp
  sound _ _ _ _ h hs := by cases h; exact hs

/-- Pinned empty capability summary (`{}`) for elaborated direct C0 `Fn`s. -/
@[expose] def c0FnCaps : Fn → Caps := fnCaps

/-- Pinned direct `Frontend` for elaborated C0 `Fn` modules (`caps := {}`, `lower := id`). -/
@[expose] def c0FnFrontend : Frontend.{1, 1} :=
  ⟨c0FnSrc, c0FnCaps, c0FnLower⟩

theorem c0FnFrontend_caps (fn : Fn) : c0FnFrontend.caps fn = {} :=
  rfl

theorem c0FnFrontend_direct (fn : Fn) : route (c0FnFrontend.caps fn) = .direct :=
  rfl

theorem c0FnFrontend_unified_direct (Bs : Backends.{0}) (fn : Fn) :
    pick Bs (route (c0FnFrontend.caps fn)) = Bs.direct :=
  rfl

theorem c0FnFrontend_unified_eq_legacy (lt : LegalTarget) (B : Backend.{0}) (fn : Fn) :
    (unified c0FnFrontend lt B).run fn = bindE (legacyMid lt fn) B.lower :=
  rfl

theorem c0FnFrontend_unified_rega_eq_compileFn (T : Target) (lt : LegalTarget)
    (hints : Fn → T.toIsa.Hints) (fn : Fn)
    (hsupp : (fn.earlyOpt).body.supportsSource lt = true) :
    (unified c0FnFrontend lt (regaBackend T hints)).run fn =
      compileFn T.toIsa lt (hints (fn.mid lt)) fn :=
  unified_rega_eq_compileFn c0FnFrontend T lt hints fn fn rfl hsupp

theorem c0FnFrontend_mapM (fns : List Fn) :
    c0FnFrontend.lower.mapM fns = .ok fns := by
  induction fns with
  | nil => rfl
  | cons fn rest ih =>
    change bindE (c0FnFrontend.lower.mapM rest) (fun qs => .ok (fn :: qs)) = .ok (fn :: rest)
    rw [ih]
    rfl

/-- Route elaborated C0 `Fn`s through `c0FnFrontend` and shared `midEnd lt`. -/
@[expose] def c0FnMid (lt : LegalTarget) (fns : List Fn) : Except String (List Fn) :=
  (c0FnFrontend.lower ≫ midEnd lt).mapM fns

theorem c0FnMid_eq (lt : LegalTarget) :
    ∀ (fns : List Fn) {qs : List Fn}, c0FnMid lt fns = .ok qs → qs = fns.map (·.mid lt)
  | [], qs, h => by
    simp only [c0FnMid, Stage.mapM] at h
    cases h
    rfl
  | fn :: rest, qs, h => by
    dsimp only [c0FnMid] at h
    obtain ⟨q, qs', hq, hqs, rfl⟩ :=
      @Stage.mapM_cons_ok c0FnSrc ssa (c0FnFrontend.lower ≫ midEnd lt) fn rest qs h
    dsimp only [Stage.comp, c0FnFrontend, c0FnLower, bindE, midEnd] at hq
    by_cases hs : (fn.earlyOpt).body.supportsSource lt = true
    · simp only [hs, ↓reduceIte] at hq
      cases hq
      have ih := c0FnMid_eq lt rest hqs
      rw [ih]
      rfl
    · simp only [hs, Bool.false_eq_true, ↓reduceIte] at hq
      cases hq

theorem c0FnMid_wf (lt : LegalTarget) (fns : List Fn) (hwf : ∀ fn ∈ fns, fn.Wf) {qs : List Fn}
    (h : c0FnMid lt fns = .ok qs) : ∀ q ∈ qs, q.Wf := by
  intro q hq
  obtain ⟨_, _, _, hok, _⟩ := Stage.mapM_sound (c0FnFrontend.lower ≫ midEnd lt)
    (fun _ => ssa.top) fns qs hwf (fun _ _ _ _ _ _ hF => False.elim hF) h q hq
  exact hok

/-- Module-level byte-identity theorem for `unified c0FnFrontend lt (regaBackend T hfn)` vs
legacy `compileModule` (serving `m7FidelityModule`, `fidBaseModule`, and all C0 modules). -/
theorem c0Fn_unified_rega_mapM_eq_compileModule_code (T : Target) (lt : LegalTarget)
    (extCallees : List (SigEntry × Nat)) (exits : List Sym) (nX : Nat)
    (fns : List Fn) (hints : List T.toIsa.Hints) (hfn : Fn → T.toIsa.Hints)
    (hh : ∀ i (hi : i < fns.length) (hj : i < hints.length),
      hfn ((fns[i]'hi).mid lt) = hints[i]'hj)
    {code : List T.Directive} {bounds : List (Sym × Nat)}
    (hcm : compileModule T.toIsa lt T.frame.raBytes extCallees exits nX fns hints =
      .ok (code, bounds)) :
    ∃ perFn, (unified c0FnFrontend lt (regaBackend T hfn)).mapM fns = .ok perFn ∧
      perFn.flatten = code := by
  have hmapEq : ∀ xs : List Fn,
      (unified c0FnFrontend lt (regaBackend T hfn)).mapM xs =
        (midEnd lt ≫ (regaBackend T hfn).stage).mapM xs := by
    intro xs
    induction xs with
    | nil => rfl
    | cons x rest ih =>
      show bindE ((midEnd lt ≫ (regaBackend T hfn).stage).run x)
          (fun q => bindE ((unified c0FnFrontend lt (regaBackend T hfn)).mapM rest)
            (fun qs => .ok (q :: qs))) =
        bindE ((midEnd lt ≫ (regaBackend T hfn).stage).run x)
          (fun q => bindE ((midEnd lt ≫ (regaBackend T hfn).stage).mapM rest)
            (fun qs => .ok (q :: qs)))
      cases (midEnd lt ≫ (regaBackend T hfn).stage).run x with
      | error _ => rfl
      | ok _ =>
        dsimp only [bindE]
        rw [ih]
  rw [hmapEq]
  exact rega_mapM_eq_compileModule_code T lt extCallees exits nX fns hints hfn hh hcm

/-! ## 4. `ModuleOk` & `Env.ofTable_moduleOk` Bridges for `c0FnFrontend` -/

/-- Lift any `ModuleOk Γ M` to pointwise `c0FnSrc.Sat` at `Env.ofModule M Γ`. -/
theorem c0FnFrontend_moduleOk_sat {Γ : Env} {M : Module}
    (hM : ModuleOk Γ M) {fn : Fn} (hmem : fn ∈ M.fns) :
    c0FnSrc.Sat fn (fnSSpec (Env.ofModule M Γ) fn.name) := by
  have hMod := hM.ofModule
  obtain ⟨pre, post, hsp⟩ := List.mem_iff_append.mp hmem
  exact (hMod.fnsOk pre fn post hsp).2.2

/-- Bridge any `SpecEntry` table (`TableImpl`) to `c0FnSrc.Sat` via `Env.ofTable_moduleOk`. -/
theorem c0FnFrontend_ofTable_sat {tbl : List SpecEntry} {M : Module}
    (hchk : M.checkAcyclic = true) (hwf : AllFns Fn.Wf M.fns)
    (hok : TableImpl (Env.ofTable tbl) M.fns tbl)
    {fn : Fn} (hmem : fn ∈ M.fns) :
    c0FnSrc.Sat fn (fnSSpec (Env.ofModule M (Env.ofTable tbl)) fn.name) :=
  c0FnFrontend_moduleOk_sat (Env.ofTable_moduleOk hchk hwf hok) hmem

/-- Per-function `Target.FnSpec` directly from `ModuleOk Γ M` + `unified c0FnFrontend`. -/
theorem c0Fn_unified_moduleOk_fnSpec (T : Target) (lt : LegalTarget)
    (hints : Fn → T.toIsa.Hints) {Γ : Env} {M : Module} (hM : ModuleOk Γ M)
    {fn : Fn} (hmem : fn ∈ M.fns) (ds : List T.Directive)
    (hrun : (unified c0FnFrontend lt (regaBackend T hints)).run fn = .ok ds)
    (h : T.mach.Host) (k₀ n nX : Nat) (bound : Sym → Nat)
    (hinf : ds.IsInfixAt (T.mach.prog h) k₀) (hu : T.LabelsUnique h)
    (hfr : Rega.effFrame T.toIsa (hints (fn.mid lt)) (fn.mid lt).ext ≤ n)
    (hn : n + T.frame.raBytes ≤ 2 ^ 64)
    (hcal : ∀ g as bs, (g, as, bs) ∈ (fn.mid lt).ext.callees →
      T.FnSpec h g (legalEnv lt (Env.ofModule M Γ) g as bs) (bound g) nX ∧
      Rega.effFrame T.toIsa (hints (fn.mid lt)) (fn.mid lt).ext +
        T.frame.raBytes + bound g ≤ n)
    (hex : ∀ g, g ∈ (fn.mid lt).ext.exits → T.Defined h g ∧ nX ≤ n) :
    T.Defined h fn.name ∧
    T.FnSpec h fn.name
      (legalEnv lt (Env.ofModule M Γ) fn.name (lt.legalSig fn.as) (lt.legalSig fn.rs))
      n nX := by
  obtain ⟨pre, post, hsp⟩ := List.mem_iff_append.mp hmem
  have hwf : fn.Wf := (hM.fnsOk pre fn post hsp).1
  let s₀ := fnSSpec (Env.ofModule M Γ) fn.name
  obtain ⟨_, _, hhost⟩ := unified_rega_hostSpec c0FnFrontend T lt hints fn fn s₀ ds hwf rfl hrun
    (c0FnFrontend_moduleOk_sat hM hmem)
  obtain ⟨hdef, hfn⟩ := hhost h k₀ n nX bound hinf hu hfr hn hcal hex
  refine ⟨hdef, fun args m Q X hleg s ra R hargs hra hspE hmemS => ?_⟩
  rcases hleg with ⟨as, bs, has, hbs, xs, P, E, hxs, hQ, hX, hEnv⟩
  have hsig : as = fn.as ∧ bs = fn.rs := by
    by_cases he : (as, bs) = (fn.as, fn.rs)
    · exact ⟨congrArg Prod.fst he, congrArg Prod.snd he⟩
    · exact absurd hEnv (Env.ofModule_empty_off_sig hM.nodup Γ hmem he xs m P E)
  rcases hsig with ⟨rfl, rfl⟩
  have hxs' : encodeTup lt fn.as xs = args := by simpa only [cast_eq] using hxs
  have hQ' : ∀ r m₁, legalPost lt P r m₁ → Q r m₁ := by
    intro r m₁ hp
    have := hQ r m₁ hp
    rwa [cast_eq] at this
  have htr : (legalTr lt fn s₀).C (lt.legalSig fn.as) (lt.legalSig fn.rs)
      args m (legalPost lt P) (legalXPost lt E) :=
    ⟨rfl, rfl, xs, P, E, hEnv, hxs', rfl, rfl⟩
  refine eventually_weaken _ _ _ _ ?_
    (hfn args m (legalPost lt P) (legalXPost lt E) htr s ra R hargs hra hspE hmemS)
  rintro st (⟨hpc, rets, m', hP', hrets, hrest, hm'⟩ | ⟨sym', cs, xs', m', hE', rest⟩)
  · exact Or.inl ⟨hpc, rets, m', hQ' rets m' hP', hrets, hrest, hm'⟩
  · exact Or.inr ⟨sym', cs, xs', m', hX sym' cs xs' m' hE', rest⟩

/-- Per-function `Target.FnSpec` from a `SpecEntry` table (`TableImpl`) +
`unified c0FnFrontend lt (regaBackend T hints)`. -/
theorem c0Fn_unified_ofTable_fnSpec (T : Target) (lt : LegalTarget)
    (hints : Fn → T.toIsa.Hints) {tbl : List SpecEntry} {M : Module}
    (hchk : M.checkAcyclic = true) (hwf : AllFns Fn.Wf M.fns)
    (hok : TableImpl (Env.ofTable tbl) M.fns tbl)
    {fn : Fn} (hmem : fn ∈ M.fns) (ds : List T.Directive)
    (hrun : (unified c0FnFrontend lt (regaBackend T hints)).run fn = .ok ds)
    (h : T.mach.Host) (k₀ n nX : Nat) (bound : Sym → Nat)
    (hinf : ds.IsInfixAt (T.mach.prog h) k₀) (hu : T.LabelsUnique h)
    (hfr : Rega.effFrame T.toIsa (hints (fn.mid lt)) (fn.mid lt).ext ≤ n)
    (hn : n + T.frame.raBytes ≤ 2 ^ 64)
    (hcal : ∀ g as bs, (g, as, bs) ∈ (fn.mid lt).ext.callees →
      T.FnSpec h g (legalEnv lt (Env.ofModule M (Env.ofTable tbl)) g as bs) (bound g) nX ∧
      Rega.effFrame T.toIsa (hints (fn.mid lt)) (fn.mid lt).ext +
        T.frame.raBytes + bound g ≤ n)
    (hex : ∀ g, g ∈ (fn.mid lt).ext.exits → T.Defined h g ∧ nX ≤ n) :
    T.Defined h fn.name ∧
    T.FnSpec h fn.name
      (legalEnv lt (Env.ofModule M (Env.ofTable tbl)) fn.name
        (lt.legalSig fn.as) (lt.legalSig fn.rs))
      n nX :=
  c0Fn_unified_moduleOk_fnSpec T lt hints (Env.ofTable_moduleOk hchk hwf hok) hmem ds hrun
    h k₀ n nX bound hinf hu hfr hn hcal hex

/-- Whole-module `Compiled` `FnSpec` for a `TableImpl`-verified C0 module. -/
theorem c0Fn_compiled_ofTable_fnSpec {T : Target} {lt : LegalTarget}
    {tbl : List SpecEntry} {M : Module} {nX : Nat}
    {hints : List T.toIsa.Hints} {maxBound : Nat}
    (hchk : M.checkAcyclic = true) (hwf : AllFns Fn.Wf M.fns)
    (hok : TableImpl (Env.ofTable tbl) M.fns tbl)
    (C : Compiled T lt [] M.exits nX M.fns hints maxBound)
    {fn : Fn} (hfn : fn ∈ M.fns) :
    T.Defined C.host fn.name ∧
    T.FnSpec C.host fn.name
      (legalEnv lt (Env.ofModule M (Env.ofTable tbl)) fn.name
        (lt.legalSig fn.as) (lt.legalSig fn.rs))
      (C.bound fn.name) nX :=
  rega_compiled_ofTable_fnSpec hchk hwf hok C hfn

/-- End-to-end `TargetInit.run_fnSpec` for a `TableImpl`-verified C0 module. -/
theorem c0Fn_compiled_ofTable_run_fnSpec {T : Target} {maxStack maxMem : Nat}
    (I : TargetInit T maxStack maxMem) {lt : LegalTarget}
    {tbl : List SpecEntry} {M : Module} {nX : Nat}
    {hints : List T.toIsa.Hints} {maxBound : Nat}
    (hchk : M.checkAcyclic = true) (hwf : AllFns Fn.Wf M.fns)
    (hok : TableImpl (Env.ofTable tbl) M.fns tbl)
    (C : Compiled T lt [] M.exits nX M.fns hints maxBound)
    {fn : Fn} (hfn : fn ∈ M.fns)
    (has : lt.legalSig fn.as = fn.as) (hrs : lt.legalSig fn.rs = fn.rs)
    (bsMem : List UInt8) (args : Tup Val fn.as) (hbs : bsMem.length ≤ maxMem)
    (hargs : (T.toIsa.assignArgs fn.as).isSome = true) {Q : Post fn.rs} {X : XPost}
    (hspec : Env.ofTable tbl fn.name fn.as fn.rs args (bsMem.At 0x1000#64) Q
      (fun g cs xs m' => X g (lt.legalSig cs) (encodeTup lt cs xs) m'))
    {post : T.mach.State → Prop}
    (hpost : ∀ st, (T.mach.pc st = I.ra0 ∧ ∃ rets m', Q rets m' ∧
        T.RetsIn rets (T.mach.data st) ∧
        (T.mach.mem (T.mach.data st) =⋆ Eq m' ⋆ T.Exit I.sp0 (C.bound fn.name) ⋆
          Std.ExtHashMap.emp)) ∨
      (∃ (sym' : Sym) (cs : List Ty) (xs : Tup Val cs) (m' : Mem 64), X sym' cs xs m' ∧
        T.mach.pc st = T.mach.labelAddr C.host sym' ∧ T.ArgsIn xs (T.mach.data st)) → post st)
    (hbound : maxBound ≤ maxStack := by omega) :
    Eventually (T.mach.step C.host) post
      (T.mach.mkState (I.initState (C.bound fn.name) bsMem args)
        (T.mach.labelAddr C.host fn.name)) :=
  rega_compiled_ofTable_run_fnSpec I hchk hwf hok C hfn has hrs bsMem args hbs hargs hspec
    hpost hbound

end LeanQbe.T.Unified
