module

public import LeanQbe.T.Unified.Driver
public import LeanQbe.T.Main
public import LeanQbe.T.MainCertCore
public import LeanQbe.T.Target
public import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Unified.DriverLemmas
import LeanQbe.T.RegaLemmas
import LeanQbe.T.TargetLemmas
import LeanQbe.T.MainCertProof

/-!
# Shared Arch-Free `Rega` Backend on `LeanQbe.T.Unified` (`Unified.Backend.Rega`)

Target-generic `LeanQbe.T.Unified.Backend` wrapping `Rega.lowerFn` + `Rega.lowerFn_correct` for
any `T : Target` (`x64Target`, `armTarget`, etc.), shared across C0, LCNF, Bedrock2, and
BedrockWord frontends with zero Kraken/Amd64/Arm64 imports and zero `*Lemmas*` in `public import`:

* `fnSSpec` / `ssa_sat_fnSSpec`: packages an `Env` + function symbol into `Unified.SSpec`.
* `regaHostSpec` / `regaMSat` / `regaBackend` / `regaBackends`: arch-free `Unified.Backend`
  slot with universal host `Target.FnSpec` soundness.
* `regaCompileModule`: module-level driver matching `compileModule` step-for-step.
* `unified_rega_eq_compileFn` & `rega_mapM_eq_compileModule_code`: kernel per-function and
  whole-module byte-identity theorems connecting `unified` / `Stage.mapM` directly to
  `compileFn` / `compileModule`.
* `rega_compiled_moduleOk_fnSpec` / `rega_compiled_ofTable_fnSpec` /
  `rega_compiled_ofTable_run_fnSpec` (plus `LinkedCert` variants): bridge `ModuleOk Γ M` and
  `SpecEntry` tables (`Env.ofTable_moduleOk`) through `Compiled` to `T.FnSpec` and
  `TargetInit.run_fnSpec`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Unified

open LeanQbe.T

universe u v

/-! ## 1. Shared `SSpec` Packaging & Arch-Free `regaBackend` -/

/-- Package an `Env` and a function symbol into a per-function `SSpec`. -/
@[expose] def fnSSpec (Γ : Env) (nm : Sym) : SSpec where
  Γ := Γ
  C := Γ nm

theorem ssa_sat_fnSSpec (Γ : Env) (fn : Fn) :
    ssa.Sat fn (fnSSpec Γ fn.name) ↔
      ∀ xs m Q X, Γ fn.name fn.as fn.rs xs m Q X → Func.spec Γ fn.body xs m Q X :=
  Iff.rfl

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

/-- Per-function host-level `Target.FnSpec` obligation for `ds` compiled from `fn : Fn` on any
`T : Target` (arch-free: shared across `Amd64` and `Arm64`). -/
@[expose] def regaHostSpec (T : Target) (hints : Fn → T.toIsa.Hints)
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

/-- Target-tier `MSat` for `regaBackend T hints`: non-vacuous compilation witness paired with
universal host soundness for every matching `Fn`. -/
@[expose] def regaMSat (T : Target) (hints : Fn → T.toIsa.Hints)
    (ds : List T.Directive) (s : SSpec) : Prop :=
  (∃ fn : Fn, fn.Wf ∧ Rega.lowerFn T.toIsa (hints fn) fn.ext fn = .ok ds ∧
    regaHostSpec T hints ds s fn) ∧
  (∀ fn : Fn, fn.Wf → Rega.lowerFn T.toIsa (hints fn) fn.ext fn = .ok ds →
    ssa.Sat fn s → regaHostSpec T hints ds s fn)

theorem regaHostSpec_of_lower {T : Target} {hints : Fn → T.toIsa.Hints}
    {fn : Fn} {ds : List T.Directive} {s : SSpec}
    (hwf : fn.Wf) (hl : Rega.lowerFn T.toIsa (hints fn) fn.ext fn = .ok ds)
    (hsat : ssa.Sat fn s) : regaHostSpec T hints ds s fn := by
  intro h k₀ n nX bound hinf hu hfr hn hcal hex
  refine ⟨defined_of_lowerFn_loc hl hinf, ?_⟩
  have hfn := Rega.lowerFn_correct T h (hints fn) fn.ext fn s.Γ n nX bound hwf hl hinf hu
    hfr hn hcal hex
  exact fun args m Q X hC => hfn args m Q X (hsat args m Q X hC)

/-- Generic arch-free `Unified.Backend` wrapping `Rega.lowerFn` + `Rega.lowerFn_correct`. -/
@[expose] def regaBackend (T : Target) (hints : Fn → T.toIsa.Hints) : Backend.{0} where
  D := T.Directive
  MSat := regaMSat T hints
  lower fn := Rega.lowerFn T.toIsa (hints fn) fn.ext fn
  correct fn _ _ hwf hl hsat :=
    ⟨⟨fn, hwf, hl, regaHostSpec_of_lower hwf hl hsat⟩,
     fun _ hwf' hl' hsat' => regaHostSpec_of_lower hwf' hl' hsat'⟩

/-- Convenience `Backends` table routing `.direct` to `regaBackend T hints`. -/
@[expose] def regaBackends (T : Target) (hints : Fn → T.toIsa.Hints)
    (designB word : Backend.{0}) : Backends.{0} :=
  ⟨regaBackend T hints, designB, word⟩

/-- Module-level unified driver matching `compileModule` step-for-step. -/
@[expose] def regaCompileModule (T : Target) (lt : LegalTarget)
    (extCallees : List (SigEntry × Nat)) (exits : List Sym) (nX : Nat)
    (fns : List Fn) (hints : List T.toIsa.Hints) :
    Except String (List T.Directive × List (Sym × Nat)) :=
  compileModule T.toIsa lt T.frame.raBytes extCallees exits nX fns hints

/-! ## 2. Per-Function & Module-Level Exact Equality Theorems -/

/-- Per-function definitional equality between `unified` and `compileFn` under
`supportsSource`. -/
theorem unified_rega_eq_compileFn (fe : Frontend.{u, v}) (T : Target) (lt : LegalTarget)
    (hints : Fn → T.toIsa.Hints) (p : fe.src.Prog) (fn : Fn)
    (hfe : fe.lower.run p = .ok fn)
    (hsupp : (fn.earlyOpt).body.supportsSource lt = true) :
    (unified fe lt (regaBackend T hints)).run p = compileFn T.toIsa lt (hints (fn.mid lt)) fn := by
  change bindE (fe.lower.run p) (fun q => bindE (legacyMid lt q) (regaBackend T hints).lower) = _
  rw [hfe]
  dsimp only [bindE, legacyMid, regaBackend, compileFn]
  simp only [hsupp, ↓reduceIte]

/-- Generic host-level soundness extraction for any frontend routed through `regaBackend`. -/
theorem unified_rega_hostSpec (fe : Frontend.{u, v}) (T : Target) (lt : LegalTarget)
    (hints : Fn → T.toIsa.Hints) (p : fe.src.Prog) (fn : Fn) (s : fe.src.Spec)
    (ds : List T.Directive) (hp : fe.src.Ok p) (hfe : fe.lower.run p = .ok fn)
    (hrun : (unified fe lt (regaBackend T hints)).run p = .ok ds)
    (hs : fe.src.Sat p s) :
    (fn.earlyOpt).body.supportsSource lt = true ∧
      Rega.lowerFn T.toIsa (hints (fn.mid lt)) (fn.mid lt).ext (fn.mid lt) = .ok ds ∧
      regaHostSpec T hints ds (legalTr lt fn (fe.lower.tr p s)) (fn.mid lt) := by
  have hrun' :
      bindE (fe.lower.run p) (fun q => bindE (legacyMid lt q) (regaBackend T hints).lower) =
        .ok ds := hrun
  rw [hfe] at hrun'
  dsimp only [bindE, legacyMid, regaBackend] at hrun'
  by_cases hsupp : (fn.earlyOpt).body.supportsSource lt = true
  · simp only [hsupp, ↓reduceIte] at hrun'
    have hmsat := (unified fe lt (regaBackend T hints)).sound p ds s hp hrun hs
    have htr : (unified fe lt (regaBackend T hints)).tr p s =
        legalTr lt fn (fe.lower.tr p s) := by
      dsimp only [unified, Stage.comp, Backend.stage]
      rw [hfe]
      dsimp only
      rw [midEnd_run lt fn hsupp]
      rfl
    rw [htr] at hmsat
    have hmid_run : (fe.lower ≫ midEnd lt).run p = .ok (fn.mid lt) := by
      dsimp only [Stage.comp, bindE]
      rw [hfe]
      exact midEnd_run lt fn hsupp
    have hmid_wf : (fn.mid lt).Wf := (fe.lower ≫ midEnd lt).ok p (fn.mid lt) hp hmid_run
    have hmid_sat : ssa.Sat (fn.mid lt) (legalTr lt fn (fe.lower.tr p s)) := by
      have hs' := (fe.lower ≫ midEnd lt).sound p (fn.mid lt) s hp hmid_run hs
      dsimp only [Stage.comp] at hs'
      rw [hfe] at hs'
      exact hs'
    exact ⟨hsupp, hrun', hmsat.2 (fn.mid lt) hmid_wf hrun' hmid_sat⟩
  · simp only [hsupp, Bool.false_eq_true, ↓reduceIte] at hrun'
    cases hrun'

/-- Module-level byte-identity theorem: `Stage.mapM` over `midEnd ≫ regaBackend` produces the
exact directive stream of `compile` / `compileModule` for identical per-fn hints. -/
theorem rega_mapM_eq_compileModule_code (T : Target) (lt : LegalTarget)
    (extCallees : List (SigEntry × Nat)) (exits : List Sym) (nX : Nat)
    (fns : List Fn) (hints : List T.toIsa.Hints) (hfn : Fn → T.toIsa.Hints)
    (hh : ∀ i (hi : i < fns.length) (hj : i < hints.length),
      hfn ((fns[i]'hi).mid lt) = hints[i]'hj)
    {code : List T.Directive} {bounds : List (Sym × Nat)}
    (hcm : compileModule T.toIsa lt T.frame.raBytes extCallees exits nX fns hints =
      .ok (code, bounds)) :
    ∃ perFn, (midEnd lt ≫ (regaBackend T hfn).stage).mapM fns = .ok perFn ∧
      perFn.flatten = code := by
  induction fns generalizing extCallees hints code bounds with
  | nil =>
    cases hints with
    | nil =>
      dsimp only [compileModule] at hcm
      cases hcm
      exact ⟨[], rfl, rfl⟩
    | cons _ _ =>
      dsimp only [compileModule] at hcm
      cases hcm
  | cons f fs ih =>
    cases hints with
    | nil =>
      dsimp only [compileModule] at hcm
      cases hcm
    | cons h hs =>
      have hsupp := compileModule_cons_supportsSource hcm
      rw [compileModule_cons_mid hsupp] at hcm
      have h0 : hfn (f.mid lt) = h :=
        hh 0 (Nat.zero_lt_succ _) (Nat.zero_lt_succ _)
      cases hl : Rega.lowerFn T.toIsa h (f.mid lt).ext (f.mid lt) with
      | error _ => simp only [hl] at hcm; cases hcm
      | ok c =>
        cases hchk : checkAndBoundExt T.toIsa T.frame.raBytes exits nX extCallees h
            (f.mid lt).ext with
        | none => simp only [hl, hchk] at hcm; cases hcm
        | some b =>
          simp only [hl, hchk] at hcm
          cases hrest : compileModule T.toIsa lt T.frame.raBytes
              (((f.mid lt).sig, b) :: extCallees) exits nX fs hs with
          | error _ => simp only [hrest] at hcm; cases hcm
          | ok res =>
            rcases res with ⟨cs, bs⟩
            simp only [hrest, Except.ok.injEq, Prod.mk.injEq] at hcm
            rcases hcm with ⟨rfl, rfl⟩
            have hh' : ∀ i (hi : i < fs.length) (hj : i < hs.length),
                hfn ((fs[i]'hi).mid lt) = hs[i]'hj :=
              fun i hi hj => hh (i + 1) (Nat.succ_lt_succ hi) (Nat.succ_lt_succ hj)
            obtain ⟨perFnRest, hmapRest, hflatRest⟩ := ih _ hs hh' hrest
            have hrun : (midEnd lt ≫ (regaBackend T hfn).stage).run f = .ok c := by
              dsimp only [Stage.comp, midEnd, Backend.stage, regaBackend, bindE]
              simp only [hsupp, ↓reduceIte, h0]
              exact hl
            refine ⟨c :: perFnRest, ?_, ?_⟩
            · dsimp only [Stage.mapM]
              rw [hrun]
              dsimp only [bindE]
              rw [hmapRest]
            · exact congrArg (c ++ ·) hflatRest

/-- Corollary matching `regaCompileModule` directly against `(midEnd ≫ regaBackend).mapM`. -/
theorem rega_mapM_eq_regaCompileModule_code (T : Target) (lt : LegalTarget)
    (extCallees : List (SigEntry × Nat)) (exits : List Sym) (nX : Nat)
    (fns : List Fn) (hints : List T.toIsa.Hints) (hfn : Fn → T.toIsa.Hints)
    (hh : ∀ i (hi : i < fns.length) (hj : i < hints.length),
      hfn ((fns[i]'hi).mid lt) = hints[i]'hj)
    {code : List T.Directive} {bounds : List (Sym × Nat)}
    (hcm : regaCompileModule T lt extCallees exits nX fns hints = .ok (code, bounds)) :
    ∃ perFn, (midEnd lt ≫ (regaBackend T hfn).stage).mapM fns = .ok perFn ∧
      perFn.flatten = code :=
  rega_mapM_eq_compileModule_code T lt extCallees exits nX fns hints hfn hh hcm

/-! ## 3. Bridges from `ModuleOk` & `Env.ofTable` + `Compiled` / `LinkedCert` to `FnSpec` -/

/-- Lift any `ModuleOk Γ M` + `Compiled` (with optional `extCallees`) to `T.Defined` and
`T.FnSpec` on `C.host`. -/
theorem rega_compiled_moduleOk_fnSpec {T : Target} {lt : LegalTarget}
    {extCallees : List (SigEntry × Nat)} {nX : Nat} {Γ : Env} {M : Module}
    {hints : List T.toIsa.Hints} {maxBound : Nat}
    (hacyc : M.checkAcyclic = true) (hM : ModuleOk Γ M)
    (C : Compiled T lt extCallees M.exits nX M.fns hints maxBound)
    (hext : ∀ p ∈ extCallees,
      T.FnSpec C.host p.1.1 (legalEnv lt (Env.ofModule M Γ) p.1.1 p.1.2.1 p.1.2.2) p.2 nX)
    (hext_uniq : (∀ p ∈ extCallees, ∀ q ∈ extCallees, p.1.1 = q.1.1 → p.2 = q.2) ∧
      (∀ p ∈ extCallees, p.1.1 ∉ M.fns.map Fn.name))
    {fn : Fn} (hfn : fn ∈ M.fns) :
    T.Defined C.host fn.name ∧
    T.FnSpec C.host fn.name
      (legalEnv lt (Env.ofModule M Γ) fn.name (lt.legalSig fn.as) (lt.legalSig fn.rs))
      (C.bound fn.name) nX :=
  C.fnSpec M rfl C.host Γ 0 C.code_infix_host C.labelsUnique hacyc
    (fun f hf =>
      let ⟨pre, post, hsp⟩ := List.mem_iff_append.mp hf
      (hM.fnsOk pre f post hsp).1)
    C.supportsSource
    (fun f hf xs m Q X hc =>
      let ⟨pre, post, hsp⟩ := List.mem_iff_append.mp hf
      (hM.fnsOk pre f post hsp).2.2 xs m Q X hc)
    hext hext_uniq (fun _ hg => C.defined_exit_host hg) hfn

/-- Self-contained `ModuleOk Γ M` + `Compiled` bridge (`extCallees = []`). -/
theorem rega_compiled_moduleOk_fnSpec_host {T : Target} {lt : LegalTarget} {nX : Nat}
    {Γ : Env} {M : Module} {hints : List T.toIsa.Hints} {maxBound : Nat}
    (hacyc : M.checkAcyclic = true) (hM : ModuleOk Γ M)
    (C : Compiled T lt [] M.exits nX M.fns hints maxBound)
    {fn : Fn} (hfn : fn ∈ M.fns) :
    T.Defined C.host fn.name ∧
    T.FnSpec C.host fn.name
      (legalEnv lt (Env.ofModule M Γ) fn.name (lt.legalSig fn.as) (lt.legalSig fn.rs))
      (C.bound fn.name) nX :=
  rega_compiled_moduleOk_fnSpec hacyc hM C (fun _ h => nomatch h)
    ⟨(fun _ h => nomatch h), (fun _ h => nomatch h)⟩ hfn

/-- Source-signature transfer for `rega_compiled_moduleOk_fnSpec_host` when `lt.legalSig` fixes
`(fn.as, fn.rs)`. -/
theorem rega_compiled_moduleOk_fnSpec_src {T : Target} {lt : LegalTarget} {nX : Nat}
    {Γ : Env} {M : Module} {hints : List T.toIsa.Hints} {maxBound : Nat}
    (hacyc : M.checkAcyclic = true) (hM : ModuleOk Γ M)
    (C : Compiled T lt [] M.exits nX M.fns hints maxBound)
    {fn : Fn} (hfn : fn ∈ M.fns)
    (has : lt.legalSig fn.as = fn.as) (hrs : lt.legalSig fn.rs = fn.rs) :
    T.Defined C.host fn.name ∧
    T.FnSpec C.host fn.name
      (fun args m Q X => Γ fn.name fn.as fn.rs args m Q
        (fun g cs xs m' => X g (lt.legalSig cs) (encodeTup lt cs xs) m'))
      (C.bound fn.name) nX := by
  obtain ⟨hdef, hsp⟩ := rega_compiled_moduleOk_fnSpec_host hacyc hM C hfn
  have hmem : (fn.name, fn.as, fn.rs) ∈ M.sigs :=
    List.mem_append_left _ (List.mem_map.mpr ⟨fn, hfn, rfl⟩)
  exact ⟨hdef, fnSpec_of_legalEnv_legalSig_eq has hrs hmem hsp⟩

/-- Concrete `TargetInit.run_fnSpec` execution bridge for any `ModuleOk Γ M` + `Compiled`. -/
theorem rega_compiled_moduleOk_run_fnSpec {T : Target} {maxStack maxMem : Nat}
    (I : TargetInit T maxStack maxMem) {lt : LegalTarget} {nX : Nat}
    {Γ : Env} {M : Module} {hints : List T.toIsa.Hints} {maxBound : Nat}
    (hacyc : M.checkAcyclic = true) (hM : ModuleOk Γ M)
    (C : Compiled T lt [] M.exits nX M.fns hints maxBound)
    {fn : Fn} (hfn : fn ∈ M.fns)
    (has : lt.legalSig fn.as = fn.as) (hrs : lt.legalSig fn.rs = fn.rs)
    (bsMem : List UInt8) (args : Tup Val fn.as) (hbs : bsMem.length ≤ maxMem)
    (hargs : (T.toIsa.assignArgs fn.as).isSome = true) {Q : Post fn.rs} {X : XPost}
    (hspec : Γ fn.name fn.as fn.rs args (bsMem.At 0x1000#64) Q
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
  I.run_fnSpec C (rega_compiled_moduleOk_fnSpec_src hacyc hM C hfn has hrs).2
    bsMem args hbs hargs hspec hpost hbound

/-- Bridge `Env.ofTable` (`TableImpl`) + `Compiled` directly to `T.Defined` and `T.FnSpec`. -/
theorem rega_compiled_ofTable_fnSpec {T : Target} {lt : LegalTarget}
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
  rega_compiled_moduleOk_fnSpec_host hchk (Env.ofTable_moduleOk hchk hwf hok) C hfn

/-- Source-signature transfer for `rega_compiled_ofTable_fnSpec` (`lt.legalSig` fixes
`(fn.as, fn.rs)`). -/
theorem rega_compiled_ofTable_fnSpec_src {T : Target} {lt : LegalTarget}
    {tbl : List SpecEntry} {M : Module} {nX : Nat}
    {hints : List T.toIsa.Hints} {maxBound : Nat}
    (hchk : M.checkAcyclic = true) (hwf : AllFns Fn.Wf M.fns)
    (hok : TableImpl (Env.ofTable tbl) M.fns tbl)
    (C : Compiled T lt [] M.exits nX M.fns hints maxBound)
    {fn : Fn} (hfn : fn ∈ M.fns)
    (has : lt.legalSig fn.as = fn.as) (hrs : lt.legalSig fn.rs = fn.rs) :
    T.Defined C.host fn.name ∧
    T.FnSpec C.host fn.name
      (fun args m Q X => Env.ofTable tbl fn.name fn.as fn.rs args m Q
        (fun g cs xs m' => X g (lt.legalSig cs) (encodeTup lt cs xs) m'))
      (C.bound fn.name) nX :=
  rega_compiled_moduleOk_fnSpec_src hchk (Env.ofTable_moduleOk hchk hwf hok) C hfn has hrs

/-- Exit-independent specialization of `rega_compiled_ofTable_fnSpec_src` for `noExit` tables. -/
theorem rega_compiled_ofTable_fnSpec_noExit {T : Target} {lt : LegalTarget}
    {tbl : List SpecEntry} {M : Module} {nX : Nat}
    {hints : List T.toIsa.Hints} {maxBound : Nat}
    (hchk : M.checkAcyclic = true) (hwf : AllFns Fn.Wf M.fns)
    (hok : TableImpl (Env.ofTable tbl) M.fns tbl)
    (hnoex : ∀ e ∈ tbl, e.noExit = true)
    (C : Compiled T lt [] M.exits nX M.fns hints maxBound)
    {fn : Fn} (hfn : fn ∈ M.fns)
    (has : lt.legalSig fn.as = fn.as) (hrs : lt.legalSig fn.rs = fn.rs) :
    T.Defined C.host fn.name ∧
    T.FnSpec C.host fn.name (Env.ofTable tbl fn.name fn.as fn.rs) (C.bound fn.name) nX := by
  obtain ⟨hdef, hsp⟩ := rega_compiled_ofTable_fnSpec_src hchk hwf hok C hfn has hrs
  exact ⟨hdef, fun args m Q X hC =>
    hsp args m Q X (Env.ofTable_noExit hnoex fn.name fn.as fn.rs args m Q X _ hC)⟩

/-- End-to-end `TargetInit.run_fnSpec` bridge for `TableImpl` + `Compiled`. -/
theorem rega_compiled_ofTable_run_fnSpec {T : Target} {maxStack maxMem : Nat}
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
  rega_compiled_moduleOk_run_fnSpec I hchk (Env.ofTable_moduleOk hchk hwf hok) C hfn has hrs
    bsMem args hbs hargs hspec hpost hbound

/-- Bridge `Env.ofTable` (`TableImpl`) + chunked `LinkedCert` to `T.Defined` and `T.FnSpec`. -/
theorem rega_linkedCert_ofTable_fnSpec {T : Target} {L : TargetLayout T} {lt : LegalTarget}
    {hcl : Rega.LabelClean T.toIsa} {tbl : List SpecEntry} {M : Module} {nX maxBound : Nat}
    (hchk : M.checkAcyclic = true) (hwf : AllFns Fn.Wf M.fns)
    (hok : TableImpl (Env.ofTable tbl) M.fns tbl)
    (cert : LinkedCert T L lt hcl M [] M.exits nX maxBound)
    {fn : Fn} (hfn : fn ∈ M.fns) :
    T.Defined cert.host fn.name ∧
    T.FnSpec cert.host fn.name
      (legalEnv lt (Env.ofModule M (Env.ofTable tbl)) fn.name
        (lt.legalSig fn.as) (lt.legalSig fn.rs))
      (cert.bound fn.name) nX := by
  have hM := Env.ofTable_moduleOk hchk hwf hok
  exact cert.fnSpec_host (Env.ofTable tbl) hchk hwf.mem
    (fun f hf xs m Q X hc =>
      let ⟨pre, post, hsp⟩ := List.mem_iff_append.mp hf
      (hM.fnsOk pre f post hsp).2.2 xs m Q X hc)
    hfn

/-- End-to-end `TargetInit.run_fnSpec` bridge for `TableImpl` + chunked `LinkedCert`. -/
theorem rega_linkedCert_ofTable_run_fnSpec {T : Target} {L : TargetLayout T}
    {maxStack maxMem : Nat} (I : TargetInit T maxStack maxMem) {lt : LegalTarget}
    {hcl : Rega.LabelClean T.toIsa} {tbl : List SpecEntry} {M : Module} {nX maxBound : Nat}
    (hchk : M.checkAcyclic = true) (hwf : AllFns Fn.Wf M.fns)
    (hok : TableImpl (Env.ofTable tbl) M.fns tbl)
    (hnoex : ∀ e ∈ tbl, e.noExit = true)
    (cert : LinkedCert T L lt hcl M [] M.exits nX maxBound)
    {fn : Fn} (hfn : fn ∈ M.fns)
    (has : lt.legalSig fn.as = fn.as) (hrs : lt.legalSig fn.rs = fn.rs)
    (bsMem : List UInt8) (args : Tup Val fn.as) (hbs : bsMem.length ≤ maxMem)
    (hargs : (T.toIsa.assignArgs fn.as).isSome = true) {Q : Post fn.rs} {X : XPost}
    (hspec : Env.ofTable tbl fn.name fn.as fn.rs args (bsMem.At 0x1000#64) Q X)
    {post : T.mach.State → Prop}
    (hpost : ∀ st, (T.mach.pc st = I.ra0 ∧ ∃ rets m', Q rets m' ∧
        T.RetsIn rets (T.mach.data st) ∧
        (T.mach.mem (T.mach.data st) =⋆ Eq m' ⋆ T.Exit I.sp0 (cert.bound fn.name) ⋆
          Std.ExtHashMap.emp)) ∨
      (∃ (sym' : Sym) (cs : List Ty) (xs : Tup Val cs) (m' : Mem 64), X sym' cs xs m' ∧
        T.mach.pc st = T.mach.labelAddr cert.host sym' ∧ T.ArgsIn xs (T.mach.data st)) → post st)
    (hbound : maxBound ≤ maxStack := by omega) :
    Eventually (T.mach.step cert.host) post
      (T.mach.mkState (I.initState (cert.bound fn.name) bsMem args)
        (T.mach.labelAddr cert.host fn.name)) := by
  have hM := Env.ofTable_moduleOk hchk hwf hok
  exact cert.eventually_fnSpec I (Env.ofTable tbl) hchk hwf.mem
    (fun f hf xs m Q X hc =>
      let ⟨pre, post, hsp⟩ := List.mem_iff_append.mp hf
      (hM.fnsOk pre f post hsp).2.2 xs m Q X hc)
    hfn has hrs (Env.ofTable_noExit hnoex fn.name fn.as fn.rs)
    bsMem args hbs hargs hspec hpost hbound

end LeanQbe.T.Unified
