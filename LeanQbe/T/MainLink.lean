module

public import LeanQbe.T.MainLemmas

/-!
# Compositional Multi-Chunk Compilation & Linking Certificates (`MainLink`)

Enables large typed-IR modules to compile and certify per-chunk in parallel before linking in
O(N) metadata-only kernel time without re-running `compileFn` or `Rega.lowerFn`:

* `Compiled.sigBounds`: exports `(fnSig, stackBound)` entries of a verified chunk.
* `checkCompileLit` / `checkCompileLitWithLabels` & `compileCheckedLit` /
  `compileCheckedLitWithLabels`: literal-backed `Compiled` constructors storing pre-evaluated
  `(code, bounds)` literals alongside a one-shot `compileModule` kernel proof so downstream
  `sigBounds`, `checkLink`, and `checkLinkList` never re-evaluate `compileModule`.
* `checkLink` / `checkLinkWithLabels` & `linkCompiled` / `linkCompiledWithLabels`: pairwise
  O(N) metadata-only linker validator (when chunks are literal-backed) and combined `Compiled`
  certificate constructor.
* `CompiledChunk`, `checkLinkList` / `checkLinkListWithLabels`, & `linkCompiledList` /
  `linkCompiledListWithLabels`: arbitrary multi-chunk list linking via accumulator validation.
* `linkCompiled_fnSpec` & `linkCompiledList_fnSpec`: end-to-end `T.Defined` and `T.FnSpec` over
  concatenated hosts.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T

/-! ## 1. Signature-bound export, literal-backed constructors, & lookup helpers -/

/-- Legalized `(fnSig, stackBound)` entries exported by a pre-verified `Compiled` chunk. -/
@[expose] def Compiled.sigBounds {T : Target} {lt : LegalTarget}
    {extCallees : List (SigEntry × Nat)} {exits : List Sym} {nX : Nat}
    {fs : List Fn} {hints : List T.toIsa.Hints} {maxBound : Nat}
    (M : Compiled T lt extCallees exits nX fs hints maxBound) :
    List (SigEntry × Nat) :=
  fs.map fun f => ((f.name, lt.legalSig f.as, lt.legalSig f.rs), M.bound f.name)

@[expose] def sigBoundsOf (lt : LegalTarget) (fs : List Fn) (bounds : List (Sym × Nat)) :
    List (SigEntry × Nat) :=
  fs.map fun f =>
    ((f.name, lt.legalSig f.as, lt.legalSig f.rs), (lookupFnBound bounds f.name).getD 0)

theorem sigBoundsOf_eq {T : Target} {lt : LegalTarget} {extCallees : List (SigEntry × Nat)}
    {exits : List Sym} {nX : Nat} {fs : List Fn} {hints : List T.toIsa.Hints} {maxBound : Nat}
    (M : Compiled T lt extCallees exits nX fs hints maxBound) :
    M.sigBounds = sigBoundsOf lt fs M.bounds :=
  rfl

theorem sigBoundsOf_names (lt : LegalTarget) (fs : List Fn) (bounds : List (Sym × Nat)) :
    (sigBoundsOf lt fs bounds).map (fun p => p.1.1) = fs.map Fn.name := by
  dsimp only [sigBoundsOf]; simp [List.map_map, Function.comp_def]

theorem compileModule_bounds_names {I : Isa} {lt : LegalTarget} {raBytes : Nat}
    {exits : List Sym} {nX : Nat} :
    ∀ {extCallees : List (SigEntry × Nat)} {fs : List Fn} {hints : List I.Hints}
      {code : List I.Directive} {bounds : List (Sym × Nat)},
      compileModule I lt raBytes extCallees exits nX fs hints = .ok (code, bounds) →
      bounds.map Prod.fst = fs.map Fn.name
  | _, [], [], _, _, h => by dsimp only [compileModule] at h; cases h; rfl
  | _, [], _ :: _, _, _, h => by dsimp only [compileModule] at h; cases h
  | _, _ :: _, [], _, _, h => by dsimp only [compileModule] at h; cases h
  | _, f :: _, _ :: _, _, _, h => by
    dsimp only [compileModule] at h
    split at h
    · split at h
      · rename_i hrest
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        rcases h with ⟨_, rfl⟩
        simpa [List.map_cons] using compileModule_bounds_names hrest
      · simp at h
    · simp at h
    · simp at h

theorem lookupFnBound_append_left :
    ∀ {bs₁ bs₂ : List (Sym × Nat)} {nm : Sym},
      nm ∈ bs₁.map Prod.fst → lookupFnBound (bs₁ ++ bs₂) nm = lookupFnBound bs₁ nm
  | [], _, _, h => nomatch h
  | (k, v) :: bs₁, bs₂, nm, h => by
    dsimp only [lookupFnBound]
    simp only [List.cons_append, List.find?]
    cases hbeq : k == nm
    · simp only [List.map_cons, List.mem_cons] at h
      rcases h with rfl | h'
      · simp at hbeq
      · exact lookupFnBound_append_left h'
    · rfl

theorem lookupFnBound_append_right :
    ∀ {bs₁ bs₂ : List (Sym × Nat)} {nm : Sym},
      nm ∉ bs₁.map Prod.fst → lookupFnBound (bs₁ ++ bs₂) nm = lookupFnBound bs₂ nm
  | [], _, _, _ => rfl
  | (k, v) :: bs₁, bs₂, nm, h => by
    simp only [List.map_cons, List.mem_cons, not_or] at h
    have hne : (k == nm) = false := beq_false_of_ne (Ne.symm h.1)
    dsimp only [lookupFnBound]
    simp only [List.cons_append, List.find?, hne]
    exact lookupFnBound_append_right h.2

private theorem lookupFnBound_cons_ne {k : Sym} {b : Nat} {bs : List (Sym × Nat)} {nm : Sym}
    (hne : nm ≠ k) : lookupFnBound ((k, b) :: bs) nm = lookupFnBound bs nm := by
  have hb : (k == nm) = false := beq_false_of_ne (Ne.symm hne)
  dsimp only [lookupFnBound]; simp [hb]

private theorem sigBoundsOf_cons (lt : LegalTarget) (f : Fn) (fs : List Fn)
    (b : Nat) (bs : List (Sym × Nat)) (hnd : f.name ∉ fs.map Fn.name) :
    sigBoundsOf lt (f :: fs) ((f.name, b) :: bs) =
      ((f.mid lt).sig, b) :: sigBoundsOf lt fs bs := by
  have hhead : ((f.name, lt.legalSig f.as, lt.legalSig f.rs),
      (lookupFnBound ((f.name, b) :: bs) f.name).getD 0) = ((f.mid lt).sig, b) := by
    dsimp only [Fn.mid, Fn.lateOpt, Fn.legal, Fn.earlyOpt, Fn.sig, lookupFnBound]
    simp
  have htail : fs.map (fun g => ((g.name, lt.legalSig g.as, lt.legalSig g.rs),
        (lookupFnBound ((f.name, b) :: bs) g.name).getD 0)) = sigBoundsOf lt fs bs := by
    refine List.map_congr_left fun g hg => ?_
    have hne : g.name ≠ f.name := fun e => hnd (e ▸ List.mem_map_of_mem hg)
    rw [lookupFnBound_cons_ne hne]
  dsimp only [sigBoundsOf]
  simp only [List.map_cons]
  rw [hhead]
  exact congrArg (List.cons _) htail

private theorem lookupBound_cons_swap :
    ∀ {xs ys : List (SigEntry × Nat)} {p : SigEntry × Nat},
      (∀ q ∈ xs, q.1.1 ≠ p.1.1) → ∀ (g : SigEntry),
      lookupBound (xs ++ p :: ys) g = lookupBound (p :: (xs ++ ys)) g
  | [], _, _, _, _ => rfl
  | q :: xs, ys, p, hnd, g => by
    have hq_ne : q.1.1 ≠ p.1.1 := hnd q List.mem_cons_self
    have hxs_ne : ∀ r ∈ xs, r.1.1 ≠ p.1.1 := fun r hr => hnd r (List.mem_cons_of_mem q hr)
    have ih := lookupBound_cons_swap (ys := ys) hxs_ne g
    cases hp : SigEntry.beq p.1 g <;> cases hq : SigEntry.beq q.1 g
    · dsimp only [lookupBound] at ih ⊢
      simp only [List.cons_append, List.find?, hq, hp] at ih ⊢
      exact ih
    · dsimp only [lookupBound]; simp only [List.cons_append, List.find?, hq, hp]
    · dsimp only [lookupBound] at ih ⊢
      simp only [List.cons_append, List.find?, hq, hp] at ih ⊢
      exact ih
    · have hp_eq : p.1 = g := SigEntry.beq_iff_eq.mp hp
      have hq_eq : q.1 = g := SigEntry.beq_iff_eq.mp hq
      exact absurd (congrArg Prod.fst (hq_eq.trans hp_eq.symm)) hq_ne

/-! ## 2. `compileModule` monotonicity & append composition -/

private theorem calleesBound_mono_lookupBound {F raBytes : Nat}
    {ext₁ ext₂ : List (SigEntry × Nat)}
    (hmono : ∀ g bg, lookupBound ext₁ g = some bg → lookupBound ext₂ g = some bg) :
    ∀ {gs : List SigEntry} {n : Nat},
      calleesBound F raBytes ext₁ gs = some n → calleesBound F raBytes ext₂ gs = some n
  | [], _, h => h
  | g :: gs, n, h => by
    dsimp only [calleesBound] at h ⊢
    cases h1 : lookupBound ext₁ g with
    | none => simp [h1] at h
    | some bg =>
      cases h2 : calleesBound F raBytes ext₁ gs with
      | none => simp [h1, h2] at h
      | some rest =>
        simp only [h1, h2, Option.some.injEq] at h
        rw [hmono g bg h1, calleesBound_mono_lookupBound hmono h2]
        dsimp only
        rw [h]

private theorem checkAndBoundExt_mono_lookupBound {I : Isa} {raBytes : Nat}
    {exits : List Sym} {nX : Nat} {ext₁ ext₂ : List (SigEntry × Nat)}
    (hmono : ∀ g bg, lookupBound ext₁ g = some bg → lookupBound ext₂ g = some bg)
    {h : I.Hints} {ext : Rega.Ext} {b : Nat}
    (hc : checkAndBoundExt I raBytes exits nX ext₁ h ext = some b) :
    checkAndBoundExt I raBytes exits nX ext₂ h ext = some b := by
  dsimp only [checkAndBoundExt] at hc ⊢
  cases hcb : calleesBound (Rega.effFrame I h ext) raBytes ext₁ ext.callees with
  | none => simp [hcb] at hc
  | some n₁ =>
    rw [hcb] at hc
    rw [calleesBound_mono_lookupBound hmono hcb]
    exact hc

private theorem lookupBound_cons_mono {s : SigEntry} {b : Nat}
    {ext₁ ext₂ : List (SigEntry × Nat)}
    (hmono : ∀ g bg, lookupBound ext₁ g = some bg → lookupBound ext₂ g = some bg) :
    ∀ g bg,
      lookupBound ((s, b) :: ext₁) g = some bg → lookupBound ((s, b) :: ext₂) g = some bg := by
  intro g bg hg
  dsimp only [lookupBound] at hg ⊢; simp only [List.find?] at hg ⊢
  cases hbeq : SigEntry.beq s g
  · simp only [hbeq] at hg ⊢; exact hmono g bg hg
  · simp only [hbeq] at hg ⊢; exact hg

/-- If `ext₂` preserves every `lookupBound` answer of `ext₁`, `compileModule` succeeds with the
exact same directive stream and stack bounds under `ext₂`. -/
theorem compileModule_mono_lookupBound {I : Isa} {lt : LegalTarget} {raBytes : Nat}
    {exits : List Sym} {nX : Nat} :
    ∀ {ext₁ ext₂ : List (SigEntry × Nat)} {fs : List Fn} {hints : List I.Hints}
      {code : List I.Directive} {bounds : List (Sym × Nat)},
      (∀ g bg, lookupBound ext₁ g = some bg → lookupBound ext₂ g = some bg) →
      compileModule I lt raBytes ext₁ exits nX fs hints = .ok (code, bounds) →
      compileModule I lt raBytes ext₂ exits nX fs hints = .ok (code, bounds)
  | _, _, [], [], _, _, _, h => h
  | _, _, [], _ :: _, _, _, _, h => by dsimp only [compileModule] at h; cases h
  | _, _, _ :: _, [], _, _, _, h => by dsimp only [compileModule] at h; cases h
  | ext₁, ext₂, f :: fs, hint :: hints, code, bounds, hmono, h => by
    dsimp only [compileModule] at h ⊢
    cases hl : Rega.lowerFn I hint (f.mid lt).ext (f.mid lt) with
    | error e => simp [hl] at h
    | ok c =>
      cases hchk : checkAndBoundExt I raBytes exits nX ext₁ hint (f.mid lt).ext with
      | none => simp [hl, hchk] at h
      | some b =>
        simp only [hl, hchk] at h ⊢
        rw [checkAndBoundExt_mono_lookupBound hmono hchk]
        dsimp only
        cases hrest : compileModule I lt raBytes (((f.mid lt).sig, b) :: ext₁) exits nX fs
            hints with
        | error e => simp [hrest] at h
        | ok res =>
          simp only [hrest] at h
          rw [compileModule_mono_lookupBound (lookupBound_cons_mono hmono) hrest]
          exact h

/-- Compose two `compileModule` certificates into a single concatenated `compileModule` result
without re-running `compileFn` or `Rega.lowerFn`. -/
theorem compileModule_append {I : Isa} {lt : LegalTarget} {raBytes : Nat}
    {exits : List Sym} {nX : Nat} :
    ∀ {ext₀ ext₂ : List (SigEntry × Nat)} {fs₁ : List Fn} {hints₁ : List I.Hints}
      {fs₂ : List Fn} {hints₂ : List I.Hints} {code₁ code₂ : List I.Directive}
      {bounds₁ bounds₂ : List (Sym × Nat)},
      compileModule I lt raBytes ext₀ exits nX fs₁ hints₁ = .ok (code₁, bounds₁) →
      compileModule I lt raBytes ext₂ exits nX fs₂ hints₂ = .ok (code₂, bounds₂) →
      (fs₁.map Fn.name).Nodup →
      (∀ g bg, lookupBound ext₂ g = some bg →
        lookupBound (sigBoundsOf lt fs₁ bounds₁ ++ ext₀) g = some bg) →
      compileModule I lt raBytes ext₀ exits nX (fs₁ ++ fs₂) (hints₁ ++ hints₂) =
        .ok (code₁ ++ code₂, bounds₁ ++ bounds₂)
  | ext₀, ext₂, [], [], fs₂, hints₂, code₁, code₂, bounds₁, bounds₂, h₁, h₂, _, hsig => by
    dsimp only [compileModule] at h₁; cases h₁
    simp only [List.nil_append]
    exact compileModule_mono_lookupBound (by dsimp only [sigBoundsOf] at hsig; simpa using hsig) h₂
  | _, _, [], _ :: _, _, _, _, _, _, _, h₁, _, _, _ => by
    dsimp only [compileModule] at h₁; cases h₁
  | _, _, _ :: _, [], _, _, _, _, _, _, h₁, _, _, _ => by
    dsimp only [compileModule] at h₁; cases h₁
  | ext₀, ext₂, f :: fs₁, hint :: hints₁, fs₂, hints₂, code₁, code₂, bounds₁, bounds₂,
      h₁, h₂, hnd, hsig => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    dsimp only [compileModule] at h₁ ⊢
    cases hl : Rega.lowerFn I hint (f.mid lt).ext (f.mid lt) with
    | error e => simp [hl] at h₁
    | ok c =>
      cases hchk : checkAndBoundExt I raBytes exits nX ext₀ hint (f.mid lt).ext with
      | none => simp [hl, hchk] at h₁
      | some b =>
        simp only [hl, hchk] at h₁ ⊢
        cases hrest : compileModule I lt raBytes (((f.mid lt).sig, b) :: ext₀) exits nX fs₁
            hints₁ with
        | error e => simp [hrest] at h₁
        | ok res =>
          rcases res with ⟨cs₁, bs₁⟩
          simp only [hrest, Except.ok.injEq, Prod.mk.injEq] at h₁
          rcases h₁ with ⟨rfl, rfl⟩
          have hsb : sigBoundsOf lt (f :: fs₁) ((f.name, b) :: bs₁) =
              ((f.mid lt).sig, b) :: sigBoundsOf lt fs₁ bs₁ :=
            sigBoundsOf_cons lt f fs₁ b bs₁ hnd.1
          have hsig' : ∀ g bg, lookupBound ext₂ g = some bg →
              lookupBound (sigBoundsOf lt fs₁ bs₁ ++ (((f.mid lt).sig, b) :: ext₀)) g =
                some bg := by
            intro g bg hg
            have hsw : lookupBound (sigBoundsOf lt fs₁ bs₁ ++ (((f.mid lt).sig, b) :: ext₀)) g =
                lookupBound (((f.mid lt).sig, b) :: (sigBoundsOf lt fs₁ bs₁ ++ ext₀)) g :=
              lookupBound_cons_swap (fun q hq e => by
                have hmem : q.1.1 ∈ (sigBoundsOf lt fs₁ bs₁).map (fun p => p.1.1) :=
                  List.mem_map_of_mem hq
                rw [sigBoundsOf_names] at hmem
                have hf_eq : q.1.1 = f.name := e
                exact hnd.1 (hf_eq ▸ hmem)) g
            rw [hsw]
            have h0 := hsig g bg hg
            rwa [hsb, List.cons_append] at h0
          have ih := compileModule_append hrest h₂ hnd.2 hsig'
          rw [List.cons_append, List.cons_append]
          dsimp only [compileModule]
          rw [hl, hchk]
          dsimp only
          rw [ih]
          simp only [List.append_assoc, List.cons_append]

/-! ## 3. Literal-backed `Compiled` constructors (`checkCompileLit`, `compileCheckedLit`) -/

/-- Metadata-only validity check over pre-evaluated literal `(code, bounds)` (does not invoke
`compileModule`), used with `compileCheckedLit` so downstream `checkLink*` never re-runs the
compiler. -/
@[expose] def checkCompileLit {D : Type} (label : Sym → D) (progSmall : List D → Bool)
    (code : List D) (bounds : List (Sym × Nat))
    (fnNames exits : List Sym) (maxBound : Nat) : Bool :=
  checkCompileResult label progSmall (.ok (code, bounds)) fnNames exits maxBound

/-- Variant of `checkCompileLit` checking label uniqueness via `labelsNodup`. -/
@[expose] def checkCompileLitWithLabels {D : Type} (label : Sym → D)
    (labelsNodup progSmall : List D → Bool)
    (code : List D) (bounds : List (Sym × Nat))
    (fnNames exits : List Sym) (maxBound : Nat) : Bool :=
  checkCompileResultWithLabels label labelsNodup progSmall (.ok (code, bounds))
    fnNames exits maxBound

private theorem extractCode_ok {D : Type} (c : List D) (b : List (Sym × Nat)) :
    extractCode (.ok (c, b)) = c := by
  unfold extractCode; rfl

private theorem extractBounds_ok {D : Type} (c : List D) (b : List (Sym × Nat)) :
    extractBounds (.ok (c, b)) = b := by
  unfold extractBounds; rfl

/-- Construct a literal-backed `Compiled` bundle from pre-evaluated `(code, bounds)` literals,
a one-shot `compileModule` kernel proof `hcm`, and a fast metadata check `hchk`. Unlike
`MainLemmas.compileChecked` (whose `extractCode`/`extractBounds` fields force `compileModule`
whenever read in `t_kernel_rfl`), this stores `code` and `bounds` directly so downstream
`sigBounds`, `checkLink`, and `checkLinkList` are purely metadata-only. -/
@[expose] def compileCheckedLit (T : Target) (L : TargetLayout T) (lt : LegalTarget)
    (hcl : Rega.LabelClean T.toIsa) (extCallees : List (SigEntry × Nat)) (exits : List Sym)
    (nX : Nat) (fs : List Fn) (hints : List T.toIsa.Hints) (maxBound : Nat := 2048)
    (code : List T.Directive) (bounds : List (Sym × Nat))
    (hcm : compileModule T.toIsa lt T.frame.raBytes extCallees exits nX fs hints =
      .ok (code, bounds))
    (hchk : checkCompileLit T.frame.label L.progSmall code bounds (fs.map Fn.name) exits
      maxBound = true) :
    Compiled T lt extCallees exits nX fs hints maxBound where
  code := code
  bounds := bounds
  compileModule_eq := hcm
  compile_eq := compile_of_compileModule hcm
  bound_mem hnm := by
    have hp := checkCompileResult_parts hchk
    simp only [extractBounds_ok] at hp
    have hm := bound_mem_of_all (res := .ok (code, bounds)) rfl hp.2.2.2.2.2.2 hnm
    rwa [extractBounds_ok] at hm
  bound_le nm := by
    have hp := checkCompileResult_parts hchk
    simp only [extractBounds_ok] at hp
    have hl := bound_le_of_all (res := .ok (code, bounds)) rfl hp.2.2.2.2.2.1 nm
    rwa [extractBounds_ok] at hl
  host := L.layoutOf (code ++ exits.map T.frame.label) (by
    have hp := checkCompileResult_parts hchk
    simpa [extractCode_ok] using hp.2.2.2.2.1)
  prog_host := L.prog_layoutOf _ _
  labelsUnique := by
    have hp := checkCompileResult_parts hchk
    intro i j l hi hj
    rw [L.prog_layoutOf _ (by simpa [extractCode_ok] using hp.2.2.2.2.1)] at hi hj
    exact compileModule_labelsUnique hcl hcm hp.2.2.2.1
      (by simp only [List.all_append, Bool.and_eq_true]; exact ⟨hp.2.1, hp.2.2.1⟩) i j l hi hj

/-- Variant of `compileCheckedLit` using `checkCompileLitWithLabels` and
`L.labelsUnique_layoutOf`. -/
@[expose] def compileCheckedLitWithLabels (T : Target) (L : TargetLayout T) (lt : LegalTarget)
    (extCallees : List (SigEntry × Nat)) (exits : List Sym)
    (nX : Nat) (fs : List Fn) (hints : List T.toIsa.Hints) (maxBound : Nat := 2048)
    (code : List T.Directive) (bounds : List (Sym × Nat))
    (hcm : compileModule T.toIsa lt T.frame.raBytes extCallees exits nX fs hints =
      .ok (code, bounds))
    (hchk : checkCompileLitWithLabels T.frame.label L.labelsNodup L.progSmall code bounds
      (fs.map Fn.name) exits maxBound = true) :
    Compiled T lt extCallees exits nX fs hints maxBound where
  code := code
  bounds := bounds
  compileModule_eq := hcm
  compile_eq := compile_of_compileModule hcm
  bound_mem hnm := by
    have hp := checkWithLabels_parts hchk
    simp only [extractBounds_ok] at hp
    have hm := bound_mem_of_all (res := .ok (code, bounds)) rfl hp.2.2.2.2 hnm
    rwa [extractBounds_ok] at hm
  bound_le nm := by
    have hp := checkWithLabels_parts hchk
    simp only [extractBounds_ok] at hp
    have hl := bound_le_of_all (res := .ok (code, bounds)) rfl hp.2.2.2.1 nm
    rwa [extractBounds_ok] at hl
  host := L.layoutOf (code ++ exits.map T.frame.label) (by
    have hp := checkWithLabels_parts hchk
    simpa [extractCode_ok] using hp.2.2.1)
  prog_host := L.prog_layoutOf _ _
  labelsUnique := L.labelsUnique_layoutOf
    (by simpa [extractCode_ok] using (checkWithLabels_parts hchk).2.2.1)
    (by simpa [extractCode_ok] using (checkWithLabels_parts hchk).2.1)

/-! ## 4. Pairwise O(N) metadata-only linker (`checkLink`, `linkCompiled`) -/

/-- Metadata-only O(N) linker validator using structural `fnNameOk` + `stringsNodup` + `L.progSmall`
(when `M₁`, `M₂` are literal-backed via `compileCheckedLit`, kernel evaluation never re-runs
`compileFn`, `Rega.lowerFn`, or `compileModule`). -/
@[expose] def checkLink {T : Target} (L : TargetLayout T) {lt : LegalTarget}
    {ext₀ : List (SigEntry × Nat)} {exits : List Sym} {nX : Nat}
    {fs₁ : List Fn} {hints₁ : List T.toIsa.Hints} {maxB₁ : Nat}
    {fs₂ : List Fn} {hints₂ : List T.toIsa.Hints} {maxB₂ : Nat}
    (M₁ : Compiled T lt ext₀ exits nX fs₁ hints₁ maxB₁)
    (M₂ : Compiled T lt (M₁.sigBounds ++ ext₀) exits nX fs₂ hints₂ maxB₂) : Bool :=
  let fnNames := fs₁.map Fn.name ++ fs₂.map Fn.name
  let prog := M₁.code ++ M₂.code ++ exits.map T.frame.label
  fnNames.all fnNameOk &&
  exits.all fnNameOk &&
  stringsNodup (fnNames ++ exits) &&
  L.progSmall prog

/-- Variant of `checkLink` checking label uniqueness via `L.labelsNodup`. -/
@[expose] def checkLinkWithLabels {T : Target} (L : TargetLayout T) {lt : LegalTarget}
    {ext₀ : List (SigEntry × Nat)} {exits : List Sym} {nX : Nat}
    {fs₁ : List Fn} {hints₁ : List T.toIsa.Hints} {maxB₁ : Nat}
    {fs₂ : List Fn} {hints₂ : List T.toIsa.Hints} {maxB₂ : Nat}
    (M₁ : Compiled T lt ext₀ exits nX fs₁ hints₁ maxB₁)
    (M₂ : Compiled T lt (M₁.sigBounds ++ ext₀) exits nX fs₂ hints₂ maxB₂) : Bool :=
  let fnNames := fs₁.map Fn.name ++ fs₂.map Fn.name
  let prog := M₁.code ++ M₂.code ++ exits.map T.frame.label
  stringsNodup (fnNames ++ exits) &&
  L.labelsNodup prog &&
  L.progSmall prog

theorem checkLink_parts {T : Target} {L : TargetLayout T} {lt : LegalTarget}
    {ext₀ : List (SigEntry × Nat)} {exits : List Sym} {nX : Nat}
    {fs₁ : List Fn} {hints₁ : List T.toIsa.Hints} {maxB₁ : Nat}
    {fs₂ : List Fn} {hints₂ : List T.toIsa.Hints} {maxB₂ : Nat}
    {M₁ : Compiled T lt ext₀ exits nX fs₁ hints₁ maxB₁}
    {M₂ : Compiled T lt (M₁.sigBounds ++ ext₀) exits nX fs₂ hints₂ maxB₂}
    (h : checkLink L M₁ M₂ = true) :
    ((fs₁ ++ fs₂).map Fn.name).all fnNameOk = true ∧
      exits.all fnNameOk = true ∧
      ((fs₁ ++ fs₂).map Fn.name ++ exits).Nodup ∧
      L.progSmall (M₁.code ++ M₂.code ++ exits.map T.frame.label) = true := by
  dsimp only [checkLink] at h
  simp only [Bool.and_eq_true] at h
  refine ⟨?_, h.1.1.2, ?_, h.2⟩
  · simpa [List.map_append] using h.1.1.1
  · simpa [List.map_append] using stringsNodup_nodup h.1.2

theorem checkLinkWithLabels_parts {T : Target} {L : TargetLayout T} {lt : LegalTarget}
    {ext₀ : List (SigEntry × Nat)} {exits : List Sym} {nX : Nat}
    {fs₁ : List Fn} {hints₁ : List T.toIsa.Hints} {maxB₁ : Nat}
    {fs₂ : List Fn} {hints₂ : List T.toIsa.Hints} {maxB₂ : Nat}
    {M₁ : Compiled T lt ext₀ exits nX fs₁ hints₁ maxB₁}
    {M₂ : Compiled T lt (M₁.sigBounds ++ ext₀) exits nX fs₂ hints₂ maxB₂}
    (h : checkLinkWithLabels L M₁ M₂ = true) :
    ((fs₁ ++ fs₂).map Fn.name ++ exits).Nodup ∧
      L.labelsNodup (M₁.code ++ M₂.code ++ exits.map T.frame.label) = true ∧
      L.progSmall (M₁.code ++ M₂.code ++ exits.map T.frame.label) = true := by
  dsimp only [checkLinkWithLabels] at h
  simp only [Bool.and_eq_true] at h
  exact ⟨by simpa [List.map_append] using stringsNodup_nodup h.1.1, h.1.2, h.2⟩

theorem compileModule_pair_eq {T : Target} {lt : LegalTarget}
    {ext₀ : List (SigEntry × Nat)} {exits : List Sym} {nX : Nat}
    {fs₁ : List Fn} {hints₁ : List T.toIsa.Hints} {maxB₁ : Nat}
    {fs₂ : List Fn} {hints₂ : List T.toIsa.Hints} {maxB₂ : Nat}
    (M₁ : Compiled T lt ext₀ exits nX fs₁ hints₁ maxB₁)
    (M₂ : Compiled T lt (M₁.sigBounds ++ ext₀) exits nX fs₂ hints₂ maxB₂)
    (hnd : ((fs₁ ++ fs₂).map Fn.name ++ exits).Nodup) :
    compileModule T.toIsa lt T.frame.raBytes ext₀ exits nX (fs₁ ++ fs₂) (hints₁ ++ hints₂) =
      .ok (M₁.code ++ M₂.code, M₁.bounds ++ M₂.bounds) := by
  have hfns : (fs₁.map Fn.name ++ fs₂.map Fn.name).Nodup := by
    simpa [List.map_append] using (List.nodup_append.mp hnd).1
  exact compileModule_append M₁.compileModule_eq M₂.compileModule_eq
    (List.nodup_append.mp hfns).1 (fun _ _ hg => by simpa [sigBoundsOf_eq] using hg)

theorem pair_bound_mem {T : Target} {lt : LegalTarget}
    {ext₀ : List (SigEntry × Nat)} {exits : List Sym} {nX : Nat}
    {fs₁ : List Fn} {hints₁ : List T.toIsa.Hints} {maxB₁ : Nat}
    {fs₂ : List Fn} {hints₂ : List T.toIsa.Hints} {maxB₂ : Nat}
    (M₁ : Compiled T lt ext₀ exits nX fs₁ hints₁ maxB₁)
    (M₂ : Compiled T lt (M₁.sigBounds ++ ext₀) exits nX fs₂ hints₂ maxB₂)
    {nm : Sym} (hnm : nm ∈ (fs₁ ++ fs₂).map Fn.name) :
    (nm, (lookupFnBound (M₁.bounds ++ M₂.bounds) nm).getD 0) ∈ M₁.bounds ++ M₂.bounds := by
  have hb1 : M₁.bounds.map Prod.fst = fs₁.map Fn.name :=
    compileModule_bounds_names M₁.compileModule_eq
  rw [List.map_append, List.mem_append] at hnm
  rcases hnm with h1 | h2
  · rw [lookupFnBound_append_left (hb1 ▸ h1)]
    exact List.mem_append_left _ (M₁.bound_mem h1)
  · by_cases hm1 : nm ∈ M₁.bounds.map Prod.fst
    · rw [lookupFnBound_append_left hm1]
      exact List.mem_append_left _ (M₁.bound_mem (hb1 ▸ hm1))
    · rw [lookupFnBound_append_right hm1]
      exact List.mem_append_right _ (M₂.bound_mem h2)

theorem pair_bound_le {T : Target} {lt : LegalTarget}
    {ext₀ : List (SigEntry × Nat)} {exits : List Sym} {nX : Nat}
    {fs₁ : List Fn} {hints₁ : List T.toIsa.Hints} {maxB₁ : Nat}
    {fs₂ : List Fn} {hints₂ : List T.toIsa.Hints} {maxB₂ : Nat}
    (M₁ : Compiled T lt ext₀ exits nX fs₁ hints₁ maxB₁)
    (M₂ : Compiled T lt (M₁.sigBounds ++ ext₀) exits nX fs₂ hints₂ maxB₂)
    (nm : Sym) :
    (lookupFnBound (M₁.bounds ++ M₂.bounds) nm).getD 0 ≤ Nat.max maxB₁ maxB₂ := by
  by_cases hm1 : nm ∈ M₁.bounds.map Prod.fst
  · rw [lookupFnBound_append_left hm1]
    exact Nat.le_trans (M₁.bound_le nm) (Nat.le_max_left _ _)
  · rw [lookupFnBound_append_right hm1]
    exact Nat.le_trans (M₂.bound_le nm) (Nat.le_max_right _ _)

/-- Link two pre-verified `Compiled` chunks into one `Compiled` over `fs₁ ++ fs₂` using only
metadata validation (`checkLink`) and `hcl : Rega.LabelClean T.toIsa`. -/
@[expose] def linkCompiled {T : Target} (L : TargetLayout T) {lt : LegalTarget}
    (hcl : Rega.LabelClean T.toIsa)
    {ext₀ : List (SigEntry × Nat)} {exits : List Sym} {nX : Nat}
    {fs₁ : List Fn} {hints₁ : List T.toIsa.Hints} {maxB₁ : Nat}
    {fs₂ : List Fn} {hints₂ : List T.toIsa.Hints} {maxB₂ : Nat}
    (M₁ : Compiled T lt ext₀ exits nX fs₁ hints₁ maxB₁)
    (M₂ : Compiled T lt (M₁.sigBounds ++ ext₀) exits nX fs₂ hints₂ maxB₂)
    (h : checkLink L M₁ M₂ = true) :
    Compiled T lt ext₀ exits nX (fs₁ ++ fs₂) (hints₁ ++ hints₂) (Nat.max maxB₁ maxB₂) where
  code := M₁.code ++ M₂.code
  bounds := M₁.bounds ++ M₂.bounds
  compileModule_eq := compileModule_pair_eq M₁ M₂ (checkLink_parts h).2.2.1
  compile_eq := compile_of_compileModule (compileModule_pair_eq M₁ M₂ (checkLink_parts h).2.2.1)
  bound_mem := pair_bound_mem M₁ M₂
  bound_le := pair_bound_le M₁ M₂
  host := L.layoutOf (M₁.code ++ M₂.code ++ exits.map T.frame.label) (checkLink_parts h).2.2.2
  prog_host := L.prog_layoutOf _ _
  labelsUnique := by
    have hp := checkLink_parts h
    have hcm := compileModule_pair_eq M₁ M₂ hp.2.2.1
    intro i j l hi hj
    rw [L.prog_layoutOf _ hp.2.2.2] at hi hj
    exact compileModule_labelsUnique hcl hcm hp.2.2.1
      (by simp only [List.all_append, Bool.and_eq_true]; exact ⟨hp.1, hp.2.1⟩) i j l hi hj

/-- Variant of `linkCompiled` using `checkLinkWithLabels` and `L.labelsUnique_layoutOf`. -/
@[expose] def linkCompiledWithLabels {T : Target} (L : TargetLayout T) {lt : LegalTarget}
    {ext₀ : List (SigEntry × Nat)} {exits : List Sym} {nX : Nat}
    {fs₁ : List Fn} {hints₁ : List T.toIsa.Hints} {maxB₁ : Nat}
    {fs₂ : List Fn} {hints₂ : List T.toIsa.Hints} {maxB₂ : Nat}
    (M₁ : Compiled T lt ext₀ exits nX fs₁ hints₁ maxB₁)
    (M₂ : Compiled T lt (M₁.sigBounds ++ ext₀) exits nX fs₂ hints₂ maxB₂)
    (h : checkLinkWithLabels L M₁ M₂ = true) :
    Compiled T lt ext₀ exits nX (fs₁ ++ fs₂) (hints₁ ++ hints₂) (Nat.max maxB₁ maxB₂) where
  code := M₁.code ++ M₂.code
  bounds := M₁.bounds ++ M₂.bounds
  compileModule_eq := compileModule_pair_eq M₁ M₂ (checkLinkWithLabels_parts h).1
  compile_eq :=
    compile_of_compileModule (compileModule_pair_eq M₁ M₂ (checkLinkWithLabels_parts h).1)
  bound_mem := pair_bound_mem M₁ M₂
  bound_le := pair_bound_le M₁ M₂
  host := L.layoutOf (M₁.code ++ M₂.code ++ exits.map T.frame.label)
    (checkLinkWithLabels_parts h).2.2
  prog_host := L.prog_layoutOf _ _
  labelsUnique :=
    L.labelsUnique_layoutOf (checkLinkWithLabels_parts h).2.2 (checkLinkWithLabels_parts h).2.1

theorem linkCompiled_bound_left {T : Target} {L : TargetLayout T} {lt : LegalTarget}
    {hcl : Rega.LabelClean T.toIsa}
    {ext₀ : List (SigEntry × Nat)} {exits : List Sym} {nX : Nat}
    {fs₁ : List Fn} {hints₁ : List T.toIsa.Hints} {maxB₁ : Nat}
    {fs₂ : List Fn} {hints₂ : List T.toIsa.Hints} {maxB₂ : Nat}
    (M₁ : Compiled T lt ext₀ exits nX fs₁ hints₁ maxB₁)
    (M₂ : Compiled T lt (M₁.sigBounds ++ ext₀) exits nX fs₂ hints₂ maxB₂)
    (h : checkLink L M₁ M₂ = true) {nm : Sym} (hnm : nm ∈ fs₁.map Fn.name) :
    (linkCompiled L hcl M₁ M₂ h).bound nm = M₁.bound nm := by
  have hb1 : M₁.bounds.map Prod.fst = fs₁.map Fn.name :=
    compileModule_bounds_names M₁.compileModule_eq
  dsimp only [Compiled.bound, linkCompiled]
  rw [lookupFnBound_append_left (hb1 ▸ hnm)]

theorem linkCompiled_bound_right {T : Target} {L : TargetLayout T} {lt : LegalTarget}
    {hcl : Rega.LabelClean T.toIsa}
    {ext₀ : List (SigEntry × Nat)} {exits : List Sym} {nX : Nat}
    {fs₁ : List Fn} {hints₁ : List T.toIsa.Hints} {maxB₁ : Nat}
    {fs₂ : List Fn} {hints₂ : List T.toIsa.Hints} {maxB₂ : Nat}
    (M₁ : Compiled T lt ext₀ exits nX fs₁ hints₁ maxB₁)
    (M₂ : Compiled T lt (M₁.sigBounds ++ ext₀) exits nX fs₂ hints₂ maxB₂)
    (h : checkLink L M₁ M₂ = true) {nm : Sym} (hnm : nm ∈ fs₂.map Fn.name) :
    (linkCompiled L hcl M₁ M₂ h).bound nm = M₂.bound nm := by
  have hp := (checkLink_parts h).2.2.1
  have hfns : (fs₁.map Fn.name ++ fs₂.map Fn.name).Nodup := by
    simpa [List.map_append] using (List.nodup_append.mp hp).1
  have hdisj := (List.nodup_append.mp hfns).2.2
  have hb1 : M₁.bounds.map Prod.fst = fs₁.map Fn.name :=
    compileModule_bounds_names M₁.compileModule_eq
  have hnot : nm ∉ M₁.bounds.map Prod.fst := by
    rw [hb1]
    intro h1
    exact hdisj nm h1 nm hnm rfl
  dsimp only [Compiled.bound, linkCompiled]
  rw [lookupFnBound_append_right hnot]

/-! ## 5. Multi-chunk list linking (`CompiledChunk`, `checkLinkList`, `linkCompiledList`) -/

/-- Type-erased compiled chunk over fixed target `T`, legalization `lt`, `exits`, and `nX`. -/
structure CompiledChunk (T : Target) (lt : LegalTarget) (exits : List Sym) (nX : Nat) where
  extCallees : List (SigEntry × Nat)
  fs : List Fn
  hints : List T.toIsa.Hints
  maxBound : Nat
  compiled : Compiled T lt extCallees exits nX fs hints maxBound

/-- Concatenated directive stream of a chunk list. -/
@[expose] def chunksCode {T : Target} {lt : LegalTarget} {exits : List Sym} {nX : Nat} :
    List (CompiledChunk T lt exits nX) → List T.Directive
  | [] => []
  | c :: cs => c.compiled.code ++ chunksCode cs

/-- Concatenated typed functions of a chunk list. -/
@[expose] def chunksFns {T : Target} {lt : LegalTarget} {exits : List Sym} {nX : Nat} :
    List (CompiledChunk T lt exits nX) → List Fn
  | [] => []
  | c :: cs => c.fs ++ chunksFns cs

/-- Concatenated register-allocation hints of a chunk list. -/
@[expose] def chunksHints {T : Target} {lt : LegalTarget} {exits : List Sym} {nX : Nat} :
    List (CompiledChunk T lt exits nX) → List T.toIsa.Hints
  | [] => []
  | c :: cs => c.hints ++ chunksHints cs

/-- Concatenated stack bounds of a chunk list. -/
@[expose] def chunksBounds {T : Target} {lt : LegalTarget} {exits : List Sym} {nX : Nat} :
    List (CompiledChunk T lt exits nX) → List (Sym × Nat)
  | [] => []
  | c :: cs => c.compiled.bounds ++ chunksBounds cs

/-- Maximum stack-frame bound across a chunk list. -/
@[expose] def chunksMaxBound {T : Target} {lt : LegalTarget} {exits : List Sym} {nX : Nat} :
    List (CompiledChunk T lt exits nX) → Nat
  | [] => 0
  | c :: cs => Nat.max c.maxBound (chunksMaxBound cs)

@[expose] def sigEntryNatBeq (a b : SigEntry × Nat) : Bool :=
  SigEntry.beq a.1 b.1 && (a.2 == b.2)

theorem sigEntryNatBeq_iff_eq {a b : SigEntry × Nat} :
    sigEntryNatBeq a b = true ↔ a = b := by
  rcases a with ⟨sa, na⟩; rcases b with ⟨sb, nb⟩
  dsimp only [sigEntryNatBeq]; simp [SigEntry.beq_iff_eq]

@[expose] def extListBeq : List (SigEntry × Nat) → List (SigEntry × Nat) → Bool
  | [], [] => true
  | a :: as, b :: bs => sigEntryNatBeq a b && extListBeq as bs
  | _, _ => false

theorem extListBeq_eq : ∀ {xs ys : List (SigEntry × Nat)},
    extListBeq xs ys = true → xs = ys
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by
    dsimp only [extListBeq] at h
    simp only [Bool.and_eq_true, sigEntryNatBeq_iff_eq] at h
    rw [h.1, extListBeq_eq h.2]

@[expose] def checkExtCompat (acc ext : List (SigEntry × Nat)) : Bool :=
  extListBeq ext acc || ext.all (fun p => lookupBound acc p.1 == some p.2)

theorem checkExtCompat_lookupBound {acc ext : List (SigEntry × Nat)}
    (h : checkExtCompat acc ext = true) :
    ∀ g bg, lookupBound ext g = some bg → lookupBound acc g = some bg := by
  dsimp only [checkExtCompat] at h
  simp only [Bool.or_eq_true] at h
  rcases h with heq | hall
  · rw [extListBeq_eq heq]; exact fun _ _ hg => hg
  · intro g bg hg
    exact beq_iff_eq.mp (List.all_eq_true.mp hall (g, bg) (lookupBound_mem hg))

/-- Check that every chunk's `extCallees` is compatible with the accumulated `sigBounds` of
preceding chunks plus `ext₀`. -/
@[expose] def checkChunksExt {T : Target} {lt : LegalTarget} {exits : List Sym} {nX : Nat}
    (acc : List (SigEntry × Nat)) : List (CompiledChunk T lt exits nX) → Bool
  | [] => true
  | c :: cs =>
    checkExtCompat acc c.extCallees &&
    checkChunksExt (c.compiled.sigBounds ++ acc) cs

/-- O(N) metadata-only linker validator for a list of pre-compiled chunks using structural
`fnNameOk` + `stringsNodup` + `L.progSmall` (with zero compiler re-evaluation when chunks are
literal-backed via `compileCheckedLit`). -/
@[expose] def checkLinkList {T : Target} (L : TargetLayout T) {lt : LegalTarget}
    {exits : List Sym} {nX : Nat} (ext₀ : List (SigEntry × Nat))
    (chunks : List (CompiledChunk T lt exits nX)) : Bool :=
  let fnNames := (chunksFns chunks).map Fn.name
  let prog := chunksCode chunks ++ exits.map T.frame.label
  checkChunksExt ext₀ chunks &&
  fnNames.all fnNameOk &&
  exits.all fnNameOk &&
  stringsNodup (fnNames ++ exits) &&
  L.progSmall prog

/-- Variant of `checkLinkList` checking label uniqueness via `L.labelsNodup`. -/
@[expose] def checkLinkListWithLabels {T : Target} (L : TargetLayout T) {lt : LegalTarget}
    {exits : List Sym} {nX : Nat} (ext₀ : List (SigEntry × Nat))
    (chunks : List (CompiledChunk T lt exits nX)) : Bool :=
  let fnNames := (chunksFns chunks).map Fn.name
  let prog := chunksCode chunks ++ exits.map T.frame.label
  checkChunksExt ext₀ chunks &&
  stringsNodup (fnNames ++ exits) &&
  L.labelsNodup prog &&
  L.progSmall prog

theorem checkLinkList_parts {T : Target} {L : TargetLayout T} {lt : LegalTarget}
    {exits : List Sym} {nX : Nat} {ext₀ : List (SigEntry × Nat)}
    {chunks : List (CompiledChunk T lt exits nX)}
    (h : checkLinkList L ext₀ chunks = true) :
    checkChunksExt ext₀ chunks = true ∧
      ((chunksFns chunks).map Fn.name).all fnNameOk = true ∧
      exits.all fnNameOk = true ∧
      ((chunksFns chunks).map Fn.name ++ exits).Nodup ∧
      L.progSmall (chunksCode chunks ++ exits.map T.frame.label) = true := by
  dsimp only [checkLinkList] at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, stringsNodup_nodup h.1.2, h.2⟩

theorem checkLinkListWithLabels_parts {T : Target} {L : TargetLayout T} {lt : LegalTarget}
    {exits : List Sym} {nX : Nat} {ext₀ : List (SigEntry × Nat)}
    {chunks : List (CompiledChunk T lt exits nX)}
    (h : checkLinkListWithLabels L ext₀ chunks = true) :
    checkChunksExt ext₀ chunks = true ∧
      ((chunksFns chunks).map Fn.name ++ exits).Nodup ∧
      L.labelsNodup (chunksCode chunks ++ exits.map T.frame.label) = true ∧
      L.progSmall (chunksCode chunks ++ exits.map T.frame.label) = true := by
  dsimp only [checkLinkListWithLabels] at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1, stringsNodup_nodup h.1.1.2, h.1.2, h.2⟩

theorem compileModule_chunks_eq {T : Target} {lt : LegalTarget}
    {exits : List Sym} {nX : Nat} :
    ∀ {ext₀ : List (SigEntry × Nat)} (chunks : List (CompiledChunk T lt exits nX)),
      checkChunksExt ext₀ chunks = true →
      ((chunksFns chunks).map Fn.name).Nodup →
      compileModule T.toIsa lt T.frame.raBytes ext₀ exits nX
        (chunksFns chunks) (chunksHints chunks) = .ok (chunksCode chunks, chunksBounds chunks)
  | _, [], _, _ => rfl
  | ext₀, c :: cs, hchk, hnd => by
    dsimp only [checkChunksExt] at hchk
    simp only [Bool.and_eq_true] at hchk
    dsimp only [chunksFns] at hnd
    simp only [List.map_append] at hnd
    have hnd_split := List.nodup_append.mp hnd
    have hc_ext : compileModule T.toIsa lt T.frame.raBytes ext₀ exits nX c.fs c.hints =
        .ok (c.compiled.code, c.compiled.bounds) :=
      compileModule_mono_lookupBound (checkExtCompat_lookupBound hchk.1) c.compiled.compileModule_eq
    have hcs_ext := compileModule_chunks_eq cs hchk.2 hnd_split.2.1
    exact compileModule_append hc_ext hcs_ext hnd_split.1
      (fun _ _ hg => by simpa [sigBoundsOf_eq] using hg)

theorem chunks_bound_mem {T : Target} {lt : LegalTarget}
    {exits : List Sym} {nX : Nat} :
    ∀ (chunks : List (CompiledChunk T lt exits nX)) {nm : Sym},
      nm ∈ (chunksFns chunks).map Fn.name →
      (nm, (lookupFnBound (chunksBounds chunks) nm).getD 0) ∈ chunksBounds chunks
  | [], _, h => nomatch h
  | c :: cs, nm, h => by
    have hb : c.compiled.bounds.map Prod.fst = c.fs.map Fn.name :=
      compileModule_bounds_names c.compiled.compileModule_eq
    dsimp only [chunksFns, chunksBounds] at h ⊢
    simp only [List.map_append, List.mem_append] at h ⊢
    rcases h with hc | hcs
    · rw [lookupFnBound_append_left (hb ▸ hc)]
      exact Or.inl (c.compiled.bound_mem hc)
    · by_cases hm : nm ∈ c.compiled.bounds.map Prod.fst
      · rw [lookupFnBound_append_left hm]
        exact Or.inl (c.compiled.bound_mem (hb ▸ hm))
      · rw [lookupFnBound_append_right hm]
        exact Or.inr (chunks_bound_mem cs hcs)

theorem chunks_bound_le {T : Target} {lt : LegalTarget}
    {exits : List Sym} {nX : Nat} :
    ∀ (chunks : List (CompiledChunk T lt exits nX)) (nm : Sym),
      (lookupFnBound (chunksBounds chunks) nm).getD 0 ≤ chunksMaxBound chunks
  | [], _ => Nat.le_refl 0
  | c :: cs, nm => by
    dsimp only [chunksBounds, chunksMaxBound]
    by_cases hm : nm ∈ c.compiled.bounds.map Prod.fst
    · rw [lookupFnBound_append_left hm]
      exact Nat.le_trans (c.compiled.bound_le nm) (Nat.le_max_left _ _)
    · rw [lookupFnBound_append_right hm]
      exact Nat.le_trans (chunks_bound_le cs nm) (Nat.le_max_right _ _)

/-- Link an arbitrary list of pre-verified `CompiledChunk`s into a single `Compiled` over
`chunksFns chunks` using only O(N) metadata validation (`checkLinkList`). -/
@[expose] def linkCompiledList {T : Target} (L : TargetLayout T) {lt : LegalTarget}
    (hcl : Rega.LabelClean T.toIsa) {exits : List Sym} {nX : Nat}
    (ext₀ : List (SigEntry × Nat)) (chunks : List (CompiledChunk T lt exits nX))
    (h : checkLinkList L ext₀ chunks = true) :
    Compiled T lt ext₀ exits nX (chunksFns chunks) (chunksHints chunks)
      (chunksMaxBound chunks) where
  code := chunksCode chunks
  bounds := chunksBounds chunks
  compileModule_eq :=
    compileModule_chunks_eq chunks (checkLinkList_parts h).1
      (List.nodup_append.mp (checkLinkList_parts h).2.2.2.1).1
  compile_eq := compile_of_compileModule
    (compileModule_chunks_eq chunks (checkLinkList_parts h).1
      (List.nodup_append.mp (checkLinkList_parts h).2.2.2.1).1)
  bound_mem := chunks_bound_mem chunks
  bound_le := chunks_bound_le chunks
  host := L.layoutOf (chunksCode chunks ++ exits.map T.frame.label)
    (checkLinkList_parts h).2.2.2.2
  prog_host := L.prog_layoutOf _ _
  labelsUnique := by
    have hp := checkLinkList_parts h
    have hcm := compileModule_chunks_eq chunks hp.1 (List.nodup_append.mp hp.2.2.2.1).1
    intro i j l hi hj
    rw [L.prog_layoutOf _ hp.2.2.2.2] at hi hj
    exact compileModule_labelsUnique hcl hcm hp.2.2.2.1
      (by simp only [List.all_append, Bool.and_eq_true]; exact ⟨hp.2.1, hp.2.2.1⟩) i j l hi hj

/-- Variant of `linkCompiledList` using `checkLinkListWithLabels` and `L.labelsUnique_layoutOf`. -/
@[expose] def linkCompiledListWithLabels {T : Target} (L : TargetLayout T) {lt : LegalTarget}
    {exits : List Sym} {nX : Nat} (ext₀ : List (SigEntry × Nat))
    (chunks : List (CompiledChunk T lt exits nX))
    (h : checkLinkListWithLabels L ext₀ chunks = true) :
    Compiled T lt ext₀ exits nX (chunksFns chunks) (chunksHints chunks)
      (chunksMaxBound chunks) where
  code := chunksCode chunks
  bounds := chunksBounds chunks
  compileModule_eq :=
    compileModule_chunks_eq chunks (checkLinkListWithLabels_parts h).1
      (List.nodup_append.mp (checkLinkListWithLabels_parts h).2.1).1
  compile_eq := compile_of_compileModule
    (compileModule_chunks_eq chunks (checkLinkListWithLabels_parts h).1
      (List.nodup_append.mp (checkLinkListWithLabels_parts h).2.1).1)
  bound_mem := chunks_bound_mem chunks
  bound_le := chunks_bound_le chunks
  host := L.layoutOf (chunksCode chunks ++ exits.map T.frame.label)
    (checkLinkListWithLabels_parts h).2.2.2
  prog_host := L.prog_layoutOf _ _
  labelsUnique := L.labelsUnique_layoutOf
    (checkLinkListWithLabels_parts h).2.2.2 (checkLinkListWithLabels_parts h).2.2.1

private theorem mem_chunksFns_of_mem {T : Target} {lt : LegalTarget}
    {exits : List Sym} {nX : Nat} {c : CompiledChunk T lt exits nX} {nm : Sym}
    (hnm : nm ∈ c.fs.map Fn.name) :
    ∀ {cs : List (CompiledChunk T lt exits nX)}, c ∈ cs → nm ∈ (chunksFns cs).map Fn.name
  | [], h => nomatch h
  | d :: ds, h => by
    dsimp only [chunksFns]; simp only [List.map_append, List.mem_append]
    rcases List.mem_cons.mp h with rfl | hds
    · exact Or.inl hnm
    · exact Or.inr (mem_chunksFns_of_mem hnm hds)

private theorem chunks_bound_eq_of_mem {T : Target} {lt : LegalTarget}
    {exits : List Sym} {nX : Nat} :
    ∀ (chunks : List (CompiledChunk T lt exits nX)),
      ((chunksFns chunks).map Fn.name).Nodup →
      ∀ c ∈ chunks, ∀ {nm : Sym}, nm ∈ c.fs.map Fn.name →
        (lookupFnBound (chunksBounds chunks) nm).getD 0 = c.compiled.bound nm
  | [], _, _, hc, _, _ => nomatch hc
  | c₀ :: cs, hnd, c, hc, nm, hnm => by
    dsimp only [chunksFns] at hnd; simp only [List.map_append] at hnd
    have hnd_split := List.nodup_append.mp hnd
    have hb0 : c₀.compiled.bounds.map Prod.fst = c₀.fs.map Fn.name :=
      compileModule_bounds_names c₀.compiled.compileModule_eq
    rcases List.mem_cons.mp hc with rfl | hcs
    · dsimp only [chunksBounds, Compiled.bound]
      rw [lookupFnBound_append_left (hb0 ▸ hnm)]
    · have hnm_cs : nm ∈ (chunksFns cs).map Fn.name := mem_chunksFns_of_mem hnm hcs
      have hnot0 : nm ∉ c₀.compiled.bounds.map Prod.fst := by
        rw [hb0]
        intro h0
        exact hnd_split.2.2 nm h0 nm hnm_cs rfl
      dsimp only [chunksBounds]
      rw [lookupFnBound_append_right hnot0]
      exact chunks_bound_eq_of_mem cs hnd_split.2.1 c hcs hnm

theorem linkCompiledList_bound {T : Target} {L : TargetLayout T} {lt : LegalTarget}
    {hcl : Rega.LabelClean T.toIsa} {exits : List Sym} {nX : Nat}
    {ext₀ : List (SigEntry × Nat)} {chunks : List (CompiledChunk T lt exits nX)}
    (h : checkLinkList L ext₀ chunks = true) {c : CompiledChunk T lt exits nX}
    (hc : c ∈ chunks) {nm : Sym} (hnm : nm ∈ c.fs.map Fn.name) :
    (linkCompiledList L hcl ext₀ chunks h).bound nm = c.compiled.bound nm := by
  dsimp only [Compiled.bound, linkCompiledList]
  exact chunks_bound_eq_of_mem chunks
    (List.nodup_append.mp (checkLinkList_parts h).2.2.2.1).1 c hc hnm

/-! ## 6. End-to-end `FnSpec` linking theorems over concatenated hosts -/

/-- Direct `Defined` + `FnSpec` theorem for every function in `mod.fns = fs₁ ++ fs₂` over the
linked host of `linkCompiled`. -/
theorem linkCompiled_fnSpec {T : Target} {L : TargetLayout T} {lt : LegalTarget}
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
  let linked := linkCompiled L hcl M₁ M₂ hchk
  linked.fnSpec mod hfs linked.host Γ 0 linked.code_infix_host linked.labelsUnique
    hacyc hwf hsupp hwp hext hext_uniq (fun _ hg => linked.defined_exit_host hg) hf

/-- Direct `Defined` + `FnSpec` theorem for every function in `mod.fns = chunksFns chunks` over
the linked host of `linkCompiledList`. -/
theorem linkCompiledList_fnSpec {T : Target} {L : TargetLayout T} {lt : LegalTarget}
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
  let linked := linkCompiledList L hcl ext₀ chunks hchk
  linked.fnSpec mod hfs linked.host Γ 0 linked.code_infix_host linked.labelsUnique
    hacyc hwf hsupp hwp hext hext_uniq (fun _ hg => linked.defined_exit_host hg) hf

end LeanQbe.T
