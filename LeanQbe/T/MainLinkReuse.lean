module

public import LeanQbe.T.MainCertCore

/-!
# Callee-Pruned Cross-Target Chunk Reuse (`MainLinkReuse`)

`MainLink.compileModule_mono_lookupBound` lets a pre-verified chunk be relinked under a new
callee table `ext₂` only if `ext₂` preserves **every** `lookupBound` answer of the chunk's
original table `ext₁`. When an earlier function's stack bound changes, or an earlier function is
removed or reordered, that condition fails for every later chunk, even chunks that never call
the changed function.

`compileModule` only looks up the direct callees of each function, namely
`(f.mid lt).ext.callees`. This module weakens the relinking condition to those callees:

* `compileModule_mono_callees`: `compileModule` returns the same `(code, bounds)` under `ext₂` as
  under `ext₁` when the two tables agree on the actual direct callees of `fs`.
* `CalleesCover lt fs S` (`S` lists every direct callee of `fs`) with the kernel-reducible checker
  `checkCalleesCover` and the exact list `midCallees`. `checkExtAgreeOn S ext₁ ext₂` checks that
  the two tables agree on `S`.
* `Compiled.reExt` / `Compiled.relink` / `CompiledChunk.relink`: retype a literal-backed chunk to
  a new callee table, reusing its `code`, `bounds`, `host`, and `labelsUnique` unchanged.
  `CompiledChunk.relinkCover` takes a `CalleesCover` proof built elsewhere.
* `pruneExt S acc`: the entries of `acc` for the callees in `S`, to use as the relinked chunk's
  `extCallees`. `checkLinkList` then checks it against the new accumulator in `|S|` lookups.
* `Fn.rawLegalCallees` / `rawLegalCalleesOf`: an untrusted candidate `S` computed by a single
  walk of the source `f.body`. It evaluates no `earlyOpt`, `Legal`, `lateOpt`, or `Rega`. Its
  `CalleesCover` is not proved here; check it with `checkCalleesCover`, or prove it in a later
  pass-invariance theorem.

Nothing here changes `compileModule`, `Compiled`, `CompiledChunk`, `checkLinkList`, or
`LinkedCert`. A relinked chunk is an ordinary `CompiledChunk`, so `linkCompiledList`,
`LinkedCert`, and every downstream `FnSpec` theorem apply to it unchanged.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T

/-! ## 1. Callee covers and table agreement -/

/-- `S` lists every direct callee signature that `compileModule` looks up for `fs`. -/
@[expose] def CalleesCover (lt : LegalTarget) (fs : List Fn) (S : List SigEntry) : Prop :=
  ∀ f ∈ fs, ∀ g ∈ (f.mid lt).ext.callees, g ∈ S

/-- Exact list of direct callees of `fs`, computed by running the mid-end (no `Rega`). -/
@[expose] def midCallees (lt : LegalTarget) (fs : List Fn) : List SigEntry :=
  fs.flatMap fun f => (f.mid lt).ext.callees

theorem calleesCover_midCallees (lt : LegalTarget) (fs : List Fn) :
    CalleesCover lt fs (midCallees lt fs) := by
  intro f hf g hg
  exact List.mem_flatMap.mpr ⟨f, hf, hg⟩

/-- Kernel-reducible checker for `CalleesCover` (membership via `SigEntry.beq`). -/
@[expose] def checkCalleesCover (lt : LegalTarget) (fs : List Fn) (S : List SigEntry) : Bool :=
  fs.all fun f => (f.mid lt).ext.callees.all fun g => S.any (SigEntry.beq g)

theorem calleesCover_of_check {lt : LegalTarget} {fs : List Fn} {S : List SigEntry}
    (h : checkCalleesCover lt fs S = true) : CalleesCover lt fs S := by
  intro f hf g hg
  have hall := List.all_eq_true.mp (List.all_eq_true.mp h f hf) g hg
  obtain ⟨s, hs, hbeq⟩ := List.any_eq_true.mp hall
  rw [SigEntry.beq_iff_eq.mp hbeq]
  exact hs

theorem CalleesCover.mono {lt : LegalTarget} {fs : List Fn} {S S' : List SigEntry}
    (h : CalleesCover lt fs S) (hsub : ∀ g ∈ S, g ∈ S') : CalleesCover lt fs S' :=
  fun f hf g hg => hsub g (h f hf g hg)

theorem CalleesCover.append {lt : LegalTarget} {fs₁ fs₂ : List Fn} {S : List SigEntry}
    (h₁ : CalleesCover lt fs₁ S) (h₂ : CalleesCover lt fs₂ S) :
    CalleesCover lt (fs₁ ++ fs₂) S := by
  intro f hf
  rcases List.mem_append.mp hf with h | h
  · exact h₁ f h
  · exact h₂ f h

theorem CalleesCover.of_eq {lt : LegalTarget} {fs₁ fs₂ : List Fn} {S : List SigEntry}
    (heq : fs₁ = fs₂) (h : CalleesCover lt fs₂ S) : CalleesCover lt fs₁ S :=
  heq ▸ h

/-- Every `ext₁` answer for a signature in `S` is also an `ext₂` answer. Kernel-reducible. -/
@[expose] def checkExtAgreeOn (S : List SigEntry) (ext₁ ext₂ : List (SigEntry × Nat)) : Bool :=
  S.all fun g => (lookupBound ext₁ g).all fun b => lookupBound ext₂ g == some b

theorem extAgreeOn_of_check {S : List SigEntry} {ext₁ ext₂ : List (SigEntry × Nat)}
    (h : checkExtAgreeOn S ext₁ ext₂ = true) :
    ∀ g ∈ S, ∀ bg, lookupBound ext₁ g = some bg → lookupBound ext₂ g = some bg := by
  intro g hg bg h1
  have hall := List.all_eq_true.mp h g hg
  rw [h1] at hall
  exact beq_iff_eq.mp hall

/-- The entries of `acc` for the callees in `S`: a small literal table to use as the `extCallees`
of a relinked chunk. -/
@[expose] def pruneExt (S : List SigEntry) (acc : List (SigEntry × Nat)) :
    List (SigEntry × Nat) :=
  S.filterMap fun g => (lookupBound acc g).map fun b => (g, b)

/-! ## 2. Callee-pruned `compileModule` monotonicity -/

private theorem calleesBound_mono_on {F raBytes : Nat} {ext₁ ext₂ : List (SigEntry × Nat)} :
    ∀ {gs : List SigEntry} {n : Nat},
      (∀ g ∈ gs, ∀ bg, lookupBound ext₁ g = some bg → lookupBound ext₂ g = some bg) →
      calleesBound F raBytes ext₁ gs = some n → calleesBound F raBytes ext₂ gs = some n
  | [], _, _, h => h
  | g :: gs, n, hmono, h => by
    dsimp only [calleesBound] at h ⊢
    cases h1 : lookupBound ext₁ g with
    | none => simp [h1] at h
    | some bg =>
      cases h2 : calleesBound F raBytes ext₁ gs with
      | none => simp [h1, h2] at h
      | some rest =>
        simp only [h1, h2, Option.some.injEq] at h
        rw [hmono g List.mem_cons_self bg h1,
          calleesBound_mono_on (fun g' hg' => hmono g' (List.mem_cons_of_mem g hg')) h2]
        dsimp only
        rw [h]

private theorem checkAndBoundExt_mono_on {I : Isa} {raBytes : Nat}
    {exits : List Sym} {nX : Nat} {ext₁ ext₂ : List (SigEntry × Nat)}
    {h : I.Hints} {ext : Rega.Ext}
    (hmono : ∀ g ∈ ext.callees, ∀ bg, lookupBound ext₁ g = some bg → lookupBound ext₂ g = some bg)
    {b : Nat} (hc : checkAndBoundExt I raBytes exits nX ext₁ h ext = some b) :
    checkAndBoundExt I raBytes exits nX ext₂ h ext = some b := by
  dsimp only [checkAndBoundExt] at hc ⊢
  cases hcb : calleesBound (Rega.effFrame I h ext) raBytes ext₁ ext.callees with
  | none => simp [hcb] at hc
  | some n₁ =>
    rw [hcb] at hc
    rw [calleesBound_mono_on hmono hcb]
    exact hc

private theorem lookupBound_cons_mono_on {s : SigEntry} {b : Nat}
    {ext₁ ext₂ : List (SigEntry × Nat)} {g : SigEntry}
    (hmono : ∀ bg, lookupBound ext₁ g = some bg → lookupBound ext₂ g = some bg) :
    ∀ bg, lookupBound ((s, b) :: ext₁) g = some bg → lookupBound ((s, b) :: ext₂) g = some bg := by
  intro bg hg
  dsimp only [lookupBound] at hg ⊢; simp only [List.find?] at hg ⊢
  cases hbeq : SigEntry.beq s g
  · simp only [hbeq] at hg ⊢; exact hmono bg hg
  · simp only [hbeq] at hg ⊢; exact hg

/-- **Callee-pruned relinking.** If `ext₂` gives the same answer as `ext₁` for every direct callee
signature of `fs`, `compileModule` succeeds under `ext₂` with the same directive stream and stack
bounds. `ext₂` may differ arbitrarily on everything else: changed bounds of unrelated functions,
removed or reordered entries. -/
theorem compileModule_mono_callees {I : Isa} {lt : LegalTarget} {raBytes : Nat}
    {exits : List Sym} {nX : Nat} :
    ∀ {ext₁ ext₂ : List (SigEntry × Nat)} {fs : List Fn} {hints : List I.Hints}
      {code : List I.Directive} {bounds : List (Sym × Nat)},
      (∀ f ∈ fs, ∀ g ∈ (f.mid lt).ext.callees, ∀ bg,
        lookupBound ext₁ g = some bg → lookupBound ext₂ g = some bg) →
      compileModule I lt raBytes ext₁ exits nX fs hints = .ok (code, bounds) →
      compileModule I lt raBytes ext₂ exits nX fs hints = .ok (code, bounds)
  | _, _, [], [], _, _, _, h => h
  | _, _, [], _ :: _, _, _, _, h => by dsimp only [compileModule] at h; cases h
  | _, _, _ :: _, [], _, _, _, h => by dsimp only [compileModule] at h; cases h
  | ext₁, ext₂, f :: fs, hint :: hints, code, bounds, hmono, h => by
    have hsupp := compileModule_cons_supportsSource h
    rw [compileModule_cons_mid hsupp] at h ⊢
    cases hl : Rega.lowerFn I hint (f.mid lt).ext (f.mid lt) with
    | error e => simp [hl] at h
    | ok c =>
      cases hchk : checkAndBoundExt I raBytes exits nX ext₁ hint (f.mid lt).ext with
      | none => simp [hl, hchk] at h
      | some b =>
        simp only [hl, hchk] at h ⊢
        rw [checkAndBoundExt_mono_on (hmono f List.mem_cons_self) hchk]
        dsimp only
        cases hrest : compileModule I lt raBytes (((f.mid lt).sig, b) :: ext₁) exits nX fs
            hints with
        | error e => simp [hrest] at h
        | ok res =>
          simp only [hrest] at h
          rw [compileModule_mono_callees
            (fun f' hf' g hg => lookupBound_cons_mono_on
              (hmono f' (List.mem_cons_of_mem f hf') g hg)) hrest]
          exact h

/-- `compileModule_mono_callees` stated with a callee cover `S` and table agreement on `S`. -/
theorem compileModule_mono_cover {I : Isa} {lt : LegalTarget} {raBytes : Nat}
    {exits : List Sym} {nX : Nat} {ext₁ ext₂ : List (SigEntry × Nat)} {fs : List Fn}
    {hints : List I.Hints} {code : List I.Directive} {bounds : List (Sym × Nat)}
    {S : List SigEntry} (hcov : CalleesCover lt fs S)
    (hagree : ∀ g ∈ S, ∀ bg, lookupBound ext₁ g = some bg → lookupBound ext₂ g = some bg)
    (h : compileModule I lt raBytes ext₁ exits nX fs hints = .ok (code, bounds)) :
    compileModule I lt raBytes ext₂ exits nX fs hints = .ok (code, bounds) :=
  compileModule_mono_callees (fun f hf g hg => hagree g (hcov f hf g hg)) h

/-- Boolean form of `compileModule_mono_cover` (`checkExtAgreeOn`). -/
theorem compileModule_mono_check {I : Isa} {lt : LegalTarget} {raBytes : Nat}
    {exits : List Sym} {nX : Nat} {ext₁ ext₂ : List (SigEntry × Nat)} {fs : List Fn}
    {hints : List I.Hints} {code : List I.Directive} {bounds : List (Sym × Nat)}
    {S : List SigEntry} (hcov : CalleesCover lt fs S)
    (hagree : checkExtAgreeOn S ext₁ ext₂ = true)
    (h : compileModule I lt raBytes ext₁ exits nX fs hints = .ok (code, bounds)) :
    compileModule I lt raBytes ext₂ exits nX fs hints = .ok (code, bounds) :=
  compileModule_mono_cover hcov (extAgreeOn_of_check hagree) h

/-! ## 3. Retyping literal-backed `Compiled` bundles and `CompiledChunk`s -/

/-- Retype `M` to callee table `ext₂`, given `compileModule` under `ext₂` returns `M`'s
`(code, bounds)`. Every data field (`code`, `bounds`, `host`) is reused verbatim. -/
@[expose] def Compiled.reExt {T : Target} {lt : LegalTarget} {ext₁ : List (SigEntry × Nat)}
    {exits : List Sym} {nX : Nat} {fs : List Fn} {hints : List T.toIsa.Hints} {maxBound : Nat}
    (M : Compiled T lt ext₁ exits nX fs hints maxBound) (ext₂ : List (SigEntry × Nat))
    (h : compileModule T.toIsa lt T.frame.raBytes ext₂ exits nX fs hints = .ok (M.code, M.bounds)) :
    Compiled T lt ext₂ exits nX fs hints maxBound where
  code := M.code
  bounds := M.bounds
  compileModule_eq := h
  compile_eq := M.compile_eq
  bound_mem := M.bound_mem
  bound_le := M.bound_le
  host := M.host
  prog_host := M.prog_host
  labelsUnique := M.labelsUnique

/-- Callee-pruned relink of a `Compiled` bundle to `ext₂`. -/
@[expose] def Compiled.relink {T : Target} {lt : LegalTarget} {ext₁ : List (SigEntry × Nat)}
    {exits : List Sym} {nX : Nat} {fs : List Fn} {hints : List T.toIsa.Hints} {maxBound : Nat}
    (M : Compiled T lt ext₁ exits nX fs hints maxBound) (ext₂ : List (SigEntry × Nat))
    (S : List SigEntry) (hcov : CalleesCover lt fs S)
    (hagree : checkExtAgreeOn S ext₁ ext₂ = true) :
    Compiled T lt ext₂ exits nX fs hints maxBound :=
  M.reExt ext₂ (compileModule_mono_check hcov hagree M.compileModule_eq)

section CompiledFacts

variable {T : Target} {lt : LegalTarget} {ext₁ : List (SigEntry × Nat)}
  {exits : List Sym} {nX : Nat} {fs : List Fn} {hints : List T.toIsa.Hints} {maxBound : Nat}

@[simp] theorem Compiled.reExt_code (M : Compiled T lt ext₁ exits nX fs hints maxBound)
    (ext₂ : List (SigEntry × Nat)) (h) : (M.reExt ext₂ h).code = M.code := rfl

@[simp] theorem Compiled.reExt_bounds (M : Compiled T lt ext₁ exits nX fs hints maxBound)
    (ext₂ : List (SigEntry × Nat)) (h) : (M.reExt ext₂ h).bounds = M.bounds := rfl

@[simp] theorem Compiled.reExt_host (M : Compiled T lt ext₁ exits nX fs hints maxBound)
    (ext₂ : List (SigEntry × Nat)) (h) : (M.reExt ext₂ h).host = M.host := rfl

@[simp] theorem Compiled.reExt_bound (M : Compiled T lt ext₁ exits nX fs hints maxBound)
    (ext₂ : List (SigEntry × Nat)) (h) (nm : Sym) : (M.reExt ext₂ h).bound nm = M.bound nm := rfl

theorem Compiled.reExt_sigBounds (M : Compiled T lt ext₁ exits nX fs hints maxBound)
    (ext₂ : List (SigEntry × Nat)) (h) : (M.reExt ext₂ h).sigBounds = M.sigBounds := rfl

end CompiledFacts

namespace CompiledChunk

variable {T : Target} {lt : LegalTarget} {exits : List Sym} {nX : Nat}

/-- Relink chunk `c` to callee table `ext₂`, given any `CalleesCover` proof for `c.fs` (for
example a stored literal-cover theorem from the chunk's original build). -/
@[expose] def relinkCover (c : CompiledChunk T lt exits nX) (ext₂ : List (SigEntry × Nat))
    (S : List SigEntry) (hcov : CalleesCover lt c.fs S)
    (hagree : checkExtAgreeOn S c.extCallees ext₂ = true) : CompiledChunk T lt exits nX where
  extCallees := ext₂
  fs := c.fs
  hints := c.hints
  maxBound := c.maxBound
  compiled := c.compiled.relink ext₂ S hcov hagree

/-- Relink chunk `c` to callee table `ext₂` with kernel-checked cover `S` and agreement. -/
@[expose] def relink (c : CompiledChunk T lt exits nX) (ext₂ : List (SigEntry × Nat))
    (S : List SigEntry) (hcov : checkCalleesCover lt c.fs S = true)
    (hagree : checkExtAgreeOn S c.extCallees ext₂ = true) : CompiledChunk T lt exits nX :=
  c.relinkCover ext₂ S (calleesCover_of_check hcov) hagree

variable (c : CompiledChunk T lt exits nX) (ext₂ : List (SigEntry × Nat)) (S : List SigEntry)

@[simp] theorem relinkCover_extCallees (hcov hagree) :
    (c.relinkCover ext₂ S hcov hagree).extCallees = ext₂ := rfl
@[simp] theorem relinkCover_fs (hcov hagree) : (c.relinkCover ext₂ S hcov hagree).fs = c.fs := rfl
@[simp] theorem relinkCover_hints (hcov hagree) :
    (c.relinkCover ext₂ S hcov hagree).hints = c.hints := rfl
@[simp] theorem relinkCover_maxBound (hcov hagree) :
    (c.relinkCover ext₂ S hcov hagree).maxBound = c.maxBound := rfl
@[simp] theorem relinkCover_code (hcov hagree) :
    (c.relinkCover ext₂ S hcov hagree).compiled.code = c.compiled.code := rfl
@[simp] theorem relinkCover_bounds (hcov hagree) :
    (c.relinkCover ext₂ S hcov hagree).compiled.bounds = c.compiled.bounds := rfl
@[simp] theorem relinkCover_host (hcov hagree) :
    (c.relinkCover ext₂ S hcov hagree).compiled.host = c.compiled.host := rfl

@[simp] theorem relink_extCallees (hcov hagree) : (c.relink ext₂ S hcov hagree).extCallees = ext₂ :=
  rfl
@[simp] theorem relink_fs (hcov hagree) : (c.relink ext₂ S hcov hagree).fs = c.fs := rfl
@[simp] theorem relink_hints (hcov hagree) : (c.relink ext₂ S hcov hagree).hints = c.hints := rfl
@[simp] theorem relink_maxBound (hcov hagree) :
    (c.relink ext₂ S hcov hagree).maxBound = c.maxBound := rfl
@[simp] theorem relink_code (hcov hagree) :
    (c.relink ext₂ S hcov hagree).compiled.code = c.compiled.code := rfl
@[simp] theorem relink_bounds (hcov hagree) :
    (c.relink ext₂ S hcov hagree).compiled.bounds = c.compiled.bounds := rfl
@[simp] theorem relink_host (hcov hagree) :
    (c.relink ext₂ S hcov hagree).compiled.host = c.compiled.host := rfl

end CompiledChunk

/-! ## 4. Untrusted source-level callee candidates (`Fn.rawLegalCallees`) -/

mutual
/-- Collect `(g, lt.legalSig as, lt.legalSig bs)` for every `.call g` in a source body, over both
arms of every `.jnz` and every block of every `.group`. -/
@[expose] def Expr.rawLegalCallsAux (lt : LegalTarget) {rs : List Ty} :
    Expr (fun _ => Unit) (fun _ => Unit) rs → List SigEntry → List SigEntry
  | .let_ (ts := ts) _ k, cs => Expr.rawLegalCallsAux lt (k (Tup.units ts)) cs
  | .load _ _ k, cs => Expr.rawLegalCallsAux lt (k ()) cs
  | .store _ _ k, cs => Expr.rawLegalCallsAux lt k cs
  | .call g (as := as) (bs := bs) _ k, cs =>
    Expr.rawLegalCallsAux lt (k (Tup.units bs)) (addCalleeSig g (lt.legalSig as) (lt.legalSig bs) cs)
  | .jnz _ t e, cs => Expr.rawLegalCallsAux lt t (Expr.rawLegalCallsAux lt e cs)
  | .jump _ _, cs | .ret _, cs | .hlt, cs | .exit _ _, cs => cs
  | .group (sig := sig) bodies k, cs =>
    let ls := Tup.units sig
    Blocks.rawLegalCallsAux lt (bodies ls) (Expr.rawLegalCallsAux lt (k ls) cs)

/-- Mutual helper for `Expr.rawLegalCallsAux` over `Blocks`. -/
@[expose] def Blocks.rawLegalCallsAux (lt : LegalTarget) {rs : List Ty} :
    {sig : List (List Ty)} → Blocks (fun _ => Unit) (fun _ => Unit) rs sig →
    List SigEntry → List SigEntry
  | _, .nil, cs => cs
  | _, .cons (ts := ts) b bs, cs =>
    Blocks.rawLegalCallsAux lt bs (Expr.rawLegalCallsAux lt (b (Tup.units ts)) cs)
end

/-- Untrusted candidate callee list of `f` after legalization, from one walk of `f.body`. -/
@[expose] def Fn.rawLegalCallees (lt : LegalTarget) (f : Fn) : List SigEntry :=
  Expr.rawLegalCallsAux lt (f.body (fun _ => Unit) (fun _ => Unit) (Tup.units f.as)) []

/-- Untrusted candidate callee list of `fs`; check it with `checkCalleesCover`. -/
@[expose] def rawLegalCalleesOf (lt : LegalTarget) (fs : List Fn) : List SigEntry :=
  fs.flatMap (Fn.rawLegalCallees lt)

end LeanQbe.T
