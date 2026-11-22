module

public import LeanQbe.T.MainLink

/-!
# Core `LinkedCert` Data & Kernel-Reducible Shape Interface (`MainCertCore`)

Pure, `Lean`-meta-free core definitions and structural slice/chunk composition lemmas for
`LinkedCert`. Proof bodies stay opaque in `.olean.private` (only the 10 data/shape definitions
that unfold or project in downstream kernel reductions carry `@[expose]`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T

/-! ## 1. O(#chunks) list-slicing, `supportsSource`, `LegalSigAll`, & stack-bound helpers -/

/-- Adjacent slice identity used to reconstruct `mod.fns = chunksFns chunks` in O(#chunks) steps
without unfolding `mod.fns` or any `Fn.body`. -/
theorem drop_take_append_drop {α : Type _} (l : List α) (s k : Nat) :
    (l.drop s).take k ++ l.drop (s + k) = l.drop s := by
  have hdrop : l.drop (s + k) = (l.drop s).drop k := by
    rw [List.drop_drop, Nat.add_comm]
  rw [hdrop, List.take_append_drop]

/-- Inductive step for building `l.drop s = c_s ++ (c_{s+1} ++ ...)` along chunk boundaries. -/
theorem slice_cons_eq {α : Type _} {l rest : List α} {s k : Nat}
    (h : l.drop (s + k) = rest) :
    l.drop s = (l.drop s).take k ++ rest := by
  rw [← h, drop_take_append_drop]

/-- Terminal chunk identity closing the slice chain at `l.drop s`. -/
theorem slice_last_eq {α : Type _} (l : List α) (s : Nat) :
    l.drop s = l.drop s ++ [] :=
  (List.append_nil _).symm

/-- Kernel-reducible per-chunk `supportsSource` checker. -/
@[expose] def checkSupportsChunk (lt : LegalTarget) (fs : List Fn) : Bool :=
  fs.all (fun f => (f.earlyOpt).body.supportsSource lt)

theorem supportsAll_nil {lt : LegalTarget} :
    ∀ f ∈ ([] : List Fn), (f.earlyOpt).body.supportsSource lt = true :=
  fun _ h => nomatch h

theorem supportsAll_append {lt : LegalTarget} {fs₁ fs₂ : List Fn}
    (h₁ : checkSupportsChunk lt fs₁ = true)
    (h₂ : ∀ f ∈ fs₂, (f.earlyOpt).body.supportsSource lt = true) :
    ∀ f ∈ fs₁ ++ fs₂, (f.earlyOpt).body.supportsSource lt = true := by
  intro f hf
  rcases List.mem_append.mp hf with h1 | h2
  · exact List.all_eq_true.mp h₁ f h1
  · exact h₂ f h2

theorem supportsAll_of_eq {lt : LegalTarget} {fs₁ fs₂ : List Fn} (heq : fs₁ = fs₂)
    (h : ∀ f ∈ fs₂, (f.earlyOpt).body.supportsSource lt = true) :
    ∀ f ∈ fs₁, (f.earlyOpt).body.supportsSource lt = true :=
  heq ▸ h

/-- Every function in `fs` has identity legalization (`lt.legalSig f.as = f.as` and
`lt.legalSig f.rs = f.rs`). -/
@[expose] def LegalSigAll (lt : LegalTarget) (fs : List Fn) : Prop :=
  ∀ f ∈ fs, lt.legalSig f.as = f.as ∧ lt.legalSig f.rs = f.rs

/-- Kernel-reducible boolean checker for `LegalSigAll`. -/
@[expose] def checkLegalSigAll (lt : LegalTarget) (fs : List Fn) : Bool :=
  fs.all (fun f => (lt.legalSig f.as == f.as) && (lt.legalSig f.rs == f.rs))

theorem legalSigAll_of_check {lt : LegalTarget} {fs : List Fn}
    (h : checkLegalSigAll lt fs = true) : LegalSigAll lt fs := by
  intro f hf
  have h' := List.all_eq_true.mp h f hf
  simp only [Bool.and_eq_true, beq_iff_eq] at h'
  exact h'

theorem chunksMaxBound_nil {T : Target} {lt : LegalTarget} {exits : List Sym} {nX B : Nat} :
    chunksMaxBound ([] : List (CompiledChunk T lt exits nX)) ≤ B :=
  Nat.zero_le B

theorem chunksMaxBound_cons {T : Target} {lt : LegalTarget} {exits : List Sym} {nX B : Nat}
    {c : CompiledChunk T lt exits nX} {cs : List (CompiledChunk T lt exits nX)}
    (hc : c.maxBound ≤ B) (hcs : chunksMaxBound cs ≤ B) :
    chunksMaxBound (c :: cs) ≤ B :=
  Nat.max_le.mpr ⟨hc, hcs⟩

theorem chunksFns_append {T : Target} {lt : LegalTarget} {exits : List Sym} {nX : Nat} :
    ∀ (cs₁ cs₂ : List (CompiledChunk T lt exits nX)),
      chunksFns (cs₁ ++ cs₂) = chunksFns cs₁ ++ chunksFns cs₂
  | [], _ => rfl
  | c :: cs₁, cs₂ => by
    simp only [List.cons_append, chunksFns, chunksFns_append cs₁ cs₂, List.append_assoc]

theorem chunksMaxBound_append {T : Target} {lt : LegalTarget} {exits : List Sym} {nX : Nat} :
    ∀ (cs₁ cs₂ : List (CompiledChunk T lt exits nX)),
      chunksMaxBound (cs₁ ++ cs₂) = Nat.max (chunksMaxBound cs₁) (chunksMaxBound cs₂)
  | [], cs₂ => by simp [chunksMaxBound]
  | c :: cs₁, cs₂ => by
    simp only [List.cons_append, chunksMaxBound, chunksMaxBound_append cs₁ cs₂, Nat.max_assoc]

/-! ## 2. `LinkedCert`: chunked literal-backed module compilation certificate -/

/-- Chunked, literal-backed native compilation and linking certificate for an acyclic `Module`
over any target `T`, layout `L`, legalization `lt`, and structural `LabelClean` proof `hcl`. -/
structure LinkedCert (T : Target) (L : TargetLayout T) (lt : LegalTarget)
    (hcl : Rega.LabelClean T.toIsa) (mod : Module)
    (ext₀ : List (SigEntry × Nat) := []) (exits : List Sym := []) (nX : Nat := 0)
    (maxBound : Nat := 2048) where
  chunks : List (CompiledChunk T lt exits nX)
  linkCheck : checkLinkList L ext₀ chunks = true
  fns_eq : mod.fns = chunksFns chunks
  supportsAll : ∀ f ∈ mod.fns, (f.earlyOpt).body.supportsSource lt = true
  maxBound_le : chunksMaxBound chunks ≤ maxBound

namespace LinkedCert

variable {T : Target} {L : TargetLayout T} {lt : LegalTarget}
  {hcl : Rega.LabelClean T.toIsa} {mod : Module}
  {ext₀ : List (SigEntry × Nat)} {exits : List Sym} {nX maxBound : Nat}

/-- Linked whole-module `Compiled` bundle built via `linkCompiledList` from `cert.chunks`. -/
@[expose] noncomputable def compiled (cert : LinkedCert T L lt hcl mod ext₀ exits nX maxBound) :
    Compiled T lt ext₀ exits nX (chunksFns cert.chunks)
      (chunksHints cert.chunks) (chunksMaxBound cert.chunks) :=
  linkCompiledList L hcl ext₀ cert.chunks cert.linkCheck

/-- Linked machine-code host for the full module. -/
@[expose] noncomputable def host (cert : LinkedCert T L lt hcl mod ext₀ exits nX maxBound) :
    T.mach.Host :=
  cert.compiled.host

/-- Concatenated literal directive stream of all linked chunks. -/
@[expose] noncomputable def code (cert : LinkedCert T L lt hcl mod ext₀ exits nX maxBound) :
    List T.Directive :=
  cert.compiled.code

/-- Concatenated literal `(fnName, stackBound)` table of all linked chunks. -/
@[expose] noncomputable def bounds (cert : LinkedCert T L lt hcl mod ext₀ exits nX maxBound) :
    List (Sym × Nat) :=
  cert.compiled.bounds

/-- Stack bound computed for function `nm` in `cert`. -/
@[expose] noncomputable def bound (cert : LinkedCert T L lt hcl mod ext₀ exits nX maxBound)
    (nm : Sym) : Nat :=
  cert.compiled.bound nm

/-- Number of compiled chunks linked in `cert`. -/
@[expose] def numChunks (cert : LinkedCert T L lt hcl mod ext₀ exits nX maxBound) : Nat :=
  cert.chunks.length

/-- Compositionally link two pre-verified `LinkedCert`s (for instance, compiled in parallel in
separate `.lean` modules) into a single whole-module `LinkedCert` using only O(N) metadata-only
`checkLinkList` validation. -/
@[expose] noncomputable def append {mod₁ mod₂ mod : Module} {ext₂ : List (SigEntry × Nat)}
    {maxB₁ maxB₂ : Nat}
    (c₁ : LinkedCert T L lt hcl mod₁ ext₀ exits nX maxB₁)
    (c₂ : LinkedCert T L lt hcl mod₂ ext₂ exits nX maxB₂)
    (hmod : mod.fns = mod₁.fns ++ mod₂.fns)
    (hchk : checkLinkList L ext₀ (c₁.chunks ++ c₂.chunks) = true) :
    LinkedCert T L lt hcl mod ext₀ exits nX (Nat.max maxB₁ maxB₂) where
  chunks := c₁.chunks ++ c₂.chunks
  linkCheck := hchk
  fns_eq := by
    rw [hmod, c₁.fns_eq, c₂.fns_eq, chunksFns_append]
  supportsAll := by
    intro f hf
    rw [hmod, List.mem_append] at hf
    rcases hf with h1 | h2
    · exact c₁.supportsAll f h1
    · exact c₂.supportsAll f h2
  maxBound_le := by
    rw [chunksMaxBound_append]
    exact Nat.max_le.mpr
      ⟨Nat.le_trans c₁.maxBound_le (Nat.le_max_left _ _),
       Nat.le_trans c₂.maxBound_le (Nat.le_max_right _ _)⟩

end LinkedCert

end LeanQbe.T
