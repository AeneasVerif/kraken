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

theorem supportsAll_of_all {lt : LegalTarget} {fs : List Fn}
    (h : checkSupportsChunk lt fs = true) :
    ∀ f ∈ fs, (f.earlyOpt).body.supportsSource lt = true :=
  fun f hf => List.all_eq_true.mp h f hf

theorem supportsAll_append {lt : LegalTarget} {fs₁ fs₂ : List Fn}
    (h₁ : checkSupportsChunk lt fs₁ = true)
    (h₂ : ∀ f ∈ fs₂, (f.earlyOpt).body.supportsSource lt = true) :
    ∀ f ∈ fs₁ ++ fs₂, (f.earlyOpt).body.supportsSource lt = true := by
  intro f hf
  rcases List.mem_append.mp hf with h1 | h2
  · exact List.all_eq_true.mp h₁ f h1
  · exact h₂ f h2

theorem supportsAll_append_pred {lt : LegalTarget} {fs₁ fs₂ : List Fn}
    (h₁ : ∀ f ∈ fs₁, (f.earlyOpt).body.supportsSource lt = true)
    (h₂ : ∀ f ∈ fs₂, (f.earlyOpt).body.supportsSource lt = true) :
    ∀ f ∈ fs₁ ++ fs₂, (f.earlyOpt).body.supportsSource lt = true := by
  intro f hf
  rcases List.mem_append.mp hf with h1 | h2
  · exact h₁ f h1
  · exact h₂ f h2

theorem supportsAll_of_eq {lt : LegalTarget} {fs₁ fs₂ : List Fn} (heq : fs₁ = fs₂)
    (h : ∀ f ∈ fs₂, (f.earlyOpt).body.supportsSource lt = true) :
    ∀ f ∈ fs₁, (f.earlyOpt).body.supportsSource lt = true :=
  heq ▸ h

/-- Derive `supportsSource lt` for every function in `chunksFns cs` directly from each chunk's
`compileModule_eq` proof, with zero redundant `earlyOpt` kernel evaluation. -/
theorem supportsAll_of_chunks {T : Target} {lt : LegalTarget} {exits : List Sym} {nX : Nat} :
    ∀ (cs : List (CompiledChunk T lt exits nX)),
      ∀ f ∈ chunksFns cs, (f.earlyOpt).body.supportsSource lt = true
  | [], _, hf => nomatch hf
  | c :: cs, f, hf => by
    dsimp only [chunksFns] at hf
    rcases List.mem_append.mp hf with h1 | h2
    · exact c.compiled.supportsSource f h1
    · exact supportsAll_of_chunks cs f h2

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
  rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at h'
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
    show c.fs ++ chunksFns (cs₁ ++ cs₂) = (c.fs ++ chunksFns cs₁) ++ chunksFns cs₂
    rw [chunksFns_append cs₁ cs₂, List.append_assoc]

theorem chunksMaxBound_append {T : Target} {lt : LegalTarget} {exits : List Sym} {nX : Nat} :
    ∀ (cs₁ cs₂ : List (CompiledChunk T lt exits nX)),
      chunksMaxBound (cs₁ ++ cs₂) = Nat.max (chunksMaxBound cs₁) (chunksMaxBound cs₂)
  | [], cs₂ => rfl
  | c :: cs₁, cs₂ => by
    show Nat.max c.maxBound (chunksMaxBound (cs₁ ++ cs₂)) =
      Nat.max (Nat.max c.maxBound (chunksMaxBound cs₁)) (chunksMaxBound cs₂)
    rw [chunksMaxBound_append cs₁ cs₂]
    exact (Nat.max_assoc c.maxBound (chunksMaxBound cs₁) (chunksMaxBound cs₂)).symm

theorem chunksMaxBound_append_le {T : Target} {lt : LegalTarget} {exits : List Sym} {nX : Nat}
    {maxB₁ maxB₂ : Nat} {cs₁ cs₂ : List (CompiledChunk T lt exits nX)}
    (h₁ : chunksMaxBound cs₁ ≤ maxB₁) (h₂ : chunksMaxBound cs₂ ≤ maxB₂) :
    chunksMaxBound (cs₁ ++ cs₂) ≤ Nat.max maxB₁ maxB₂ := by
  rw [chunksMaxBound_append]
  exact Nat.max_le.mpr
    ⟨Nat.le_trans h₁ (Nat.le_max_left _ _),
     Nat.le_trans h₂ (Nat.le_max_right _ _)⟩

theorem linkedCert_fns_eq_append {T : Target} {lt : LegalTarget} {exits : List Sym} {nX : Nat}
    {mod₁ mod₂ mod : Module} {cs₁ cs₂ : List (CompiledChunk T lt exits nX)}
    (hmod : mod.fns = mod₁.fns ++ mod₂.fns)
    (h₁ : mod₁.fns = chunksFns cs₁)
    (h₂ : mod₂.fns = chunksFns cs₂) :
    mod.fns = chunksFns (cs₁ ++ cs₂) := by
  rw [hmod, h₁, h₂, chunksFns_append]

theorem bound_mem_of_getElem {bs : List (Sym × Nat)} {i : Nat} (hi : i < bs.length) :
    bs[i] ∈ bs :=
  List.getElem_mem hi

theorem lookupFnBound_of_mem_nodup {bs : List (Sym × Nat)} {nm : Sym} {b : Nat}
    (hnd : (bs.map Prod.fst).Nodup) (hmem : (nm, b) ∈ bs) :
    lookupFnBound bs nm = some b := by
  induction bs with
  | nil => nomatch hmem
  | cons hd tl ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    dsimp only [lookupFnBound, List.find?]
    cases List.mem_cons.mp hmem with
    | inl heq =>
      subst heq
      rw [beq_self_eq_true]
      rfl
    | inr hmem' =>
      have hne : (hd.1 == nm) = false := beq_false_of_ne fun e =>
        hnd.1 (by cases e; exact List.mem_map.mpr ⟨(hd.1, b), hmem', rfl⟩)
      rw [hne]
      exact ih hnd.2 hmem'

theorem lookupFnBound_getElem_nodup {bs : List (Sym × Nat)} (hnd : (bs.map Prod.fst).Nodup)
    {i : Nat} (hi : i < bs.length) :
    lookupFnBound bs bs[i].1 = some bs[i].2 :=
  lookupFnBound_of_mem_nodup hnd (List.getElem_mem hi)

theorem mem_of_take_drop {α : Type _} {l : List α} {s k i : Nat} (hi : i < k)
    (hbound : s + i < l.length) :
    l[s + i] ∈ (l.drop s).take k := by
  have hlt : s + i - s < ((l.drop s).take k).length := by
    rw [List.length_take, List.length_drop]
    omega
  have h_idx : ((l.drop s).take k)[s + i - s]'hlt = l[s + i] := by
    rw [List.getElem_take, List.getElem_drop]
    congr 1
    omega
  rw [← h_idx]
  exact List.getElem_mem hlt

theorem mem_of_chunksFns {T : Target} {lt : LegalTarget} {exits : List Sym} {nX : Nat}
    {cs : List (CompiledChunk T lt exits nX)} {c : CompiledChunk T lt exits nX}
    (hc : c ∈ cs) {f : Fn} (hf : f ∈ c.fs) :
    f ∈ chunksFns cs := by
  induction cs with
  | nil => nomatch hc
  | cons c' rest ih =>
    rcases List.mem_cons.mp hc with rfl | hrest
    · dsimp only [chunksFns]
      exact List.mem_append_left _ hf
    · dsimp only [chunksFns]
      exact List.mem_append_right _ (ih hrest)

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

/-- Function names in `cert.bounds` match source module function names in order. -/
theorem bounds_names (cert : LinkedCert T L lt hcl mod ext₀ exits nX maxBound) :
    cert.bounds.map Prod.fst = mod.fns.map Fn.name := by
  have hb := compileModule_bounds_names cert.compiled.compileModule_eq
  have hfns : (chunksFns cert.chunks).map Fn.name = mod.fns.map Fn.name :=
    congrArg (List.map Fn.name) cert.fns_eq.symm
  rw [show cert.bounds = cert.compiled.bounds from rfl, hb, hfns]

/-- `cert.bounds` has no duplicate names if the source module has no duplicate function names. -/
theorem bounds_nodup (cert : LinkedCert T L lt hcl mod ext₀ exits nX maxBound)
    (hnd : (mod.fns.map Fn.name).Nodup) :
    (cert.bounds.map Prod.fst).Nodup := by
  rw [cert.bounds_names]
  exact hnd

/-- Number of bounds in `cert.bounds` matches the number of functions in `mod.fns`. -/
theorem bounds_length (cert : LinkedCert T L lt hcl mod ext₀ exits nX maxBound) :
    cert.bounds.length = mod.fns.length := by
  have h := congrArg List.length cert.bounds_names
  rw [List.length_map, List.length_map] at h
  exact h

/-- The $i$-th entry of `cert.bounds` has function name matching `mod.fns[i].name`. -/
theorem bounds_getElem_fst (cert : LinkedCert T L lt hcl mod ext₀ exits nX maxBound)
    {i : Nat} (hi : i < mod.fns.length) :
    (cert.bounds[i]'(by rw [cert.bounds_length]; exact hi)).1 = mod.fns[i].name := by
  have hi_b : i < cert.bounds.length := by rw [cert.bounds_length]; exact hi
  have h := congrArg (fun (l : List Sym) => l[i]?) cert.bounds_names
  rw [List.getElem?_eq_getElem (by rw [List.length_map]; exact hi_b),
      List.getElem?_eq_getElem (by rw [List.length_map]; exact hi),
      List.getElem_map, List.getElem_map] at h
  exact Option.some.inj h

/-- Stack bound lookup by index into `cert.bounds`. -/
theorem bound_at_idx (cert : LinkedCert T L lt hcl mod ext₀ exits nX maxBound)
    (hnd : (cert.bounds.map Prod.fst).Nodup) {i : Nat} (hi : i < cert.bounds.length) :
    cert.bound cert.bounds[i].1 = cert.bounds[i].2 := by
  have h := lookupFnBound_getElem_nodup (bs := cert.bounds) hnd hi
  dsimp only [bound, Compiled.bound]
  rw [show cert.compiled.bounds = cert.bounds from rfl, h]
  rfl

/-- Direct $O(1)$ stack bound evaluation for `mod.fns[i].name` via index into `cert.bounds`. -/
theorem bound_at_fn_idx (cert : LinkedCert T L lt hcl mod ext₀ exits nX maxBound)
    (hnd : (mod.fns.map Fn.name).Nodup) {i : Nat} (hi : i < mod.fns.length) :
    cert.bound mod.fns[i].name = (cert.bounds[i]'(by rw [cert.bounds_length]; exact hi)).2 := by
  have hi_b : i < cert.bounds.length := by rw [cert.bounds_length]; exact hi
  have h_idx := cert.bound_at_idx (cert.bounds_nodup hnd) hi_b
  have hfst := cert.bounds_getElem_fst hi
  rw [hfst] at h_idx
  exact h_idx

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
  fns_eq := linkedCert_fns_eq_append hmod c₁.fns_eq c₂.fns_eq
  supportsAll := supportsAll_of_eq hmod (supportsAll_append_pred c₁.supportsAll c₂.supportsAll)
  maxBound_le := chunksMaxBound_append_le c₁.maxBound_le c₂.maxBound_le

end LinkedCert

end LeanQbe.T
