module

public import LeanQbe.T.MainCertProof

/-!
# Additive Slice-List Certificate Assembler (`MainCertSlices`)

O(1)-boilerplate alternative to the O(N) `sufChunksK` / `fns_eqK` / `maxBK` certificate ladder in
generated `<Prefix>Cert.lean` files, placed in a fresh additive leaf module so zero upstream M5/M6/M7
certificates rebuild:
* `ChunkSlice`: contiguous slice `[start, start + count)` of `CompiledChunk`s covering
  `(fs.drop start).take count` with `chunksMaxBound chunks ≤ maxBound`.
* `ChunkSlice.ofCert` / `ChunkSlice.ofDrop`: construct `ChunkSlice` from per-slice `LinkedCert`s.
* `LinkedCert.ofChunkSlices`: assemble a whole-module `LinkedCert` in O(1) boilerplate using pure
  `Nat` contiguity (`ChunkSlice.contiguousFrom`) and `checkLinkList`.
* `LinkedCert.toCompiled`: O(1) type normalization from `LinkedCert.compiled` to `mod.fns` /
  `maxBound` without re-running `linkCompiledList`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T

/-- Contiguous compiled chunk slice covering `(fs.drop start).take count` with pre-checked stack
bound `chunksMaxBound chunks ≤ maxBound`. -/
structure ChunkSlice (T : Target) (lt : LegalTarget) (exits : List Sym)
    (nX maxBound : Nat) (fs : List Fn) where
  start : Nat
  count : Nat
  chunks : List (CompiledChunk T lt exits nX)
  fns_eq : (fs.drop start).take count = chunksFns chunks
  maxBound_le : chunksMaxBound chunks ≤ maxBound

namespace ChunkSlice

variable {T : Target} {lt : LegalTarget} {exits : List Sym}
  {nX maxBound : Nat} {fs : List Fn}

/-- Right-associated concatenation of slice chunks (`sl.chunks ++ ...`), matching traditional
`sufChunks` reduction shape under `t_kernel_rfl`. -/
@[expose] def allChunks :
    List (ChunkSlice T lt exits nX maxBound fs) → List (CompiledChunk T lt exits nX)
  | [] => []
  | sl :: rest => sl.chunks ++ allChunks rest

/-- Pure `Nat`-only contiguity validator starting at offset `pos` and ending at `total`.
Runs in O(#slices) integer steps without unfolding `fs : List Fn`. -/
@[expose] def contiguousFrom (pos : Nat) :
    List (ChunkSlice T lt exits nX maxBound fs) → Nat → Bool
  | [], total => pos == total
  | sl :: rest, total =>
      (sl.start == pos) && contiguousFrom (pos + sl.count) rest total

theorem maxBound_allChunks :
    ∀ (slices : List (ChunkSlice T lt exits nX maxBound fs)),
      chunksMaxBound (allChunks slices) ≤ maxBound
  | [] => chunksMaxBound_nil
  | sl :: rest => by
      dsimp only [allChunks]
      rw [chunksMaxBound_append]
      exact Nat.max_le.mpr ⟨sl.maxBound_le, maxBound_allChunks rest⟩

theorem drop_eq_chunksFns :
    ∀ (slices : List (ChunkSlice T lt exits nX maxBound fs)) (pos : Nat),
      contiguousFrom pos slices fs.length = true →
      fs.drop pos = chunksFns (allChunks slices)
  | [], pos, h => by
      unfold contiguousFrom at h
      rw [beq_iff_eq.mp h, List.drop_length]
      rfl
  | sl :: rest, pos, h => by
      unfold contiguousFrom at h
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨hst, hrest⟩ := h
      dsimp only [allChunks]
      rw [chunksFns_append, ← sl.fns_eq,
        ← drop_eq_chunksFns rest (pos + sl.count) hrest,
        hst, drop_take_append_drop]

theorem fns_eq_allChunks
    (slices : List (ChunkSlice T lt exits nX maxBound fs))
    (hcontig : contiguousFrom 0 slices fs.length = true) :
    fs = chunksFns (allChunks slices) := by
  simpa only [List.drop_zero] using drop_eq_chunksFns slices 0 hcontig

/-- Build a `ChunkSlice` from a per-slice `LinkedCert` over `(fs.drop start).take count`. -/
@[expose] noncomputable def ofCert {L : TargetLayout T} {hcl : Rega.LabelClean T.toIsa}
    {sliceMod : Module} {extK : List (SigEntry × Nat)}
    (start count : Nat)
    (cert : LinkedCert T L lt hcl sliceMod extK exits nX maxBound)
    (hslice : (fs.drop start).take count = sliceMod.fns := by rfl) :
    ChunkSlice T lt exits nX maxBound fs where
  start := start
  count := count
  chunks := cert.chunks
  fns_eq := hslice.trans cert.fns_eq
  maxBound_le := cert.maxBound_le

/-- Build a trailing (or full-module) `ChunkSlice` from a per-slice `LinkedCert` over
`fs.drop start` using `hlen : fs.length = total` without unfolding `fs` in the kernel. -/
@[expose] noncomputable def ofDrop {L : TargetLayout T} {hcl : Rega.LabelClean T.toIsa}
    {sliceMod : Module} {extK : List (SigEntry × Nat)}
    (start count : Nat) {total : Nat}
    (cert : LinkedCert T L lt hcl sliceMod extK exits nX maxBound)
    (hlen : fs.length = total)
    (hend : start + count = total := by decide)
    (hslice : fs.drop start = sliceMod.fns := by rfl) :
    ChunkSlice T lt exits nX maxBound fs where
  start := start
  count := count
  chunks := cert.chunks
  fns_eq := by
    have hdrop : (fs.drop start).length ≤ count := by
      rw [List.length_drop, hlen]; omega
    rw [List.take_of_length_le hdrop, hslice, cert.fns_eq]
  maxBound_le := cert.maxBound_le

end ChunkSlice

namespace LinkedCert

variable {T : Target} {L : TargetLayout T} {lt : LegalTarget}
  {hcl : Rega.LabelClean T.toIsa} {mod : Module}
  {ext₀ : List (SigEntry × Nat)} {exits : List Sym} {nX maxBound : Nat}

/-- Assemble a whole-module `LinkedCert` from a list of `ChunkSlice`s in O(1) boilerplate,
eliminating all `sufChunksK` / `fns_eqK` / `maxBK` ladders. Passing explicit `total`
(`hlen : mod.fns.length = total`) allows `hcontig` to check by `decide` without unfolding
`mod.fns` in the kernel. -/
@[expose] noncomputable def ofChunkSlices
    (slices : List (ChunkSlice T lt exits nX maxBound mod.fns))
    {total : Nat} (hlen : mod.fns.length = total)
    (hcontig : ChunkSlice.contiguousFrom 0 slices total = true)
    (hlink : checkLinkList L ext₀ (ChunkSlice.allChunks slices) = true) :
    LinkedCert T L lt hcl mod ext₀ exits nX maxBound where
  chunks := ChunkSlice.allChunks slices
  linkCheck := hlink
  fns_eq := ChunkSlice.fns_eq_allChunks slices (hlen ▸ hcontig)
  supportsAll := supportsAll_of_eq
    (ChunkSlice.fns_eq_allChunks slices (hlen ▸ hcontig))
    (supportsAll_of_chunks (ChunkSlice.allChunks slices))
  maxBound_le := ChunkSlice.maxBound_allChunks slices

/-- Normalize `cert.compiled` to `mod.fns` and `maxBound`, preserving `code`, `bounds`, `host`,
`prog_host`, and `labelsUnique` definitionally without re-running `linkCompiledList`. -/
@[expose] noncomputable def toCompiled
    (cert : LinkedCert T L lt hcl mod ext₀ exits nX maxBound) :
    Compiled T lt ext₀ exits nX mod.fns (chunksHints cert.chunks) maxBound where
  code := cert.compiled.code
  bounds := cert.compiled.bounds
  compileModule_eq := by rw [cert.fns_eq]; exact cert.compiled.compileModule_eq
  compile_eq := by rw [cert.fns_eq]; exact cert.compiled.compile_eq
  bound_mem hnm := cert.compiled.bound_mem (cert.fns_eq ▸ hnm)
  bound_le nm := Nat.le_trans (cert.compiled.bound_le nm) cert.maxBound_le
  host := cert.compiled.host
  prog_host := cert.compiled.prog_host
  labelsUnique := cert.compiled.labelsUnique

end LinkedCert

end LeanQbe.T
