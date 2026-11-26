module

public import LeanQbe.T.MainCertProof

/-!
# Additive Slice-List Certificate Assembler (`MainCertSlices`)

O(1)-boilerplate alternative to the O(N) `sufChunksK` / `fns_eqK` / `maxBK` certificate ladder in
generated `<Prefix>Cert.lean` files, placed in a fresh additive leaf module so zero upstream
M5/M6/M7 certificates rebuild:
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

private theorem contiguousFrom_le :
    ∀ (slices : List (ChunkSlice T lt exits nX maxBound fs)) (pos total : Nat),
      contiguousFrom pos slices total = true → pos ≤ total
  | [], pos, total, h => by
      unfold contiguousFrom at h
      exact Nat.le_of_eq (beq_iff_eq.mp h)
  | sl :: rest, pos, total, h => by
      unfold contiguousFrom at h
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      exact Nat.le_trans (Nat.le_add_right pos sl.count)
        (contiguousFrom_le rest (pos + sl.count) total h.2)

theorem take_drop_eq_chunksFns :
    ∀ (slices : List (ChunkSlice T lt exits nX maxBound fs)) (pos total : Nat),
      contiguousFrom pos slices total = true →
      (fs.drop pos).take (total - pos) = chunksFns (allChunks slices)
  | [], pos, total, h => by
      unfold contiguousFrom at h
      have hpe : pos = total := beq_iff_eq.mp h
      subst hpe
      simp [allChunks, chunksFns]
  | sl :: rest, pos, total, h => by
      unfold contiguousFrom at h
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨hst, hrest⟩ := h
      have hle : pos + sl.count ≤ total := contiguousFrom_le rest (pos + sl.count) total hrest
      have hih := take_drop_eq_chunksFns rest (pos + sl.count) total hrest
      dsimp only [allChunks]
      rw [chunksFns_append, ← sl.fns_eq, ← hih, hst]
      have hsplit : total - pos = sl.count + (total - (pos + sl.count)) := by omega
      rw [hsplit, List.take_add, List.drop_drop]

/-- Combine a contiguous sub-list of `ChunkSlice`s covering `[start, start + count)` into a single
super-`ChunkSlice` for 2-level balanced certificate trees (`N6`). -/
@[expose] noncomputable def ofSlices
    (start count : Nat)
    (slices : List (ChunkSlice T lt exits nX maxBound fs))
    (hcontig : contiguousFrom start slices (start + count) = true) :
    ChunkSlice T lt exits nX maxBound fs where
  start := start
  count := count
  chunks := allChunks slices
  fns_eq := by
    have h := take_drop_eq_chunksFns slices start (start + count) hcontig
    rwa [Nat.add_sub_cancel_left] at h
  maxBound_le := maxBound_allChunks slices

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

/-! ## 2-Level Balanced `checkLinkList` Tree Helpers (`N6`) -/

/-- Accumulated newest-first `sigBounds` table after linking `cs` onto `acc`, matching
`checkChunksExt`'s exact accumulator threading. -/
@[expose] def chunksNextExt {T : Target} {lt : LegalTarget} {exits : List Sym} {nX : Nat}
    (acc : List (SigEntry × Nat)) :
    List (CompiledChunk T lt exits nX) → List (SigEntry × Nat)
  | [] => acc
  | c :: cs => chunksNextExt (c.compiled.sigBounds.reverse ++ acc) cs

theorem checkChunksExt_append {T : Target} {lt : LegalTarget} {exits : List Sym} {nX : Nat} :
    ∀ (acc : List (SigEntry × Nat)) (cs₁ cs₂ : List (CompiledChunk T lt exits nX)),
      checkChunksExt acc (cs₁ ++ cs₂) =
        (checkChunksExt acc cs₁ && checkChunksExt (chunksNextExt acc cs₁) cs₂)
  | _, [], _ => rfl
  | acc, c :: cs₁, cs₂ => by
      dsimp only [List.cons_append, checkChunksExt, chunksNextExt]
      rw [checkChunksExt_append (c.compiled.sigBounds.reverse ++ acc) cs₁ cs₂, Bool.and_assoc]

/-- Metadata-only half of `checkLinkList` (`fnNameOk`, `stringsNodup`, `L.progSmall`), decoupled
from `checkChunksExt` so super-groups can verify `checkChunksExt` in parallel kernel tasks. -/
@[expose] def checkLinkMeta {T : Target} (L : TargetLayout T) {lt : LegalTarget}
    {exits : List Sym} {nX : Nat}
    (chunks : List (CompiledChunk T lt exits nX)) : Bool :=
  let fnNames := (chunksFns chunks).map Fn.name
  let prog := chunksCode chunks ++ exits.map T.frame.label
  fnNames.all fnNameOk &&
  exits.all fnNameOk &&
  stringsNodup (fnNames ++ exits) &&
  L.progSmall prog

theorem checkLinkList_of_checkChunksExt {T : Target} {L : TargetLayout T} {lt : LegalTarget}
    {exits : List Sym} {nX : Nat} {ext₀ : List (SigEntry × Nat)}
    {chunks : List (CompiledChunk T lt exits nX)}
    (hext : checkChunksExt ext₀ chunks = true)
    (hmeta : checkLinkMeta L chunks = true) :
    checkLinkList L ext₀ chunks = true := by
  dsimp only [checkLinkList]
  dsimp only [checkLinkMeta] at hmeta
  simp only [Bool.and_eq_true] at hmeta ⊢
  exact ⟨⟨⟨⟨hext, hmeta.1.1.1⟩, hmeta.1.1.2⟩, hmeta.1.2⟩, hmeta.2⟩

/-- Super-slice group pairing a `ChunkSlice` with its independently kernel-checked
`checkChunksExt extIn slice.chunks = true` witness for 2-level balanced linking. -/
structure CheckedSliceGroup (T : Target) (lt : LegalTarget) (exits : List Sym)
    (nX maxBound : Nat) (fs : List Fn) where
  slice : ChunkSlice T lt exits nX maxBound fs
  extIn : List (SigEntry × Nat)
  extOk : checkChunksExt extIn slice.chunks = true

namespace CheckedSliceGroup

variable {T : Target} {lt : LegalTarget} {exits : List Sym}
  {nX maxBound : Nat} {fs : List Fn}

/-- Definitional threading predicate ensuring each group's `extIn` matches the previous group's
`chunksNextExt` output (`⟨rfl, ..., trivial⟩` when `extIn` is defined sequentially). -/
@[expose] def chainedFrom (acc : List (SigEntry × Nat)) :
    List (CheckedSliceGroup T lt exits nX maxBound fs) → Prop
  | [] => True
  | g :: rest =>
      g.extIn = acc ∧
      chainedFrom (chunksNextExt acc g.slice.chunks) rest

theorem checkChunksExt_allChunks :
    ∀ (groups : List (CheckedSliceGroup T lt exits nX maxBound fs))
      (acc : List (SigEntry × Nat)),
      chainedFrom acc groups →
      checkChunksExt acc (ChunkSlice.allChunks (groups.map (·.slice))) = true
  | [], _, _ => rfl
  | g :: rest, acc, ⟨heq, hrest⟩ => by
      change checkChunksExt acc (g.slice.chunks ++ ChunkSlice.allChunks (rest.map (·.slice))) = true
      rw [checkChunksExt_append]
      simp only [Bool.and_eq_true]
      exact ⟨heq ▸ g.extOk, checkChunksExt_allChunks rest (chunksNextExt acc g.slice.chunks) hrest⟩

end CheckedSliceGroup

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

/-- Assemble a whole-module `LinkedCert` from a 2-level list of `CheckedSliceGroup`s whose
per-group `checkChunksExt` proofs run in parallel kernel tasks (`N6`). -/
@[expose] noncomputable def ofCheckedGroups
    (groups : List (CheckedSliceGroup T lt exits nX maxBound mod.fns))
    {total : Nat} (hlen : mod.fns.length = total)
    (hcontig : ChunkSlice.contiguousFrom 0 (groups.map (·.slice)) total = true)
    (hchain : CheckedSliceGroup.chainedFrom ext₀ groups)
    (hmeta : checkLinkMeta L (ChunkSlice.allChunks (groups.map (·.slice))) = true) :
    LinkedCert T L lt hcl mod ext₀ exits nX maxBound :=
  ofChunkSlices (groups.map (·.slice)) hlen hcontig
    (checkLinkList_of_checkChunksExt
      (CheckedSliceGroup.checkChunksExt_allChunks groups ext₀ hchain) hmeta)

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
