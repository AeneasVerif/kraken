/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.MainLinkReuse
public import LeanQbe.T.MainLinkReuseCalls
public import LeanQbe.T.MainCertCore

/-!
# Fast Callee-Cover Bridge & Chunk-List Relinking (`MainLinkReuseCover`)

Strictly additive bridge over `LeanQbe.T.MainLinkReuse`, `LeanQbe.T.MainLinkReuseCalls`, and
`LeanQbe.T.MainCertCore` eliminating kernel `Fn.mid` re-evaluation from `CalleesCover` proofs:

1. **Option B (`calleesCover_of_checkRaw`, `calleesCover_rawLegal`)**: proves via
   `Fn.mid_callsOk` and `fn_ext_callees_sub` that a single raw AST traversal (`Fn.rawCalls` /
   `Fn.rawLegalCallees`) over well-formed (`Fn.Wf`) functions sound-over-approximates
   `(f.mid lt).ext.callees`, avoiding `Fn.mid` / `earlyOpt` / `Rega` evaluation in the kernel.
2. **Option A (`CalleesCoverBundle`, `relinkChunkListLit`, `relinkLinkedCertCover`)**: packages
   stored callee-cover literals with zero-AST-walk transport (`of_eq`, `toCoverSub`) and
   multi-chunk `CompiledChunk` / `LinkedCert` relinkers preserving `chunksFns`, `chunksCode`,
   `chunksBounds`, `chunksMaxBound`, and `checkLinkList` metadata checks.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T

section RawCallsToExt

private theorem addCalleeSig_mem {g : Sym} {as bs : List Ty}
    {cs : List SigEntry} {g' : SigEntry} :
    g' ∈ addCalleeSig g as bs cs ↔ g' ∈ cs ∨ g' = (g, as, bs) := by
  unfold addCalleeSig
  dsimp only
  split
  · rename_i h
    rw [List.any_eq_true] at h
    rcases h with ⟨x, hx, hbeq⟩
    have heq : SigEntry.beq (g, as, bs) x = true := by
      simpa [SigEntry.beq] using hbeq
    have hgx : (g, as, bs) = x := SigEntry.beq_iff_eq.mp heq
    constructor
    · intro hg'; exact Or.inl hg'
    · intro hg'
      rcases hg' with hg' | rfl
      · exact hg'
      · exact hgx ▸ hx
  · simp [List.mem_cons]
    exact or_comm

private theorem addCalleeSig_sub {allowed cs : List SigEntry} {g : Sym} {as bs : List Ty}
    (hcs : ∀ x ∈ cs, x ∈ allowed) (hg : (g, as, bs) ∈ allowed) :
    ∀ x ∈ addCalleeSig g as bs cs, x ∈ allowed := by
  intro x hx
  rcases addCalleeSig_mem.mp hx with h | rfl
  · exact hcs x h
  · exact hg

mutual
private theorem extAux_callees_sub {allowed : List SigEntry} {exits : List Sym} {rs : List Ty}
    (cs : List SigEntry) (xs : List Sym) :
    (e : Expr (fun _ => Unit) (fun _ => Unit) rs) →
    (∀ g ∈ cs, g ∈ allowed) → e.callsOk allowed exits →
    ∀ g ∈ (e.extAux cs xs).1, g ∈ allowed
  | .let_ _ k, hcs, hc =>
    extAux_callees_sub cs xs (k (Tup.units _)) hcs hc
  | .load _ _ k, hcs, hc =>
    extAux_callees_sub cs xs (k ()) hcs hc
  | .store _ _ k, hcs, hc =>
    extAux_callees_sub cs xs k hcs hc
  | .call (as := as) (bs := bs) nm _ k, hcs, ⟨hm, hk⟩ =>
    extAux_callees_sub (addCalleeSig nm as bs cs) xs (k (Tup.units _))
      (addCalleeSig_sub hcs hm) hk
  | .jnz c t e, hcs, ⟨ht, he⟩ => by
    cases c with
    | imm b =>
      dsimp only [Expr.extAux]
      split
      · exact extAux_callees_sub cs xs t hcs ht
      · exact extAux_callees_sub cs xs e hcs he
    | var v =>
      dsimp only [Expr.extAux]
      have he' := extAux_callees_sub cs xs e hcs he
      exact extAux_callees_sub (e.extAux cs xs).1 (e.extAux cs xs).2 t he' ht
  | .jump _ _, hcs, _ => hcs
  | .ret _, hcs, _ => hcs
  | .exit _ _, hcs, _ => hcs
  | .hlt, hcs, _ => hcs
  | .group b k, hcs, ⟨hb, hk⟩ => by
    dsimp only [Expr.extAux]
    have hk' := extAux_callees_sub cs xs (k (Tup.units _)) hcs hk
    exact blocksExtAux_callees_sub
      ((k (Tup.units _)).extAux cs xs).1 ((k (Tup.units _)).extAux cs xs).2
      (b (Tup.units _)) hk' hb

private theorem blocksExtAux_callees_sub {allowed : List SigEntry} {exits : List Sym}
    {rs : List Ty} (cs : List SigEntry) (xs : List Sym) :
    {sig : List (List Ty)} → (bs : Blocks (fun _ => Unit) (fun _ => Unit) rs sig) →
    (∀ g ∈ cs, g ∈ allowed) → bs.callsOk allowed exits →
    ∀ g ∈ (bs.extAux cs xs).1, g ∈ allowed
  | [], .nil, hcs, _ => hcs
  | _ :: _, .cons b bs, hcs, hbs => by
    dsimp only [Blocks.callsOk, Blocks.extAux] at hbs ⊢
    have hb' := extAux_callees_sub cs xs (b (Tup.units _)) hcs hbs.1
    exact blocksExtAux_callees_sub
      (Expr.extAux (b (Tup.units _)) cs xs).1
      (Expr.extAux (b (Tup.units _)) cs xs).2 bs hb' hbs.2
end

/-- If `f.callsOk allowed exits`, every callee signature in `f.ext.callees` belongs to
`allowed`. -/
theorem fn_ext_callees_sub {allowed : List SigEntry} {exits : List Sym} {f : Fn}
    (hc : f.callsOk allowed exits) :
    ∀ g ∈ f.ext.callees, g ∈ allowed := by
  intro g hg
  dsimp only [Fn.ext] at hg
  exact extAux_callees_sub [] [] _ (fun _ h => nomatch h) hc g (List.mem_reverse.mp hg)

/-- For any well-formed `f`, every callee in `(f.mid lt).ext.callees` lies in
`f.rawCalls.map (sigEntryLegal lt)`. -/
theorem fn_mid_ext_callees_sub (lt : LegalTarget) {f : Fn} (hf : f.Wf) :
    ∀ g ∈ (f.mid lt).ext.callees, g ∈ f.rawCalls.map (sigEntryLegal lt) :=
  fn_ext_callees_sub (Fn.mid_callsOk lt hf)

mutual
private theorem rawLegalCallsAux_acc (lt : LegalTarget) {rs : List Ty}
    (cs : List SigEntry) :
    (e : Expr (fun _ => Unit) (fun _ => Unit) rs) →
    ∀ {g}, g ∈ cs → g ∈ Expr.rawLegalCallsAux lt e cs
  | .let_ _ k, _, hg => rawLegalCallsAux_acc lt cs (k (Tup.units _)) hg
  | .load _ _ k, _, hg => rawLegalCallsAux_acc lt cs (k ()) hg
  | .store _ _ k, _, hg => rawLegalCallsAux_acc lt cs k hg
  | .call (as := as) (bs := bs) nm _ k, _, hg =>
    rawLegalCallsAux_acc lt _ (k (Tup.units bs)) (addCalleeSig_mem.mpr (Or.inl hg))
  | .jnz _ t e, _, hg => by
    dsimp only [Expr.rawLegalCallsAux]
    exact rawLegalCallsAux_acc lt _ t (rawLegalCallsAux_acc lt cs e hg)
  | .jump _ _, _, hg => hg
  | .ret _, _, hg => hg
  | .exit _ _, _, hg => hg
  | .hlt, _, hg => hg
  | .group b k, _, hg => by
    dsimp only [Expr.rawLegalCallsAux]
    exact blocksRawLegalCallsAux_acc lt _ (b (Tup.units _))
      (rawLegalCallsAux_acc lt cs (k (Tup.units _)) hg)

private theorem blocksRawLegalCallsAux_acc (lt : LegalTarget) {rs : List Ty}
    (cs : List SigEntry) :
    {sig : List (List Ty)} → (bs : Blocks (fun _ => Unit) (fun _ => Unit) rs sig) →
    ∀ {g}, g ∈ cs → g ∈ Blocks.rawLegalCallsAux lt bs cs
  | [], .nil, _, hg => hg
  | _ :: _, .cons b bs, _, hg => by
    dsimp only [Blocks.rawLegalCallsAux]
    exact blocksRawLegalCallsAux_acc lt _ bs (rawLegalCallsAux_acc lt cs (b (Tup.units _)) hg)
end

mutual
private theorem rawCallsAux_mem_or (lt : LegalTarget) {rs : List Ty}
    (cs cs' : List SigEntry) :
    (e : Expr (fun _ => Unit) (fun _ => Unit) rs) →
    ∀ {g}, g ∈ Expr.rawCallsAux cs e →
      g ∈ cs ∨ sigEntryLegal lt g ∈ Expr.rawLegalCallsAux lt e cs'
  | .let_ _ k, g, hg =>
    rawCallsAux_mem_or lt cs cs' (k (Tup.units _)) hg
  | .load _ _ k, g, hg =>
    rawCallsAux_mem_or lt cs cs' (k ()) hg
  | .store _ _ k, g, hg =>
    rawCallsAux_mem_or lt cs cs' k hg
  | .call (as := as) (bs := bs) nm _ k, g, hg => by
    dsimp only [Expr.rawCallsAux, Expr.rawLegalCallsAux] at hg ⊢
    rcases rawCallsAux_mem_or lt _ _ (k (Tup.units bs)) hg with h | h
    · split at h
      · exact Or.inl h
      · rcases List.mem_cons.mp h with rfl | h
        · exact Or.inr (rawLegalCallsAux_acc lt _ (k (Tup.units bs))
            (addCalleeSig_mem.mpr (Or.inr rfl)))
        · exact Or.inl h
    · exact Or.inr h
  | .jnz _ t e, g, hg => by
    dsimp only [Expr.rawCallsAux, Expr.rawLegalCallsAux] at hg ⊢
    rcases rawCallsAux_mem_or lt _ cs' e hg with h | h
    · rcases rawCallsAux_mem_or lt cs (Expr.rawLegalCallsAux lt e cs') t h with h1 | h2
      · exact Or.inl h1
      · exact Or.inr h2
    · exact Or.inr (rawLegalCallsAux_acc lt _ t h)
  | .jump _ _, _, hg => Or.inl hg
  | .ret _, _, hg => Or.inl hg
  | .exit _ _, _, hg => Or.inl hg
  | .hlt, _, hg => Or.inl hg
  | .group b k, g, hg => by
    dsimp only [Expr.rawCallsAux, Expr.rawLegalCallsAux] at hg ⊢
    rcases rawCallsAux_mem_or lt _ cs' (k (Tup.units _)) hg with h | h
    · rcases blocksRawCallsAux_mem_or lt cs (Expr.rawLegalCallsAux lt (k (Tup.units _)) cs')
          (b (Tup.units _)) h with h1 | h2
      · exact Or.inl h1
      · exact Or.inr h2
    · exact Or.inr (blocksRawLegalCallsAux_acc lt _ (b (Tup.units _)) h)

private theorem blocksRawCallsAux_mem_or (lt : LegalTarget) {rs : List Ty}
    (cs cs' : List SigEntry) :
    {sig : List (List Ty)} → (bs : Blocks (fun _ => Unit) (fun _ => Unit) rs sig) →
    ∀ {g}, g ∈ Blocks.rawCallsAux cs bs →
      g ∈ cs ∨ sigEntryLegal lt g ∈ Blocks.rawLegalCallsAux lt bs cs'
  | [], .nil, _, hg => Or.inl hg
  | _ :: _, .cons b bs, g, hg => by
    dsimp only [Blocks.rawCallsAux, Blocks.rawLegalCallsAux] at hg ⊢
    rcases blocksRawCallsAux_mem_or lt _ (Expr.rawLegalCallsAux lt (b (Tup.units _)) cs')
        bs hg with h | h
    · rcases rawCallsAux_mem_or lt cs cs' (b (Tup.units _)) h with h1 | h2
      · exact Or.inl h1
      · exact Or.inr (blocksRawLegalCallsAux_acc lt _ bs h2)
    · exact Or.inr h
end

/-- Every `sigEntryLegal lt g` from `f.rawCalls` belongs to `f.rawLegalCallees lt`. -/
theorem rawCalls_map_sub_rawLegalCallees (lt : LegalTarget) (f : Fn) :
    ∀ g ∈ f.rawCalls.map (sigEntryLegal lt), g ∈ f.rawLegalCallees lt := by
  intro g hg
  rcases List.mem_map.mp hg with ⟨g₀, hg₀, rfl⟩
  dsimp only [Fn.rawCalls] at hg₀
  rcases rawCallsAux_mem_or lt [] []
      (f.body (fun _ => Unit) (fun _ => Unit) (Tup.units f.as))
      (List.mem_reverse.mp hg₀) with h | h
  · exact nomatch h
  · exact h

end RawCallsToExt

section FastCoverChecks

/-- Boolean membership check `g ∈ S` via `SigEntry.beq`. -/
@[expose] def sigEntryMem (g : SigEntry) (S : List SigEntry) : Bool :=
  S.any (SigEntry.beq g)

theorem sigEntryMem_iff {g : SigEntry} {S : List SigEntry} :
    sigEntryMem g S = true ↔ g ∈ S := by
  simp [sigEntryMem, List.any_eq_true, SigEntry.beq_iff_eq]

/-- Kernel-friendly subset check `S₁ ⊆ S₂` via `SigEntry.beq`. -/
@[expose] def checkSigSub (S₁ S₂ : List SigEntry) : Bool :=
  S₁.all (fun g => sigEntryMem g S₂)

theorem checkSigSub_mem {S₁ S₂ : List SigEntry} (h : checkSigSub S₁ S₂ = true) :
    ∀ g ∈ S₁, g ∈ S₂ := by
  intro g hg
  exact sigEntryMem_iff.mp (List.all_eq_true.mp h g hg)

/-- Fast callee-cover reflection checker over raw call lists (`Fn.rawCalls`), avoiding
kernel `Fn.mid` evaluation. -/
@[expose] def checkRawCallsCover (lt : LegalTarget) (fs : List Fn) (S : List SigEntry) : Bool :=
  fs.all fun f => checkSigSub (f.rawCalls.map (sigEntryLegal lt)) S

/-- Fast callee-cover reflection checker over `MainLinkReuse.Fn.rawLegalCallees`, avoiding
kernel `Fn.mid` evaluation. -/
@[expose] def checkRawLegalCover (lt : LegalTarget) (fs : List Fn) (S : List SigEntry) : Bool :=
  fs.all fun f => checkSigSub (f.rawLegalCallees lt) S

/-- Every well-formed function list is covered by its mapped `Fn.rawCalls` list. -/
theorem calleesCover_rawCalls (lt : LegalTarget) {fs : List Fn} (hwf : ∀ f ∈ fs, f.Wf) :
    CalleesCover lt fs (fs.flatMap fun f => f.rawCalls.map (sigEntryLegal lt)) := by
  intro f hf g hg
  exact List.mem_flatMap.mpr ⟨f, hf, fn_mid_ext_callees_sub lt (hwf f hf) g hg⟩

/-- **Option B soundness theorem**: `rawLegalCalleesOf lt fs` always covers `(f.mid lt).ext.callees`
when every `f ∈ fs` is well-formed (`Fn.Wf`), requiring zero kernel `Fn.mid` evaluation. -/
theorem calleesCover_rawLegal (lt : LegalTarget) {fs : List Fn} (hwf : ∀ f ∈ fs, f.Wf) :
    CalleesCover lt fs (rawLegalCalleesOf lt fs) := by
  intro f hf g hg
  have hmem := rawCalls_map_sub_rawLegalCallees lt f g
    (fn_mid_ext_callees_sub lt (hwf f hf) g hg)
  exact List.mem_flatMap.mpr ⟨f, hf, hmem⟩

/-- Proves `CalleesCover lt fs S` from `∀ f ∈ fs, f.Wf` and `checkRawCallsCover lt fs S = true`
without running `Fn.mid` in the kernel. -/
theorem calleesCover_of_checkRaw {lt : LegalTarget} {fs : List Fn} {S : List SigEntry}
    (hwf : ∀ f ∈ fs, f.Wf) (hchk : checkRawCallsCover lt fs S = true) :
    CalleesCover lt fs S := by
  intro f hf g hg
  have hfchk : checkSigSub (f.rawCalls.map (sigEntryLegal lt)) S = true :=
    List.all_eq_true.mp hchk f hf
  exact checkSigSub_mem hfchk g (fn_mid_ext_callees_sub lt (hwf f hf) g hg)

/-- Proves `CalleesCover lt fs S` from `∀ f ∈ fs, f.Wf` and `checkRawLegalCover lt fs S = true`
without running `Fn.mid` in the kernel. -/
theorem calleesCover_of_checkRawLegal {lt : LegalTarget} {fs : List Fn} {S : List SigEntry}
    (hwf : ∀ f ∈ fs, f.Wf) (hchk : checkRawLegalCover lt fs S = true) :
    CalleesCover lt fs S := by
  intro f hf g hg
  have hfchk : checkSigSub (f.rawLegalCallees lt) S = true :=
    List.all_eq_true.mp hchk f hf
  have hraw := rawCalls_map_sub_rawLegalCallees lt f g
    (fn_mid_ext_callees_sub lt (hwf f hf) g hg)
  exact checkSigSub_mem hfchk g hraw

/-- Subset transport for `CalleesCover` checked via `checkSigSub`. -/
theorem calleesCover_of_checkSub {lt : LegalTarget} {fs : List Fn} {S₁ S₂ : List SigEntry}
    (hcov : CalleesCover lt fs S₁) (hsub : checkSigSub S₁ S₂ = true) :
    CalleesCover lt fs S₂ :=
  hcov.mono (checkSigSub_mem hsub)

/-- Propagate `(∀ f ∈ fs, f.Wf)` to any `(fs.drop d).take k` slice in O(1) without unfolding
function bodies. -/
theorem wf_of_take_drop {fs : List Fn} (d k : Nat) (hwf : ∀ f ∈ fs, f.Wf) :
    ∀ f ∈ (fs.drop d).take k, f.Wf := by
  intro f hf
  exact hwf f (List.mem_of_mem_drop (List.mem_of_mem_take hf))

end FastCoverChecks

section CalleesCoverBundleSec

/-- **Option A** pre-verified callee-cover literal bundle for a function list `fs`.
Once certified (via `calleesCover_of_checkRaw` or `calleesCover_of_checkRawLegal`), downstream
relinking transports `cover` by `of_eq` or flat-list `checkSigSub` with zero AST traversal. -/
structure CalleesCoverBundle (lt : LegalTarget) (fs : List Fn) where
  callees : List SigEntry
  cover : CalleesCover lt fs callees

namespace CalleesCoverBundle

/-- Build a `CalleesCoverBundle` from `Fn.Wf` and `checkRawCallsCover`. -/
@[expose] def ofCheckRaw {lt : LegalTarget} {fs : List Fn} (S : List SigEntry)
    (hwf : ∀ f ∈ fs, f.Wf) (hchk : checkRawCallsCover lt fs S = true) :
    CalleesCoverBundle lt fs :=
  ⟨S, calleesCover_of_checkRaw hwf hchk⟩

@[simp] theorem ofCheckRaw_callees {lt : LegalTarget} {fs : List Fn} (S : List SigEntry)
    (hwf : ∀ f ∈ fs, f.Wf) (hchk : checkRawCallsCover lt fs S = true) :
    (ofCheckRaw S hwf hchk).callees = S := rfl

/-- Build a `CalleesCoverBundle` from `Fn.Wf` and `checkRawLegalCover`. -/
@[expose] def ofCheckRawLegal {lt : LegalTarget} {fs : List Fn} (S : List SigEntry)
    (hwf : ∀ f ∈ fs, f.Wf) (hchk : checkRawLegalCover lt fs S = true) :
    CalleesCoverBundle lt fs :=
  ⟨S, calleesCover_of_checkRawLegal hwf hchk⟩

@[simp] theorem ofCheckRawLegal_callees {lt : LegalTarget} {fs : List Fn} (S : List SigEntry)
    (hwf : ∀ f ∈ fs, f.Wf) (hchk : checkRawLegalCover lt fs S = true) :
    (ofCheckRawLegal S hwf hchk).callees = S := rfl

/-- Zero-AST-cost `CalleesCoverBundle` transport across slice equality `fs' = fs`. -/
@[expose] def of_eq {lt : LegalTarget} {fs fs' : List Fn} (heq : fs' = fs)
    (b : CalleesCoverBundle lt fs) : CalleesCoverBundle lt fs' :=
  ⟨b.callees, b.cover.of_eq heq⟩

@[simp] theorem of_eq_callees {lt : LegalTarget} {fs fs' : List Fn} (heq : fs' = fs)
    (b : CalleesCoverBundle lt fs) :
    (b.of_eq heq).callees = b.callees := rfl

/-- Upgrade a stored `CalleesCoverBundle` to any superset `S` via flat-list `checkSigSub`. -/
theorem toCoverSub {lt : LegalTarget} {fs : List Fn} (b : CalleesCoverBundle lt fs)
    {S : List SigEntry} (hsub : checkSigSub b.callees S = true) :
    CalleesCover lt fs S :=
  calleesCover_of_checkSub b.cover hsub

end CalleesCoverBundle

end CalleesCoverBundleSec

section ChunkListRelink

/-- Left projection of `CalleesCover` across `c :: cs`. -/
theorem calleesCover_cons_left {lt : LegalTarget} {T : Target}
    {exits : List Sym} {nX : Nat}
    {c : CompiledChunk T lt exits nX} {cs : List (CompiledChunk T lt exits nX)}
    {S : List SigEntry} (h : CalleesCover lt (chunksFns (c :: cs)) S) :
    CalleesCover lt c.fs S := by
  intro f hf
  exact h f (List.mem_append_left _ hf)

/-- Right projection of `CalleesCover` across `c :: cs`. -/
theorem calleesCover_cons_right {lt : LegalTarget} {T : Target}
    {exits : List Sym} {nX : Nat}
    {c : CompiledChunk T lt exits nX} {cs : List (CompiledChunk T lt exits nX)}
    {S : List SigEntry} (h : CalleesCover lt (chunksFns (c :: cs)) S) :
    CalleesCover lt (chunksFns cs) S := by
  intro f hf
  exact h f (List.mem_append_right _ hf)

@[simp] theorem relinkCover_fs {T : Target} {lt : LegalTarget} {exits : List Sym} {nX : Nat}
    (c : CompiledChunk T lt exits nX) (ext₂ : List (SigEntry × Nat)) (S : List SigEntry)
    (hcov : CalleesCover lt c.fs S) (hagree : checkExtAgreeOn S c.extCallees ext₂ = true) :
    (c.relinkCover ext₂ S hcov hagree).fs = c.fs := rfl

@[simp] theorem relinkCover_code {T : Target} {lt : LegalTarget} {exits : List Sym} {nX : Nat}
    (c : CompiledChunk T lt exits nX) (ext₂ : List (SigEntry × Nat)) (S : List SigEntry)
    (hcov : CalleesCover lt c.fs S) (hagree : checkExtAgreeOn S c.extCallees ext₂ = true) :
    (c.relinkCover ext₂ S hcov hagree).compiled.code = c.compiled.code := rfl

@[simp] theorem relinkCover_bounds {T : Target} {lt : LegalTarget} {exits : List Sym}
    {nX : Nat} (c : CompiledChunk T lt exits nX) (ext₂ : List (SigEntry × Nat))
    (S : List SigEntry) (hcov : CalleesCover lt c.fs S)
    (hagree : checkExtAgreeOn S c.extCallees ext₂ = true) :
    (c.relinkCover ext₂ S hcov hagree).compiled.bounds = c.compiled.bounds := rfl

@[simp] theorem relinkCover_maxBound {T : Target} {lt : LegalTarget} {exits : List Sym}
    {nX : Nat} (c : CompiledChunk T lt exits nX) (ext₂ : List (SigEntry × Nat))
    (S : List SigEntry) (hcov : CalleesCover lt c.fs S)
    (hagree : checkExtAgreeOn S c.extCallees ext₂ = true) :
    (c.relinkCover ext₂ S hcov hagree).maxBound = c.maxBound := rfl

@[simp] theorem relinkCover_sigBounds {T : Target} {lt : LegalTarget} {exits : List Sym}
    {nX : Nat} (c : CompiledChunk T lt exits nX) (ext₂ : List (SigEntry × Nat))
    (S : List SigEntry) (hcov : CalleesCover lt c.fs S)
    (hagree : checkExtAgreeOn S c.extCallees ext₂ = true) :
    (c.relinkCover ext₂ S hcov hagree).compiled.sigBounds = c.compiled.sigBounds := rfl

/-- Check `checkExtAgreeOn S` on every chunk in a list against the chained accumulator
`acc`, `c₀.compiled.sigBounds ++ acc`, etc. -/
@[expose] def checkChunksExtAgreeOn {T : Target} {lt : LegalTarget}
    {exits : List Sym} {nX : Nat} (S : List SigEntry) :
    List (CompiledChunk T lt exits nX) → List (SigEntry × Nat) → Bool
  | [], _ => true
  | c :: cs, acc =>
    checkExtAgreeOn S c.extCallees acc &&
    checkChunksExtAgreeOn S cs (c.compiled.sigBounds ++ acc)

/-- Check `checkExtAgreeOn S` pairwise against explicit literal callee-bound lists `extLits`. -/
@[expose] def checkChunksExtAgreeOnLit {T : Target} {lt : LegalTarget}
    {exits : List Sym} {nX : Nat} (S : List SigEntry) :
    List (CompiledChunk T lt exits nX) → List (List (SigEntry × Nat)) → Bool
  | [], [] => true
  | c :: cs, ext :: exts =>
    checkExtAgreeOn S c.extCallees ext && checkChunksExtAgreeOnLit S cs exts
  | _, _ => false

/-- Relink every chunk in `chunks` sequentially against `acc`, `c₀.compiled.sigBounds ++ acc`,
etc., using a `CalleesCover` proof and `checkChunksExtAgreeOn`. -/
@[expose] def relinkChunkListCover {T : Target} {lt : LegalTarget}
    {exits : List Sym} {nX : Nat}
    (chunks : List (CompiledChunk T lt exits nX))
    (acc : List (SigEntry × Nat)) (S : List SigEntry)
    (hcov : CalleesCover lt (chunksFns chunks) S)
    (hagree : checkChunksExtAgreeOn S chunks acc = true) :
    List (CompiledChunk T lt exits nX) :=
  match chunks with
  | [] => []
  | c :: cs =>
    have hpair := Bool.and_eq_true_iff.mp hagree
    c.relinkCover acc S (calleesCover_cons_left hcov) hpair.1 ::
      relinkChunkListCover cs (c.compiled.sigBounds ++ acc) S
        (calleesCover_cons_right hcov) hpair.2

/-- Relink every chunk in `chunks` using pruned accumulator `pruneExt S newAcc` for chunk 0. -/
@[expose] def relinkChunkListPrune {T : Target} {lt : LegalTarget}
    {exits : List Sym} {nX : Nat}
    (chunks : List (CompiledChunk T lt exits nX))
    (newAcc : List (SigEntry × Nat)) (S : List SigEntry)
    (hcov : CalleesCover lt (chunksFns chunks) S)
    (hagree : checkChunksExtAgreeOn S chunks (pruneExt S newAcc) = true) :
    List (CompiledChunk T lt exits nX) :=
  relinkChunkListCover chunks (pruneExt S newAcc) S hcov hagree

/-- Relink every chunk in `chunks` against pre-pruned literal `extLits` without calling
`pruneExt` inside the kernel. -/
@[expose] def relinkChunkListLit {T : Target} {lt : LegalTarget}
    {exits : List Sym} {nX : Nat}
    (chunks : List (CompiledChunk T lt exits nX))
    (extLits : List (List (SigEntry × Nat))) (S : List SigEntry)
    (hcov : CalleesCover lt (chunksFns chunks) S)
    (hagree : checkChunksExtAgreeOnLit S chunks extLits = true) :
    List (CompiledChunk T lt exits nX) :=
  match chunks, extLits with
  | [], [] => []
  | c :: cs, ext :: exts =>
    have hpair := Bool.and_eq_true_iff.mp hagree
    c.relinkCover ext S (calleesCover_cons_left hcov) hpair.1 ::
      relinkChunkListLit cs exts S (calleesCover_cons_right hcov) hpair.2
  | [], _ :: _ | _ :: _, [] => by simp [checkChunksExtAgreeOnLit] at hagree

section ChunkListPreservation

variable {T : Target} {lt : LegalTarget} {exits : List Sym} {nX : Nat}

@[simp] theorem relinkChunkListCover_fns
    (chunks : List (CompiledChunk T lt exits nX))
    (acc : List (SigEntry × Nat)) (S : List SigEntry)
    (hcov : CalleesCover lt (chunksFns chunks) S)
    (hagree : checkChunksExtAgreeOn S chunks acc = true) :
    chunksFns (relinkChunkListCover chunks acc S hcov hagree) = chunksFns chunks := by
  induction chunks generalizing acc with
  | nil => rfl
  | cons c cs ih =>
    dsimp only [relinkChunkListCover, chunksFns]
    rw [relinkCover_fs, ih]

@[simp] theorem relinkChunkListCover_code
    (chunks : List (CompiledChunk T lt exits nX))
    (acc : List (SigEntry × Nat)) (S : List SigEntry)
    (hcov : CalleesCover lt (chunksFns chunks) S)
    (hagree : checkChunksExtAgreeOn S chunks acc = true) :
    chunksCode (relinkChunkListCover chunks acc S hcov hagree) = chunksCode chunks := by
  induction chunks generalizing acc with
  | nil => rfl
  | cons c cs ih =>
    dsimp only [relinkChunkListCover, chunksCode]
    rw [relinkCover_code, ih]

@[simp] theorem relinkChunkListCover_bounds
    (chunks : List (CompiledChunk T lt exits nX))
    (acc : List (SigEntry × Nat)) (S : List SigEntry)
    (hcov : CalleesCover lt (chunksFns chunks) S)
    (hagree : checkChunksExtAgreeOn S chunks acc = true) :
    chunksBounds (relinkChunkListCover chunks acc S hcov hagree) = chunksBounds chunks := by
  induction chunks generalizing acc with
  | nil => rfl
  | cons c cs ih =>
    dsimp only [relinkChunkListCover, chunksBounds]
    rw [relinkCover_bounds, ih]

@[simp] theorem relinkChunkListCover_maxBound
    (chunks : List (CompiledChunk T lt exits nX))
    (acc : List (SigEntry × Nat)) (S : List SigEntry)
    (hcov : CalleesCover lt (chunksFns chunks) S)
    (hagree : checkChunksExtAgreeOn S chunks acc = true) :
    chunksMaxBound (relinkChunkListCover chunks acc S hcov hagree) =
      chunksMaxBound chunks := by
  induction chunks generalizing acc with
  | nil => rfl
  | cons c cs ih =>
    dsimp only [relinkChunkListCover, chunksMaxBound]
    rw [relinkCover_maxBound, ih]

@[simp] theorem relinkChunkListLit_fns
    (chunks : List (CompiledChunk T lt exits nX))
    (extLits : List (List (SigEntry × Nat))) (S : List SigEntry)
    (hcov : CalleesCover lt (chunksFns chunks) S)
    (hagree : checkChunksExtAgreeOnLit S chunks extLits = true) :
    chunksFns (relinkChunkListLit chunks extLits S hcov hagree) = chunksFns chunks := by
  induction chunks generalizing extLits with
  | nil =>
    cases extLits with
    | nil => rfl
    | cons => simp [checkChunksExtAgreeOnLit] at hagree
  | cons c cs ih =>
    cases extLits with
    | nil => simp [checkChunksExtAgreeOnLit] at hagree
    | cons ext exts =>
      dsimp only [relinkChunkListLit, chunksFns]
      rw [relinkCover_fs, ih]

@[simp] theorem relinkChunkListLit_code
    (chunks : List (CompiledChunk T lt exits nX))
    (extLits : List (List (SigEntry × Nat))) (S : List SigEntry)
    (hcov : CalleesCover lt (chunksFns chunks) S)
    (hagree : checkChunksExtAgreeOnLit S chunks extLits = true) :
    chunksCode (relinkChunkListLit chunks extLits S hcov hagree) = chunksCode chunks := by
  induction chunks generalizing extLits with
  | nil =>
    cases extLits with
    | nil => rfl
    | cons => simp [checkChunksExtAgreeOnLit] at hagree
  | cons c cs ih =>
    cases extLits with
    | nil => simp [checkChunksExtAgreeOnLit] at hagree
    | cons ext exts =>
      dsimp only [relinkChunkListLit, chunksCode]
      rw [relinkCover_code, ih]

@[simp] theorem relinkChunkListLit_bounds
    (chunks : List (CompiledChunk T lt exits nX))
    (extLits : List (List (SigEntry × Nat))) (S : List SigEntry)
    (hcov : CalleesCover lt (chunksFns chunks) S)
    (hagree : checkChunksExtAgreeOnLit S chunks extLits = true) :
    chunksBounds (relinkChunkListLit chunks extLits S hcov hagree) = chunksBounds chunks := by
  induction chunks generalizing extLits with
  | nil =>
    cases extLits with
    | nil => rfl
    | cons => simp [checkChunksExtAgreeOnLit] at hagree
  | cons c cs ih =>
    cases extLits with
    | nil => simp [checkChunksExtAgreeOnLit] at hagree
    | cons ext exts =>
      dsimp only [relinkChunkListLit, chunksBounds]
      rw [relinkCover_bounds, ih]

@[simp] theorem relinkChunkListLit_maxBound
    (chunks : List (CompiledChunk T lt exits nX))
    (extLits : List (List (SigEntry × Nat))) (S : List SigEntry)
    (hcov : CalleesCover lt (chunksFns chunks) S)
    (hagree : checkChunksExtAgreeOnLit S chunks extLits = true) :
    chunksMaxBound (relinkChunkListLit chunks extLits S hcov hagree) =
      chunksMaxBound chunks := by
  induction chunks generalizing extLits with
  | nil =>
    cases extLits with
    | nil => rfl
    | cons => simp [checkChunksExtAgreeOnLit] at hagree
  | cons c cs ih =>
    cases extLits with
    | nil => simp [checkChunksExtAgreeOnLit] at hagree
    | cons ext exts =>
      dsimp only [relinkChunkListLit, chunksMaxBound]
      rw [relinkCover_maxBound, ih]

end ChunkListPreservation

section LinkCheckPreservation

/-- Reuse `fnNameOk`, `stringsNodup`, and `L.progSmall` from an existing `checkLinkList` proof
when `chunksFns` and `chunksCode` are preserved, avoiding re-checking assembly size and label
uniqueness in the kernel. -/
theorem checkLinkList_of_preserved {T : Target} {L : TargetLayout T} {lt : LegalTarget}
    {exits : List Sym} {nX : Nat} {ext₁ ext₂ : List (SigEntry × Nat)}
    {chunks₁ chunks₂ : List (CompiledChunk T lt exits nX)}
    (hlink₁ : checkLinkList L ext₁ chunks₁ = true)
    (hfns : chunksFns chunks₂ = chunksFns chunks₁)
    (hcode : chunksCode chunks₂ = chunksCode chunks₁)
    (hchkExt : checkChunksExt ext₂ chunks₂ = true) :
    checkLinkList L ext₂ chunks₂ = true := by
  have h1 := hlink₁
  dsimp only [checkLinkList] at h1 ⊢
  rw [hfns, hcode]
  simp only [Bool.and_eq_true] at h1 ⊢
  rcases h1 with ⟨⟨⟨⟨_, h2⟩, h3⟩, h4⟩, h5⟩
  exact ⟨⟨⟨⟨hchkExt, h2⟩, h3⟩, h4⟩, h5⟩

/-- Relink an entire `LinkedCert` via `relinkChunkListCover` without re-evaluating `supportsSource`,
`fnNameOk`, `stringsNodup`, or `L.progSmall` in the kernel. -/
@[expose] noncomputable def relinkLinkedCertCover {T : Target} {L : TargetLayout T}
    {lt : LegalTarget} {hcl : Rega.LabelClean T.toIsa} {mod mod' : Module}
    {extOld extNew : List (SigEntry × Nat)} {exits : List Sym} {nX maxBound : Nat}
    (cert : LinkedCert T L lt hcl mod extOld exits nX maxBound)
    (hmod' : mod'.fns = mod.fns)
    (acc : List (SigEntry × Nat)) (S : List SigEntry)
    (hcov : CalleesCover lt (chunksFns cert.chunks) S)
    (hagree : checkChunksExtAgreeOn S cert.chunks acc = true)
    (hchkExt : checkChunksExt extNew
      (relinkChunkListCover cert.chunks acc S hcov hagree) = true) :
    LinkedCert T L lt hcl mod' extNew exits nX maxBound where
  chunks := relinkChunkListCover cert.chunks acc S hcov hagree
  linkCheck := checkLinkList_of_preserved cert.linkCheck
    (relinkChunkListCover_fns cert.chunks acc S hcov hagree)
    (relinkChunkListCover_code cert.chunks acc S hcov hagree)
    hchkExt
  fns_eq := by
    rw [relinkChunkListCover_fns, hmod', cert.fns_eq]
  supportsAll := supportsAll_of_eq hmod' cert.supportsAll
  maxBound_le := by
    rw [relinkChunkListCover_maxBound]
    exact cert.maxBound_le

/-- Relink an entire `LinkedCert` via pre-pruned `extLits` (`relinkChunkListLit`) with zero
`pruneExt` evaluation and zero code/AST traversal in the kernel. -/
@[expose] noncomputable def relinkLinkedCertLit {T : Target} {L : TargetLayout T}
    {lt : LegalTarget} {hcl : Rega.LabelClean T.toIsa} {mod mod' : Module}
    {extOld extNew : List (SigEntry × Nat)} {exits : List Sym} {nX maxBound : Nat}
    (cert : LinkedCert T L lt hcl mod extOld exits nX maxBound)
    (hmod' : mod'.fns = mod.fns)
    (extLits : List (List (SigEntry × Nat))) (S : List SigEntry)
    (hcov : CalleesCover lt (chunksFns cert.chunks) S)
    (hagree : checkChunksExtAgreeOnLit S cert.chunks extLits = true)
    (hchkExt : checkChunksExt extNew
      (relinkChunkListLit cert.chunks extLits S hcov hagree) = true) :
    LinkedCert T L lt hcl mod' extNew exits nX maxBound where
  chunks := relinkChunkListLit cert.chunks extLits S hcov hagree
  linkCheck := checkLinkList_of_preserved cert.linkCheck
    (relinkChunkListLit_fns cert.chunks extLits S hcov hagree)
    (relinkChunkListLit_code cert.chunks extLits S hcov hagree)
    hchkExt
  fns_eq := by
    rw [relinkChunkListLit_fns, hmod', cert.fns_eq]
  supportsAll := supportsAll_of_eq hmod' cert.supportsAll
  maxBound_le := by
    rw [relinkChunkListLit_maxBound]
    exact cert.maxBound_le

@[simp] theorem relinkLinkedCertCover_chunks {T : Target} {L : TargetLayout T} {lt : LegalTarget}
    {hcl : Rega.LabelClean T.toIsa} {mod mod' : Module}
    {extOld extNew : List (SigEntry × Nat)} {exits : List Sym} {nX maxBound : Nat}
    (cert : LinkedCert T L lt hcl mod extOld exits nX maxBound)
    (hmod' : mod'.fns = mod.fns)
    (acc : List (SigEntry × Nat)) (S : List SigEntry)
    (hcov : CalleesCover lt (chunksFns cert.chunks) S)
    (hagree : checkChunksExtAgreeOn S cert.chunks acc = true)
    (hchkExt : checkChunksExt extNew
      (relinkChunkListCover cert.chunks acc S hcov hagree) = true) :
    (relinkLinkedCertCover cert hmod' acc S hcov hagree hchkExt).chunks =
      relinkChunkListCover cert.chunks acc S hcov hagree := rfl

@[simp] theorem relinkLinkedCertCover_code {T : Target} {L : TargetLayout T} {lt : LegalTarget}
    {hcl : Rega.LabelClean T.toIsa} {mod mod' : Module}
    {extOld extNew : List (SigEntry × Nat)} {exits : List Sym} {nX maxBound : Nat}
    (cert : LinkedCert T L lt hcl mod extOld exits nX maxBound)
    (hmod' : mod'.fns = mod.fns)
    (acc : List (SigEntry × Nat)) (S : List SigEntry)
    (hcov : CalleesCover lt (chunksFns cert.chunks) S)
    (hagree : checkChunksExtAgreeOn S cert.chunks acc = true)
    (hchkExt : checkChunksExt extNew
      (relinkChunkListCover cert.chunks acc S hcov hagree) = true) :
    (relinkLinkedCertCover cert hmod' acc S hcov hagree hchkExt).code = cert.code := by
  dsimp only [LinkedCert.code, LinkedCert.compiled, linkCompiledList]
  rw [relinkLinkedCertCover_chunks, relinkChunkListCover_code]

@[simp] theorem relinkLinkedCertCover_bounds {T : Target} {L : TargetLayout T} {lt : LegalTarget}
    {hcl : Rega.LabelClean T.toIsa} {mod mod' : Module}
    {extOld extNew : List (SigEntry × Nat)} {exits : List Sym} {nX maxBound : Nat}
    (cert : LinkedCert T L lt hcl mod extOld exits nX maxBound)
    (hmod' : mod'.fns = mod.fns)
    (acc : List (SigEntry × Nat)) (S : List SigEntry)
    (hcov : CalleesCover lt (chunksFns cert.chunks) S)
    (hagree : checkChunksExtAgreeOn S cert.chunks acc = true)
    (hchkExt : checkChunksExt extNew
      (relinkChunkListCover cert.chunks acc S hcov hagree) = true) :
    (relinkLinkedCertCover cert hmod' acc S hcov hagree hchkExt).bounds = cert.bounds := by
  dsimp only [LinkedCert.bounds, LinkedCert.compiled, linkCompiledList]
  rw [relinkLinkedCertCover_chunks, relinkChunkListCover_bounds]

@[simp] theorem relinkLinkedCertLit_chunks {T : Target} {L : TargetLayout T} {lt : LegalTarget}
    {hcl : Rega.LabelClean T.toIsa} {mod mod' : Module}
    {extOld extNew : List (SigEntry × Nat)} {exits : List Sym} {nX maxBound : Nat}
    (cert : LinkedCert T L lt hcl mod extOld exits nX maxBound)
    (hmod' : mod'.fns = mod.fns)
    (extLits : List (List (SigEntry × Nat))) (S : List SigEntry)
    (hcov : CalleesCover lt (chunksFns cert.chunks) S)
    (hagree : checkChunksExtAgreeOnLit S cert.chunks extLits = true)
    (hchkExt : checkChunksExt extNew
      (relinkChunkListLit cert.chunks extLits S hcov hagree) = true) :
    (relinkLinkedCertLit cert hmod' extLits S hcov hagree hchkExt).chunks =
      relinkChunkListLit cert.chunks extLits S hcov hagree := rfl

@[simp] theorem relinkLinkedCertLit_code {T : Target} {L : TargetLayout T} {lt : LegalTarget}
    {hcl : Rega.LabelClean T.toIsa} {mod mod' : Module}
    {extOld extNew : List (SigEntry × Nat)} {exits : List Sym} {nX maxBound : Nat}
    (cert : LinkedCert T L lt hcl mod extOld exits nX maxBound)
    (hmod' : mod'.fns = mod.fns)
    (extLits : List (List (SigEntry × Nat))) (S : List SigEntry)
    (hcov : CalleesCover lt (chunksFns cert.chunks) S)
    (hagree : checkChunksExtAgreeOnLit S cert.chunks extLits = true)
    (hchkExt : checkChunksExt extNew
      (relinkChunkListLit cert.chunks extLits S hcov hagree) = true) :
    (relinkLinkedCertLit cert hmod' extLits S hcov hagree hchkExt).code = cert.code := by
  dsimp only [LinkedCert.code, LinkedCert.compiled, linkCompiledList]
  rw [relinkLinkedCertLit_chunks, relinkChunkListLit_code]

@[simp] theorem relinkLinkedCertLit_bounds {T : Target} {L : TargetLayout T} {lt : LegalTarget}
    {hcl : Rega.LabelClean T.toIsa} {mod mod' : Module}
    {extOld extNew : List (SigEntry × Nat)} {exits : List Sym} {nX maxBound : Nat}
    (cert : LinkedCert T L lt hcl mod extOld exits nX maxBound)
    (hmod' : mod'.fns = mod.fns)
    (extLits : List (List (SigEntry × Nat))) (S : List SigEntry)
    (hcov : CalleesCover lt (chunksFns cert.chunks) S)
    (hagree : checkChunksExtAgreeOnLit S cert.chunks extLits = true)
    (hchkExt : checkChunksExt extNew
      (relinkChunkListLit cert.chunks extLits S hcov hagree) = true) :
    (relinkLinkedCertLit cert hmod' extLits S hcov hagree hchkExt).bounds = cert.bounds := by
  dsimp only [LinkedCert.bounds, LinkedCert.compiled, linkCompiledList]
  rw [relinkLinkedCertLit_chunks, relinkChunkListLit_bounds]

end LinkCheckPreservation

end ChunkListRelink

end LeanQbe.T
