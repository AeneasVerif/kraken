module

public import LeanQbe.T.Examples.Kissat.FullInv2
public import LeanQbe.T.Examples.Kissat.SolverIngestLemmas1
public import LeanQbe.T.Logic.C0Step
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Full` UNSAT-Only Shared Invariants & Transition Helpers (`Stage 4`, Part 1)

Defines canonical Stage-4 UNSAT-only invariants (`FullMrkZero`, `FullLitMarksClear`,
`FullArenaVarsNodup`, `FullLastLearnedWf`, `FullExtScratchOk`, `FullSparseInv`, `FullDenseInv`,
`FullSparseInvW`, `FullDenseInvW`, `FullOtfsInvW`), watch/dense/arena transition helpers
(`inPlaceShrink_preserves_arena`, `addGarbageClause_preserves_fullCore`, `addUnit`/`addBin`/
`deleteBin` wrappers), level-0 conflict refutation helpers, and shared auxiliary predicates.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test

/-! ## 1. Canonical Stage-4 UNSAT-only invariants -/

/-- Variable marks (`mrk[0 ..< max_vars]`) are cleared to `0#8`. -/
def FullMrkZero (c : FullCfg) (s : FullState) : Prop :=
  ∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8

/-- Both variable marks (`mrk`) and literal marks (`lit_mark`) are cleared to `0#8`. -/
def FullLitMarksClear (c : FullCfg) (s : FullState) : Prop :=
  FullMrkZero c s ∧ (∀ l < 2 * c.max_vars, s.core.lit_mark[l]?.getD 0#8 = 0#8)

/-- Every live arena clause has pairwise distinct variables (`NoDup` & non-tautology). -/
def FullArenaVarsNodup (s : FullState) : Prop :=
  ∀ r ∈ fullArenaClauseRefs s, fullArenaClauseGarb s r = false →
    ((fullArenaClauseLits s r).map (· / 2)).Nodup

/-- Every active slot in `last_learned[0 ..< 8]` is `0xFFFFFFFF#32` or a valid arena ref. -/
def FullLastLearnedWf (s : FullState) : Prop :=
  ∀ i < 8,
    let cr := s.scratch.last_learned[i]?.getD 0xFFFFFFFF#32
    cr = 0xFFFFFFFF#32 ∨ cr.toNat ∈ fullArenaClauseRefs s

/-- Soundness-adjacent scratch bounds (`last_learned` validity + `extend_len ≤ extend_cap`). -/
def FullExtScratchOk (c : FullCfg) (s : FullState) : Prop :=
  FullLastLearnedWf s ∧ s.scratch.extend_len ≤ c.extend_cap

/-- Canonical sparse-mode (2WL) UNSAT-only solver invariant (`dense_mode = 0#64`). -/
def FullSparseInv (c : FullCfg) (F0 : CNF Nat) (s : FullState) : Prop :=
  FullCoreInv c F0 s ∧ FullLitMarksClear c s ∧ FullArenaVarsNodup s ∧
  FullExtScratchOk c s ∧ s.core.dense_mode = 0#64

/-- Canonical dense-mode (level-0 occurrence lists) UNSAT-only invariant (`dense_mode ≠ 0#64`). -/
def FullDenseInv (c : FullCfg) (F0 : CNF Nat) (s : FullState) : Prop :=
  FullCoreInv c F0 s ∧ FullLitMarksClear c s ∧ FullArenaVarsNodup s ∧
  FullExtScratchOk c s ∧ s.core.cur_level = 0 ∧ s.core.dense_mode ≠ 0#64

/-- Scratch-level equality predicate preserving `last_learned` and `extend_len`. -/
def FullExtScratchPres (s s' : FullState) : Prop :=
  s'.scratch.last_learned = s.scratch.last_learned ∧
  s'.scratch.extend_len = s.scratch.extend_len

/-- Extended scratch-frame predicate preserved by `full_backtrack`, `full_propagate*`,
`full_add_unit`, and `full_sweep_copy` for probing, transitive, & kitten-sweeping callers. -/
def FullProbeScratchPres (s s' : FullState) : Prop :=
  FullExtScratchPres s s' ∧
  s'.scratch.work_stk1 = s.scratch.work_stk1 ∧
  s'.scratch.work_stk2 = s.scratch.work_stk2 ∧
  s'.scratch.tarjan_mark = s.scratch.tarjan_mark ∧
  s'.scratch.scratch_buf = s.scratch.scratch_buf ∧
  s'.scratch.ant_sz = s.scratch.ant_sz ∧
  s'.scratch.res_sz = s.scratch.res_sz ∧
  s'.scratch.sim_sig = s.scratch.sim_sig

/-- Explicit-witness sparse-mode invariant (`FullSparseInv c F0 s ↔ ∃ F_cur, ...`). -/
def FullSparseInvW (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) : Prop :=
  s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧ FullLitMarksClear c s ∧
  FullArenaVarsNodup s ∧ FullExtScratchOk c s ∧ s.core.dense_mode = 0#64

/-- Explicit-witness dense-mode invariant (`FullDenseInv c F0 s ↔ ∃ F_cur, ...`). -/
def FullDenseInvW (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) : Prop :=
  s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧ FullLitMarksClear c s ∧
  FullArenaVarsNodup s ∧ FullExtScratchOk c s ∧ s.core.cur_level = 0 ∧ s.core.dense_mode ≠ 0#64

theorem FullSparseInvW.toSparse {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullSparseInvW c F0 F_cur s) : FullSparseInv c F0 s :=
  ⟨⟨h.1, F_cur, h.2.1⟩, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

theorem FullSparseInv.exists_witness {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseInv c F0 s) : ∃ F_cur, FullSparseInvW c F0 F_cur s :=
  let ⟨F_cur, hw⟩ := h.1.witness
  ⟨F_cur, h.1.lengths, hw, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

theorem FullDenseInvW.toDense {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) : FullDenseInv c F0 s :=
  ⟨⟨h.1, F_cur, h.2.1⟩, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

theorem FullDenseInv.exists_witness {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullDenseInv c F0 s) : ∃ F_cur, FullDenseInvW c F0 F_cur s :=
  let ⟨F_cur, hw⟩ := h.1.witness
  ⟨F_cur, h.1.lengths, hw, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

theorem FullLitMarksClear.toFullMarksClear {c : FullCfg} {s : FullState}
    (hlen : s.LengthsOk c) (h : FullLitMarksClear c s) : FullMarksClear s :=
  fun v hv => h.1 v (Nat.lt_of_lt_of_le hv hlen.core_ok.cur_vars_le)

theorem FullSparseInv.toFullInv {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseInv c F0 s) : FullInv c F0 s :=
  ⟨h.1, h.2.1.toFullMarksClear h.1.lengths⟩

theorem FullDenseInv.toFullInv {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullDenseInv c F0 s) : FullInv c F0 s :=
  ⟨h.1, h.2.1.toFullMarksClear h.1.lengths⟩

theorem FullSparseInv.lengths {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseInv c F0 s) : s.LengthsOk c := h.1.lengths

theorem FullDenseInv.lengths {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullDenseInv c F0 s) : s.LengthsOk c := h.1.lengths

theorem FullSparseInv.inconsistent_unsat {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseInv c F0 s) (hinc : s.core.inconsistent ≠ 0#64) : F0.Unsat :=
  h.1.inconsistent_unsat hinc

theorem FullDenseInv.inconsistent_unsat {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullDenseInv c F0 s) (hinc : s.core.inconsistent ≠ 0#64) : F0.Unsat :=
  h.1.inconsistent_unsat hinc

theorem FullExtScratchOk.of_pres {c : FullCfg} {s s' : FullState}
    (h : FullExtScratchOk c s) (hpres : FullExtScratchPres s s')
    (hsub : ∀ r ∈ fullArenaClauseRefs s, r ∈ fullArenaClauseRefs s') : FullExtScratchOk c s' := by
  refine ⟨fun i hi => ?_, hpres.2 ▸ h.2⟩
  dsimp only; rw [hpres.1]
  exact (h.1 i hi).elim Or.inl fun hr => Or.inr (hsub _ hr)

theorem FullLastLearnedWf.of_refs_subset {s s' : FullState}
    (h : FullLastLearnedWf s) (hll : s'.scratch.last_learned = s.scratch.last_learned)
    (hsub : ∀ r ∈ fullArenaClauseRefs s, r ∈ fullArenaClauseRefs s') : FullLastLearnedWf s' := by
  intro i hi; dsimp only; rw [hll]
  exact (h i hi).elim Or.inl fun hr => Or.inr (hsub _ hr)

theorem FullLastLearnedWf.of_cleared {s : FullState}
    (hclear : ∀ i < 8, s.scratch.last_learned[i]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32) :
    FullLastLearnedWf s := fun i hi => Or.inl (hclear i hi)

private theorem nodup_of_map {α β : Type} (f : α → β) :
    ∀ {xs : List α}, (xs.map f).Nodup → xs.Nodup
  | [], _ => List.Pairwise.nil
  | x :: xs, h => by
    rw [List.map_cons, List.nodup_cons] at h
    rw [List.nodup_cons]
    exact ⟨fun hx => h.1 (List.mem_map_of_mem hx), nodup_of_map f h.2⟩

theorem FullArenaVarsNodup.nodup_lits {s : FullState} (h : FullArenaVarsNodup s)
    {r : Nat} (hr : r ∈ fullArenaClauseRefs s) (hg : fullArenaClauseGarb s r = false) :
    (fullArenaClauseLits s r).Nodup :=
  nodup_of_map (· / 2) (h r hr hg)

private theorem no_taut_of_map_div2 :
    ∀ {xs : List Nat}, (xs.map (· / 2)).Nodup → ∀ {l}, l ∈ xs → (l ^^^ 1) ∉ xs
  | [], _, _, h => nomatch h
  | x :: xs, hnd, l, hl => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hl with rfl | hmem
    · intro hneg
      rcases List.mem_cons.mp hneg with heq | hmem'
      · exact litNeg_ne_self l heq
      · exact hnd.1 (List.mem_map.mpr ⟨l ^^^ 1, hmem', litVar_litNeg l⟩)
    · intro hneg
      rcases List.mem_cons.mp hneg with heq | hmem'
      · exact hnd.1 (List.mem_map.mpr ⟨l, hmem, by rw [← heq]; exact (litVar_litNeg l).symm⟩)
      · exact no_taut_of_map_div2 hnd.2 hmem hmem'

theorem FullArenaVarsNodup.no_taut {s : FullState} (h : FullArenaVarsNodup s)
    {r : Nat} (hr : r ∈ fullArenaClauseRefs s) (hg : fullArenaClauseGarb s r = false)
    {l : Nat} (hl : l ∈ fullArenaClauseLits s r) : (l ^^^ 1) ∉ fullArenaClauseLits s r :=
  no_taut_of_map_div2 (h r hr hg) hl

theorem FullSparseInv.with_scratch {c : FullCfg} {F0 : CNF Nat} {s s' : FullState}
    (h : FullSparseInv c F0 s) (hlen' : s'.LengthsOk c)
    (hcore : PreservesCoreSlice (fullSafetySlice c).coreProj s s')
    (hext' : FullExtScratchOk c s') : FullSparseInv c F0 s' := by
  have heq : s'.core = s.core := fullCoreState_agrees_with_scratch hcore
  refine ⟨h.1.with_scratch hlen' hcore, ?_, ?_, hext', heq ▸ h.2.2.2.2⟩
  · unfold FullLitMarksClear FullMrkZero; rw [heq]; exact h.2.1
  · unfold FullArenaVarsNodup fullArenaClauseRefs fullArenaClauseGarb fullArenaClauseLits
    rw [heq]; exact h.2.2.1

theorem FullSparseInv.of_safetySlice {c : FullCfg} {F0 : CNF Nat} {s s' : FullState}
    (h : FullSparseInv c F0 s) (hlen' : s'.LengthsOk c)
    (hcore : PreservesCoreSlice (fullSafetySlice c).coreProj s s')
    (hpres : FullExtScratchPres s s') : FullSparseInv c F0 s' := by
  have heq : s'.core = s.core := fullCoreState_agrees_with_scratch hcore
  exact h.with_scratch hlen' hcore
    (h.2.2.2.1.of_pres hpres fun r hr => by unfold fullArenaClauseRefs; rwa [heq])

theorem FullDenseInv.with_scratch {c : FullCfg} {F0 : CNF Nat} {s s' : FullState}
    (h : FullDenseInv c F0 s) (hlen' : s'.LengthsOk c)
    (hcore : PreservesCoreSlice (fullSafetySlice c).coreProj s s')
    (hext' : FullExtScratchOk c s') : FullDenseInv c F0 s' := by
  have heq : s'.core = s.core := fullCoreState_agrees_with_scratch hcore
  refine ⟨h.1.with_scratch hlen' hcore, ?_, ?_, hext', heq ▸ h.2.2.2.2.1, heq ▸ h.2.2.2.2.2⟩
  · unfold FullLitMarksClear FullMrkZero; rw [heq]; exact h.2.1
  · unfold FullArenaVarsNodup fullArenaClauseRefs fullArenaClauseGarb fullArenaClauseLits
    rw [heq]; exact h.2.2.1

theorem FullDenseInv.of_safetySlice {c : FullCfg} {F0 : CNF Nat} {s s' : FullState}
    (h : FullDenseInv c F0 s) (hlen' : s'.LengthsOk c)
    (hcore : PreservesCoreSlice (fullSafetySlice c).coreProj s s')
    (hpres : FullExtScratchPres s s') : FullDenseInv c F0 s' := by
  have heq : s'.core = s.core := fullCoreState_agrees_with_scratch hcore
  exact h.with_scratch hlen' hcore
    (h.2.2.2.1.of_pres hpres fun r hr => by unfold fullArenaClauseRefs; rwa [heq])

/-- Updating `core.fuel` and `scratch` preserves `FullCoreInv` (used by `full_walk`). -/
theorem FullCoreInv.with_fuel_scratch_spec {c : FullCfg} {F0 : CNF Nat} {s s' : FullState}
    (h : FullCoreInv c F0 s) (hlen' : s'.LengthsOk c) {fuel' : BitVec 64}
    (hcore : s'.core = { s.core with fuel := fuel' }) : FullCoreInv c F0 s' := by
  obtain ⟨F_cur, hw⟩ := h.witness
  refine ⟨hlen', F_cur, ?_⟩
  rw [hcore]
  exact { hw with
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }

theorem FullSparseInv.with_fuel_scratch {c : FullCfg} {F0 : CNF Nat} {s s' : FullState}
    (h : FullSparseInv c F0 s) (hlen' : s'.LengthsOk c) {fuel' : BitVec 64}
    (hcore : s'.core = { s.core with fuel := fuel' })
    (hpres : FullExtScratchPres s s') : FullSparseInv c F0 s' := by
  refine ⟨h.1.with_fuel_scratch_spec hlen' hcore, ?_, ?_, ?_, by rw [hcore]; exact h.2.2.2.2⟩
  · unfold FullLitMarksClear FullMrkZero; rw [hcore]; exact h.2.1
  · unfold FullArenaVarsNodup fullArenaClauseRefs fullArenaClauseGarb fullArenaClauseLits
    rw [hcore]; exact h.2.2.1
  · exact h.2.2.2.1.of_pres hpres fun r hr => by unfold fullArenaClauseRefs; rwa [hcore]

theorem FullSparseInv.with_d {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseInv c F0 s) (cur' val' : BitVec 64) :
    FullSparseInv c F0 { s with core := { s.core with d_cur := cur', d_val := val' } } :=
  ⟨h.1.with_d cur' val', h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

/-- Initial zeroed state produced by `full_init_state` satisfies `FullSparseInv`. -/
theorem fullInv_init_sparse {c : FullCfg} {F0 : CNF Nat} {s : FullState} (hlen : s.LengthsOk c)
    (hinc : s.core.inconsistent = 0#64) (hal : s.core.arena_len = 0)
    (hwvec : s.core.wvec = List.replicate (4 * c.max_vars) 0#32)
    (hte : s.core.trail_end = 0) (hcl : s.core.cur_level = 0)
    (hft0 : (s.core.frame_trail[0]?.getD 0#32).toNat = 0)
    (hvals : s.core.vals = List.replicate (2 * c.max_vars) 0#8)
    (hmrk : s.core.mrk = List.replicate c.max_vars 0#8)
    (hlm : s.core.lit_mark = List.replicate (2 * c.max_vars) 0#8)
    (hll : ∀ i < 8, s.scratch.last_learned[i]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32)
    (hext : s.scratch.extend_len = 0) (hdense : s.core.dense_mode = 0#64) :
    FullSparseInv c F0 s := by
  have hfi := fullInv_init (F0 := F0) hlen hinc hal hwvec hte hcl hft0 hvals hmrk
  have hrefs : fullArenaClauseRefs s = [] := by
    simp [fullArenaClauseRefs, fullArenaClauseRefsCore, hal, fullArenaScanRefs]
  refine ⟨hfi.core, ⟨fun v hv => by rw [hmrk]; simp [hv], fun l hl => by rw [hlm]; simp [hl]⟩,
    fun r hr _ => by simp [hrefs] at hr,
    ⟨FullLastLearnedWf.of_cleared hll, by omega⟩, hdense⟩

/-! ## 2. Watch-stack, dense-to-sparse, and `addUnit`/`addBin`/`deleteBin` helpers -/

theorem DenseWatchSliceOk.toWatchSliceOk {F_cur : List (List Nat)} {k : FullCoreState}
    {lit p rem : Nat} (h : DenseWatchSliceOk F_cur k lit p rem) :
    WatchSliceOk F_cur k lit p rem := by
  induction h with
  | empty => exact .empty
  | bin hp hf hne hlt hent _ ih => exact .bin hp hf hne hlt hent ih
  | occ hp hp1 hf _ hlt href _ ih => exact .large hp hp1 hf hlt href ih

theorem DenseWatchesInv.toWatchesInv {F_cur : List (List Nat)} {k : FullCoreState}
    (h : DenseWatchesInv F_cur k) : WatchesInv F_cur k :=
  ⟨h.layout, fun l hl => (h.slices l hl).toWatchSliceOk⟩

/-- Clearing `dense_mode := 0#64` converts `FullDenseInvW` directly into `FullSparseInvW`. -/
theorem FullDenseInvW.toSparse_clear_dense {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) :
    FullSparseInvW c F0 F_cur { s with core := { s.core with dense_mode := 0#64 } } := by
  let hw := h.2.1
  let k' : FullCoreState := { s.core with dense_mode := 0#64 }
  have hdw : DenseWatchesInv F_cur s.core := by
    have hm := hw.watches; unfold ModeWatchesInv at hm
    simp only [h.2.2.2.2.2.2, ↓reduceIte] at hm; exact hm
  have hsw : ModeWatchesInv F_cur k' := by
    unfold ModeWatchesInv; simp only [show k'.dense_mode = 0#64 from rfl, ↓reduceIte]
    have hrefl : (cnfOfClauses F_cur).Entails (cnfOfClauses F_cur) := by
      rw [CNF.entails_def]; exact fun _ h => h
    exact ⟨hdw.layout.with_wstk (k' := k') rfl rfl rfl rfl, fun l hl =>
      WatchSliceOk.mono (k := s.core) (k' := k') hrefl (Nat.le_refl _) (fun _ hr => hr)
        (fun _ _ _ => rfl) (hdw.slices l hl).toWatchSliceOk⟩
  refine ⟨⟨{ h.1.core_ok with vals_len := h.1.core_ok.vals_len }, h.1.scratch_ok⟩,
    { hw with arena := { hw.arena with len_ok := hw.arena.len_ok }, watches := hsw },
    h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, rfl⟩

/-- Clearing `dense_mode := 0#64` converts `FullDenseInv` directly into `FullSparseInv`
(`full_rebuild_watches` entry). -/
theorem FullDenseInv.toSparse_clear_dense {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullDenseInv c F0 s) :
    FullSparseInv c F0 { s with core := { s.core with dense_mode := 0#64 } } :=
  let ⟨_, hdw⟩ := h.exists_witness; hdw.toSparse_clear_dense.toSparse

theorem fullWatchSlice_relocate {F F' : List (List Nat)} {k k' : FullCoreState}
    {lit p p' rem : Nat} (hF : (cnfOfClauses F').Entails (cnfOfClauses F))
    (hvars : k.cur_vars ≤ k'.cur_vars)
    (hsub : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k')
    (hwstk : ∀ idx < rem, k'.wstk[p' + idx]? = k.wstk[p + idx]?)
    (h : WatchSliceOk F k lit p rem) : WatchSliceOk F' k' lit p' rem := by
  induction h generalizing p' with
  | empty => exact .empty
  | @bin p rem w0 hp hflag hne hlt hent _ ih =>
    refine .bin (by simpa using (hwstk 0 (by omega)).trans hp) hflag hne (by omega)
      (CNF.entails_clause_trans hF hent)
      (ih (p' := p' + 1) fun idx hi => by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hwstk (idx + 1) (by omega))
  | @large p rem w0 cref hp hp1 hflag hlt href _ ih =>
    refine .large (by simpa using (hwstk 0 (by omega)).trans hp)
      (by simpa using (hwstk 1 (by omega)).trans hp1) hflag hlt (hsub _ href)
      (ih (p' := p' + 2) fun idx hi => by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hwstk (idx + 2) (by omega))

theorem DenseWatchSliceOk.relocate {F F' : List (List Nat)} {k k' : FullCoreState}
    {lit p p' rem : Nat} (hF : (cnfOfClauses F').Entails (cnfOfClauses F))
    (hvars : k.cur_vars ≤ k'.cur_vars)
    (hsub : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k')
    (hwstk : ∀ idx < rem, k'.wstk[p' + idx]? = k.wstk[p + idx]?)
    (h : DenseWatchSliceOk F k lit p rem) : DenseWatchSliceOk F' k' lit p' rem := by
  induction h generalizing p' with
  | empty => exact .empty
  | @bin p rem w0 hp hflag hne hlt hent _ ih =>
    refine .bin (by simpa using (hwstk 0 (by omega)).trans hp) hflag hne (by omega)
      (CNF.entails_clause_trans hF hent)
      (ih (p' := p' + 1) fun idx hi => by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hwstk (idx + 1) (by omega))
  | @occ p rem w0 cref hp hp1 hflag hsz hlt href _ ih =>
    refine .occ (by simpa using (hwstk 0 (by omega)).trans hp)
      (by simpa using (hwstk 1 (by omega)).trans hp1) hflag hsz hlt (hsub _ href)
      (ih (p' := p' + 2) fun idx hi => by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hwstk (idx + 2) (by omega))

theorem fullWatchSlice_append_bin {F_cur : List (List Nat)} {k k' : FullCoreState}
    {lit p p' rem : Nat} {w0 : BitVec 32} (hvars : k.cur_vars ≤ k'.cur_vars)
    (hsub : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k')
    (hwstk : ∀ idx < rem, k'.wstk[p' + idx]? = k.wstk[p + idx]?)
    (h : WatchSliceOk F_cur k lit p rem) (hw0 : k'.wstk[p' + rem]? = some w0)
    (hflag : (w0 &&& 0x80000000#32) ≠ 0#32) (hne : w0 ≠ 0xFFFFFFFF#32)
    (hlt : (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k'.cur_vars)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [lit, (w0 &&& 0x7FFFFFFF#32).toNat])) :
    WatchSliceOk F_cur k' lit p' (rem + 1) := by
  induction h generalizing p' with
  | empty => exact .bin (by simpa using hw0) hflag hne hlt hent .empty
  | @bin p rem w hp hf hn hl he _ ih =>
    exact .bin (by simpa using (hwstk 0 (by omega)).trans hp) hf hn (by omega) he
      (ih (p' := p' + 1) (fun idx hi => by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hwstk (idx + 1) (by omega))
        (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hw0))
  | @large p rem w cref hp hp1 hf hl href _ ih =>
    exact .large (by simpa using (hwstk 0 (by omega)).trans hp)
      (by simpa using (hwstk 1 (by omega)).trans hp1) hf hl (hsub _ href)
      (ih (p' := p' + 2) (fun idx hi => by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hwstk (idx + 2) (by omega))
        (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hw0))

theorem fullWatchSlice_append_large {F_cur : List (List Nat)} {k k' : FullCoreState}
    {lit p p' rem : Nat} {w0 cref : BitVec 32} (hvars : k.cur_vars ≤ k'.cur_vars)
    (hsub : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k')
    (hwstk : ∀ idx < rem, k'.wstk[p' + idx]? = k.wstk[p + idx]?)
    (h : WatchSliceOk F_cur k lit p rem)
    (hw0 : k'.wstk[p' + rem]? = some w0) (hw1 : k'.wstk[p' + rem + 1]? = some cref)
    (hflag : (w0 &&& 0x80000000#32) = 0#32) (hlt : cref.toNat < 0x80000000)
    (href : cref.toNat ∈ fullArenaClauseRefsCore k') :
    WatchSliceOk F_cur k' lit p' (rem + 2) := by
  induction h generalizing p' with
  | empty => exact .large (by simpa using hw0) (by simpa using hw1) hflag hlt href .empty
  | @bin p rem w hp hf hn hl he _ ih =>
    exact .bin (by simpa using (hwstk 0 (by omega)).trans hp) hf hn (by omega) he
      (ih (p' := p' + 1) (fun idx hi => by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hwstk (idx + 1) (by omega))
        (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hw0)
        (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hw1))
  | @large p rem w cr hp hp1 hf hl hr _ ih =>
    exact .large (by simpa using (hwstk 0 (by omega)).trans hp)
      (by simpa using (hwstk 1 (by omega)).trans hp1) hf hl (hsub _ hr)
      (ih (p' := p' + 2) (fun idx hi => by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hwstk (idx + 2) (by omega))
        (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hw0)
        (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hw1))

theorem DenseWatchSliceOk.append_bin {F_cur : List (List Nat)} {k k' : FullCoreState}
    {lit p p' rem : Nat} {w0 : BitVec 32} (hvars : k.cur_vars ≤ k'.cur_vars)
    (hsub : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k')
    (hwstk : ∀ idx < rem, k'.wstk[p' + idx]? = k.wstk[p + idx]?)
    (h : DenseWatchSliceOk F_cur k lit p rem) (hw0 : k'.wstk[p' + rem]? = some w0)
    (hflag : (w0 &&& 0x80000000#32) ≠ 0#32) (hne : w0 ≠ 0xFFFFFFFF#32)
    (hlt : (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k'.cur_vars)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [lit, (w0 &&& 0x7FFFFFFF#32).toNat])) :
    DenseWatchSliceOk F_cur k' lit p' (rem + 1) := by
  induction h generalizing p' with
  | empty => exact .bin (by simpa using hw0) hflag hne hlt hent .empty
  | @bin p rem w hp hf hn hl he _ ih =>
    exact .bin (by simpa using (hwstk 0 (by omega)).trans hp) hf hn (by omega) he
      (ih (p' := p' + 1) (fun idx hi => by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hwstk (idx + 1) (by omega))
        (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hw0))
  | @occ p rem w cref hp hp1 hf hsz hl href _ ih =>
    exact .occ (by simpa using (hwstk 0 (by omega)).trans hp)
      (by simpa using (hwstk 1 (by omega)).trans hp1) hf hsz hl (hsub _ href)
      (ih (p' := p' + 2) (fun idx hi => by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hwstk (idx + 2) (by omega))
        (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hw0))

theorem DenseWatchSliceOk.append_occ {F_cur : List (List Nat)} {k k' : FullCoreState}
    {lit p p' rem : Nat} {w0 cref : BitVec 32} (hvars : k.cur_vars ≤ k'.cur_vars)
    (hsub : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k')
    (hwstk : ∀ idx < rem, k'.wstk[p' + idx]? = k.wstk[p + idx]?)
    (h : DenseWatchSliceOk F_cur k lit p rem)
    (hw0 : k'.wstk[p' + rem]? = some w0) (hw1 : k'.wstk[p' + rem + 1]? = some cref)
    (hflag : (w0 &&& 0x80000000#32) = 0#32) (hsz : 3 ≤ w0.toNat) (hlt : cref.toNat < 0x80000000)
    (href : cref.toNat ∈ fullArenaClauseRefsCore k') :
    DenseWatchSliceOk F_cur k' lit p' (rem + 2) := by
  induction h generalizing p' with
  | empty => exact .occ (by simpa using hw0) (by simpa using hw1) hflag hsz hlt href .empty
  | @bin p rem w hp hf hn hl he _ ih =>
    exact .bin (by simpa using (hwstk 0 (by omega)).trans hp) hf hn (by omega) he
      (ih (p' := p' + 1) (fun idx hi => by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hwstk (idx + 1) (by omega))
        (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hw0)
        (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hw1))
  | @occ p rem w cr hp hp1 hf hsz0 hl hr _ ih =>
    exact .occ (by simpa using (hwstk 0 (by omega)).trans hp)
      (by simpa using (hwstk 1 (by omega)).trans hp1) hf hsz0 hl (hsub _ hr)
      (ih (p' := p' + 2) (fun idx hi => by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hwstk (idx + 2) (by omega))
        (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hw0)
        (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hw1))

/-- Verbatim slice-preserving defragmentation preserves `ModeWatchesInv` across both sparse
and dense modes. -/
theorem fullWstackDefrag_preserves_modeWatchesInv {F_cur : List (List Nat)}
    {k k' : FullCoreState} (hw : ModeWatchesInv F_cur k) (hlay : WatchStackLayout k')
    (hvars : k'.cur_vars = k.cur_vars) (hdm : k'.dense_mode = k.dense_mode)
    (hsub : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k')
    (hpres : ∀ l < 2 * k.cur_vars, fullWatchSizeCore k' l = fullWatchSizeCore k l ∧
      ∀ idx < fullWatchSizeCore k l,
        k'.wstk[fullWatchOffCore k' l + idx]? = k.wstk[fullWatchOffCore k l + idx]?) :
    ModeWatchesInv F_cur k' := by
  have hrefl : (cnfOfClauses F_cur).Entails (cnfOfClauses F_cur) := by
    rw [CNF.entails_def]; exact fun _ h => h
  unfold ModeWatchesInv at hw ⊢; rw [hdm]
  by_cases hc : k.dense_mode = 0#64 <;> simp only [hc, ↓reduceIte] at hw ⊢
  · refine ⟨hlay, fun l hl => ?_⟩
    obtain ⟨hsz, hslice⟩ := hpres l (hvars ▸ hl); rw [hsz]
    exact fullWatchSlice_relocate hrefl (by omega) hsub hslice (hw.slices l (hvars ▸ hl))
  · refine ⟨hlay, fun l hl => ?_⟩
    obtain ⟨hsz, hslice⟩ := hpres l (hvars ▸ hl); rw [hsz]
    exact (hw.slices l (hvars ▸ hl)).relocate hrefl (by omega) hsub hslice

/-- Exact-append watch push preserves `ModeWatchesInv` across both sparse and dense modes. -/
theorem fullWatchPush_preserves_modeWatchesInv {F_cur : List (List Nat)}
    {k k' : FullCoreState} {lit w0 w1 cnt : BitVec 32} {ok : Bool}
    (hw : ModeWatchesInv F_cur k) (hlay : WatchStackLayout k')
    (hvars : k'.cur_vars = k.cur_vars) (hdm : k'.dense_mode = k.dense_mode)
    (hsub : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k')
    (hbin : cnt.toNat = 1 →
      (w0 &&& 0x80000000#32) ≠ 0#32 ∧ w0 ≠ 0xFFFFFFFF#32 ∧
      (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k'.cur_vars ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause [lit.toNat, (w0 &&& 0x7FFFFFFF#32).toNat]))
    (hlarge : cnt.toNat = 2 →
      (w0 &&& 0x80000000#32) = 0#32 ∧ (k.dense_mode ≠ 0#64 → 3 ≤ w0.toNat) ∧
      w1.toNat < 0x80000000 ∧ w1.toNat ∈ fullArenaClauseRefsCore k')
    (hother : ∀ l < 2 * k.cur_vars, l ≠ lit.toNat →
      fullWatchSizeCore k' l = fullWatchSizeCore k l ∧
      ∀ idx < fullWatchSizeCore k l,
        k'.wstk[fullWatchOffCore k' l + idx]? = k.wstk[fullWatchOffCore k l + idx]?)
    (hok_true : ok = true →
      lit.toNat < 2 * k.cur_vars ∧ (cnt.toNat = 1 ∨ cnt.toNat = 2) ∧
      fullWatchSizeCore k' lit.toNat = fullWatchSizeCore k lit.toNat + cnt.toNat ∧
      (∀ idx < fullWatchSizeCore k lit.toNat,
        k'.wstk[fullWatchOffCore k' lit.toNat + idx]? =
          k.wstk[fullWatchOffCore k lit.toNat + idx]?) ∧
      k'.wstk[fullWatchOffCore k' lit.toNat + fullWatchSizeCore k lit.toNat]? = some w0 ∧
      (cnt.toNat = 2 →
        k'.wstk[fullWatchOffCore k' lit.toNat + fullWatchSizeCore k lit.toNat + 1]? = some w1))
    (hok_false : ok = false → lit.toNat < 2 * k.cur_vars →
      fullWatchSizeCore k' lit.toNat = fullWatchSizeCore k lit.toNat ∧
      ∀ idx < fullWatchSizeCore k lit.toNat,
        k'.wstk[fullWatchOffCore k' lit.toNat + idx]? =
          k.wstk[fullWatchOffCore k lit.toNat + idx]?) :
    ModeWatchesInv F_cur k' := by
  have hrefl : (cnfOfClauses F_cur).Entails (cnfOfClauses F_cur) := by
    rw [CNF.entails_def]; exact fun _ h => h
  unfold ModeWatchesInv at hw ⊢; rw [hdm]
  by_cases hc : k.dense_mode = 0#64 <;> simp only [hc, ↓reduceIte] at hw ⊢
  · refine ⟨hlay, fun l hl => ?_⟩
    by_cases hle : l = lit.toNat
    · subst hle; cases ok with
      | false =>
        obtain ⟨hsz, hslice⟩ := hok_false rfl (hvars ▸ hl); rw [hsz]
        exact fullWatchSlice_relocate hrefl (by omega) hsub hslice (hw.slices _ (hvars ▸ hl))
      | true =>
        obtain ⟨_, hcnt, hsz, hpre, hw0, hw1⟩ := hok_true rfl; rw [hsz]
        rcases hcnt with hc1 | hc2
        · rw [hc1]; obtain ⟨hf, hn, hlt, hent⟩ := hbin hc1
          exact fullWatchSlice_append_bin (by omega) hsub hpre (hw.slices _ (hvars ▸ hl))
            hw0 hf hn hlt hent
        · rw [hc2]; obtain ⟨hf, _, hlt, href⟩ := hlarge hc2
          exact fullWatchSlice_append_large (by omega) hsub hpre (hw.slices _ (hvars ▸ hl))
            hw0 (hw1 hc2) hf hlt href
    · obtain ⟨hsz, hslice⟩ := hother l (hvars ▸ hl) hle; rw [hsz]
      exact fullWatchSlice_relocate hrefl (by omega) hsub hslice (hw.slices l (hvars ▸ hl))
  · refine ⟨hlay, fun l hl => ?_⟩
    by_cases hle : l = lit.toNat
    · subst hle; cases ok with
      | false =>
        obtain ⟨hsz, hslice⟩ := hok_false rfl (hvars ▸ hl); rw [hsz]
        exact (hw.slices _ (hvars ▸ hl)).relocate hrefl (by omega) hsub hslice
      | true =>
        obtain ⟨_, hcnt, hsz, hpre, hw0, hw1⟩ := hok_true rfl; rw [hsz]
        rcases hcnt with hc1 | hc2
        · rw [hc1]; obtain ⟨hf, hn, hlt, hent⟩ := hbin hc1
          exact (hw.slices _ (hvars ▸ hl)).append_bin (by omega) hsub hpre hw0 hf hn hlt hent
        · rw [hc2]; obtain ⟨hf, h3, hlt, href⟩ := hlarge hc2
          exact (hw.slices _ (hvars ▸ hl)).append_occ (by omega) hsub hpre hw0 (hw1 hc2)
            hf (h3 hc) hlt href
    · obtain ⟨hsz, hslice⟩ := hother l (hvars ▸ hl) hle; rw [hsz]
      exact (hw.slices l (hvars ▸ hl)).relocate hrefl (by omega) hsub hslice

/-- Core wrapper for `full_add_unit` at level 0 (`cur_level = 0`, `alvl = 0`, unassigned `lit`). -/
theorem addUnit_preserves_fullCore {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hinv : FullCoreInv c F0 s) (hcl0 : s.core.cur_level = 0) {lit : BitVec 32}
    {flags' : List (BitVec 32)} {unassigned' unflushed' : BitVec 64} {scratch' : FullScratch}
    (hsok' : scratch'.LengthsOk c) (hfll : flags'.length = c.max_vars)
    (hlit : lit.toNat < 2 * s.core.cur_vars)
    (hun : s.core.vals[lit.toNat]?.getD 0#8 = 0#8)
    (hl0 : ∀ F_cur, FullWitnessInv c F0 F_cur s.core →
      (cnfOfClauses F_cur).EntailsClause (cnfClause [lit.toNat])) :
    let v := lit.toNat / 2
    let s' : FullState :=
      { s with
        core :=
          { s.core with
            vals := (s.core.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8
            flags := flags', lvl := s.core.lvl.set v 0#32
            rsns := s.core.rsns.set v 0xFFFFFFFF#32, trl := s.core.trl.set s.core.trail_end lit
            trail_pos := s.core.trail_pos.set v (BitVec.ofNat 32 s.core.trail_end)
            trail_end := s.core.trail_end + 1
            unassigned := unassigned', unflushed := unflushed' }
        scratch := scratch' }
    FullCoreInv c F0 s' := by
  obtain ⟨F_cur, hw⟩ := hinv.witness
  have hft0 : (s.core.frame_trail[0]?.getD 0#32).toNat ≤ s.core.trail_end :=
    hw.frame_trail_lt 0 (by omega)
  have hcl := hinv.lengths.core_ok
  simpa [hcl0] using chronoAssign_preserves_fullCore (c := c) (F0 := F0) (s := s) hinv
    (lit := lit) (rsn := 0xFFFFFFFF#32) (alvl := 0) (cur_level' := 0)
    (propagated' := s.core.propagated) (flags' := flags')
    (frame_trail' := s.core.frame_trail) (frame_dec' := s.core.frame_dec)
    (unassigned' := unassigned') (unflushed' := unflushed') (scratch' := scratch')
    hsok' hfll hcl.frame_trail_len hcl.frame_dec_len hlit hun (Nat.le_refl 0)
    (by have := hcl.propagated_le; omega) (Nat.zero_le _)
    (fun L hL => by have hLz : L = 0 := (by omega); rw [hLz]; omega)
    (fun L1 L2 h1 h2 => by
      have h1z : L1 = 0 := (by omega); have h2z : L2 = 0 := (by omega)
      rw [h1z, h2z]; exact Nat.le_refl _)
    (fun L hL1 hL2 => by omega) (fun L hL1 hL2 => by omega)
    (fun i hi => by have := hw.lvl_le i hi; omega) (fun L hL1 hL2 => by omega)
    (fun h0 => by omega) (fun _ => hl0) (fun h0 => by omega) (fun h0 => by omega)

/-- Witness-level wrapper for watch-stack updates (`full_add_bin`, `full_delete_bin_side`,
`full_delete_binary`, `full_unwatch_large`). -/
theorem watchUpdate_preserves_witness {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k)
    {wvec' wstk' : List (BitVec 32)} {wlen' : Nat} {wusable' nb' oom' : BitVec 64}
    (hwat : ModeWatchesInv F_cur
      { k with wvec := wvec', wstk := wstk', wlen := wlen',
               wusable := wusable', num_binary := nb', oom := oom' }) :
    FullWitnessInv c F0 F_cur
      { k with wvec := wvec', wstk := wstk', wlen := wlen',
               wusable := wusable', num_binary := nb', oom := oom' } :=
  { hw with arena := { hw.arena with len_ok := hw.arena.len_ok }, watches := hwat }

/-- Core wrapper for `full_add_bin` / `full_delete_bin_side` / `full_delete_binary`: updating only
watch-stack fields (`wvec`, `wstk`, `wlen`, `wusable`, `num_binary`, `oom`, `scratch`) while
preserving `ModeWatchesInv` preserves `FullCoreInv` verbatim. -/
theorem watchUpdate_preserves_fullCore {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hinv : FullCoreInv c F0 s) {wvec' wstk' : List (BitVec 32)} {wlen' : Nat}
    {wusable' nb' oom' : BitVec 64} {scratch' : FullScratch}
    (hwvl : wvec'.length = 4 * c.max_vars) (hwsl : wstk'.length = c.wcap)
    (hwle : wlen' ≤ c.wcap) (hsok' : scratch'.LengthsOk c)
    (hwat : ∀ F_cur, FullWitnessInv c F0 F_cur s.core →
      ModeWatchesInv F_cur
        { s.core with wvec := wvec', wstk := wstk', wlen := wlen',
                      wusable := wusable', num_binary := nb', oom := oom' }) :
    FullCoreInv c F0
      { s with
        core := { s.core with wvec := wvec', wstk := wstk', wlen := wlen',
                              wusable := wusable', num_binary := nb', oom := oom' }
        scratch := scratch' } := by
  obtain ⟨F_cur, hw⟩ := hinv.witness
  exact ⟨⟨{ hinv.lengths.core_ok with
      wvec_len := hwvl, wstk_len_arr := hwsl, wlen_le := hwle }, hsok'⟩,
    F_cur, watchUpdate_preserves_witness hw (hwat F_cur hw)⟩

/-- Deleting one binary watch (or subset of entries) from `lit`'s watch slice preserves
`FullCoreInv` across both sparse and dense modes (`full_delete_bin_side`, `full_delete_binary`,
`full_unwatch_large`). -/
theorem deleteBin_preserves_fullCore {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hinv : FullCoreInv c F0 s) {lit : Nat}
    {wvec' wstk' : List (BitVec 32)} {wlen' : Nat} {wusable' nb' : BitVec 64}
    {scratch' : FullScratch}
    (hwvl : wvec'.length = 4 * c.max_vars) (hwsl : wstk'.length = c.wcap)
    (hwle : wlen' ≤ c.wcap) (hsok' : scratch'.LengthsOk c)
    (hlay : WatchStackLayout
      { s.core with wvec := wvec', wstk := wstk', wlen := wlen',
                    wusable := wusable', num_binary := nb' })
    (hother : ∀ l < 2 * s.core.cur_vars, l ≠ lit →
      fullWatchSizeCore { s.core with wvec := wvec' } l = fullWatchSizeCore s.core l ∧
      ∀ idx < fullWatchSizeCore s.core l,
        wstk'[fullWatchOffCore { s.core with wvec := wvec' } l + idx]? =
          s.core.wstk[fullWatchOffCore s.core l + idx]?)
    (hlit_ok : ∀ F_cur, FullWitnessInv c F0 F_cur s.core → lit < 2 * s.core.cur_vars →
      let k' := { s.core with wvec := wvec', wstk := wstk', wlen := wlen',
                              wusable := wusable', num_binary := nb' }
      if s.core.dense_mode = 0#64 then
        WatchSliceOk F_cur k' lit (fullWatchOffCore k' lit) (fullWatchSizeCore k' lit)
      else
        DenseWatchSliceOk F_cur k' lit (fullWatchOffCore k' lit) (fullWatchSizeCore k' lit)) :
    FullCoreInv c F0
      { s with
        core := { s.core with wvec := wvec', wstk := wstk', wlen := wlen',
                              wusable := wusable', num_binary := nb' }
        scratch := scratch' } := by
  refine watchUpdate_preserves_fullCore hinv hwvl hwsl hwle hsok' (oom' := s.core.oom) ?_
  intro F_cur hw
  have hrefl : (cnfOfClauses F_cur).Entails (cnfOfClauses F_cur) := by
    rw [CNF.entails_def]; exact fun _ h => h
  have hwm := hw.watches
  let k' : FullCoreState :=
    { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wusable',
                  num_binary := nb' }
  change ModeWatchesInv F_cur k'
  unfold ModeWatchesInv at hwm ⊢
  by_cases hc : s.core.dense_mode = 0#64
  · simp only [hc, ↓reduceIte] at hwm
    have hc' : k'.dense_mode = 0#64 := hc
    simp only [hc', ↓reduceIte]
    refine ⟨hlay, fun l hl => ?_⟩
    by_cases hle : l = lit
    · subst hle; have h0 := hlit_ok F_cur hw hl
      split at h0; · exact h0
      · exact absurd hc ‹_›
    · obtain ⟨hsz, hslice⟩ := hother l hl hle
      have hsz' : fullWatchSizeCore k' l = fullWatchSizeCore s.core l := hsz
      rw [hsz']
      exact fullWatchSlice_relocate (k := s.core) (k' := k') hrefl (Nat.le_refl _)
        (fun _ hr => hr) hslice (hwm.slices l hl)
  · simp only [hc, ↓reduceIte] at hwm
    have hc' : ¬ k'.dense_mode = 0#64 := hc
    simp only [hc', ↓reduceIte]
    refine ⟨hlay, fun l hl => ?_⟩
    by_cases hle : l = lit
    · subst hle; have h0 := hlit_ok F_cur hw hl
      split at h0; · exact absurd ‹_› hc
      · exact h0
    · obtain ⟨hsz, hslice⟩ := hother l hl hle
      have hsz' : fullWatchSizeCore k' l = fullWatchSizeCore s.core l := hsz
      rw [hsz']
      exact DenseWatchSliceOk.relocate (k := s.core) (k' := k') hrefl (Nat.le_refl _)
        (fun _ hr => hr) hslice (hwm.slices l hl)

/-- Core wrapper for `full_add_bin`: adding watches for an entailed binary clause `[a, b]`
preserves `FullCoreInv` across both sparse and dense modes. -/
abbrev addBin_preserves_fullCore := @watchUpdate_preserves_fullCore

/-! ## 3. Arena shrink (`PH_SHRK`), garbage append, and swap helpers -/

private theorem bit23_or_shrk (x : BitVec 32) :
    ((x ||| 0x00800000#32) &&& 0x00800000#32) ≠ 0#32 := by
  intro h; have := congrArg (·[23]) h; simp at this

private theorem bit19_or_shrk (x : BitVec 32) :
    ((x ||| 0x00800000#32) &&& 0x00080000#32) = (x &&& 0x00080000#32) := by
  ext i hi; simp only [BitVec.getElem_and, BitVec.getElem_or]
  have h19 : (0x00080000#32)[i] = true → (0x00800000#32)[i] = false := by
    revert i hi; decide
  cases h : (0x00080000#32)[i]
  · simp
  · simp [h19 h]

theorem fullArenaSkipShrk_of_first_sentinel {ar : List (BitVec 32)} {alen t : Nat} :
    ∀ {fuel p : Nat}, p ≤ t → t < alen → ar[t]? = some 0xFFFFFFFF#32 →
      (∀ i, p ≤ i → i < t → ar[i]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32) →
      t - p + 1 ≤ fuel → fullArenaSkipShrk ar alen p fuel = t + 1
  | 0, _, _, _, _, _, hf => by omega
  | fuel + 1, p, hpt, hta, hsent, hne_lt, hf => by
    have hpa : p < alen := by omega
    unfold fullArenaSkipShrk; simp only [hpa, ↓reduceIte]
    by_cases hpeq : p = t
    · subst p; simp [hsent]
    · have hne : ar[p]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := hne_lt p (Nat.le_refl p) (by omega)
      simp only [hne, ne_eq, not_false_eq_true, ↓reduceIte]
      exact fullArenaSkipShrk_of_first_sentinel (by omega) hta hsent
        (fun i hi1 hi2 => hne_lt i (by omega) hi2) (by omega)

theorem fullArenaSkipShrk_first_sentinel {ar : List (BitVec 32)} {alen t : Nat} :
    ∀ {fuel p : Nat}, p ≤ t → t < alen → ar[t]? = some 0xFFFFFFFF#32 → t - p + 1 ≤ fuel →
      ∃ t0, p ≤ t0 ∧ t0 ≤ t ∧ fullArenaSkipShrk ar alen p fuel = t0 + 1 ∧
        ar[t0]? = some 0xFFFFFFFF#32 ∧
        (∀ i, p ≤ i → i < t0 → ar[i]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32)
  | 0, _, _, _, _, hf => by omega
  | fuel + 1, p, hpt, hta, hsent, hf => by
    have hpa : p < alen := by omega
    unfold fullArenaSkipShrk; simp only [hpa, ↓reduceIte]; split
    · rename_i hne
      have hp_ne : p ≠ t := by rintro rfl; simp [hsent] at hne
      obtain ⟨t0, h1, h2, h3, h4, h5⟩ := fullArenaSkipShrk_first_sentinel (ar := ar) (alen := alen)
        (t := t) (fuel := fuel) (p := p + 1) (by omega) hta hsent (by omega)
      refine ⟨t0, by omega, h2, h3, h4, fun i hi1 hi2 => ?_⟩
      by_cases hip : i = p
      · subst i; exact hne
      · exact h5 i (by omega) hi2
    · rename_i heq
      have heqv : ar[p]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 :=
        Classical.byContradiction fun hn => heq hn
      have hlen_t : t < ar.length := (List.getElem?_eq_some_iff.mp hsent).1
      have hp_some : ar[p]? = some (ar[p]'(by omega)) := List.getElem?_eq_getElem (by omega)
      rw [hp_some, Option.getD_some] at heqv
      exact ⟨p, Nat.le_refl p, hpt, rfl, by rw [hp_some, heqv], fun _ h1 h2 => by omega⟩

/-- Shrinking live arena clause `cref` in place (`3 ≤ nsz < old_sz`) by updating `ar[cref + 1]`,
`ar[cref + 2] := nsz`, literals `[cref + 3 ..< cref + 3 + nsz)`, and (when `PH_SHRK` was clear)
setting `PH_SHRK` on `ar[cref]` + sentinel `0xFFFFFFFF#32` at `cref + 3 + old_sz - 1` preserves
`fullArenaNextOff`, `fullArenaClauseRefsCore`, and `FullArenaClausesInv` (`full_otfs_large`,
`full_viv_simplify`, `full_viv_commit`, `full_subst_rewrite_ar`, `full_fwd_check_cl`). -/
theorem inPlaceShrink_preserves_arena {c : FullCfg} {F_cur : List (List Nat)}
    {k : FullCoreState} {arena' : List (BitVec 32)} {cref nsz : Nat}
    (ha : FullArenaClausesInv c F_cur k) (hlen : k.LengthsOk c)
    (hcref : cref ∈ fullArenaClauseRefsCore k) (hng : fullArenaClauseGarbCore k cref = false)
    (hnsz3 : 3 ≤ nsz) (hnsz_lt : nsz < fullArenaClauseSizeCore k cref)
    (har_len' : arena'.length = c.arena_cap)
    (hhdr' : arena'[cref]? = some
      (if (fullArenaHdrCore k cref &&& 0x00800000#32) = 0#32 then
        fullArenaHdrCore k cref ||| 0x00800000#32
      else fullArenaHdrCore k cref))
    (hsz' : arena'[cref + 2]? = some (BitVec.ofNat 32 nsz))
    (hpad_old : ∀ j, nsz ≤ j → j < fullArenaClauseSizeCore k cref - 1 →
      arena'[cref + 3 + j]? = k.arena[cref + 3 + j]?)
    (hlast_sent : (fullArenaHdrCore k cref &&& 0x00800000#32) = 0#32 →
      arena'[cref + 3 + fullArenaClauseSizeCore k cref - 1]? = some 0xFFFFFFFF#32)
    (hlast_keep : (fullArenaHdrCore k cref &&& 0x00800000#32) ≠ 0#32 →
      arena'[cref + 3 + fullArenaClauseSizeCore k cref - 1]? =
        k.arena[cref + 3 + fullArenaClauseSizeCore k cref - 1]?)
    (hout : ∀ i, i < cref ∨ cref + 3 + fullArenaClauseSizeCore k cref ≤ i →
      arena'[i]? = k.arena[i]?)
    (hlits_lt' : ∀ l ∈ fullArenaClauseLitsCore { k with arena := arena' } cref,
      l < 2 * k.cur_vars)
    (hent' : (cnfOfClauses F_cur).EntailsClause
      (cnfClause (fullArenaClauseLitsCore { k with arena := arena' } cref))) :
    let k' := { k with arena := arena' }
    fullArenaClauseRefsCore k' = fullArenaClauseRefsCore k ∧
    (∀ r ∈ fullArenaClauseRefsCore k, r ≠ cref →
      fullArenaClauseSizeCore k' r = fullArenaClauseSizeCore k r ∧
      fullArenaClauseGarbCore k' r = fullArenaClauseGarbCore k r ∧
      fullArenaClauseLitsCore k' r = fullArenaClauseLitsCore k r) ∧
    fullArenaClauseSizeCore k' cref = nsz ∧
    fullArenaClauseGarbCore k' cref = false ∧
    FullArenaClausesInv c F_cur k' := by
  intro k'
  let old_sz := fullArenaClauseSizeCore k cref
  have hwf := ha.refs_wf cref hcref
  have hal_len : k.arena_len ≤ k.arena.length := by
    have := hlen.arena_len_le; have := hlen.arena_len_arr; omega
  have hnsz_lt32 : nsz < 2 ^ 32 := by
    have := (k.arena[cref + 2]?.getD 0#32).isLt; unfold fullArenaClauseSizeCore at hnsz_lt; omega
  have hsz_cref' : fullArenaClauseSizeCore k' cref = nsz := by
    unfold fullArenaClauseSizeCore k'; rw [hsz', Option.getD_some, bv32_ofNat_toNat hnsz_lt32]
  have hold_lit_ne :
      ∀ j, j < old_sz → k.arena[cref + 3 + j]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := by
    intro j hj
    have hbd : cref + 3 + old_sz ≤ k.arena.length := by omega
    have hlt_j : cref + 3 + j < k.arena.length := by omega
    rw [List.getElem?_eq_getElem hlt_j, Option.getD_some]
    have hmem : (k.arena[cref + 3 + j]'hlt_j).toNat ∈ fullArenaClauseLitsCore k cref :=
      (mem_fullArenaClauseLitsCore_iff hbd).mpr ⟨j, hj, rfl⟩
    have hlt_v := ha.lits_lt cref hcref hng _ hmem
    have hmx := c.hmaxv; have hcv := hlen.cur_vars_le; unfold dimacsBound at hmx
    intro heq; rw [heq] at hlt_v; simp at hlt_v; omega
  have hcref_shrk' : (fullArenaHdrCore k' cref &&& 0x00800000#32) ≠ 0#32 := by
    unfold fullArenaHdrCore k'; rw [hhdr', Option.getD_some]
    split; · exact bit23_or_shrk _
    · rename_i h; exact h
  have hcref_garb' : fullArenaClauseGarbCore k' cref = false := by
    unfold fullArenaClauseGarbCore fullArenaHdrCore at hng ⊢; dsimp only [k']
    rw [hhdr', Option.getD_some]; split
    · rw [bit19_or_shrk]; exact hng
    · exact hng
  have hcref_nxt :
      fullArenaNextOff arena' k.arena_len cref = fullArenaNextOff k.arena k.arena_len cref := by
    have h1 : ¬ (cref + 3 > k.arena_len) := by omega
    have h2 : ¬ (cref + 3 + old_sz > k.arena_len) := by omega
    have h2' : ¬ (cref + 3 + nsz > k.arena_len) := by omega
    have hsz'_n : (arena'[cref + 2]?.getD 0#32).toNat = nsz := hsz_cref'
    have hsh' : (arena'[cref]?.getD 0#32 &&& 0x00800000#32) ≠ 0#32 := hcref_shrk'
    unfold fullArenaNextOff
    simp only [h1, ↓reduceIte, hsz'_n, h2', hsh', ne_eq, not_false_eq_true]
    have hsz_old_eq : (k.arena[cref + 2]?.getD 0#32).toNat = old_sz := rfl
    rw [hsz_old_eq]; simp only [h2, ↓reduceIte]
    by_cases hsh0 : (k.arena[cref]?.getD 0#32 &&& 0x00800000#32) = 0#32
    · simp only [hsh0, not_true_eq_false, ↓reduceIte]
      have hsent := hlast_sent hsh0
      have hts := fullArenaSkipShrk_of_first_sentinel (ar := arena') (alen := k.arena_len)
        (t := cref + 3 + old_sz - 1) (fuel := k.arena_len - (cref + 3 + nsz)) (p := cref + 3 + nsz)
        (by omega) (by omega) hsent (fun i hi1 hi2 => by
          have hj : i = cref + 3 + (i - (cref + 3)) := by omega
          rw [hj, hpad_old (i - (cref + 3)) (by omega) (by omega)]
          exact hold_lit_ne (i - (cref + 3)) (by omega)) (by omega)
      omega
    · simp only [hsh0, not_false_eq_true, ↓reduceIte]
      obtain ⟨t, ht1, ht2, hsent⟩ := ha.shrk_term cref hcref hsh0
      obtain ⟨t0, ht0_lo, ht0_hi, ht0_nxt, ht0_sent, ht0_first⟩ :=
        fullArenaSkipShrk_first_sentinel (ar := k.arena) (alen := k.arena_len) (t := t)
          (fuel := k.arena_len - (cref + 3 + old_sz)) (p := cref + 3 + old_sz) ht1 ht2 hsent
          (by omega)
      rw [ht0_nxt]
      refine fullArenaSkipShrk_of_first_sentinel (ar := arena') (alen := k.arena_len) (t := t0)
        (fuel := k.arena_len - (cref + 3 + nsz)) (p := cref + 3 + nsz) (by omega) (by omega)
        (by rw [hout t0 (Or.inr ht0_lo)]; exact ht0_sent) (fun i hi1 hi2 => ?_) (by omega)
      by_cases hmid : i < cref + 3 + old_sz
      · by_cases hlast : i = cref + 3 + old_sz - 1
        · rw [hlast, hlast_keep hsh0]
          have heq : cref + 3 + fullArenaClauseSizeCore k cref - 1 = cref + 3 + (old_sz - 1) := by
            dsimp only [old_sz]; omega
          rw [heq]; exact hold_lit_ne (old_sz - 1) (by dsimp only [old_sz]; omega)
        · have hj : i = cref + 3 + (i - (cref + 3)) := by omega
          rw [hj, hpad_old (i - (cref + 3)) (by omega) (by omega)]
          exact hold_lit_ne (i - (cref + 3)) (by omega)
      · rw [hout i (Or.inr (by omega))]; exact ht0_first i (by omega) hi2
  have hout_ref : ∀ r ∈ fullArenaClauseRefsCore k, r ≠ cref →
      (r + 3 + fullArenaClauseSizeCore k r ≤ cref ∧ fullArenaNextOff k.arena k.arena_len r ≤ cref) ∨
      cref + 3 + old_sz ≤ r := by
    intro r hr hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · exact Or.inl ⟨ha.disjoint hr hcref hlt, fullArenaScanRefs_disjoint hr hcref hlt⟩
    · exact Or.inr (ha.disjoint hcref hr hgt)
  have hnxt : ∀ r ∈ fullArenaClauseRefsCore k,
      fullArenaNextOff arena' k.arena_len r = fullArenaNextOff k.arena k.arena_len r := by
    intro r hr
    by_cases hrc : r = cref
    · subst r; exact hcref_nxt
    · rcases hout_ref r hr hrc with ⟨hlt, hnl⟩ | hgt
      · have hr3 := (ha.refs_wf r hr).2.1
        exact fullArenaNextOff_congr_block (hout r (Or.inl (by omega)))
          (hout (r + 2) (Or.inl (by omega))) fun i _ hi2 => hout i (Or.inl (by omega))
      · exact fullArenaNextOff_congr_block (hout r (Or.inr hgt))
          (hout (r + 2) (Or.inr (by omega))) fun i _ _ => hout i (Or.inr (by omega))
  have hrefs : fullArenaClauseRefsCore k' = fullArenaClauseRefsCore k :=
    fullArenaClauseRefsCore_congr rfl hnxt
  have hother : ∀ r ∈ fullArenaClauseRefsCore k, r ≠ cref →
      fullArenaClauseSizeCore k' r = fullArenaClauseSizeCore k r ∧
      fullArenaClauseGarbCore k' r = fullArenaClauseGarbCore k r ∧
      fullArenaClauseLitsCore k' r = fullArenaClauseLitsCore k r := by
    intro r hr hne
    have hrwf := ha.refs_wf r hr
    rcases hout_ref r hr hne with ⟨hlt, _⟩ | hgt
    · have hszr : fullArenaClauseSizeCore k' r = fullArenaClauseSizeCore k r := by
        unfold fullArenaClauseSizeCore k'; rw [hout (r + 2) (Or.inl (by omega))]
      have hgar : fullArenaClauseGarbCore k' r = fullArenaClauseGarbCore k r := by
        unfold fullArenaClauseGarbCore fullArenaHdrCore k'; rw [hout r (Or.inl (by omega))]
      refine ⟨hszr, hgar, fullArenaClauseLitsCore_eq_of_hold (by omega)
        (by dsimp only [k']; rw [har_len']; have := hlen.arena_len_le; omega) hszr
        fun j hj => hout (r + 3 + j) (Or.inl (by omega))⟩
    · have hszr : fullArenaClauseSizeCore k' r = fullArenaClauseSizeCore k r := by
        unfold fullArenaClauseSizeCore k'; rw [hout (r + 2) (Or.inr (by omega))]
      have hgar : fullArenaClauseGarbCore k' r = fullArenaClauseGarbCore k r := by
        unfold fullArenaClauseGarbCore fullArenaHdrCore k'; rw [hout r (Or.inr hgt)]
      refine ⟨hszr, hgar, fullArenaClauseLitsCore_eq_of_hold (by omega)
        (by dsimp only [k']; rw [har_len']; have := hlen.arena_len_le; omega) hszr
        fun j hj => hout (r + 3 + j) (Or.inr (by omega))⟩
  refine ⟨hrefs, hother, hsz_cref', hcref_garb', ⟨ha.len_ok, ?_, ?_, ?_, ?_⟩⟩
  · intro r hr; rw [hrefs] at hr; dsimp only [k']; rw [hnxt r hr]
    by_cases hrc : r = cref
    · subst r; rw [hsz_cref']; exact ⟨hwf.1, hnsz3, by omega, hwf.2.2.2.1, hwf.2.2.2.2⟩
    · rw [(hother r hr hrc).1]; exact ha.refs_wf r hr
  · intro r hr hsh; rw [hrefs] at hr
    by_cases hrc : r = cref
    · subst r; rw [hsz_cref']
      by_cases hsh0 : (fullArenaHdrCore k cref &&& 0x00800000#32) = 0#32
      · exact ⟨cref + 3 + old_sz - 1, by dsimp only [old_sz]; omega,
          by dsimp only [k', old_sz]; omega, hlast_sent hsh0⟩
      · obtain ⟨t, ht1, ht2, hsent⟩ := ha.shrk_term cref hr hsh0
        exact ⟨t, by omega, ht2, by rw [hout t (Or.inr ht1)]; exact hsent⟩
    · rcases hout_ref r hr hrc with ⟨hlt, hnl⟩ | hgt
      · have hsh0 : (fullArenaHdrCore k r &&& 0x00800000#32) ≠ 0#32 := by
          unfold fullArenaHdrCore k' at hsh; rwa [hout r (Or.inl (by omega))] at hsh
        obtain ⟨t, ht1, ht2, hsent⟩ := ha.shrk_term r hr hsh0
        obtain ⟨t0, ht0_lo, _, ht0_nxt, ht0_sent⟩ :=
          fullArenaNextOff_hits_sentinel (ha.refs_wf r hr).1 hsh0 ht1 ht2 hsent
        rw [(hother r hr hrc).1]
        exact ⟨t0, ht0_lo, by dsimp only [k']; omega,
          by dsimp only [k']; rw [hout t0 (Or.inl (by omega))]; exact ht0_sent⟩
      · have hsh0 : (fullArenaHdrCore k r &&& 0x00800000#32) ≠ 0#32 := by
          unfold fullArenaHdrCore k' at hsh; rwa [hout r (Or.inr hgt)] at hsh
        obtain ⟨t, ht1, ht2, hsent⟩ := ha.shrk_term r hr hsh0
        rw [(hother r hr hrc).1]
        exact ⟨t, ht1, ht2, by dsimp only [k']; rw [hout t (Or.inr (by omega))]; exact hsent⟩
  · intro r hr hng'; rw [hrefs] at hr
    by_cases hrc : r = cref
    · subst r; exact hlits_lt'
    · rw [(hother r hr hrc).2.1] at hng'; rw [(hother r hr hrc).2.2]
      exact ha.lits_lt r hr hng'
  · intro r hr hng'; rw [hrefs] at hr
    by_cases hrc : r = cref
    · subst r; exact hent'
    · rw [(hother r hr hrc).2.1] at hng'; rw [(hother r hr hrc).2.2]
      exact ha.entails r hr hng'

/-- Appending a garbage-marked clause (`len ≥ 3`, `PH_GARB` set, `PH_SHRK` clear) preserves
`FullCoreInv` and `FullArenaVarsNodup` (used when `full_watch_push` fails in `full_add_clause`
or `full_bve_commit_res`). -/
theorem addGarbageClause_preserves_fullCore {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hinv : FullCoreInv c F0 s) {len : Nat}
    {arena' wvec' wstk' : List (BitVec 32)} {wlen' : Nat}
    {wusable' ag' oom' : BitVec 64} {scratch' : FullScratch}
    (hlen' : ({ s with
      core := { s.core with arena := arena', arena_len := s.core.arena_len + 3 + len,
                            wvec := wvec', wstk := wstk', wlen := wlen', wusable := wusable',
                            arena_garbage := ag', oom := oom' }
      scratch := scratch' } : FullState).LengthsOk c)
    (hge3 : 3 ≤ len)
    (hhold_arena : ∀ i < s.core.arena_len, arena'[i]? = s.core.arena[i]?)
    (hnew_noshrk : (arena'[s.core.arena_len]?.getD 0#32 &&& 0x00800000#32) = 0#32)
    (hnew_garb : (arena'[s.core.arena_len]?.getD 0#32 &&& 0x00080000#32) ≠ 0#32)
    (hnew_sz : (arena'[s.core.arena_len + 2]?.getD 0#32).toNat = len)
    (hwat : ∀ F_cur, FullWitnessInv c F0 F_cur s.core →
      ModeWatchesInv F_cur
        { s.core with arena := arena', arena_len := s.core.arena_len + 3 + len,
                      wvec := wvec', wstk := wstk', wlen := wlen', wusable := wusable',
                      arena_garbage := ag', oom := oom' }) :
    let s' : FullState :=
      { s with
        core := { s.core with arena := arena', arena_len := s.core.arena_len + 3 + len,
                              wvec := wvec', wstk := wstk', wlen := wlen', wusable := wusable',
                              arena_garbage := ag', oom := oom' }
        scratch := scratch' }
    FullCoreInv c F0 s' ∧ fullArenaClauseRefs s' = fullArenaClauseRefs s ++ [s.core.arena_len] ∧
    (FullArenaVarsNodup s → FullArenaVarsNodup s') := by
  intro s'
  obtain ⟨F_cur, hw⟩ := hinv.witness
  have hnxt_hold := hw.arena.arenaNextOff_extend (alen' := s.core.arena_len + 3 + len)
    (by omega) hhold_arena
  have hrefs :
      fullArenaClauseRefsCore s'.core = fullArenaClauseRefsCore s.core ++ [s.core.arena_len] :=
    fullArenaClauseRefsCore_append hw.arena hge3 rfl hhold_arena hnew_noshrk hnew_sz
  have hold_garb : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaClauseGarbCore s'.core r = fullArenaClauseGarbCore s.core r := fun r hr => by
    have := (hw.arena.refs_wf r hr).1
    unfold fullArenaClauseGarbCore fullArenaHdrCore s'; simp [hhold_arena r (by omega)]
  have hold_sz : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaClauseSizeCore s'.core r = fullArenaClauseSizeCore s.core r := fun r hr => by
    have := (hw.arena.refs_wf r hr).1
    unfold fullArenaClauseSizeCore s'; simp [hhold_arena (r + 2) (by omega)]
  have hold_lits : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaClauseLitsCore s'.core r = fullArenaClauseLitsCore s.core r := fun r hr => by
    have hwf := hw.arena.refs_wf r hr
    have h1l := hinv.lengths.core_ok.arena_len_arr; have h1e := hinv.lengths.core_ok.arena_len_le
    have h2l : arena'.length = c.arena_cap := hlen'.core_ok.arena_len_arr
    have h2e : s.core.arena_len + 3 + len ≤ c.arena_cap := hlen'.core_ok.arena_len_le
    have hbd_ar : r + 3 + fullArenaClauseSizeCore s.core r ≤ s.core.arena_len := by omega
    exact fullArenaClauseLitsCore_eq_of_hold (by omega) (by dsimp only [s']; omega)
      (hold_sz r hr) fun j hj => hhold_arena (r + 3 + j) (by omega)
  have hnew_garb_s' : fullArenaClauseGarbCore s'.core s.core.arena_len = true := by
    unfold fullArenaClauseGarbCore fullArenaHdrCore s'; simp [hnew_garb]
  have harena' : FullArenaClausesInv c F_cur s'.core := by
    refine ⟨Or.inr (by dsimp [s']; omega), ?_, ?_, ?_, ?_⟩
    · intro r hr; rw [hrefs, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · have hwf := hw.arena.refs_wf r hr
        rw [hnxt_hold r hr, hold_sz r hr]
        refine ⟨by dsimp [s']; omega, hwf.2.1, hwf.2.2.1, by dsimp [s']; omega, ?_⟩
        rcases hwf.2.2.2.2 with he | h3 <;> right <;> dsimp [s'] <;> omega
      · have hnxt_new : fullArenaNextOff s'.core.arena s'.core.arena_len s.core.arena_len =
            s.core.arena_len + 3 + len := by unfold fullArenaNextOff s'; simp [hnew_sz, hnew_noshrk]
        rw [hnxt_new, show fullArenaClauseSizeCore s'.core s.core.arena_len = len from hnew_sz]
        refine ⟨by dsimp [s']; omega, hge3, by omega, by dsimp [s']; omega, Or.inl (by dsimp [s'])⟩
    · intro r hr hsh; rw [hrefs, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · have hr3 := (hw.arena.refs_wf r hr).1
        have hsh0 : (fullArenaHdrCore s.core r &&& 0x00800000#32) ≠ 0#32 := by
          unfold fullArenaHdrCore at hsh ⊢; dsimp only [s'] at hsh
          rwa [hhold_arena r (by omega)] at hsh
        obtain ⟨t, ht1, ht2, hsent⟩ := hw.arena.shrk_term r hr hsh0
        exact ⟨t, by rw [hold_sz r hr]; exact ht1, by dsimp only [s']; omega,
          by dsimp only [s']; rw [hhold_arena t ht2]; exact hsent⟩
      · unfold fullArenaHdrCore at hsh; dsimp only [s'] at hsh; exact absurd hnew_noshrk hsh
    · intro r hr hng; rw [hrefs, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · rw [hold_garb r hr] at hng; rw [hold_lits r hr]; exact hw.arena.lits_lt r hr hng
      · rw [hnew_garb_s'] at hng; cases hng
    · intro r hr hng; rw [hrefs, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · rw [hold_garb r hr] at hng; rw [hold_lits r hr]; exact hw.arena.entails r hr hng
      · rw [hnew_garb_s'] at hng; cases hng
  refine ⟨⟨hlen', F_cur, { hw with
    arena := harena', watches := hwat F_cur hw
    reason_inv := fun idx hidx hne => by
      have hne0 : s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 ≠
          0xFFFFFFFF#32 := hne
      have hrs := hw.reason_inv idx hidx hne0
      rw [show s'.core.trl = s.core.trl from rfl, show s'.core.rsns = s.core.rsns from rfl,
        show s'.core.cur_vars = s.core.cur_vars from rfl, show s'.core.lvl = s.core.lvl from rfl]
      by_cases hb : (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
          0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32
      · rw [ite_eq_left hb] at hrs ⊢; exact hrs
      · rw [ite_eq_right hb] at hrs ⊢
        exact ⟨hrefs ▸ List.mem_append_left _ hrs.1, (hold_garb _ hrs.1).trans hrs.2.1,
          fun q hq => hrs.2.2 q (hold_lits _ hrs.1 ▸ hq)⟩
    reason_lit_mem := fun idx hidx hne hlg => by
      have hne0 : s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 ≠
          0xFFFFFFFF#32 := hne
      have hlg0 : (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
          0xFFFFFFFF#32 &&& 0x80000000#32) = 0#32 := hlg
      have hrs := hw.reason_inv idx hidx hne0
      have hb : ¬ (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
          0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32 := fun h => absurd hlg0 h
      rw [ite_eq_right hb] at hrs
      rw [show s'.core.trl = s.core.trl from rfl, show s'.core.rsns = s.core.rsns from rfl]
      exact hold_lits _ hrs.1 ▸ hw.reason_lit_mem idx hidx hne0 hlg0 }⟩, hrefs,
    fun hnd r hr hng => ?_⟩
  change r ∈ fullArenaClauseRefsCore s'.core at hr
  rw [hrefs, List.mem_append, List.mem_singleton] at hr
  rcases hr with hr | rfl
  · change fullArenaClauseGarbCore s'.core r = false at hng
    rw [hold_garb r hr] at hng
    unfold fullArenaClauseLits; rw [hold_lits r hr]; exact hnd r hr hng
  · change fullArenaClauseGarbCore s'.core s.core.arena_len = false at hng
    rw [hnew_garb_s'] at hng; cases hng

/-- Setting `PH_GARB` on a clause preserves `FullArenaVarsNodup`. -/
theorem FullArenaVarsNodup.of_markGarb {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hinv : FullCoreInv c F0 s) (hnd : FullArenaVarsNodup s)
    {cref : Nat} (href : cref ∈ fullArenaClauseRefs s) (ag' : BitVec 64) :
    let s' : FullState :=
      { s with core :=
        { s.core with
          arena := s.core.arena.set cref (fullArenaHdr s cref ||| 0x00080000#32)
          arena_garbage := ag' } }
    FullArenaVarsNodup s' := by
  intro s' r hr hng
  obtain ⟨F_cur, hw⟩ := hinv.witness
  have hmg := hw.arena.markGarb hinv.lengths.core_ok href ag'
  have hr0 : r ∈ fullArenaClauseRefsCore s.core := by
    change r ∈ fullArenaClauseRefsCore s'.core at hr; rwa [hmg.1] at hr
  have har_len : cref < s.core.arena.length := by
    have := (hw.arena.refs_wf cref href).1; have := hinv.lengths.core_ok.arena_len_le
    have := hinv.lengths.core_ok.arena_len_arr; omega
  have hne : r ≠ cref := by
    rintro rfl
    unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore s' at hng
    rw [List.getElem?_set_self har_len, Option.getD_some] at hng
    have hbit : ((fullArenaHdr s r ||| 0x00080000#32) &&& 0x00080000#32) ≠ 0#32 := by
      intro h; have := congrArg (·[19]) h; simp at this
    exact hbit (by simpa using hng)
  have hng0 : fullArenaClauseGarb s r = false := by
    unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore at hng ⊢
    simpa [s', List.getElem?_set_ne hne.symm] using hng
  have hdisj : r + 3 + fullArenaClauseSizeCore s.core r ≤ cref ∨ cref + 3 ≤ r := by
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · exact Or.inl (hw.arena.disjoint hr0 href hlt)
    · exact Or.inr (by have := hw.arena.disjoint href hr0 hgt; omega)
  have hbd : r + 3 + fullArenaClauseSizeCore s.core r ≤ s.core.arena.length := by
    have := (hw.arena.refs_wf r hr0).2.2.1; have := (hw.arena.refs_wf r hr0).2.2.2.1
    have := hinv.lengths.core_ok.arena_len_le; have := hinv.lengths.core_ok.arena_len_arr; omega
  have hlits : fullArenaClauseLitsCore s'.core r = fullArenaClauseLitsCore s.core r :=
    (fullArenaClauseLitsCore_set_outside (v := fullArenaHdr s cref ||| 0x00080000#32)
      hbd hdisj).2
  unfold fullArenaClauseLits; rw [hlits]
  exact hnd r hr0 hng0

/-! ## 4. Level-0 conflict & refutation helpers -/

/-- Explicit-witness conflict predicate (`FullConflictOkW F_cur s`) shared by both
`FullWitnessInv` and `FullOtfsWitnessInv`. -/
def FullConflictOkW (F_cur : List (List Nat)) (s : FullState) : Prop :=
  (s.core.confl_type = 1#64 ∧
    s.core.confl_lit0.toNat < 2 * s.core.cur_vars ∧
    s.core.confl_lit1.toNat < 2 * s.core.cur_vars ∧
    s.core.vals[s.core.confl_lit0.toNat]?.getD 0#8 = 0xFF#8 ∧
    s.core.vals[s.core.confl_lit1.toNat]?.getD 0#8 = 0xFF#8 ∧
    (cnfOfClauses F_cur).EntailsClause
      (cnfClause [s.core.confl_lit0.toNat, s.core.confl_lit1.toNat])) ∨
  (s.core.confl_type = 2#64 ∧
    s.core.confl_ref.toNat ∈ fullArenaClauseRefs s ∧
    fullArenaClauseGarb s s.core.confl_ref.toNat = false ∧
    ∀ l ∈ fullArenaClauseLits s s.core.confl_ref.toNat, s.core.vals[l]?.getD 0#8 = 0xFF#8)

theorem level0_unsat_of_conflict_okW {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hw : FullWitnessInv c F0 F_cur s.core) (hl0 : s.core.cur_level = 0)
    (hc : FullConflictOkW F_cur s) : F0.Unsat := by
  rcases hc with ⟨_, h0lt, h1lt, hf0, hf1, hent⟩ | ⟨_, href, hng, hfals⟩
  · refine hw.ext_sound.2 (unsat_of_entails_nil (entails_of_mem_or_false hent fun l hl => ?_))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    right; rcases hl with rfl | rfl
    · obtain ⟨i, hi, heq⟩ := (hw.vals_false_iff _ h0lt).mp hf0
      have hs := hw.level0_sound i hi (by have := hw.lvl_le i hi; omega)
      rwa [heq] at hs
    · obtain ⟨i, hi, heq⟩ := (hw.vals_false_iff _ h1lt).mp hf1
      have hs := hw.level0_sound i hi (by have := hw.lvl_le i hi; omega)
      rwa [heq] at hs
  · refine hw.ext_sound.2
      (unsat_of_entails_nil (entails_of_mem_or_false (hw.arena.entails _ href hng) fun l hl => ?_))
    right
    have hlt := hw.arena.lits_lt _ href hng l hl
    obtain ⟨i, hi, heq⟩ := (hw.vals_false_iff l hlt).mp (hfals l hl)
    have hs := hw.level0_sound i hi (by have := hw.lvl_le i hi; omega)
    rwa [heq] at hs

/-- Valid conflict witness stored in `(confl_type, confl_ref, confl_lit0, confl_lit1)`:
either a falsified entailed binary clause (`confl_type = 1#64`) or a falsified live arena clause
(`confl_type = 2#64`, `confl_ref ∈ fullArenaClauseRefs s`, `garb = false`). -/
def FullConflictOk (c : FullCfg) (F0 : CNF Nat) (s : FullState) : Prop :=
  (s.core.confl_type = 1#64 ∧
    s.core.confl_lit0.toNat < 2 * s.core.cur_vars ∧
    s.core.confl_lit1.toNat < 2 * s.core.cur_vars ∧
    (∀ F_cur, FullWitnessInv c F0 F_cur s.core →
      (cnfOfClauses F_cur).EntailsClause
        (cnfClause [s.core.confl_lit0.toNat, s.core.confl_lit1.toNat])) ∧
    s.core.vals[s.core.confl_lit0.toNat]?.getD 0#8 = 0xFF#8 ∧
    s.core.vals[s.core.confl_lit1.toNat]?.getD 0#8 = 0xFF#8) ∨
  (s.core.confl_type = 2#64 ∧
    s.core.confl_ref.toNat ∈ fullArenaClauseRefs s ∧
    fullArenaClauseGarb s s.core.confl_ref.toNat = false ∧
    ∀ l ∈ fullArenaClauseLits s s.core.confl_ref.toNat, s.core.vals[l]?.getD 0#8 = 0xFF#8)

theorem level0_unsat_of_conflict_ok {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullCoreInv c F0 s) (hl0 : s.core.cur_level = 0) (hc : FullConflictOk c F0 s) :
    F0.Unsat := by
  rcases hc with ⟨_, h0lt, h1lt, hent, hf0, hf1⟩ | ⟨_, href, hng, hfals⟩
  · exact h.level0_unsat_of_bin_conflict hl0 h0lt h1lt hent hf0 hf1
  · exact h.level0_unsat_of_conflict hl0 href hng hfals

/-- Level-0 unit contradiction refutation helper (`full_add_unit`, `full_sweep_copy`,
`full_ingest_cl`). -/
theorem level0_unit_conflict_unsat {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullCoreInv c F0 s) (hl0 : s.core.cur_level = 0) {lit : Nat}
    (hlt : lit < 2 * s.core.cur_vars) (hfals : s.core.vals[lit]?.getD 0#8 = 0xFF#8)
    (hent : ∀ F_cur, FullWitnessInv c F0 F_cur s.core →
      (cnfOfClauses F_cur).EntailsClause (cnfClause [lit])) : F0.Unsat := by
  obtain ⟨F_cur, hw⟩ := h.witness
  refine hw.ext_sound.2
    (unsat_of_entails_nil (entails_of_mem_or_false (hent F_cur hw) fun l hl => ?_))
  simp only [List.mem_singleton] at hl; subst hl; right
  obtain ⟨i, hi, hieq⟩ := (hw.vals_false_iff l hlt).mp hfals
  have hs := hw.level0_sound i hi (by have := hw.lvl_le i hi; omega)
  rwa [hieq] at hs

/-! ## 5. Shared auxiliary predicates for `FullSpec2` / `FullSpec3` -/

/-- Trail-prefix and assigned-level preservation across BCP (`full_prop_lit`, `full_propagate*`). -/
def FullTrailExt (k k' : FullCoreState) : Prop :=
  k.trail_end ≤ k'.trail_end ∧
  (∀ i < k.trail_end, k'.trl[i]? = k.trl[i]?) ∧
  (∀ i < k.trail_end,
    k'.lvl[(k.trl[i]?.getD 0#32).toNat / 2]? = k.lvl[(k.trl[i]?.getD 0#32).toNat / 2]?)

/-- Arena clause-ref and literal-permutation preservation (`full_prop_lit`, `full_propagate*`,
`full_warmup`). -/
def FullArenaPermEq (k k' : FullCoreState) : Prop :=
  k'.arena_len = k.arena_len ∧
  fullArenaClauseRefsCore k' = fullArenaClauseRefsCore k ∧
  ∀ r ∈ fullArenaClauseRefsCore k,
    fullArenaClauseSizeCore k' r = fullArenaClauseSizeCore k r ∧
    fullArenaClauseGarbCore k' r = fullArenaClauseGarbCore k r ∧
    (fullArenaClauseLitsCore k' r).Perm (fullArenaClauseLitsCore k r)

/-- Binary-only watch-stack invariant after `full_sweep_bins` and during `full_sweep_copy`. -/
def FullBinOnlyWatchesInv (F_cur : List (List Nat)) (k : FullCoreState) : Prop :=
  WatchStackLayout k ∧
  ∀ l < 2 * k.cur_vars, ∀ i < fullWatchSizeCore k l,
    let w := k.wstk[fullWatchOffCore k l + i]?.getD 0#32
    (w &&& 0x80000000#32) ≠ 0#32 ∧ (w &&& 0x7FFFFFFF#32).toNat < 2 * k.cur_vars ∧
    (cnfOfClauses F_cur).EntailsClause (cnfClause [l, (w &&& 0x7FFFFFFF#32).toNat])

/-- Every large arena reason referenced by a positive-level trail literal has `PH_RSN`
(`0x00200000#32`) set (`full_mark_reasons`, `full_arena_sweep`, `full_reduce`). -/
def FullReasonsMarked (s : FullState) : Prop :=
  ∀ idx < s.core.trail_end,
    let v := (s.core.trl[idx]?.getD 0#32).toNat / 2
    let rsn := s.core.rsns[v]?.getD 0xFFFFFFFF#32
    0 < (s.core.lvl[v]?.getD 0#32).toNat → (rsn &&& 0x80000000#32) = 0#32 →
    (fullArenaHdr s rsn.toNat &&& 0x00200000#32) ≠ 0#32

/-- Literals scanned by `full_analyze_rsn` for binary or large reason `rsn`. -/
def fullRsnLits (s : FullState) (rsn : BitVec 32) : List Nat :=
  if rsn = 0xFFFFFFFF#32 then []
  else if (rsn &&& 0x80000000#32) ≠ 0#32 then [(rsn &&& 0x7FFFFFFF#32).toNat]
  else fullArenaClauseLits s rsn.toNat

/-- Relaxed `FullWitnessInv` during OTFS retry (`full_deduce_1uip` returning `2#64` inside
`full_analyze`): `reason_inv` and `reason_lit_mem` hold strictly below `cur_level`. -/
structure FullOtfsWitnessInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (k : FullCoreState) : Prop where
  ext_sound : ExtUnsatSound F0 k.cur_vars F_cur
  inconsistent_sound : k.inconsistent ≠ 0#64 → (cnfOfClauses F_cur).Unsat
  arena : FullArenaClausesInv c F_cur k
  watches : ModeWatchesInv F_cur k
  cur_level_le : k.cur_level ≤ k.trail_end
  trail_lits_lt : ∀ i < k.trail_end, (k.trl[i]?.getD 0#32).toNat < 2 * k.cur_vars
  trail_vars_nodup : ∀ i j, i < k.trail_end → j < k.trail_end →
    (k.trl[i]?.getD 0#32).toNat / 2 = (k.trl[j]?.getD 0#32).toNat / 2 → i = j
  vals_domain : ∀ l < 2 * k.cur_vars,
    k.vals[l]?.getD 0#8 = 0#8 ∨ k.vals[l]?.getD 0#8 = 1#8 ∨ k.vals[l]?.getD 0#8 = 0xFF#8
  vals_true_iff : ∀ l < 2 * k.cur_vars,
    k.vals[l]?.getD 0#8 = 1#8 ↔ ∃ i < k.trail_end, (k.trl[i]?.getD 0#32).toNat = l
  vals_false_iff : ∀ l < 2 * k.cur_vars,
    k.vals[l]?.getD 0#8 = 0xFF#8 ↔ ∃ i < k.trail_end, (k.trl[i]?.getD 0#32).toNat = l ^^^ 1
  lvl_le : ∀ i < k.trail_end,
    (k.lvl[(k.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ k.cur_level
  dec_earliest : ∀ i j, i < k.trail_end → j < k.trail_end →
    (k.lvl[(k.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat =
      (k.lvl[(k.trl[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat →
    0 < (k.lvl[(k.trl[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ∧
    k.rsns[(k.trl[j]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 → j ≤ i
  levels_inhabited : ∀ L, 1 ≤ L → L ≤ k.cur_level →
    ∃ i < k.trail_end, (k.lvl[(k.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = L
  level0_sound : ∀ i < k.trail_end,
    (k.lvl[(k.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 →
    (cnfOfClauses F_cur).EntailsClause (cnfClause [(k.trl[i]?.getD 0#32).toNat])
  trail_pos_inv : ∀ i < k.trail_end,
    (k.trail_pos[(k.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = i
  level0_rsn_none : ∀ idx < k.trail_end,
    (k.lvl[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 →
    k.rsns[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32
  frame_trail_lt : ∀ L ≤ k.cur_level, (k.frame_trail[L]?.getD 0#32).toNat ≤ k.trail_end
  frame_trail_mono : ∀ L1 L2, L1 ≤ L2 → L2 ≤ k.cur_level →
    (k.frame_trail[L1]?.getD 0#32).toNat ≤ (k.frame_trail[L2]?.getD 0#32).toNat
  frame_trail_before_lt : ∀ L, 1 ≤ L → L ≤ k.cur_level →
    ∀ i < (k.frame_trail[L]?.getD 0#32).toNat,
      (k.lvl[(k.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat < L
  frame_dec_lt : ∀ L, 1 ≤ L → L ≤ k.cur_level →
    (k.frame_dec[L]?.getD 0#32).toNat < 2 * k.cur_vars
  reason_inv_below : ∀ idx < k.trail_end,
    let p := (k.trl[idx]?.getD 0#32).toNat
    let rsn := k.rsns[p / 2]?.getD 0xFFFFFFFF#32
    (k.lvl[p / 2]?.getD 0#32).toNat < k.cur_level → rsn ≠ 0xFFFFFFFF#32 →
    if (rsn &&& 0x80000000#32) ≠ 0#32 then
      let ot := (rsn &&& 0x7FFFFFFF#32).toNat
      ot < 2 * k.cur_vars ∧ (cnfOfClauses F_cur).EntailsClause (cnfClause [p, ot]) ∧
      ∃ m < idx, (k.trl[m]?.getD 0#32).toNat = ot ^^^ 1 ∧
        (k.lvl[ot / 2]?.getD 0#32).toNat ≤ (k.lvl[p / 2]?.getD 0#32).toNat
    else
      rsn.toNat ∈ fullArenaClauseRefsCore k ∧ fullArenaClauseGarbCore k rsn.toNat = false ∧
      ∀ q ∈ fullArenaClauseLitsCore k rsn.toNat,
        q = p ∨ ∃ m < idx, (k.trl[m]?.getD 0#32).toNat = q ^^^ 1 ∧
          (k.lvl[q / 2]?.getD 0#32).toNat ≤ (k.lvl[p / 2]?.getD 0#32).toNat
  reason_lit_mem_below : ∀ idx < k.trail_end,
    let p := (k.trl[idx]?.getD 0#32).toNat
    let rsn := k.rsns[p / 2]?.getD 0xFFFFFFFF#32
    (k.lvl[p / 2]?.getD 0#32).toNat < k.cur_level →
    rsn ≠ 0xFFFFFFFF#32 → (rsn &&& 0x80000000#32) = 0#32 →
    p ∈ fullArenaClauseLitsCore k rsn.toNat

/-- Cut-strengthened OTFS invariant: `reason_inv` and `reason_lit_mem` also hold on `[0 ..< cut)`.
At `cut = k.trail_end` this equals `FullWitnessInv`, and after OTFS at `idx_u` it holds at `idx_u`
so subsequent 1UIP retries in `full_analyze` can still resolve every reason strictly below `cut`. -/
structure FullWitnessCutInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (cut : Nat) (k : FullCoreState) : Prop extends FullOtfsWitnessInv c F0 F_cur k where
  cut_le : cut ≤ k.trail_end
  reason_inv_cut : ∀ idx < cut,
    let p := (k.trl[idx]?.getD 0#32).toNat
    let rsn := k.rsns[p / 2]?.getD 0xFFFFFFFF#32
    rsn ≠ 0xFFFFFFFF#32 →
    if (rsn &&& 0x80000000#32) ≠ 0#32 then
      let ot := (rsn &&& 0x7FFFFFFF#32).toNat
      ot < 2 * k.cur_vars ∧ (cnfOfClauses F_cur).EntailsClause (cnfClause [p, ot]) ∧
      ∃ m < idx, (k.trl[m]?.getD 0#32).toNat = ot ^^^ 1 ∧
        (k.lvl[ot / 2]?.getD 0#32).toNat ≤ (k.lvl[p / 2]?.getD 0#32).toNat
    else
      rsn.toNat ∈ fullArenaClauseRefsCore k ∧ fullArenaClauseGarbCore k rsn.toNat = false ∧
      ∀ q ∈ fullArenaClauseLitsCore k rsn.toNat,
        q = p ∨ ∃ m < idx, (k.trl[m]?.getD 0#32).toNat = q ^^^ 1 ∧
          (k.lvl[q / 2]?.getD 0#32).toNat ≤ (k.lvl[p / 2]?.getD 0#32).toNat
  reason_lit_mem_cut : ∀ idx < cut,
    let p := (k.trl[idx]?.getD 0#32).toNat
    let rsn := k.rsns[p / 2]?.getD 0xFFFFFFFF#32
    rsn ≠ 0xFFFFFFFF#32 → (rsn &&& 0x80000000#32) = 0#32 →
    p ∈ fullArenaClauseLitsCore k rsn.toNat

def FullOtfsCoreInv (c : FullCfg) (F0 : CNF Nat) (s : FullState) : Prop :=
  s.LengthsOk c ∧ ∃ F_cur, FullOtfsWitnessInv c F0 F_cur s.core

theorem FullWitnessInv.toOtfs {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (h : FullWitnessInv c F0 F_cur k) : FullOtfsWitnessInv c F0 F_cur k :=
  ⟨h.ext_sound, h.inconsistent_sound, h.arena, h.watches, h.cur_level_le, h.trail_lits_lt,
   h.trail_vars_nodup, h.vals_domain, h.vals_true_iff, h.vals_false_iff, h.lvl_le, h.dec_earliest,
   h.levels_inhabited, h.level0_sound, h.trail_pos_inv, h.level0_rsn_none, h.frame_trail_lt,
   h.frame_trail_mono, h.frame_trail_before_lt, h.frame_dec_lt,
   fun idx hi _ hne => h.reason_inv idx hi hne,
   fun idx hi _ hne hlg => h.reason_lit_mem idx hi hne hlg⟩

theorem FullWitnessInv.toCut {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (h : FullWitnessInv c F0 F_cur k) :
    FullWitnessCutInv c F0 F_cur k.trail_end k :=
  ⟨h.toOtfs, Nat.le_refl _, h.reason_inv, h.reason_lit_mem⟩

theorem FullCoreInv.toOtfs {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullCoreInv c F0 s) : FullOtfsCoreInv c F0 s :=
  let ⟨F_cur, hw⟩ := h.witness; ⟨h.lengths, F_cur, hw.toOtfs⟩

/-- Conflict-analysis variable mark coverage (`full_analyze_lit`, `full_bump_analyzed`,
`full_clear_ana`): `work_stk1[0 ..< min_clr_len)` is a `Nodup` list of marked `< cur_vars`
variables covering every nonzero `mrk[v]`. -/
def FullAnaMarksCov (c : FullCfg) (s : FullState) : Prop :=
  s.core.min_clr_len ≤ s.core.cur_vars ∧
  ((s.scratch.work_stk1.take s.core.min_clr_len).map BitVec.toNat).Nodup ∧
  (∀ k < s.core.min_clr_len,
    (s.scratch.work_stk1[k]?.getD 0#32).toNat < s.core.cur_vars ∧
    s.core.mrk[(s.scratch.work_stk1[k]?.getD 0#32).toNat]?.getD 0#8 ≠ 0#8) ∧
  (∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 ≠ 0#8 →
    ∃ i < s.core.min_clr_len, (s.scratch.work_stk1[i]?.getD 0#32).toNat = v)

/-- Explicit-witness OTFS invariant (`FullSparseInvW.toOtfs`). -/
def FullOtfsInvW (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) : Prop :=
  s.LengthsOk c ∧ FullOtfsWitnessInv c F0 F_cur s.core ∧ FullLitMarksClear c s ∧
  FullArenaVarsNodup s ∧ FullExtScratchOk c s ∧ s.core.dense_mode = 0#64

/-- Explicit-witness cut-OTFS invariant (`FullSparseInvW.toCut`). -/
def FullCutInvW (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (cut : Nat)
    (s : FullState) : Prop :=
  s.LengthsOk c ∧ FullWitnessCutInv c F0 F_cur cut s.core ∧ FullLitMarksClear c s ∧
  FullArenaVarsNodup s ∧ FullExtScratchOk c s ∧ s.core.dense_mode = 0#64

/-- Conflict witness whose current-level literals all have trail position `< cut`. -/
def FullConflictOkCut (F_cur : List (List Nat)) (cut : Nat) (s : FullState) : Prop :=
  FullConflictOkW F_cur s ∧
  (if s.core.confl_type = 1#64 then
    ((s.core.lvl[s.core.confl_lit0.toNat / 2]?.getD 0#32).toNat = s.core.cur_level →
      ∃ m < cut, (s.core.trl[m]?.getD 0#32).toNat = s.core.confl_lit0.toNat ^^^ 1) ∧
    ((s.core.lvl[s.core.confl_lit1.toNat / 2]?.getD 0#32).toNat = s.core.cur_level →
      ∃ m < cut, (s.core.trl[m]?.getD 0#32).toNat = s.core.confl_lit1.toNat ^^^ 1)
   else
    ∀ l ∈ fullArenaClauseLits s s.core.confl_ref.toNat,
      (s.core.lvl[l / 2]?.getD 0#32).toNat = s.core.cur_level →
      ∃ m < cut, (s.core.trl[m]?.getD 0#32).toNat = l ^^^ 1)

theorem FullSparseInvW.toOtfs {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullSparseInvW c F0 F_cur s) : FullOtfsInvW c F0 F_cur s :=
  ⟨h.1, h.2.1.toOtfs, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

theorem FullSparseInvW.toCut {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullSparseInvW c F0 F_cur s) :
    FullCutInvW c F0 F_cur s.core.trail_end s :=
  ⟨h.1, h.2.1.toCut, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

theorem FullCutInvW.toOtfs {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {s : FullState} (h : FullCutInvW c F0 F_cur cut s) : FullOtfsInvW c F0 F_cur s :=
  ⟨h.1, h.2.1.toFullOtfsWitnessInv, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

theorem FullConflictOkW.toCut {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hw : FullWitnessInv c F0 F_cur s.core) (hc : FullConflictOkW F_cur s) :
    FullConflictOkCut F_cur s.core.trail_end s := by
  refine ⟨hc, ?_⟩
  split
  · rename_i h1
    rcases hc with ⟨_, h0lt, h1lt, hf0, hf1, _⟩ | ⟨hne, _⟩
    · exact ⟨fun _ => (hw.vals_false_iff _ h0lt).mp hf0, fun _ => (hw.vals_false_iff _ h1lt).mp hf1⟩
    · exact absurd (h1.symm.trans hne) (by decide)
  · rename_i hne
    rcases hc with ⟨h1, _⟩ | ⟨_, href, hng, hfals⟩
    · exact absurd h1 hne
    · exact fun l hl _ => (hw.vals_false_iff l (hw.arena.lits_lt _ href hng l hl)).mp (hfals l hl)

/-- At level 0, `FullOtfsWitnessInv` coincides with `FullWitnessInv` (`level0_rsn_none`). -/
theorem FullOtfsWitnessInv.toWitness_of_level0 {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {k : FullCoreState} (h : FullOtfsWitnessInv c F0 F_cur k)
    (hl0 : k.cur_level = 0) : FullWitnessInv c F0 F_cur k :=
  ⟨h.ext_sound, h.inconsistent_sound, h.arena, h.watches, h.cur_level_le, h.trail_lits_lt,
   h.trail_vars_nodup, h.vals_domain, h.vals_true_iff, h.vals_false_iff, h.lvl_le, h.dec_earliest,
   h.levels_inhabited, h.level0_sound, h.trail_pos_inv, h.level0_rsn_none, h.frame_trail_lt,
   h.frame_trail_mono, h.frame_trail_before_lt, h.frame_dec_lt,
   fun idx hi hne => absurd (h.level0_rsn_none idx hi (by have := h.lvl_le idx hi; omega)) hne,
   fun idx hi hne _ => absurd (h.level0_rsn_none idx hi (by have := h.lvl_le idx hi; omega)) hne⟩

theorem FullOtfsInvW.toSparse_of_level0 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullOtfsInvW c F0 F_cur s) (hl0 : s.core.cur_level = 0) :
    FullSparseInvW c F0 F_cur s :=
  ⟨h.1, h.2.1.toWitness_of_level0 hl0, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

end LeanQbe.T.Examples.Kissat.Full
