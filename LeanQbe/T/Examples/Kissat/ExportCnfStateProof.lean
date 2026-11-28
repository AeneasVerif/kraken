/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.ExportCnfState
public import LeanQbe.T.Examples.Kissat.ExportCnfFmtProof
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts1
public import LeanQbe.T.Logic.Bytes
public import LeanQbe.T.Logic.Rules
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
meta import LeanQbe.T.Logic.C0HeadStep
import Kraken.Mem
import Kraken.Separation

/-!
# Verification and UNSAT-Soundness Proofs for `ExportCnfState`

Proves (`0` `import all`, `0` `@[expose]` on theorems/lemmas, `<= std3`, `0` changes to
`FullWitnessInv`):
1. Pure clause extraction from `FullCoreState` (`exportTrailUnitClauses`, `exportBinSliceClauses`,
   `exportBinClauses`, `exportArenaClauses`, `exportStateClauses`, `exportStateBytes`), exact
   size/byte-length bounds (`< 2^31` clauses, `< 2^36` bytes — zero 64-bit overflow for any
   `FullCfg`), and semantic soundness:
   - `exportStateBytes_sound`: under `FullWitnessInv c F0 F_cur k` at level 0,
     `parseDimacs (exportStateBytes k) = some cnfOut` and `cnfOut.Unsat → F0.Unsat`.
   - `exportStateBytes_sound_dimacs`: 1-based input `cnfIn` corollary
     (`cnfOut.Unsat → cnfIn.Unsat`).
2. `XPost`-polymorphic parametric `(Γ : Env)` WP proofs for all five C0 functions:
   - `kissat_export_arena_next_wp`
   - `kissat_export_trail_units_wp`
   - `kissat_export_bin_clauses_wp` (uniformly covering sparse 2WL and dense occurrence watch modes)
   - `kissat_export_arena_clauses_wp` (`PH_SHRK`-aware, filtering `(hdr & (PH_GARB | PH_RED)) == 0`)
   - `kissat_export_cnf_bytes_wp` (optional `full_backtrack(h, 0ULL)` against canonical
     `fullBacktrackSpec`, inconsistent `"p cnf 0 1\n0\n"`, 2-pass count/bounds-check/emit).
3. Closed module certification (`exportCnfStateEnv_moduleOk`, `exportCnfStateFns_sound_in`) ready
   for direct compositional integration into any Kissat assembly.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.ExportCnfState

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref hiding dimacsBound parseDimacs
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.ExportCnfFmt
open Kraken.Bedrock2.Test
open scoped FullArenaTactics

/-! ## 1. Pure Clause Extraction and `XPost`-Polymorphic `Spec` Contracts -/

@[expose] public section

/-- Level-0 trail unit clauses `[l]` extracted from `k.trl[0 ..< k.trail_end)`. -/
def exportTrailUnitClauses (k : FullCoreState) : List (List Nat) :=
  ((k.trl.take k.trail_end).map BitVec.toNat).map fun l => [l]

/-- Deduplicated binary watch clauses `[l0, l1]` (`l0 < l1`) extracted from watch-stack slice
`wstk[p ..< p + rem)` (works identically in sparse 2WL and dense occurrence watch modes). -/
def exportBinSliceClauses (wstk : List (BitVec 32)) (l0 p : Nat) : Nat → List (List Nat)
  | 0 => []
  | fuel + 1 =>
    let w0 := wstk[p]?.getD 0#32
    if (w0 &&& 0x80000000#32) ≠ 0#32 then
      let l1 := (w0 &&& 0x7FFFFFFF#32).toNat
      let rest := exportBinSliceClauses wstk l0 (p + 1) fuel
      if l0 < l1 then [l0, l1] :: rest else rest
    else
      match fuel with
      | 0 => []
      | fuel' + 1 => exportBinSliceClauses wstk l0 (p + 2) fuel'

/-- All deduplicated binary clauses `[l0, l1]` (`l0 < l1`) across `0 ..< 2 * k.cur_vars`. -/
def exportBinClauses (k : FullCoreState) : List (List Nat) :=
  (List.range (2 * k.cur_vars)).flatMap fun l0 =>
    exportBinSliceClauses k.wstk l0 (fullWatchOffCore k l0) (fullWatchSizeCore k l0)

/-- Predicate selecting live irredundant arena clauses (`(hdr & (PH_GARB | PH_RED)) == 0`). -/
def fullArenaClauseIrredLiveCore (k : FullCoreState) (r : Nat) : Bool :=
  (fullArenaHdrCore k r &&& 0x00480000#32) == 0#32

/-- All live irredundant arena clauses in scan order (`fullArenaClauseRefsCore k`). -/
def exportArenaClauses (k : FullCoreState) : List (List Nat) :=
  ((fullArenaClauseRefsCore k).filter (fullArenaClauseIrredLiveCore k)).map
    (fullArenaClauseLitsCore k)

/-- Complete exported 0-based Kissat clause list for a level-0 core state `k`. -/
def exportStateClauses (k : FullCoreState) : List (List Nat) :=
  if k.inconsistent ≠ 0#64 then [[]]
  else exportTrailUnitClauses k ++ exportBinClauses k ++ exportArenaClauses k

/-- Declared DIMACS header `max_var` for level-0 core state `k`. -/
def exportStateMv (k : FullCoreState) : Nat :=
  if k.inconsistent ≠ 0#64 then 0 else k.cur_vars

/-- Complete emitted ASCII DIMACS byte stream for level-0 core state `k`. -/
def exportStateBytes (k : FullCoreState) : List UInt8 :=
  emitDimacsBytes (exportStateMv k) (exportStateClauses k)

/-- `XPost`-polymorphic WP contract for `kissat_export_arena_next(h, cref)`. -/
def kissatExportArenaNextSpec : Spec [i64, i64] [i64] :=
  fun args m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (cref : BitVec 64) (R : Mem 64 → Prop),
      args = (c.hdr, cref, ()) ∧
      s.LengthsOk c ∧
      cref.toNat ≤ s.core.arena_len ∧
      (FullMem c s ⋆ R) m ∧
      Q (BitVec.ofNat 64 (fullArenaNextOff s.core.arena s.core.arena_len cref.toNat), ()) m

/-- `XPost`-polymorphic WP contract for `kissat_export_trail_units(h, out, cap, pos, cnt_ptr)`. -/
def kissatExportTrailUnitsSpec : Spec [i64, i64, i64, i64, i64] [i64] :=
  fun args m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (out cnt_ptr : BitVec 64) (buf : List UInt8)
      (pos cnt0 : Nat) (R : Mem 64 → Prop),
      let emitBs := (exportTrailUnitClauses s.core).flatMap emitDimacsClauseBytes
      args = (c.hdr, out, BitVec.ofNat 64 buf.length, BitVec.ofNat 64 pos, cnt_ptr, ()) ∧
      s.LengthsOk c ∧
      buf.length < 2 ^ 64 ∧
      pos + emitBs.length < 2 ^ 64 ∧
      cnt0 + s.core.trail_end < 2 ^ 64 ∧
      (FullMem c s ⋆ bytes out buf ⋆ cell64 cnt_ptr (BitVec.ofNat 64 cnt0) ⋆ R) m ∧
      ∀ m',
        (FullMem c s ⋆ bytes out (writeSlice buf pos emitBs) ⋆
          cell64 cnt_ptr (BitVec.ofNat 64 (cnt0 + s.core.trail_end)) ⋆ R) m' →
        Q (BitVec.ofNat 64 (pos + emitBs.length), ()) m'

/-- `XPost`-polymorphic WP contract for `kissat_export_bin_clauses(h, out, cap, pos, cnt_ptr)`. -/
def kissatExportBinClausesSpec : Spec [i64, i64, i64, i64, i64] [i64] :=
  fun args m Q _ =>
    ∃ (c : FullCfg) (F_cur : List (List Nat)) (s : FullState) (out cnt_ptr : BitVec 64)
      (buf : List UInt8) (pos cnt0 : Nat) (R : Mem 64 → Prop),
      let cls := exportBinClauses s.core
      let emitBs := cls.flatMap emitDimacsClauseBytes
      args = (c.hdr, out, BitVec.ofNat 64 buf.length, BitVec.ofNat 64 pos, cnt_ptr, ()) ∧
      s.LengthsOk c ∧
      ModeWatchesInv F_cur s.core ∧
      buf.length < 2 ^ 64 ∧
      pos + emitBs.length < 2 ^ 64 ∧
      cnt0 + cls.length < 2 ^ 64 ∧
      (FullMem c s ⋆ bytes out buf ⋆ cell64 cnt_ptr (BitVec.ofNat 64 cnt0) ⋆ R) m ∧
      ∀ m',
        (FullMem c s ⋆ bytes out (writeSlice buf pos emitBs) ⋆
          cell64 cnt_ptr (BitVec.ofNat 64 (cnt0 + cls.length)) ⋆ R) m' →
        Q (BitVec.ofNat 64 (pos + emitBs.length), ()) m'

/-- `XPost`-polymorphic WP contract for `kissat_export_arena_clauses(h, out, cap, pos, cnt_ptr)`. -/
def kissatExportArenaClausesSpec : Spec [i64, i64, i64, i64, i64] [i64] :=
  fun args m Q _ =>
    ∃ (c : FullCfg) (F_cur : List (List Nat)) (s : FullState) (out cnt_ptr : BitVec 64)
      (buf : List UInt8) (pos cnt0 : Nat) (R : Mem 64 → Prop),
      let cls := exportArenaClauses s.core
      let emitBs := cls.flatMap emitDimacsClauseBytes
      args = (c.hdr, out, BitVec.ofNat 64 buf.length, BitVec.ofNat 64 pos, cnt_ptr, ()) ∧
      s.LengthsOk c ∧
      FullArenaClausesInv c F_cur s.core ∧
      buf.length < 2 ^ 64 ∧
      pos + emitBs.length < 2 ^ 64 ∧
      cnt0 + cls.length < 2 ^ 64 ∧
      (FullMem c s ⋆ bytes out buf ⋆ cell64 cnt_ptr (BitVec.ofNat 64 cnt0) ⋆ R) m ∧
      ∀ m',
        (FullMem c s ⋆ bytes out (writeSlice buf pos emitBs) ⋆
          cell64 cnt_ptr (BitVec.ofNat 64 (cnt0 + cls.length)) ⋆ R) m' →
        Q (BitVec.ofNat 64 (pos + emitBs.length), ()) m'

/-- Top-level `XPost`-polymorphic WP contract for `kissat_export_cnf_bytes(h, out, cap, lenp)`.
Establishes valid ASCII DIMACS grammar (`parseDimacs outBytes = some cnfOut`) and UNSAT soundness
(`cnfOut.Unsat → F0.Unsat`) directly from `FullWitnessInv` (with `0` changes to `FullWitnessInv`),
while preserving `FullWitnessInv`, `FullProbeScratchPres`, and safe untouched `out` on dry-run or
insufficient capacity. -/
def kissatExportCnfBytesSpec : Spec [i64, i64, i64, i64] [i64] :=
  fun args m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (out out_len_ptr old_len : BitVec 64) (buf : List UInt8) (R : Mem 64 → Prop),
      args = (c.hdr, out, BitVec.ofNat 64 buf.length, out_len_ptr, ()) ∧
      buf.length < 2 ^ 64 ∧
      s.LengthsOk c ∧
      FullWitnessInv c F0 F_cur s.core ∧
      (FullMem c s ⋆ bytes out buf ⋆ cell64 out_len_ptr old_len ⋆ R) m ∧
      ∀ (r : BitVec 64) (s' : FullState) (outBytes : List UInt8) (written : Nat)
        (m' : Mem 64),
        s'.LengthsOk c →
        FullWitnessInv c F0 F_cur s'.core →
        s'.core.cur_level = 0 →
        s'.core.cur_vars = s.core.cur_vars →
        s'.core.inconsistent = s.core.inconsistent →
        s'.core.arena = s.core.arena →
        s'.core.arena_len = s.core.arena_len →
        s'.core.wvec = s.core.wvec →
        s'.core.wstk = s.core.wstk →
        s'.core.wlen = s.core.wlen →
        s'.core.dense_mode = s.core.dense_mode →
        FullProbeScratchPres s s' →
        (r = 0#64 ∨ r = 1#64) →
        written < 2 ^ 64 →
        (r = 0#64 →
          (written = 0 ∨ written = (exportStateBytes s'.core).length) ∧
          (exportStateMv s'.core < dimacsBound →
            (exportStateClauses s'.core).length < dimacsBound →
            written = (exportStateBytes s'.core).length ∧ buf.length < written) ∧
          (FullMem c s' ⋆ bytes out buf ⋆
            cell64 out_len_ptr (BitVec.ofNat 64 written) ⋆ R) m') →
        (r = 1#64 →
          outBytes = exportStateBytes s'.core ∧
          written = outBytes.length ∧
          written ≤ buf.length ∧
          (∃ cnfOut : CNF Nat,
            parseDimacs outBytes = some cnfOut ∧
            cnfOut = kissatCnfToDimacs (exportStateClauses s'.core) ∧
            (cnfOut.Unsat → F0.Unsat)) ∧
          (FullMem c s' ⋆ bytes out (outBytes ++ buf.drop written) ⋆
            cell64 out_len_ptr (BitVec.ofNat 64 written) ⋆ R) m') →
        Q (r, ()) m'

/-- Closed specification environment for `exportCnfStateMod` (`4` formatter fns + `5` exporter fns +
extern `full_backtrack`). -/
def exportCnfStateEnv : Env :=
  fun f as rs =>
    if h : f = "full_backtrack" ∧ as = [i64, i64] ∧ rs = [] then
      h.2.1 ▸ h.2.2 ▸ fullBacktrackSpec
    else if h : f = "kissat_export_arena_next" ∧ as = [i64, i64] ∧ rs = [i64] then
      h.2.1 ▸ h.2.2 ▸ kissatExportArenaNextSpec
    else if h : f = "kissat_export_trail_units" ∧
        as = [i64, i64, i64, i64, i64] ∧ rs = [i64] then
      h.2.1 ▸ h.2.2 ▸ kissatExportTrailUnitsSpec
    else if h : f = "kissat_export_bin_clauses" ∧
        as = [i64, i64, i64, i64, i64] ∧ rs = [i64] then
      h.2.1 ▸ h.2.2 ▸ kissatExportBinClausesSpec
    else if h : f = "kissat_export_arena_clauses" ∧
        as = [i64, i64, i64, i64, i64] ∧ rs = [i64] then
      h.2.1 ▸ h.2.2 ▸ kissatExportArenaClausesSpec
    else if h : f = "kissat_export_cnf_bytes" ∧
        as = [i64, i64, i64, i64] ∧ rs = [i64] then
      h.2.1 ▸ h.2.2 ▸ kissatExportCnfBytesSpec
    else
      exportCnfFmtEnv f as rs

end

/-! ## 2. Pure Size Bounds, Disjoint-Interval Pigeonhole, and Semantic Soundness -/

public section

private theorem nodup_not_mem_erase_self {a : Nat} :
    ∀ {xs : List Nat}, xs.Nodup → a ∉ xs.erase a
  | [], _ => by simp
  | x :: xs, hnd => by
    rw [List.nodup_cons] at hnd
    by_cases h : x == a
    · have hxa : x = a := beq_iff_eq.mp h
      subst hxa
      simp [List.erase_cons_head, hnd.1]
    · have hne : x ≠ a := fun heq => h (beq_iff_eq.mpr heq)
      rw [List.erase_cons_tail (by simpa using h)]
      intro hm
      rcases List.mem_cons.mp hm with rfl | hrest
      · exact hne rfl
      · exact nodup_not_mem_erase_self hnd.2 hrest

private theorem nodup_length_le_of_lt :
    ∀ (N : Nat) (xs : List Nat), xs.Nodup → (∀ x ∈ xs, x < N) → xs.length ≤ N
  | 0, [], _, _ => Nat.zero_le 0
  | 0, x :: _, _, hlt => absurd (hlt x (by simp)) (by omega)
  | N + 1, xs, hnd, hlt => by
    by_cases hmem : N ∈ xs
    · have hnd' : (xs.erase N).Nodup := hnd.erase N
      have hlt' : ∀ x ∈ xs.erase N, x < N := by
        intro x hx
        have hx_in : x ∈ xs := List.mem_of_mem_erase hx
        have hltN : x < N + 1 := hlt x hx_in
        have hne : x ≠ N := fun heq => nodup_not_mem_erase_self hnd (heq ▸ hx)
        omega
      have ih := nodup_length_le_of_lt N (xs.erase N) hnd' hlt'
      have hlen : (xs.erase N).length = xs.length - 1 := List.length_erase_of_mem hmem
      have hpos : 0 < xs.length := List.length_pos_of_mem hmem
      omega
    · have ih := nodup_length_le_of_lt N xs hnd fun x hx => by
        have h1 := hlt x hx
        have hne : x ≠ N := fun heq => hmem (heq ▸ hx)
        omega
      omega

private theorem nodup_map_inj {α β : Type} {f : α → β} (hinj : ∀ a b, f a = f b → a = b) :
    ∀ {xs : List α}, xs.Nodup → (xs.map f).Nodup
  | [], _ => List.nodup_nil
  | x :: xs, hnd => by
    rw [List.nodup_cons] at hnd
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => ?_, nodup_map_inj hinj hnd.2⟩
    obtain ⟨y, hy, hfy⟩ := List.mem_map.mp hm
    exact hnd.1 ((hinj y x hfy) ▸ hy)

private theorem range_map_add_nodup (off sz : Nat) :
    ((List.range sz).map (off + ·)).Nodup :=
  nodup_map_inj (fun _ _ h => by omega) List.nodup_range

private theorem mem_range_map_add_iff {off sz x : Nat} :
    x ∈ (List.range sz).map (off + ·) ↔ off ≤ x ∧ x < off + sz := by
  rw [List.mem_map]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rw [List.mem_range] at hi; omega
  · rintro ⟨h1, h2⟩
    exact ⟨x - off, List.mem_range.mpr (by omega), by omega⟩

private theorem flatMap_length_sum {α β : Type} (xs : List α) (f : α → List β) :
    (xs.flatMap f).length = (xs.map fun x => (f x).length).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [List.flatMap_cons, ih]

private theorem flatMap_range_intervals_nodup {off sz : Nat → Nat} :
    ∀ (n : Nat),
      (∀ l1 l2, l1 < n → l2 < n → l1 ≠ l2 → 0 < sz l1 → 0 < sz l2 →
        off l1 + sz l1 ≤ off l2 ∨ off l2 + sz l2 ≤ off l1) →
      ((List.range n).flatMap fun l => (List.range (sz l)).map (off l + ·)).Nodup
  | 0, _ => by simp
  | n + 1, hdisj => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.nodup_append]
    refine ⟨flatMap_range_intervals_nodup n (fun l1 l2 h1 h2 => hdisj l1 l2 (by omega) (by omega)),
      range_map_add_nodup (off n) (sz n), ?_⟩
    intro x hx y hy hxy
    subst hxy
    rw [List.mem_flatMap] at hx
    obtain ⟨l, hl, hxl⟩ := hx
    rw [List.mem_range] at hl
    rw [mem_range_map_add_iff] at hxl hy
    have hp1 : 0 < sz l := by omega
    have hp2 : 0 < sz n := by omega
    rcases hdisj l n (by omega) (by omega) (by omega) hp1 hp2 with h | h <;> omega

theorem watchStackLayout_sum_sizes_le {k : FullCoreState} (h : WatchStackLayout k) :
    ((List.range (2 * k.cur_vars)).map (fullWatchSizeCore k)).sum ≤ k.wlen := by
  let idxList :=
    (List.range (2 * k.cur_vars)).flatMap fun l =>
      (List.range (fullWatchSizeCore k l)).map (fullWatchOffCore k l + ·)
  have hlen : idxList.length = ((List.range (2 * k.cur_vars)).map (fullWatchSizeCore k)).sum := by
    dsimp only [idxList]
    rw [flatMap_length_sum]
    congr 1
    apply List.map_congr_left
    intro l _
    simp
  have hnd : idxList.Nodup := flatMap_range_intervals_nodup (2 * k.cur_vars) h.disjoint
  have hlt : ∀ x ∈ idxList, x < k.wlen := by
    intro x hx
    rw [List.mem_flatMap] at hx
    obtain ⟨l, hl, hxl⟩ := hx
    rw [List.mem_range] at hl
    rw [mem_range_map_add_iff] at hxl
    have hb := h.bounds l hl
    omega
  rw [← hlen]
  exact nodup_length_le_of_lt k.wlen idxList hnd hlt

private theorem emitDimacsClauseBytes_length_le {cl : List Nat}
    (hcl : ∀ l ∈ cl, l < 2 ^ 64) :
    (emitDimacsClauseBytes cl).length ≤ 22 * cl.length + 2 := by
  unfold emitDimacsClauseBytes
  rw [List.length_append, List.length_cons, List.length_cons, List.length_nil]
  suffices (cl.flatMap emitDimacsLitBytes).length ≤ 22 * cl.length by omega
  induction cl with
  | nil => simp
  | cons l ls ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have h1 := emitDimacsLitBytes_length_le_22 (hcl l (by simp))
    have h2 := ih (fun x hx => hcl x (by simp [hx]))
    omega

theorem exportTrailUnitClauses_length {c : FullCfg} {k : FullCoreState}
    (hlen : k.LengthsOk c) :
    (exportTrailUnitClauses k).length = k.trail_end := by
  unfold exportTrailUnitClauses
  simp only [List.length_map, List.length_take]
  have := hlen.trl_len; have := hlen.trail_end_le; have := hlen.cur_vars_le
  omega

theorem exportTrailUnitClauses_bytes_le {c : FullCfg} {k : FullCoreState}
    (hlen : k.LengthsOk c) :
    ((exportTrailUnitClauses k).flatMap emitDimacsClauseBytes).length ≤ 24 * k.trail_end := by
  have hlen_eq := exportTrailUnitClauses_length hlen
  have hbound : ∀ (xs : List (BitVec 32)),
      (((xs.map BitVec.toNat).map fun l => [l]).flatMap emitDimacsClauseBytes).length ≤
        24 * xs.length := by
    intro xs
    induction xs with
    | nil => simp
    | cons x xs ih =>
      simp only [List.map_cons, List.flatMap_cons, List.length_append, List.length_cons]
      have hx : x.toNat < 2 ^ 64 := lt_trans x.isLt (by decide : 2 ^ 32 < 2 ^ 64)
      have h1 := emitDimacsClauseBytes_length_le (cl := [x.toNat]) (by simp [hx])
      simp only [List.length_singleton] at h1
      omega
  have h := hbound (k.trl.take k.trail_end)
  have ht : (k.trl.take k.trail_end).length = k.trail_end := by
    rw [List.length_take]
    have := hlen.trl_len; have := hlen.trail_end_le; have := hlen.cur_vars_le; omega
  rw [ht] at h
  exact h

theorem exportTrailUnitClauses_sound {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hlen : k.LengthsOk c) (hw : FullWitnessInv c F0 F_cur k)
    (hl0 : k.cur_level = 0) :
    ∀ cl ∈ exportTrailUnitClauses k,
      (∀ l ∈ cl, l < 2 * k.cur_vars) ∧ (cnfOfClauses F_cur).EntailsClause (cnfClause cl) := by
  intro cl hcl
  unfold exportTrailUnitClauses at hcl
  rw [List.mem_map] at hcl
  obtain ⟨l, hl, rfl⟩ := hcl
  rw [List.mem_map] at hl
  obtain ⟨bv, hbv, rfl⟩ := hl
  obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hbv
  have htrl_lt : k.trail_end ≤ k.trl.length := by
    have := hlen.trl_len; have := hlen.trail_end_le; have := hlen.cur_vars_le; omega
  have hi_te : i < k.trail_end := by rw [List.length_take] at hi; omega
  rw [List.getElem_take] at hget
  have hget_opt : (k.trl[i]?.getD 0#32).toNat = bv.toNat := by
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some, hget]
  have hlit_lt := hw.trail_lits_lt i hi_te
  have hlvl_le := hw.lvl_le i hi_te
  rw [hl0] at hlvl_le
  have hlvl_z : (k.lvl[(k.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by omega
  have hent := hw.level0_sound i hi_te hlvl_z
  rw [hget_opt] at hlit_lt hent
  exact ⟨fun x hx => by rw [List.mem_singleton.mp hx]; exact hlit_lt, hent⟩

/-- Unified sparse/dense slice validity predicate (`WatchSliceOk` when `dense_mode = 0`,
`DenseWatchSliceOk` otherwise). -/
private def ModeWatchSliceOk (F_cur : List (List Nat)) (k : FullCoreState)
    (l0 p rem : Nat) : Prop :=
  if k.dense_mode = 0#64 then WatchSliceOk F_cur k l0 p rem
  else DenseWatchSliceOk F_cur k l0 p rem

private theorem modeWatchesInv_slice {F_cur : List (List Nat)} {k : FullCoreState}
    (hw : ModeWatchesInv F_cur k) {l0 : Nat} (hl0 : l0 < 2 * k.cur_vars) :
    ModeWatchSliceOk F_cur k l0 (fullWatchOffCore k l0) (fullWatchSizeCore k l0) := by
  unfold ModeWatchSliceOk
  unfold ModeWatchesInv at hw
  split at hw <;> simp_all [WatchesInv.slices, DenseWatchesInv.slices]

private theorem modeWatchSlice_step {F_cur : List (List Nat)} {k : FullCoreState}
    {l0 p rem : Nat} (h : ModeWatchSliceOk F_cur k l0 p rem) (hpos : 0 < rem) :
    ∃ w0, k.wstk[p]? = some w0 ∧
      ((w0 &&& 0x80000000#32) ≠ 0#32 →
        (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k.cur_vars ∧
        (cnfOfClauses F_cur).EntailsClause (cnfClause [l0, (w0 &&& 0x7FFFFFFF#32).toNat]) ∧
        ModeWatchSliceOk F_cur k l0 (p + 1) (rem - 1)) ∧
      ((w0 &&& 0x80000000#32) = 0#32 →
        2 ≤ rem ∧ ModeWatchSliceOk F_cur k l0 (p + 2) (rem - 2)) := by
  by_cases hdm : k.dense_mode = 0#64
  · rw [ModeWatchSliceOk, ite_eq_left hdm] at h
    cases h with
    | empty => omega
    | @bin _ r' w0 hp hflag _ hlt hent hrest =>
      refine ⟨w0, hp, fun _ => ⟨hlt, hent, by simp [ModeWatchSliceOk, hdm]; exact hrest⟩,
        fun hz => absurd hz hflag⟩
    | @large _ r' w0 _ hp _ hflag _ _ hrest =>
      refine ⟨w0, hp, fun hne => absurd hflag hne,
        fun _ => ⟨by omega, by simp [ModeWatchSliceOk, hdm]; exact hrest⟩⟩
  · rw [ModeWatchSliceOk, ite_eq_right hdm] at h
    cases h with
    | empty => omega
    | @bin _ r' w0 hp hflag _ hlt hent hrest =>
      refine ⟨w0, hp, fun _ => ⟨hlt, hent, by simp [ModeWatchSliceOk, hdm]; exact hrest⟩,
        fun hz => absurd hz hflag⟩
    | @occ _ r' w0 _ hp _ hflag _ _ _ hrest =>
      refine ⟨w0, hp, fun hne => absurd hflag hne,
        fun _ => ⟨by omega, by simp [ModeWatchSliceOk, hdm]; exact hrest⟩⟩

private theorem exportBinSliceClauses_props {c : FullCfg} {F_cur : List (List Nat)}
    {k : FullCoreState} (hlen : k.LengthsOk c) {l0 : Nat} (hl0 : l0 < 2 * k.cur_vars) :
    ∀ {rem p : Nat}, ModeWatchSliceOk F_cur k l0 p rem →
      (exportBinSliceClauses k.wstk l0 p rem).length ≤ rem ∧
      ((exportBinSliceClauses k.wstk l0 p rem).flatMap emitDimacsClauseBytes).length ≤ 46 * rem ∧
      ∀ cl ∈ exportBinSliceClauses k.wstk l0 p rem,
        (∀ l ∈ cl, l < 2 * k.cur_vars) ∧ (cnfOfClauses F_cur).EntailsClause (cnfClause cl) := by
  intro rem
  induction rem using Nat.strongRecOn with
  | ind rem ih =>
    intro p hslice
    cases rem with
    | zero => simp [exportBinSliceClauses]
    | succ r =>
      obtain ⟨w0, hget, hbin, hlg⟩ := modeWatchSlice_step hslice (Nat.succ_pos r)
      have hmax := c.hmaxv; unfold Ref.dimacsBound at hmax
      have hcv := hlen.cur_vars_le
      have hl0_64 : l0 < 2 ^ 64 := by omega
      unfold exportBinSliceClauses
      rw [hget, Option.getD_some]
      by_cases hflag : (w0 &&& 0x80000000#32) ≠ 0#32
      · rw [ite_eq_left hflag]
        obtain ⟨hl1, hent, hrest⟩ := hbin hflag
        have hrest' : ModeWatchSliceOk F_cur k l0 (p + 1) r := by simpa using hrest
        obtain ⟨hlen_r, hbytes_r, hsound_r⟩ := ih r (by omega) hrest'
        have hl1_64 : (w0 &&& 0x7FFFFFFF#32).toNat < 2 ^ 64 := by omega
        by_cases hlt : l0 < (w0 &&& 0x7FFFFFFF#32).toNat
        · rw [ite_eq_left hlt]
          have hcl_len := emitDimacsClauseBytes_length_le
            (cl := [l0, (w0 &&& 0x7FFFFFFF#32).toNat]) (fun l hl => by
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
              rcases hl with rfl | rfl <;> assumption)
          simp only [List.length_cons, List.length_nil] at hcl_len
          refine ⟨by simp; omega, ?_, ?_⟩
          · simp only [List.flatMap_cons, List.length_append]; omega
          · intro cl hcl
            rcases List.mem_cons.mp hcl with rfl | hmem
            · exact ⟨fun l hl => by
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
                rcases hl with rfl | rfl <;> assumption, hent⟩
            · exact hsound_r cl hmem
        · rw [ite_eq_right hlt]
          exact ⟨by omega, by omega, hsound_r⟩
      · have hz : (w0 &&& 0x80000000#32) = 0#32 :=
          Classical.byContradiction fun hne => hflag hne
        rw [ite_eq_right hflag]
        obtain ⟨hge2, hrest⟩ := hlg hz
        cases r with
        | zero => omega
        | succ r' =>
          have hrest' : ModeWatchSliceOk F_cur k l0 (p + 2) r' := by simpa using hrest
          obtain ⟨hlen_r, hbytes_r, hsound_r⟩ := ih r' (by omega) hrest'
          dsimp only
          exact ⟨by omega, by omega, hsound_r⟩

theorem exportBinClauses_props {c : FullCfg} {F_cur : List (List Nat)} {k : FullCoreState}
    (hlen : k.LengthsOk c) (hw : ModeWatchesInv F_cur k) :
    (exportBinClauses k).length ≤ k.wlen ∧
    ((exportBinClauses k).flatMap emitDimacsClauseBytes).length ≤ 46 * k.wlen ∧
    ∀ cl ∈ exportBinClauses k,
      (∀ l ∈ cl, l < 2 * k.cur_vars) ∧ (cnfOfClauses F_cur).EntailsClause (cnfClause cl) := by
  have hsum := watchStackLayout_sum_sizes_le hw.layout
  have hlen_go : ∀ (xs : List Nat), (∀ l ∈ xs, l < 2 * k.cur_vars) →
      (xs.flatMap fun l0 =>
        exportBinSliceClauses k.wstk l0 (fullWatchOffCore k l0) (fullWatchSizeCore k l0)).length ≤
      (xs.map (fullWatchSizeCore k)).sum ∧
      ((xs.flatMap fun l0 =>
        exportBinSliceClauses k.wstk l0 (fullWatchOffCore k l0)
          (fullWatchSizeCore k l0)).flatMap emitDimacsClauseBytes).length ≤
      46 * (xs.map (fullWatchSizeCore k)).sum ∧
      ∀ cl ∈ (xs.flatMap fun l0 =>
        exportBinSliceClauses k.wstk l0 (fullWatchOffCore k l0) (fullWatchSizeCore k l0)),
        (∀ l ∈ cl, l < 2 * k.cur_vars) ∧ (cnfOfClauses F_cur).EntailsClause (cnfClause cl) := by
    intro xs hxs
    induction xs with
    | nil => simp
    | cons l0 ls ih =>
      have hl0 : l0 < 2 * k.cur_vars := hxs l0 (by simp)
      have h1 := exportBinSliceClauses_props hlen hl0 (modeWatchesInv_slice hw hl0)
      have h2 := ih (fun x hx => hxs x (by simp [hx]))
      simp only [List.flatMap_cons, List.length_append, List.map_cons, List.sum_cons,
        List.flatMap_append]
      refine ⟨by omega, by omega, fun cl hcl => ?_⟩
      rcases List.mem_append.mp hcl with hcl1 | hcl2
      · exact h1.2.2 cl hcl1
      · exact h2.2.2 cl hcl2
  obtain ⟨h1, h2, h3⟩ := hlen_go (List.range (2 * k.cur_vars)) (fun l hl => List.mem_range.mp hl)
  exact ⟨Nat.le_trans h1 hsum, Nat.le_trans h2 (Nat.mul_le_mul_left 46 hsum), h3⟩

private theorem fullArenaClauseGarb_false_of_irredLive {k : FullCoreState} {r : Nat}
    (h : fullArenaClauseIrredLiveCore k r = true) :
    fullArenaClauseGarbCore k r = false := by
  unfold fullArenaClauseIrredLiveCore at h
  have h0 : (fullArenaHdrCore k r &&& 0x00480000#32) = 0#32 := beq_iff_eq.mp h
  have hsub : (0x00480000#32 &&& 0x00080000#32) = 0x00080000#32 := by decide
  have hg : (fullArenaHdrCore k r &&& 0x00080000#32) = 0#32 := by
    rw [← hsub, ← BitVec.and_assoc, h0]; decide
  simp [fullArenaClauseGarbCore, hg]

private theorem exportArenaScan_props {c : FullCfg} {F_cur : List (List Nat)} {k : FullCoreState}
    (hlen : k.LengthsOk c) (ha : FullArenaClausesInv c F_cur k) :
    ∀ (fuel pos : Nat),
      (∀ r ∈ fullArenaScanRefs k.arena k.arena_len pos fuel, r ∈ fullArenaClauseRefsCore k) →
      let cls := ((fullArenaScanRefs k.arena k.arena_len pos fuel).filter
        (fullArenaClauseIrredLiveCore k)).map (fullArenaClauseLitsCore k)
      cls.length ≤ k.arena_len - pos ∧
      (cls.flatMap emitDimacsClauseBytes).length ≤ 22 * (k.arena_len - pos) := by
  intro fuel
  induction fuel with
  | zero => intro pos _; simp [fullArenaScanRefs]
  | succ fuel ih =>
    intro pos hsub
    unfold fullArenaScanRefs
    by_cases hle : pos + 3 ≤ k.arena_len
    · rw [ite_eq_left hle]
      have hpos_mem : pos ∈ fullArenaClauseRefsCore k :=
        hsub pos (by simp [fullArenaScanRefs, hle])
      have hwf := ha.refs_wf pos hpos_mem
      have hrest_sub : ∀ r ∈ fullArenaScanRefs k.arena k.arena_len
          (fullArenaNextOff k.arena k.arena_len pos) fuel, r ∈ fullArenaClauseRefsCore k :=
        fun r hr => hsub r (by simp [fullArenaScanRefs, hle, hr])
      obtain ⟨hl_r, hb_r⟩ := ih (fullArenaNextOff k.arena k.arena_len pos) hrest_sub
      have hstep : pos + 3 + fullArenaClauseSizeCore k pos ≤
          fullArenaNextOff k.arena k.arena_len pos := hwf.2.2.1
      have hnxt_le : fullArenaNextOff k.arena k.arena_len pos ≤ k.arena_len := hwf.2.2.2.1
      have hmax := c.hmaxv; unfold Ref.dimacsBound at hmax
      have hcv := hlen.cur_vars_le
      by_cases hlive : fullArenaClauseIrredLiveCore k pos = true
      · simp only [List.filter_cons, hlive, ↓reduceIte, List.map_cons, List.length_cons,
          List.flatMap_cons, List.length_append]
        have hng := fullArenaClauseGarb_false_of_irredLive hlive
        have hlits_len :
            (fullArenaClauseLitsCore k pos).length = fullArenaClauseSizeCore k pos := by
          unfold fullArenaClauseLitsCore
          rw [List.length_map, List.length_take, List.length_drop]
          have := hlen.arena_len_arr; have := hlen.arena_len_le; omega
        have hcl_b := emitDimacsClauseBytes_length_le (cl := fullArenaClauseLitsCore k pos)
          fun l hl => Nat.lt_trans (ha.lits_lt pos hpos_mem hng l hl) (by omega)
        rw [hlits_len] at hcl_b
        exact ⟨by omega, by omega⟩
      · have hlf : fullArenaClauseIrredLiveCore k pos = false := Bool.eq_false_iff.mpr hlive
        simp only [List.filter_cons, hlf, Bool.false_eq_true, ↓reduceIte]
        exact ⟨by omega, by omega⟩
    · rw [ite_eq_right hle]; simp

theorem exportArenaClauses_props {c : FullCfg} {F_cur : List (List Nat)} {k : FullCoreState}
    (hlen : k.LengthsOk c) (ha : FullArenaClausesInv c F_cur k) :
    (exportArenaClauses k).length ≤ k.arena_len ∧
    ((exportArenaClauses k).flatMap emitDimacsClauseBytes).length ≤ 22 * k.arena_len ∧
    ∀ cl ∈ exportArenaClauses k,
      (∀ l ∈ cl, l < 2 * k.cur_vars) ∧ (cnfOfClauses F_cur).EntailsClause (cnfClause cl) := by
  obtain ⟨h1, h2⟩ := exportArenaScan_props hlen ha k.arena_len 0 (fun _ hr => hr)
  refine ⟨by simpa [exportArenaClauses, fullArenaClauseRefsCore] using h1,
    by simpa [exportArenaClauses, fullArenaClauseRefsCore] using h2, ?_⟩
  intro cl hcl
  unfold exportArenaClauses at hcl
  rw [List.mem_map] at hcl
  obtain ⟨r, hr, rfl⟩ := hcl
  rw [List.mem_filter] at hr
  have hng := fullArenaClauseGarb_false_of_irredLive hr.2
  exact ⟨ha.lits_lt r hr.1 hng, ha.entails r hr.1 hng⟩

theorem exportState_counts_lt {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hlen : k.LengthsOk c) (hw : FullWitnessInv c F0 F_cur k) :
    (exportTrailUnitClauses k).length + (exportBinClauses k).length +
      (exportArenaClauses k).length < 2 ^ 31 ∧
    ((exportTrailUnitClauses k).flatMap emitDimacsClauseBytes).length +
      ((exportBinClauses k).flatMap emitDimacsClauseBytes).length +
      ((exportArenaClauses k).flatMap emitDimacsClauseBytes).length < 2 ^ 36 ∧
    (exportStateBytes k).length < 2 ^ 36 := by
  have ht_l := exportTrailUnitClauses_length hlen
  have ht_b := exportTrailUnitClauses_bytes_le hlen
  obtain ⟨hb_l, hb_b, _⟩ := exportBinClauses_props hlen hw.watches
  obtain ⟨ha_l, ha_b, _⟩ := exportArenaClauses_props hlen hw.arena
  have hmx := c.hmaxv; have har := c.harena; have hwc := c.hwcap
  unfold Ref.dimacsBound at hmx har hwc
  have hcv := hlen.cur_vars_le; have hte := hlen.trail_end_le
  have hal := hlen.arena_len_le; have hwl := hlen.wlen_le
  refine ⟨by omega, by omega, ?_⟩
  unfold exportStateBytes exportStateMv exportStateClauses emitDimacsBytes
  by_cases hinc : k.inconsistent ≠ 0#64
  · rw [ite_eq_left hinc, ite_eq_left hinc]
    decide
  · rw [ite_eq_right hinc, ite_eq_right hinc]
    simp only [List.length_append, List.flatMap_append]
    have hhdr := emitDimacsHdrBytes_length_le_48 (mv := k.cur_vars)
      (nc := (exportTrailUnitClauses k).length + (exportBinClauses k).length +
        (exportArenaClauses k).length) (by omega) (by omega)
    omega

/-- Semantic UNSAT lift from 1-based exported DIMACS `kissatCnfToDimacs clauses` back to
0-based `cnfOfClauses F_cur` whenever every exported clause is entailed by `F_cur`. -/
theorem kissatCnfToDimacs_unsat_of_entails {F_cur clauses : List (List Nat)}
    (hent : ∀ cl ∈ clauses, (cnfOfClauses F_cur).EntailsClause (cnfClause cl))
    (hu : (kissatCnfToDimacs clauses).Unsat) :
    (cnfOfClauses F_cur).Unsat := by
  rw [CNF.unsat_iff_not_sat] at hu ⊢
  intro α hα
  apply hu (fun v => α (v - 1))
  rw [CNF.sat_iff_all_mem_sat]
  intro clD hclD
  rw [CNF.Internal.mem_iff, kissatCnfToDimacs, List.mem_toArray, List.mem_map] at hclD
  obtain ⟨cl, hcl, rfl⟩ := hclD
  have hsat_cl : (cnfClause cl).Sat α := CNF.entails_clause_def.mp (hent cl hcl) α hα
  rw [CNF.Clause.sat_iff_exists_mem_eq] at hsat_cl ⊢
  obtain ⟨⟨v, p⟩, hmem, heq⟩ := hsat_cl
  rw [← CNF.Clause.mem_literals_iff, cnfClause, CNF.Clause.literals_ofLiterals,
    List.mem_map] at hmem
  obtain ⟨l, hl, hlit_eq⟩ := hmem
  cases hlit_eq
  refine ⟨kissatLitToDimacs l, ?_, ?_⟩
  · rw [← CNF.Clause.mem_literals_iff, kissatClauseToDimacs, CNF.Clause.literals_ofLiterals]
    exact List.mem_map.mpr ⟨l, hl, rfl⟩
  · simpa [kissatLitToDimacs, litToLiteral] using heq

/-- Complete pure DIMACS grammar & UNSAT-soundness theorem for `exportStateBytes k` at level 0. -/
theorem exportStateBytes_sound {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hlen : k.LengthsOk c) (hw : FullWitnessInv c F0 F_cur k)
    (hl0 : k.cur_level = 0)
    (hmv : exportStateMv k < dimacsBound)
    (hnc : (exportStateClauses k).length < dimacsBound) :
    let cnfOut := kissatCnfToDimacs (exportStateClauses k)
    parseDimacs (exportStateBytes k) = some cnfOut ∧
    (cnfOut.Unsat → F0.Unsat) := by
  intro cnfOut
  by_cases hinc : k.inconsistent ≠ 0#64
  · have hmv0 : exportStateMv k = 0 := by simp [exportStateMv, hinc]
    have hcls0 : exportStateClauses k = [[]] := by simp [exportStateClauses, hinc]
    refine ⟨?_, fun _ => hw.ext_sound.2 (hw.inconsistent_sound hinc)⟩
    dsimp only [cnfOut]
    unfold exportStateBytes
    rw [hmv0, hcls0]
    exact parseDimacs_emitDimacsBytes (mv := 0) (clauses := [[]])
      (by simp [dimacsBound]) (by simp [dimacsBound]) (by simp)
  · have hmv0 : exportStateMv k = k.cur_vars := by simp [exportStateMv, hinc]
    have hcls0 : exportStateClauses k =
        exportTrailUnitClauses k ++ exportBinClauses k ++ exportArenaClauses k := by
      simp [exportStateClauses, hinc]
    have htrl := exportTrailUnitClauses_sound hlen hw hl0
    have hbin := (exportBinClauses_props hlen hw.watches).2.2
    have harn := (exportArenaClauses_props hlen hw.arena).2.2
    have hall : ∀ cl ∈ exportStateClauses k,
        (∀ l ∈ cl, l < 2 * k.cur_vars) ∧ (cnfOfClauses F_cur).EntailsClause (cnfClause cl) := by
      intro cl hcl
      rw [hcls0] at hcl
      simp only [List.mem_append] at hcl
      rcases hcl with (h1 | h2) | h3
      · exact htrl cl h1
      · exact hbin cl h2
      · exact harn cl h3
    have hvars : ∀ cl ∈ exportStateClauses k, ∀ l ∈ cl, litVar l < exportStateMv k := by
      intro cl hcl l hl
      rw [hmv0]
      exact Nat.div_lt_of_lt_mul ((hall cl hcl).1 l hl)
    exact ⟨parseDimacs_emitDimacsBytes hmv hnc hvars,
      fun hu => hw.ext_sound.2
        (kissatCnfToDimacs_unsat_of_entails (fun cl hcl => (hall cl hcl).2) hu)⟩

/-- 1-based input DIMACS corollary (`F0 = shiftDownCnf cnfIn`, `CnfVarsPos cnfIn`):
unsatisfiability of the exported simplified CNF directly proves `cnfIn.Unsat`. -/
theorem exportStateBytes_sound_dimacs {c : FullCfg} {cnfIn : CNF Nat}
    {F_cur : List (List Nat)} {k : FullCoreState}
    (hlen : k.LengthsOk c) (hpos : CnfVarsPos cnfIn)
    (hw : FullWitnessInv c (shiftDownCnf cnfIn) F_cur k)
    (hl0 : k.cur_level = 0)
    (hmv : exportStateMv k < dimacsBound)
    (hnc : (exportStateClauses k).length < dimacsBound) :
    let cnfOut := kissatCnfToDimacs (exportStateClauses k)
    parseDimacs (exportStateBytes k) = some cnfOut ∧
    (cnfOut.Unsat → cnfIn.Unsat) := by
  obtain ⟨hp, hu⟩ := exportStateBytes_sound hlen hw hl0 hmv hnc
  exact ⟨hp, fun h => shiftDownCnf_unsat hpos (hu h)⟩

/-! ## 3. Parametric `(Γ : Env)` WP Proofs for All Five C0 Functions -/

private theorem sep_bytes_nil_intro {P : Mem 64 → Prop} {out : BitVec 64} {m : Mem 64}
    (h : P m) : (bytes out [] ⋆ P) m := by
  change (Eq (([] : List UInt8).At out) ⋆ P) m
  rw [← eq_nil_At out, emp_sep]; exact h

private theorem sep_bytes_nil_elim {P : Mem 64 → Prop} {out : BitVec 64} {m : Mem 64}
    (h : (bytes out [] ⋆ P) m) : P m := by
  change (Eq (([] : List UInt8).At out) ⋆ P) m at h
  rwa [← eq_nil_At out, emp_sep] at h

private theorem full_frame_ac {c : FullCfg} {s : FullState} {out ptr v : BitVec 64}
    {buf : List UInt8} {R : Mem 64 → Prop} {m : Mem 64}
    (h : (FullMem c s ⋆ bytes out buf ⋆ cell64 ptr v ⋆ R) m) :
    (FullMem c s ⋆ (bytes out buf ⋆ cell64 ptr v ⋆ R)) m := sep_ac h

private theorem load_cnt_from_full {c : FullCfg} {s : FullState} {out ptr v : BitVec 64}
    {buf : List UInt8} {R : Mem 64 → Prop} {m : Mem 64}
    (h : (FullMem c s ⋆ bytes out buf ⋆ cell64 ptr v ⋆ R) m) :
    loadVal m i64 ptr = some v :=
  loadVal_cell64 (R := FullMem c s ⋆ bytes out buf ⋆ R) (sep_ac h)

private theorem store_cnt_from_full {c : FullCfg} {s : FullState} {out ptr v0 : BitVec 64}
    (v : BitVec 64) {buf : List UInt8} {R : Mem 64 → Prop} {m : Mem 64}
    (h : (FullMem c s ⋆ bytes out buf ⋆ cell64 ptr v0 ⋆ R) m) :
    storeOk m i64 ptr ∧
      (FullMem c s ⋆ bytes out buf ⋆ cell64 ptr v ⋆ R) (storeMem m i64 ptr v) := by
  obtain ⟨hok, hst⟩ := store_cell64 (R := FullMem c s ⋆ bytes out buf ⋆ R) v (sep_ac h)
  exact ⟨hok, sep_ac hst⟩

private theorem wp_load_cnt {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {c : FullCfg} {s : FullState} {out ptr v : BitVec 64}
    {buf : List UInt8} {R : Mem 64 → Prop} {m : Mem 64} {k : Val i64 → Expr Val Cont rs}
    (h : (FullMem c s ⋆ bytes out buf ⋆ cell64 ptr v ⋆ R) m)
    (hk : wp Γ Q X (k v) m) :
    wp Γ Q X (.load i64 (.var ptr) k) m :=
  wp_load_of (load_cnt_from_full h) hk

private theorem wp_store_cnt {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {c : FullCfg} {s : FullState} {out ptr v0 : BitVec 64} {v : Arg Val i64}
    {buf : List UInt8} {R : Mem 64 → Prop} {m : Mem 64} {k : Expr Val Cont rs}
    (h : (FullMem c s ⋆ bytes out buf ⋆ cell64 ptr v0 ⋆ R) m)
    (hk : ∀ m', (FullMem c s ⋆ bytes out buf ⋆ cell64 ptr v.val ⋆ R) m' → wp Γ Q X k m') :
    wp Γ Q X (.store v (.var ptr) k) m :=
  wp_store_sep (store_cnt_from_full v.val h) hk

/-- Helper lemma stepping a single `kissat_emit_byte` call while preserving `FullMem` + `cell64`. -/
private theorem call_emit_byte {Γ : Env}
    (hByte : ∀ a m Q X, kissatEmitByteSpec a m Q X →
      Γ "kissat_emit_byte" [i64, i64, i64, i64] [i64] a m Q X)
    {c : FullCfg} {s : FullState} {out ptr v b : BitVec 64}
    {buf pre : List UInt8} {pos0 : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (hcap : buf.length < 2 ^ 64) (hpos : pos0 + pre.length + 1 < 2 ^ 64)
    (hm : (FullMem c s ⋆ bytes out (writeSlice buf pos0 pre) ⋆ cell64 ptr v ⋆ R) m)
    (hQ : ∀ m',
      (FullMem c s ⋆ bytes out (writeSlice buf pos0 (pre ++ [UInt8.ofNat b.toNat])) ⋆
        cell64 ptr v ⋆ R) m' →
      Q (BitVec.ofNat 64 (pos0 + (pre ++ [UInt8.ofNat b.toNat]).length), ()) m') :
    Γ "kissat_emit_byte" [i64, i64, i64, i64] [i64]
      (out, BitVec.ofNat 64 buf.length, BitVec.ofNat 64 (pos0 + pre.length), b, ()) m Q X := by
  apply hByte
  have hwl : (writeSlice buf pos0 pre).length = buf.length := writeSlice_length buf pos0 pre
  refine ⟨out, writeSlice buf pos0 pre, pos0 + pre.length, b,
    FullMem c s ⋆ cell64 ptr v ⋆ R, by rw [hwl], by rw [hwl]; exact hcap, hpos, sep_ac hm,
    fun m' _ hm' => ?_⟩
  rw [← writeSlice_append] at hm'
  have hlen : pos0 + (pre ++ [UInt8.ofNat b.toNat]).length = pos0 + pre.length + 1 := by simp; omega
  rw [← hlen]
  exact hQ m' (sep_ac hm')

/-- Helper lemma stepping a single `kissat_emit_dimacs_lit` call while preserving `FullMem` +
`cell64`. -/
private theorem call_emit_lit {Γ : Env}
    (hLit : ∀ a m Q X, kissatEmitDimacsLitSpec a m Q X →
      Γ "kissat_emit_dimacs_lit" [i64, i64, i64, i64] [i64] a m Q X)
    {c : FullCfg} {s : FullState} {out ptr v lit : BitVec 64}
    {buf pre : List UInt8} {pos0 : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (hcap : buf.length < 2 ^ 64)
    (hpos : pos0 + pre.length + (emitDimacsLitBytes lit.toNat).length < 2 ^ 64)
    (hm : (FullMem c s ⋆ bytes out (writeSlice buf pos0 pre) ⋆ cell64 ptr v ⋆ R) m)
    (hQ : ∀ m',
      (FullMem c s ⋆ bytes out (writeSlice buf pos0 (pre ++ emitDimacsLitBytes lit.toNat)) ⋆
        cell64 ptr v ⋆ R) m' →
      Q (BitVec.ofNat 64 (pos0 + (pre ++ emitDimacsLitBytes lit.toNat).length), ()) m') :
    Γ "kissat_emit_dimacs_lit" [i64, i64, i64, i64] [i64]
      (out, BitVec.ofNat 64 buf.length, BitVec.ofNat 64 (pos0 + pre.length), lit, ()) m Q X := by
  apply hLit
  have hwl : (writeSlice buf pos0 pre).length = buf.length := writeSlice_length buf pos0 pre
  refine ⟨out, writeSlice buf pos0 pre, pos0 + pre.length, lit,
    FullMem c s ⋆ cell64 ptr v ⋆ R, by rw [hwl], by rw [hwl]; exact hcap, hpos, sep_ac hm,
    fun m' _ hm' => ?_⟩
  rw [← writeSlice_append] at hm'
  have hlen : pos0 + (pre ++ emitDimacsLitBytes lit.toNat).length =
      pos0 + pre.length + (emitDimacsLitBytes lit.toNat).length := by simp; omega
  rw [← hlen]
  exact hQ m' (sep_ac hm')

private theorem bv32_setWidth64_toNat (x : BitVec 32) : (x.setWidth 64).toNat = x.toNat := by
  have hx : x.toNat < 2 ^ 64 := lt_trans x.isLt (by decide : 2 ^ 32 < 2 ^ 64)
  simp [BitVec.toNat_setWidth, Nat.mod_eq_of_lt hx]

/-! ### 3.1 `kissat_export_arena_next` -/

theorem kissat_export_arena_next_wp (Γ : Env) :
    ∀ args m Q X, kissatExportArenaNextSpec args m Q X →
      Func.wp Γ kissat_export_arena_next_body args m Q X := by
  rintro args m Q X ⟨c, s, cref, R, rfl, hlen, hcref_le, hm, hQ⟩
  have hcl := hlen.core_ok
  have har_len := hcl.arena_len_arr
  have hale := hcl.arena_len_le
  have hcap := c.harena; unfold Ref.dimacsBound at hcap
  have hcref_lt64 : cref.toNat + 3 < 2 ^ 64 := by omega
  have hal_lt64 : s.core.arena_len < 2 ^ 64 := by omega
  unfold Func.wp kissat_export_arena_next_body; dsimp only
  c0_hsteps_nogrp
  · have hgt : cref.toNat + 3 > s.core.arena_len := by c0_bound
    simpa [fullArenaNextOff, hgt] using hQ
  · rename_i hle3_c
    have hle3 : cref.toNat + 3 ≤ s.core.arena_len := by
      change ¬ s.core.arena_len % 2 ^ 64 < (cref.toNat + 3) % 2 ^ 64 at hle3_c
      rw [Nat.mod_eq_of_lt hal_lt64, Nat.mod_eq_of_lt hcref_lt64] at hle3_c
      omega
    have hcref2_lt : cref.toNat + 2 < s.core.arena.length := by omega
    have hsz32 := (s.core.arena[cref.toNat + 2]'hcref2_lt).isLt
    have hgtp :
        cref.toNat + 3 + (s.core.arena[cref.toNat + 2]'hcref2_lt).toNat > s.core.arena_len := by
      have hc' := hc
      have h2 : (cref.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64 = cref.toNat + 2 := by
        change (cref.toNat + 2) % 2 ^ 64 = cref.toNat + 2; exact Nat.mod_eq_of_lt (by omega)
      simp only [h2, show BitVec.toNat (3 : BitVec 64) = 3 from rfl, Nat.mod_eq_of_lt hal_lt64,
        Nat.mod_eq_of_lt (by omega :
          cref.toNat + 3 + (s.core.arena[cref.toNat + 2]'hcref2_lt).toNat < 2 ^ 64)] at hc'
      omega
    simpa [fullArenaNextOff, show ¬ (cref.toNat + 3 > s.core.arena_len) by omega,
      List.getElem?_eq_getElem hcref2_lt, hgtp] using hQ
  · rename_i hle3_c
    have hle3 : cref.toNat + 3 ≤ s.core.arena_len := by
      change ¬ s.core.arena_len % 2 ^ 64 < (cref.toNat + 3) % 2 ^ 64 at hle3_c
      rw [Nat.mod_eq_of_lt hal_lt64, Nat.mod_eq_of_lt hcref_lt64] at hle3_c
      omega
    have hcref_lt : cref.toNat < s.core.arena.length := by omega
    have hcref2_lt : cref.toNat + 2 < s.core.arena.length := by omega
    have hsz32 := (s.core.arena[cref.toNat + 2]'hcref2_lt).isLt
    have hlep :
        cref.toNat + 3 + (s.core.arena[cref.toNat + 2]'hcref2_lt).toNat ≤ s.core.arena_len := by
      have hc' := hc
      have h2 : (cref.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64 = cref.toNat + 2 := by
        change (cref.toNat + 2) % 2 ^ 64 = cref.toNat + 2; exact Nat.mod_eq_of_lt (by omega)
      simp only [h2, show BitVec.toNat (3 : BitVec 64) = 3 from rfl, Nat.mod_eq_of_lt hal_lt64,
        Nat.mod_eq_of_lt (by omega :
          cref.toNat + 3 + (s.core.arena[cref.toNat + 2]'hcref2_lt).toNat < 2 ^ 64)] at hc'
      omega
    let p0 := cref.toNat + 3 + (s.core.arena[cref.toNat + 2]'hcref2_lt).toNat
    have hp0_bv :
        cref + 3 + (s.core.arena[(cref + 2).toNat]'(by c0_bound)).setWidth 64 =
        BitVec.ofNat 64 p0 := by
      have hsub : (cref + 2).toNat = cref.toNat + 2 := by c0_bound
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, bv32_setWidth64_toNat, hsub]
      change ((cref.toNat + 3) % 2 ^ 64 + (s.core.arena[cref.toNat + 2]'hcref2_lt).toNat) % 2 ^ 64 =
        p0 % 2 ^ 64
      rw [Nat.mod_eq_of_lt hcref_lt64]
    refine wp_join_state_pure (ts := [i64]) (α := Unit)
      (proj := fun _ =>
        (BitVec.ofNat 64 (fullArenaNextOff s.core.arena s.core.arena_len cref.toNat), ()))
      (Inv := fun _ => True)
      (fun _ _ _ => by c0_hsteps_nogrp; exact hQ)
      (fun Jshrk hJshrk => ?_)
    c0_hsteps_nogrp
    · have hshrk : s.core.arena[cref.toNat]'hcref_lt &&& 0x00800000#32 ≠ 0#32 := hc
      have hnext_eq : fullArenaNextOff s.core.arena s.core.arena_len cref.toNat =
          fullArenaSkipShrk s.core.arena s.core.arena_len p0 (s.core.arena_len - p0) := by
        unfold fullArenaNextOff
        simp only [show ¬ (cref.toNat + 3 > s.core.arena_len) by omega, ↓reduceIte,
          List.getElem?_eq_getElem hcref_lt, List.getElem?_eq_getElem hcref2_lt, Option.getD_some,
          show ¬ (cref.toNat + 3 +
            (s.core.arena[cref.toNat + 2]'hcref2_lt).toNat > s.core.arena_len) by omega,
          hshrk, ne_eq, not_false_eq_true]
        rfl
      refine wp_while_state_pure (ts := [i64]) (α := Nat)
        (proj := fun p => (BitVec.ofNat 64 p, ()))
        (μ := fun p => s.core.arena_len - p)
        (Inv := fun p => p ≤ s.core.arena_len ∧
          fullArenaSkipShrk s.core.arena s.core.arena_len p (s.core.arena_len - p) =
            fullArenaSkipShrk s.core.arena s.core.arena_len p0 (s.core.arena_len - p0))
        (fun J hLoop => ?_) (fun J p ⟨hple, hskip⟩ hLoop => ?_)
      · c0_hsteps_nogrp
        rw [hp0_bv]
        exact hLoop p0 ⟨hlep, rfl⟩
      · c0_hsteps
        · rename_i hlt_c
          have hplt : p < s.core.arena_len := by c0_bound
          have hpar : p < s.core.arena.length := by omega
          have hne : s.core.arena[p]'hpar ≠ 0xFFFFFFFF#32 := by
            simpa [Nat.mod_eq_of_lt (by omega : p < 2 ^ 64)] using hc
          have hstep : fullArenaSkipShrk s.core.arena s.core.arena_len (p + 1)
              (s.core.arena_len - (p + 1)) =
              fullArenaSkipShrk s.core.arena s.core.arena_len p (s.core.arena_len - p) := by
            have hs : s.core.arena_len - p = (s.core.arena_len - (p + 1)) + 1 := by omega
            conv => rhs; rw [hs]; unfold fullArenaSkipShrk
            simp [hplt, List.getElem?_eq_getElem hpar, hne]
          rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, bv_add_ofNat]
          exact hLoop (p + 1) (by omega) ⟨by omega, by rw [hstep, hskip]⟩
        · rename_i hlt_c hsent_c
          have hplt : p < s.core.arena_len := by c0_bound
          have hpar : p < s.core.arena.length := by omega
          have heq_sent : s.core.arena[p]'hpar = 0xFFFFFFFF#32 := by
            simpa [Nat.mod_eq_of_lt (by omega : p < 2 ^ 64)] using hsent_c
          have hstep : fullArenaSkipShrk s.core.arena s.core.arena_len p
              (s.core.arena_len - p) = p + 1 := by
            have hs : s.core.arena_len - p = (s.core.arena_len - (p + 1)) + 1 := by omega
            conv => lhs; rw [hs]; unfold fullArenaSkipShrk
            simp [hplt, List.getElem?_eq_getElem hpar, heq_sent]
          rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, bv_add_ofNat, show p + 1 =
              fullArenaNextOff s.core.arena s.core.arena_len cref.toNat by
            rw [hnext_eq, ← hskip, hstep]]
          exact hJshrk () trivial
        · have hpe : p = s.core.arena_len := by c0_bound
          have hstep : fullArenaSkipShrk s.core.arena s.core.arena_len p
              (s.core.arena_len - p) = s.core.arena_len := by
            simp [hpe, fullArenaSkipShrk]
          rw [show p = fullArenaNextOff s.core.arena s.core.arena_len cref.toNat by
            rw [hnext_eq, ← hskip, hstep, hpe]]
          exact hJshrk () trivial
    · have hnoshrk : s.core.arena[cref.toNat]'hcref_lt &&& 0x00800000#32 = 0#32 := hc
      have hnext_eq : fullArenaNextOff s.core.arena s.core.arena_len cref.toNat = p0 := by
        unfold fullArenaNextOff
        simp [p0, show ¬ (cref.toNat + 3 > s.core.arena_len) by omega,
          List.getElem?_eq_getElem hcref_lt, List.getElem?_eq_getElem hcref2_lt,
          show ¬ (cref.toNat + 3 +
            (s.core.arena[cref.toNat + 2]'hcref2_lt).toNat > s.core.arena_len) by omega,
          hnoshrk]
      rw [hp0_bv, ← hnext_eq]
      exact hJshrk () trivial

/-! ### 3.2 `kissat_export_trail_units` -/

private def trailPrefixBytes (k : FullCoreState) (i : Nat) : List UInt8 :=
  (((k.trl.take i).map BitVec.toNat).map fun l => [l]).flatMap emitDimacsClauseBytes

private theorem trailPrefixBytes_zero (k : FullCoreState) :
    trailPrefixBytes k 0 = [] := rfl

private theorem trailPrefixBytes_succ {k : FullCoreState} {i : Nat} (hi : i < k.trl.length) :
    trailPrefixBytes k (i + 1) =
      trailPrefixBytes k i ++
        (emitDimacsLitBytes (k.trl[i]'hi).toNat ++ [48, 10]) := by
  unfold trailPrefixBytes
  rw [List.take_add_one, List.getElem?_eq_getElem hi]
  simp only [Option.toList_some, List.map_append, List.map_cons, List.map_nil,
    List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    emitDimacsClauseBytes, asciiZero, asciiNewline]
  rfl

private theorem trailPrefixBytes_mono_len {k : FullCoreState} {i j : Nat}
    (hij : i ≤ j) (hj : j ≤ k.trl.length) :
    (trailPrefixBytes k i).length ≤ (trailPrefixBytes k j).length := by
  induction j with
  | zero =>
    have hi0 : i = 0 := by omega
    subst hi0; exact Nat.le_refl _
  | succ j ih =>
    by_cases h : i = j + 1
    · subst h; exact Nat.le_refl _
    · rw [trailPrefixBytes_succ (by omega), List.length_append]
      have := ih (by omega) (by omega)
      omega

theorem kissat_export_trail_units_wp (Γ : Env)
    (hByte : ∀ a m Q X, kissatEmitByteSpec a m Q X →
      Γ "kissat_emit_byte" [i64, i64, i64, i64] [i64] a m Q X)
    (hLit : ∀ a m Q X, kissatEmitDimacsLitSpec a m Q X →
      Γ "kissat_emit_dimacs_lit" [i64, i64, i64, i64] [i64] a m Q X) :
    ∀ args m Q X, kissatExportTrailUnitsSpec args m Q X →
      Func.wp Γ kissat_export_trail_units_body args m Q X := by
  rintro args m Q X ⟨c, s, out, cnt_ptr, buf, pos0, cnt0, R, rfl, hlen, hcap, hpos_fit, hcnt_fit,
    hm, hQ⟩
  have hcl := hlen.core_ok
  have htrl_len := hcl.trl_len
  have hte_le := hcl.trail_end_le
  have hcv_le := hcl.cur_vars_le
  have hmx := c.hmaxv; unfold Ref.dimacsBound at hmx
  have hte_lt64 : s.core.trail_end < 2 ^ 64 := by omega
  have hmF : (FullMem c s ⋆ (bytes out buf ⋆ cell64 cnt_ptr (BitVec.ofNat 64 cnt0) ⋆ R)) m :=
    full_frame_ac hm
  unfold Func.wp kissat_export_trail_units_body; dsimp only
  c0_hsteps_nogrp
  refine wp_while_state (ts := [i64, i64]) (α := Nat)
    (proj := fun i =>
      (BitVec.ofNat 64 (pos0 + (trailPrefixBytes s.core i).length), BitVec.ofNat 64 i, ()))
    (μ := fun i => s.core.trail_end - i)
    (Inv := fun i m1 =>
      i ≤ s.core.trail_end ∧
      (FullMem c s ⋆ bytes out (writeSlice buf pos0 (trailPrefixBytes s.core i)) ⋆
        cell64 cnt_ptr (BitVec.ofNat 64 cnt0) ⋆ R) m1)
    (fun J hLoop => ?_) (fun J i m1 ⟨hile, hm1⟩ hLoop => ?_)
  · c0_hsteps_nogrp
    have h0 := hLoop 0 m ⟨Nat.zero_le _,
      by simpa [trailPrefixBytes_zero, writeSlice_nil] using hm⟩
    simpa [trailPrefixBytes_zero] using h0
  · have hm1F : (FullMem c s ⋆
        (bytes out (writeSlice buf pos0 (trailPrefixBytes s.core i)) ⋆
          cell64 cnt_ptr (BitVec.ofNat 64 cnt0) ⋆ R)) m1 := full_frame_ac hm1
    c0_hsteps_nogrp
    · have hilt : i < s.core.trail_end := by c0_bound
      have hi_trl : i < s.core.trl.length := by omega
      have hpre_succ := trailPrefixBytes_succ hi_trl
      have hlen_succ_le : (trailPrefixBytes s.core (i + 1)).length ≤
          ((exportTrailUnitClauses s.core).flatMap emitDimacsClauseBytes).length :=
        trailPrefixBytes_mono_len (by omega) (by omega)
      rw [hpre_succ, List.length_append, List.length_append, List.length_cons,
        List.length_cons, List.length_nil] at hlen_succ_le
      have hlit_bv : ((s.core.trl[(BitVec.ofNat 64 i).toNat]'(by c0_bound)).setWidth 64).toNat =
          (s.core.trl[i]'hi_trl).toNat := by
        rw [bv32_setWidth64_toNat]
        simp [Nat.mod_eq_of_lt (by omega : i < 2 ^ 64)]
      refine wp_call_of_spec _ _ (call_emit_lit hLit hcap
        (by dsimp only [Arg.val]; rw [hlit_bv]; omega) hm1 fun m2 hm2 => ?_)
      dsimp only [Arg.val] at hm2 ⊢
      refine wp_call_of_spec _ _ (call_emit_byte hByte hcap
        (by simp only [List.length_append, hlit_bv]; omega) hm2 fun m3 hm3 => ?_)
      dsimp only [Arg.val] at hm3 ⊢
      refine wp_call_of_spec _ _ (call_emit_byte hByte hcap
        (by simp only [List.length_append, List.length_singleton, hlit_bv]; omega) hm3
        fun m4 hm4 => ?_)
      c0_hsteps_nogrp
      dsimp only [Arg.val] at hm4 ⊢
      have hpre_eq : trailPrefixBytes s.core i ++
          emitDimacsLitBytes
            ((s.core.trl[(BitVec.ofNat 64 i).toNat]'(by c0_bound)).setWidth 64).toNat ++
          [UInt8.ofNat (BitVec.toNat (48 : BitVec 64))] ++
          [UInt8.ofNat (BitVec.toNat (10 : BitVec 64))] =
          trailPrefixBytes s.core (i + 1) := by
        rw [hlit_bv, hpre_succ, List.append_assoc, List.append_assoc]
        rfl
      rw [hpre_eq] at hm4 ⊢
      rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, bv_add_ofNat]
      exact hLoop (i + 1) m4 (by omega) ⟨by omega, hm4⟩
    · have hieq : i = s.core.trail_end := by c0_bound
      subst hieq
      refine wp_load_cnt hm1 ?_
      c0_hsteps_nogrp
      have hsum_bv : BitVec.ofNat 64 cnt0 + BitVec.ofNat 64 s.core.trail_end =
          BitVec.ofNat 64 (cnt0 + s.core.trail_end) := bv_add_ofNat cnt0 s.core.trail_end
      rw [hsum_bv]
      refine wp_store_cnt hm1 fun m2 hm2 => ?_
      c0_hsteps_nogrp
      exact hQ m2 hm2

/-! ### 3.3 `kissat_export_bin_clauses` -/

private def binPrefixClauses (k : FullCoreState) (n : Nat) : List (List Nat) :=
  (List.range n).flatMap fun l0 =>
    exportBinSliceClauses k.wstk l0 (fullWatchOffCore k l0) (fullWatchSizeCore k l0)

private theorem binPrefixClauses_zero (k : FullCoreState) :
    binPrefixClauses k 0 = [] := rfl

private theorem binPrefixClauses_succ (k : FullCoreState) (n : Nat) :
    binPrefixClauses k (n + 1) =
      binPrefixClauses k n ++
        exportBinSliceClauses k.wstk n (fullWatchOffCore k n) (fullWatchSizeCore k n) := by
  unfold binPrefixClauses
  rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]

private theorem binPrefixClauses_mono_len (k : FullCoreState) {i j : Nat} (hij : i ≤ j) :
    (binPrefixClauses k i).length ≤ (binPrefixClauses k j).length ∧
    ((binPrefixClauses k i).flatMap emitDimacsClauseBytes).length ≤
      ((binPrefixClauses k j).flatMap emitDimacsClauseBytes).length := by
  induction j with
  | zero =>
    have hi0 : i = 0 := by omega
    subst hi0; exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  | succ j ih =>
    by_cases h : i = j + 1
    · subst h; exact ⟨Nat.le_refl _, Nat.le_refl _⟩
    · have hih := ih (by omega)
      rw [binPrefixClauses_succ, List.length_append, List.flatMap_append, List.length_append]
      exact ⟨by omega, by omega⟩

theorem kissat_export_bin_clauses_wp (Γ : Env)
    (hByte : ∀ a m Q X, kissatEmitByteSpec a m Q X →
      Γ "kissat_emit_byte" [i64, i64, i64, i64] [i64] a m Q X)
    (hLit : ∀ a m Q X, kissatEmitDimacsLitSpec a m Q X →
      Γ "kissat_emit_dimacs_lit" [i64, i64, i64, i64] [i64] a m Q X) :
    ∀ args m Q X, kissatExportBinClausesSpec args m Q X →
      Func.wp Γ kissat_export_bin_clauses_body args m Q X := by
  rintro args m Q X ⟨c, F_cur, s, out, cnt_ptr, buf, pos0, cnt0, R, rfl, hlen, hwat,
    hcap, hpos_fit, hcnt_fit, hm, hQ⟩
  have hcl := hlen.core_ok
  have hwvec_len := hcl.wvec_len
  have hwstk_len := hcl.wstk_len_arr
  have hwlen_le := hcl.wlen_le
  have hcv_le := hcl.cur_vars_le
  have hmx := c.hmaxv; have hwc := c.hwcap; unfold Ref.dimacsBound at hmx hwc
  have hmF : (FullMem c s ⋆ (bytes out buf ⋆ cell64 cnt_ptr (BitVec.ofNat 64 cnt0) ⋆ R)) m :=
    full_frame_ac hm
  unfold Func.wp kissat_export_bin_clauses_body; dsimp only
  c0_hsteps_nogrp
  refine wp_load_cnt hm ?_
  dsimp only
  refine wp_while_state (ts := [i64, i64, i64]) (α := Nat)
    (proj := fun l0 =>
      let preCls := binPrefixClauses s.core l0
      let preBs := preCls.flatMap emitDimacsClauseBytes
      (BitVec.ofNat 64 (pos0 + preBs.length), BitVec.ofNat 64 (cnt0 + preCls.length),
        BitVec.ofNat 64 l0, ()))
    (μ := fun l0 => 2 * s.core.cur_vars - l0)
    (Inv := fun l0 m1 =>
      l0 ≤ 2 * s.core.cur_vars ∧
      (FullMem c s ⋆
        bytes out (writeSlice buf pos0
          ((binPrefixClauses s.core l0).flatMap emitDimacsClauseBytes)) ⋆
        cell64 cnt_ptr (BitVec.ofNat 64 cnt0) ⋆ R) m1)
    (fun J hLoop => ?_) (fun J l0 m1 ⟨hl0_le, hm1⟩ hLoop => ?_)
  · c0_hsteps_nogrp
    have h0 := hLoop 0 m ⟨Nat.zero_le _,
      by simpa [binPrefixClauses_zero, writeSlice_nil] using hm⟩
    simpa [binPrefixClauses_zero] using h0
  · have hm1F : (FullMem c s ⋆
        (bytes out (writeSlice buf pos0
          ((binPrefixClauses s.core l0).flatMap emitDimacsClauseBytes))
          ⋆ cell64 cnt_ptr (BitVec.ofNat 64 cnt0) ⋆ R)) m1 := full_frame_ac hm1
    c0_hsteps_nogrp
    · have hl0_lt : l0 < 2 * s.core.cur_vars := by c0_bound
      have h2l0_lt : 2 * l0 < s.core.wvec.length := by omega
      have h2l1_lt : 2 * l0 + 1 < s.core.wvec.length := by omega
      have hidx0 : (l0 * 2) % 2 ^ 64 = 2 * l0 := by
        rw [Nat.mul_comm, Nat.mod_eq_of_lt (by omega)]
      have hidx1 : (l0 * 2 + 1) % 2 ^ 64 = 2 * l0 + 1 := by
        rw [Nat.mul_comm, Nat.mod_eq_of_lt (by omega)]
      have hoff_eq : ((s.core.wvec[(l0 * 2) % 2 ^ 64]'(by rw [hidx0]; exact h2l0_lt)).setWidth 64) =
          BitVec.ofNat 64 (fullWatchOffCore s.core l0) := by
        unfold fullWatchOffCore
        apply BitVec.eq_of_toNat_eq
        simp only [bv32_setWidth64_toNat, hidx0, List.getElem?_eq_getElem h2l0_lt, Option.getD_some,
          BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (lt_trans (s.core.wvec[2 * l0]'h2l0_lt).isLt
            (by decide : 2 ^ 32 < 2 ^ 64))]
      have hsz_eq :
          ((s.core.wvec[(l0 * 2 + 1) % 2 ^ 64]'(by rw [hidx1]; exact h2l1_lt)).setWidth 64) =
          BitVec.ofNat 64 (fullWatchSizeCore s.core l0) := by
        unfold fullWatchSizeCore
        apply BitVec.eq_of_toNat_eq
        simp only [bv32_setWidth64_toNat, hidx1, List.getElem?_eq_getElem h2l1_lt, Option.getD_some,
          BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt
            (lt_trans (s.core.wvec[2 * l0 + 1]'h2l1_lt).isLt (by decide : 2 ^ 32 < 2 ^ 64))]
      have hwb := hwat.bounds l0 hl0_lt
      have hslice0 := modeWatchesInv_slice hwat hl0_lt
      let off0 := fullWatchOffCore s.core l0
      let sz0 := fullWatchSizeCore s.core l0
      let end0 := off0 + sz0
      let pre0 := binPrefixClauses s.core l0
      let fullSlice := exportBinSliceClauses s.core.wstk l0 off0 sz0
      have hsucc_bound := binPrefixClauses_mono_len s.core (i := l0 + 1) (j := 2 * s.core.cur_vars)
        (by omega)
      rw [binPrefixClauses_succ] at hsucc_bound
      have htot_cnt : cnt0 + pre0.length + fullSlice.length < 2 ^ 64 := by
        have h1 := hsucc_bound.1; rw [List.length_append] at h1
        change pre0.length + fullSlice.length ≤ (exportBinClauses s.core).length at h1
        omega
      have htot_pos : pos0 + (pre0.flatMap emitDimacsClauseBytes).length +
          (fullSlice.flatMap emitDimacsClauseBytes).length < 2 ^ 64 := by
        have h2 := hsucc_bound.2; rw [List.flatMap_append, List.length_append] at h2
        change (pre0.flatMap emitDimacsClauseBytes).length +
          (fullSlice.flatMap emitDimacsClauseBytes).length ≤
          ((exportBinClauses s.core).flatMap emitDimacsClauseBytes).length at h2
        omega
      have hl0_m : l0 % 2 ^ 64 = l0 := Nat.mod_eq_of_lt (by omega)
      have hidx0' : l0 % 2 ^ 64 * BitVec.toNat (2 : BitVec 64) % 2 ^ 64 = 2 * l0 := by
        rw [hl0_m]; exact hidx0
      have hidx1' :
          (l0 % 2 ^ 64 * BitVec.toNat (2 : BitVec 64) + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 =
          2 * l0 + 1 := by
        rw [hl0_m]; exact hidx1
      have hend_nat :
          ((s.core.wvec[l0 % 2 ^ 64 * BitVec.toNat (2 : BitVec 64) % 2 ^ 64]'(by
              rw [hidx0']; exact h2l0_lt)).toNat +
           (s.core.wvec[(l0 % 2 ^ 64 * BitVec.toNat (2 : BitVec 64) +
              BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
              rw [hidx1']; exact h2l1_lt)).toNat) % 2 ^ 64 = end0 := by
        simp only [hidx0', hidx1']
        have h1 : (s.core.wvec[2 * l0]'h2l0_lt).toNat = off0 := by
          simp [off0, fullWatchOffCore, List.getElem?_eq_getElem h2l0_lt]
        have h2 : (s.core.wvec[2 * l0 + 1]'h2l1_lt).toNat = sz0 := by
          simp [sz0, fullWatchSizeCore, List.getElem?_eq_getElem h2l1_lt]
        rw [h1, h2]
        exact Nat.mod_eq_of_lt (by omega)
      refine wp_while_state (ts := [i64, i64, i64]) (α := Nat × Nat × List (List Nat))
        (proj := fun (p, _, doneCls) =>
          (BitVec.ofNat 64 (pos0 + ((pre0 ++ doneCls).flatMap emitDimacsClauseBytes).length),
            BitVec.ofNat 64 (cnt0 + (pre0 ++ doneCls).length),
            BitVec.ofNat 64 p, ()))
        (μ := fun (p, _, _) => end0 - p)
        (Inv := fun (p, rem, doneCls) mi =>
          p + rem = end0 ∧
          ModeWatchSliceOk F_cur s.core l0 p rem ∧
          doneCls ++ exportBinSliceClauses s.core.wstk l0 p rem = fullSlice ∧
          (FullMem c s ⋆
            bytes out (writeSlice buf pos0 ((pre0 ++ doneCls).flatMap emitDimacsClauseBytes)) ⋆
            cell64 cnt_ptr (BitVec.ofNat 64 cnt0) ⋆ R) mi)
        (fun Ji hIn => ?_)
        (fun Ji ⟨p, rem, doneCls⟩ mi ⟨hpr, hsl, hsplit, hmi⟩ hIn => ?_)
      · c0_hsteps_nogrp
        have h0 := hIn (off0, sz0, []) m1 ⟨rfl, hslice0, rfl, by simpa [pre0] using hm1⟩
        have hoff_bv : (s.core.wvec[(BitVec.ofNat 64 l0 * 2).toNat]'(by c0_bound)).setWidth 64 =
            BitVec.ofNat 64 off0 := by
          have : (BitVec.ofNat 64 l0 * 2).toNat = (l0 * 2) % 2 ^ 64 := by
            simp [BitVec.toNat_mul, hl0_m]
          simpa [this] using hoff_eq
        dsimp only
        rw [hoff_bv]
        simpa [pre0] using h0
      · have hmiF : (FullMem c s ⋆
            (bytes out (writeSlice buf pos0 ((pre0 ++ doneCls).flatMap emitDimacsClauseBytes)) ⋆
              cell64 cnt_ptr (BitVec.ofNat 64 cnt0) ⋆ R)) mi := full_frame_ac hmi
        have hp_le : p ≤ end0 := by omega
        have hend_lt64 : end0 < 2 ^ 64 := by omega
        c0_hsteps_nogrp
        · have hp_lt : p < end0 := by
            have hc' := hc
            rw [hend_nat, Nat.mod_eq_of_lt (by omega : p < 2 ^ 64)] at hc'
            exact hc'
          have hrem_pos : 0 < rem := by omega
          have hp_wstk : p < s.core.wstk.length := by omega
          obtain ⟨w0, hw0_get, hbin_st, hlg_st⟩ := modeWatchSlice_step hsl hrem_pos
          have hw0_at : s.core.wstk[(BitVec.ofNat 64 p).toNat]'(by c0_bound) = w0 := by
            have hg := hw0_get
            rw [List.getElem?_eq_getElem hp_wstk, Option.some.injEq] at hg
            simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : p < 2 ^ 64)] using hg
          have hw0_at' : s.core.wstk[p % 2 ^ 64]'(by
              rw [Nat.mod_eq_of_lt (by omega)]; exact hp_wstk) = w0 := hw0_at
          c0_hsteps
          · rename_i hbin_c
            have hflag_ne : (w0 &&& 0x80000000#32) ≠ 0#32 := by simpa [hw0_at'] using hbin_c
            obtain ⟨hl1_lt, _, hrest_sl⟩ := hbin_st hflag_ne
            have hrem_eq : rem = (rem - 1) + 1 := by omega
            have hslice_eq : exportBinSliceClauses s.core.wstk l0 p rem =
                if l0 < (w0 &&& 0x7FFFFFFF#32).toNat then
                  [l0, (w0 &&& 0x7FFFFFFF#32).toNat] ::
                    exportBinSliceClauses s.core.wstk l0 (p + 1) (rem - 1)
                else exportBinSliceClauses s.core.wstk l0 (p + 1) (rem - 1) := by
              conv => lhs; rw [hrem_eq]; unfold exportBinSliceClauses
              rw [hw0_get, Option.getD_some, ite_eq_left hflag_ne]
            let l1_bv : BitVec 64 := (w0 &&& (2147483647 : BitVec 32)).setWidth 64
            have hl1_bv_nat : l1_bv.toNat = (w0 &&& 0x7FFFFFFF#32).toNat :=
              bv32_setWidth64_toNat _
            have hl0_lt_l1 : l0 < (w0 &&& 0x7FFFFFFF#32).toNat := by
              have hc' := hc
              rw [hw0_at', hl0_m] at hc'
              simpa [l1_bv, hl1_bv_nat] using hc'
            rw [ite_eq_left hl0_lt_l1] at hslice_eq
            rw [hslice_eq] at hsplit
            have hdone_len :
                ((pre0 ++ doneCls).flatMap emitDimacsClauseBytes).length +
                  (emitDimacsLitBytes l0).length +
                  (emitDimacsLitBytes (w0 &&& 0x7FFFFFFF#32).toNat).length + 2 ≤
                (pre0.flatMap emitDimacsClauseBytes).length +
                  (fullSlice.flatMap emitDimacsClauseBytes).length := by
              rw [← hsplit]
              simp only [List.flatMap_append, List.flatMap_cons, List.length_append,
                emitDimacsClauseBytes, List.flatMap_nil, List.append_nil, List.length_cons,
                List.length_nil]
              omega
            have hcnt_step : cnt0 + (pre0 ++ doneCls).length + 1 < 2 ^ 64 := by
              have hl : doneCls.length + 1 ≤ fullSlice.length := by
                rw [← hsplit]; simp
              simp only [List.length_append]; omega
            have hl0_nat : (BitVec.ofNat 64 l0).toNat = l0 := hl0_m
            dsimp only
            refine wp_call_of_spec _ _ (call_emit_lit hLit hcap
              (by dsimp only [Arg.val]; rw [hl0_nat]; omega) hmi fun m2 hm2 => ?_)
            dsimp only [Arg.val] at hm2 ⊢
            rw [hw0_at]
            refine wp_call_of_spec _ _ (call_emit_lit hLit hcap
              (by dsimp only [Arg.val]; simp only [List.length_append, hl0_nat];
                  change _ + _ + (emitDimacsLitBytes l1_bv.toNat).length < _;
                  rw [hl1_bv_nat]; omega) hm2 fun m3 hm3 => ?_)
            dsimp only [Arg.val] at hm3 ⊢
            refine wp_call_of_spec _ _ (call_emit_byte hByte hcap
              (by simp only [List.length_append, hl0_nat];
                  change _ + (_ + (emitDimacsLitBytes l1_bv.toNat).length) + 1 < _;
                  rw [hl1_bv_nat]; omega) hm3 fun m4 hm4 => ?_)
            dsimp only [Arg.val] at hm4 ⊢
            refine wp_call_of_spec _ _ (call_emit_byte hByte hcap
              (by simp only [List.length_append, List.length_singleton, hl0_nat];
                  change _ + (_ + (emitDimacsLitBytes l1_bv.toNat).length + 1) + 1 < _;
                  rw [hl1_bv_nat]; omega)
              hm4 fun m5 hm5 => ?_)
            c0_hsteps
            dsimp only [Arg.val] at hm5 ⊢
            let newCl := [l0, (w0 &&& 0x7FFFFFFF#32).toNat]
            have hbytes_eq :
                (pre0 ++ doneCls).flatMap emitDimacsClauseBytes ++
                  emitDimacsLitBytes (BitVec.ofNat 64 l0).toNat ++
                  emitDimacsLitBytes ((w0 &&& (2147483647 : BitVec 32)).setWidth 64).toNat ++
                  [UInt8.ofNat (BitVec.toNat (48 : BitVec 64))] ++
                  [UInt8.ofNat (BitVec.toNat (10 : BitVec 64))] =
                (pre0 ++ (doneCls ++ [newCl])).flatMap emitDimacsClauseBytes := by
              change (pre0 ++ doneCls).flatMap emitDimacsClauseBytes ++
                  emitDimacsLitBytes (BitVec.ofNat 64 l0).toNat ++
                  emitDimacsLitBytes l1_bv.toNat ++
                  [UInt8.ofNat (BitVec.toNat (48 : BitVec 64))] ++
                  [UInt8.ofNat (BitVec.toNat (10 : BitVec 64))] = _
              simp only [hl0_nat, hl1_bv_nat, newCl, List.append_assoc, List.flatMap_append,
                emitDimacsClauseBytes, List.flatMap_cons, List.flatMap_nil, List.append_nil]
              rfl
            rw [hbytes_eq] at hm5 ⊢
            rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, bv_add_ofNat, bv_add_ofNat]
            have hcnt_eq : cnt0 + (pre0 ++ doneCls).length + 1 =
                cnt0 + (pre0 ++ (doneCls ++ [newCl])).length := by
              simp [List.length_append, Nat.add_assoc]
            rw [hcnt_eq]
            exact hIn (p + 1, rem - 1, doneCls ++ [newCl]) m5 (by dsimp only; omega)
              ⟨by omega, hrest_sl, by simpa [newCl, List.append_assoc] using hsplit, hm5⟩
          · rename_i hbin_c
            have hflag_ne : (w0 &&& 0x80000000#32) ≠ 0#32 := by simpa [hw0_at'] using hbin_c
            obtain ⟨_, _, hrest_sl⟩ := hbin_st hflag_ne
            have hrem_eq : rem = (rem - 1) + 1 := by omega
            have hnot_lt : ¬ (l0 < (w0 &&& 0x7FFFFFFF#32).toNat) := by
              intro hlt
              apply hc
              rw [hw0_at', hl0_m]
              simpa [bv32_setWidth64_toNat] using hlt
            have hslice_eq : exportBinSliceClauses s.core.wstk l0 p rem =
                exportBinSliceClauses s.core.wstk l0 (p + 1) (rem - 1) := by
              conv => lhs; rw [hrem_eq]; unfold exportBinSliceClauses
              rw [hw0_get, Option.getD_some, ite_eq_left hflag_ne, ite_eq_right hnot_lt]
            rw [hslice_eq] at hsplit
            dsimp only
            rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, bv_add_ofNat]
            exact hIn (p + 1, rem - 1, doneCls) mi (by dsimp only; omega)
              ⟨by omega, hrest_sl, hsplit, hmi⟩
          · have hflag_z : (w0 &&& 0x80000000#32) = 0#32 := by
              rw [← hw0_at']; exact hc
            obtain ⟨hge2, hrest_sl⟩ := hlg_st hflag_z
            have hrem_eq : rem = (rem - 2) + 2 := by omega
            have hslice_eq : exportBinSliceClauses s.core.wstk l0 p rem =
                exportBinSliceClauses s.core.wstk l0 (p + 2) (rem - 2) := by
              conv => lhs; rw [hrem_eq]; unfold exportBinSliceClauses
              rw [hw0_get, Option.getD_some, ite_eq_right (fun h => absurd hflag_z h)]
            rw [hslice_eq] at hsplit
            dsimp only
            rw [show (2 : BitVec 64) = BitVec.ofNat 64 2 from rfl, bv_add_ofNat]
            exact hIn (p + 2, rem - 2, doneCls) mi (by dsimp only; omega)
              ⟨by omega, hrest_sl, hsplit, hmi⟩
        · have hpe : p = end0 := by
            have hc' := hc
            rw [hend_nat, Nat.mod_eq_of_lt (by omega : p < 2 ^ 64)] at hc'
            omega
          have hrem0 : rem = 0 := by omega
          subst hrem0
          simp only [exportBinSliceClauses, List.append_nil] at hsplit
          have hnext_pre : pre0 ++ doneCls = binPrefixClauses s.core (l0 + 1) := by
            rw [hsplit, binPrefixClauses_succ]
          dsimp only
          rw [hnext_pre] at hmi ⊢
          rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, bv_add_ofNat]
          exact hLoop (l0 + 1) mi (by omega) ⟨by omega, hmi⟩
    · have hl0_eq : l0 = 2 * s.core.cur_vars := by c0_bound
      subst hl0_eq
      refine wp_store_cnt hm1 fun m2 hm2 => ?_
      c0_hsteps_nogrp
      exact hQ m2 hm2

/-! ### 3.4 `kissat_export_arena_clauses` -/

private def arenaScanClauses (k : FullCoreState) (pos fuel : Nat) : List (List Nat) :=
  ((fullArenaScanRefs k.arena k.arena_len pos fuel).filter
    (fullArenaClauseIrredLiveCore k)).map (fullArenaClauseLitsCore k)

private def arenaLitPrefixBytes (k : FullCoreState) (cref i : Nat) : List UInt8 :=
  (((k.arena.drop (cref + 3)).take i).map BitVec.toNat).flatMap emitDimacsLitBytes

private theorem arenaLitPrefixBytes_zero (k : FullCoreState) (cref : Nat) :
    arenaLitPrefixBytes k cref 0 = [] := rfl

private theorem arenaLitPrefixBytes_succ {k : FullCoreState} {cref i : Nat}
    (hi : cref + 3 + i < k.arena.length) :
    arenaLitPrefixBytes k cref (i + 1) =
      arenaLitPrefixBytes k cref i ++ emitDimacsLitBytes (k.arena[cref + 3 + i]'hi).toNat := by
  unfold arenaLitPrefixBytes
  have hlt : i < (k.arena.drop (cref + 3)).length := by rw [List.length_drop]; omega
  rw [List.take_add_one, List.getElem?_eq_getElem hlt]
  simp [List.getElem_drop]

private theorem arenaLitPrefixBytes_mono_len {k : FullCoreState} {cref i j : Nat}
    (hij : i ≤ j) (hj : cref + 3 + j ≤ k.arena.length) :
    (arenaLitPrefixBytes k cref i).length ≤ (arenaLitPrefixBytes k cref j).length := by
  induction j with
  | zero =>
    have hi0 : i = 0 := by omega
    subst hi0; exact Nat.le_refl _
  | succ j ih =>
    by_cases h : i = j + 1
    · subst h; exact Nat.le_refl _
    · rw [arenaLitPrefixBytes_succ (by omega), List.length_append]
      have := ih (by omega) (by omega)
      omega

theorem kissat_export_arena_clauses_wp (Γ : Env)
    (hByte : ∀ a m Q X, kissatEmitByteSpec a m Q X →
      Γ "kissat_emit_byte" [i64, i64, i64, i64] [i64] a m Q X)
    (hLit : ∀ a m Q X, kissatEmitDimacsLitSpec a m Q X →
      Γ "kissat_emit_dimacs_lit" [i64, i64, i64, i64] [i64] a m Q X)
    (hArenaNext : ∀ a m Q X, kissatExportArenaNextSpec a m Q X →
      Γ "kissat_export_arena_next" [i64, i64] [i64] a m Q X) :
    ∀ args m Q X, kissatExportArenaClausesSpec args m Q X →
      Func.wp Γ kissat_export_arena_clauses_body args m Q X := by
  rintro args m Q X ⟨c, F_cur, s, out, cnt_ptr, buf, pos0, cnt0, R, rfl, hlen, ha,
    hcap, hpos_fit, hcnt_fit, hm, hQ⟩
  have hcl := hlen.core_ok
  have har_len := hcl.arena_len_arr
  have hale := hcl.arena_len_le
  have hcap_ar := c.harena; unfold Ref.dimacsBound at hcap_ar
  have hmF : (FullMem c s ⋆ (bytes out buf ⋆ cell64 cnt_ptr (BitVec.ofNat 64 cnt0) ⋆ R)) m :=
    full_frame_ac hm
  unfold Func.wp kissat_export_arena_clauses_body; dsimp only
  c0_hsteps_nogrp
  refine wp_load_cnt hm ?_
  refine wp_while_state (ts := [i64, i64, i64]) (α := Nat × List (List Nat))
    (proj := fun (cref, doneCls) =>
      (BitVec.ofNat 64 (pos0 + (doneCls.flatMap emitDimacsClauseBytes).length),
        BitVec.ofNat 64 (cnt0 + doneCls.length),
        BitVec.ofNat 64 cref, ()))
    (μ := fun (cref, _) => s.core.arena_len - cref)
    (Inv := fun (cref, doneCls) m1 =>
      cref ≤ s.core.arena_len ∧
      (∀ r ∈ fullArenaScanRefs s.core.arena s.core.arena_len cref (s.core.arena_len - cref),
        r ∈ fullArenaClauseRefsCore s.core) ∧
      doneCls ++ arenaScanClauses s.core cref (s.core.arena_len - cref) =
        exportArenaClauses s.core ∧
      (FullMem c s ⋆ bytes out (writeSlice buf pos0 (doneCls.flatMap emitDimacsClauseBytes)) ⋆
        cell64 cnt_ptr (BitVec.ofNat 64 cnt0) ⋆ R) m1)
    (fun J hLoop => ?_)
    (fun J ⟨cref, doneCls⟩ m1 ⟨hcref_le, hsub, hsplit, hm1⟩ hLoop => ?_)
  · c0_hsteps_nogrp
    have h0 := hLoop (0, []) m ⟨Nat.zero_le _, fun _ hr => hr,
      by simp [arenaScanClauses, exportArenaClauses, fullArenaClauseRefsCore],
      by simpa [writeSlice_nil] using hm⟩
    simpa using h0
  · have hm1F : (FullMem c s ⋆
        (bytes out (writeSlice buf pos0 (doneCls.flatMap emitDimacsClauseBytes)) ⋆
          cell64 cnt_ptr (BitVec.ofNat 64 cnt0) ⋆ R)) m1 := full_frame_ac hm1
    have hcref_lt64 : cref + 3 < 2 ^ 64 := by omega
    have hal_lt64 : s.core.arena_len < 2 ^ 64 := by omega
    c0_hsteps_nogrp
    · have hle3 : cref + 3 ≤ s.core.arena_len := by c0_bound
      have hcref_lt : cref < s.core.arena.length := by omega
      have hcref2_lt : cref + 2 < s.core.arena.length := by omega
      have hf_eq : s.core.arena_len - cref = (s.core.arena_len - cref - 1) + 1 := by omega
      have hnxt_bd := fullArenaNextOff_bounds (ar := s.core.arena) (alen := s.core.arena_len)
        (cref := cref) hle3
      let nxt := fullArenaNextOff s.core.arena s.core.arena_len cref
      have hrefs_step :
          fullArenaScanRefs s.core.arena s.core.arena_len cref (s.core.arena_len - cref) =
          cref :: fullArenaScanRefs s.core.arena s.core.arena_len nxt (s.core.arena_len - nxt) := by
        conv => lhs; rw [hf_eq]; unfold fullArenaScanRefs
        rw [ite_eq_left hle3]
        congr 1
        exact fullArenaScanRefs_fuel_ge (ar := s.core.arena) (alen := s.core.arena_len)
          (f1 := s.core.arena_len - cref - 1) (f2 := s.core.arena_len - nxt) (pos := nxt)
          (by omega) (by omega)
      have hcref_mem : cref ∈ fullArenaClauseRefsCore s.core :=
        hsub cref (by rw [hrefs_step]; simp)
      have hsub_nxt :
          ∀ r ∈ fullArenaScanRefs s.core.arena s.core.arena_len nxt (s.core.arena_len - nxt),
            r ∈ fullArenaClauseRefsCore s.core :=
        fun r hr => hsub r (by rw [hrefs_step]; simp [hr])
      have hwf := ha.refs_wf cref hcref_mem
      have hsz_nat :
          (s.core.arena[(cref + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64]'(by
            have h2 : (cref + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64 = cref + 2 := by
              change (cref + 2) % 2 ^ 64 = cref + 2; exact Nat.mod_eq_of_lt (by omega)
            rw [h2]; exact hcref2_lt)).toNat = fullArenaClauseSizeCore s.core cref := by
        have h2 : (cref + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64 = cref + 2 := by
          change (cref + 2) % 2 ^ 64 = cref + 2; exact Nat.mod_eq_of_lt (by omega)
        simp only [h2, fullArenaClauseSizeCore, List.getElem?_eq_getElem hcref2_lt,
          Option.getD_some]
      have hhdr_at : s.core.arena[cref % 2 ^ 64]'(by
          rw [Nat.mod_eq_of_lt (by omega)]; exact hcref_lt) =
          fullArenaHdrCore s.core cref := by
        unfold fullArenaHdrCore
        simp only [Nat.mod_eq_of_lt (by omega : cref < 2 ^ 64), List.getElem?_eq_getElem hcref_lt,
          Option.getD_some]
      refine wp_join_state (ts := [i64, i64]) (α := List (List Nat))
        (proj := fun doneCls' =>
          (BitVec.ofNat 64 (pos0 + (doneCls'.flatMap emitDimacsClauseBytes).length),
            BitVec.ofNat 64 (cnt0 + doneCls'.length), ()))
        (Inv := fun doneCls' m2 =>
          doneCls' ++ arenaScanClauses s.core nxt (s.core.arena_len - nxt) =
            exportArenaClauses s.core ∧
          (FullMem c s ⋆
            bytes out (writeSlice buf pos0 (doneCls'.flatMap emitDimacsClauseBytes)) ⋆
            cell64 cnt_ptr (BitVec.ofNat 64 cnt0) ⋆ R) m2)
        (fun _ doneCls' m2 ⟨hsplit', hm2⟩ => ?_)
        (fun Jif hJif => ?_)
      · dsimp only
        refine wp_call_of_spec _ _ (hArenaNext _ _ _ _
          ⟨c, s, BitVec.ofNat 64 cref,
            bytes out (writeSlice buf pos0 (doneCls'.flatMap emitDimacsClauseBytes)) ⋆
              cell64 cnt_ptr (BitVec.ofNat 64 cnt0) ⋆ R,
            rfl, hlen, by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hcref_le,
            full_frame_ac hm2, ?_⟩)
        c0_hsteps_nogrp
        have hnxt_eq :
            fullArenaNextOff s.core.arena s.core.arena_len (BitVec.ofNat 64 cref).toNat = nxt := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        rw [hnxt_eq]
        exact hLoop (nxt, doneCls') m2 (by dsimp only; omega) ⟨hnxt_bd.2, hsub_nxt, hsplit', hm2⟩
      · c0_hsteps_nogrp
        · have hlive : fullArenaClauseIrredLiveCore s.core cref = true := by
            unfold fullArenaClauseIrredLiveCore
            have hz : fullArenaHdrCore s.core cref &&& 0x00480000#32 = 0#32 := by
              rw [← hhdr_at]; exact hc
            exact beq_iff_eq.mpr hz
          have hscan_step : arenaScanClauses s.core cref (s.core.arena_len - cref) =
              fullArenaClauseLitsCore s.core cref ::
                arenaScanClauses s.core nxt (s.core.arena_len - nxt) := by
            unfold arenaScanClauses
            rw [hrefs_step, List.filter_cons, ite_eq_left hlive, List.map_cons]
          rw [hscan_step] at hsplit
          let sz := fullArenaClauseSizeCore s.core cref
          have hsz_bd : cref + 3 + sz ≤ s.core.arena.length := by omega
          have hlit_full : arenaLitPrefixBytes s.core cref sz =
              (fullArenaClauseLitsCore s.core cref).flatMap emitDimacsLitBytes := rfl
          have hcl_fit : pos0 + (doneCls.flatMap emitDimacsClauseBytes).length +
              (arenaLitPrefixBytes s.core cref sz).length + 2 < 2 ^ 64 := by
            have hle_b : (doneCls.flatMap emitDimacsClauseBytes).length +
                (arenaLitPrefixBytes s.core cref sz).length + 2 ≤
                ((exportArenaClauses s.core).flatMap emitDimacsClauseBytes).length := by
              rw [← hsplit]
              simp only [List.flatMap_append, List.flatMap_cons, List.length_append,
                emitDimacsClauseBytes, hlit_full, List.length_cons, List.length_nil]
              omega
            omega
          have hcnt_step : cnt0 + doneCls.length + 1 < 2 ^ 64 := by
            have hle_c : doneCls.length + 1 ≤ (exportArenaClauses s.core).length := by
              rw [← hsplit]; simp
            omega
          refine wp_while_state (ts := [i64, i64]) (α := Nat)
            (proj := fun i =>
              let preBs :=
                doneCls.flatMap emitDimacsClauseBytes ++ arenaLitPrefixBytes s.core cref i
              (BitVec.ofNat 64 (pos0 + preBs.length), BitVec.ofNat 64 i, ()))
            (μ := fun i => sz - i)
            (Inv := fun i mi =>
              i ≤ sz ∧
              (FullMem c s ⋆
                bytes out (writeSlice buf pos0
                  (doneCls.flatMap emitDimacsClauseBytes ++ arenaLitPrefixBytes s.core cref i)) ⋆
                cell64 cnt_ptr (BitVec.ofNat 64 cnt0) ⋆ R) mi)
            (fun Ji hIn => ?_)
            (fun Ji i mi ⟨hile, hmi⟩ hIn => ?_)
          · c0_hsteps_nogrp
            have h0 := hIn 0 m1 ⟨Nat.zero_le _, by simpa [arenaLitPrefixBytes_zero] using hm1⟩
            simpa [arenaLitPrefixBytes_zero] using h0
          · have hmiF : (FullMem c s ⋆
                (bytes out (writeSlice buf pos0
                  (doneCls.flatMap emitDimacsClauseBytes ++ arenaLitPrefixBytes s.core cref i)) ⋆
                  cell64 cnt_ptr (BitVec.ofNat 64 cnt0) ⋆ R)) mi := full_frame_ac hmi
            c0_hsteps_nogrp
            · have hilt : i < sz := by
                have hc' := hc
                rw [hsz_nat, Nat.mod_eq_of_lt (by omega : i < 2 ^ 64)] at hc'
                exact hc'
              have hi_ar : cref + 3 + i < s.core.arena.length := by omega
              have hidx_ar :
                  (BitVec.ofNat 64 cref + 3 + BitVec.ofNat 64 i).toNat = cref + 3 + i := by
                c0_bound
              have hlit_bv :
                  ((s.core.arena[(BitVec.ofNat 64 cref + 3 + BitVec.ofNat 64 i).toNat]'(by
                    rw [hidx_ar]; exact hi_ar)).setWidth 64).toNat =
                  (s.core.arena[cref + 3 + i]'hi_ar).toNat := by
                rw [bv32_setWidth64_toNat]; simp only [hidx_ar]
              have hstep_len : (arenaLitPrefixBytes s.core cref (i + 1)).length ≤
                  (arenaLitPrefixBytes s.core cref sz).length :=
                arenaLitPrefixBytes_mono_len (by omega) hsz_bd
              rw [arenaLitPrefixBytes_succ hi_ar, List.length_append] at hstep_len
              refine wp_call_of_spec _ _ (call_emit_lit hLit hcap
                (by dsimp only [Arg.val]; simp only [List.length_append, hlit_bv]; omega)
                hmi fun m2 hm2 => ?_)
              c0_hsteps_nogrp
              dsimp only [Arg.val] at hm2 ⊢
              have hpre_eq :
                  doneCls.flatMap emitDimacsClauseBytes ++ arenaLitPrefixBytes s.core cref i ++
                    emitDimacsLitBytes
                      ((s.core.arena[(BitVec.ofNat 64 cref + 3 + BitVec.ofNat 64 i).toNat]'(by
                        rw [hidx_ar]; exact hi_ar)).setWidth 64).toNat =
                  doneCls.flatMap emitDimacsClauseBytes ++
                    arenaLitPrefixBytes s.core cref (i + 1) := by
                rw [hlit_bv, List.append_assoc, arenaLitPrefixBytes_succ hi_ar]
              rw [hpre_eq] at hm2 ⊢
              rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, bv_add_ofNat]
              exact hIn (i + 1) m2 (by omega) ⟨by omega, hm2⟩
            · have hieq : i = sz := by
                have hc' := hc
                rw [hsz_nat, Nat.mod_eq_of_lt (by omega : i < 2 ^ 64)] at hc'
                omega
              subst hieq
              refine wp_call_of_spec _ _ (call_emit_byte hByte hcap
                (by simp only [List.length_append]; omega) hmi fun m2 hm2 => ?_)
              dsimp only [Arg.val] at hm2 ⊢
              refine wp_call_of_spec _ _ (call_emit_byte hByte hcap
                (by simp only [List.length_append, List.length_singleton]; omega) hm2
                fun m3 hm3 => ?_)
              c0_hsteps_nogrp
              dsimp only [Arg.val] at hm3 ⊢
              let newCl := fullArenaClauseLitsCore s.core cref
              have hbytes_eq :
                  doneCls.flatMap emitDimacsClauseBytes ++ arenaLitPrefixBytes s.core cref sz ++
                    [UInt8.ofNat (BitVec.toNat (48 : BitVec 64))] ++
                    [UInt8.ofNat (BitVec.toNat (10 : BitVec 64))] =
                  (doneCls ++ [newCl]).flatMap emitDimacsClauseBytes := by
                simp only [List.append_assoc, List.flatMap_append, List.flatMap_singleton,
                  emitDimacsClauseBytes, newCl, hlit_full]
                rfl
              rw [hbytes_eq] at hm3 ⊢
              rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, bv_add_ofNat]
              have hcnt_eq : cnt0 + doneCls.length + 1 = cnt0 + (doneCls ++ [newCl]).length := by
                simp [Nat.add_assoc]
              rw [hcnt_eq]
              exact hJif (doneCls ++ [newCl]) m3
                ⟨by simpa [newCl, List.append_assoc] using hsplit, hm3⟩
        · have hnlive : fullArenaClauseIrredLiveCore s.core cref = false := by
            unfold fullArenaClauseIrredLiveCore
            have hne : fullArenaHdrCore s.core cref &&& 0x00480000#32 ≠ 0#32 := by
              rw [← hhdr_at]; exact hc
            exact beq_false_of_ne hne
          have hscan_step : arenaScanClauses s.core cref (s.core.arena_len - cref) =
              arenaScanClauses s.core nxt (s.core.arena_len - nxt) := by
            unfold arenaScanClauses
            rw [hrefs_step, List.filter_cons, hnlive]
            simp
          rw [hscan_step] at hsplit
          exact hJif doneCls m1 ⟨hsplit, hm1⟩
    · have hgt3 : ¬ (cref + 3 ≤ s.core.arena_len) := by c0_bound
      have hscan_nil : arenaScanClauses s.core cref (s.core.arena_len - cref) = [] := by
        unfold arenaScanClauses
        cases hf : s.core.arena_len - cref with
        | zero => simp [fullArenaScanRefs]
        | succ _ => simp [fullArenaScanRefs, hgt3]
      rw [hscan_nil, List.append_nil] at hsplit
      subst hsplit
      refine wp_store_cnt hm1 fun m2 hm2 => ?_
      c0_hsteps_nogrp
      exact hQ m2 hm2

/-! ### 3.5 `kissat_export_cnf_bytes` -/

private theorem fullProbeScratchPres_refl (s : FullState) : FullProbeScratchPres s s :=
  ⟨⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem kissat_export_cnf_bytes_wp (Γ : Env)
    (hBacktrack : ∀ a m Q X, fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hByte : ∀ a m Q X, kissatEmitByteSpec a m Q X →
      Γ "kissat_emit_byte" [i64, i64, i64, i64] [i64] a m Q X)
    (hHdr : ∀ a m Q X, kissatEmitDimacsHdrSpec a m Q X →
      Γ "kissat_emit_dimacs_hdr" [i64, i64, i64, i64, i64] [i64] a m Q X)
    (hTrail : ∀ a m Q X, kissatExportTrailUnitsSpec a m Q X →
      Γ "kissat_export_trail_units" [i64, i64, i64, i64, i64] [i64] a m Q X)
    (hBin : ∀ a m Q X, kissatExportBinClausesSpec a m Q X →
      Γ "kissat_export_bin_clauses" [i64, i64, i64, i64, i64] [i64] a m Q X)
    (hArena : ∀ a m Q X, kissatExportArenaClausesSpec a m Q X →
      Γ "kissat_export_arena_clauses" [i64, i64, i64, i64, i64] [i64] a m Q X) :
    ∀ args m Q X, kissatExportCnfBytesSpec args m Q X →
      Func.wp Γ kissat_export_cnf_bytes_body args m Q X := by
  rintro args m Q X ⟨c, F0, F_cur, s, out, out_len_ptr, old_len, buf, R, rfl, hcap, hlen, hw,
    hm, hQ⟩
  have hmx := c.hmaxv; unfold Ref.dimacsBound at hmx
  have hcl_lt64 : s.core.cur_level < 2 ^ 64 := by
    have := hw.cur_level_le; have := hlen.core_ok.trail_end_le
    have := hlen.core_ok.cur_vars_le; omega
  unfold Func.wp kissat_export_cnf_bytes_body; dsimp only
  -- Step (a): optional backtrack to level 0
  refine wp_join_group (ts := [])
    (fun () m1 =>
      ∃ s1 : FullState,
        s1.LengthsOk c ∧
        FullWitnessInv c F0 F_cur s1.core ∧
        s1.core.cur_level = 0 ∧
        s1.core.cur_vars = s.core.cur_vars ∧
        s1.core.inconsistent = s.core.inconsistent ∧
        s1.core.arena = s.core.arena ∧
        s1.core.arena_len = s.core.arena_len ∧
        s1.core.wvec = s.core.wvec ∧
        s1.core.wstk = s.core.wstk ∧
        s1.core.wlen = s.core.wlen ∧
        s1.core.dense_mode = s.core.dense_mode ∧
        FullProbeScratchPres s s1 ∧
        (FullMem c s1 ⋆ bytes out buf ⋆ cell64 out_len_ptr old_len ⋆ R) m1) ?_ ?_
  · rintro _ ⟨⟩ m1 ⟨s1, hlen1, hw1, hl0, hcv1, hinc1, har1, hal1, hwv1, hws1, hwl1, hdm1, hpres1,
      hm1⟩
    have hm1F : (FullMem c s1 ⋆ (bytes out buf ⋆ cell64 out_len_ptr old_len ⋆ R)) m1 :=
      full_frame_ac hm1
    c0_hsteps_nogrp
    · -- Step (b): inconsistent != 0 -> emit "p cnf 0 1\n0\n" (12 bytes)
      have hinc_ne : s1.core.inconsistent ≠ 0#64 := hc
      have hes_bytes : exportStateBytes s1.core = emitDimacsBytes 0 [[]] := by
        simp [exportStateBytes, exportStateMv, exportStateClauses, hinc_ne]
      have hes_len : (exportStateBytes s1.core).length = 12 := by
        rw [hes_bytes]; decide
      refine wp_store_cnt hm1 fun m2 hm2 => ?_
      c0_hsteps_nogrp
      · -- cap < 12 -> return 0 without touching out
        have hcap_lt12 : buf.length < 12 := by c0_bound
        exact hQ 0#64 s1 [] 12 _ hlen1 hw1 hl0 hcv1 hinc1 har1 hal1 hwv1 hws1 hwl1 hdm1 hpres1
          (Or.inl rfl) (by decide)
          (fun _ => ⟨Or.inr hes_len.symm, fun _ _ => ⟨hes_len.symm, by omega⟩, hm2⟩)
          (fun h => by cases h)
      · -- cap >= 12 -> emit header "p cnf 0 1\n" + "0\n"
        have hcap_ge12 : 12 ≤ buf.length := by c0_bound
        refine wp_call_of_spec _ _ (hHdr _ _ _ _
          ⟨out, buf, 0, 0#64, 1#64, FullMem c s1 ⋆ cell64 out_len_ptr 12#64 ⋆ R,
            rfl, hcap, by decide, sep_ac hm2, fun m3 _ hm3 => ?_⟩)
        dsimp only
        have hpos10 : BitVec.ofNat 64 (0 + (emitDimacsHdrBytes (0#64).toNat (1#64).toNat).length) =
            BitVec.ofNat 64 (0 + (emitDimacsHdrBytes 0 1).length) := rfl
        rw [hpos10]
        change (bytes out (writeSlice buf 0 (emitDimacsHdrBytes 0 1)) ⋆
          (FullMem c s1 ⋆ cell64 out_len_ptr 12#64 ⋆ R)) m3 at hm3
        have hm3' : (FullMem c s1 ⋆ bytes out (writeSlice buf 0 (emitDimacsHdrBytes 0 1)) ⋆
            cell64 out_len_ptr 12#64 ⋆ R) m3 := sep_ac hm3
        refine wp_call_of_spec _ _
          (call_emit_byte hByte hcap (by decide) hm3' fun m4 hm4 => ?_)
        dsimp only [Arg.val] at hm4 ⊢
        refine wp_call_of_spec _ _ (call_emit_byte hByte hcap (by decide) hm4 fun m5 hm5 => ?_)
        dsimp only [Arg.val] at hm5 ⊢
        have hbs_eq : emitDimacsHdrBytes 0 1 ++ [UInt8.ofNat (BitVec.toNat (48 : BitVec 64))] ++
            [UInt8.ofNat (BitVec.toNat (10 : BitVec 64))] = exportStateBytes s1.core := by
          rw [hes_bytes]; decide
        have hlen_eq : (emitDimacsHdrBytes 0 1 ++ [UInt8.ofNat (BitVec.toNat (48 : BitVec 64))] ++
            [UInt8.ofNat (BitVec.toNat (10 : BitVec 64))]).length = 12 := by rw [hbs_eq, hes_len]
        rw [hbs_eq] at hm5
        rw [writeSlice_fit buf 0 (exportStateBytes s1.core) (by rw [hes_len]; omega)] at hm5
        simp only [List.take_zero, List.nil_append, Nat.zero_add, hes_len] at hm5
        rw [show BitVec.ofNat 64 (0 + (emitDimacsHdrBytes 0 1 ++
            [UInt8.ofNat (BitVec.toNat (48 : BitVec 64))] ++
            [UInt8.ofNat (BitVec.toNat (10 : BitVec 64))]).length) =
            BitVec.ofNat 64 12 by rw [hlen_eq]]
        refine wp_store_cnt hm5 fun m6 hm6 => ?_
        c0_hsteps_nogrp
        obtain ⟨hp_d, hu_d⟩ := exportStateBytes_sound hlen1.core_ok hw1 hl0
          (by simp [exportStateMv, hinc_ne, dimacsBound])
          (by simp [exportStateClauses, hinc_ne, dimacsBound])
        exact hQ 1#64 s1 (exportStateBytes s1.core) 12 _ hlen1 hw1 hl0 hcv1 hinc1 har1 hal1
          hwv1 hws1 hwl1 hdm1 hpres1 (Or.inr rfl) (by decide)
          (fun h => by cases h)
          (fun _ => ⟨rfl, hes_len.symm, hcap_ge12,
            ⟨kissatCnfToDimacs (exportStateClauses s1.core), hp_d, rfl, hu_d⟩, hm6⟩)
    · -- Step (c1): inconsistent == 0, mv >= dimacsBound -> store 0, return 0
      rename_i hinc_z_raw
      have hinc_z : s1.core.inconsistent = 0#64 := hinc_z_raw
      have hmv_eq : exportStateMv s1.core = s1.core.cur_vars := by
        simp [exportStateMv, hinc_z]
      have hcv_lt64 : s1.core.cur_vars < 2 ^ 64 := by
        have := hlen1.core_ok.cur_vars_le; omega
      have hmv_ge : dimacsBound ≤ s1.core.cur_vars := by
        unfold dimacsBound; c0_bound
      refine wp_store_cnt hm1 fun m2 hm2 => ?_
      c0_hsteps_nogrp
      exact hQ 0#64 s1 [] 0 m2 hlen1 hw1 hl0 hcv1 hinc1 har1 hal1 hwv1 hws1 hwl1 hdm1 hpres1
        (Or.inl rfl) (by decide)
        (fun _ => ⟨Or.inl rfl, fun hmv_lt _ => absurd (hmv_eq ▸ hmv_lt) (by omega), hm2⟩)
        (fun h => by cases h)
    · -- Step (c2): inconsistent == 0, mv < dimacsBound -> Pass 1 (dry-run, cap = 0)
      rename_i hinc_z_raw
      have hinc_z : s1.core.inconsistent = 0#64 := hinc_z_raw
      have hmv_eq : exportStateMv s1.core = s1.core.cur_vars := by
        simp [exportStateMv, hinc_z]
      have hcls_eq : exportStateClauses s1.core =
          exportTrailUnitClauses s1.core ++ exportBinClauses s1.core ++
            exportArenaClauses s1.core := by
        simp [exportStateClauses, hinc_z]
      have hcv_lt64 : s1.core.cur_vars < 2 ^ 64 := by
        have := hlen1.core_ok.cur_vars_le; omega
      have hmv_lt : s1.core.cur_vars < dimacsBound := by
        unfold dimacsBound; c0_bound
      obtain ⟨hcnt_lt31, hbody_lt36, htot_lt36⟩ := exportState_counts_lt hlen1.core_ok hw1
      have ht_len := exportTrailUnitClauses_length hlen1.core_ok
      let trailBs := (exportTrailUnitClauses s1.core).flatMap emitDimacsClauseBytes
      let binBs := (exportBinClauses s1.core).flatMap emitDimacsClauseBytes
      let arenaBs := (exportArenaClauses s1.core).flatMap emitDimacsClauseBytes
      let bodyBs := trailBs ++ binBs ++ arenaBs
      let clauseCnt := s1.core.trail_end + (exportBinClauses s1.core).length +
          (exportArenaClauses s1.core).length
      have hclauseCnt_eq : clauseCnt = (exportStateClauses s1.core).length := by
        rw [hcls_eq, List.length_append, List.length_append, ht_len]
      have hbodyBs_len : bodyBs.length = trailBs.length + binBs.length + arenaBs.length := by
        simp [bodyBs, Nat.add_assoc]
      have hbody_lt : trailBs.length + binBs.length + arenaBs.length < 2 ^ 36 := hbody_lt36
      have hcnt_lt' : s1.core.trail_end + (exportBinClauses s1.core).length +
          (exportArenaClauses s1.core).length < 2 ^ 31 := by
        rw [← ht_len]; exact hcnt_lt31
      refine wp_store_cnt hm1 fun m2 hm2 => ?_
      -- Pass 1a: trail units (dry-run with buf := [])
      have hm2_dry : (FullMem c s1 ⋆ bytes out [] ⋆ cell64 out_len_ptr (BitVec.ofNat 64 0) ⋆
          (bytes out buf ⋆ R)) m2 :=
        sep_ac (sep_bytes_nil_intro hm2)
      refine wp_call_of_spec _ _ (hTrail _ _ _ _
        ⟨c, s1, out, out_len_ptr, [], 0, 0, bytes out buf ⋆ R,
          rfl, hlen1, by decide, by omega, by omega, hm2_dry, fun m3 hm3 => ?_⟩)
      dsimp only
      rw [writeSlice_nil_buf] at hm3
      -- Pass 1b: binary clauses (dry-run)
      refine wp_call_of_spec _ _ (hBin _ _ _ _
        ⟨c, F_cur, s1, out, out_len_ptr, [], 0 + trailBs.length, 0 + s1.core.trail_end,
          bytes out buf ⋆ R, rfl, hlen1, hw1.watches, by decide, by omega, by omega, hm3,
          fun m4 hm4 => ?_⟩)
      dsimp only
      rw [writeSlice_nil_buf] at hm4
      -- Pass 1c: arena clauses (dry-run)
      refine wp_call_of_spec _ _ (hArena _ _ _ _
        ⟨c, F_cur, s1, out, out_len_ptr, [],
          0 + trailBs.length + binBs.length,
          0 + s1.core.trail_end + (exportBinClauses s1.core).length,
          bytes out buf ⋆ R, rfl, hlen1, hw1.arena, by decide, by omega, by omega, hm4,
          fun m5 hm5 => ?_⟩)
      dsimp only
      rw [writeSlice_nil_buf] at hm5
      have hm5_restored : (FullMem c s1 ⋆ bytes out buf ⋆
          cell64 out_len_ptr (BitVec.ofNat 64 clauseCnt) ⋆ R) m5 := by
        have hm5' : (bytes out [] ⋆
            (FullMem c s1 ⋆ bytes out buf ⋆
              cell64 out_len_ptr (BitVec.ofNat 64
                (0 + s1.core.trail_end + (exportBinClauses s1.core).length +
                  (exportArenaClauses s1.core).length)) ⋆ R)) m5 := sep_ac hm5
        have h := sep_bytes_nil_elim hm5'
        simpa [clauseCnt, Nat.zero_add, Nat.add_assoc] using h
      refine wp_load_cnt hm5_restored ?_
      c0_hsteps_nogrp
      · -- clause_cnt >= dimacsBound -> store 0, return 0
        have hcnt_ge : dimacsBound ≤ clauseCnt := by
          unfold dimacsBound; c0_bound
        refine wp_store_cnt hm5_restored fun m6 hm6 => ?_
        c0_hsteps_nogrp
        exact hQ 0#64 s1 [] 0 _ hlen1 hw1 hl0 hcv1 hinc1 har1 hal1 hwv1 hws1 hwl1 hdm1 hpres1
          (Or.inl rfl) (by decide)
          (fun _ => ⟨Or.inl rfl, fun _ hnc_lt => absurd (hclauseCnt_eq ▸ hnc_lt) (by omega), hm6⟩)
          (fun h => by cases h)
      · -- clause_cnt < dimacsBound -> compute hdr_len (dry-run) and check need <= cap
        have hcnt_lt : clauseCnt < dimacsBound := by
          unfold dimacsBound; c0_bound
        let hdrBs := emitDimacsHdrBytes s1.core.cur_vars clauseCnt
        have hhdr_le48 : hdrBs.length ≤ 48 :=
          emitDimacsHdrBytes_length_le_48 (by omega) (by omega)
        have hes_eq : exportStateBytes s1.core = hdrBs ++ bodyBs := by
          unfold exportStateBytes emitDimacsBytes
          rw [hmv_eq, ← hclauseCnt_eq, hcls_eq]
          simp [hdrBs, bodyBs, trailBs, binBs, arenaBs, List.flatMap_append]
        have hneed_eq : hdrBs.length + bodyBs.length = (exportStateBytes s1.core).length := by
          rw [hes_eq]; exact (@List.length_append _ hdrBs bodyBs).symm
        have hhdr_args : emitDimacsHdrBytes (BitVec.ofNat 64 s1.core.cur_vars).toNat
            (BitVec.ofNat 64 clauseCnt).toNat = hdrBs := by
          simp [hdrBs, Nat.mod_eq_of_lt (by omega : s1.core.cur_vars < 2 ^ 64),
            Nat.mod_eq_of_lt (by omega : clauseCnt < 2 ^ 64)]
        have hm5_dry : (bytes out [] ⋆
            (FullMem c s1 ⋆ bytes out buf ⋆
              cell64 out_len_ptr (BitVec.ofNat 64 clauseCnt) ⋆ R)) m5 :=
          sep_bytes_nil_intro hm5_restored
        refine wp_call_of_spec _ _ (hHdr _ _ _ _
          ⟨out, [], 0, BitVec.ofNat 64 s1.core.cur_vars, BitVec.ofNat 64 clauseCnt,
            FullMem c s1 ⋆ bytes out buf ⋆ cell64 out_len_ptr (BitVec.ofNat 64 clauseCnt) ⋆ R,
            rfl, by decide, by rw [hhdr_args]; omega, hm5_dry, fun m6 _ hm6 => ?_⟩)
        c0_hsteps_nogrp
        rw [writeSlice_nil_buf] at hm6
        have hm6_restored : (FullMem c s1 ⋆ bytes out buf ⋆
            cell64 out_len_ptr (BitVec.ofNat 64 clauseCnt) ⋆ R) m6 :=
          sep_bytes_nil_elim hm6
        rw [hhdr_args, Nat.zero_add]
        have hbody_bv : BitVec.ofNat 64 (0 + trailBs.length + binBs.length + arenaBs.length) =
            BitVec.ofNat 64 bodyBs.length := by rw [hbodyBs_len, Nat.zero_add]
        rw [hbody_bv, bv_add_ofNat, hneed_eq]
        refine wp_store_cnt hm6_restored fun m7 hm7 => ?_
        c0_hsteps_nogrp
        · -- need > cap -> return 0 without touching out
          have hneed_gt : buf.length < (exportStateBytes s1.core).length := by c0_bound
          exact hQ 0#64 s1 [] (exportStateBytes s1.core).length _ hlen1 hw1 hl0 hcv1 hinc1
            har1 hal1 hwv1 hws1 hwl1 hdm1 hpres1 (Or.inl rfl) (by omega)
            (fun _ => ⟨Or.inr rfl, fun _ _ => ⟨rfl, hneed_gt⟩, hm7⟩)
            (fun h => by cases h)
        · -- need <= cap -> Pass 2 (full write into out[0 ..< need))
          have hneed_le : (exportStateBytes s1.core).length ≤ buf.length := by c0_bound
          refine wp_store_cnt hm7 fun m8 hm8 => ?_
          -- Pass 2a: header
          refine wp_call_of_spec _ _ (hHdr _ _ _ _
            ⟨out, buf, 0, BitVec.ofNat 64 s1.core.cur_vars, BitVec.ofNat 64 clauseCnt,
              FullMem c s1 ⋆ cell64 out_len_ptr 0#64 ⋆ R,
              rfl, hcap, by rw [hhdr_args]; omega, sep_ac hm8, fun m9 _ hm9 => ?_⟩)
          dsimp only
          rw [hhdr_args] at hm9 ⊢
          rw [Nat.zero_add]
          -- Pass 2b: trail units
          have hbl1 : (writeSlice buf 0 hdrBs).length = buf.length :=
            writeSlice_length buf 0 hdrBs
          refine wp_call_of_spec _ _ (hTrail _ _ _ _
            ⟨c, s1, out, out_len_ptr, writeSlice buf 0 hdrBs, hdrBs.length, 0, R,
              by rw [hbl1]; rfl, hlen1, by rw [hbl1]; exact hcap, by omega, by omega,
              sep_ac hm9, fun m10 hm10 => ?_⟩)
          dsimp only
          rw [← Nat.zero_add hdrBs.length, ← writeSlice_append (pos := 0)] at hm10
          -- Pass 2c: binary clauses
          have hbl2 : (writeSlice buf 0 (hdrBs ++ trailBs)).length = buf.length :=
            writeSlice_length buf 0 _
          refine wp_call_of_spec _ _ (hBin _ _ _ _
            ⟨c, F_cur, s1, out, out_len_ptr, writeSlice buf 0 (hdrBs ++ trailBs),
              hdrBs.length + trailBs.length, 0 + s1.core.trail_end, R,
              by rw [hbl2]; rfl, hlen1, hw1.watches, by rw [hbl2]; exact hcap, by omega, by omega,
              hm10, fun m11 hm11 => ?_⟩)
          dsimp only
          have hlen_ht : (hdrBs ++ trailBs).length = hdrBs.length + trailBs.length := by simp
          rw [← hlen_ht, ← Nat.zero_add (hdrBs ++ trailBs).length,
            ← writeSlice_append (pos := 0)] at hm11
          -- Pass 2d: arena clauses
          have hbl3 : (writeSlice buf 0 (hdrBs ++ trailBs ++ binBs)).length = buf.length :=
            writeSlice_length buf 0 _
          refine wp_call_of_spec _ _ (hArena _ _ _ _
            ⟨c, F_cur, s1, out, out_len_ptr, writeSlice buf 0 (hdrBs ++ trailBs ++ binBs),
              hdrBs.length + trailBs.length + binBs.length,
              0 + s1.core.trail_end + (exportBinClauses s1.core).length, R,
              by rw [hbl3]; rfl, hlen1, hw1.arena, by rw [hbl3]; exact hcap, by omega, by omega,
              hm11, fun m12 hm12 => ?_⟩)
          dsimp only
          have hlen_htb : (hdrBs ++ trailBs ++ binBs).length =
              hdrBs.length + trailBs.length + binBs.length := by simp [Nat.add_assoc]
          rw [← hlen_htb, ← Nat.zero_add (hdrBs ++ trailBs ++ binBs).length,
            ← writeSlice_append (pos := 0)] at hm12
          have hfull_bs : hdrBs ++ trailBs ++ binBs ++ arenaBs = exportStateBytes s1.core := by
            rw [hes_eq]; simp [bodyBs, List.append_assoc]
          have hfull_len : hdrBs.length + trailBs.length + binBs.length + arenaBs.length =
              (exportStateBytes s1.core).length := by
            rw [← hneed_eq, hbodyBs_len]; omega
          rw [hfull_bs, writeSlice_fit buf 0 (exportStateBytes s1.core) (by simpa using hneed_le)]
            at hm12
          simp only [List.take_zero, List.nil_append, Nat.zero_add] at hm12
          rw [hfull_len]
          refine wp_store_cnt hm12 fun m13 hm13 => ?_
          c0_hsteps_nogrp
          obtain ⟨hp_d, hu_d⟩ := exportStateBytes_sound hlen1.core_ok hw1 hl0
            (by rw [hmv_eq]; exact hmv_lt) (by rw [← hclauseCnt_eq]; exact hcnt_lt)
          exact hQ 1#64 s1 (exportStateBytes s1.core) (exportStateBytes s1.core).length _
            hlen1 hw1 hl0 hcv1 hinc1 har1 hal1 hwv1 hws1 hwl1 hdm1 hpres1
            (Or.inr rfl) (by omega) (fun h => by cases h)
            (fun _ => ⟨rfl, rfl, hneed_le,
              ⟨kissatCnfToDimacs (exportStateClauses s1.core), hp_d, rfl, hu_d⟩, hm13⟩)
  · -- Backtrack branch for Step (a)
    intro Jbt hJbt
    have hmF : (FullMem c s ⋆ (bytes out buf ⋆ cell64 out_len_ptr old_len ⋆ R)) m :=
      full_frame_ac hm
    c0_hsteps_nogrp
    · have hcl_pos : 0 < s.core.cur_level := by c0_bound
      refine wp_call_of_spec _ _ (hBacktrack _ _ _ _
        ⟨c, s, bytes out buf ⋆ cell64 out_len_ptr old_len ⋆ R, rfl, hlen, hcl_lt64,
          (fun _ => by
            have := hw.cur_level_le; have := hlen.core_ok.trail_end_le
            have := hlen.core_ok.cur_vars_le; omega),
          hw.trail_lits_lt, hmF,
          fun vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m1
            hlen1 _ _ hcl1 hpres1 _ _ _ hbt_wit _ hm1 => ?_⟩)
      c0_hsteps_nogrp
      have hcl0 : cl' = 0 := by simpa using hcl1
      exact hJbt () m1 ⟨_, hlen1, hbt_wit F0 F_cur hw (Nat.zero_le _), hcl0,
        rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hpres1, sep_ac hm1⟩
    · have hcl0 : s.core.cur_level = 0 := by c0_bound
      exact hJbt () m ⟨s, hlen, hw, hcl0, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        fullProbeScratchPres_refl s, hm⟩

/-! ## 4. Closed Module Certification & Compositional Soundness for Downstream Shards -/

private theorem exportCnfStateEnv_backtrack :
    exportCnfStateEnv "full_backtrack" [i64, i64] [] = fullBacktrackSpec := by
  funext a m Q X; simp [exportCnfStateEnv]

private theorem exportCnfStateEnv_arena_next :
    exportCnfStateEnv "kissat_export_arena_next" [i64, i64] [i64] =
      kissatExportArenaNextSpec := by
  funext a m Q X; simp [exportCnfStateEnv]

private theorem exportCnfStateEnv_trail_units :
    exportCnfStateEnv "kissat_export_trail_units" [i64, i64, i64, i64, i64] [i64] =
      kissatExportTrailUnitsSpec := by
  funext a m Q X; simp [exportCnfStateEnv]

private theorem exportCnfStateEnv_bin_clauses :
    exportCnfStateEnv "kissat_export_bin_clauses" [i64, i64, i64, i64, i64] [i64] =
      kissatExportBinClausesSpec := by
  funext a m Q X; simp [exportCnfStateEnv]

private theorem exportCnfStateEnv_arena_clauses :
    exportCnfStateEnv "kissat_export_arena_clauses" [i64, i64, i64, i64, i64] [i64] =
      kissatExportArenaClausesSpec := by
  funext a m Q X; simp [exportCnfStateEnv]

private theorem exportCnfStateEnv_cnf_bytes :
    exportCnfStateEnv "kissat_export_cnf_bytes" [i64, i64, i64, i64] [i64] =
      kissatExportCnfBytesSpec := by
  funext a m Q X; simp [exportCnfStateEnv]

private theorem exportCnfStateEnv_byte :
    exportCnfStateEnv "kissat_emit_byte" [i64, i64, i64, i64] [i64] =
      kissatEmitByteSpec := by
  funext a m Q X; simp [exportCnfStateEnv, exportCnfFmtEnv]

private theorem exportCnfStateEnv_u64 :
    exportCnfStateEnv "kissat_emit_u64" [i64, i64, i64, i64] [i64] =
      kissatEmitU64Spec := by
  funext a m Q X; simp [exportCnfStateEnv, exportCnfFmtEnv]

private theorem exportCnfStateEnv_lit :
    exportCnfStateEnv "kissat_emit_dimacs_lit" [i64, i64, i64, i64] [i64] =
      kissatEmitDimacsLitSpec := by
  funext a m Q X; simp [exportCnfStateEnv, exportCnfFmtEnv]

private theorem exportCnfStateEnv_hdr :
    exportCnfStateEnv "kissat_emit_dimacs_hdr" [i64, i64, i64, i64, i64] [i64] =
      kissatEmitDimacsHdrSpec := by
  funext a m Q X; simp [exportCnfStateEnv, exportCnfFmtEnv]

/-- Compositional soundness of all `5` exporter functions in any enclosing environment `Γ`
(enabling direct drop-in integration into Kissat assemblies such as `fidStep10Module`). -/
theorem exportCnfStateFns_sound_in (Γ : Env)
    (hBacktrack : ∀ a m Q X, fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hByte : ∀ a m Q X, kissatEmitByteSpec a m Q X →
      Γ "kissat_emit_byte" [i64, i64, i64, i64] [i64] a m Q X)
    (hLit : ∀ a m Q X, kissatEmitDimacsLitSpec a m Q X →
      Γ "kissat_emit_dimacs_lit" [i64, i64, i64, i64] [i64] a m Q X)
    (hHdr : ∀ a m Q X, kissatEmitDimacsHdrSpec a m Q X →
      Γ "kissat_emit_dimacs_hdr" [i64, i64, i64, i64, i64] [i64] a m Q X)
    (hArenaNext : ∀ a m Q X, kissatExportArenaNextSpec a m Q X →
      Γ "kissat_export_arena_next" [i64, i64] [i64] a m Q X)
    (hTrail : ∀ a m Q X, kissatExportTrailUnitsSpec a m Q X →
      Γ "kissat_export_trail_units" [i64, i64, i64, i64, i64] [i64] a m Q X)
    (hBin : ∀ a m Q X, kissatExportBinClausesSpec a m Q X →
      Γ "kissat_export_bin_clauses" [i64, i64, i64, i64, i64] [i64] a m Q X)
    (hArena : ∀ a m Q X, kissatExportArenaClausesSpec a m Q X →
      Γ "kissat_export_arena_clauses" [i64, i64, i64, i64, i64] [i64] a m Q X)
    (hSpecArenaNext : ∀ a m Q X,
      Γ "kissat_export_arena_next" [i64, i64] [i64] a m Q X →
        kissatExportArenaNextSpec a m Q X)
    (hSpecTrail : ∀ a m Q X,
      Γ "kissat_export_trail_units" [i64, i64, i64, i64, i64] [i64] a m Q X →
        kissatExportTrailUnitsSpec a m Q X)
    (hSpecBin : ∀ a m Q X,
      Γ "kissat_export_bin_clauses" [i64, i64, i64, i64, i64] [i64] a m Q X →
        kissatExportBinClausesSpec a m Q X)
    (hSpecArena : ∀ a m Q X,
      Γ "kissat_export_arena_clauses" [i64, i64, i64, i64, i64] [i64] a m Q X →
        kissatExportArenaClausesSpec a m Q X)
    (hSpecCnf : ∀ a m Q X,
      Γ "kissat_export_cnf_bytes" [i64, i64, i64, i64] [i64] a m Q X →
        kissatExportCnfBytesSpec a m Q X) :
    ∀ f ∈ exportCnfState_fns, ∀ xs m Q X,
      Γ f.name f.as f.rs xs m Q X → Func.wp Γ f.body xs m Q X := by
  intro f hf xs m Q X hlk
  simp only [exportCnfState_fns, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · dsimp only [kissat_export_arena_next] at hlk ⊢
    exact kissat_export_arena_next_wp Γ xs m Q X (hSpecArenaNext xs m Q X hlk)
  · dsimp only [kissat_export_trail_units] at hlk ⊢
    exact kissat_export_trail_units_wp Γ hByte hLit xs m Q X (hSpecTrail xs m Q X hlk)
  · dsimp only [kissat_export_bin_clauses] at hlk ⊢
    exact kissat_export_bin_clauses_wp Γ hByte hLit xs m Q X (hSpecBin xs m Q X hlk)
  · dsimp only [kissat_export_arena_clauses] at hlk ⊢
    exact kissat_export_arena_clauses_wp Γ hByte hLit hArenaNext xs m Q X
      (hSpecArena xs m Q X hlk)
  · dsimp only [kissat_export_cnf_bytes] at hlk ⊢
    exact kissat_export_cnf_bytes_wp Γ hBacktrack hByte hHdr hTrail hBin hArena xs m Q X
      (hSpecCnf xs m Q X hlk)

/-- All `9` functions in `exportCnfStateMod` satisfy `exportCnfStateEnv`. -/
theorem exportCnfStateEnv_sound :
    ∀ f ∈ exportCnfStateMod.fns, ∀ xs m Q X,
      exportCnfStateEnv f.name f.as f.rs xs m Q X →
      Func.wp exportCnfStateEnv f.body xs m Q X := by
  intro f hf xs m Q X hlk
  rw [show exportCnfStateMod.fns = exportCnfFmt_fns ++ exportCnfState_fns from rfl,
    List.mem_append] at hf
  rcases hf with hf | hf
  · have hEq : ∀ g ∈ exportCnfFmt_fns,
        exportCnfStateEnv g.name g.as g.rs = exportCnfFmtEnv g.name g.as g.rs := by
      intro g hg
      simp only [exportCnfFmt_fns, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl <;>
        (funext a' m' Q' X'; simp [exportCnfStateEnv, exportCnfFmtEnv,
          kissat_emit_byte, kissat_emit_u64, kissat_emit_dimacs_lit, kissat_emit_dimacs_hdr])
    rw [hEq f hf] at hlk
    exact exportCnfFmtFns_sound_in exportCnfStateEnv
      (fun g hg a' m' Q' X' hs => by rw [hEq g hg]; exact hs) f hf xs m Q X hlk
  · exact exportCnfStateFns_sound_in exportCnfStateEnv
      (fun _ _ _ _ h => by rwa [exportCnfStateEnv_backtrack])
      (fun _ _ _ _ h => by rwa [exportCnfStateEnv_byte])
      (fun _ _ _ _ h => by rwa [exportCnfStateEnv_lit])
      (fun _ _ _ _ h => by rwa [exportCnfStateEnv_hdr])
      (fun _ _ _ _ h => by rwa [exportCnfStateEnv_arena_next])
      (fun _ _ _ _ h => by rwa [exportCnfStateEnv_trail_units])
      (fun _ _ _ _ h => by rwa [exportCnfStateEnv_bin_clauses])
      (fun _ _ _ _ h => by rwa [exportCnfStateEnv_arena_clauses])
      (fun _ _ _ _ h => by rwa [exportCnfStateEnv_arena_next] at h)
      (fun _ _ _ _ h => by rwa [exportCnfStateEnv_trail_units] at h)
      (fun _ _ _ _ h => by rwa [exportCnfStateEnv_bin_clauses] at h)
      (fun _ _ _ _ h => by rwa [exportCnfStateEnv_arena_clauses] at h)
      (fun _ _ _ _ h => by rwa [exportCnfStateEnv_cnf_bytes] at h)
      f hf xs m Q X hlk

/-- `ModuleOk` certification for `exportCnfStateMod` (`9` fns, `1` extern `full_backtrack`, `0`
exits). -/
theorem exportCnfStateEnv_moduleOk : ModuleOk exportCnfStateEnv exportCnfStateMod :=
  Module.moduleOk_of_checkAcyclic exportCnfStateMod_checkAcyclic exportCnfStateAllFns_wf
    exportCnfStateEnv_sound

/-- Direct `exportCnfStateEnv` WP soundness corollary for `kissat_export_cnf_bytes`. -/
theorem kissat_export_cnf_bytes_sound :
    ∀ args m Q X, kissatExportCnfBytesSpec args m Q X →
      Func.wp exportCnfStateEnv kissat_export_cnf_bytes_body args m Q X :=
  kissat_export_cnf_bytes_wp exportCnfStateEnv
    (fun _ _ _ _ h => by rwa [exportCnfStateEnv_backtrack])
    (fun _ _ _ _ h => by rwa [exportCnfStateEnv_byte])
    (fun _ _ _ _ h => by rwa [exportCnfStateEnv_hdr])
    (fun _ _ _ _ h => by rwa [exportCnfStateEnv_trail_units])
    (fun _ _ _ _ h => by rwa [exportCnfStateEnv_bin_clauses])
    (fun _ _ _ _ h => by rwa [exportCnfStateEnv_arena_clauses])

/-- 1-based input DIMACS end-to-end WP corollary (`F0 = shiftDownCnf cnfIn`, `CnfVarsPos cnfIn`):
when `kissat_export_cnf_bytes` returns `1#64`, `outBytes` parses via `LratBytes.parseDimacs` to a
valid `cnfOut : CNF Nat` satisfying `cnfOut.Unsat → cnfIn.Unsat`. -/
theorem kissat_export_cnf_bytes_sound_dimacs
    {c : FullCfg} {cnfIn : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {out out_len_ptr old_len : BitVec 64} {buf : List UInt8} {R : Mem 64 → Prop}
    {m : Mem 64} {X : XPost}
    (hcap : buf.length < 2 ^ 64)
    (hlen : s.LengthsOk c)
    (hpos : CnfVarsPos cnfIn)
    (hw : FullWitnessInv c (shiftDownCnf cnfIn) F_cur s.core)
    (hm : (FullMem c s ⋆ bytes out buf ⋆ cell64 out_len_ptr old_len ⋆ R) m) :
    Func.wp exportCnfStateEnv kissat_export_cnf_bytes_body
      (c.hdr, out, BitVec.ofNat 64 buf.length, out_len_ptr, ()) m
      (fun (r, ()) m' =>
        ∃ (s' : FullState) (outBytes : List UInt8) (written : Nat),
          s'.LengthsOk c ∧
          FullWitnessInv c (shiftDownCnf cnfIn) F_cur s'.core ∧
          s'.core.cur_level = 0 ∧
          (r = 0#64 ∨ r = 1#64) ∧
          (r = 0#64 →
            (FullMem c s' ⋆ bytes out buf ⋆
              cell64 out_len_ptr (BitVec.ofNat 64 written) ⋆ R) m') ∧
          (r = 1#64 →
            outBytes = exportStateBytes s'.core ∧
            written = outBytes.length ∧
            written ≤ buf.length ∧
            (∃ cnfOut : CNF Nat,
              parseDimacs outBytes = some cnfOut ∧
              (cnfOut.Unsat → cnfIn.Unsat)) ∧
            (FullMem c s' ⋆ bytes out (outBytes ++ buf.drop written) ⋆
              cell64 out_len_ptr (BitVec.ofNat 64 written) ⋆ R) m'))
      X := by
  refine kissat_export_cnf_bytes_sound _ m _ X
    ⟨c, shiftDownCnf cnfIn, F_cur, s, out, out_len_ptr, old_len, buf, R,
      rfl, hcap, hlen, hw, hm, ?_⟩
  intro r s' outBytes written m' hlen' hw' hl0 _ _ _ _ _ _ _ _ _ hr _ h0 h1
  refine ⟨s', outBytes, written, hlen', hw', hl0, hr, fun h => (h0 h).2.2, fun h => ?_⟩
  obtain ⟨hb, hw_eq, hle, ⟨cnfOut, hp, _, hu⟩, hm'⟩ := h1 h
  exact ⟨hb, hw_eq, hle, ⟨cnfOut, hp, fun huOut => shiftDownCnf_unsat hpos (hu huOut)⟩, hm'⟩

end

end LeanQbe.T.Examples.Kissat.ExportCnfState
