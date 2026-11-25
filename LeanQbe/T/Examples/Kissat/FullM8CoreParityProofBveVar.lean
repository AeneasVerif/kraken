/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM8CoreParityProofBve0
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullDenseWatchLemmas1
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat M8 Core Parity (`FullM8CoreParity`) Rank #8 Proofs — BVE Variable (`BveVar`)

UNSAT-only `Func.wp` proofs (`public section`, clean `std3`, `XPost := False`):
1. `full_bve_var_m7_m8_wp`: certifies canonical `FullFastBveBudgets.fullBveVarDefSpec` for
   `FullM8CoreParity.full_bve_var_m7_body` (handles `use_m8 = (h->scratch_cap >= 16384ULL)` split,
   dispatches `full_bve_gates_m8` vs `full_bve_gates_m7`, and calls `full_bve_bce_side_m8`).
2. `full_bve_var_m8_wp`: certifies canonical `FullFastBveBudgets.fullBveVarDefSpec` for
   `FullM8CoreParity.full_bve_var_body`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM8CoreParity

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullDenseWatchHelpers
open LeanQbe.T.Examples.Kissat.FullFastBveBudgets
open LeanQbe.T.Examples.Kissat.FullM6BveFwd
open LeanQbe.T.Examples.Kissat.FullM7BveGates
open Kraken.Bedrock2.Test

open scoped FullArenaTactics

/-! ## 1. Private Helpers for `full_bve_var_m7_m8_wp` -/

private theorem m8_var_resBuf_mono {F_cur : List (List Nat)} {s s' : FullState}
    {r_end p : Nat} (hcv : s'.core.cur_vars = s.core.cur_vars)
    (heq : ∀ idx, p ≤ idx → idx < r_end →
      s'.scratch.scratch_buf[idx]? = s.scratch.scratch_buf[idx]?)
    (h : FullResBufOkW F_cur s r_end p) : FullResBufOkW F_cur s' r_end p := by
  induction h with
  | nil => exact .nil
  | @cons p sz hle hsz hlt hnd hent _ ih =>
    have h0 := heq p (Nat.le_refl _) (by omega)
    have hk : ∀ k < sz, s'.scratch.scratch_buf[p + 1 + k]? = s.scratch.scratch_buf[p + 1 + k]? :=
      fun k hk => heq (p + 1 + k) (by omega) (by omega)
    refine .cons hle (by rw [h0]; exact hsz)
      (fun k hkl => by rw [hk k hkl, hcv]; exact hlt k hkl) ?_ ?_
      (ih fun idx hi1 hi2 => heq idx (by omega) hi2)
    · have hm : ((List.range sz).map fun k =>
          (s'.scratch.scratch_buf[p + 1 + k]?.getD 0#32).toNat / 2) =
          ((List.range sz).map fun k =>
          (s.scratch.scratch_buf[p + 1 + k]?.getD 0#32).toNat / 2) :=
        List.map_congr_left fun k hkm => by rw [hk k (List.mem_range.mp hkm)]
      rw [hm]; exact hnd
    · have hm : ((List.range sz).map fun k =>
          (s'.scratch.scratch_buf[p + 1 + k]?.getD 0#32).toNat) =
          ((List.range sz).map fun k =>
          (s.scratch.scratch_buf[p + 1 + k]?.getD 0#32).toNat) :=
        List.map_congr_left fun k hkm => by rw [hk k (List.mem_range.mp hkm)]
      rw [hm]; exact hent

private theorem m8_var_resBuf_append {F_cur : List (List Nat)} {s s' : FullState}
    {r_off rp sz : Nat} (hcv : s'.core.cur_vars = s.core.cur_vars)
    (hpref : ∀ idx, r_off ≤ idx → idx < rp →
      s'.scratch.scratch_buf[idx]? = s.scratch.scratch_buf[idx]?)
    (h : FullResBufOkW F_cur s rp r_off)
    (hsz : (s'.scratch.scratch_buf[rp]?.getD 0#32).toNat = sz)
    (hlt : ∀ k < sz, (s'.scratch.scratch_buf[rp + 1 + k]?.getD 0#32).toNat < 2 * s'.core.cur_vars)
    (hnd : ((List.range sz).map fun k =>
      (s'.scratch.scratch_buf[rp + 1 + k]?.getD 0#32).toNat / 2).Nodup)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause ((List.range sz).map fun k =>
      (s'.scratch.scratch_buf[rp + 1 + k]?.getD 0#32).toNat))) :
    FullResBufOkW F_cur s' (rp + 1 + sz) r_off := by
  induction h with
  | nil => exact .cons (Nat.le_refl _) hsz hlt hnd hent .nil
  | @cons p psz hle hpsz hplt hpnd hpent _ ih =>
    have h0 := hpref p (Nat.le_refl _) (by omega)
    have hk : ∀ k < psz, s'.scratch.scratch_buf[p + 1 + k]? = s.scratch.scratch_buf[p + 1 + k]? :=
      fun k hk => hpref (p + 1 + k) (by omega) (by omega)
    refine .cons (by omega) (by rw [h0]; exact hpsz)
      (fun k hkl => by rw [hk k hkl, hcv]; exact hplt k hkl) ?_ ?_
      (ih fun idx hi1 hi2 => hpref idx (by omega) hi2)
    · have hm : ((List.range psz).map fun k =>
          (s'.scratch.scratch_buf[p + 1 + k]?.getD 0#32).toNat / 2) =
          ((List.range psz).map fun k =>
          (s.scratch.scratch_buf[p + 1 + k]?.getD 0#32).toNat / 2) :=
        List.map_congr_left fun k hkm => by rw [hk k (List.mem_range.mp hkm)]
      rw [hm]; exact hpnd
    · have hm : ((List.range psz).map fun k =>
          (s'.scratch.scratch_buf[p + 1 + k]?.getD 0#32).toNat) =
          ((List.range psz).map fun k =>
          (s.scratch.scratch_buf[p + 1 + k]?.getD 0#32).toNat) :=
        List.map_congr_left fun k hkm => by rw [hk k (List.mem_range.mp hkm)]
      rw [hm]; exact hpent

private theorem m8_var_bveEntry_weak {F_cur : List (List Nat)} {s : FullState} {lit : Nat}
    {w : BitVec 32} (h : FullBveEntryOkW F_cur s lit w) : FullBveWeakItemOk s.core w := by
  unfold FullBveEntryOkW at h; unfold FullBveWeakItemOk; split at h <;> simp_all

private theorem m8_var_bveEntry_bceEntry {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hdw : FullDenseInvW c F0 F_cur s) {lit : Nat} {w : BitVec 32}
    (h : FullBveEntryOkW F_cur s lit w) :
    FullBveVarSpecs.FullBveTryBceEntryOk c s w ∧
    ((w &&& 0x80000000#32) ≠ 0#32 → (w &&& 0x7FFFFFFF#32).toNat < 2 * s.core.cur_vars) := by
  unfold FullBveEntryOkW at h; unfold FullBveVarSpecs.FullBveTryBceEntryOk
  have hcv := hdw.1.core_ok.cur_vars_le
  by_cases hb : (w &&& 0x80000000#32) ≠ 0#32
  · rw [ite_eq_left hb] at h ⊢; exact ⟨by omega, fun _ => h.1⟩
  · rw [ite_eq_right hb] at h ⊢
    have hwf := hdw.2.1.arena.refs_wf w.toNat h.1
    refine ⟨⟨h.1, Nat.le_trans hwf.2.2.1 hwf.2.2.2.1, fun l hl => ?_,
      hdw.2.2.2.1 w.toNat h.1 h.2⟩, fun hne => absurd hne hb⟩
    have := hdw.2.1.arena.lits_lt w.toNat h.1 h.2 l hl; omega

private theorem m8_var_bveEntry_bceOpp {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hdw : FullDenseInvW c F0 F_cur s) {lit : Nat} {w : BitVec 32}
    (h : FullBveEntryOkW F_cur s lit w) :
    FullBveVarSpecs.FullBveTryBceOppOk c s w := by
  unfold FullBveEntryOkW at h; unfold FullBveVarSpecs.FullBveTryBceOppOk
  have hcv := hdw.1.core_ok.cur_vars_le
  by_cases hb : (w &&& 0x80000000#32) ≠ 0#32
  · rw [ite_eq_left hb] at h ⊢; omega
  · rw [ite_eq_right hb] at h ⊢
    have hwf := hdw.2.1.arena.refs_wf w.toNat h.1
    refine ⟨h.1, Nat.le_trans hwf.2.2.1 hwf.2.2.2.1, fun l hl => ?_⟩
    have := hdw.2.1.arena.lits_lt w.toNat h.1 h.2 l hl; omega

private theorem m8_var_bveEntry_bceEntry_congr {c : FullCfg} {s s' : FullState} {w : BitVec 32}
    (h : FullBveVarSpecs.FullBveTryBceEntryOk c s w ∧
      ((w &&& 0x80000000#32) ≠ 0#32 → (w &&& 0x7FFFFFFF#32).toNat < 2 * s.core.cur_vars))
    (hcv : s'.core.cur_vars = s.core.cur_vars)
    (hrefs : fullArenaClauseRefs s' = fullArenaClauseRefs s)
    (hal : s'.core.arena_len = s.core.arena_len)
    (hper : ∀ r ∈ fullArenaClauseRefs s,
      fullArenaClauseSize s' r = fullArenaClauseSize s r ∧
      fullArenaClauseLits s' r = fullArenaClauseLits s r) :
    FullBveVarSpecs.FullBveTryBceEntryOk c s' w ∧
    ((w &&& 0x80000000#32) ≠ 0#32 → (w &&& 0x7FFFFFFF#32).toNat < 2 * s'.core.cur_vars) := by
  refine ⟨?_, fun hb => by rw [hcv]; exact h.2 hb⟩
  have h1 := h.1
  unfold FullBveVarSpecs.FullBveTryBceEntryOk at h1 ⊢
  by_cases hb : (w &&& 0x80000000#32) ≠ 0#32
  · rw [ite_eq_left hb] at h1 ⊢; exact h1
  · rw [ite_eq_right hb] at h1 ⊢
    rw [hrefs, hal, (hper _ h1.1).1, (hper _ h1.1).2]; exact h1

private theorem m8_var_bveEntry_bceOpp_congr {c : FullCfg} {s s' : FullState} {w : BitVec 32}
    (h : FullBveVarSpecs.FullBveTryBceOppOk c s w)
    (hrefs : fullArenaClauseRefs s' = fullArenaClauseRefs s)
    (hal : s'.core.arena_len = s.core.arena_len)
    (hper : ∀ r ∈ fullArenaClauseRefs s,
      fullArenaClauseSize s' r = fullArenaClauseSize s r ∧
      fullArenaClauseLits s' r = fullArenaClauseLits s r) :
    FullBveVarSpecs.FullBveTryBceOppOk c s' w := by
  unfold FullBveVarSpecs.FullBveTryBceOppOk at h ⊢
  by_cases hb : (w &&& 0x80000000#32) ≠ 0#32
  · rw [ite_eq_left hb] at h ⊢; exact h
  · rw [ite_eq_right hb] at h ⊢
    rw [hrefs, hal, (hper _ h.1).1, (hper _ h.1).2]; exact h

private theorem m8_var_bveEntry_extNeed {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hdw : FullDenseInvW c F0 F_cur s) {lit : Nat} {w : BitVec 32}
    (h : FullBveEntryOkW F_cur s lit w) :
    (w &&& 0x80000000#32) ≠ 0#32 ∨ w.toNat + 2 < c.arena_cap := by
  unfold FullBveEntryOkW at h
  by_cases hb : (w &&& 0x80000000#32) ≠ 0#32
  · exact Or.inl hb
  · right; rw [ite_eq_right hb] at h
    have hwf := hdw.2.1.arena.refs_wf w.toNat h.1
    have hal := hdw.1.core_ok.arena_len_le; omega

private theorem m8_var_fullDenseInvW_setInact {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (h : FullDenseInvW c F0 F_cur s)
    {fl' : List (BitVec 32)} {unass' : BitVec 64} (hfl : fl'.length = c.max_vars) :
    FullDenseInvW c F0 F_cur
      { s with core := { s.core with flags := fl', unassigned := unass' } } :=
  ⟨⟨{ h.1.core_ok with flags_len := hfl }, h.1.scratch_ok⟩,
   { h.2.1 with
     arena := { h.2.1.arena with len_ok := h.2.1.arena.len_ok }
     watches := h.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) },
   h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

private theorem m8_var_list_take_map_eq_range {xs : List (BitVec 32)} {n : Nat}
    (hn : n ≤ xs.length) :
    (xs.take n).map BitVec.toNat =
      (List.range n).map (fun k => (xs[k]?.getD 0#32).toNat) := by
  apply List.ext_getElem
  · simp [hn]
  · intro i hi1 hi2
    simp only [List.getElem_map, List.getElem_take, List.getElem_range]
    have hi : i < n := by simp at hi2; exact hi2
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]

private theorem m8_var_list_take_map_div2_eq_range {xs : List (BitVec 32)} {n : Nat}
    (hn : n ≤ xs.length) :
    (xs.take n).map (fun x => x.toNat / 2) =
      (List.range n).map (fun k => (xs[k]?.getD 0#32).toNat / 2) := by
  apply List.ext_getElem
  · simp [hn]
  · intro i hi1 hi2
    simp only [List.getElem_map, List.getElem_take, List.getElem_range]
    have hi : i < n := by simp at hi2; exact hi2
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]

private theorem m8_var_pl_nl_eq (v : BitVec 32) (hv : v.toNat < 2 * 2 ^ 28) :
    (v <<< (1 : Nat)).toNat = 2 * v.toNat ∧
    ((v <<< (1 : Nat)) ||| (1 : BitVec 32)).toNat = 2 * v.toNat + 1 := by
  have h := m8_pl_nl_eq v hv
  exact ⟨h.1, by simpa [show ((1 : BitVec 32)) = 1#32 from rfl] using h.2⟩

private theorem m8_var_layout_ok {scap : Nat}
    {occ_lim neg_off pos_mask neg_mask gf_idx rg_idx : BitVec 32} {r_off : BitVec 64}
    (hsc2048 : 2048 ≤ scap)
    (hocc : (16384 ≤ scap ∧ occ_lim = 2001#32) ∨ (scap < 16384 ∧ occ_lim = 512#32))
    (hneg : neg_off = occ_lim)
    (hpm : (occ_lim = 2001#32 ∧ pos_mask = 4002#32) ∨ (occ_lim = 512#32 ∧ pos_mask = 1024#32))
    (hnm : (occ_lim = 2001#32 ∧ neg_mask = 4066#32) ∨ (occ_lim = 512#32 ∧ neg_mask = 1040#32))
    (hgf : (occ_lim = 2001#32 ∧ gf_idx = 4130#32) ∨ (occ_lim = 512#32 ∧ gf_idx = 1056#32))
    (hrg : (occ_lim = 2001#32 ∧ rg_idx = 4131#32) ∨ (occ_lim = 512#32 ∧ rg_idx = 1057#32))
    (hroff : (occ_lim = 2001#32 ∧ r_off = 4192#64) ∨ (occ_lim = 512#32 ∧ r_off = 1088#64)) :
    occ_lim.toNat + occ_lim.toNat ≤ r_off.toNat ∧
    r_off.toNat ≤ scap ∧
    gf_idx.toNat < r_off.toNat ∧
    rg_idx.toNat < r_off.toNat ∧
    (∀ i : BitVec 32, i.toNat < occ_lim.toNat →
      ((pos_mask + (i >>> (5 : Nat))).setWidth 64).toNat < r_off.toNat) ∧
    (∀ j : BitVec 32, j.toNat < occ_lim.toNat →
      ((neg_mask + (j >>> (5 : Nat))).setWidth 64).toNat < r_off.toNat) ∧
    (16384 ≤ scap → occ_lim = 2001#32 ∧ neg_off.toNat = 2001) ∧
    (scap < 16384 → occ_lim = 512#32 ∧ neg_off.toNat = 512) := by
  subst hneg
  have hne : (2001#32 : BitVec 32) ≠ 512#32 := by decide
  rcases hocc with ⟨hsc16, rfl⟩ | ⟨hsc16, rfl⟩
  · rcases hpm.resolve_right (fun h => hne h.1) with ⟨_, rfl⟩
    rcases hnm.resolve_right (fun h => hne h.1) with ⟨_, rfl⟩
    rcases hgf.resolve_right (fun h => hne h.1) with ⟨_, rfl⟩
    rcases hrg.resolve_right (fun h => hne h.1) with ⟨_, rfl⟩
    rcases hroff.resolve_right (fun h => hne h.1) with ⟨_, rfl⟩
    refine ⟨by decide, by simp; omega, by decide, by decide, ?_, ?_,
      fun _ => ⟨rfl, rfl⟩, fun hlt => by omega⟩
    · intro i hi
      rw [m6_zext32_toNat, BitVec.toNat_add, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      simp only [BitVec.toNat_ofNat] at hi ⊢
      rw [Nat.mod_eq_of_lt (by omega)]; omega
    · intro j hj
      rw [m6_zext32_toNat, BitVec.toNat_add, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      simp only [BitVec.toNat_ofNat] at hj ⊢
      rw [Nat.mod_eq_of_lt (by omega)]; omega
  · rcases hpm.resolve_left (fun h => hne h.1.symm) with ⟨_, rfl⟩
    rcases hnm.resolve_left (fun h => hne h.1.symm) with ⟨_, rfl⟩
    rcases hgf.resolve_left (fun h => hne h.1.symm) with ⟨_, rfl⟩
    rcases hrg.resolve_left (fun h => hne h.1.symm) with ⟨_, rfl⟩
    rcases hroff.resolve_left (fun h => hne h.1.symm) with ⟨_, rfl⟩
    refine ⟨by decide, by simp; omega, by decide, by decide, ?_, ?_,
      fun hge => by omega, fun _ => ⟨rfl, rfl⟩⟩
    · intro i hi
      rw [m6_zext32_toNat, BitVec.toNat_add, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      simp only [BitVec.toNat_ofNat] at hi ⊢
      rw [Nat.mod_eq_of_lt (by omega)]; omega
    · intro j hj
      rw [m6_zext32_toNat, BitVec.toNat_add, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      simp only [BitVec.toNat_ofNat] at hj ⊢
      rw [Nat.mod_eq_of_lt (by omega)]; omega

/-! ## 2. `full_bve_var_m7_m8_wp` (Canonical `FullFastBveBudgets.fullBveVarDefSpec`) -/

/-- Certifies canonical `FullFastBveBudgets.fullBveVarDefSpec` for
`FullM8CoreParity.full_bve_var_m7_body` (M8 `2001`-occ / `16384`-scratch split + legacy `512`
fallback + `full_bve_bce_side_m8`). -/
theorem full_bve_var_m7_m8_wp (Γ : Env)
    (hCollect : ∀ a m Q X, Full.fullBveCollectSpec a m Q X →
      Γ "full_bve_collect_m7" [i64, i32, i64, i32] [i32] a m Q X)
    (hExtNeed : ∀ a m Q X, Full.fullBveExtNeedSpec a m Q X →
      Γ "full_bve_ext_need" [i64, i32, i32] [i64] a m Q X)
    (hWeaken : ∀ a m Q X, FullFastBveBudgets.fullBveWeakenTmkSpec a m Q X →
      Γ "full_bve_weaken" [i64, i32, i32, i32] [.bool] a m Q X)
    (hSetInact : ∀ a m Q X, Full.fullSetInactiveSpec a m Q X →
      Γ "full_set_inactive" [i64, i32, i32] [] a m Q X)
    (hGatesM8 : ∀ a m Q X, m8BveGatesSpec a m Q X →
      Γ "full_bve_gates_m8" [i64, i32, i32, i32] [] a m Q X)
    (hGatesM7 : ∀ a m Q X, FullM7BveGates.fullBveGatesM7Spec a m Q X →
      Γ "full_bve_gates_m7" [i64, i32, i32, i32] [] a m Q X)
    (hResPair : ∀ a m Q X, Full.fullBveResolvePairSpec a m Q X →
      Γ "full_bve_resolve_pair" [i64, i32, i32, i32] [.bool] a m Q X)
    (hDefrag : ∀ a m Q X, Full.fullWstackDefragSpec a m Q X →
      Γ "full_wstack_defrag" [i64] [] a m Q X)
    (hCommit : ∀ a m Q X, FullFastBveBudgets.fullBveCommitResTmkSpec a m Q X →
      Γ "full_bve_commit_res" [i64, i64, i64] [i64] a m Q X)
    (hFlushUnits : ∀ a m Q X, FullM6BveFwd.fullDenseFlushUnitsM6Spec a m Q X →
      Γ "full_dense_flush_units_m7" [i64] [.bool] a m Q X)
    (hBceSide : ∀ a m Q X, m8BveBceSideSpec a m Q X →
      Γ "full_bve_bce_side_m8" [i64, i32, i32, i32, i32, i32] [] a m Q X) :
    ∀ a m Q X, FullFastBveBudgets.fullBveVarDefSpec a m Q X →
      Func.wp Γ FullM8CoreParity.full_bve_var_m7_body a m Q X := by
  rintro ⟨h, v, ⟨⟩⟩ m0 Q X ⟨c, F0, s0, R, rfl, hd0, htmk0, hv_lt, hm0, hQ⟩
  have hmx := c.hmaxv; have hsc := c.hscr; have harc := c.harena; have hwc := c.hwcap
  unfold dimacsBound at hmx hsc harc hwc
  obtain ⟨F_cur, hdw0⟩ := hd0.exists_witness
  have hcv_le := hdw0.1.core_ok.cur_vars_le
  have hplnl := m8_var_pl_nl_eq v (by omega)
  unfold Func.wp FullM8CoreParity.full_bve_var_m7_body
  c0_hsplit
  · c0_hsteps!
    exact hQ 1#64 s0 m0 hd0 htmk0 (Nat.le_refl _) (Nat.le_refl _) (Or.inl rfl) (by simp) hm0
  · have hsc2048 : 2048 ≤ c.scratch_cap := by
      rw [Nat.mod_eq_of_lt (by omega), show (2048 : BitVec 64).toNat = 2048 from rfl] at hc
      omega
    c0_hsteps_nogrp
    -- Join 1: `occ_lim = use_m8 ? 2001u : 512u`
    refine wp_join_state_pure (ts := [i32]) (α := BitVec 32) (fun x => (x, ()))
      (fun x => (16384 ≤ c.scratch_cap ∧ x = 2001#32) ∨ (c.scratch_cap < 16384 ∧ x = 512#32))
      ?_ (fun J1 hJ1 => by
        c0_hsplit
        · c0_hsteps!
          exact hJ1 2001#32 (Or.inl ⟨by
            rw [Nat.mod_eq_of_lt (by omega),
              show (16384 : BitVec 64).toNat = 16384 from rfl] at hc; omega, rfl⟩)
        · c0_hsteps!
          exact hJ1 512#32 (Or.inr ⟨by
            rw [Nat.mod_eq_of_lt (by omega),
              show (16384 : BitVec 64).toNat = 16384 from rfl] at hc; omega, rfl⟩))
    intro _ occ_lim hocc_cas
    -- Join 2: `neg_off = use_m8 ? 2001u : 512u`
    refine wp_join_state_pure (ts := [i32]) (α := BitVec 32) (fun x => (x, ()))
      (fun x => x = occ_lim)
      ?_ (fun J2 hJ2 => by
        c0_hsplit
        · have hge : 16384 ≤ c.scratch_cap := by
            rw [Nat.mod_eq_of_lt (by omega),
              show (16384 : BitVec 64).toNat = 16384 from rfl] at hc; omega
          have ho : occ_lim = 2001#32 := hocc_cas.elim (·.2) (fun h => by omega)
          c0_hsteps!; exact hJ2 2001#32 ho.symm
        · have hlt : c.scratch_cap < 16384 := by
            rw [Nat.mod_eq_of_lt (by omega),
              show (16384 : BitVec 64).toNat = 16384 from rfl] at hc; omega
          have ho : occ_lim = 512#32 := hocc_cas.elim (fun h => by omega) (·.2)
          c0_hsteps!; exact hJ2 512#32 ho.symm)
    intro _ neg_off hneg_eq
    -- Join 3: `pos_mask = use_m8 ? 4002u : 1024u`
    refine wp_join_state_pure (ts := [i32]) (α := BitVec 32) (fun x => (x, ()))
      (fun x => (occ_lim = 2001#32 ∧ x = 4002#32) ∨ (occ_lim = 512#32 ∧ x = 1024#32))
      ?_ (fun J3 hJ3 => by
        c0_hsplit
        · have hge : 16384 ≤ c.scratch_cap := by
            rw [Nat.mod_eq_of_lt (by omega),
              show (16384 : BitVec 64).toNat = 16384 from rfl] at hc; omega
          have ho : occ_lim = 2001#32 := hocc_cas.elim (·.2) (fun h => by omega)
          c0_hsteps!; exact hJ3 4002#32 (Or.inl ⟨ho, rfl⟩)
        · have hlt : c.scratch_cap < 16384 := by
            rw [Nat.mod_eq_of_lt (by omega),
              show (16384 : BitVec 64).toNat = 16384 from rfl] at hc; omega
          have ho : occ_lim = 512#32 := hocc_cas.elim (fun h => by omega) (·.2)
          c0_hsteps!; exact hJ3 1024#32 (Or.inr ⟨ho, rfl⟩))
    intro _ pos_mask hpm_cas
    -- Join 4: `neg_mask = use_m8 ? 4066u : 1040u`
    refine wp_join_state_pure (ts := [i32]) (α := BitVec 32) (fun x => (x, ()))
      (fun x => (occ_lim = 2001#32 ∧ x = 4066#32) ∨ (occ_lim = 512#32 ∧ x = 1040#32))
      ?_ (fun J4 hJ4 => by
        c0_hsplit
        · have hge : 16384 ≤ c.scratch_cap := by
            rw [Nat.mod_eq_of_lt (by omega),
              show (16384 : BitVec 64).toNat = 16384 from rfl] at hc; omega
          have ho : occ_lim = 2001#32 := hocc_cas.elim (·.2) (fun h => by omega)
          c0_hsteps!; exact hJ4 4066#32 (Or.inl ⟨ho, rfl⟩)
        · have hlt : c.scratch_cap < 16384 := by
            rw [Nat.mod_eq_of_lt (by omega),
              show (16384 : BitVec 64).toNat = 16384 from rfl] at hc; omega
          have ho : occ_lim = 512#32 := hocc_cas.elim (fun h => by omega) (·.2)
          c0_hsteps!; exact hJ4 1040#32 (Or.inr ⟨ho, rfl⟩))
    intro _ neg_mask hnm_cas
    -- Join 5: `gf_idx = use_m8 ? 4130u : 1056u`
    refine wp_join_state_pure (ts := [i32]) (α := BitVec 32) (fun x => (x, ()))
      (fun x => (occ_lim = 2001#32 ∧ x = 4130#32) ∨ (occ_lim = 512#32 ∧ x = 1056#32))
      ?_ (fun J5 hJ5 => by
        c0_hsplit
        · have hge : 16384 ≤ c.scratch_cap := by
            rw [Nat.mod_eq_of_lt (by omega),
              show (16384 : BitVec 64).toNat = 16384 from rfl] at hc; omega
          have ho : occ_lim = 2001#32 := hocc_cas.elim (·.2) (fun h => by omega)
          c0_hsteps!; exact hJ5 4130#32 (Or.inl ⟨ho, rfl⟩)
        · have hlt : c.scratch_cap < 16384 := by
            rw [Nat.mod_eq_of_lt (by omega),
              show (16384 : BitVec 64).toNat = 16384 from rfl] at hc; omega
          have ho : occ_lim = 512#32 := hocc_cas.elim (fun h => by omega) (·.2)
          c0_hsteps!; exact hJ5 1056#32 (Or.inr ⟨ho, rfl⟩))
    intro _ gf_idx hgf_cas
    -- Join 6: `rg_idx = use_m8 ? 4131u : 1057u`
    refine wp_join_state_pure (ts := [i32]) (α := BitVec 32) (fun x => (x, ()))
      (fun x => (occ_lim = 2001#32 ∧ x = 4131#32) ∨ (occ_lim = 512#32 ∧ x = 1057#32))
      ?_ (fun J6 hJ6 => by
        c0_hsplit
        · have hge : 16384 ≤ c.scratch_cap := by
            rw [Nat.mod_eq_of_lt (by omega),
              show (16384 : BitVec 64).toNat = 16384 from rfl] at hc; omega
          have ho : occ_lim = 2001#32 := hocc_cas.elim (·.2) (fun h => by omega)
          c0_hsteps!; exact hJ6 4131#32 (Or.inl ⟨ho, rfl⟩)
        · have hlt : c.scratch_cap < 16384 := by
            rw [Nat.mod_eq_of_lt (by omega),
              show (16384 : BitVec 64).toNat = 16384 from rfl] at hc; omega
          have ho : occ_lim = 512#32 := hocc_cas.elim (fun h => by omega) (·.2)
          c0_hsteps!; exact hJ6 1057#32 (Or.inr ⟨ho, rfl⟩))
    intro _ rg_idx hrg_cas
    -- Join 7: `r_off = use_m8 ? 4192ULL : 1088ULL`
    refine wp_join_state_pure (ts := [i64]) (α := BitVec 64) (fun x => (x, ()))
      (fun x => (occ_lim = 2001#32 ∧ x = 4192#64) ∨ (occ_lim = 512#32 ∧ x = 1088#64))
      ?_ (fun J7 hJ7 => by
        c0_hsplit
        · have hge : 16384 ≤ c.scratch_cap := by
            rw [Nat.mod_eq_of_lt (by omega),
              show (16384 : BitVec 64).toNat = 16384 from rfl] at hc; omega
          have ho : occ_lim = 2001#32 := hocc_cas.elim (·.2) (fun h => by omega)
          c0_hsteps!; exact hJ7 4192#64 (Or.inl ⟨ho, rfl⟩)
        · have hlt : c.scratch_cap < 16384 := by
            rw [Nat.mod_eq_of_lt (by omega),
              show (16384 : BitVec 64).toNat = 16384 from rfl] at hc; omega
          have ho : occ_lim = 512#32 := hocc_cas.elim (fun h => by omega) (·.2)
          c0_hsteps!; exact hJ7 1088#64 (Or.inr ⟨ho, rfl⟩))
    intro _ r_off hroff_cas
    -- Unified layout arithmetic valid in BOTH M8 (`2001`/`4192`) and M7 (`512`/`1088`) modes
    obtain ⟨hocc_le_roff, hroff_le_sc, hgf_lt_roff, hrg_lt_roff, hpm_lt_roff, hnm_lt_roff,
      hm8_eqs, hm7_eqs⟩ :=
      m8_var_layout_ok hsc2048 hocc_cas hneg_eq hpm_cas hnm_cas hgf_cas hrg_cas hroff_cas
    clear hocc_cas hpm_cas hnm_cas hgf_cas hrg_cas hroff_cas
    have hneg_off_lt : neg_off.toNat + occ_lim.toNat ≤ c.scratch_cap := by
      rw [hneg_eq]; omega
    have hneg_ptr : c.pScratchBuf + neg_off.setWidth 64 * 4#64 =
        c.pScratchBuf + BitVec.ofNat 64 (4 * neg_off.toNat) := by
      congr 1; apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_mul, m6_zext32_toNat, show (4#64 : BitVec 64).toNat = 4 from rfl,
        BitVec.toNat_ofNat]
      have : neg_off.toNat < 2 ^ 32 := neg_off.isLt
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
    c0_hsteps_nogrp
    -- Collect positive occurrences into `scr[0 ..< np)` (`cap = occ_lim`)
    refine wp_call_of_spec _ _ (hCollect _ _ _ _ ?_)
    dsimp only [vals, Arg.val]
    refine ⟨c, F0, F_cur, s0, 0, R, rfl, hdw0, by rw [hplnl.1]; omega,
      by simp, by simp; omega, hm0, ?_⟩
    intro np scr1 m1
    dsimp only
    intro hsc1 hout1 hnp_ok hm1
    let s1 : FullState := { s0 with scratch := { s0.scratch with scratch_buf := scr1 } }
    have hdw1 : FullDenseInvW c F0 F_cur s1 := m8_fullDenseInvW_scr hdw0 hsc1
    c0_hsteps_nogrp
    -- Collect negative occurrences into `scr[neg_off ..< neg_off + nn)` (`cap = occ_lim`)
    refine wp_call_of_spec _ _ (hCollect _ _ _ _ ?_)
    dsimp only [vals, Arg.val]
    refine ⟨c, F0, F_cur, s1, neg_off.toNat, R, rfl, hdw1,
      by dsimp only [s1]; rw [hplnl.2]; omega, hneg_ptr, hneg_off_lt, hm1, ?_⟩
    intro nn scr2 m2
    dsimp only
    intro hsc2 hout2 hnn_ok hm2
    let s2 : FullState := { s1 with scratch := { s1.scratch with scratch_buf := scr2 } }
    have hdw2 : FullDenseInvW c F0 F_cur s2 := m8_fullDenseInvW_scr hdw1 hsc2
    c0_hsplit
    · c0_hsteps!
      exact hQ 1#64 s2 m2 hdw2.toDense htmk0 (Nat.le_refl _) (Nat.le_refl _) (Or.inl rfl)
        (by simp) hm2
    · have hnp_ne : np ≠ 0xFFFFFFFF#32 := hc
      c0_hsplit
      · c0_hsteps!
        exact hQ 1#64 s2 m2 hdw2.toDense htmk0 (Nat.le_refl _) (Nat.le_refl _) (Or.inl rfl)
          (by simp) hm2
      · have hnn_ne : nn ≠ 0xFFFFFFFF#32 := hc
        obtain ⟨hnp_le, hent_p1⟩ := hnp_ok.resolve_left hnp_ne
        obtain ⟨hnn_le, hent_n2⟩ := hnn_ok.resolve_left hnn_ne
        have hent_p2 : ∀ i < np.toNat,
            FullBveEntryOkW F_cur s2 (2 * v.toNat) (scr2[i]?.getD 0#32) := fun i hi => by
          rw [hout2 i (by omega) (Or.inl (by rw [hneg_eq]; omega))]
          have h := hent_p1 i hi; rw [Nat.zero_add, hplnl.1] at h
          exact m8_bveEntry_congr_core h rfl rfl rfl
        have hent_n2' : ∀ j < nn.toNat,
            FullBveEntryOkW F_cur s2 (2 * v.toNat + 1)
              (scr2[neg_off.toNat + j]?.getD 0#32) := fun j hj => by
          have h := hent_n2 j hj; rw [hplnl.2] at h; exact h
        c0_hsteps_nogrp
        refine wp_call_of_spec _ _ (hExtNeed _ _ _ _ ?_)
        dsimp only [vals, Arg.val]
        refine ⟨c, s2, R, rfl, hdw2.1, by simp; omega, fun i hi => by
          dsimp only [s2]; rw [show ((0 : BitVec 32)).toNat = 0 from rfl, Nat.zero_add]
          exact m8_var_bveEntry_extNeed hdw2 (hent_p2 i hi), hm2, ?_⟩
        intro en1
        c0_hsteps_nogrp
        refine wp_call_of_spec _ _ (hExtNeed _ _ _ _ ?_)
        dsimp only [vals, Arg.val]
        refine ⟨c, s2, R, rfl, hdw2.1, by omega, fun j hj => by
          dsimp only [s2]; exact m8_var_bveEntry_extNeed hdw2 (hent_n2' j hj), hm2, ?_⟩
        intro en2
        c0_hsteps_nogrp
        -- Pure-literal fast path (`ext_ok && (np == 0 || nn == 0)`) vs general BVE path (`J25`)
        refine wp_join0 (P := fun mj => mj = m2)
          (fun _ mj hmj => by
            rcases hmj.symm with rfl
            c0_hsteps_nogrp
            refine wp_join_state (ts := [i64, i64, i64, .bool])
              (α := BitVec 64 × BitVec 64 × BitVec 64 × Bool × FullState)
              (fun x => (x.1, x.2.1, x.2.2.1, x.2.2.2.1, ()))
              (fun x mi =>
                let si := x.2.2.2.2
                let rp := x.1
                FullDenseInvW c F0 F_cur si ∧ TmkZero si ∧
                si.core.cur_vars = s0.core.cur_vars ∧ si.core.arena = s2.core.arena ∧
                si.core.arena_len = s2.core.arena_len ∧
                si.core.fuel.toNat ≤ s0.core.fuel.toNat ∧
                r_off.toNat ≤ rp.toNat ∧ rp.toNat ≤ c.scratch_cap ∧
                FullResBufOkW F_cur si rp.toNat r_off.toNat ∧
                (∀ k < np.toNat, si.scratch.scratch_buf[k]? = s2.scratch.scratch_buf[k]?) ∧
                (∀ k < nn.toNat,
                  si.scratch.scratch_buf[neg_off.toNat + k]? =
                    s2.scratch.scratch_buf[neg_off.toNat + k]?) ∧
                (FullMem c si ⋆ R) mi)
              (fun _ ⟨rp, r_cnt, w_est, fit, si⟩ mi
                  ⟨hdwi, htmki, hcvi, hari, hali, hfli, hrp_lo, hrp_hi, hres_i, hkeep_pi,
                    hkeep_ni, hmi⟩ => by
                c0_hsteps_nogrp
                -- Post-resolution pre-check + commit (`fit = true`) or BCE fallback (`fit = false`)
                refine wp_join_state (ts := [.bool]) (α := Bool × FullState) (fun x => (x.1, ()))
                  (fun x mp =>
                    FullDenseInvW c F0 F_cur x.2 ∧ TmkZero x.2 ∧
                    x.2.core.cur_vars = s0.core.cur_vars ∧ x.2.core.arena = s2.core.arena ∧
                    x.2.core.arena_len = s2.core.arena_len ∧
                    x.2.core.fuel.toNat ≤ s0.core.fuel.toNat ∧
                    FullResBufOkW F_cur x.2 rp.toNat r_off.toNat ∧
                    (∀ k < np.toNat, x.2.scratch.scratch_buf[k]? = s2.scratch.scratch_buf[k]?) ∧
                    (∀ k < nn.toNat,
                      x.2.scratch.scratch_buf[neg_off.toNat + k]? =
                        s2.scratch.scratch_buf[neg_off.toNat + k]?) ∧
                    (FullMem c x.2 ⋆ R) mp)
                  (fun _ ⟨fit_f, sf⟩ mf
                      ⟨hdwf, htmkf, hcvf, harf, half, hflf, hresf, hkeep_pf, hkeep_nf, hmf⟩ => by
                    dsimp only at hcvf harf half hflf
                    have hent_pf : ∀ k < np.toNat, FullBveEntryOkW F_cur sf (2 * v.toNat)
                        (sf.scratch.scratch_buf[k]?.getD 0#32) := fun k hk => by
                      rw [hkeep_pf k hk]; exact m8_bveEntry_congr_core (hent_p2 k hk) hcvf harf half
                    have hent_nf : ∀ k < nn.toNat, FullBveEntryOkW F_cur sf (2 * v.toNat + 1)
                        (sf.scratch.scratch_buf[neg_off.toNat + k]?.getD 0#32) := fun k hk => by
                      rw [hkeep_nf k hk]
                      exact m8_bveEntry_congr_core (hent_n2' k hk) hcvf harf half
                    c0_hsplit
                    · -- `fit_f = true`: weaken `pl` & `nl`, set inactive, commit, flush units
                      c0_hsteps_nogrp
                      refine wp_join0 (P := fun mo => ∃ so : FullState,
                          FullDenseInvW c F0 F_cur so ∧ TmkZero so ∧
                          so.core.cur_vars = s0.core.cur_vars ∧
                          so.core.fuel.toNat ≤ s0.core.fuel.toNat ∧
                          (FullMem c so ⋆ R) mo)
                        (fun _ mo ⟨so, hdwo, htmko, hcvo, hflo, hmo⟩ => by
                          c0_hsteps!
                          let soom : FullState := { so with core := { so.core with oom := 1#64 } }
                          exact hQ 2#64 soom _ (m6_fullDenseInvW_with_oom hdwo 1#64).toDense htmko
                            (by dsimp only [soom]; omega) hflo (Or.inr (Or.inl rfl)) (by simp) hm)
                        (fun J39 hJ39 => by
                          c0_hsteps_nogrp
                          refine wp_call_of_spec _ _ (hWeaken _ _ _ _ ?_)
                          dsimp only [vals, Arg.val]
                          refine ⟨c, F0, F_cur, sf, R, rfl, hdwf, htmkf,
                            by rw [hplnl.1, hcvf]; omega,
                            by rw [show (0 : BitVec 32).toNat = 0 from rfl]; omega, fun k hk => by
                              rw [show (0 : BitVec 32).toNat = 0 from rfl, Nat.zero_add]
                              exact m8_var_bveEntry_weak (hent_pf k hk), hmf, ?_⟩
                          intro ok1 sw1 mw1 hdww1 htmkw1 hcvw1 hflw1 hscrw1 hrefsw1 hmw1
                          c0_hsplit
                          · c0_hsteps_nogrp
                            refine wp_call_of_spec _ _ (hWeaken _ _ _ _ ?_)
                            dsimp only [vals, Arg.val]
                            refine ⟨c, F0, F_cur, sw1, R, rfl, hdww1, htmkw1,
                              by rw [hplnl.2, hcvw1, hcvf]; omega,
                              by omega,
                              fun k hk => by
                                rw [hscrw1]
                                have hwk := m8_var_bveEntry_weak (hent_nf k hk)
                                unfold FullBveWeakItemOk at hwk ⊢
                                split at hwk
                                · next hb =>
                                    rw [ite_eq_left hb] at ⊢; rw [hcvw1]; exact hwk
                                · next hb =>
                                    rw [ite_eq_right hb] at ⊢
                                    change _ ∈ fullArenaClauseRefs sw1; rw [hrefsw1]; exact hwk,
                              hmw1, ?_⟩
                            intro ok2 sw2 mw2 hdww2 htmkw2 hcvw2 hflw2 hscrw2 _ hmw2
                            c0_hsplit
                            · c0_hsteps_nogrp
                              refine wp_call_of_spec _ _ (hSetInact _ _ _ _ ?_)
                              dsimp only [vals, Arg.val]
                              refine ⟨c, sw2, R, rfl, hdww2.1, hmw2, ?_⟩
                              rw [ite_eq_right (by rw [hcvw2, hcvw1, hcvf]; omega)]
                              intro fl' unass' m_i hfl_i
                              dsimp only
                              intro hm_i
                              let si' : FullState := { sw2 with core := { sw2.core with
                                flags := fl', unassigned := unass' } }
                              have hdwi' := m8_var_fullDenseInvW_setInact hdww2
                                (unass' := unass') hfl_i
                              c0_hsteps_nogrp
                              let sbve : FullState := { si' with scratch := { si'.scratch with
                                bve_cnt := si'.scratch.bve_cnt + 1#64 } }
                              have hdwbve := m6_fullDenseInvW_with_scratch hdwi'
                                (sc' := sbve.scratch) { hdwi'.1.scratch_ok with } rfl rfl
                              have hres_bve : FullResBufOkW F_cur sbve rp.toNat r_off.toNat :=
                                m8_var_resBuf_mono (s := sf) (s' := sbve)
                                  (hcvw2.trans hcvw1)
                                  (fun idx _ _ => by dsimp only [sbve, si']; rw [hscrw2, hscrw1])
                                  hresf
                              refine wp_call_of_spec _ _ (hCommit _ _ _ _ ?_)
                              refine ⟨c, F0, F_cur, sbve, R, rfl, hdwbve, htmkw2.congr rfl rfl,
                                hrp_lo, hrp_hi, hres_bve, hm, ?_⟩
                              intro cr_r sc mc hdwc htmkc hcvc hflc hcr_disj hcr20 hmc
                              dsimp only [sbve, si'] at hcvc hflc
                              c0_hsplit
                              · c0_hsteps!
                                exact hQ 20#64 sc mc hdwc.toDense htmkc (by omega)
                                  (by rw [hflc, hflw2, hflw1]; exact hflf)
                                  (Or.inr (Or.inr rfl)) (fun _ => hcr20 hc) hmc
                              · c0_hsplit
                                · c0_hsteps_nogrp
                                  refine wp_call_of_spec _ _ (hFlushUnits _ _ _ _ ?_)
                                  refine fullDenseFlushUnitsM6Spec_intro rfl hdwc hmc ?_
                                  intro ok_u su mu hdwu hcvu _ hflu _ htmku _ _ _ _ _ hfu hmu
                                  c0_hsplit
                                  · c0_hsteps!
                                    exact hQ cr_r su mu hdwu.toDense (htmkc.congr hcvu htmku)
                                      (by omega) (by rw [hflu, hflc, hflw2, hflw1]; exact hflf)
                                      hcr_disj (fun h => hcr20 h) hmu
                                  · c0_hsteps!
                                    exact hQ 20#64 su mu hdwu.toDense (htmkc.congr hcvu htmku)
                                      (by omega) (by rw [hflu, hflc, hflw2, hflw1]; exact hflf)
                                      (Or.inr (Or.inr rfl)) (fun _ => hfu (by simpa using hc)) hmu
                                · c0_hsteps!
                                  exact hQ cr_r sc mc hdwc.toDense htmkc (by omega)
                                    (by rw [hflc, hflw2, hflw1]; exact hflf) hcr_disj hcr20 hmc
                            · c0_hsteps!
                              exact hJ39 mw2 ⟨sw2, hdww2, htmkw2, hcvw2.trans (hcvw1.trans hcvf),
                                by rw [hflw2, hflw1]; exact hflf, hmw2⟩
                          · c0_hsteps!
                            exact hJ39 mw1 ⟨sw1, hdww1, htmkw1, hcvw1.trans hcvf,
                              by rw [hflw1]; exact hflf, hmw1⟩)
                    · -- `fit_f = false`: two `full_bve_bce_side_m8` calls
                      c0_hsteps_nogrp
                      refine wp_call_of_spec _ _ (hBceSide _ _ _ _ ?_)
                      dsimp only [vals, Arg.val]
                      refine m8BveBceSideSpec_intro rfl hdwf htmkf (by rw [hplnl.1, hcvf]; omega)
                        (by rw [show (0 : BitVec 32).toNat = 0 from rfl, Nat.zero_add]; omega)
                        (by omega)
                        (fun k hk => by
                          rw [show (0 : BitVec 32).toNat = 0 from rfl, Nat.zero_add]
                          exact m8_var_bveEntry_bceEntry hdwf (hent_pf k hk))
                        (fun k hk => m8_var_bveEntry_bceOpp hdwf (hent_nf k hk))
                        hmf ?_
                      intro sb1 mb1 hdwb1 htmkb1 hcvb1 halb1 hflb1 hscrb1 hrefsb1 hperb1 hmb1
                      c0_hsteps_nogrp
                      refine wp_call_of_spec _ _ (hBceSide _ _ _ _ ?_)
                      dsimp only [vals, Arg.val]
                      refine m8BveBceSideSpec_intro rfl hdwb1 htmkb1
                        (by rw [hplnl.2, hcvb1, hcvf]; omega)
                        (by omega)
                        (by rw [show (0 : BitVec 32).toNat = 0 from rfl, Nat.zero_add]; omega)
                        (fun k hk => by
                          rw [hscrb1]
                          exact m8_var_bveEntry_bceEntry_congr
                            (m8_var_bveEntry_bceEntry hdwf (hent_nf k hk))
                            hcvb1 hrefsb1 halb1 hperb1)
                        (fun k hk => by
                          rw [show (0 : BitVec 32).toNat = 0 from rfl, Nat.zero_add, hscrb1]
                          exact m8_var_bveEntry_bceOpp_congr
                            (m8_var_bveEntry_bceOpp hdwf (hent_pf k hk))
                            hrefsb1 halb1 hperb1)
                        hmb1 ?_
                      intro sb2 mb2 hdwb2 htmkb2 hcvb2 _ hflb2 _ _ _ hmb2
                      c0_hsteps!
                      exact hQ 1#64 sb2 mb2 hdwb2.toDense htmkb2
                        (by rw [hcvb2, hcvb1, hcvf]; exact Nat.le_refl _)
                        (by rw [hflb2, hflb1]; exact hflf)
                        (Or.inl rfl) (by simp) hmb2)
                  (fun Jpre hJpre => by
                    c0_hsplit
                    · c0_hsteps_nogrp
                      refine wp_join_state (ts := [.bool]) (α := Bool × FullState)
                        (fun x => (x.1, ()))
                        (fun x md =>
                          FullDenseInvW c F0 F_cur x.2 ∧ TmkZero x.2 ∧
                          x.2.core.cur_vars = s0.core.cur_vars ∧
                          x.2.core.arena = s2.core.arena ∧
                          x.2.core.arena_len = s2.core.arena_len ∧
                          x.2.core.fuel.toNat ≤ s0.core.fuel.toNat ∧
                          FullResBufOkW F_cur x.2 rp.toNat r_off.toNat ∧
                          (∀ k < np.toNat,
                            x.2.scratch.scratch_buf[k]? = s2.scratch.scratch_buf[k]?) ∧
                          (∀ k < nn.toNat,
                            x.2.scratch.scratch_buf[neg_off.toNat + k]? =
                              s2.scratch.scratch_buf[neg_off.toNat + k]?) ∧
                          (FullMem c x.2 ⋆ R) md)
                        (fun _ ⟨b45, s45⟩ md h45 => by
                          c0_hsteps!; exact hJpre (b45, s45) md h45)
                        (fun J45p hJ45p => by
                          c0_hsplit
                          · c0_hsteps!
                            exact hJ45p (false, si) mi ⟨hdwi, htmki, hcvi, hari, hali, hfli,
                              hres_i, hkeep_pi, hkeep_ni, hmi⟩
                          · c0_hsteps_nogrp
                            refine wp_join_state (ts := [.bool]) (α := Bool × FullState)
                              (fun x => (x.1, ()))
                              (fun x md =>
                                FullDenseInvW c F0 F_cur x.2 ∧ TmkZero x.2 ∧
                                x.2.core.cur_vars = s0.core.cur_vars ∧
                                x.2.core.arena = s2.core.arena ∧
                                x.2.core.arena_len = s2.core.arena_len ∧
                                x.2.core.fuel.toNat ≤ s0.core.fuel.toNat ∧
                                FullResBufOkW F_cur x.2 rp.toNat r_off.toNat ∧
                                (∀ k < np.toNat,
                                  x.2.scratch.scratch_buf[k]? = s2.scratch.scratch_buf[k]?) ∧
                                (∀ k < nn.toNat,
                                  x.2.scratch.scratch_buf[neg_off.toNat + k]? =
                                    s2.scratch.scratch_buf[neg_off.toNat + k]?) ∧
                                (FullMem c x.2 ⋆ R) md)
                              (fun _ ⟨b52, s52⟩ md h52 => by
                                c0_hsteps!; exact hJ45p (b52, s52) md h52)
                              (fun J52p hJ52p => by
                                c0_hsplit
                                · c0_hsteps_nogrp
                                  refine wp_join_state (ts := []) (α := FullState)
                                    (fun _ => ())
                                    (fun sd md =>
                                      FullDenseInvW c F0 F_cur sd ∧ TmkZero sd ∧
                                      sd.core.cur_vars = s0.core.cur_vars ∧
                                      sd.core.arena = s2.core.arena ∧
                                      sd.core.arena_len = s2.core.arena_len ∧
                                      sd.core.fuel.toNat ≤ s0.core.fuel.toNat ∧
                                      FullResBufOkW F_cur sd rp.toNat r_off.toNat ∧
                                      (∀ k < np.toNat,
                                        sd.scratch.scratch_buf[k]? = s2.scratch.scratch_buf[k]?) ∧
                                      (∀ k < nn.toNat,
                                        sd.scratch.scratch_buf[neg_off.toNat + k]? =
                                          s2.scratch.scratch_buf[neg_off.toNat + k]?) ∧
                                      (FullMem c sd ⋆ R) md)
                                    (fun _ sd md ⟨hdwd, htmkd, hcvd, hard, hald, hfld, hresd,
                                        hkeep_pd, hkeep_nd, hmd⟩ => by
                                      c0_hsteps_nogrp
                                      refine wp_join_state (ts := [.bool])
                                        (α := Bool × FullState) (fun x => (x.1, ()))
                                        (fun x md' =>
                                          FullDenseInvW c F0 F_cur x.2 ∧ TmkZero x.2 ∧
                                          x.2.core.cur_vars = s0.core.cur_vars ∧
                                          x.2.core.arena = s2.core.arena ∧
                                          x.2.core.arena_len = s2.core.arena_len ∧
                                          x.2.core.fuel.toNat ≤ s0.core.fuel.toNat ∧
                                          FullResBufOkW F_cur x.2 rp.toNat r_off.toNat ∧
                                          (∀ k < np.toNat,
                                            x.2.scratch.scratch_buf[k]? =
                                              s2.scratch.scratch_buf[k]?) ∧
                                          (∀ k < nn.toNat,
                                            x.2.scratch.scratch_buf[neg_off.toNat + k]? =
                                              s2.scratch.scratch_buf[neg_off.toNat + k]?) ∧
                                          (FullMem c x.2 ⋆ R) md')
                                        (fun _ ⟨b60, s60⟩ md' h60 => by
                                          c0_hsteps!; exact hJ52p (b60, s60) md' h60)
                                        (fun J60p hJ60p => by
                                          c0_hsplit
                                          · c0_hsteps!
                                            exact hJ60p (false, sd) md ⟨hdwd, htmkd, hcvd,
                                              hard, hald, hfld, hresd, hkeep_pd, hkeep_nd,
                                              hmd⟩
                                          · c0_hsteps!
                                            exact hJ60p (fit, sd) md ⟨hdwd, htmkd, hcvd,
                                              hard, hald, hfld, hresd, hkeep_pd, hkeep_nd,
                                              hmd⟩))
                                    (fun Jd hJd => by
                                      c0_hsplit
                                      · c0_hsteps_nogrp
                                        refine wp_call_of_spec _ _ (hDefrag _ _ _ _ ?_)
                                        refine ⟨c, si, R, rfl, hdwi.1,
                                          (m6_denseWatchesInv_of_w hdwi).layout, hmi, ?_⟩
                                        intro wvec' wstk' wlen' wsort' md sd hlen_d hlay_d _
                                          hslice_d hmd
                                        have hdwd := m6_fullDenseInvW_of_wstackDefrag hdwi
                                          hlen_d hlay_d hslice_d
                                        c0_hsteps!
                                        exact hJd sd md ⟨hdwd, htmki, hcvi, hari, hali, hfli,
                                          m8_var_resBuf_mono (s := si) (s' := sd) rfl
                                            (fun _ _ _ => rfl) hres_i,
                                          hkeep_pi, hkeep_ni, hmd⟩
                                      · c0_hsteps!
                                        exact hJd si mi ⟨hdwi, htmki, hcvi, hari, hali, hfli,
                                          hres_i, hkeep_pi, hkeep_ni, hmi⟩)
                                · c0_hsteps!
                                  exact hJ52p (fit, si) mi ⟨hdwi, htmki, hcvi, hari, hali,
                                    hfli, hres_i, hkeep_pi, hkeep_ni, hmi⟩))
                    · c0_hsteps!
                      exact hJpre (fit, si) mi ⟨hdwi, htmki, hcvi, hari, hali, hfli,
                        hres_i, hkeep_pi, hkeep_ni, hmi⟩))
              (fun J32 hJ32 => by
                c0_hsplit
                · c0_hsteps_nogrp
                  -- Dispatch `if (use_m8) full_bve_gates_m8 else full_bve_gates_m7`
                  refine wp_join_state (ts := []) (α := FullState) (fun _ => ())
                    (fun s3 m3 =>
                      FullDenseInvW c F0 F_cur s3 ∧ TmkZero s3 ∧
                      s3.core.cur_vars = s0.core.cur_vars ∧ s3.core.arena = s2.core.arena ∧
                      s3.core.arena_len = s2.core.arena_len ∧
                      s3.core.fuel.toNat ≤ s0.core.fuel.toNat ∧
                      (∀ i < np.toNat, s3.scratch.scratch_buf[i]? = s2.scratch.scratch_buf[i]?) ∧
                      (∀ j < nn.toNat,
                        s3.scratch.scratch_buf[neg_off.toNat + j]? =
                          s2.scratch.scratch_buf[neg_off.toNat + j]?) ∧
                      (FullMem c s3 ⋆ R) m3)
                    (fun _ s3 m3 ⟨hdw3, htmk3, hcv3, har3, hal3, hfl3, hp3, hn3, hm3⟩ => by
                      have hent_p3 : ∀ i < np.toNat, FullBveEntryOkW F_cur s3 (2 * v.toNat)
                          (s3.scratch.scratch_buf[i]?.getD 0#32) := fun i hi => by
                        rw [hp3 i hi]; exact m8_bveEntry_congr_core (hent_p2 i hi) hcv3 har3 hal3
                      have hent_n3 : ∀ j < nn.toNat, FullBveEntryOkW F_cur s3 (2 * v.toNat + 1)
                          (s3.scratch.scratch_buf[neg_off.toNat + j]?.getD 0#32) := fun j hj => by
                        rw [hn3 j hj]; exact m8_bveEntry_congr_core (hent_n2' j hj) hcv3 har3 hal3
                      have hgf_sc : (gf_idx.setWidth 64).toNat < s3.scratch.scratch_buf.length := by
                        rw [hdw3.1.scratch_ok.scratch_buf_len, m6_zext32_toNat]; omega
                      have hrg_sc : (rg_idx.setWidth 64).toNat < s3.scratch.scratch_buf.length := by
                        rw [hdw3.1.scratch_ok.scratch_buf_len, m6_zext32_toNat]; omega
                      c0_hsteps_nogrp
                      refine wp_loop_group (ts := [i64, i64, i64, .bool, i32])
                        (fun rem_i (rp, r_cnt, w_est, fit, i, ()) mi => ∃ si : FullState,
                          i.toNat ≤ np.toNat ∧ rem_i = np.toNat - i.toNat ∧
                          FullDenseInvW c F0 F_cur si ∧ TmkZero si ∧
                          si.core.cur_vars = s0.core.cur_vars ∧ si.core.arena = s3.core.arena ∧
                          si.core.arena_len = s3.core.arena_len ∧
                          si.core.fuel.toNat ≤ s0.core.fuel.toNat ∧
                          r_off.toNat ≤ rp.toNat ∧ rp.toNat ≤ c.scratch_cap ∧
                          FullResBufOkW F_cur si rp.toNat r_off.toNat ∧
                          (∀ k < r_off.toNat,
                            si.scratch.scratch_buf[k]? = s3.scratch.scratch_buf[k]?) ∧
                          (FullMem c si ⋆ R) mi)
                        ?_ ?_
                      · rintro Li rem_i ⟨rp, r_cnt, w_est, fit, i, ⟨⟩⟩ mi hLi
                          ⟨si, hi_le, rfl, hdwi, htmki, hcvi, hari, hali, hfli, hrp_lo, hrp_hi,
                            hres_i, hkeep_i, hmi⟩
                        c0_hsplit
                        · have hi_lt : i.toNat < np.toNat := hc
                          c0_hsplit
                          · have hi_mask_sc : ((pos_mask + (i >>> (5 : Nat))).setWidth 64).toNat <
                                si.scratch.scratch_buf.length := by
                              rw [hdwi.1.scratch_ok.scratch_buf_len]
                              exact Nat.lt_of_lt_of_le (hpm_lt_roff i (by omega)) hroff_le_sc
                            have hi1 : (i + 1#32).toNat = i.toNat + 1 := by c0_bound
                            c0_hsteps_nogrp
                            refine wp_loop_break_group
                              (brkTs := [i64, i64, i64, .bool, i32])
                              (lpTs := [i64, i64, i64, i32])
                              (fun (rp_b, rcnt_b, west_b, fit_b, _ib, ()) mb => ∃ sb : FullState,
                                FullDenseInvW c F0 F_cur sb ∧ TmkZero sb ∧
                                sb.core.cur_vars = s0.core.cur_vars ∧
                                sb.core.arena = s3.core.arena ∧
                                sb.core.arena_len = s3.core.arena_len ∧
                                sb.core.fuel.toNat ≤ s0.core.fuel.toNat ∧
                                r_off.toNat ≤ rp_b.toNat ∧ rp_b.toNat ≤ c.scratch_cap ∧
                                FullResBufOkW F_cur sb rp_b.toNat r_off.toNat ∧
                                (∀ k < r_off.toNat, sb.scratch.scratch_buf[k]? =
                                  s3.scratch.scratch_buf[k]?) ∧
                                (FullMem c sb ⋆ R) mb)
                              (fun rem_j (rp_j, rcnt_j, west_j, j, ()) mj => ∃ sj : FullState,
                                j.toNat ≤ nn.toNat ∧ rem_j = nn.toNat - j.toNat ∧
                                FullDenseInvW c F0 F_cur sj ∧ TmkZero sj ∧
                                sj.core.cur_vars = s0.core.cur_vars ∧
                                sj.core.arena = s3.core.arena ∧
                                sj.core.arena_len = s3.core.arena_len ∧
                                sj.core.fuel.toNat ≤ s0.core.fuel.toNat ∧
                                r_off.toNat ≤ rp_j.toNat ∧ rp_j.toNat ≤ c.scratch_cap ∧
                                FullResBufOkW F_cur sj rp_j.toNat r_off.toNat ∧
                                (∀ k < r_off.toNat, sj.scratch.scratch_buf[k]? =
                                  s3.scratch.scratch_buf[k]?) ∧
                                (FullMem c sj ⋆ R) mj)
                              ?_ ?_ ?_
                            · rintro _ ⟨rp_b, rcnt_b, west_b, fit_b, _ib, ⟨⟩⟩ mb
                                ⟨sb, hdwb, htmkb, hcvb, harb, halb, hflb, hrpb_lo, hrpb_hi,
                                  hresb, hkeepb, hmb⟩
                              c0_hsteps!
                              exact hLi (np.toNat - (i + 1#32).toNat)
                                (rp_b, rcnt_b, west_b, fit_b, i + 1#32, ()) mb (by omega)
                                ⟨sb, by omega, rfl, hdwb, htmkb, hcvb, harb, halb, hflb,
                                 hrpb_lo, hrpb_hi, hresb, hkeepb, hmb⟩
                            · rintro Bj Lj rem_j ⟨rp_j, rcnt_j, west_j, j, ⟨⟩⟩ mj hBj hLj
                                ⟨sj, hj_le, rfl, hdwj, htmkj, hcvj, harj, halj, hflj, hrpj_lo,
                                  hrpj_hi, hresj, hkeepj, hmj⟩
                              c0_hsplit
                              · have hj_lt : j.toNat < nn.toNat := hc
                                c0_hsplit
                                · have hj_mask_sc :
                                      ((neg_mask + (j >>> (5 : Nat))).setWidth 64).toNat <
                                      sj.scratch.scratch_buf.length := by
                                    rw [hdwj.1.scratch_ok.scratch_buf_len]
                                    exact Nat.lt_of_lt_of_le (hnm_lt_roff j (by omega)) hroff_le_sc
                                  have hj1 : (j + 1#32).toNat = j.toNat + 1 := by c0_bound
                                  c0_hsteps_nogrp
                                  refine wp_join_state_pure (ts := [.bool]) (α := Bool)
                                    (fun np_b => (np_b, ())) (fun _ => True)
                                    (fun _ np_b _ => by
                                      c0_hsteps_nogrp
                                      refine wp_join_state (ts := [i64, i64, i64, .bool])
                                        (α := BitVec 64 × BitVec 64 × BitVec 64 × Bool × FullState)
                                        (fun x => (x.1, x.2.1, x.2.2.1, x.2.2.2.1, ()))
                                        (fun x mk =>
                                          let sk := x.2.2.2.2
                                          FullDenseInvW c F0 F_cur sk ∧ TmkZero sk ∧
                                          sk.core.cur_vars = s0.core.cur_vars ∧
                                          sk.core.arena = s3.core.arena ∧
                                          sk.core.arena_len = s3.core.arena_len ∧
                                          sk.core.fuel.toNat ≤ s0.core.fuel.toNat ∧
                                          r_off.toNat ≤ x.1.toNat ∧ x.1.toNat ≤ c.scratch_cap ∧
                                          FullResBufOkW F_cur sk x.1.toNat r_off.toNat ∧
                                          (∀ k < r_off.toNat, sk.scratch.scratch_buf[k]? =
                                            s3.scratch.scratch_buf[k]?) ∧
                                          (FullMem c sk ⋆ R) mk)
                                        (fun _ ⟨rp_k, rcnt_k, west_k, fit_k, sk⟩ mk
                                            ⟨hdwk, htmkk, hcvk, hark, halk, hflk, hrpk_lo, hrpk_hi,
                                              hresk, hkeepk, hmk⟩ => by
                                          c0_hsteps!
                                          exact hLj (nn.toNat - (j + 1#32).toNat)
                                            (rp_k, rcnt_k, west_k, j + 1#32, ()) mk
                                            (by rw [hj1]; omega)
                                            ⟨sk, by rw [hj1]; omega, rfl, hdwk, htmkk, hcvk, hark,
                                             halk, hflk, hrpk_lo, hrpk_hi, hresk, hkeepk, hmk⟩)
                                        (fun J81 hJ81 => by
                                          c0_hsplit
                                          · have hi_scj : (i.setWidth 64).toNat <
                                                sj.scratch.scratch_buf.length := by
                                              rw [hdwj.1.scratch_ok.scratch_buf_len,
                                                m6_zext32_toNat]
                                              omega
                                            have hneg_j_eq : ((neg_off + j).setWidth 64).toNat =
                                                neg_off.toNat + j.toNat := by
                                              rw [m6_zext32_toNat, BitVec.toNat_add,
                                                Nat.mod_eq_of_lt (by omega)]
                                            have hj_scj : ((neg_off + j).setWidth 64).toNat <
                                                sj.scratch.scratch_buf.length := by
                                              rw [hdwj.1.scratch_ok.scratch_buf_len, hneg_j_eq]
                                              omega
                                            c0_hsteps_nogrp
                                            refine wp_call_of_spec _ _ (hResPair _ _ _ _ ?_)
                                            dsimp only [vals, Arg.val]
                                            refine ⟨c, F0, F_cur, sj, R, rfl, hdwj, by omega,
                                              (by
                                                have hget : sj.scratch.scratch_buf[(i.setWidth
                                                    64).toNat]'hi_scj =
                                                    s3.scratch.scratch_buf[i.toNat]?.getD 0#32 := by
                                                  have h0 := hkeepj i.toNat (by omega)
                                                  rw [← h0, List.getElem?_eq_getElem (by
                                                    rw [m6_zext32_toNat] at hi_scj; exact hi_scj),
                                                    Option.getD_some]
                                                  exact m6_getElem_congr (m6_zext32_toNat i) _ _
                                                rw [hget]
                                                exact m8_bveEntry_congr_core (hent_p3 i.toNat hi_lt)
                                                  (hcvj.trans hcv3.symm) harj halj),
                                              (by
                                                have hget : sj.scratch.scratch_buf[((neg_off +
                                                    j).setWidth 64).toNat]'hj_scj =
                                                    s3.scratch.scratch_buf[neg_off.toNat +
                                                      j.toNat]?.getD 0#32 := by
                                                  have h0 := hkeepj (neg_off.toNat + j.toNat)
                                                    (by rw [hneg_eq]; omega)
                                                  rw [← h0, List.getElem?_eq_getElem (by
                                                    rw [← hneg_j_eq]; exact hj_scj),
                                                    Option.getD_some]
                                                  exact m6_getElem_congr hneg_j_eq _ _
                                                rw [hget]
                                                exact m8_bveEntry_congr_core (hent_n3 j.toNat hj_lt)
                                                  (hcvj.trans hcv3.symm) harj halj),
                                              hmj, ?_⟩
                                            intro ok_r lm_r tmp_r tl_r m_r
                                            dsimp only
                                            intro hdwr htl_le hres_ok hm_r
                                            let sr : FullState := { sj with core := { sj.core with
                                              lit_mark := lm_r, tmp := tmp_r, tmp_len := tl_r } }
                                            have htmkr : TmkZero sr := htmkj
                                            have hres_sr :
                                                FullResBufOkW F_cur sr rp_j.toNat r_off.toNat :=
                                              m8_var_resBuf_mono (s := sj) (s' := sr) rfl
                                                (fun _ _ _ => rfl) hresj
                                            c0_hsplit
                                            · obtain ⟨hr_lt, hr_nd, hr_ent⟩ :=
                                                hres_ok (by simpa using hc)
                                              have htl_cv : tl_r ≤ c.max_vars := by
                                                have := hdwr.1.core_ok.cur_vars_le; omega
                                              c0_hsplit
                                              · c0_hsteps!
                                                exact hBj
                                                  (rp_j, rcnt_j + 1#64, west_j, false, j, ()) m_r
                                                  ⟨sr, hdwr, htmkr, hcvj, harj, halj, hflj, hrpj_lo,
                                                   hrpj_hi, hres_sr, hkeepj, hm_r⟩
                                              · have htl100 : tl_r ≤ 100 := by
                                                  rw [Nat.mod_eq_of_lt (by omega : tl_r < 2 ^ 64),
                                                    show (100 : BitVec 64).toNat = 100 from rfl]
                                                    at hc
                                                  omega
                                                c0_hsplit
                                                · c0_hsteps!
                                                  exact hBj
                                                    (rp_j, rcnt_j + 1#64, west_j, false, j, ())
                                                    m_r ⟨sr, hdwr, htmkr, hcvj, harj, halj, hflj,
                                                     hrpj_lo, hrpj_hi, hres_sr, hkeepj, hm_r⟩
                                                · c0_hsplit
                                                  · c0_hsteps!
                                                    exact hBj
                                                      (rp_j, rcnt_j + 1#64, west_j, false, j, ())
                                                      m_r ⟨sr, hdwr, htmkr, hcvj, harj, halj, hflj,
                                                       hrpj_lo, hrpj_hi, hres_sr, hkeepj, hm_r⟩
                                                  · have hrp_sum : (rp_j + 1#64 +
                                                        BitVec.ofNat 64 tl_r).toNat =
                                                        rp_j.toNat + 1 + tl_r := by c0_bound
                                                    have hrp_fit : rp_j.toNat + 1 + tl_r ≤
                                                        c.scratch_cap := by
                                                      rw [show (1 : BitVec 64).toNat = 1 from rfl,
                                                        Nat.mod_eq_of_lt (by omega :
                                                          c.scratch_cap < 2 ^ 64),
                                                        Nat.mod_eq_of_lt (by omega :
                                                          rp_j.toNat + 1 + tl_r < 2 ^ 64)] at hc
                                                      omega
                                                    have hrp_sc : rp_j.toNat <
                                                        sr.scratch.scratch_buf.length := by
                                                      rw [hdwr.1.scratch_ok.scratch_buf_len]; omega
                                                    c0_hsteps_nogrp
                                                    let scr_w0 := sr.scratch.scratch_buf.set
                                                      rp_j.toNat
                                                      ((BitVec.ofNat 64 tl_r).setWidth 32)
                                                    have hlen_w0 :
                                                        (BitVec.ofNat 64 tl_r).setWidth 32 =
                                                          BitVec.ofNat 32 tl_r := by
                                                      apply BitVec.eq_of_toNat_eq; simp
                                                    refine wp_loop_group (ts := [i64, i32])
                                                      (fun rem_k (wk, k, ()) mk =>
                                                        ∃ scr_k : List (BitVec 32),
                                                          let sk : FullState := { sr with scratch :=
                                                            { sr.scratch with
                                                              scratch_buf := scr_k } }
                                                          scr_k.length = c.scratch_cap ∧
                                                          k.toNat ≤ tl_r ∧ rem_k = tl_r - k.toNat ∧
                                                          (∀ idx < rp_j.toNat, scr_k[idx]? =
                                                            sr.scratch.scratch_buf[idx]?) ∧
                                                          scr_k[rp_j.toNat]? = some (BitVec.ofNat 32
                                                            tl_r) ∧
                                                          (∀ t < k.toNat,
                                                            scr_k[rp_j.toNat + 1 + t]? = tmp_r[t]?)
                                                          ∧ (FullMem c sk ⋆ R) mk)
                                                      ?_ ?_
                                                    · rintro Lk rem_k ⟨wk, k, ⟨⟩⟩ mk hLk
                                                        ⟨scr_k, hsck, hk_le, rfl, hpre_k, hsz_k,
                                                          hcp_k, hmk⟩
                                                      c0_hsplit
                                                      · have hk_lt : k.toNat < tl_r := by
                                                          rw [Nat.mod_eq_of_lt (by omega :
                                                            tl_r < 2 ^ 64)] at hc
                                                          exact hc
                                                        have hk_tmp : (k.setWidth 64).toNat <
                                                            tmp_r.length := by
                                                          rw [hdwr.1.core_ok.tmp_len_arr,
                                                            m6_zext32_toNat]; omega
                                                        have hk_sc :
                                                            (rp_j + 1#64 + k.setWidth 64).toNat <
                                                            scr_k.length := by rw [hsck]; c0_bound
                                                        have hk_sc_eq : (rp_j + 1#64 + k.setWidth
                                                            64).toNat = rp_j.toNat + 1 + k.toNat :=
                                                          by c0_bound
                                                        have hk1 : (k + 1#32).toNat = k.toNat + 1 :=
                                                          by c0_bound
                                                        c0_hsteps_nogrp
                                                        let scr_k' := scr_k.set (rp_j + 1#64 +
                                                          k.setWidth 64).toNat
                                                          (tmp_r[(k.setWidth 64).toNat]'hk_tmp)
                                                        have hstep_k : ∀ (wk' : BitVec 64) m_step,
                                                            (FullMem c { sr with scratch :=
                                                              { sr.scratch with
                                                                scratch_buf := scr_k' }
                                                              } ⋆ R) m_step →
                                                            Lk (wk', k + 1#32, ()) m_step :=
                                                          fun wk' m_step hm_s =>
                                                            hLk (tl_r - (k + 1#32).toNat)
                                                              (wk', k + 1#32, ()) m_step (by omega)
                                                              ⟨scr_k', by simp [scr_k', hsck],
                                                               by omega, rfl,
                                                               fun idx hidx => by
                                                                 dsimp only [scr_k']
                                                                 rw [List.getElem?_set_ne
                                                                   (by omega)]
                                                                 exact hpre_k idx hidx,
                                                               by
                                                                 dsimp only [scr_k']
                                                                 rw [List.getElem?_set_ne
                                                                   (by omega)]
                                                                 exact hsz_k,
                                                               fun t ht => by
                                                                 dsimp only [scr_k']
                                                                 rcases Nat.lt_or_eq_of_le
                                                                   (Nat.lt_succ_iff.mp (hk1 ▸ ht))
                                                                   with h | h
                                                                 · rw [List.getElem?_set_ne
                                                                     (by omega)]
                                                                   exact hcp_k t h
                                                                 · subst h
                                                                   rw [← hk_sc_eq,
                                                                     List.getElem?_set_self hk_sc,
                                                                     List.getElem?_eq_getElem (by
                                                                       rw [m6_zext32_toNat]
                                                                         at hk_tmp
                                                                       exact hk_tmp)]
                                                                   exact congrArg some
                                                                     (m6_getElem_congr
                                                                       (m6_zext32_toNat k) _ _),
                                                               hm_s⟩
                                                        refine wp_join_state_pure (ts := [i64])
                                                          (α := BitVec 64) (fun x => (x, ()))
                                                          (fun _ => True)
                                                          (fun _ wk' _ => by
                                                            c0_hsteps!; exact hstep_k wk' _ hm)
                                                          (fun Jw hJw => by
                                                            c0_hsplit
                                                            · c0_hsplit
                                                              · have hlk_lt :
                                                                    (tmp_r[(k.setWidth 64).toNat]'
                                                                    hk_tmp).toNat <
                                                                    2 * sr.core.cur_vars := by
                                                                  have hlt_k : k.toNat <
                                                                      tmp_r.length := by
                                                                    rw [m6_zext32_toNat] at hk_tmp
                                                                    exact hk_tmp
                                                                  have h0 := hr_lt k.toNat hk_lt
                                                                  rw [List.getElem?_eq_getElem
                                                                    hlt_k, Option.getD_some] at h0
                                                                  rw [m6_getElem_congr
                                                                    (m6_zext32_toNat k)
                                                                    hk_tmp hlt_k]
                                                                  exact h0
                                                                have hlk_wv : ((tmp_r[(k.setWidth
                                                                    64).toNat]'hk_tmp).setWidth 64
                                                                    <<< (1 : Nat) + 1#64).toNat <
                                                                    sr.core.wvec.length := by
                                                                  rw [hdwr.1.core_ok.wvec_len]
                                                                  have hcv_r :
                                                                      sr.core.cur_vars ≤
                                                                        c.max_vars :=
                                                                    hdwr.1.core_ok.cur_vars_le
                                                                  have hlk_le_r :
                                                                      (tmp_r[(k.setWidth 64).toNat]'
                                                                        hk_tmp).toNat <
                                                                      2 * sr.core.cur_vars := by
                                                                    rw [m6_getElem_congr
                                                                      (m6_zext32_toNat k) hk_tmp (by
                                                                        rw [m6_zext32_toNat]
                                                                          at hk_tmp
                                                                        exact hk_tmp)]
                                                                    exact hlk_lt
                                                                  rw [BitVec.toNat_add,
                                                                    BitVec.toNat_shiftLeft,
                                                                    Nat.shiftLeft_eq,
                                                                    BitVec.toNat_setWidth]
                                                                  simp only [BitVec.toNat_ofNat,
                                                                    Nat.reducePow]
                                                                  rw [Nat.mod_eq_of_lt (by omega),
                                                                    Nat.mod_eq_of_lt (by omega),
                                                                    Nat.mod_eq_of_lt (by omega)]
                                                                  omega
                                                                c0_hsteps!; exact hJw _ trivial
                                                              · c0_hsteps!; exact hJw wk trivial
                                                            · c0_hsteps!; exact hJw wk trivial)
                                                      · have hk_eq : k.toNat = tl_r := by
                                                          rw [Nat.mod_eq_of_lt (by omega :
                                                            tl_r < 2 ^ 64)] at hc
                                                          change ¬ k.toNat < tl_r at hc; omega
                                                        let s_ap : FullState := { sr with scratch :=
                                                          { sr.scratch with scratch_buf := scr_k } }
                                                        have hdw_ap : FullDenseInvW c F0 F_cur s_ap
                                                            := m8_fullDenseInvW_scr hdwr hsck
                                                        have hrp_next : (rp_j + 1#64 +
                                                            BitVec.ofNat 64 tl_r).toNat =
                                                            rp_j.toNat + 1 + tl_r := by c0_bound
                                                        have hcp_full : ∀ t < tl_r,
                                                            scr_k[rp_j.toNat + 1 + t]? = tmp_r[t]?
                                                            := fun t ht => hcp_k t (by omega)
                                                        have hres_ap : FullResBufOkW F_cur s_ap
                                                            (rp_j + 1#64 +
                                                              BitVec.ofNat 64 tl_r).toNat
                                                            r_off.toNat := by
                                                          rw [hrp_next]
                                                          refine m8_var_resBuf_append (s := sr)
                                                            (s' := s_ap) rfl
                                                            (fun idx _ hi2 => hpre_k idx hi2)
                                                            hres_sr
                                                            (by
                                                              dsimp only [s_ap]; rw [hsz_k,
                                                                Option.getD_some,
                                                                BitVec.toNat_ofNat,
                                                                Nat.mod_eq_of_lt (by omega)])
                                                            (fun t ht => by
                                                              dsimp only [s_ap]
                                                              rw [hcp_full t ht]
                                                              exact hr_lt t ht) ?_ ?_
                                                          · have hmap : ((List.range tl_r).map
                                                                fun t =>
                                                                  (s_ap.scratch.scratch_buf[
                                                                    rp_j.toNat + 1 + t]?.getD
                                                                      0#32).toNat / 2) =
                                                                (tmp_r.take tl_r).map
                                                                  (fun x => x.toNat / 2) := by
                                                              rw [m8_var_list_take_map_div2_eq_range
                                                                (by
                                                                  rw [hdwr.1.core_ok.tmp_len_arr]
                                                                  omega)]
                                                              exact List.map_congr_left
                                                                fun t htm => by
                                                                  dsimp only [s_ap]
                                                                  rw [hcp_full t
                                                                    (List.mem_range.mp htm)]
                                                            rw [hmap]; exact hr_nd
                                                          · have hmap : ((List.range tl_r).map
                                                                fun t =>
                                                                  (s_ap.scratch.scratch_buf[
                                                                    rp_j.toNat + 1 + t]?.getD
                                                                      0#32).toNat) =
                                                                (tmp_r.take tl_r).map
                                                                  BitVec.toNat := by
                                                              rw [m8_var_list_take_map_eq_range (by
                                                                rw [hdwr.1.core_ok.tmp_len_arr]
                                                                omega)]
                                                              exact List.map_congr_left
                                                                fun t htm => by
                                                                  dsimp only [s_ap]
                                                                  rw [hcp_full t
                                                                    (List.mem_range.mp htm)]
                                                            rw [hmap]; exact hr_ent
                                                        c0_hsteps!
                                                        exact hJ81 (rp_j + 1#64 +
                                                          BitVec.ofNat 64 tl_r,
                                                          rcnt_j + 1#64, wk, fit, s_ap) mk
                                                          ⟨hdw_ap, htmkr, hcvj, harj, halj, hflj,
                                                           by rw [hrp_next]; omega,
                                                           by rw [hrp_next]; omega, hres_ap,
                                                           fun idx hidx =>
                                                             (hpre_k idx (by omega)).trans
                                                               (hkeepj idx hidx), hmk⟩
                                                    · intro Lk hLk; c0_hsteps!
                                                      exact hLk tl_r (west_j, 0#32, ()) _
                                                        ⟨scr_w0, by
                                                           dsimp only [scr_w0, sr]
                                                           rw [List.length_set]
                                                           exact hdwj.1.scratch_ok.scratch_buf_len,
                                                         Nat.zero_le _, by simp,
                                                         fun idx hidx => by
                                                           dsimp only [scr_w0]
                                                           exact List.getElem?_set_ne (by omega),
                                                         by dsimp only [scr_w0]; rw [hlen_w0]
                                                            exact List.getElem?_set_self hrp_sc,
                                                         fun _ h => by
                                                           rw [show (0#32).toNat = 0 from rfl] at h
                                                           omega, hm⟩
                                            · c0_hsteps!
                                              exact hJ81 (rp_j, rcnt_j, west_j, fit, sr) m_r
                                                ⟨hdwr, htmkr, hcvj, harj, halj, hflj, hrpj_lo,
                                                 hrpj_hi, hres_sr, hkeepj, hm_r⟩
                                          · c0_hsteps!
                                            exact hJ81 (rp_j, rcnt_j, west_j, fit, sj) mj
                                              ⟨hdwj, htmkj, hcvj, harj, halj, hflj, hrpj_lo,
                                               hrpj_hi, hresj, hkeepj, hmj⟩))
                                    (fun Jn hJn => by
                                      c0_hsplit
                                      · refine wp_join_state_pure (ts := [i32]) (α := BitVec 32)
                                          (fun x => (x, ())) (fun _ => True)
                                          (fun _ _ _ => by
                                            c0_hsplit <;> (c0_hsteps!; exact hJn _ trivial))
                                          (fun J80 hJ80 => by
                                            c0_hsplit
                                            · refine wp_join_state_pure (ts := [.bool]) (α := Bool)
                                                (fun b => (b, ())) (fun _ => True)
                                                (fun _ _ _ => by c0_hsteps!; exact hJ80 _ trivial)
                                                (fun J81p hJ81p => by
                                                  c0_hsplit
                                                  · c0_hsteps!; exact hJ81p true trivial
                                                  · c0_hsplit
                                                    · c0_hsteps!; exact hJ81p true trivial
                                                    · c0_hsteps!; exact hJ81p false trivial)
                                            · c0_hsteps!; exact hJ80 _ trivial)
                                      · c0_hsteps!; exact hJn true trivial)
                                · c0_hsteps!
                                  exact hBj (rp_j, rcnt_j, west_j, fit, j, ()) mj
                                    ⟨sj, hdwj, htmkj, hcvj, harj, halj, hflj, hrpj_lo, hrpj_hi,
                                     hresj, hkeepj, hmj⟩
                              · c0_hsteps!
                                exact hBj (rp_j, rcnt_j, west_j, fit, j, ()) mj
                                  ⟨sj, hdwj, htmkj, hcvj, harj, halj, hflj, hrpj_lo, hrpj_hi,
                                   hresj, hkeepj, hmj⟩
                            · intro _ Lj _ hLj; c0_hsteps!
                              exact hLj nn.toNat (rp, r_cnt, w_est, 0#32, ()) mi
                                ⟨si, Nat.zero_le _, by simp, hdwi, htmki, hcvi, hari, hali, hfli,
                                 hrp_lo, hrp_hi, hres_i, hkeep_i, hmi⟩
                          · c0_hsteps!
                            exact hJ32 (rp, r_cnt, w_est, fit, si) mi
                              ⟨hdwi, htmki, hcvi, hari.trans har3, hali.trans hal3, hfli, hrp_lo,
                               hrp_hi, hres_i, fun k hk => (hkeep_i k (by omega)).trans (hp3 k hk),
                               fun k hk =>
                                 (hkeep_i (neg_off.toNat + k) (by rw [hneg_eq]; omega)).trans
                                   (hn3 k hk),
                               hmi⟩
                        · c0_hsteps!
                          exact hJ32 (rp, r_cnt, w_est, fit, si) mi
                            ⟨hdwi, htmki, hcvi, hari.trans har3, hali.trans hal3, hfli, hrp_lo,
                             hrp_hi, hres_i, fun k hk => (hkeep_i k (by omega)).trans (hp3 k hk),
                             fun k hk =>
                               (hkeep_i (neg_off.toNat + k) (by rw [hneg_eq]; omega)).trans
                                 (hn3 k hk),
                             hmi⟩
                      · intro Li hLi; c0_hsteps!
                        exact hLi np.toNat (r_off, 0#64, 0#64, _, 0#32, ()) m3
                          ⟨s3, Nat.zero_le _, by simp, hdw3, htmk3, hcv3, rfl, rfl, hfl3,
                           Nat.le_refl _, hroff_le_sc, .nil, fun _ _ => rfl, hm3⟩)
                    (fun Jg hJg => by
                      c0_hsplit
                      · have hge16 : 16384 ≤ c.scratch_cap := by
                          rw [Nat.mod_eq_of_lt (by omega),
                            show (16384 : BitVec 64).toNat = 16384 from rfl] at hc; omega
                        obtain ⟨ho2001, hneg2001⟩ := hm8_eqs hge16
                        have hnp2001 : np.toNat ≤ 2001 := by rw [ho2001] at hnp_le; exact hnp_le
                        have hnn2001 : nn.toNat ≤ 2001 := by rw [ho2001] at hnn_le; exact hnn_le
                        c0_hsteps_nogrp
                        refine wp_call_of_spec _ _ (hGatesM8 _ _ _ _ ?_)
                        refine m8BveGatesSpec_intro rfl hdw2 htmk0 hge16 hv_lt hnp2001 hnn2001
                          hent_p2 (fun j hj => by rw [← hneg2001]; exact hent_n2' j hj) hm2 ?_
                        intro s3 m3 hdw3 htmk3 hcv3 har3 hal3 hfl3 hp3 hn3 hm3
                        c0_hsteps!
                        exact hJg s3 m3 ⟨hdw3, htmk3, hcv3, har3, hal3, hfl3, hp3,
                          fun j hj => by rw [hneg2001]; exact hn3 j hj, hm3⟩
                      · have hlt16 : c.scratch_cap < 16384 := by
                          rw [Nat.mod_eq_of_lt (by omega),
                            show (16384 : BitVec 64).toNat = 16384 from rfl] at hc; omega
                        obtain ⟨ho512, hneg512⟩ := hm7_eqs hlt16
                        have hnp512 : np.toNat ≤ 512 := by rw [ho512] at hnp_le; exact hnp_le
                        have hnn512 : nn.toNat ≤ 512 := by rw [ho512] at hnn_le; exact hnn_le
                        c0_hsteps_nogrp
                        refine wp_call_of_spec _ _ (hGatesM7 _ _ _ _ ?_)
                        refine fullBveGatesM7Spec_intro rfl hdw2 htmk0 (by omega) hv_lt hnp512
                          hnn512 hent_p2 (fun j hj => by rw [← hneg512]; exact hent_n2' j hj)
                          hm2 ?_
                        intro s3 m3 hdw3 htmk3 hcv3 har3 hal3 hfl3 hp3 hn3 hm3
                        c0_hsteps!
                        exact hJg s3 m3 ⟨hdw3, htmk3, hcv3, har3, hal3, hfl3, hp3,
                          fun j hj => by rw [hneg512]; exact hn3 j hj, hm3⟩)
                · c0_hsteps!
                  exact hJ32 (r_off, 0#64, 0#64, _, s2) m2
                    ⟨hdw2, htmk0, rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, hroff_le_sc, .nil,
                     fun _ _ => rfl, fun _ _ => rfl, hm2⟩))
          (fun J25 hJ25 => by
            c0_hsplit
            · refine wp_join0 (P := fun mj => mj = m2 ∧ (np = 0#32 ∨ nn = 0#32))
                (fun _ mj ⟨hmj, hnp_nn⟩ => by
                  rcases hmj.symm with rfl
                  refine wp_join_state (ts := []) (α := FullState) (fun _ => ())
                    (fun sw moom =>
                      FullDenseInvW c F0 F_cur sw ∧ TmkZero sw ∧
                      sw.core.cur_vars = s0.core.cur_vars ∧
                      sw.core.fuel.toNat ≤ s0.core.fuel.toNat ∧
                      (FullMem c sw ⋆ R) moom)
                    (fun _ sw moom ⟨hdww, htmkw, hcvw, hflw, hmw⟩ => by
                      c0_hsteps!
                      let soom : FullState := { sw with core := { sw.core with oom := 1#64 } }
                      exact hQ 2#64 soom _ (m6_fullDenseInvW_with_oom hdww 1#64).toDense htmkw
                        (by dsimp only [soom]; omega) hflw (Or.inr (Or.inl rfl)) (by simp) hm)
                    (fun J27 hJ27 => by
                      refine wp_join_state (ts := []) (α := FullState) (fun _ => ())
                        (fun sp mp =>
                          FullDenseInvW c F0 F_cur sp ∧ TmkZero sp ∧
                          sp.core.cur_vars = s0.core.cur_vars ∧
                          sp.core.fuel.toNat ≤ s0.core.fuel.toNat ∧
                          (∀ j < nn.toNat, FullBveEntryOkW F_cur sp (2 * v.toNat + 1)
                            (sp.scratch.scratch_buf[neg_off.toNat + j]?.getD 0#32)) ∧
                          (FullMem c sp ⋆ R) mp)
                        (fun _ sp mp ⟨hdwp, htmkp, hcvp, hflp, hent_np, hmp⟩ => by
                          refine wp_join_state (ts := []) (α := FullState) (fun _ => ())
                            (fun sn mn =>
                              FullDenseInvW c F0 F_cur sn ∧ TmkZero sn ∧
                              sn.core.cur_vars = s0.core.cur_vars ∧
                              sn.core.fuel.toNat ≤ s0.core.fuel.toNat ∧
                              (FullMem c sn ⋆ R) mn) ?_ ?_
                          · intro _ sn mn ⟨hdwn, htmkn, hcvn, hfln, hmn⟩
                            c0_hsteps_nogrp
                            refine wp_call_of_spec _ _ (hSetInact _ _ _ _ ?_)
                            dsimp only [vals, Arg.val]
                            refine ⟨c, sn, R, rfl, hdwn.1, hmn, ?_⟩
                            rw [ite_eq_right (by omega)]
                            intro fl' unass' m_i hfl_i
                            dsimp only
                            intro hm_i
                            let si : FullState :=
                              { sn with core := { sn.core with
                                flags := fl', unassigned := unass' } }
                            have hdwi := m8_var_fullDenseInvW_setInact hdwn
                              (unass' := unass') hfl_i
                            c0_hsteps!
                            let sf : FullState :=
                              { si with scratch := { si.scratch with
                                bve_cnt := si.scratch.bve_cnt + 1#64 } }
                            have hdwf := m6_fullDenseInvW_with_scratch hdwi
                              (sc' := sf.scratch) { hdwi.1.scratch_ok with } rfl rfl
                            exact hQ 1#64 sf _ hdwf.toDense (htmkn.congr rfl rfl)
                              (by dsimp only [sf, si]; omega)
                              hfln (Or.inl rfl) (by simp) hm
                          · intro J29 hJ29
                            c0_hsplit
                            · c0_hsteps_nogrp
                              refine wp_call_of_spec _ _ (hWeaken _ _ _ _ ?_)
                              dsimp only [vals, Arg.val]
                              refine ⟨c, F0, F_cur, sp, R, rfl, hdwp, htmkp,
                                by rw [hplnl.2, hcvp]; omega,
                                by omega,
                                fun j hj => m8_var_bveEntry_weak (hent_np j hj),
                                hmp, ?_⟩
                              intro ok_w sw mw hdww htmkw hcvw hflw _ _ hmw
                              c0_hsplit
                              · c0_hsteps!
                                exact hJ29 sw mw ⟨hdww, htmkw, hcvw.trans hcvp,
                                  by rw [hflw]; exact hflp, hmw⟩
                              · c0_hsteps!
                                exact hJ27 sw mw ⟨hdww, htmkw, hcvw.trans hcvp,
                                  by rw [hflw]; exact hflp, hmw⟩
                            · c0_hsteps!
                              exact hJ29 sp mp ⟨hdwp, htmkp, hcvp, hflp, hmp⟩)
                        (fun J28 hJ28 => by
                          c0_hsplit
                          · c0_hsteps_nogrp
                            refine wp_call_of_spec _ _ (hWeaken _ _ _ _ ?_)
                            dsimp only [vals, Arg.val]
                            refine ⟨c, F0, F_cur, s2, R, rfl, hdw2, htmk0,
                              by dsimp only [s2, s1]; rw [hplnl.1]; omega,
                              by rw [show (0 : BitVec 32).toNat = 0 from rfl, Nat.zero_add]; omega,
                              fun i hi => by
                                dsimp only [s2]
                                rw [show (0 : BitVec 32).toNat = 0 from rfl, Nat.zero_add]
                                exact m8_var_bveEntry_weak (hent_p2 i hi),
                              hm2, ?_⟩
                            intro ok_w sw mw hdww htmkw hcvw hflw _ _ hmw
                            c0_hsplit
                            · c0_hsteps!
                              refine hJ28 sw mw
                                ⟨hdww, htmkw, hcvw, by rw [hflw]; exact Nat.le_refl _,
                                  fun j hj => ?_, hmw⟩
                              exfalso
                              have hnp0 : np ≠ 0#32 := fun h => by subst h; simp at hc
                              have hnn0 := hnp_nn.resolve_left hnp0
                              rw [hnn0, show (0#32).toNat = 0 from rfl] at hj; omega
                            · c0_hsteps!
                              exact hJ27 sw mw ⟨hdww, htmkw, hcvw,
                                by rw [hflw]; exact Nat.le_refl _, hmw⟩
                          · c0_hsteps!
                            exact hJ28 s2 m2 ⟨hdw2, htmk0, rfl, Nat.le_refl _, hent_n2', hm2⟩)))
                (fun J26 hJ26 => by
                  c0_hsplit
                  · c0_hsteps!; exact hJ26 m2 ⟨rfl, Or.inl hc⟩
                  · c0_hsplit
                    · c0_hsteps!; exact hJ26 m2 ⟨rfl, Or.inr hc⟩
                    · c0_hsteps!; exact hJ25 m2 rfl)
            · c0_hsteps!; exact hJ25 m2 rfl)

/-! ## 3. `full_bve_var_m8_wp` (Canonical `FullFastBveBudgets.fullBveVarDefSpec`) -/

/-- Certifies canonical `FullFastBveBudgets.fullBveVarDefSpec` for
`FullM8CoreParity.full_bve_var_body`. -/
theorem full_bve_var_m8_wp (Γ : Env)
    (hVarM7 : ∀ a m Q X, FullFastBveBudgets.fullBveVarDefSpec a m Q X →
      Γ "full_bve_var_m7" [i64, i32] [i64] a m Q X) :
    ∀ a m Q X, FullFastBveBudgets.fullBveVarDefSpec a m Q X →
      Func.wp Γ FullM8CoreParity.full_bve_var_body a m Q X := by
  rintro ⟨h, v, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hden, htmk, hv, hm, hQ⟩
  unfold Func.wp FullM8CoreParity.full_bve_var_body
  c0_hsteps_nogrp
  refine wp_call_of_spec _ _ (hVarM7 _ _ _ _ ?_)
  refine ⟨c, F0, s, R, rfl, hden, htmk, hv, hm, fun r s' m' hden' htmk' hcv hfu hr h20 hm' => ?_⟩
  c0_hsteps!
  exact hQ r s' m' hden' htmk' hcv hfu hr h20 hm'

end LeanQbe.T.Examples.Kissat.FullM8CoreParity
