/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Substitute.Helpers

/-!
# Tarjan SCC DFS Invariant & Core Transitions (`Proof.Substitute.TarjanInv0`)

Defines `TarjanLoopBase`, `M6TarjanDfsInv`, termination `measure`, `scc_pop_equiv`,
and the initial/step/back-edge DFS transitions for single-pass `wvec` `full_tarjan_scc`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Substitute

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open Kraken.Bedrock2.Test

public section

/-- Common base invariants carried across all `full_tarjan_scc` loops and joins. -/
@[expose] def TarjanLoopBase (c : FullCfg) (F_cur : List (List Nat))
    (s0 st : FullState) : Prop :=
  AgreesExcept tarjanSccMask s0 st ∧ st.LengthsOk c ∧ st.scratch.res_sz.toNat ≤ c.max_vars ∧
  FullPartialReprInv F_cur st.core ∧ FullUnitsSoundInv F_cur st st.scratch.res_sz.toNat ∧
  (st.core.inconsistent ≠ 0#64 → (cnfOfClauses F_cur).Unsat)

@[expose] def activeLit (s0 : FullState) (l : Nat) : Prop :=
  l < 2 * s0.core.cur_vars ∧ (s0.core.flags[l / 2]?.getD 0#32 &&& 1#32) ≠ 0#32

@[expose] def activeEdge (s0 : FullState) (u v : Nat) : Prop :=
  activeLit s0 u ∧ activeLit s0 v ∧
  v ∈ sliceBinsFrom s0.core.wstk (fullWatchOffCore s0.core (u ^^^ 1))
    (fullWatchSizeCore s0.core (u ^^^ 1))

theorem activeEdge_binEdge {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 : FullState} (hw0 : FullWitnessInv c F0 F_cur s0.core) (hdm : s0.core.dense_mode = 0#64)
    {u v : Nat} (he : activeEdge s0 u v) : BinEdge (cnfOfClauses F_cur) u v := by
  have hwat : WatchesInv F_cur s0.core := by
    have hm := hw0.watches; unfold ModeWatchesInv at hm; rwa [ite_eq_left hdm] at hm
  have hbe :=
    watchSlice_mem_sliceBinsFrom (hwat.slices (u ^^^ 1) (litNeg_lt_two_mul he.1.1)) v he.2.2
  simpa only [← litNeg_eq_xor1, litNeg_litNeg] using hbe.2

@[expose] def onScc (st : FullState) (l : Nat) : Prop :=
  ∃ j < st.core.tmp_cnt, (st.scratch.work_stk1[j]?.getD 0#32).toNat = l

@[expose] def onDv (st : FullState) (dsp l : Nat) : Prop :=
  ∃ i < dsp, (st.scratch.work_stk2[i]?.getD 0#32).toNat = l

@[expose] def dvWorkSum (s0 st : FullState) : Nat → Nat
  | 0 => 0
  | k + 1 =>
    let lit := (st.scratch.work_stk2[k]?.getD 0#32).toNat
    let sz := fullWatchSizeCore s0.core (lit ^^^ 1)
    let pos := (st.scratch.wsort[k]?.getD 0#32).toNat
    dvWorkSum s0 st k + (sz - pos + 1)

theorem dvWorkSum_congr {s0 st1 st2 : FullState} :
    ∀ k, (∀ i < k, st1.scratch.work_stk2[i]? = st2.scratch.work_stk2[i]? ∧
      st1.scratch.wsort[i]? = st2.scratch.wsort[i]?) →
      dvWorkSum s0 st1 k = dvWorkSum s0 st2 k
  | 0, _ => rfl
  | k + 1, h => by
    unfold dvWorkSum
    rw [dvWorkSum_congr k (fun i hi => h i (by omega)), (h k (by omega)).1, (h k (by omega)).2]

/-- Complete Tarjan SCC invariant across outer (`dsp = 0`, `tmp_cnt = 0`) and inner DFS loops. -/
structure M6TarjanDfsInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s0 : FullState) (root mroot reached dsp : Nat) (st : FullState) : Prop where
  agrees : AgreesExcept tarjanSccMask s0 st
  len_ok : st.LengthsOk c
  inc0 : st.core.inconsistent = 0#64
  rsz_le : st.scratch.res_sz.toNat ≤ c.max_vars
  partial_repr : FullPartialReprInv F_cur st.core
  units_ok : FullUnitsSoundInv F_cur st st.scratch.res_sz.toNat
  reached_le : reached ≤ 2 * s0.core.cur_vars
  tmk_le : ∀ l < 2 * s0.core.cur_vars, (st.scratch.tarjan_mark[l]?.getD 0#32).toNat ≤ reached
  tmk_inj : ∀ a b, a < 2 * s0.core.cur_vars → b < 2 * s0.core.cur_vars →
    1 ≤ (st.scratch.tarjan_mark[a]?.getD 0#32).toNat →
    (st.scratch.tarjan_mark[a]?.getD 0#32).toNat = (st.scratch.tarjan_mark[b]?.getD 0#32).toNat →
    a = b
  tmk_surj : ∀ t, 1 ≤ t → t ≤ reached →
    ∃ l < 2 * s0.core.cur_vars, (st.scratch.tarjan_mark[l]?.getD 0#32).toNat = t
  tmk_active : ∀ l < 2 * s0.core.cur_vars,
    1 ≤ (st.scratch.tarjan_mark[l]?.getD 0#32).toNat → activeLit s0 l
  top_le : st.core.tmp_cnt ≤ reached
  scc_lt : ∀ i < st.core.tmp_cnt,
    (st.scratch.work_stk1[i]?.getD 0#32).toNat < 2 * s0.core.cur_vars
  scc_tmk_ge : ∀ i < st.core.tmp_cnt,
    1 ≤ mroot ∧
    mroot ≤ (st.scratch.tarjan_mark[(st.scratch.work_stk1[i]?.getD 0#32).toNat]?.getD 0#32).toNat
  scc_tmk_mono : ∀ i j, i < j → j < st.core.tmp_cnt →
    (st.scratch.tarjan_mark[(st.scratch.work_stk1[i]?.getD 0#32).toNat]?.getD 0#32).toNat <
    (st.scratch.tarjan_mark[(st.scratch.work_stk1[j]?.getD 0#32).toNat]?.getD 0#32).toNat
  scc_iff_trc : ∀ l < 2 * s0.core.cur_vars,
    onScc st l ↔
      (1 ≤ (st.scratch.tarjan_mark[l]?.getD 0#32).toNat ∧
       st.scratch.tarjan_reach[l]?.getD 0#32 ≠ 0xFFFFFFFF#32)
  trc_range : ∀ i < st.core.tmp_cnt,
    let x := (st.scratch.work_stk1[i]?.getD 0#32).toNat
    mroot ≤ (st.scratch.tarjan_reach[x]?.getD 0#32).toNat ∧
    (st.scratch.tarjan_reach[x]?.getD 0#32).toNat ≤ (st.scratch.tarjan_mark[x]?.getD 0#32).toNat
  trc_witness : ∀ i < st.core.tmp_cnt,
    let x := (st.scratch.work_stk1[i]?.getD 0#32).toNat
    ∃ w < 2 * s0.core.cur_vars, onScc st w ∧
      (st.scratch.tarjan_mark[w]?.getD 0#32).toNat =
        (st.scratch.tarjan_reach[x]?.getD 0#32).toNat ∧
      BinReach (cnfOfClauses F_cur) x w
  dsp_le : dsp ≤ st.core.tmp_cnt
  dv_on_scc : ∀ i < dsp, onScc st (st.scratch.work_stk2[i]?.getD 0#32).toNat
  dv_tmk_mono : ∀ i j, i < j → j < dsp →
    (st.scratch.tarjan_mark[(st.scratch.work_stk2[i]?.getD 0#32).toNat]?.getD 0#32).toNat <
    (st.scratch.tarjan_mark[(st.scratch.work_stk2[j]?.getD 0#32).toNat]?.getD 0#32).toNat
  dv0_root : 0 < dsp →
    (st.scratch.work_stk2[0]?.getD 0#32).toNat = root ∧
    (st.scratch.work_stk1[0]?.getD 0#32).toNat = root ∧
    (st.scratch.tarjan_mark[root]?.getD 0#32).toNat = mroot ∧ activeLit s0 root
  dv_edges : ∀ i, i + 1 < dsp →
    activeEdge s0 (st.scratch.work_stk2[i]?.getD 0#32).toNat
      (st.scratch.work_stk2[i + 1]?.getD 0#32).toNat
  dpos_slice : ∀ i < dsp,
    let lit := (st.scratch.work_stk2[i]?.getD 0#32).toNat
    let nl := lit ^^^ 1
    let off := fullWatchOffCore s0.core nl
    let sz := fullWatchSizeCore s0.core nl
    let pos := (st.scratch.wsort[i]?.getD 0#32).toNat
    pos ≤ sz ∧ WatchSliceOk F_cur s0.core nl (off + pos) (sz - pos) ∧
    ∃ scanned, sliceBinsFrom s0.core.wstk off sz =
        scanned ++ sliceBinsFrom s0.core.wstk (off + pos) (sz - pos) ∧
      ∀ ot ∈ scanned, activeLit s0 ot →
        1 ≤ (st.scratch.tarjan_mark[ot]?.getD 0#32).toNat ∧
        (onScc st ot → (i + 1 < dsp → ot ≠ (st.scratch.work_stk2[i + 1]?.getD 0#32).toNat) →
          (st.scratch.tarjan_reach[lit]?.getD 0#32).toNat ≤
            (st.scratch.tarjan_reach[ot]?.getD 0#32).toNat) ∧
        (i + 1 < dsp → ot = (st.scratch.work_stk2[i + 1]?.getD 0#32).toNat ∨
          (st.scratch.tarjan_mark[ot]?.getD 0#32).toNat <
            (st.scratch.tarjan_mark[(st.scratch.work_stk2[i + 1]?.getD 0#32).toNat]?.getD
              0#32).toNat)
  pop_trc_lt : ∀ u, onScc st u → ¬ onDv st dsp u →
    (st.scratch.tarjan_reach[u]?.getD 0#32).toNat < (st.scratch.tarjan_mark[u]?.getD 0#32).toNat
  pop_edges_vis : ∀ u v, onScc st u → ¬ onDv st dsp u → activeEdge s0 u v →
    1 ≤ (st.scratch.tarjan_mark[v]?.getD 0#32).toNat
  pop_trc_fwd : ∀ u v, onScc st u → ¬ onDv st dsp u → activeEdge s0 u v → onScc st v →
    (st.scratch.tarjan_mark[u]?.getD 0#32).toNat < (st.scratch.tarjan_mark[v]?.getD 0#32).toNat →
    (st.scratch.tarjan_reach[u]?.getD 0#32).toNat ≤ (st.scratch.tarjan_reach[v]?.getD 0#32).toNat
  pop_dv_order : ∀ u i, onScc st u → ¬ onDv st dsp u → i < dsp →
    activeEdge s0 u (st.scratch.work_stk2[i]?.getD 0#32).toNat →
    (st.scratch.tarjan_mark[(st.scratch.work_stk2[i]?.getD 0#32).toNat]?.getD 0#32).toNat <
    (st.scratch.tarjan_mark[u]?.getD 0#32).toNat
  scc_parent_ge : ∀ j < st.core.tmp_cnt, ∀ d < dsp,
    (st.scratch.tarjan_mark[(st.scratch.work_stk2[d]?.getD 0#32).toNat]?.getD 0#32).toNat <
    (st.scratch.tarjan_mark[(st.scratch.work_stk1[j]?.getD 0#32).toNat]?.getD 0#32).toNat →
    ∃ i < j,
      (st.scratch.tarjan_mark[(st.scratch.work_stk2[d]?.getD 0#32).toNat]?.getD 0#32).toNat ≤
        (st.scratch.tarjan_mark[(st.scratch.work_stk1[i]?.getD 0#32).toNat]?.getD 0#32).toNat ∧
      activeEdge s0 (st.scratch.work_stk1[i]?.getD 0#32).toNat
        (st.scratch.work_stk1[j]?.getD 0#32).toNat
  mroot_reach : 0 < dsp →
    ∀ l < 2 * s0.core.cur_vars,
      mroot ≤ (st.scratch.tarjan_mark[l]?.getD 0#32).toNat → BinReach (cnfOfClauses F_cur) root l

namespace M6TarjanDfsInv

variable {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
  {s0 st : FullState} {root mroot reached dsp : Nat}

theorem toBase (h : M6TarjanDfsInv c F0 F_cur s0 root mroot reached dsp st) :
    TarjanLoopBase c F_cur s0 st :=
  ⟨h.agrees, h.len_ok, h.rsz_le, h.partial_repr, h.units_ok, fun hc => absurd h.inc0 hc⟩

theorem onScc_lt (h : M6TarjanDfsInv c F0 F_cur s0 root mroot reached dsp st)
    {u : Nat} (hu : onScc st u) : u < 2 * s0.core.cur_vars :=
  let ⟨j, hj, hje⟩ := hu; hje ▸ h.scc_lt j hj

theorem dv_lt (h : M6TarjanDfsInv c F0 F_cur s0 root mroot reached dsp st)
    {i : Nat} (hi : i < dsp) : (st.scratch.work_stk2[i]?.getD 0#32).toNat < 2 * s0.core.cur_vars :=
  h.onScc_lt (h.dv_on_scc i hi)

theorem reached_lt_of_unvisited (h : M6TarjanDfsInv c F0 F_cur s0 root mroot reached dsp st)
    {l : Nat} (hl : l < 2 * s0.core.cur_vars)
    (h0 : (st.scratch.tarjan_mark[l]?.getD 0#32).toNat = 0) : reached < 2 * s0.core.cur_vars := by
  let f : Nat → Nat := fun k =>
    if hk : k < reached then (h.tmk_surj (k + 1) (by omega) (by omega)).choose else 0
  have hf : ∀ k (hk : k < reached),
      f k < 2 * s0.core.cur_vars ∧ (st.scratch.tarjan_mark[f k]?.getD 0#32).toNat = k + 1 :=
    fun k hk => by
      simp only [f, hk, ↓reduceDIte]
      exact (h.tmk_surj (k + 1) (by omega) (by omega)).choose_spec
  refine inj_lt_of_missing (v := l) f (fun i j hi hj heq => ?_) (fun i hi => (hf i hi).1) hl
    (fun i hi heq => ?_)
  · have h1 := (hf i hi).2; have h2 := (hf j hj).2; rw [heq] at h1; omega
  · have h1 := (hf i hi).2; rw [heq, h0] at h1; omega

@[expose] def measure (c : FullCfg) (s0 st : FullState) (reached dsp : Nat) : Nat :=
  (2 * s0.core.cur_vars - reached) * (c.wcap + 2) + dvWorkSum s0 st dsp

theorem dvWorkSum_split_aux {s0 st : FullState} {dsp : Nat} (hdsp : 0 < dsp) :
    dvWorkSum s0 st dsp = dvWorkSum s0 st (dsp - 1) +
      (fullWatchSizeCore s0.core ((st.scratch.work_stk2[dsp - 1]?.getD 0#32).toNat ^^^ 1) -
        (st.scratch.wsort[dsp - 1]?.getD 0#32).toNat + 1) := by
  cases dsp with | zero => omega | succ _ => rfl

theorem measure_pos (hdsp : 0 < dsp) : 0 < measure c s0 st reached dsp := by
  cases dsp with
  | zero => omega
  | succ k =>
    have hs := dvWorkSum_split_aux (s0 := s0) (st := st) (Nat.succ_pos k)
    dsimp only [measure]; rw [hs]; omega

theorem reset_empty (h : M6TarjanDfsInv c F0 F_cur s0 root mroot reached dsp st)
    (htc0 : st.core.tmp_cnt = 0) : M6TarjanDfsInv c F0 F_cur s0 0 1 reached 0 st :=
  { h with
    top_le := by omega, scc_lt := by omega, scc_tmk_ge := by omega, scc_tmk_mono := by omega
    trc_range := by omega, trc_witness := by omega, dsp_le := by omega, dv_on_scc := by omega
    dv_tmk_mono := by omega, dv0_root := by omega, dv_edges := by omega, dpos_slice := by omega
    pop_trc_lt := fun _ ⟨_, h, _⟩ => by omega, pop_edges_vis := fun _ _ ⟨_, h, _⟩ => by omega
    pop_trc_fwd := fun _ _ ⟨_, h, _⟩ => by omega, pop_dv_order := fun _ _ ⟨_, h, _⟩ => by omega
    scc_parent_ge := by omega, mroot_reach := by omega }

theorem scc_pop_equiv (h : M6TarjanDfsInv c F0 F_cur s0 root mroot reached dsp st)
    (hw0 : FullWitnessInv c F0 F_cur s0.core) (hdm : s0.core.dense_mode = 0#64) (hdsp : 0 < dsp)
    (htrc_eq : (st.scratch.tarjan_reach[(st.scratch.work_stk2[dsp - 1]?.getD 0#32).toNat]?.getD
        0#32).toNat =
      (st.scratch.tarjan_mark[(st.scratch.work_stk2[dsp - 1]?.getD 0#32).toNat]?.getD 0#32).toNat)
    (hscan : ∀ v, activeEdge s0 (st.scratch.work_stk2[dsp - 1]?.getD 0#32).toNat v → onScc st v →
      (st.scratch.tarjan_mark[(st.scratch.work_stk2[dsp - 1]?.getD 0#32).toNat]?.getD 0#32).toNat ≤
        (st.scratch.tarjan_reach[v]?.getD 0#32).toNat) :
    ∃ k0 < st.core.tmp_cnt,
      st.scratch.work_stk1[k0]?.getD 0#32 = st.scratch.work_stk2[dsp - 1]?.getD 0#32 ∧
      (∀ j, k0 < j → j < st.core.tmp_cnt →
        st.scratch.work_stk1[j]?.getD 0#32 ≠ st.scratch.work_stk2[dsp - 1]?.getD 0#32) ∧
      (dsp = 1 → k0 = 0) ∧
      (∀ j, k0 ≤ j → j < st.core.tmp_cnt →
        LitEquiv (cnfOfClauses F_cur) (st.scratch.work_stk1[j]?.getD 0#32).toNat
          (st.scratch.work_stk2[dsp - 1]?.getD 0#32).toNat) := by
  let lit := (st.scratch.work_stk2[dsp - 1]?.getD 0#32).toNat
  obtain ⟨k0, hk0_lt, hk0_eq⟩ := h.dv_on_scc (dsp - 1) (by omega)
  have hk0_bv : st.scratch.work_stk1[k0]?.getD 0#32 = st.scratch.work_stk2[dsp - 1]?.getD 0#32 :=
    BitVec.eq_of_toNat_eq hk0_eq
  have hk0_uniq : ∀ j, k0 < j → j < st.core.tmp_cnt →
      st.scratch.work_stk1[j]?.getD 0#32 ≠ st.scratch.work_stk2[dsp - 1]?.getD 0#32 :=
    fun j hj1 hj2 heq => by have := h.scc_tmk_mono k0 j hj1 hj2; rw [heq, hk0_bv] at this; omega
  have hk0_zero : dsp = 1 → k0 = 0 := fun h1 => Classical.byContradiction fun hz => by
    have h0 := h.dv0_root hdsp; have hmt := h.scc_tmk_mono 0 k0 (by omega) hk0_lt
    have hk0_rt : (st.scratch.work_stk1[k0]?.getD 0#32).toNat = root := by
      rw [hk0_eq, h1]; exact h0.1
    rw [h0.2.1, hk0_rt] at hmt; omega
  have hnot_dv : ∀ j, k0 < j → j < st.core.tmp_cnt →
      ¬ onDv st dsp (st.scratch.work_stk1[j]?.getD 0#32).toNat := fun j hj1 hj2 ⟨d, hd, hdeq⟩ => by
    have hlt1 := h.scc_tmk_mono k0 j hj1 hj2; rw [hk0_eq, ← hdeq] at hlt1
    by_cases hde : d = dsp - 1
    · subst hde; omega
    · have := h.dv_tmk_mono d (dsp - 1) (by omega) (by omega); omega
  have hge_of_tmk : ∀ i < st.core.tmp_cnt,
      (st.scratch.tarjan_mark[lit]?.getD 0#32).toNat ≤
        (st.scratch.tarjan_mark[(st.scratch.work_stk1[i]?.getD 0#32).toNat]?.getD 0#32).toNat →
      k0 ≤ i := fun i hi hle => Classical.byContradiction fun hlt => by
    have hmt := h.scc_tmk_mono i k0 (by omega) hk0_lt; rw [hk0_eq] at hmt; dsimp only [lit] at hle
    omega
  have htrc_ge : ∀ j, k0 ≤ j → j < st.core.tmp_cnt →
      (st.scratch.tarjan_mark[lit]?.getD 0#32).toNat ≤
        (st.scratch.tarjan_reach[(st.scratch.work_stk1[j]?.getD 0#32).toNat]?.getD 0#32).toNat := by
    intro j; induction j using Nat.strongRecOn with
    | ind j ih =>
      intro hj1 hj2; rcases Nat.eq_or_lt_of_le hj1 with rfl | hgt
      · rw [hk0_eq]; exact Nat.le_of_eq htrc_eq.symm
      · have hlt := h.scc_tmk_mono k0 j hgt hj2; rw [hk0_eq] at hlt
        obtain ⟨i, hij, hi_tmk, hedge⟩ := h.scc_parent_ge j hj2 (dsp - 1) (by omega) hlt
        have hi_ge := hge_of_tmk i (by omega) hi_tmk
        rcases Nat.eq_or_lt_of_le hi_ge with rfl | higt
        · rw [hk0_eq] at hedge; exact hscan _ hedge ⟨j, hj2, rfl⟩
        · exact Nat.le_trans (ih i hij hi_ge (by omega))
            (h.pop_trc_fwd _ _ ⟨i, by omega, rfl⟩ (hnot_dv i higt (by omega)) hedge
              ⟨j, hj2, rfl⟩ (h.scc_tmk_mono i j hij hj2))
  have hdown : ∀ j, k0 ≤ j → j < st.core.tmp_cnt →
      BinReach (cnfOfClauses F_cur) lit (st.scratch.work_stk1[j]?.getD 0#32).toNat := by
    intro j; induction j using Nat.strongRecOn with
    | ind j ih =>
      intro hj1 hj2; rcases Nat.eq_or_lt_of_le hj1 with rfl | hgt
      · dsimp only [lit]; rw [hk0_eq]; exact BinReach.refl _
      · have hlt := h.scc_tmk_mono k0 j hgt hj2; rw [hk0_eq] at hlt
        obtain ⟨i, hij, hi_tmk, hedge⟩ := h.scc_parent_ge j hj2 (dsp - 1) (by omega) hlt
        exact binReach_trans (ih i hij (hge_of_tmk i (by omega) hi_tmk) (by omega))
          (BinReach.step (activeEdge_binEdge hw0 hdm hedge) (BinReach.refl _))
  have hup : ∀ j, k0 ≤ j → j < st.core.tmp_cnt →
      BinReach (cnfOfClauses F_cur) (st.scratch.work_stk1[j]?.getD 0#32).toNat lit := by
    intro j; induction j using Nat.strongRecOn with
    | ind j ih =>
      intro hj1 hj2; rcases Nat.eq_or_lt_of_le hj1 with rfl | hgt
      · dsimp only [lit]; rw [hk0_eq]; exact BinReach.refl _
      · have hlt_trc := h.pop_trc_lt _ ⟨j, hj2, rfl⟩ (hnot_dv j hgt hj2)
        have hge_trc := htrc_ge j hj1 hj2
        obtain ⟨_, _, ⟨i, hi_lt, rfl⟩, htmk_w, hreach_w⟩ := h.trc_witness j hj2
        have hij : i < j := Classical.byContradiction fun hle => by
          rcases Nat.eq_or_lt_of_le (Nat.le_of_not_gt hle) with rfl | hji
          · omega
          · have := h.scc_tmk_mono j i hji hi_lt; omega
        exact binReach_trans hreach_w (ih i hij (hge_of_tmk i hi_lt (by omega)) hi_lt)
  refine ⟨k0, hk0_lt, hk0_bv, hk0_uniq, hk0_zero, fun j hj1 hj2 =>
    ⟨binReach_sound (hup j hj1 hj2), ?_⟩⟩
  have hd := binReach_sound (hdown j hj1 hj2)
  rw [CNF.entails_clause_def] at hd ⊢; intro α hα
  have h1 := (clauseEvalVal_iff α _).mpr (hd α hα); rw [← clauseEvalVal_iff]
  simp only [clauseEvalVal, List.any_cons, List.any_nil, Bool.or_false] at h1 ⊢
  simpa [Bool.or_comm] using h1

end M6TarjanDfsInv

section M6TarjanTransitions0

attribute [local grind =] List.getElem?_set_self List.getElem?_set_ne Option.getD_some

theorem dvWorkSum_split {s0 st : FullState} {dsp : Nat} (hdsp : 0 < dsp) :
    dvWorkSum s0 st dsp = dvWorkSum s0 st (dsp - 1) +
      (fullWatchSizeCore s0.core ((st.scratch.work_stk2[dsp - 1]?.getD 0#32).toNat ^^^ 1) -
        (st.scratch.wsort[dsp - 1]?.getD 0#32).toNat + 1) :=
  M6TarjanDfsInv.dvWorkSum_split_aux hdsp

theorem m6_tarjan_init_root {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st : FullState} {root mroot reached : Nat}
    (hw0 : FullWitnessInv c F0 F_cur s0.core) (hdm : s0.core.dense_mode = 0#64)
    (h : M6TarjanDfsInv c F0 F_cur s0 0 mroot reached 0 st) (htop0 : st.core.tmp_cnt = 0)
    (hact : activeLit s0 root) (h0 : (st.scratch.tarjan_mark[root]?.getD 0#32).toNat = 0) :
    let reached' := reached + 1
    let r32 := BitVec.ofNat 32 reached'; let rt32 := BitVec.ofNat 32 root
    let st' : FullState :=
      { st with
        core := { st.core with tmp_cnt := 1 }
        scratch :=
          { st.scratch with
            work_stk2 := st.scratch.work_stk2.set 0 rt32, wsort := st.scratch.wsort.set 0 0#32
            tarjan_mark := st.scratch.tarjan_mark.set root r32
            tarjan_reach := st.scratch.tarjan_reach.set root r32
            work_stk1 := st.scratch.work_stk1.set 0 rt32 } }
    reached' ≤ 2 * s0.core.cur_vars ∧
    M6TarjanDfsInv c F0 F_cur s0 root reached' reached' 1 st' := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcl := h.len_ok.core_ok; have hsl := h.len_ok.scratch_ok
  have hcv_le := hcl.cur_vars_le; have hcv_eq := h.agrees.get (·.core.cur_vars)
  have hreach_lt := h.reached_lt_of_unvisited hact.1 h0
  have hwat : WatchesInv F_cur s0.core := by
    have hm := hw0.watches; unfold ModeWatchesInv at hm; rwa [ite_eq_left hdm] at hm
  have hr32 : (BitVec.ofNat 32 (reached + 1)).toNat = reached + 1 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hrt32 : (BitVec.ofNat 32 root).toNat = root := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hact.1; omega)]
  have hscc_l := hsl.work_stk1_len; have hdv_l := hsl.work_stk2_len; have hdp_l := hsl.wsort_len
  have htmk_l := hsl.tarjan_mark_len; have htrc_l := hsl.tarjan_reach_len
  have hrt_lt : root < 2 * c.max_vars := by have := hact.1; omega
  have h0_lt : 0 < 2 * c.max_vars := by omega
  intro reached' r32 rt32 st'
  have hscc_onDv : ∀ u, onScc st' u → onDv st' 1 u := by
    rintro u ⟨j, hj, hjeq⟩; dsimp only [st'] at hj hjeq; obtain rfl : j = 0 := by omega
    exact ⟨0, by omega, by dsimp only [st']; grind⟩
  refine ⟨by omega, {
      agrees := h.agrees.update _, inc0 := h.inc0, rsz_le := h.rsz_le, reached_le := by omega
      partial_repr := h.partial_repr, units_ok := h.units_ok
      len_ok := ⟨{ hcl with vals_len := hcl.vals_len },
        { hsl with work_stk1_len := by simp [st', hscc_l], work_stk2_len := by simp [st', hdv_l],
                   wsort_len := by simp [st', hdp_l], tarjan_mark_len := by simp [st', htmk_l],
                   tarjan_reach_len := by simp [st', htrc_l] }⟩
      tmk_le := fun l hl => by
        dsimp only [st']; by_cases hlr : l = root; · subst hlr; grind
        · have := h.tmk_le l hl; grind
      tmk_inj := fun a b ha hb hpos heq => by
        dsimp only [st'] at hpos heq; by_cases har : a = root <;> by_cases hbr : b = root
        · omega
        · subst har; have := h.tmk_le b hb; grind
        · subst hbr; have := h.tmk_le a ha; grind
        · rw [List.getElem?_set_ne (Ne.symm har)] at hpos heq
          rw [List.getElem?_set_ne (Ne.symm hbr)] at heq; exact h.tmk_inj a b ha hb hpos heq
      tmk_surj := fun t ht1 ht2 => by
        dsimp only [st']; by_cases htr : t = reached + 1
        · subst htr; exact ⟨root, hact.1, by grind⟩
        · obtain ⟨l, hl, hlt⟩ := h.tmk_surj t ht1 (by omega)
          exact ⟨l, hl, by rw [List.getElem?_set_ne (fun he => by subst he; omega)]; exact hlt⟩
      tmk_active := fun l hl hpos => by
        dsimp only [st'] at hpos; by_cases hlr : l = root; · subst hlr; exact hact
        · rw [List.getElem?_set_ne (Ne.symm hlr)] at hpos; exact h.tmk_active l hl hpos
      top_le := by dsimp only [st']; omega
      scc_lt := fun i hi => by
        dsimp only [st'] at hi ⊢; obtain rfl : i = 0 := by omega
        have := hact.1; grind
      scc_tmk_ge := fun i hi => by
        dsimp only [st'] at hi ⊢; obtain rfl : i = 0 := by omega
        grind
      scc_tmk_mono := fun _ _ _ h => by dsimp only [st'] at h; omega
      scc_iff_trc := fun l hl => by
        dsimp only [onScc, st']; constructor
        · rintro ⟨j, hj, hjeq⟩; obtain rfl : j = 0 := by omega
          have hlr : root = l := by grind
          subst hlr; refine ⟨by grind, fun heq => ?_⟩
          rw [List.getElem?_set_self (by omega), Option.getD_some] at heq
          have := congrArg BitVec.toNat heq; rw [hr32] at this; revert this; simp; omega
        · rintro ⟨hpos, hne⟩; by_cases hlr : l = root; · subst hlr; exact ⟨0, by omega, by grind⟩
          · rw [List.getElem?_set_ne (Ne.symm hlr)] at hpos hne
            obtain ⟨_, hj, _⟩ := (h.scc_iff_trc l hl).mpr ⟨hpos, hne⟩; omega
      trc_range := fun i hi => by
        dsimp only [st'] at hi ⊢; obtain rfl : i = 0 := by omega
        grind
      trc_witness := fun i hi => by
        dsimp only [st'] at hi ⊢; obtain rfl : i = 0 := by omega
        refine ⟨root, hact.1, ⟨0, by dsimp only [st']; omega, by dsimp only [st']; grind⟩,
          by grind, ?_⟩
        rw [List.getElem?_set_self (by omega), Option.getD_some, hrt32]; exact BinReach.refl _
      dsp_le := by dsimp only [st']; omega
      dv_on_scc := fun i hi => by
        obtain rfl : i = 0 := by omega
        exact ⟨0, by dsimp only [st']; omega, by dsimp only [st']; grind⟩
      dv_tmk_mono := by omega
      dv0_root := fun _ =>
        ⟨by dsimp only [st']; grind, by dsimp only [st']; grind, by dsimp only [st']; grind, hact⟩
      dv_edges := fun _ hi => by omega
      dpos_slice := fun i hi => by
        obtain rfl : i = 0 := by omega
        dsimp only [st']
        rw [List.getElem?_set_self (by omega), List.getElem?_set_self (by omega),
          Option.getD_some, Option.getD_some, hrt32]
        simp only [show (0#32 : BitVec 32).toNat = 0 from rfl, Nat.add_zero, Nat.sub_zero]
        exact ⟨Nat.zero_le _, hwat.slices _ (litNeg_lt_two_mul hact.1), [], by simp,
          fun _ hm => nomatch hm⟩
      pop_trc_lt := fun u hu hnd => absurd (hscc_onDv u hu) hnd
      pop_edges_vis := fun u _ hu hnd => absurd (hscc_onDv u hu) hnd
      pop_trc_fwd := fun u _ hu hnd => absurd (hscc_onDv u hu) hnd
      pop_dv_order := fun u _ hu hnd => absurd (hscc_onDv u hu) hnd
      scc_parent_ge := fun j hj d hd hlt => by
        dsimp only [st'] at hj hlt ⊢; obtain rfl : j = 0 := by omega
        obtain rfl : d = 0 := by omega
        grind
      mroot_reach := fun _ l hl hge => by
        dsimp only [st'] at hge; by_cases hlr : l = root; · subst hlr; exact BinReach.refl _
        · have := h.tmk_le l hl; grind }⟩

theorem m6_tarjan_advance_dpos {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st : FullState} {root mroot reached dsp : Nat}
    (h : M6TarjanDfsInv c F0 F_cur s0 root mroot reached dsp st)
    (hdsp : 0 < dsp) {pos' : BitVec 32}
    (hpos_gt : (st.scratch.wsort[dsp - 1]?.getD 0#32).toNat < pos'.toNat)
    (hslice' : let lit := (st.scratch.work_stk2[dsp - 1]?.getD 0#32).toNat; let nl := lit ^^^ 1
      let off := fullWatchOffCore s0.core nl; let sz := fullWatchSizeCore s0.core nl
      pos'.toNat ≤ sz ∧ WatchSliceOk F_cur s0.core nl (off + pos'.toNat) (sz - pos'.toNat) ∧
      ∃ scanned, sliceBinsFrom s0.core.wstk off sz =
          scanned ++ sliceBinsFrom s0.core.wstk (off + pos'.toNat) (sz - pos'.toNat) ∧
        ∀ ot ∈ scanned, activeLit s0 ot →
          1 ≤ (st.scratch.tarjan_mark[ot]?.getD 0#32).toNat ∧
          (onScc st ot →
            (st.scratch.tarjan_reach[lit]?.getD 0#32).toNat ≤
              (st.scratch.tarjan_reach[ot]?.getD 0#32).toNat)) :
    let st' : FullState :=
      { st with scratch := { st.scratch with wsort := st.scratch.wsort.set (dsp - 1) pos' } }
    M6TarjanDfsInv c F0 F_cur s0 root mroot reached dsp st' ∧
    M6TarjanDfsInv.measure c s0 st' reached dsp < M6TarjanDfsInv.measure c s0 st reached dsp := by
  intro st'; have hdp_l := h.len_ok.scratch_ok.wsort_len
  have hcv_le := h.len_ok.core_ok.cur_vars_le; have hcv_eq := h.agrees.get (·.core.cur_vars)
  have hdsp_lt : dsp - 1 < st.scratch.wsort.length := by
    have := h.dsp_le; have := h.top_le; have := h.reached_le; omega
  refine ⟨{ h with
      agrees := h.agrees.update _
      len_ok := ⟨h.len_ok.core_ok, { h.len_ok.scratch_ok with wsort_len := by simp [st', hdp_l] }⟩
      dpos_slice := fun i hi => by
        dsimp only [st']; by_cases hid : i = dsp - 1
        · subst hid; rw [List.getElem?_set_self hdsp_lt, Option.getD_some]
          obtain ⟨h1, h2, sc, h3, h4⟩ := hslice'
          exact ⟨h1, h2, sc, h3, fun ot ho ha =>
            ⟨(h4 ot ho ha).1, fun hs _ => (h4 ot ho ha).2 hs, fun hbad => by omega⟩⟩
        · rw [List.getElem?_set_ne (Ne.symm hid)]; exact h.dpos_slice i hi }, ?_⟩
  have hcongr : dvWorkSum s0 st' (dsp - 1) = dvWorkSum s0 st (dsp - 1) :=
    dvWorkSum_congr (dsp - 1) fun i hi => ⟨rfl, List.getElem?_set_ne (by omega)⟩
  have hsz_ge := hslice'.1; unfold M6TarjanDfsInv.measure
  rw [dvWorkSum_split (st := st') hdsp, dvWorkSum_split (st := st) hdsp, hcongr]
  dsimp only [st']; rw [List.getElem?_set_self hdsp_lt, Option.getD_some]; omega

theorem m6_tarjan_back_edge {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st : FullState} {root mroot reached dsp : Nat}
    (hw0 : FullWitnessInv c F0 F_cur s0.core) (hdm : s0.core.dense_mode = 0#64)
    (h : M6TarjanDfsInv c F0 F_cur s0 root mroot reached dsp st)
    (hdsp : 0 < dsp) {ot pos1 trc_ot : BitVec 32}
    (hpos1 : pos1.toNat = (st.scratch.wsort[dsp - 1]?.getD 0#32).toNat + 1)
    (hedge : activeEdge s0 (st.scratch.work_stk2[dsp - 1]?.getD 0#32).toNat ot.toNat)
    (h0_pos : 1 ≤ (st.scratch.tarjan_mark[ot.toNat]?.getD 0#32).toNat)
    (htrc_ot : trc_ot = st.scratch.tarjan_reach[ot.toNat]?.getD 0#32)
    (hlt_trc : trc_ot.toNat <
      (st.scratch.tarjan_reach[(st.scratch.work_stk2[dsp - 1]?.getD 0#32).toNat]?.getD 0#32).toNat)
    (hslice1 :
      let lit := (st.scratch.work_stk2[dsp - 1]?.getD 0#32).toNat
      let nl := lit ^^^ 1; let off := fullWatchOffCore s0.core nl
      let sz := fullWatchSizeCore s0.core nl
      pos1.toNat ≤ sz ∧ WatchSliceOk F_cur s0.core nl (off + pos1.toNat) (sz - pos1.toNat) ∧
      ∃ scanned, sliceBinsFrom s0.core.wstk off sz =
          scanned ++ sliceBinsFrom s0.core.wstk (off + pos1.toNat) (sz - pos1.toNat) ∧
        ∀ x ∈ scanned, activeLit s0 x →
          x = ot.toNat ∨
          (1 ≤ (st.scratch.tarjan_mark[x]?.getD 0#32).toNat ∧
            (onScc st x →
              (st.scratch.tarjan_reach[lit]?.getD 0#32).toNat ≤
                (st.scratch.tarjan_reach[x]?.getD 0#32).toNat))) :
    let lit := (st.scratch.work_stk2[dsp - 1]?.getD 0#32).toNat
    let st' : FullState := { st with scratch :=
      { st.scratch with
        wsort := st.scratch.wsort.set (dsp - 1) pos1
        tarjan_reach := st.scratch.tarjan_reach.set lit trc_ot } }
    M6TarjanDfsInv c F0 F_cur s0 root mroot reached dsp st' ∧
    M6TarjanDfsInv.measure c s0 st' reached dsp < M6TarjanDfsInv.measure c s0 st reached dsp := by
  intro lit st'
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcl := h.len_ok.core_ok; have hsl := h.len_ok.scratch_ok
  have hcv_le := hcl.cur_vars_le; have hcv_eq := h.agrees.get (·.core.cur_vars)
  have hlit_lt : lit < 2 * s0.core.cur_vars := h.dv_lt (by omega)
  have hot_lt : ot.toNat < 2 * s0.core.cur_vars := hedge.2.1.1
  obtain ⟨jlit, hjlit, hjliteq⟩ := h.dv_on_scc (dsp - 1) (by omega)
  have hlit_rng := h.trc_range jlit hjlit
  dsimp only at hlit_rng
  rw [hjliteq] at hlit_rng
  have hlit_tmk := h.tmk_le lit hlit_lt; have hre := h.reached_le
  have htrc_ot_ne_ff : st.scratch.tarjan_reach[ot.toNat]?.getD 0#32 ≠ 0xFFFFFFFF#32 :=
    fun heq => by
      rw [← htrc_ot] at heq; rw [heq] at hlt_trc; revert hlt_trc; simp; omega
  obtain ⟨jot, hjot, hjoteq⟩ := (h.scc_iff_trc ot.toNat hot_lt).mpr ⟨h0_pos, htrc_ot_ne_ff⟩
  have hot_rng := h.trc_range jot hjot
  dsimp only at hot_rng
  rw [hjoteq, ← htrc_ot] at hot_rng
  obtain ⟨w, hw_lt, hwon, hwtmk, hwbr⟩ := h.trc_witness jot hjot
  rw [hjoteq] at hwtmk hwbr
  rw [← htrc_ot] at hwtmk
  have hot_ne_lit : ot.toNat ≠ lit := fun heq => by
    dsimp only [lit] at heq; rw [heq] at htrc_ot; rw [← htrc_ot] at hlt_trc; omega
  have hw_scc : onScc st' w := by
    obtain ⟨jw, hjw, hjwe⟩ := hwon; exact ⟨jw, hjw, hjwe⟩
  have htrc_l := hsl.tarjan_reach_len; have hdp_l := hsl.wsort_len
  have hdsp_lt : dsp - 1 < st.scratch.wsort.length := by
    have := h.dsp_le; have := h.top_le; omega
  refine ⟨{ h with
      agrees := h.agrees.update _
      len_ok := ⟨hcl, { hsl with
        wsort_len := by simp [st', hdp_l], tarjan_reach_len := by simp [st', htrc_l] }⟩
      scc_iff_trc := fun l hl => by
        dsimp only [onScc, st']
        by_cases hll : l = lit
        · subst hll; constructor
          · intro _; refine ⟨((h.scc_iff_trc lit hl).mp ⟨jlit, hjlit, hjliteq⟩).1, fun heq => ?_⟩
            rw [List.getElem?_set_self (by omega), Option.getD_some] at heq
            exact htrc_ot_ne_ff (htrc_ot ▸ heq)
          · intro _; exact ⟨jlit, hjlit, hjliteq⟩
        · rw [List.getElem?_set_ne (Ne.symm hll)]; exact h.scc_iff_trc l hl
      trc_range := fun i hi => by
        dsimp only [st']; by_cases hxl : (st.scratch.work_stk1[i]?.getD 0#32).toNat = lit
        · rw [hxl, List.getElem?_set_self (by omega), Option.getD_some]
          have hrm := hlit_rng.2; dsimp only [lit]; exact ⟨hot_rng.1, by omega⟩
        · rw [List.getElem?_set_ne (Ne.symm hxl)]; exact h.trc_range i hi
      trc_witness := fun i hi => by
        dsimp only [st']; by_cases hxl : (st.scratch.work_stk1[i]?.getD 0#32).toNat = lit
        · rw [hxl, List.getElem?_set_self (by omega), Option.getD_some]
          refine ⟨w, hw_lt, hw_scc, hwtmk,
            binReach_trans (BinReach.step (activeEdge_binEdge hw0 hdm hedge) (BinReach.refl _))
              hwbr⟩
        · rw [List.getElem?_set_ne (Ne.symm hxl)]; exact h.trc_witness i hi
      dpos_slice := fun i hi => by
        by_cases hid : i = dsp - 1
        · subst hid
          obtain ⟨hle, hslc, sc, hseq, hsok⟩ := hslice1
          have hdp_set : (st'.scratch.wsort[dsp - 1]?.getD 0#32).toNat = pos1.toNat := by
            dsimp only [st']; rw [List.getElem?_set_self (by omega), Option.getD_some]
          have hdv_set : (st'.scratch.work_stk2[dsp - 1]?.getD 0#32).toNat = lit := rfl
          rw [hdv_set, hdp_set]
          refine ⟨hle, hslc, sc, hseq, fun x hx hax => ?_⟩
          rcases hsok x hx hax with rfl | ⟨htmk_x, htrc_x⟩
          · refine ⟨h0_pos, fun _ _ => ?_, fun hbad => by omega⟩
            dsimp only [st']
            rw [List.getElem?_set_self (by omega), Option.getD_some,
              List.getElem?_set_ne hot_ne_lit.symm, ← htrc_ot]
            exact Nat.le_refl _
          · refine ⟨htmk_x, fun hx_scc _ => ?_, fun hbad => by omega⟩
            have hx_t : onScc st x := hx_scc
            have hle_x := htrc_x hx_t
            dsimp only [st']
            rw [List.getElem?_set_self (by omega), Option.getD_some]
            by_cases hxl : x = lit
            · subst hxl; rw [List.getElem?_set_self (by omega), Option.getD_some]
              exact Nat.le_refl _
            · rw [List.getElem?_set_ne (Ne.symm hxl)]; omega
        · have hdv_ne_lit : (st.scratch.work_stk2[i]?.getD 0#32).toNat ≠ lit := fun heq => by
            have := h.dv_tmk_mono i (dsp - 1) (by omega) (by omega)
            dsimp only [lit] at heq; rw [← heq] at this; omega
          have hdp_eq : (st'.scratch.wsort[i]?.getD 0#32).toNat =
              (st.scratch.wsort[i]?.getD 0#32).toNat := by
            dsimp only [st']; rw [List.getElem?_set_ne (Ne.symm hid)]
          have hdv_eq : (st'.scratch.work_stk2[i]?.getD 0#32).toNat =
              (st.scratch.work_stk2[i]?.getD 0#32).toNat := rfl
          rw [hdv_eq, hdp_eq]
          obtain ⟨hle, hslc, sc, hseq, hsok⟩ := h.dpos_slice i hi
          refine ⟨hle, hslc, sc, hseq, fun x hx hax => ?_⟩
          obtain ⟨h1, h2, h3⟩ := hsok x hx hax
          refine ⟨h1, fun hsx hne => ?_, fun hi' => h3 hi'⟩
          have hx_ne_lit : x ≠ lit := by
            by_cases hi2 : i = dsp - 2
            · subst hi2
              exact fun he => hne (by omega)
                (by rw [he, show dsp - 2 + 1 = dsp - 1 by omega])
            · have hlt_i1 := h.dv_tmk_mono (i + 1) (dsp - 1) (by omega) (by omega)
              rcases h3 (by omega) with rfl | hlt_x
              · intro he; dsimp only [lit] at he; rw [he] at hlt_i1; omega
              · intro he; dsimp only [lit] at he; rw [he] at hlt_x; omega
          dsimp only [st']
          rw [List.getElem?_set_ne hdv_ne_lit.symm, List.getElem?_set_ne hx_ne_lit.symm]
          exact h2 hsx hne
      pop_trc_lt := fun u hu hnd => by
        have hnul : u ≠ lit := fun he => hnd ⟨dsp - 1, by omega, he.symm⟩
        dsimp only [st']; rw [List.getElem?_set_ne (Ne.symm hnul)]; exact h.pop_trc_lt u hu hnd
      pop_trc_fwd := fun u v hu hnd huv hv htlt => by
        have hnul : u ≠ lit := fun he => hnd ⟨dsp - 1, by omega, he.symm⟩
        have hnvl : v ≠ lit := fun he => by
          have huv' := huv; rw [he] at huv'; dsimp only [lit] at huv'
          have := h.pop_dv_order u (dsp - 1) hu hnd (by omega) huv'
          dsimp only [st'] at htlt; rw [he] at htlt; dsimp only [lit] at htlt; omega
        dsimp only [st'] at htlt ⊢
        rw [List.getElem?_set_ne (Ne.symm hnul), List.getElem?_set_ne (Ne.symm hnvl)]
        exact h.pop_trc_fwd u v hu hnd huv hv htlt }, ?_⟩
  have hcongr : dvWorkSum s0 st' (dsp - 1) = dvWorkSum s0 st (dsp - 1) :=
    dvWorkSum_congr (dsp - 1) fun i hi => ⟨rfl, List.getElem?_set_ne (by omega)⟩
  have hsz_ge := hslice1.1; unfold M6TarjanDfsInv.measure
  rw [dvWorkSum_split (st := st') hdsp, dvWorkSum_split (st := st) hdsp, hcongr]
  dsimp only [st']; rw [List.getElem?_set_self hdsp_lt, Option.getD_some]; omega

theorem dpos_step_nonbin {F_cur : List (List Nat)} {s0 st : FullState}
    {nl off sz pos pos2 : Nat} (hpos_lt : pos < sz) (hpos2 : pos2 = pos + 2)
    (hslc : WatchSliceOk F_cur s0.core nl (off + pos) (sz - pos))
    (hflag0 : (s0.core.wstk[off + pos]?.getD 0#32 &&& 0x80000000#32) = 0#32)
    (hsc : ∃ sc, sliceBinsFrom s0.core.wstk off sz =
        sc ++ sliceBinsFrom s0.core.wstk (off + pos) (sz - pos) ∧
      ∀ x ∈ sc, activeLit s0 x →
        1 ≤ (st.scratch.tarjan_mark[x]?.getD 0#32).toNat ∧
        (onScc st x →
          (st.scratch.tarjan_reach[nl ^^^ 1]?.getD 0#32).toNat ≤
            (st.scratch.tarjan_reach[x]?.getD 0#32).toNat)) :
    pos2 ≤ sz ∧ WatchSliceOk F_cur s0.core nl (off + pos2) (sz - pos2) ∧
    ∃ sc, sliceBinsFrom s0.core.wstk off sz =
        sc ++ sliceBinsFrom s0.core.wstk (off + pos2) (sz - pos2) ∧
      ∀ x ∈ sc, activeLit s0 x →
        1 ≤ (st.scratch.tarjan_mark[x]?.getD 0#32).toNat ∧
        (onScc st x →
          (st.scratch.tarjan_reach[nl ^^^ 1]?.getD 0#32).toNat ≤
            (st.scratch.tarjan_reach[x]?.getD 0#32).toNat) := by
  obtain ⟨_, _, h2le, _, _, _, _, _, hrest, hbins_eq⟩ :=
    watchSlice_step_nonbin hslc (by omega) hflag0
  obtain ⟨sc, hseq, hsok⟩ := hsc; refine ⟨by omega, ?_, sc, ?_, hsok⟩
  · rw [show off + pos2 = off + pos + 2 by omega, show sz - pos2 = sz - pos - 2 by omega]
    exact hrest
  · rw [hseq, hbins_eq, show off + pos2 = off + pos + 2 by omega,
      show sz - pos2 = sz - pos - 2 by omega]

theorem dpos_step_bin {F_cur : List (List Nat)} {s0 st : FullState}
    {nl off sz pos pos1 : Nat} (hpos_lt : pos < sz) (hpos1 : pos1 = pos + 1)
    (hslc : WatchSliceOk F_cur s0.core nl (off + pos) (sz - pos))
    (hflag1 : (s0.core.wstk[off + pos]?.getD 0#32 &&& 0x80000000#32) ≠ 0#32)
    (hsc : ∃ sc, sliceBinsFrom s0.core.wstk off sz =
        sc ++ sliceBinsFrom s0.core.wstk (off + pos) (sz - pos) ∧
      ∀ x ∈ sc, activeLit s0 x →
        1 ≤ (st.scratch.tarjan_mark[x]?.getD 0#32).toNat ∧
        (onScc st x →
          (st.scratch.tarjan_reach[nl ^^^ 1]?.getD 0#32).toNat ≤
            (st.scratch.tarjan_reach[x]?.getD 0#32).toNat)) :
    ∃ w0, s0.core.wstk[off + pos]? = some w0 ∧
      (w0 &&& 0x7FFFFFFF#32).toNat < 2 * s0.core.cur_vars ∧
      (w0 &&& 0x7FFFFFFF#32).toNat ∈ sliceBinsFrom s0.core.wstk off sz ∧
      pos1 ≤ sz ∧ WatchSliceOk F_cur s0.core nl (off + pos1) (sz - pos1) ∧
      ∃ sc, sliceBinsFrom s0.core.wstk off sz =
          sc ++ sliceBinsFrom s0.core.wstk (off + pos1) (sz - pos1) ∧
        ∀ x ∈ sc, activeLit s0 x →
          x = (w0 &&& 0x7FFFFFFF#32).toNat ∨
          (1 ≤ (st.scratch.tarjan_mark[x]?.getD 0#32).toNat ∧
            (onScc st x →
              (st.scratch.tarjan_reach[nl ^^^ 1]?.getD 0#32).toNat ≤
                (st.scratch.tarjan_reach[x]?.getD 0#32).toNat)) := by
  obtain ⟨w0, hw0_eq, _, _, hot_lt, _, hrest, hbins_eq⟩ :=
    watchSlice_step_bin hslc (by omega) hflag1
  obtain ⟨sc, hseq, hsok⟩ := hsc
  refine ⟨w0, hw0_eq, hot_lt,
    by rw [hseq, hbins_eq, List.mem_append, List.mem_cons]; exact Or.inr (Or.inl rfl),
    by omega, ?_, sc ++ [(w0 &&& 0x7FFFFFFF#32).toNat], ?_, fun x hx hax => ?_⟩
  · rw [show off + pos1 = off + pos + 1 by omega, show sz - pos1 = sz - pos - 1 by omega]
    exact hrest
  · rw [hseq, hbins_eq, List.append_assoc, List.singleton_append,
      show off + pos1 = off + pos + 1 by omega, show sz - pos1 = sz - pos - 1 by omega]
  · rcases List.mem_append.mp hx with h1 | h2
    · exact Or.inr (hsok x h1 hax)
    · simp only [List.mem_singleton] at h2; exact Or.inl h2

end M6TarjanTransitions0

end

end LeanQbe.T.Examples.Kissat.Proof.Substitute
