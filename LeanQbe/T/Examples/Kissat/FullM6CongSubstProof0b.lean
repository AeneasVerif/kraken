module

public import LeanQbe.T.Examples.Kissat.FullM6CongSubstProof0
import LeanQbe.T.Examples.Kissat.FullSccLemmas2
import LeanQbe.T.Examples.Kissat.FullSubstLemmas2
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.C0Agrees

/-!
# Kissat M6 Congruence Closure & 2-Round Substitute Proofs — Part 0b

Proves parametric `(Γ : Env)` `Func.wp` contracts for Tarjan SCC and 2-round `substitute`:
1. `full_tarjan_scc` (`full_tarjan_scc_fast_wp`, `full_tarjan_scc_wp`)
2. `full_substitute` (`full_substitute_wp`, `2`-round loop)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM6CongSubst

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullSccSpecs
open LeanQbe.T.Examples.Kissat.Full.FullSccHelpers
open LeanQbe.T.Examples.Kissat.FullFastBveBudgets
open Kraken.Bedrock2.Test

/-! ## 1. Single-Pass `wvec` `full_tarjan_scc` (`full_tarjan_scc_fast_wp` & `full_tarjan_scc_wp`) -/

section TarjanSccProof

open scoped FullArenaTactics FullSccTactics

private structure M6TarjanDfsInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s0 : FullState) (root mroot reached dsp : Nat) (st : FullState) : Prop where
  agrees : AgreesExcept tarjanSccMask s0 st
  len_ok : st.LengthsOk c
  inc0 : st.core.inconsistent = 0#64
  rsz_le : st.scratch.res_sz.toNat ≤ c.max_vars
  partial_repr : PartialReprInv F_cur st.core
  units_ok : UnitsSoundInv F_cur st st.scratch.res_sz.toNat
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
  scc_lt : ∀ i < st.core.tmp_cnt, (st.scratch.work_stk1[i]?.getD 0#32).toNat < 2 * s0.core.cur_vars
  scc_tmk_ge : ∀ i < st.core.tmp_cnt,
    1 ≤ mroot ∧ mroot ≤ (st.scratch.tarjan_mark[(st.scratch.work_stk1[i]?.getD 0#32).toNat]?.getD
      0#32).toNat
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
      (st.scratch.tarjan_mark[w]?.getD 0#32).toNat = (st.scratch.tarjan_reach[x]?.getD 0#32).toNat ∧
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

private theorem toBase (h : M6TarjanDfsInv c F0 F_cur s0 root mroot reached dsp st) :
    TarjanLoopBase c F_cur s0 st :=
  ⟨h.agrees, h.len_ok, h.rsz_le, h.partial_repr, h.units_ok, fun hc => absurd h.inc0 hc⟩

private theorem onScc_lt (h : M6TarjanDfsInv c F0 F_cur s0 root mroot reached dsp st)
    {u : Nat} (hu : onScc st u) : u < 2 * s0.core.cur_vars :=
  let ⟨j, hj, hje⟩ := hu; hje ▸ h.scc_lt j hj

private theorem dv_lt (h : M6TarjanDfsInv c F0 F_cur s0 root mroot reached dsp st)
    {i : Nat} (hi : i < dsp) : (st.scratch.work_stk2[i]?.getD 0#32).toNat < 2 * s0.core.cur_vars :=
  h.onScc_lt (h.dv_on_scc i hi)

private theorem reached_lt_of_unvisited (h : M6TarjanDfsInv c F0 F_cur s0 root mroot reached dsp st)
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

private def measure (c : FullCfg) (s0 st : FullState) (reached dsp : Nat) : Nat :=
  (2 * s0.core.cur_vars - reached) * (c.wcap + 2) + dvWorkSum s0 st dsp

private theorem measure_pos (hdsp : 0 < dsp) : 0 < measure c s0 st reached dsp := by
  cases dsp with
  | zero => omega
  | succ k =>
    have hs := dvWorkSum_split (s0 := s0) (st := st) (Nat.succ_pos k)
    dsimp only [measure]; rw [hs]; omega

private theorem reset_empty (h : M6TarjanDfsInv c F0 F_cur s0 root mroot reached dsp st)
    (htc0 : st.core.tmp_cnt = 0) : M6TarjanDfsInv c F0 F_cur s0 0 1 reached 0 st :=
  { h with
    top_le := by omega, scc_lt := by omega, scc_tmk_ge := by omega, scc_tmk_mono := by omega
    trc_range := by omega, trc_witness := by omega, dsp_le := by omega, dv_on_scc := by omega
    dv_tmk_mono := by omega, dv0_root := by omega, dv_edges := by omega, dpos_slice := by omega
    pop_trc_lt := fun _ ⟨_, h, _⟩ => by omega, pop_edges_vis := fun _ _ ⟨_, h, _⟩ => by omega
    pop_trc_fwd := fun _ _ ⟨_, h, _⟩ => by omega, pop_dv_order := fun _ _ ⟨_, h, _⟩ => by omega
    scc_parent_ge := by omega, mroot_reach := by omega }

private theorem scc_pop_equiv (h : M6TarjanDfsInv c F0 F_cur s0 root mroot reached dsp st)
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

section M6TarjanTransitions

attribute [local grind =] List.getElem?_set_self List.getElem?_set_ne Option.getD_some

private theorem dvWorkSum_split {s0 st : FullState} {dsp : Nat} (hdsp : 0 < dsp) :
    dvWorkSum s0 st dsp = dvWorkSum s0 st (dsp - 1) +
      (fullWatchSizeCore s0.core ((st.scratch.work_stk2[dsp - 1]?.getD 0#32).toNat ^^^ 1) -
        (st.scratch.wsort[dsp - 1]?.getD 0#32).toNat + 1) := by
  cases dsp with | zero => omega | succ _ => rfl

private theorem getElem_congr_idx {α : Type} {xs : List α} {i j : Nat}
    (hi : i < xs.length) (hj : j < xs.length) (h : i = j) : xs[i] = xs[j] := by subst h; rfl

private theorem list_set_getElem_self_eq {α : Type} {xs : List α} {i : Nat}
    (hi : i < xs.length) : xs.set i (xs[i]'hi) = xs := by
  apply List.ext_getElem
  · simp
  · intro j hj1 _; by_cases hji : j = i
    · subst hji; rw [List.getElem_set_self (by omega)]
    · rw [List.getElem_set_ne (Ne.symm hji)]

private theorem m6_tarjan_init_root {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
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

private theorem m6_tarjan_advance_dpos {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
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

private theorem m6_tarjan_back_edge {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
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
  have htrc_ot_ne_ff : st.scratch.tarjan_reach[ot.toNat]?.getD 0#32 ≠ 0xFFFFFFFF#32 := fun heq => by
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

private theorem m6_tarjan_discover_node {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st : FullState} {root mroot reached dsp : Nat}
    (hw0 : FullWitnessInv c F0 F_cur s0.core) (hdm : s0.core.dense_mode = 0#64)
    (h : M6TarjanDfsInv c F0 F_cur s0 root mroot reached dsp st)
    (hdsp : 0 < dsp) {ot pos1 : BitVec 32}
    (hpos1 : pos1.toNat = (st.scratch.wsort[dsp - 1]?.getD 0#32).toNat + 1)
    (hedge : activeEdge s0 (st.scratch.work_stk2[dsp - 1]?.getD 0#32).toNat ot.toNat)
    (h0 : (st.scratch.tarjan_mark[ot.toNat]?.getD 0#32).toNat = 0)
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
    let reached' := reached + 1; let r32 := BitVec.ofNat 32 reached'
    let st' : FullState :=
      { st with
        core := { st.core with tmp_cnt := st.core.tmp_cnt + 1 }
        scratch :=
          { st.scratch with
            wsort := (st.scratch.wsort.set (dsp - 1) pos1).set dsp 0#32
            tarjan_mark := st.scratch.tarjan_mark.set ot.toNat r32
            tarjan_reach := st.scratch.tarjan_reach.set ot.toNat r32
            work_stk1 := st.scratch.work_stk1.set st.core.tmp_cnt ot
            work_stk2 := st.scratch.work_stk2.set dsp ot } }
    reached' ≤ 2 * s0.core.cur_vars ∧
    M6TarjanDfsInv c F0 F_cur s0 root mroot reached' (dsp + 1) st' ∧
    M6TarjanDfsInv.measure c s0 st' reached' (dsp + 1) <
      M6TarjanDfsInv.measure c s0 st reached dsp := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcl := h.len_ok.core_ok; have hsl := h.len_ok.scratch_ok
  have hcv_le := hcl.cur_vars_le; have hcv_eq := h.agrees.get (·.core.cur_vars)
  have hact_ot := hedge.2.1; have hreach_lt := h.reached_lt_of_unvisited hact_ot.1 h0
  have hr32 : (BitVec.ofNat 32 (reached + 1)).toNat = reached + 1 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hscc_l := hsl.work_stk1_len; have hdv_l := hsl.work_stk2_len; have hdp_l := hsl.wsort_len
  have htmk_l := hsl.tarjan_mark_len; have htrc_l := hsl.tarjan_reach_len
  have hot_lt : ot.toNat < 2 * c.max_vars := by have := hact_ot.1; omega
  have htop_lt : st.core.tmp_cnt < 2 * c.max_vars := by have := h.top_le; omega
  have hdsp_lt : dsp < 2 * c.max_vars := by have := h.dsp_le; omega
  have hwat : WatchesInv F_cur s0.core := by
    have hm := hw0.watches; unfold ModeWatchesInv at hm; rwa [ite_eq_left hdm] at hm
  intro reached' r32 st'
  have hdp_set_l : (st.scratch.wsort.set (dsp - 1) pos1).length = 2 * c.max_vars := by simp [hdp_l]
  have hscc_ne : ∀ j < st.core.tmp_cnt, (st.scratch.work_stk1[j]?.getD 0#32).toNat ≠ ot.toNat :=
    fun j hj heq => by have := h.scc_tmk_ge j hj; rw [heq, h0] at this; omega
  have hdv_ne : ∀ i < dsp, (st.scratch.work_stk2[i]?.getD 0#32).toNat ≠ ot.toNat := fun i hi =>
    let ⟨j, hj, hje⟩ := h.dv_on_scc i hi; hje ▸ hscc_ne j hj
  have h0r := h.dv0_root hdsp
  have hmroot_le : 1 ≤ mroot ∧ mroot ≤ reached := by
    have := h.scc_tmk_ge 0 (by have := h.dsp_le; omega)
    rw [h0r.2.1] at this; exact ⟨this.1, h0r.2.2.1 ▸ h.tmk_le root h0r.2.2.2.1⟩
  have hndv_old : ∀ u, ¬ onDv st' (dsp + 1) u → ¬ onDv st dsp u := fun u hnd ⟨i, hi, heq⟩ =>
    hnd ⟨i, by omega, by dsimp only [st']; rw [List.getElem?_set_ne (by omega)]; exact heq⟩
  have hpop_old : ∀ u, onScc st' u → ¬ onDv st' (dsp + 1) u →
      onScc st u ∧ u ≠ ot.toNat ∧ ¬ onDv st dsp u := by
    rintro u ⟨j, hj, hjeq⟩ hnd; dsimp only [st'] at hj hjeq
    by_cases hjt : j = st.core.tmp_cnt
    · subst j; rw [List.getElem?_set_self (by omega), Option.getD_some] at hjeq
      exact absurd ⟨dsp, by omega, by
        dsimp only [st']; rw [List.getElem?_set_self (by omega), Option.getD_some]; exact hjeq⟩ hnd
    · rw [List.getElem?_set_ne (Ne.symm hjt)] at hjeq
      exact ⟨⟨j, by omega, hjeq⟩, hjeq ▸ hscc_ne j (by omega), hndv_old u hnd⟩
  have hinv' : M6TarjanDfsInv c F0 F_cur s0 root mroot (reached + 1) (dsp + 1) st' := {
      agrees := h.agrees.update _, inc0 := h.inc0, rsz_le := h.rsz_le, reached_le := by omega
      partial_repr := h.partial_repr, units_ok := h.units_ok
      len_ok := ⟨{ hcl with vals_len := hcl.vals_len },
        { hsl with work_stk1_len := by simp [st', hscc_l], work_stk2_len := by simp [st', hdv_l],
                   wsort_len := by simp [st', hdp_l], tarjan_mark_len := by simp [st', htmk_l],
                   tarjan_reach_len := by simp [st', htrc_l] }⟩
      tmk_le := fun l hl => by
        dsimp only [st']; by_cases hlo : l = ot.toNat; · subst hlo; grind
        · have := h.tmk_le l hl; grind
      tmk_inj := fun a b ha hb hpos heq => by
        dsimp only [st'] at hpos heq; by_cases hao : a = ot.toNat <;> by_cases hbo : b = ot.toNat
        · omega
        · subst hao; have := h.tmk_le b hb; grind
        · subst hbo; have := h.tmk_le a ha; grind
        · rw [List.getElem?_set_ne (Ne.symm hao)] at hpos heq
          rw [List.getElem?_set_ne (Ne.symm hbo)] at heq; exact h.tmk_inj a b ha hb hpos heq
      tmk_surj := fun t ht1 ht2 => by
        dsimp only [st']; by_cases htr : t = reached + 1
        · subst htr; exact ⟨ot.toNat, hact_ot.1, by grind⟩
        · obtain ⟨l, hl, hlt⟩ := h.tmk_surj t ht1 (by omega)
          exact ⟨l, hl, by rw [List.getElem?_set_ne (fun he => by subst he; omega)]; exact hlt⟩
      tmk_active := fun l hl hpos => by
        dsimp only [st'] at hpos; by_cases hlo : l = ot.toNat; · subst hlo; exact hact_ot
        · rw [List.getElem?_set_ne (Ne.symm hlo)] at hpos; exact h.tmk_active l hl hpos
      top_le := by dsimp only [st']; have := h.top_le; omega
      scc_lt := fun i hi => by
        dsimp only [st'] at hi ⊢; by_cases hit : i = st.core.tmp_cnt
        · subst i; have := hact_ot.1; grind
        · have := h.scc_lt i (by omega); grind
      scc_tmk_ge := fun i hi => by
        dsimp only [st'] at hi ⊢; by_cases hit : i = st.core.tmp_cnt; · subst i; grind
        · have := hscc_ne i (by omega); have := h.scc_tmk_ge i (by omega); grind
      scc_tmk_mono := fun i j hij hj => by
        dsimp only [st'] at hj ⊢; have hni := hscc_ne i (by omega)
        by_cases hjt : j = st.core.tmp_cnt
        · subst j; have := h.tmk_le _ (h.scc_lt i (by omega)); grind
        · have hnj := hscc_ne j (by omega); have := h.scc_tmk_mono i j hij (by omega); grind
      scc_iff_trc := fun l hl => by
        by_cases hlo : l = ot.toNat
        · subst hlo; constructor
          · intro _; dsimp only [st']; refine ⟨by grind, fun heq => ?_⟩
            rw [List.getElem?_set_self (by omega), Option.getD_some] at heq
            have := congrArg BitVec.toNat heq; rw [hr32] at this; revert this; simp; omega
          · intro _; exact ⟨st.core.tmp_cnt, by dsimp only [st']; omega, by dsimp only [st']; grind⟩
        · have hon : onScc st' l ↔ onScc st l :=
            ⟨fun ⟨j, hj, hjeq⟩ => by
               dsimp only [st'] at hj hjeq; by_cases hjt : j = st.core.tmp_cnt
               · subst j; grind
               · exact ⟨j, by omega, by grind⟩,
             fun ⟨j, hj, hjeq⟩ => ⟨j, by dsimp only [st']; omega, by dsimp only [st']; grind⟩⟩
          rw [hon]; dsimp only [st']
          rw [List.getElem?_set_ne (Ne.symm hlo), List.getElem?_set_ne (Ne.symm hlo)]
          exact h.scc_iff_trc l hl
      trc_range := fun i hi => by
        dsimp only [st'] at hi ⊢; by_cases hit : i = st.core.tmp_cnt; · subst i; grind
        · have := hscc_ne i (by omega); have := h.trc_range i (by omega); grind
      trc_witness := fun i hi => by
        dsimp only [st'] at hi ⊢; by_cases hit : i = st.core.tmp_cnt
        · subst i; refine ⟨ot.toNat, hact_ot.1,
            ⟨st.core.tmp_cnt, by dsimp only [st']; omega, by dsimp only [st']; grind⟩, by grind, ?_⟩
          rw [List.getElem?_set_self (by omega), Option.getD_some]; exact BinReach.refl _
        · have hni := hscc_ne i (by omega)
          obtain ⟨_, hw_lt, ⟨j, hj, rfl⟩, htw, hbr⟩ := h.trc_witness i (by omega)
          have hnj := hscc_ne j hj
          refine ⟨_, hw_lt, ⟨j, by dsimp only [st']; omega, by dsimp only [st']; grind⟩,
            by grind, ?_⟩
          rw [List.getElem?_set_ne (Ne.symm hit)]; exact hbr
      dsp_le := by dsimp only [st']; have := h.dsp_le; omega
      dv_on_scc := fun i hi => by
        by_cases hid : i = dsp
        · subst i; exact ⟨st.core.tmp_cnt, by dsimp only [st']; omega, by dsimp only [st']; grind⟩
        · obtain ⟨j, hj, hjeq⟩ := h.dv_on_scc i (by omega)
          exact ⟨j, by dsimp only [st']; omega, by dsimp only [st']; grind⟩
      dv_tmk_mono := fun i j hij hj => by
        dsimp only [st']; have hni := hdv_ne i (by omega)
        by_cases hjd : j = dsp
        · subst j
          have h1 : (st.scratch.work_stk2.set dsp ot)[dsp]? = some ot :=
            List.getElem?_set_self (by rw [hdv_l]; exact hdsp_lt)
          have h2 : (st.scratch.work_stk2.set dsp ot)[i]? = st.scratch.work_stk2[i]? :=
            List.getElem?_set_ne (by omega)
          have h3 : (st.scratch.tarjan_mark.set ot.toNat r32)[ot.toNat]? = some r32 :=
            List.getElem?_set_self (by rw [htmk_l]; exact hot_lt)
          have h4 : (st.scratch.tarjan_mark.set ot.toNat r32)[(st.scratch.work_stk2[i]?.getD
              0#32).toNat]? = st.scratch.tarjan_mark[(st.scratch.work_stk2[i]?.getD 0#32).toNat]? :=
            List.getElem?_set_ne hni.symm
          rw [h1, h2, Option.getD_some, h3, h4, Option.getD_some, hr32]
          have := h.tmk_le _ (h.dv_lt (by omega)); omega
        · have hnj := hdv_ne j (by omega); have := h.dv_tmk_mono i j hij (by omega); grind
      dv0_root := fun _ => by
        have htop_pos : 0 < st.core.tmp_cnt := by have := h.dsp_le; omega
        dsimp only [st']; refine ⟨by grind, by grind, by grind, h0r.2.2.2⟩
      dv_edges := fun i hi => by
        dsimp only [st']
        by_cases hid : i + 1 = dsp
        · rw [show i = dsp - 1 by omega, show dsp - 1 + 1 = dsp by omega,
            List.getElem?_set_ne (by omega : dsp ≠ dsp - 1),
            List.getElem?_set_self (by rw [hdv_l]; exact hdsp_lt), Option.getD_some]
          exact hedge
        · rw [List.getElem?_set_ne (by omega : dsp ≠ i),
            List.getElem?_set_ne (by omega : dsp ≠ i + 1)]
          exact h.dv_edges i (by omega)
      dpos_slice := fun i hi => by
        by_cases hid : i = dsp
        · subst i; dsimp only [st']
          have hw2 : (st.scratch.work_stk2.set dsp ot)[dsp]? = some ot :=
            List.getElem?_set_self (by rw [hdv_l]; exact hdsp_lt)
          have hws : ((st.scratch.wsort.set (dsp - 1) pos1).set dsp 0#32)[dsp]? = some 0#32 :=
            List.getElem?_set_self (by rw [hdp_set_l]; exact hdsp_lt)
          rw [hw2, hws, Option.getD_some, Option.getD_some]
          simp only [show (0#32 : BitVec 32).toNat = 0 from rfl, Nat.add_zero, Nat.sub_zero]
          exact ⟨Nat.zero_le _, hwat.slices _ (litNeg_lt_two_mul hact_ot.1), [], by simp,
            fun _ hm => nomatch hm⟩
        · have hdv_i : (st'.scratch.work_stk2[i]?.getD 0#32).toNat =
              (st.scratch.work_stk2[i]?.getD 0#32).toNat := by dsimp only [st']; grind
          rw [hdv_i]; by_cases hip : i = dsp - 1
          · subst i
            have hdp1 : (st'.scratch.wsort[dsp - 1]?.getD 0#32).toNat = pos1.toNat := by
              dsimp only [st']; rw [List.getElem?_set_ne (by omega)]; grind
            rw [hdp1]; obtain ⟨hle, hslc, sc, hseq, hsok⟩ := hslice1
            refine ⟨hle, hslc, sc, hseq, fun x hx hax => ?_⟩
            by_cases hxo : x = ot.toNat
            · subst hxo
              have hot_dv : ot.toNat = (st'.scratch.work_stk2[dsp - 1 + 1]?.getD 0#32).toNat := by
                dsimp only [st']
                rw [show dsp - 1 + 1 = dsp by omega,
                  List.getElem?_set_self (by rw [hdv_l]; exact hdsp_lt), Option.getD_some]
              refine ⟨by dsimp only [st']; grind, ?_, fun _ => Or.inl hot_dv⟩
              intro _ hne; exfalso; exact hne (by omega) hot_dv
            · obtain ⟨hx_vis, hx_trc⟩ := (hsok x hx hax).elim (fun he => absurd he hxo) id
              have hlt_reach : (st.scratch.tarjan_mark[x]?.getD 0#32).toNat ≤ reached :=
                h.tmk_le x hax.1
              have hlit_ne : (st.scratch.work_stk2[dsp - 1]?.getD 0#32).toNat ≠ ot.toNat :=
                hdv_ne (dsp - 1) (by omega)
              refine ⟨by dsimp only [st']; rw [List.getElem?_set_ne (Ne.symm hxo)]; exact hx_vis,
                fun hsx _ => ?_, fun _ => Or.inr ?_⟩
              · have hsx0 : onScc st x := by
                  obtain ⟨jx, hjx, hjxe⟩ := hsx; dsimp only [st'] at hjx hjxe
                  by_cases hjt : jx = st.core.tmp_cnt
                  · subst jx; rw [List.getElem?_set_self (by omega), Option.getD_some] at hjxe
                    exact absurd hjxe.symm hxo
                  · rw [List.getElem?_set_ne (Ne.symm hjt)] at hjxe; exact ⟨jx, by omega, hjxe⟩
                dsimp only [st']
                rw [List.getElem?_set_ne hlit_ne.symm, List.getElem?_set_ne (Ne.symm hxo)]
                exact hx_trc hsx0
              · dsimp only [st']
                rw [show dsp - 1 + 1 = dsp by omega,
                  List.getElem?_set_self (by rw [hdv_l]; exact hdsp_lt), Option.getD_some,
                  List.getElem?_set_ne (Ne.symm hxo),
                  List.getElem?_set_self (by rw [htmk_l]; exact hot_lt),
                  Option.getD_some, hr32]
                omega
          · have hdp_i : (st'.scratch.wsort[i]?.getD 0#32).toNat =
                (st.scratch.wsort[i]?.getD 0#32).toNat := by
              dsimp only [st']
              rw [List.getElem?_set_ne (Ne.symm hid), List.getElem?_set_ne (Ne.symm hip)]
            rw [hdp_i]; obtain ⟨hle, hslc, sc, hseq, hsok⟩ := h.dpos_slice i (by omega)
            refine ⟨hle, hslc, sc, hseq, fun x hx hax => ?_⟩
            obtain ⟨hx_vis, hx_trc, hx_ord⟩ := hsok x hx hax
            have hxo : x ≠ ot.toNat := fun he => by subst he; omega
            have hli : (st.scratch.work_stk2[i]?.getD 0#32).toNat ≠ ot.toNat := hdv_ne i (by omega)
            have hli1 : (st.scratch.work_stk2[i + 1]?.getD 0#32).toNat ≠ ot.toNat :=
              hdv_ne (i + 1) (by omega)
            refine ⟨by dsimp only [st']; rw [List.getElem?_set_ne (Ne.symm hxo)]; exact hx_vis,
              fun hsx hne => ?_, fun _ => ?_⟩
            · have hsx0 : onScc st x := by
                obtain ⟨jx, hjx, hjxe⟩ := hsx; dsimp only [st'] at hjx hjxe
                by_cases hjt : jx = st.core.tmp_cnt
                · subst jx; rw [List.getElem?_set_self (by omega), Option.getD_some] at hjxe
                  exact absurd hjxe.symm hxo
                · rw [List.getElem?_set_ne (Ne.symm hjt)] at hjxe; exact ⟨jx, by omega, hjxe⟩
              dsimp only [st']
              rw [List.getElem?_set_ne hli.symm, List.getElem?_set_ne (Ne.symm hxo)]
              exact hx_trc hsx0 (fun _ hbad => hne (by omega)
                (by dsimp only [st']; rw [List.getElem?_set_ne (by omega : dsp ≠ i + 1)]
                    exact hbad))
            · dsimp only [st']
              rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne hli1.symm,
                List.getElem?_set_ne (Ne.symm hxo)]
              exact hx_ord (by omega)
      pop_trc_lt := fun u hu hnd => by
        obtain ⟨hu0, hneu, hnd0⟩ := hpop_old u hu hnd
        have := h.pop_trc_lt u hu0 hnd0; dsimp only [st']; grind
      pop_edges_vis := fun u v hu hnd huv => by
        obtain ⟨hu0, _, hnd0⟩ := hpop_old u hu hnd
        by_cases hvo : v = ot.toNat; · subst hvo; dsimp only [st']; grind
        · have := h.pop_edges_vis u v hu0 hnd0 huv; dsimp only [st']; grind
      pop_trc_fwd := fun u v hu hnd huv ⟨jv, hjv, hjveq⟩ htlt => by
        obtain ⟨hu0, hneu, hnd0⟩ := hpop_old u hu hnd
        have hv_vis := h.pop_edges_vis u v hu0 hnd0 huv
        have hnev : v ≠ ot.toNat := fun he => by subst he; omega
        dsimp only [st'] at hjv hjveq htlt ⊢
        have hjvt : jv ≠ st.core.tmp_cnt := fun he => by subst jv; grind
        rw [List.getElem?_set_ne (Ne.symm hjvt)] at hjveq
        have := h.pop_trc_fwd u v hu0 hnd0 huv ⟨jv, by omega, hjveq⟩ (by grind); grind
      pop_dv_order := fun u i hu hnd hi huv => by
        obtain ⟨hu0, hneu, hnd0⟩ := hpop_old u hu hnd
        by_cases hid : i = dsp
        · subst i; dsimp only [st'] at huv
          rw [List.getElem?_set_self (by omega), Option.getD_some] at huv
          have := h.pop_edges_vis u ot.toNat hu0 hnd0 huv; omega
        · have hnid := hdv_ne i (by omega); dsimp only [st'] at huv ⊢
          rw [List.getElem?_set_ne (Ne.symm hid)] at huv
          have := h.pop_dv_order u i hu0 hnd0 (by omega) huv; grind
      scc_parent_ge := fun j hj d hd hlt => by
        dsimp only [st'] at hj hlt ⊢; by_cases hdd : d = dsp
        · subst d; by_cases hjt : j = st.core.tmp_cnt; · subst j; grind
          · have hnj := hscc_ne j (by omega); have := h.tmk_le _ (h.scc_lt j (by omega)); grind
        · have hnd := hdv_ne d (by omega); by_cases hjt : j = st.core.tmp_cnt
          · subst j; obtain ⟨i, hi_lt, hi_eq⟩ := h.dv_on_scc (dsp - 1) (by omega)
            have hni := hscc_ne i hi_lt; refine ⟨i, hi_lt, ?_, ?_⟩
            · have hle : (st.scratch.tarjan_mark[(st.scratch.work_stk2[d]?.getD 0#32).toNat]?.getD
                  0#32).toNat ≤ (st.scratch.tarjan_mark[(st.scratch.work_stk1[i]?.getD
                  0#32).toNat]?.getD 0#32).toNat := by
                rw [hi_eq]; by_cases hd1 : d = dsp - 1; · subst d; exact Nat.le_refl _
                · exact Nat.le_of_lt (h.dv_tmk_mono d (dsp - 1) (by omega) (by omega))
              grind
            · rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega),
                Option.getD_some, hi_eq]; exact hedge
          · have hnj := hscc_ne j (by omega)
            obtain ⟨i, hij, hge, he⟩ := h.scc_parent_ge j (by omega) d (by omega) (by grind)
            have hni := hscc_ne i (by omega); refine ⟨i, hij, by grind, ?_⟩
            rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (Ne.symm hjt)]; exact he
      mroot_reach := fun _ l hl hge => by
        by_cases hlo : l = ot.toNat
        · subst hlo; obtain ⟨j, hj, hjeq⟩ := h.dv_on_scc (dsp - 1) (by omega)
          have hlit_ge := (h.scc_tmk_ge j hj).2; rw [hjeq] at hlit_ge
          exact binReach_trans (h.mroot_reach hdsp _ (h.dv_lt (by omega)) hlit_ge)
            (BinReach.step (activeEdge_binEdge hw0 hdm hedge) (BinReach.refl _))
        · dsimp only [st'] at hge; rw [List.getElem?_set_ne (Ne.symm hlo)] at hge
          exact h.mroot_reach hdsp l hl hge }
  refine ⟨by omega, hinv', ?_⟩; unfold M6TarjanDfsInv.measure
  have hsum1 : dvWorkSum s0 st' (dsp + 1) =
      dvWorkSum s0 st' dsp + (fullWatchSizeCore s0.core (ot.toNat ^^^ 1) + 1) := by
    rw [dvWorkSum_split (s0 := s0) (st := st') (Nat.succ_pos dsp), Nat.succ_sub_one]
    dsimp only [st']; rw [List.getElem?_set_self (by omega),
      List.getElem?_set_self (by rw [hdp_set_l]; omega), Option.getD_some, Option.getD_some,
      show (0#32 : BitVec 32).toNat = 0 from rfl, Nat.sub_zero]
  have hcongr : dvWorkSum s0 st' (dsp - 1) = dvWorkSum s0 st (dsp - 1) :=
    dvWorkSum_congr (dsp - 1) fun i hi => by
      dsimp only [st']; exact ⟨List.getElem?_set_ne (by omega),
        by rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]⟩
  have hsum2 : dvWorkSum s0 st' dsp ≤ dvWorkSum s0 st dsp := by
    rw [dvWorkSum_split (st := st') hdsp, dvWorkSum_split (st := st) hdsp, hcongr]; dsimp only [st']
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_self (by omega), Option.getD_some]; omega
  have hsz_le : fullWatchSizeCore s0.core (ot.toNat ^^^ 1) ≤ c.wcap := by
    have := hwat.layout.bounds (ot.toNat ^^^ 1) (litNeg_lt_two_mul hact_ot.1)
    have := hcl.wlen_le; have := h.agrees.get (·.core.wlen); omega
  have hmul : (2 * s0.core.cur_vars - reached) * (c.wcap + 2) =
      (2 * s0.core.cur_vars - (reached + 1)) * (c.wcap + 2) + (c.wcap + 2) := by
    rw [show 2 * s0.core.cur_vars - reached = (2 * s0.core.cur_vars - (reached + 1)) + 1 by omega,
      Nat.add_mul, Nat.one_mul]
  dsimp only [reached']; rw [hsum1, hmul]; omega

private theorem m6_tarjan_pop_nonroot {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st : FullState} {root mroot reached dsp : Nat}
    (hw0 : FullWitnessInv c F0 F_cur s0.core) (hdm : s0.core.dense_mode = 0#64)
    (h : M6TarjanDfsInv c F0 F_cur s0 root mroot reached dsp st)
    (hdsp : 0 < dsp) {rlit : BitVec 32}
    (hr_eq : rlit = st.scratch.tarjan_reach[(st.scratch.work_stk2[dsp - 1]?.getD 0#32).toNat]?.getD
      0#32)
    (hpos_ge : fullWatchSizeCore s0.core
      ((st.scratch.work_stk2[dsp - 1]?.getD 0#32).toNat ^^^ 1) ≤
      (st.scratch.wsort[dsp - 1]?.getD 0#32).toNat)
    (hne_tmk : rlit.toNat ≠
      (st.scratch.tarjan_mark[(st.scratch.work_stk2[dsp - 1]?.getD 0#32).toNat]?.getD 0#32).toNat) :
    1 < dsp ∧
    ∀ (upd_par : Bool),
      let par := (st.scratch.work_stk2[dsp - 2]?.getD 0#32).toNat
      (upd_par = true →
        rlit.toNat < (st.scratch.tarjan_reach[par]?.getD 0#32).toNat) →
      (upd_par = false →
        (st.scratch.tarjan_reach[par]?.getD 0#32).toNat ≤ rlit.toNat) →
      let st' : FullState :=
        if upd_par then
          { st with scratch := { st.scratch with
              tarjan_reach := st.scratch.tarjan_reach.set par rlit } }
        else st
      M6TarjanDfsInv c F0 F_cur s0 root mroot reached (dsp - 1) st' ∧
      M6TarjanDfsInv.measure c s0 st' reached (dsp - 1) <
        M6TarjanDfsInv.measure c s0 st reached dsp := by
  let lit := (st.scratch.work_stk2[dsp - 1]?.getD 0#32).toNat
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv_le := h.len_ok.core_ok.cur_vars_le; have hcv_eq := h.agrees.get (·.core.cur_vars)
  have htrc_l := h.len_ok.scratch_ok.tarjan_reach_len
  have hlit_lt : lit < 2 * s0.core.cur_vars := h.dv_lt (by omega)
  obtain ⟨jlit, hjlit, hjliteq⟩ := h.dv_on_scc (dsp - 1) (by omega)
  have hlit_rng := h.trc_range jlit hjlit
  dsimp only at hlit_rng
  rw [hjliteq, ← hr_eq] at hlit_rng
  have hr_ge : mroot ≤ rlit.toNat := hlit_rng.1
  have hr_lt : rlit.toNat < (st.scratch.tarjan_mark[lit]?.getD 0#32).toNat := by
    dsimp only [lit]; omega
  have hdsp_gt1 : 1 < dsp := Classical.byContradiction fun hle => by
    have h1 : dsp = 1 := by omega
    have h0r := h.dv0_root hdsp; have hl : lit = root := by dsimp only [lit]; rw [h1]; exact h0r.1
    rw [hl, h0r.2.2.1] at hr_lt; omega
  refine ⟨hdsp_gt1, fun upd_par => ?_⟩
  intro par hupT hupF st'
  have hpar_lt : par < 2 * s0.core.cur_vars := h.dv_lt (by omega)
  obtain ⟨jpar, hjpar, hjpareq⟩ := h.dv_on_scc (dsp - 2) (by omega)
  have hpar_rng := h.trc_range jpar hjpar; rw [hjpareq] at hpar_rng
  have hedge_pl : activeEdge s0 par lit := by
    have he := h.dv_edges (dsp - 2) (by omega)
    rwa [show dsp - 2 + 1 = dsp - 1 by omega] at he
  obtain ⟨w_lit, hw_lt, hw_scc, hw_tmk, hw_br⟩ := h.trc_witness jlit hjlit
  rw [hjliteq] at hw_tmk hw_br
  rw [← hr_eq] at hw_tmk
  have hw_br_par : BinReach (cnfOfClauses F_cur) par w_lit :=
    binReach_trans (BinReach.step (activeEdge_binEdge hw0 hdm hedge_pl) (BinReach.refl _)) hw_br
  have hlit_ne_dv : ∀ i < dsp - 1, (st.scratch.work_stk2[i]?.getD 0#32).toNat ≠ lit :=
    fun i hi heq => by
      have := h.dv_tmk_mono i (dsp - 1) hi (by omega); dsimp only [lit] at heq; rw [heq] at this
      omega
  have hpar_ne_lit : par ≠ lit := hlit_ne_dv (dsp - 2) (by omega)
  have htrc_le_old : ∀ x, (st'.scratch.tarjan_reach[x]?.getD 0#32).toNat ≤
      (st.scratch.tarjan_reach[x]?.getD 0#32).toNat := fun x => by
    dsimp only [st']; cases upd_par
    · simp only [Bool.false_eq_true, ↓reduceIte]; exact Nat.le_refl _
    · simp only [↓reduceIte]
      by_cases hxp : x = par
      · subst hxp; rw [List.getElem?_set_self (by omega), Option.getD_some]
        exact Nat.le_of_lt (hupT rfl)
      · rw [List.getElem?_set_ne (Ne.symm hxp)]; exact Nat.le_refl _
  have htrc_par_le_r : (st'.scratch.tarjan_reach[par]?.getD 0#32).toNat ≤ rlit.toNat := by
    dsimp only [st']; cases upd_par
    · simp only [Bool.false_eq_true, ↓reduceIte]; exact hupF rfl
    · simp only [↓reduceIte]; rw [List.getElem?_set_self (by omega), Option.getD_some]
      exact Nat.le_refl _
  have htrc_eq_of_ne_par : ∀ x, x ≠ par →
      st'.scratch.tarjan_reach[x]? = st.scratch.tarjan_reach[x]? := fun x hne => by
    dsimp only [st']; cases upd_par
    · simp only [Bool.false_eq_true, ↓reduceIte]
    · simp only [↓reduceIte]; exact List.getElem?_set_ne (Ne.symm hne)
  have hlit_dpos := h.dpos_slice (dsp - 1) (by omega)
  have h0w : fullWatchSizeCore s0.core (lit ^^^ 1) -
      (st.scratch.wsort[dsp - 1]?.getD 0#32).toNat = 0 := by dsimp only [lit]; omega
  obtain ⟨_, _, sc_lit, hseq_lit, hsok_lit⟩ := hlit_dpos
  rw [h0w] at hseq_lit
  rw [show sliceBinsFrom s0.core.wstk _ 0 = [] from rfl, List.append_nil] at hseq_lit
  have hlit_vis : ∀ v, activeEdge s0 lit v → 1 ≤ (st.scratch.tarjan_mark[v]?.getD 0#32).toNat :=
    fun v hv => (hsok_lit v (hseq_lit ▸ hv.2.2) hv.2.1).1
  have hlit_fwd : ∀ v, activeEdge s0 lit v → onScc st v →
      rlit.toNat ≤ (st.scratch.tarjan_reach[v]?.getD 0#32).toNat := fun v hv hvo => by
    have := (hsok_lit v (hseq_lit ▸ hv.2.2) hv.2.1).2.1 hvo (fun h => by omega)
    rwa [← hr_eq] at this
  have hr_ne_ff : rlit ≠ 0xFFFFFFFF#32 := fun heq => by
    have := h.tmk_le lit hlit_lt; have := h.reached_le
    rw [heq] at hr_lt; revert hr_lt; simp; omega
  have hndv_old : ∀ u, u ≠ lit → ¬ onDv st' (dsp - 1) u → ¬ onDv st dsp u :=
    fun u hne hnd ⟨i, hi, heq⟩ => by
      dsimp only [st'] at hnd; split at hnd <;>
        · by_cases hid : i = dsp - 1
          · subst i; exact hne heq.symm
          · exact hnd ⟨i, by omega, heq⟩
  have hst'_l : st'.LengthsOk c := by
    dsimp only [st']; cases upd_par
    · simp only [Bool.false_eq_true, ↓reduceIte]; exact h.len_ok
    · simp only [↓reduceIte]
      exact ⟨h.len_ok.core_ok,
        { h.len_ok.scratch_ok with tarjan_reach_len := by simp [htrc_l] }⟩
  have hag' : AgreesExcept tarjanSccMask s0 st' := by
    dsimp only [st']; cases upd_par
    · simp only [Bool.false_eq_true, ↓reduceIte]; exact h.agrees
    · simp only [↓reduceIte]; exact h.agrees.update _
  have hbase_same : st'.core.tmp_cnt = st.core.tmp_cnt ∧
      st'.scratch.tarjan_mark = st.scratch.tarjan_mark ∧
      st'.scratch.work_stk1 = st.scratch.work_stk1 ∧
      st'.scratch.work_stk2 = st.scratch.work_stk2 ∧
      st'.scratch.wsort = st.scratch.wsort ∧
      st'.core.inconsistent = st.core.inconsistent ∧
      st'.scratch.res_sz = st.scratch.res_sz ∧
      st'.core.repr = st.core.repr ∧
      st'.scratch.shrink_stk = st.scratch.shrink_stk := by
    dsimp only [st']; cases upd_par
    · rw [ite_eq_right Bool.false_ne_true]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · rw [ite_eq_left rfl]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hon_eq : ∀ u, onScc st' u ↔ onScc st u := by
    intro u; simp only [onScc, hbase_same.1, hbase_same.2.2.1]
  refine ⟨{ h with
      agrees := hag', len_ok := hst'_l
      inc0 := by rw [hbase_same.2.2.2.2.2.1]; exact h.inc0
      rsz_le := by rw [hbase_same.2.2.2.2.2.2.1]; exact h.rsz_le
      partial_repr := fun l hl => by
        have hcv' := hag'.get (·.core.cur_vars)
        have hc := congrArg (tarjanSccMask · |>.core) hag'
        have := h.agrees.get (·.core.cur_vars)
        have heqc : st'.core.cur_vars = st.core.cur_vars := by rw [hcv', this]
        have hrpe : st'.core.repr = st.core.repr := hbase_same.2.2.2.2.2.2.2.1
        rw [heqc, hrpe]; exact h.partial_repr l (by rwa [heqc] at hl)
      units_ok := fun i hi => by
        rw [hbase_same.2.2.2.2.2.2.2.2, hag'.get (·.core.cur_vars),
          ← h.agrees.get (·.core.cur_vars)]
        rw [hbase_same.2.2.2.2.2.2.1] at hi; exact h.units_ok i hi
      tmk_le := by simp only [hbase_same.2.1]; exact h.tmk_le
      tmk_inj := by simp only [hbase_same.2.1]; exact h.tmk_inj
      tmk_surj := by simp only [hbase_same.2.1]; exact h.tmk_surj
      tmk_active := by simp only [hbase_same.2.1]; exact h.tmk_active
      top_le := by rw [hbase_same.1]; exact h.top_le
      scc_lt := fun i hi => by
        rw [hbase_same.1] at hi; simp only [hbase_same.2.2.1]; exact h.scc_lt i hi
      scc_tmk_ge := fun i hi => by
        rw [hbase_same.1] at hi; simp only [hbase_same.2.1, hbase_same.2.2.1]
        exact h.scc_tmk_ge i hi
      scc_tmk_mono := fun i j hij hj => by
        rw [hbase_same.1] at hj; simp only [hbase_same.2.1, hbase_same.2.2.1]
        exact h.scc_tmk_mono i j hij hj
      scc_iff_trc := fun l hl => by
        rw [hon_eq, hbase_same.2.1]
        by_cases hlp : l = par
        · subst hlp; have honp : onScc st par := ⟨jpar, hjpar, hjpareq⟩
          constructor
          · intro _; refine ⟨((h.scc_iff_trc par hl).mp honp).1, fun heq => ?_⟩
            dsimp only [st'] at heq; cases upd_par
            · simp only [Bool.false_eq_true, ↓reduceIte] at heq
              exact ((h.scc_iff_trc par hl).mp honp).2 heq
            · simp only [↓reduceIte] at heq
              rw [List.getElem?_set_self (by omega), Option.getD_some] at heq
              exact hr_ne_ff heq
          · intro _; exact honp
        · rw [htrc_eq_of_ne_par l hlp]; exact h.scc_iff_trc l hl
      trc_range := fun i hi => by
        rw [hbase_same.1] at hi; simp only [hbase_same.2.1, hbase_same.2.2.1]
        by_cases hxp : (st.scratch.work_stk1[i]?.getD 0#32).toNat = par
        · rw [hxp]; dsimp only [st']; cases upd_par
          · simp only [Bool.false_eq_true, ↓reduceIte]; rw [← hxp]; exact h.trc_range i hi
          · simp only [↓reduceIte]; rw [List.getElem?_set_self (by omega), Option.getD_some]
            have hup := hupT rfl; dsimp only [par] at hup
            have hpr := hpar_rng.2; dsimp only [par]; exact ⟨hr_ge, by omega⟩
        · rw [htrc_eq_of_ne_par _ hxp]; exact h.trc_range i hi
      trc_witness := fun i hi => by
        rw [hbase_same.1] at hi; simp only [hbase_same.2.1, hbase_same.2.2.1]
        by_cases hxp : (st.scratch.work_stk1[i]?.getD 0#32).toNat = par
        · rw [hxp]; dsimp only [st']; cases upd_par
          · simp only [Bool.false_eq_true, ↓reduceIte]; rw [← hxp]
            obtain ⟨w, h1, h2, h3, h4⟩ := h.trc_witness i hi
            exact ⟨w, h1, (hon_eq w).mpr h2, h3, h4⟩
          · simp only [↓reduceIte]; rw [List.getElem?_set_self (by omega), Option.getD_some]
            exact ⟨w_lit, hw_lt, (hon_eq w_lit).mpr hw_scc, hw_tmk, hw_br_par⟩
        · rw [htrc_eq_of_ne_par _ hxp]; obtain ⟨w, h1, h2, h3, h4⟩ := h.trc_witness i hi
          exact ⟨w, h1, (hon_eq w).mpr h2, h3, h4⟩
      dsp_le := by rw [hbase_same.1]; have := h.dsp_le; omega
      dv_on_scc := fun i hi => by
        rw [hon_eq, hbase_same.2.2.2.1]; exact h.dv_on_scc i (by omega)
      dv_tmk_mono := fun i j hij hj => by
        simp only [hbase_same.2.1, hbase_same.2.2.2.1]; exact h.dv_tmk_mono i j hij (by omega)
      dv0_root := fun _ => by
        simp only [hbase_same.2.1, hbase_same.2.2.1, hbase_same.2.2.2.1]; exact h.dv0_root hdsp
      dv_edges := fun i hi => by
        simp only [hbase_same.2.2.2.1]; exact h.dv_edges i (by omega)
      dpos_slice := fun i hi => by
        simp only [hbase_same.2.1, hbase_same.2.2.2.1, hbase_same.2.2.2.2.1, hon_eq]
        obtain ⟨hle, hslc, sc, hseq, hsok⟩ := h.dpos_slice i (by omega)
        refine ⟨hle, hslc, sc, hseq, fun ot hot haot => ?_⟩
        obtain ⟨h1, h2, h3⟩ := hsok ot hot haot
        refine ⟨h1, fun hsot hne => ?_, fun hbad => ?_⟩
        · by_cases hid2 : i = dsp - 2
          · subst hid2; change (st'.scratch.tarjan_reach[par]?.getD 0#32).toNat ≤ _
            by_cases hotp : ot = par
            · subst hotp; exact Nat.le_refl _
            · rw [htrc_eq_of_ne_par ot hotp]
              by_cases hotl : ot = lit
              · subst hotl; rw [← hr_eq]; exact htrc_par_le_r
              · have := h2 hsot (fun _ he => by
                  dsimp only [lit] at hotl; exact hotl (by
                    rw [show dsp - 2 + 1 = dsp - 1 by omega] at he; exact he))
                exact Nat.le_trans (htrc_le_old par) this
          · have hdv_ne_p : (st.scratch.work_stk2[i]?.getD 0#32).toNat ≠ par := fun he => by
              have := h.dv_tmk_mono i (dsp - 2) (by omega) (by omega)
              dsimp only [par] at he; rw [he] at this; omega
            have hot_ne_p : ot ≠ par := by
              by_cases hid3 : i = dsp - 3
              · subst hid3
                exact fun he => hne (by omega)
                  (by rw [he, show dsp - 3 + 1 = dsp - 2 by omega])
              · have hlt := h.dv_tmk_mono (i + 1) (dsp - 2) (by omega) (by omega)
                rcases h3 (by omega) with rfl | hlt_ot
                · intro he; dsimp only [par] at he; rw [he] at hlt; omega
                · intro he; dsimp only [par] at he; rw [he] at hlt_ot; omega
            rw [htrc_eq_of_ne_par _ hdv_ne_p, htrc_eq_of_ne_par _ hot_ne_p]
            exact h2 hsot (fun _ => hne (by omega))
        · exact h3 (by omega)
      pop_trc_lt := fun u hu hnd => by
        rw [hon_eq] at hu; rw [hbase_same.2.1]
        have hu_ne_par : u ≠ par := fun he => hnd ⟨dsp - 2, by omega, by
          rw [hbase_same.2.2.2.1]; exact he.symm⟩
        rw [htrc_eq_of_ne_par u hu_ne_par]
        by_cases hul : u = lit
        · subst hul; rwa [← hr_eq]
        · exact h.pop_trc_lt u hu (hndv_old u hul hnd)
      pop_edges_vis := fun u v hu hnd huv => by
        rw [hon_eq] at hu; rw [hbase_same.2.1]
        by_cases hul : u = lit
        · subst hul; exact hlit_vis v huv
        · exact h.pop_edges_vis u v hu (hndv_old u hul hnd) huv
      pop_trc_fwd := fun u v hu hnd huv hv htlt => by
        rw [hon_eq] at hu hv; rw [hbase_same.2.1] at htlt
        have hu_ne_par : u ≠ par := fun he => hnd ⟨dsp - 2, by omega, by
          rw [hbase_same.2.2.2.1]; exact he.symm⟩
        rw [htrc_eq_of_ne_par u hu_ne_par]
        by_cases hul : u = lit
        · subst hul
          have hnvp : v ≠ par := fun he => by
            have := h.dv_tmk_mono (dsp - 2) (dsp - 1) (by omega) (by omega)
            rw [he] at htlt; dsimp only [par] at htlt
            try dsimp only [lit] at htlt
            omega
          rw [htrc_eq_of_ne_par v hnvp, ← hr_eq]; exact hlit_fwd v huv hv
        · have hnd0 := hndv_old u hul hnd
          have hnvp : v ≠ par := fun he => by
            have huv' := huv; rw [he] at huv'; dsimp only [par] at huv'
            have := h.pop_dv_order u (dsp - 2) hu hnd0 (by omega) huv'
            rw [he] at htlt; dsimp only [par] at htlt; omega
          rw [htrc_eq_of_ne_par v hnvp]; exact h.pop_trc_fwd u v hu hnd0 huv hv htlt
      pop_dv_order := fun u i hu hnd hi huv => by
        rw [hon_eq] at hu; simp only [hbase_same.2.1, hbase_same.2.2.2.1] at huv ⊢
        by_cases hul : u = lit
        · subst hul; exact h.dv_tmk_mono i (dsp - 1) hi (by omega)
        · exact h.pop_dv_order u i hu (hndv_old u hul hnd) (by omega) huv
      scc_parent_ge := fun j hj d hd hlt => by
        rw [hbase_same.1] at hj
        simp only [hbase_same.2.1, hbase_same.2.2.1, hbase_same.2.2.2.1] at hlt ⊢
        exact h.scc_parent_ge j hj d (by omega) hlt
      mroot_reach := fun _ => by simp only [hbase_same.2.1]; exact h.mroot_reach hdsp }, ?_⟩
  have hcongr : dvWorkSum s0 st' (dsp - 1) = dvWorkSum s0 st (dsp - 1) :=
    dvWorkSum_congr (dsp - 1) fun _ _ => ⟨by rw [hbase_same.2.2.2.1], by rw [hbase_same.2.2.2.2.1]⟩
  unfold M6TarjanDfsInv.measure; rw [dvWorkSum_split (st := st) hdsp, hcongr]; omega

private theorem m6_tarjan_pop_root_after {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st : FullState} {root mroot reached dsp : Nat}
    (h : M6TarjanDfsInv c F0 F_cur s0 root mroot reached dsp st)
    (hdsp : 0 < dsp) {k0 : Nat} {st' : FullState} (hk0_lt : k0 < st.core.tmp_cnt)
    (hk0_eq : (st.scratch.work_stk1[k0]?.getD 0#32).toNat =
      (st.scratch.work_stk2[dsp - 1]?.getD 0#32).toNat)
    (hag_pop : AgreesExcept popSccMask st st') (htop' : st'.core.tmp_cnt = k0)
    (hlen' : st'.LengthsOk c) (hinc0' : st'.core.inconsistent = 0#64)
    (hrsz' : st'.scratch.res_sz.toNat ≤ c.max_vars)
    (hpr' : PartialReprInv F_cur st'.core) (hus' : UnitsSoundInv F_cur st' st'.scratch.res_sz.toNat)
    (hpop_set : ∀ j, k0 ≤ j → j < st.core.tmp_cnt →
      st'.scratch.tarjan_reach[(st.scratch.work_stk1[j]?.getD 0#32).toNat]?.getD 0#32 =
        0xFFFFFFFF#32)
    (hpop_keep : ∀ l < 2 * s0.core.cur_vars,
      (∀ j, k0 ≤ j → j < st.core.tmp_cnt → (st.scratch.work_stk1[j]?.getD 0#32).toNat ≠ l) →
      st'.scratch.tarjan_reach[l]? = st.scratch.tarjan_reach[l]?) :
    M6TarjanDfsInv c F0 F_cur s0 root mroot reached (dsp - 1) st' ∧
    M6TarjanDfsInv.measure c s0 st' reached (dsp - 1) <
      M6TarjanDfsInv.measure c s0 st reached dsp := by
  have htmk_eq := hag_pop.get (·.scratch.tarjan_mark)
  have hscc_eq := hag_pop.get (·.scratch.work_stk1)
  have hdv_eq := hag_pop.get (·.scratch.work_stk2); have hdp_eq := hag_pop.get (·.scratch.wsort)
  have hkeep : ∀ j < k0, st'.scratch.tarjan_reach[(st.scratch.work_stk1[j]?.getD 0#32).toNat]? =
      st.scratch.tarjan_reach[(st.scratch.work_stk1[j]?.getD 0#32).toNat]? := fun j hj =>
    hpop_keep _ (h.scc_lt j (by omega)) fun j2 h1 h2 heq => by
      have := h.scc_tmk_mono j j2 (by omega) h2; rw [heq] at this; omega
  have hdv_k0 : ∀ i < dsp - 1, ∃ j < k0, (st.scratch.work_stk1[j]?.getD 0#32).toNat =
      (st.scratch.work_stk2[i]?.getD 0#32).toNat := fun i hi => by
    obtain ⟨j, hj, hje⟩ := h.dv_on_scc i (by omega)
    have hlt := h.dv_tmk_mono i (dsp - 1) hi (by omega); rw [← hje, ← hk0_eq] at hlt
    exact ⟨j, Classical.byContradiction fun hge => by
      rcases Nat.eq_or_lt_of_le (Nat.le_of_not_gt hge) with rfl | hgt
      · omega
      · have := h.scc_tmk_mono k0 j hgt hj; omega, hje⟩
  have hdsp_le' : dsp - 1 ≤ k0 := Classical.byContradiction fun hgt => by
    let idx : Nat → Nat := fun i => if hi : i < dsp - 1 then (hdv_k0 i hi).choose else 0
    have hinj : ∀ a b, a < dsp - 1 → b < dsp - 1 → idx a = idx b → a = b := fun a b ha hb heq => by
      have ha_s := (hdv_k0 a ha).choose_spec.2; have hb_s := (hdv_k0 b hb).choose_spec.2
      simp only [idx, ha, hb, ↓reduceDIte] at heq; rw [heq] at ha_s
      have hdv_ab : (st.scratch.work_stk2[a]?.getD 0#32).toNat =
          (st.scratch.work_stk2[b]?.getD 0#32).toNat := by rw [← ha_s, hb_s]
      exact Classical.byContradiction fun hne => by
        rcases Nat.lt_or_gt_of_ne hne with hlt | hgt'
        · have h1 := h.dv_tmk_mono a b hlt (by omega); rw [hdv_ab] at h1; omega
        · have h1 := h.dv_tmk_mono b a hgt' (by omega); rw [hdv_ab] at h1; omega
    have hlt_k0 := inj_lt_of_missing (k := dsp - 1) (n := k0 + 1) (v := k0) idx hinj
      (fun i hi => by simp only [idx, hi, ↓reduceDIte]; have := (hdv_k0 i hi).choose_spec.1; omega)
      (by omega) (fun i hi heq => by
        simp only [idx, hi, ↓reduceDIte] at heq; have := (hdv_k0 i hi).choose_spec.1; omega)
    omega
  have hon_sub : ∀ u, onScc st' u → onScc st u :=
    fun _ ⟨j, hj, hje⟩ => ⟨j, by rw [htop'] at hj; omega, by rw [hscc_eq] at hje; exact hje⟩
  have hndv_sub : ∀ u, onScc st' u → ¬ onDv st' (dsp - 1) u → ¬ onDv st dsp u :=
    fun u ⟨j, hj, hje⟩ hnd ⟨i, hi, hie⟩ => by
      rw [htop'] at hj; rw [hscc_eq] at hje; by_cases hid : i = dsp - 1
      · subst i; have := h.scc_tmk_mono j k0 hj hk0_lt; rw [hje, hk0_eq, ← hie] at this; omega
      · exact hnd ⟨i, by omega, by rw [hdv_eq]; exact hie⟩
  refine ⟨{
      agrees := agrees_popScc_to_tarjan h.agrees hag_pop, len_ok := hlen', inc0 := hinc0'
      rsz_le := hrsz', partial_repr := hpr', units_ok := hus', reached_le := h.reached_le
      tmk_le := by simp only [htmk_eq]; exact h.tmk_le
      tmk_inj := by simp only [htmk_eq]; exact h.tmk_inj
      tmk_surj := by simp only [htmk_eq]; exact h.tmk_surj
      tmk_active := by simp only [htmk_eq]; exact h.tmk_active
      top_le := by rw [htop']; have := h.top_le; omega
      scc_lt := fun i hi => by rw [htop'] at hi; simp only [hscc_eq]; exact h.scc_lt i (by omega)
      scc_tmk_ge := fun i hi => by
        rw [htop'] at hi; simp only [htmk_eq, hscc_eq]; exact h.scc_tmk_ge i (by omega)
      scc_tmk_mono := fun i j hij hj => by
        rw [htop'] at hj; simp only [htmk_eq, hscc_eq]; exact h.scc_tmk_mono i j hij (by omega)
      scc_iff_trc := fun l hl => by
        simp only [htmk_eq]; constructor
        · rintro ⟨j, hj, hje⟩; rw [htop'] at hj; simp only [hscc_eq] at hje
          have hk := hkeep j hj; rw [hje] at hk; rw [hk]
          exact (h.scc_iff_trc l hl).mp ⟨j, by omega, hje⟩
        · rintro ⟨hpos, hne⟩
          by_cases hin : ∃ j, k0 ≤ j ∧ j < st.core.tmp_cnt ∧
              (st.scratch.work_stk1[j]?.getD 0#32).toNat = l
          · obtain ⟨j, h1, h2, hje⟩ := hin; exact absurd (hje ▸ hpop_set j h1 h2) hne
          · rw [hpop_keep l hl fun j h1 h2 heq => hin ⟨j, h1, h2, heq⟩] at hne
            obtain ⟨j, hj, hje⟩ := (h.scc_iff_trc l hl).mpr ⟨hpos, hne⟩
            have hjlt : j < k0 := Classical.byContradiction fun hge => hin ⟨j, by omega, hj, hje⟩
            exact ⟨j, by rw [htop']; exact hjlt, by simp only [hscc_eq]; exact hje⟩
      trc_range := fun i hi => by
        rw [htop'] at hi; simp only [htmk_eq, hscc_eq]; rw [hkeep i hi]
        exact h.trc_range i (by omega)
      trc_witness := fun i hi => by
        rw [htop'] at hi; simp only [hscc_eq]; rw [hkeep i hi]
        obtain ⟨_, hw_lt, ⟨jw, hjw, rfl⟩, htw, hbr⟩ := h.trc_witness i (by omega)
        have hjw_lt : jw < k0 := Classical.byContradiction fun hge => by
          have := (h.trc_range i (by omega)).2; have := h.scc_tmk_mono i k0 hi hk0_lt
          rcases Nat.eq_or_lt_of_le (Nat.le_of_not_gt hge) with rfl | hgt
          · omega
          · have := h.scc_tmk_mono k0 jw hgt hjw; omega
        exact ⟨_, hw_lt, ⟨jw, by rw [htop']; exact hjw_lt, by simp only [hscc_eq]⟩,
          by simp only [htmk_eq]; exact htw, hbr⟩
      dsp_le := by rw [htop']; exact hdsp_le'
      dv_on_scc := fun i hi => let ⟨j, hj, hje⟩ := hdv_k0 i hi
        ⟨j, by rw [htop']; exact hj, by simp only [hscc_eq, hdv_eq]; exact hje⟩
      dv_tmk_mono := fun i j hij hj => by
        simp only [htmk_eq, hdv_eq]; exact h.dv_tmk_mono i j hij (by omega)
      dv0_root := fun _ => by simp only [htmk_eq, hscc_eq, hdv_eq]; exact h.dv0_root hdsp
      dv_edges := fun i hi => by simp only [hdv_eq]; exact h.dv_edges i (by omega)
      dpos_slice := fun i hi => by
        simp only [htmk_eq, hdv_eq, hdp_eq]
        obtain ⟨hle, hslc, sc, hseq, hsok⟩ := h.dpos_slice i (by omega)
        refine ⟨hle, hslc, sc, hseq, fun ot hot haot => ?_⟩
        obtain ⟨h1, h2, h3⟩ := hsok ot hot haot
        refine ⟨h1, fun hsot hne => ?_, fun hi' => h3 (by omega)⟩
        obtain ⟨j_i, hj_i, hjeq_i⟩ := hdv_k0 i hi
        obtain ⟨j_ot, hj_ot, hjeq_ot⟩ := hsot; rw [htop'] at hj_ot; simp only [hscc_eq] at hjeq_ot
        rw [← hjeq_i, hkeep j_i hj_i, ← hjeq_ot, hkeep j_ot hj_ot, hjeq_i, hjeq_ot]
        exact h2 (hon_sub ot ⟨j_ot, by rw [htop']; exact hj_ot,
          by simp only [hscc_eq]; exact hjeq_ot⟩) (fun _ heq => by
            by_cases hi1 : i + 1 < dsp - 1
            · exact hne hi1 heq
            · have hlt_m := h.scc_tmk_mono j_ot k0 hj_ot hk0_lt
              rw [show i + 1 = dsp - 1 by omega] at heq
              rw [hjeq_ot, hk0_eq, ← heq] at hlt_m; omega)
      pop_trc_lt := fun u hu hnd => by
        obtain ⟨j, hj, hje⟩ := hu; rw [htop'] at hj; simp only [hscc_eq] at hje
        simp only [htmk_eq]; rw [← hje, hkeep j hj, hje]
        exact h.pop_trc_lt u ⟨j, by omega, hje⟩ (hndv_sub u ⟨j, by rw [htop']; exact hj,
          by simp only [hscc_eq]; exact hje⟩ hnd)
      pop_edges_vis := fun u v hu hnd huv => by
        simp only [htmk_eq]; exact h.pop_edges_vis u v (hon_sub u hu) (hndv_sub u hu hnd) huv
      pop_trc_fwd := fun u v hu hnd huv hv htlt => by
        obtain ⟨ju, hju, hjue⟩ := hu; rw [htop'] at hju; simp only [hscc_eq] at hjue
        obtain ⟨jv, hjv, hjve⟩ := hv; rw [htop'] at hjv; simp only [hscc_eq] at hjve
        simp only [htmk_eq] at htlt; rw [← hjue, hkeep ju hju, ← hjve, hkeep jv hjv, hjue, hjve]
        exact h.pop_trc_fwd u v ⟨ju, by omega, hjue⟩
          (hndv_sub u ⟨ju, by rw [htop']; exact hju, by simp only [hscc_eq]; exact hjue⟩ hnd)
          huv ⟨jv, by omega, hjve⟩ htlt
      pop_dv_order := fun u i hu hnd hi huv => by
        simp only [htmk_eq, hdv_eq] at huv ⊢
        exact h.pop_dv_order u i (hon_sub u hu) (hndv_sub u hu hnd) (by omega) huv
      scc_parent_ge := fun j hj d hd hlt => by
        rw [htop'] at hj; simp only [htmk_eq, hscc_eq, hdv_eq] at hlt ⊢
        exact h.scc_parent_ge j (by omega) d (by omega) hlt
      mroot_reach := fun _ => by simp only [htmk_eq]; exact h.mroot_reach hdsp }, ?_⟩
  have hcongr : dvWorkSum s0 st' (dsp - 1) = dvWorkSum s0 st (dsp - 1) :=
    dvWorkSum_congr (dsp - 1) fun _ _ => by simp [hdv_eq, hdp_eq]
  unfold M6TarjanDfsInv.measure; rw [dvWorkSum_split (st := st) hdsp, hcongr]; omega

private theorem dpos_step_nonbin {F_cur : List (List Nat)} {s0 st : FullState}
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

private theorem dpos_step_bin {F_cur : List (List Nat)} {s0 st : FullState}
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

end M6TarjanTransitions

private theorem m6_bv64_add_toNat {x y : BitVec 64} (h : x.toNat + y.toNat < 2 ^ 64) :
    (x + y).toNat = x.toNat + y.toNat := by rw [BitVec.toNat_add, Nat.mod_eq_of_lt h]
private theorem m6_bv64_add1_toNat {x : BitVec 64} (h : x.toNat + 1 < 2 ^ 64) :
    (x + 1#64).toNat = x.toNat + 1 :=
  (m6_bv64_add_toNat (y := 1#64) (by simpa using h)).trans (by simp)
private theorem m6_bv32_add1_toNat {x : BitVec 32} (h : x.toNat + 1 < 2 ^ 32) :
    (x + 1#32).toNat = x.toNat + 1 := by
  rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl, Nat.mod_eq_of_lt h]
private theorem m6_bv32_add2_toNat {x : BitVec 32} (h : x.toNat + 2 < 2 ^ 32) :
    (x + 2#32).toNat = x.toNat + 2 := by
  rw [BitVec.toNat_add, show (2#32 : BitVec 32).toNat = 2 from rfl, Nat.mod_eq_of_lt h]
private theorem m6_bv_ult_false_ge {w : Nat} {x y : BitVec w} (h : x.ult y = false) :
    y.toNat ≤ x.toNat :=
  Nat.le_of_not_lt fun hlt => by
    have := BitVec.ult_iff_lt.mpr (BitVec.lt_def.mpr hlt); rw [this] at h; cases h

private theorem m6_tarjan_pop_scc_call_wp {Γ : Env} {Q : Post [i64]} {X : XPost}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s0 st3 : FullState}
    {R : Mem 64 → Prop} {m3 : Mem 64} {root dsp : BitVec 64} {reached rch lit mr : BitVec 32}
    {failb : Bool} {k0 : Nat} {Jpop : Cont [.bool]}
    (hPop : ∀ args m Q X, Full.fullTarjanPopSccSpec args m Q X →
      Γ "full_tarjan_pop_scc" [i64, i32, i32, i32] [.bool] args m Q X)
    (hw0 : FullWitnessInv c F0 F_cur s0.core) (hinc30 : st3.core.inconsistent = 0#64)
    (hdsp_pos : 0 < dsp.toNat) (hrt_lt : root.toNat < 2 * s0.core.cur_vars)
    (hlit_lt : lit.toNat < 2 * s0.core.cur_vars)
    (hd3 : M6TarjanDfsInv c F0 F_cur s0 root.toNat (reached.toNat + 1) rch.toNat dsp.toNat st3)
    (hlit_get : lit = st3.scratch.work_stk2[dsp.toNat - 1]?.getD 0#32)
    (hk0_lt : k0 < st3.core.tmp_cnt)
    (hk0_bv : st3.scratch.work_stk1[k0]?.getD 0#32 =
      st3.scratch.work_stk2[dsp.toNat - 1]?.getD 0#32)
    (hk0_uniq : ∀ j, k0 < j → j < st3.core.tmp_cnt →
      st3.scratch.work_stk1[j]?.getD 0#32 ≠ st3.scratch.work_stk2[dsp.toNat - 1]?.getD 0#32)
    (hk0_zero : dsp.toNat = 1 → k0 = 0)
    (hk0_eqv : ∀ j, k0 ≤ j → j < st3.core.tmp_cnt →
      LitEquiv (cnfOfClauses F_cur) (st3.scratch.work_stk1[j]?.getD 0#32).toNat
        (st3.scratch.work_stk2[dsp.toNat - 1]?.getD 0#32).toNat)
    (hmr_reach : mr ≠ 0xFFFFFFFF#32 →
      (∀ j, k0 ≤ j → j < st3.core.tmp_cnt → BinReach (cnfOfClauses F_cur)
        (BitVec.setWidth 32 root).toNat (st3.scratch.work_stk1[j]?.getD 0#32).toNat) ∧
      (∀ l < 2 * st3.core.cur_vars,
        mr.toNat ≤ (st3.scratch.tarjan_mark[l]?.getD 0#32).toNat →
        BinReach (cnfOfClauses F_cur) (BitVec.setWidth 32 root).toNat l))
    (hm3 : (FullMem c st3 ⋆ R) m3)
    (hPopJ : ∀ (b : Bool) mj, (∃ st4 : FullState, TarjanLoopBase c F_cur s0 st4 ∧
      (st4.core.inconsistent = 0#64 →
        M6TarjanDfsInv c F0 F_cur s0 root.toNat (reached.toNat + 1) rch.toNat (dsp.toNat - 1) st4 ∧
        M6TarjanDfsInv.measure c s0 st4 rch.toNat (dsp.toNat - 1) <
          M6TarjanDfsInv.measure c s0 st3 rch.toNat dsp.toNat ∧
        (dsp.toNat - 1 = 0 → st4.core.tmp_cnt = 0)) ∧ (FullMem c st4 ⋆ R) mj) →
      Jpop (b, ()) mj) :
    wp Γ Q X (Expr.call (as := [i64, i32, i32, i32]) (bs := [.bool]) "full_tarjan_pop_scc"
      (Arg.var c.hdr, Arg.var (BitVec.setWidth 32 root), Arg.var lit, Arg.var mr, ()) fun p =>
        Expr.jnz (Arg.var p.fst)
          (Expr.jump Jpop (Arg.imm true, ())) (Expr.jump Jpop (Arg.var failb, ()))) m3 := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv3 := hd3.agrees.get (·.core.cur_vars); have hcv_le := hd3.len_ok.core_ok.cur_vars_le
  have hk0_nat : (st3.scratch.work_stk1[k0]?.getD 0#32).toNat = lit.toNat := by
    rw [hk0_bv, ← hlit_get]
  scc_call hPop
  refine ⟨c, F0, F_cur, st3, k0, R, rfl, hd3.len_ok,
    tarjanScc_preserves_witness hw0 hd3.agrees (fun h => absurd hinc30 h), hinc30,
    by rw [bv32_trunc_toNat (by omega), hcv3]; exact hrt_lt, by rw [hcv3]; exact hlit_lt,
    by have := hd3.top_le; have := hd3.reached_le; rw [hcv3]; omega, hd3.rsz_le, hk0_lt,
    by rw [hk0_bv, ← hlit_get], fun j h1 h2 => by rw [hlit_get]; exact hk0_uniq j h1 h2,
    fun j hj => by rw [hcv3]; exact hd3.scc_lt j hj,
    fun j h1 h2 => by rw [hlit_get]; exact hk0_eqv j h1 h2,
    hd3.partial_repr, hd3.units_ok, hmr_reach, hm3, ?_⟩
  intro _ st4 m4 hag_p htop4 hlen4 _ hrsz4 hpr4 hus4 _ hinc4_u hinc4_eff hm4
  have hbase4 : TarjanLoopBase c F_cur s0 st4 :=
    ⟨agrees_popScc_to_tarjan hd3.agrees hag_p, hlen4, hrsz4, hpr4, hus4, hinc4_u⟩
  have hd4_fn : st4.core.inconsistent = 0#64 →
      M6TarjanDfsInv c F0 F_cur s0 root.toNat (reached.toNat + 1) rch.toNat (dsp.toNat - 1) st4 ∧
      M6TarjanDfsInv.measure c s0 st4 rch.toNat (dsp.toNat - 1) <
        M6TarjanDfsInv.measure c s0 st3 rch.toNat dsp.toNat ∧
      (dsp.toNat - 1 = 0 → st4.core.tmp_cnt = 0) := fun h40 => by
    obtain ⟨hset, hkeep⟩ := hinc4_eff h40
    obtain ⟨hd4, hm4_lt⟩ := m6_tarjan_pop_root_after hd3 hdsp_pos hk0_lt
      (by rw [hk0_nat, ← hlit_get]) hag_p htop4 hlen4 h40 hrsz4 hpr4 hus4
      (fun j h1 h2 => (hset j h1 h2).2) (fun l hl hall => (hkeep l (by omega) hall).2)
    exact ⟨hd4, hm4_lt, fun hz => by rw [htop4]; exact hk0_zero (by omega)⟩
  scc_steps
  · exact hPopJ true m4 ⟨st4, hbase4, hd4_fn, hm4⟩
  · exact hPopJ failb m4 ⟨st4, hbase4, hd4_fn, hm4⟩

private theorem xor1_xor1 (n : Nat) : (n ^^^ 1) ^^^ 1 = n := litNeg_litNeg n

private theorem m6_tarjan_empty_dfs_inv {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st : FullState} (hsp0 : Full.FullSparseInvW c F0 F_cur s0)
    (hag : AgreesExcept tarjanSccMask s0 st) (hlen : st.LengthsOk c)
    (hinc_st : st.core.inconsistent = s0.core.inconsistent)
    (hinit : ∀ l < 2 * s0.core.cur_vars,
      st.core.repr[l]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 ∧
      (st.scratch.tarjan_mark[l]?.getD 0#32).toNat = 0 ∧
      (st.scratch.tarjan_reach[l]?.getD 0#32).toNat = 0) :
    let st1 : FullState := { st with core := { st.core with tmp_cnt := 0 }
                                     scratch := { st.scratch with res_sz := 0#64 } }
    TarjanLoopBase c F_cur s0 st1 ∧
    (st1.core.inconsistent = 0#64 →
      st1.core.tmp_cnt = 0 ∧ M6TarjanDfsInv c F0 F_cur s0 0 1 0 0 st1) := by
  intro st1
  have hw0 := hsp0.2.1; have hcv_le := hlen.core_ok.cur_vars_le
  have hag1 : AgreesExcept tarjanSccMask s0 st1 := hag.update _
  have hlen1 : st1.LengthsOk c :=
    ⟨{ hlen.core_ok with vals_len := hlen.core_ok.vals_len },
     { hlen.scratch_ok with work_stk1_len := hlen.scratch_ok.work_stk1_len }⟩
  have hpr1 : PartialReprInv F_cur st1.core := fun l hl hne => by
    rw [hag1.get (·.core.cur_vars)] at hl; exact absurd (hinit l (by omega)).1 hne
  have hinc_u1 : st1.core.inconsistent ≠ 0#64 → (cnfOfClauses F_cur).Unsat := fun hne => by
    change st.core.inconsistent ≠ 0#64 at hne; rw [hinc_st] at hne
    exact hw0.inconsistent_sound hne
  refine ⟨⟨hag1, hlen1, by simp [st1], hpr1, fun _ h => by simp [st1] at h, hinc_u1⟩, fun h0 =>
    ⟨rfl, {
      agrees := hag1, len_ok := hlen1, inc0 := h0, rsz_le := by simp [st1]
      partial_repr := hpr1, units_ok := fun _ h => by simp [st1] at h
      reached_le := Nat.zero_le _, top_le := by dsimp only [st1]; omega
      tmk_le := fun l hl => by dsimp only [st1]; rw [(hinit l (by omega)).2.1]; omega
      tmk_inj := fun a _ ha _ hp => by
        dsimp only [st1] at hp; rw [(hinit a (by omega)).2.1] at hp; omega
      tmk_surj := fun _ h1 h2 => by simp at h2; omega
      tmk_active := fun l hl hp => by
        dsimp only [st1] at hp; rw [(hinit l (by omega)).2.1] at hp; omega
      scc_lt := fun _ h => by dsimp only [st1] at h; omega
      scc_tmk_ge := fun _ h => by dsimp only [st1] at h; omega
      scc_tmk_mono := fun _ _ _ h => by dsimp only [st1] at h; omega
      scc_iff_trc := fun l hl => ⟨fun ⟨_, h, _⟩ => by dsimp only [st1] at h; omega,
        fun ⟨hp, _⟩ => by dsimp only [st1] at hp; rw [(hinit l (by omega)).2.1] at hp; omega⟩
      trc_range := fun _ h => by dsimp only [st1] at h; omega
      trc_witness := fun _ h => by dsimp only [st1] at h; omega
      dsp_le := by omega, dv_on_scc := by omega, dv_tmk_mono := by omega, dv0_root := by omega
      dv_edges := by omega, dpos_slice := by omega, scc_parent_ge := by omega
      mroot_reach := by omega
      pop_trc_lt := fun _ ⟨_, h, _⟩ => by dsimp only [st1] at h; omega
      pop_edges_vis := fun _ _ ⟨_, h, _⟩ => by dsimp only [st1] at h; omega
      pop_trc_fwd := fun _ _ ⟨_, h, _⟩ => by dsimp only [st1] at h; omega
      pop_dv_order := fun _ _ ⟨_, h, _⟩ => by dsimp only [st1] at h; omega }⟩⟩

private theorem m6_tarjan_fill_finish {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 stf st4 : FullState} (hsp0 : Full.FullSparseInvW c F0 F_cur s0)
    (hagf : AgreesExcept tarjanSccMask s0 stf)
    (husf : ∀ k < stf.scratch.res_sz.toNat,
      (stf.scratch.shrink_stk[k]?.getD 0#32).toNat < 2 * stf.core.cur_vars ∧
      (cnfOfClauses F_cur).EntailsClause
        (cnfClause [(stf.scratch.shrink_stk[k]?.getD 0#32).toNat]))
    (hag4 : AgreesExcept tarjanSccMask s0 st4) (hlen4 : st4.LengthsOk c)
    (hinc4 : st4.core.inconsistent = stf.core.inconsistent)
    (hrsz4 : st4.scratch.res_sz = stf.scratch.res_sz)
    (hsh4 : st4.scratch.shrink_stk = stf.scratch.shrink_stk)
    (hincf : stf.core.inconsistent ≠ 0#64 → (cnfOfClauses F_cur).Unsat)
    (hpr4 : PartialReprInv F_cur st4.core)
    (hfill4 : ∀ l < 2 * s0.core.cur_vars,
      st4.core.repr[l]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 ∧
      st4.scratch.tarjan_mark[l]?.getD 0#32 = 0#32 ∧
      st4.scratch.tarjan_reach[l]?.getD 0#32 = 0#32) :
    Full.FullSparseInvW c F0 F_cur st4 ∧
    (∀ (_ : Nat), Full.FullReprEquiv F_cur st4) ∧
    (∀ k < st4.scratch.res_sz.toNat,
      (st4.scratch.shrink_stk[k]?.getD 0#32).toNat < 2 * s0.core.cur_vars ∧
      (cnfOfClauses F_cur).EntailsClause
        (cnfClause [(st4.scratch.shrink_stk[k]?.getD 0#32).toNat])) ∧
    (∀ l < 2 * s0.core.cur_vars,
      st4.scratch.tarjan_mark[l]?.getD 0#32 = 0#32 ∧
      st4.scratch.tarjan_reach[l]?.getD 0#32 = 0#32) ∧
    TmkZero st4 := by
  have hrp4 := hlen4.core_ok.repr_len; have hcv4 := hag4.get (·.core.cur_vars)
  have hcv0_le := hsp0.1.core_ok.cur_vars_le
  have hsp4 := tarjanScc_preserves_sparse hsp0 hag4 hlen4 (fun h => hincf (hinc4 ▸ h))
  have hrepr4 : Full.FullReprEquiv F_cur st4 := fun l hl => by
    have hget : st4.core.repr[l]?.getD 0#32 = st4.core.repr[l]?.getD 0xFFFFFFFF#32 := by
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some, Option.getD_some]
    obtain ⟨hr_lt, h1, h2⟩ := hpr4 l hl (hfill4 l (by omega)).1
    rw [hget]; exact ⟨hr_lt, h2, h1⟩
  have hus4 : ∀ k < st4.scratch.res_sz.toNat,
      (st4.scratch.shrink_stk[k]?.getD 0#32).toNat < 2 * s0.core.cur_vars ∧
      (cnfOfClauses F_cur).EntailsClause
        (cnfClause [(st4.scratch.shrink_stk[k]?.getD 0#32).toNat]) := fun k hk => by
    rw [hrsz4] at hk; rw [hsh4]; have := husf k hk
    rwa [hagf.get (·.core.cur_vars)] at this
  have htmk_z4 : ∀ l < 2 * s0.core.cur_vars,
      st4.scratch.tarjan_mark[l]?.getD 0#32 = 0#32 ∧
      st4.scratch.tarjan_reach[l]?.getD 0#32 = 0#32 := fun l hl => (hfill4 l (by omega)).2
  have htmk_zero4 : TmkZero st4 := fun v hv => by
    rw [hag4.get (·.core.cur_vars)] at hv; exact (htmk_z4 v (by omega)).1
  exact ⟨hsp4, fun _ => hrepr4, hus4, htmk_z4, htmk_zero4⟩

theorem full_tarjan_scc_fast_wp (Γ : Env)
    (hPop : ∀ args m Q X, Full.fullTarjanPopSccSpec args m Q X →
      Γ "full_tarjan_pop_scc" [i64, i32, i32, i32] [.bool] args m Q X) :
    ∀ args m Q X, fullTarjanSccFastSpec args m Q X →
      Func.wp Γ full_tarjan_scc_body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s0, R, rfl, hsp0, _, hm, hQ⟩
  have hmx := c.hmaxv; have hwc := c.hwcap; unfold dimacsBound at hmx hwc
  have hlen0 := hsp0.1; have hw0 := hsp0.2.1; have hdm0 := hsp0.2.2.2.2.2
  have hcl0 := hlen0.core_ok; have hcv_le := hcl0.cur_vars_le
  have hwat0 : WatchesInv F_cur s0.core := by
    have hmw := hw0.watches; unfold ModeWatchesInv at hmw; rwa [ite_eq_left hdm0] at hmw
  have hnl_eq : (BitVec.ofNat 64 s0.core.cur_vars <<< (1 : Nat)).toNat = 2 * s0.core.cur_vars := by
    rw [FullArenaTactics.bv64_shl1_nat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : s0.core.cur_vars < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]
  scc_to_group
  refine wp_loop_inv
    (fun (i, ()) ml => ∃ st : FullState,
      AgreesExcept tarjanSccMask s0 st ∧ st.LengthsOk c ∧
      st.core.inconsistent = s0.core.inconsistent ∧ i.toNat ≤ 2 * s0.core.cur_vars ∧
      (∀ l < i.toNat, st.core.repr[l]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 ∧
        (st.scratch.tarjan_mark[l]?.getD 0#32).toNat = 0 ∧
        (st.scratch.tarjan_reach[l]?.getD 0#32).toNat = 0) ∧ (FullMem c st ⋆ R) ml)
    (fun (i, ()) _ => 2 * s0.core.cur_vars - i.toNat) ?_ ?_
  · intro J hJ; scc_steps
    exact hJ (0#64, ()) m ⟨s0, AgreesExcept.refl _ _, hlen0, rfl, Nat.zero_le _,
      fun _ h => by simp at h, hm⟩
  rintro J ⟨i, ⟨⟩⟩ ml ⟨st, hag, hlen, hinc_st, hi_le, hinit, hml⟩ hJ
  have hrp_l := hlen.core_ok.repr_len; have htmk_l := hlen.scratch_ok.tarjan_mark_len
  have htrc_l := hlen.scratch_ok.tarjan_reach_len
  scc_split
  · have hi_lt : i.toNat < 2 * s0.core.cur_vars := by
      have := BitVec.lt_def.mp (BitVec.ult_iff_lt.mp hc); rwa [hnl_eq] at this
    have hi1 : (i + 1#64).toNat = i.toNat + 1 := m6_bv64_add1_toNat (by omega)
    scc_steps
    let st1 : FullState :=
      { st with core := { st.core with repr := st.core.repr.set i.toNat 0xFFFFFFFF#32 }
                scratch := { st.scratch with
                  tarjan_mark := st.scratch.tarjan_mark.set i.toNat 0#32
                  tarjan_reach := st.scratch.tarjan_reach.set i.toNat 0#32 } }
    refine hJ (i + 1#64, ()) _ (by dsimp only; omega) ⟨st1, hag.update _,
      ⟨{ hlen.core_ok with repr_len := by dsimp only [st1]; rw [List.length_set, hrp_l] },
       { hlen.scratch_ok with
         tarjan_mark_len := by dsimp only [st1]; rw [List.length_set, htmk_l]
         tarjan_reach_len := by dsimp only [st1]; rw [List.length_set, htrc_l] }⟩,
      hinc_st, by omega, fun l hl => ?_, hm⟩
    by_cases hli : l = i.toNat
    · subst hli; dsimp only [st1]
      rw [List.getElem?_set_self (by omega), List.getElem?_set_self (by omega),
        List.getElem?_set_self (by omega)]; exact ⟨rfl, rfl, rfl⟩
    · dsimp only [st1]; rw [List.getElem?_set_ne (Ne.symm hli), List.getElem?_set_ne (Ne.symm hli),
        List.getElem?_set_ne (Ne.symm hli)]; exact hinit l (by omega)
  have hi_eq : i.toNat = 2 * s0.core.cur_vars := by have := m6_bv_ult_false_ge hc; omega
  scc_to_group
  refine wp_loop_inv
    (fun (reached, root, ()) ml => ∃ st : FullState,
      root.toNat ≤ 2 * s0.core.cur_vars ∧ TarjanLoopBase c F_cur s0 st ∧
      (st.core.inconsistent = 0#64 →
        st.core.tmp_cnt = 0 ∧ M6TarjanDfsInv c F0 F_cur s0 0 1 reached.toNat 0 st) ∧
      (FullMem c st ⋆ R) ml)
    (fun (_, root, ()) _ => 2 * s0.core.cur_vars - root.toNat) ?_ ?_
  · intro J2 hJ2; scc_steps
    have he := m6_tarjan_empty_dfs_inv hsp0 hag hlen hinc_st (fun l hl => hinit l (by omega))
    exact hJ2 (0#32, 0#64, ()) _ ⟨_, Nat.zero_le _, he.1, he.2, hm⟩
  rintro J2 ⟨reached, root, ⟨⟩⟩ ml ⟨st, hrt_le, hbase, hinc_dfs, hml⟩ hJ2
  clear hJ hinit hi_le hi_eq hinc_st hrp_l htmk_l htrc_l hag hlen
  obtain ⟨hag, hlen, hrsz, hpr, hus, hinc_u⟩ := hbase
  have hfl_l := hlen.core_ok.flags_len; have htmk_l := hlen.scratch_ok.tarjan_mark_len
  have htrc_l := hlen.scratch_ok.tarjan_reach_len; have hscc_l := hlen.scratch_ok.work_stk1_len
  have hdv_l := hlen.scratch_ok.work_stk2_len; have hdp_l := hlen.scratch_ok.wsort_len
  scc_to_group
  refine wp_join_group (ts := [])
    (fun () mj => ∃ st' : FullState, TarjanLoopBase c F_cur s0 st' ∧ (FullMem c st' ⋆ R) mj) ?_ ?_
  · rintro _ ⟨⟩ mj ⟨stf, ⟨hagf, hlenf, hrszf, hprf, husf, hincf⟩, hmj⟩
    scc_to_group
    refine wp_loop_inv
      (fun (idx, ()) mk => ∃ st4 : FullState,
        AgreesExcept tarjanSccMask s0 st4 ∧ st4.LengthsOk c ∧
        st4.core.inconsistent = stf.core.inconsistent ∧ st4.scratch.res_sz = stf.scratch.res_sz ∧
        st4.scratch.shrink_stk = stf.scratch.shrink_stk ∧ idx.toNat ≤ 2 * s0.core.cur_vars ∧
        PartialReprInv F_cur st4.core ∧
        (∀ l < idx.toNat, st4.core.repr[l]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 ∧
          st4.scratch.tarjan_mark[l]?.getD 0#32 = 0#32 ∧
          st4.scratch.tarjan_reach[l]?.getD 0#32 = 0#32) ∧
        (FullMem c st4 ⋆ R) mk)
      (fun (idx, ()) _ => 2 * s0.core.cur_vars - idx.toNat) ?_ ?_
    · intro J4 hJ4; scc_steps
      exact hJ4 (0#64, ()) mj ⟨stf, hagf, hlenf, rfl, rfl, rfl, Nat.zero_le _, hprf,
        fun _ h => by simp at h, hmj⟩
    rintro J4 ⟨idx, ⟨⟩⟩ mk ⟨st4, hag4, hlen4, hinc4, hrsz4, hsh4, hidx_le, hpr4, hfill4, hmk⟩ hJ4
    have hrp4 := hlen4.core_ok.repr_len; have hcv4 := hag4.get (·.core.cur_vars)
    have htmk4 := hlen4.scratch_ok.tarjan_mark_len; have htrc4 := hlen4.scratch_ok.tarjan_reach_len
    scc_split
    · have hidx_lt : idx.toNat < 2 * s0.core.cur_vars := by
        have := BitVec.lt_def.mp (BitVec.ult_iff_lt.mp hc); rwa [hnl_eq] at this
      have hidx1 : (idx + 1#64).toNat = idx.toNat + 1 := m6_bv64_add1_toNat (by omega)
      have hidx_lt32 : idx.toNat < 2 ^ 32 := by omega
      scc_to_group
      refine wp_join_group (ts := [])
        (fun () m4a => ∃ st5 : FullState,
          AgreesExcept tarjanSccMask s0 st5 ∧ st5.LengthsOk c ∧
          st5.core.inconsistent = stf.core.inconsistent ∧ st5.scratch.res_sz = stf.scratch.res_sz ∧
          st5.scratch.shrink_stk = stf.scratch.shrink_stk ∧
          st5.scratch.tarjan_mark = st4.scratch.tarjan_mark ∧
          st5.scratch.tarjan_reach = st4.scratch.tarjan_reach ∧
          PartialReprInv F_cur st5.core ∧
          st5.core.repr[idx.toNat]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 ∧
          (∀ l < idx.toNat, st5.core.repr[l]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32) ∧
          (FullMem c st5 ⋆ R) m4a) ?_ ?_
      · rintro _ ⟨⟩ m4a ⟨st5, hag5, hlen5, hinc5, hrsz5, hsh5, htmk_eq5, htrc_eq5,
            hpr5, hfill_i, hfill_prev, hm4a⟩
        have htmk5 := hlen5.scratch_ok.tarjan_mark_len
        have htrc5 := hlen5.scratch_ok.tarjan_reach_len
        scc_steps
        let st6 : FullState := { st5 with scratch := { st5.scratch with
          tarjan_mark := st5.scratch.tarjan_mark.set idx.toNat 0#32
          tarjan_reach := st5.scratch.tarjan_reach.set idx.toNat 0#32 } }
        refine hJ4 (idx + 1#64, ()) _ (by dsimp only; omega)
          ⟨st6, hag5.update _,
           ⟨hlen5.core_ok, { hlen5.scratch_ok with
             tarjan_mark_len := by simp [st6, htmk5], tarjan_reach_len := by simp [st6, htrc5] }⟩,
           hinc5, hrsz5, hsh5, by omega, hpr5, fun l hl => ?_, hm⟩
        by_cases hli : l = idx.toNat
        · subst hli; dsimp only [st6]
          refine ⟨hfill_i, by rw [List.getElem?_set_self (by omega), Option.getD_some],
            by rw [List.getElem?_set_self (by omega), Option.getD_some]⟩
        · dsimp only [st6]
          rw [List.getElem?_set_ne (Ne.symm hli), List.getElem?_set_ne (Ne.symm hli),
            htmk_eq5, htrc_eq5]
          exact ⟨hfill_prev l (by omega), (hfill4 l (by omega)).2⟩
      · intro Jrep hRep; scc_split
        · scc_steps
          let st5 : FullState := { st4 with core := { st4.core with
            repr := st4.core.repr.set idx.toNat (BitVec.setWidth 32 idx) } }
          have hpr5 : PartialReprInv F_cur st5.core := fun l hl hne => by
            dsimp only [st5] at hl ⊢; by_cases hli : l = idx.toNat
            · subst hli; rw [List.getElem?_set_self (by omega), Option.getD_some,
                bv32_trunc_toNat hidx_lt32]; exact ⟨by omega, LitEquiv.refl _ _⟩
            · rw [List.getElem?_set_ne (Ne.symm hli)] at hne ⊢; exact hpr4 l hl hne
          have hfill_i : st5.core.repr[idx.toNat]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := by
            dsimp only [st5]; rw [List.getElem?_set_self (by omega), Option.getD_some]; intro heq
            have := congrArg BitVec.toNat heq; rw [bv32_trunc_toNat hidx_lt32] at this
            revert this; simp; omega
          exact hRep () _ ⟨st5, hag4.update _,
            ⟨{ hlen4.core_ok with repr_len := by simp [st5, hrp4] }, hlen4.scratch_ok⟩,
            hinc4, hrsz4, hsh4, rfl, rfl, hpr5, hfill_i,
            fun l hl => by
              dsimp only [st5]; rw [List.getElem?_set_ne (by omega)]; exact (hfill4 l hl).1,
            hm⟩
        · have hne_idx : st4.core.repr[idx.toNat]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := by
            rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; assumption
          scc_steps
          exact hRep () mk ⟨st4, hag4, hlen4, hinc4, hrsz4, hsh4, rfl, rfl, hpr4, hne_idx,
            fun l hl => (hfill4 l hl).1, hmk⟩
    · have hidx_eq : idx.toNat = 2 * s0.core.cur_vars := by have := m6_bv_ult_false_ge hc; omega
      scc_steps
      have hfin := m6_tarjan_fill_finish hsp0 hagf husf hag4 hlen4 hinc4 hrsz4 hsh4 hincf hpr4
        (fun l hl => hfill4 l (by omega))
      have heq4 := agrees_tarjanSccMask_eq hag4
      exact hQ st4.scratch.res_sz st4.core.repr st4.core.tmp_cnt st4.core.inconsistent
        st4.scratch.tarjan_mark st4.scratch.tarjan_reach st4.scratch.work_stk1 st4.scratch.work_stk2
        st4.scratch.wsort st4.scratch.shrink_stk st4.scratch.res_sz mk
        (heq4.symm ▸ hfin.1) (by rw [hrsz4]; exact hrszf) hfin.2.2.1
        (fun _ => heq4.symm ▸ hfin.2.1 0) hfin.2.2.2.1 (heq4.symm ▸ hfin.2.2.2.2) (heq4.symm ▸ hmk)
  intro Jexit hExit; scc_split; rotate_left
  · scc_steps; exact hExit () ml ⟨st, ⟨hag, hlen, hrsz, hpr, hus, hinc_u⟩, hml⟩
  have hrt_lt : root.toNat < 2 * s0.core.cur_vars := by
    have := BitVec.lt_def.mp (BitVec.ult_iff_lt.mp hc); rwa [hnl_eq] at this
  have hrt1 : (root + 1#64).toNat = root.toNat + 1 := m6_bv64_add1_toNat (by omega)
  scc_split; rotate_left
  · scc_steps; exact hExit () ml ⟨st, ⟨hag, hlen, hrsz, hpr, hus, hinc_u⟩, hml⟩
  have hst_inc0 : st.core.inconsistent = 0#64 := hc; obtain ⟨htop0, hdfs⟩ := hinc_dfs hst_inc0
  scc_to_group
  refine wp_join_group (ts := [i32])
    (fun (rch', ()) mj => ∃ st' : FullState, TarjanLoopBase c F_cur s0 st' ∧
      (st'.core.inconsistent = 0#64 →
        st'.core.tmp_cnt = 0 ∧ M6TarjanDfsInv c F0 F_cur s0 0 1 rch'.toNat 0 st') ∧
      (FullMem c st' ⋆ R) mj) ?_ ?_
  · rintro _ ⟨rch', ⟨⟩⟩ mj ⟨st', hbase', hdfs', hmj⟩
    scc_steps; exact hJ2 (rch', root + 1#64, ()) mj (by dsimp only; omega)
      ⟨st', by omega, hbase', hdfs', hmj⟩
  intro Jskip hSkip; scc_split; rotate_left
  · scc_steps; exact hSkip (reached, ()) ml ⟨st, ⟨hag, hlen, hrsz, hpr, hus, hinc_u⟩, hinc_dfs, hml⟩
  have htmk_rt0 : (st.scratch.tarjan_mark[root.toNat]?.getD 0#32).toNat = 0 := by
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some, hc]; rfl
  scc_split; rotate_left
  · scc_steps; exact hSkip (reached, ()) ml ⟨st, ⟨hag, hlen, hrsz, hpr, hus, hinc_u⟩, hinc_dfs, hml⟩
  have hact_rt : activeLit s0 root.toNat := by
    refine ⟨hrt_lt, ?_⟩
    rw [← hag.get (·.core.flags), List.getElem?_eq_getElem (by omega), Option.getD_some]
    simp only [FullSccTactics.bv64_ushr1_nat] at hc; exact hc
  have hr_lt := hdfs.reached_lt_of_unvisited hrt_lt htmk_rt0
  have hr1_nat : (reached + (1 : BitVec 32)).toNat = reached.toNat + 1 :=
    m6_bv32_add1_toNat (by omega)
  have hrt32_eq : BitVec.setWidth 32 root = BitVec.ofNat 32 root.toNat :=
    BitVec.eq_of_toNat_eq (by
      rw [bv32_trunc_toNat (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])
  have hr32_eq : reached + (1 : BitVec 32) = BitVec.ofNat 32 (reached.toNat + 1) :=
    BitVec.eq_of_toNat_eq (by rw [hr1_nat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])
  have hinit_dfs := m6_tarjan_init_root hw0 hdm0 hdfs htop0 hact_rt htmk_rt0
  have hpos_mv : 0 < 2 * c.max_vars := by omega
  scc_to_group
  refine wp_loop_group (ts := [i32, .bool, i64])
    (fun n (rch, _failb, dsp, ()) m3 => ∃ st3 : FullState, TarjanLoopBase c F_cur s0 st3 ∧
      (st3.core.inconsistent = 0#64 →
        n = M6TarjanDfsInv.measure c s0 st3 rch.toNat dsp.toNat ∧
        M6TarjanDfsInv c F0 F_cur s0 root.toNat (reached.toNat + 1) rch.toNat dsp.toNat st3 ∧
        (dsp.toNat = 0 → st3.core.tmp_cnt = 0)) ∧ (FullMem c st3 ⋆ R) m3) ?_ ?_
  rotate_left
  · intro J3 hJ3; scc_steps
    let st_init : FullState :=
      { st with
        core := { st.core with tmp_cnt := 1 }
        scratch := { st.scratch with
          work_stk2 := st.scratch.work_stk2.set 0 (BitVec.ofNat 32 root.toNat)
          wsort := st.scratch.wsort.set 0 0#32
          tarjan_mark := st.scratch.tarjan_mark.set root.toNat (BitVec.ofNat 32 (reached.toNat + 1))
          tarjan_reach :=
            st.scratch.tarjan_reach.set root.toNat (BitVec.ofNat 32 (reached.toNat + 1))
          work_stk1 := st.scratch.work_stk1.set 0 (BitVec.ofNat 32 root.toNat) } }
    have hm_init : (FullMem c st_init ⋆ R) m := by
      rw [htop0, hrt32_eq, hr32_eq, show (BitVec.ofNat 64 0 + (1 : BitVec 64)).toNat = 1 from rfl,
        show (BitVec.ofNat 64 0).toNat = 0 from rfl] at hm; exact hm
    exact hJ3 _ (reached + (1 : BitVec 32), false, 1#64, ()) m
      ⟨st_init, hinit_dfs.2.toBase,
       fun _ => ⟨rfl, by rw [hr1_nat]; exact hinit_dfs.2, fun h => by simp at h⟩, hm_init⟩
  rintro J3 n ⟨rch, failb, dsp, ⟨⟩⟩ m3 hJ3 ⟨st3, hbase3, hdfs3, hm3⟩
  clear hinc_dfs hdfs hinit_dfs hact_rt htmk_rt0 hr_lt hrt32_eq hr32_eq hrsz hpr hus hinc_u
    hst_inc0 htop0
  scc_split; rotate_left
  · have hdsp0 : dsp.toNat = 0 := by
      have := m6_bv_ult_false_ge hc; rw [show (0 : BitVec 64).toNat = 0 from rfl] at this; omega
    scc_steps; refine hSkip (rch, ()) m3 ⟨st3, hbase3, fun hinc30 => ?_, hm3⟩
    obtain ⟨_, hd3, htop3⟩ := hdfs3 hinc30; exact ⟨htop3 hdsp0, hd3.reset_empty (htop3 hdsp0)⟩
  have hdsp_pos : 0 < dsp.toNat := by
    have := BitVec.lt_def.mp (BitVec.ult_iff_lt.mp hc)
    rwa [show (0 : BitVec 64).toNat = 0 from rfl] at this
  scc_split; rotate_left
  · scc_steps; exact hSkip (rch, ()) m3 ⟨st3, hbase3, fun h => absurd h hc, hm3⟩
  have hinc30 : st3.core.inconsistent = 0#64 := hc; obtain ⟨rfl, hd3, _⟩ := hdfs3 hinc30
  obtain ⟨hag3, hlen3, hrsz3, hpr3, hus3, hinc3⟩ := hbase3
  have hcl3 := hlen3.core_ok; have hsl3 := hlen3.scratch_ok
  have hdv_l3 := hsl3.work_stk2_len; have hdp_l3 := hsl3.wsort_len
  have hscc_l3 := hsl3.work_stk1_len; have htmk_l3 := hsl3.tarjan_mark_len
  have htrc_l3 := hsl3.tarjan_reach_len; have hfl_l3 := hcl3.flags_len
  have hwv_l3 := hcl3.wvec_len; have hws_l3 := hcl3.wstk_len_arr
  have hcv3 := hag3.get (·.core.cur_vars); have hwv3 := hag3.get (·.core.wvec)
  have hws3 := hag3.get (·.core.wstk); have hfl3 := hag3.get (·.core.flags)
  have hdsp_sub : (dsp - (1 : BitVec 64)).toNat = dsp.toNat - 1 := by
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by change 1 ≤ _; omega))]; rfl
  have hdsp_lt3 : dsp.toNat ≤ 2 * s0.core.cur_vars := by
    have := hd3.dsp_le; have := hd3.top_le; have := hd3.reached_le; omega
  let lit := st3.scratch.work_stk2[(dsp - (1 : BitVec 64)).toNat]'(by rw [hdsp_sub]; omega)
  have hlit_get : lit = st3.scratch.work_stk2[dsp.toNat - 1]?.getD 0#32 := by
    have hlt : dsp.toNat - 1 < st3.scratch.work_stk2.length := by omega
    simp only [lit, hdsp_sub, List.getElem?_eq_getElem hlt, Option.getD_some]
  have hlit_lt : lit.toNat < 2 * s0.core.cur_vars := by rw [hlit_get]; exact hd3.dv_lt (by omega)
  have hnl_lt_nat : lit.toNat ^^^ 1 < 2 * s0.core.cur_vars := litNeg_lt_two_mul hlit_lt
  have hnl_lt : (lit ^^^ (1 : BitVec 32)).toNat < 2 * s0.core.cur_vars := by
    rw [show (1 : BitVec 32) = 1#32 from rfl, bv32_xor1_toNat]; exact hnl_lt_nat
  have hlit_act : activeLit s0 lit.toNat := by
    obtain ⟨j, hj, hjeq⟩ := hd3.dv_on_scc (dsp.toNat - 1) (by omega); rw [← hlit_get] at hjeq
    exact hd3.tmk_active lit.toNat hlit_lt
      (by have := hd3.scc_tmk_ge j hj; rw [hjeq] at this; omega)
  let pos32 := st3.scratch.wsort[(dsp - (1 : BitVec 64)).toNat]'(by rw [hdsp_sub]; omega)
  have hpos_get : pos32 = st3.scratch.wsort[dsp.toNat - 1]?.getD 0#32 := by
    have hlt : dsp.toNat - 1 < st3.scratch.wsort.length := by omega
    simp only [pos32, hdsp_sub, List.getElem?_eq_getElem hlt, Option.getD_some]
  have hnl2 : (BitVec.setWidth 64 (lit ^^^ (1 : BitVec 32)) <<< (1 : Nat)).toNat =
      2 * (lit.toNat ^^^ 1) := by
    rw [FullArenaTactics.bv64_shl1_nat, zext_toNat _ (by decide),
      show (1 : BitVec 32) = 1#32 from rfl, bv32_xor1_toNat]; exact Nat.mod_eq_of_lt (by omega)
  have hnl2_1 : ((BitVec.setWidth 64 (lit ^^^ (1 : BitVec 32)) <<< (1 : Nat)) +
      (1 : BitVec 64)).toNat = 2 * (lit.toNat ^^^ 1) + 1 :=
    (m6_bv64_add1_toNat (by rw [hnl2]; omega)).trans (by rw [hnl2])
  have hnl2_u : (BitVec.setWidth 64
      (st3.scratch.work_stk2[(dsp - (1 : BitVec 64)).toNat]'(by rw [hdsp_sub]; omega) ^^^
        (1 : BitVec 32)) <<< (1 : Nat)).toNat = 2 * (lit.toNat ^^^ 1) := hnl2
  have hnl2_1_u : ((BitVec.setWidth 64
      (st3.scratch.work_stk2[(dsp - (1 : BitVec 64)).toNat]'(by rw [hdsp_sub]; omega) ^^^
        (1 : BitVec 32)) <<< (1 : Nat)) + (1 : BitVec 64)).toNat = 2 * (lit.toNat ^^^ 1) + 1 :=
    hnl2_1
  let off32 := st3.core.wvec[(BitVec.setWidth 64 (lit ^^^ (1 : BitVec 32)) <<< (1 : Nat)).toNat]'(
    by rw [hnl2]; omega)
  let sz32 := st3.core.wvec[((BitVec.setWidth 64 (lit ^^^ (1 : BitVec 32)) <<< (1 : Nat)) +
    (1 : BitVec 64)).toNat]'(by rw [hnl2_1]; omega)
  let woff := fullWatchOffCore s0.core (lit.toNat ^^^ 1)
  let wsz := fullWatchSizeCore s0.core (lit.toNat ^^^ 1)
  have hoff_get : off32.toNat = woff := by
    unfold woff fullWatchOffCore; rw [← hwv3]
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; dsimp only [off32]; simp only [hnl2]
  have hsz_get : sz32.toNat = wsz := by
    unfold wsz fullWatchSizeCore; rw [← hwv3]
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    dsimp only [sz32]; simp only [hnl2_1]
  have hslc3 := hd3.dpos_slice (dsp.toNat - 1) (by omega); rw [← hlit_get] at hslc3
  have hsb : woff + wsz ≤ s0.core.wlen := hwat0.layout.bounds (lit.toNat ^^^ 1) hnl_lt_nat
  have hwle0 := hlen0.core_ok.wlen_le
  have hz_lit : (BitVec.setWidth 64 lit).toNat = lit.toNat := zext_toNat lit (by decide)
  have hz_lit_u : (BitVec.setWidth 64
      (st3.scratch.work_stk2[(dsp - (1 : BitVec 64)).toNat]'(by rw [hdsp_sub]; omega))).toNat =
      lit.toNat := hz_lit
  have hz_lit_lt : (BitVec.setWidth 64
      (st3.scratch.work_stk2[(dsp - (1 : BitVec 64)).toNat]'(by rw [hdsp_sub]; omega))).toNat <
      2 * c.max_vars := by rw [hz_lit_u]; omega
  scc_split
  · have hpos_lt : pos32.toNat < wsz := by
      rw [← hsz_get]; exact BitVec.lt_def.mp (BitVec.ult_iff_lt.mp hc)
    have hidx_eq : (BitVec.setWidth 64 off32 + BitVec.setWidth 64 pos32).toNat =
        woff + pos32.toNat := by
      rw [m6_bv64_add_toNat (by rw [zext_toNat _ (by decide), zext_toNat _ (by decide)]; omega),
        zext_toNat _ (by decide), zext_toNat _ (by decide), hoff_get]
    have hidx_lt : (BitVec.setWidth 64 off32 + BitVec.setWidth 64 pos32).toNat <
        st3.core.wstk.length := by rw [hidx_eq]; omega
    have hidx_lt_u : (BitVec.setWidth 64 off32 + BitVec.setWidth 64 pos32).toNat < c.wcap := by
      rw [hidx_eq]; omega
    dsimp only [off32, pos32, lit] at hidx_lt_u
    scc_split
    · have hflag0 : (s0.core.wstk[woff + pos32.toNat]?.getD 0#32 &&& 0x80000000#32) = 0#32 := by
        rw [← hws3, List.getElem?_eq_getElem (by omega), Option.getD_some]
        dsimp only [off32, pos32, lit] at hidx_eq; simp only [hidx_eq] at hc; exact hc
      have hp2 : (pos32 + (2 : BitVec 32)).toNat = pos32.toNat + 2 := m6_bv32_add2_toNat (by omega)
      have hsc_nb : ∃ sc, sliceBinsFrom s0.core.wstk woff wsz =
          sc ++ sliceBinsFrom s0.core.wstk (woff + pos32.toNat) (wsz - pos32.toNat) ∧
          ∀ x ∈ sc, activeLit s0 x →
            1 ≤ (st3.scratch.tarjan_mark[x]?.getD 0#32).toNat ∧
            (onScc st3 x →
              (st3.scratch.tarjan_reach[(lit.toNat ^^^ 1) ^^^ 1]?.getD 0#32).toNat ≤
                (st3.scratch.tarjan_reach[x]?.getD 0#32).toNat) := by
        obtain ⟨sc, hseq, hsok⟩ := hslc3.2.2
        refine ⟨sc, by rw [← hpos_get] at hseq; exact hseq, fun x hx hax => ?_⟩
        have hs := hsok x hx hax
        exact ⟨hs.1, fun hso => by
          rw [xor1_xor1 lit.toNat]
          exact hs.2.1 hso (fun h => by omega)⟩
      have hslc_nb := dpos_step_nonbin hpos_lt hp2 (hpos_get ▸ hslc3.2.1) hflag0 hsc_nb
      obtain ⟨hd4, hmeas4⟩ := m6_tarjan_advance_dpos (pos' := pos32 + (2 : BitVec 32)) hd3 hdsp_pos
        (by rw [← hpos_get, hp2]; omega) (by
          rw [← hlit_get]
          refine ⟨hslc_nb.1, hslc_nb.2.1, ?_⟩
          obtain ⟨sc, hseq, hsok⟩ := hslc_nb.2.2
          exact ⟨sc, hseq, fun x hx hax =>
            ⟨(hsok x hx hax).1, fun hso => by
              have := (hsok x hx hax).2 hso
              rwa [xor1_xor1 lit.toNat] at this⟩⟩)
      scc_steps
      let st4 : FullState := { st3 with scratch := { st3.scratch with
        wsort := st3.scratch.wsort.set (dsp.toNat - 1) (pos32 + (2 : BitVec 32)) } }
      have hm4 : (FullMem c st4 ⋆ R) m := by
        have hw : st3.scratch.wsort.set (dsp - (1 : BitVec 64)).toNat (pos32 + (2 : BitVec 32)) =
            st3.scratch.wsort.set (dsp.toNat - 1) (pos32 + (2 : BitVec 32)) := by rw [hdsp_sub]
        dsimp only [st4]; rw [← hw]; exact hm
      exact hJ3 _ (rch, failb, dsp, ()) m hmeas4
        ⟨st4, hd4.toBase, fun _ => ⟨rfl, hd4, fun h => by omega⟩, hm4⟩
    have hflag1 : (s0.core.wstk[woff + pos32.toNat]?.getD 0#32 &&& 0x80000000#32) ≠ 0#32 := by
      rw [← hws3, List.getElem?_eq_getElem (by omega), Option.getD_some]
      dsimp only [off32, pos32, lit] at hidx_eq; simp only [hidx_eq] at hc; exact hc
    have hp1 : (pos32 + (1 : BitVec 32)).toNat = pos32.toNat + 1 := m6_bv32_add1_toNat (by omega)
    have hsc_b1 : ∃ sc, sliceBinsFrom s0.core.wstk woff wsz =
        sc ++ sliceBinsFrom s0.core.wstk (woff + pos32.toNat) (wsz - pos32.toNat) ∧
        ∀ x ∈ sc, activeLit s0 x →
          1 ≤ (st3.scratch.tarjan_mark[x]?.getD 0#32).toNat ∧
          (onScc st3 x →
            (st3.scratch.tarjan_reach[(lit.toNat ^^^ 1) ^^^ 1]?.getD 0#32).toNat ≤
              (st3.scratch.tarjan_reach[x]?.getD 0#32).toNat) := by
      obtain ⟨sc, hseq, hsok⟩ := hslc3.2.2
      refine ⟨sc, by rw [← hpos_get] at hseq; exact hseq, fun x hx hax => ?_⟩
      have hs := hsok x hx hax
      exact ⟨hs.1, fun hso => by
        rw [xor1_xor1 lit.toNat]
        exact hs.2.1 hso (fun h => by omega)⟩
    obtain ⟨w0, hw0_eq, hot_lt, hbins_ot, hslc_b1_raw⟩ :=
      dpos_step_bin hpos_lt hp1 (hpos_get ▸ hslc3.2.1) hflag1 hsc_b1
    have hslc_b1 : (pos32 + (1 : BitVec 32)).toNat ≤ wsz ∧
        WatchSliceOk F_cur s0.core (lit.toNat ^^^ 1)
          (woff + (pos32 + (1 : BitVec 32)).toNat) (wsz - (pos32 + (1 : BitVec 32)).toNat) ∧
        ∃ sc, sliceBinsFrom s0.core.wstk woff wsz =
            sc ++ sliceBinsFrom s0.core.wstk (woff + (pos32 + (1 : BitVec 32)).toNat)
              (wsz - (pos32 + (1 : BitVec 32)).toNat) ∧
          ∀ x ∈ sc, activeLit s0 x →
            x = (w0 &&& 0x7FFFFFFF#32).toNat ∨
            (1 ≤ (st3.scratch.tarjan_mark[x]?.getD 0#32).toNat ∧
              (onScc st3 x →
                (st3.scratch.tarjan_reach[lit.toNat]?.getD 0#32).toNat ≤
                  (st3.scratch.tarjan_reach[x]?.getD 0#32).toNat)) := by
      refine ⟨hslc_b1_raw.1, hslc_b1_raw.2.1, ?_⟩
      obtain ⟨sc, hseq, hsok⟩ := hslc_b1_raw.2.2
      exact ⟨sc, hseq, fun x hx hax =>
        (hsok x hx hax).elim Or.inl fun hs => Or.inr ⟨hs.1, fun hso => by
          have := hs.2 hso; rwa [xor1_xor1 lit.toNat] at this⟩⟩
    have hw0_get : st3.core.wstk[(BitVec.setWidth 64 off32 +
        BitVec.setWidth 64 pos32).toNat]'hidx_lt = w0 := by
      have h1 := hw0_eq; rw [← hws3, List.getElem?_eq_getElem (by omega)] at h1
      simpa only [hidx_eq] using Option.some.inj h1
    dsimp only [off32, pos32, lit] at hw0_get
    let ot := w0 &&& (2147483647 : BitVec 32)
    have hot_lt' : ot.toNat < 2 * s0.core.cur_vars := hot_lt
    have hz_ot : (BitVec.setWidth 64 ot).toNat = ot.toNat := zext_toNat ot (by decide)
    have hdiv_ot : (BitVec.setWidth 64 (ot >>> (BitVec.toNat (1 : BitVec 32) % 32))).toNat =
        ot.toNat / 2 := by
      rw [zext_toNat _ (by decide), show BitVec.toNat (1 : BitVec 32) % 32 = 1 from rfl,
        FullSccTactics.bv32_ushr1_nat]
    have hot_z_lt : (BitVec.setWidth 64 (st3.core.wstk[(BitVec.setWidth 64 off32 +
        BitVec.setWidth 64 pos32).toNat]'hidx_lt &&& (2147483647 : BitVec 32))).toNat <
        2 * c.max_vars := by
      dsimp only [off32, pos32, lit]; rw [hw0_get]; change (BitVec.setWidth 64 ot).toNat < _
      rw [hz_ot]; omega
    have hot_div_lt : (BitVec.setWidth 64 ((st3.core.wstk[(BitVec.setWidth 64 off32 +
        BitVec.setWidth 64 pos32).toNat]'hidx_lt &&& (2147483647 : BitVec 32)) >>>
          (BitVec.toNat (1 : BitVec 32) % 32))).toNat < c.max_vars := by
      dsimp only [off32, pos32, lit]; rw [hw0_get]
      change (BitVec.setWidth 64 (ot >>> (BitVec.toNat (1 : BitVec 32) % 32))).toNat < _
      rw [hdiv_ot]; omega
    dsimp only [off32, pos32, lit] at hot_z_lt hot_div_lt
    scc_to_group
    refine wp_join_group (ts := [i32, i64])
      (fun (rch', dsp', ()) mj => ∃ st4 : FullState, 0 < dsp'.toNat ∧
        M6TarjanDfsInv c F0 F_cur s0 root.toNat (reached.toNat + 1) rch'.toNat dsp'.toNat st4 ∧
        M6TarjanDfsInv.measure c s0 st4 rch'.toNat dsp'.toNat <
          M6TarjanDfsInv.measure c s0 st3 rch.toNat dsp.toNat ∧ (FullMem c st4 ⋆ R) mj) ?_ ?_
    · rintro _ ⟨rch', dsp', ⟨⟩⟩ mj ⟨st4, hdsp4, hd4, hm4, hmj⟩
      scc_steps; exact hJ3 _ (rch', failb, dsp', ()) mj hm4
        ⟨st4, hd4.toBase, fun _ => ⟨rfl, hd4, fun h => by omega⟩, hmj⟩
    intro Jb hJb
    let st3a : FullState := { st3 with scratch := { st3.scratch with
      wsort := st3.scratch.wsort.set (dsp.toNat - 1) (pos32 + (1 : BitVec 32)) } }
    have hma : (FullMem c st3a ⋆ R) m := by
      have hw : st3.scratch.wsort.set (dsp - (1 : BitVec 64)).toNat (pos32 + (1 : BitVec 32)) =
          st3.scratch.wsort.set (dsp.toNat - 1) (pos32 + (1 : BitVec 32)) := by rw [hdsp_sub]
      dsimp only [st3a]; rw [← hw]; exact hm
    have hskip_ok : (¬ activeLit s0 ot.toNat ∨
        (1 ≤ (st3.scratch.tarjan_mark[ot.toNat]?.getD 0#32).toNat ∧
          (st3.scratch.tarjan_reach[lit.toNat]?.getD 0#32).toNat ≤
            (st3.scratch.tarjan_reach[ot.toNat]?.getD 0#32).toNat)) →
        M6TarjanDfsInv c F0 F_cur s0 root.toNat (reached.toNat + 1) rch.toNat dsp.toNat st3a ∧
        M6TarjanDfsInv.measure c s0 st3a rch.toNat dsp.toNat <
          M6TarjanDfsInv.measure c s0 st3 rch.toNat dsp.toNat := by
      intro hsk; obtain ⟨hle, hslc, sc, hseq, hsok⟩ := hslc_b1
      exact m6_tarjan_advance_dpos (pos' := pos32 + (1 : BitVec 32)) hd3 hdsp_pos
        (by rw [← hpos_get, hp1]; omega)
        (by rw [← hlit_get]; refine ⟨hle, hslc, sc, hseq, fun x hx hax => ?_⟩
            rcases hsok x hx hax with rfl | hpos
            · exact hsk.elim (fun hna => absurd hax hna) fun ⟨h1, h2⟩ => ⟨h1, fun _ => h2⟩
            · exact hpos)
    clear hm
    have hfl_a : st3a.core.flags.length = c.max_vars := hfl_l3
    have htmk_a : st3a.scratch.tarjan_mark.length = 2 * c.max_vars := htmk_l3
    have htrc_a : st3a.scratch.tarjan_reach.length = 2 * c.max_vars := htrc_l3
    have hscc_a : st3a.scratch.work_stk1.length = 2 * c.max_vars := hscc_l3
    have hdv_a : st3a.scratch.work_stk2.length = 2 * c.max_vars := hdv_l3
    have hdp_a : st3a.scratch.wsort.length = 2 * c.max_vars := by
      dsimp only [st3a]; rw [List.length_set]; exact hdp_l3
    have hflag_ot : st3.core.flags[(BitVec.setWidth 64 ((st3.core.wstk[(BitVec.setWidth 64 off32 +
        BitVec.setWidth 64 pos32).toNat]'hidx_lt &&& (2147483647 : BitVec 32)) >>>
          (BitVec.toNat (1 : BitVec 32) % 32))).toNat]'(
            by rw [hfl_l3]; dsimp only [off32, pos32, lit]; exact hot_div_lt) =
        st3.core.flags[ot.toNat / 2]'(by omega) :=
      getElem_congr_idx _ _ (by dsimp only [off32, pos32, lit]; rw [hw0_get]; exact hdiv_ot)
    have htmk_ot : st3.scratch.tarjan_mark[(BitVec.setWidth 64 (st3.core.wstk[(BitVec.setWidth 64
        off32 + BitVec.setWidth 64 pos32).toNat]'hidx_lt &&& (2147483647 : BitVec 32))).toNat]'(
          by rw [htmk_l3]; dsimp only [off32, pos32, lit]; exact hot_z_lt) =
        st3.scratch.tarjan_mark[ot.toNat]'(by omega) :=
      getElem_congr_idx _ _ (by dsimp only [off32, pos32, lit]; rw [hw0_get]; exact hz_ot)
    have htrc_ot : st3.scratch.tarjan_reach[(BitVec.setWidth 64 (st3.core.wstk[(BitVec.setWidth 64
        off32 + BitVec.setWidth 64 pos32).toNat]'hidx_lt &&& (2147483647 : BitVec 32))).toNat]'(
          by rw [htrc_l3]; dsimp only [off32, pos32, lit]; exact hot_z_lt) =
        st3.scratch.tarjan_reach[ot.toNat]'(by omega) :=
      getElem_congr_idx _ _ (by dsimp only [off32, pos32, lit]; rw [hw0_get]; exact hz_ot)
    dsimp only [off32, pos32, lit] at hflag_ot htmk_ot htrc_ot
    scc_split; rotate_left
    · exfalso; rw [hw0_get] at hc; have := m6_bv_ult_false_ge hc; rw [hnl_eq, hz_ot] at this; omega
    scc_split; rotate_left
    · have hna : ¬ activeLit s0 ot.toNat := fun hact => hact.2 (by
        rw [← hfl3, List.getElem?_eq_getElem (by omega), Option.getD_some]
        dsimp only [st3a] at hc; rw [hflag_ot] at hc; exact Classical.not_not.mp hc)
      obtain ⟨hd4, hm4⟩ := hskip_ok (Or.inl hna)
      scc_steps; exact hJb (rch, dsp, ()) m ⟨st3a, hdsp_pos, hd4, hm4, hma⟩
    have hact_ot : activeLit s0 ot.toNat := ⟨hot_lt', by
      rw [← hfl3, List.getElem?_eq_getElem (by omega), Option.getD_some]
      dsimp only [st3a] at hc; rw [hflag_ot] at hc; exact hc⟩
    have hot_eq : (st3.core.wstk[(BitVec.setWidth 64 off32 +
        BitVec.setWidth 64 pos32).toNat]'hidx_lt &&& (2147483647 : BitVec 32)) = ot := by
      dsimp only [off32, pos32, lit]; rw [hw0_get]
    dsimp only [off32, pos32, lit] at hot_eq
    scc_step; scc_split
    · have htmk_ot0 : (st3.scratch.tarjan_mark[ot.toNat]?.getD 0#32).toNat = 0 := by
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
        dsimp only [st3a] at hc; rw [htmk_ot] at hc; rw [hc]; rfl
      have hr_lt3 := hd3.reached_lt_of_unvisited hot_lt' htmk_ot0
      have htop_lt3 : st3.core.tmp_cnt < 2 * s0.core.cur_vars := by have := hd3.top_le; omega
      have hdsp_lt3' : dsp.toNat < 2 * s0.core.cur_vars := by have := hd3.dsp_le; omega
      have hr1_3 : (rch + (1 : BitVec 32)).toNat = rch.toNat + 1 := m6_bv32_add1_toNat (by omega)
      have hr32_3 : rch + (1 : BitVec 32) = BitVec.ofNat 32 (rch.toNat + 1) :=
        BitVec.eq_of_toNat_eq (by rw [hr1_3, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])
      have hdsp1 : (dsp + (1 : BitVec 64)).toNat = dsp.toNat + 1 := m6_bv64_add1_toNat (by omega)
      have htc_mod_a : (BitVec.ofNat 64 st3a.core.tmp_cnt).toNat = st3.core.tmp_cnt := by
        dsimp only [st3a]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      have htc1_a : (BitVec.ofNat 64 st3a.core.tmp_cnt + (1 : BitVec 64)).toNat =
          st3.core.tmp_cnt + 1 := (m6_bv64_add1_toNat (by rw [htc_mod_a]; omega)).trans (by
            rw [htc_mod_a])
      obtain ⟨_, hdisc, hm_disc⟩ := m6_tarjan_discover_node hw0 hdm0 hd3 hdsp_pos
        (by rw [← hpos_get]; exact hp1) (by rw [← hlit_get]; exact ⟨hlit_act, hact_ot, hbins_ot⟩)
        htmk_ot0 (by rw [← hlit_get]; exact hslc_b1)
      scc_steps
      let st4 : FullState :=
        { st3 with
          core := { st3.core with tmp_cnt := st3.core.tmp_cnt + 1 }
          scratch := { st3.scratch with
            wsort := (st3.scratch.wsort.set (dsp.toNat - 1) (pos32 + (1 : BitVec 32))).set
              dsp.toNat 0#32
            tarjan_mark := st3.scratch.tarjan_mark.set ot.toNat (BitVec.ofNat 32 (rch.toNat + 1))
            tarjan_reach := st3.scratch.tarjan_reach.set ot.toNat (BitVec.ofNat 32 (rch.toNat + 1))
            work_stk1 := st3.scratch.work_stk1.set st3.core.tmp_cnt ot
            work_stk2 := st3.scratch.work_stk2.set dsp.toNat ot } }
      have hm_d : (FullMem c st4 ⋆ R) m := by
        dsimp only [st4, st3a] at hm ⊢
        rw [hot_eq, hz_ot, hr32_3, htc1_a, htc_mod_a] at hm; exact hm
      exact hJb (rch + (1 : BitVec 32), dsp + (1 : BitVec 64), ()) m
        ⟨st4, by rw [hdsp1]; omega, by rw [hr1_3, hdsp1]; exact hdisc,
         by rw [hr1_3, hdsp1]; exact hm_disc, hm_d⟩
    have htmk_pos : 1 ≤ (st3.scratch.tarjan_mark[ot.toNat]?.getD 0#32).toNat := by
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      dsimp only [st3a] at hc; rw [htmk_ot] at hc
      exact Nat.pos_of_ne_zero fun h0 => hc (BitVec.eq_of_toNat_eq (by simpa using h0))
    have htrc_lit_get :
        st3a.scratch.tarjan_reach[(BitVec.setWidth 64 lit).toNat]'(by
          dsimp only [st3a]; rw [htrc_l3, hz_lit]; omega) =
        st3.scratch.tarjan_reach[lit.toNat]?.getD 0#32 := by
      have hlt : lit.toNat < st3.scratch.tarjan_reach.length := by rw [htrc_l3]; omega
      dsimp only [st3a]; simp only [hz_lit, List.getElem?_eq_getElem hlt, Option.getD_some]
    scc_step; scc_split
    · have htrc_lt : (st3.scratch.tarjan_reach[ot.toNat]?.getD 0#32).toNat <
          (st3.scratch.tarjan_reach[lit.toNat]?.getD 0#32).toNat := by
        have h1 := BitVec.lt_def.mp (BitVec.ult_iff_lt.mp hc)
        dsimp only [st3a] at h1; rw [htrc_ot, htrc_lit_get] at h1
        rw [List.getElem?_eq_getElem (by rw [htrc_l3]; omega : ot.toNat < _), Option.getD_some]
        exact h1
      obtain ⟨hbe_inv, hbe_meas⟩ := m6_tarjan_back_edge hw0 hdm0 hd3 hdsp_pos
        (by rw [← hpos_get]; exact hp1) (by rw [← hlit_get]; exact ⟨hlit_act, hact_ot, hbins_ot⟩)
        htmk_pos rfl (by rw [← hlit_get]; exact htrc_lt) (by rw [← hlit_get]; exact hslc_b1)
      scc_steps
      let st4 : FullState := { st3 with scratch := { st3.scratch with
        wsort := st3.scratch.wsort.set (dsp.toNat - 1) (pos32 + (1 : BitVec 32))
        tarjan_reach := st3.scratch.tarjan_reach.set lit.toNat
          (st3.scratch.tarjan_reach[ot.toNat]?.getD 0#32) } }
      have hm_b : (FullMem c st4 ⋆ R) m := by
        dsimp only [st4, st3a] at hm ⊢
        have hset : st3.scratch.tarjan_reach[ot.toNat]'(by omega) =
            st3.scratch.tarjan_reach[ot.toNat]?.getD 0#32 := by
          rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
        rw [← hset]; rw [hz_lit, htrc_ot] at hm; exact hm
      rw [← hlit_get] at hbe_inv hbe_meas
      exact hJb (rch, dsp, ()) m ⟨st4, hdsp_pos, hbe_inv, hbe_meas, hm_b⟩
    · have htrc_ge : (st3.scratch.tarjan_reach[lit.toNat]?.getD 0#32).toNat ≤
          (st3.scratch.tarjan_reach[ot.toNat]?.getD 0#32).toNat := by
        have hge := m6_bv_ult_false_ge hc; dsimp only [st3a] at hge
        rw [htrc_ot, htrc_lit_get] at hge
        rw [List.getElem?_eq_getElem (by rw [htrc_l3]; omega : ot.toNat < _), Option.getD_some]
        exact hge
      obtain ⟨hd4, hm4⟩ := hskip_ok (Or.inr ⟨htmk_pos, htrc_ge⟩)
      scc_steps; exact hJb (rch, dsp, ()) m ⟨st3a, hdsp_pos, hd4, hm4, hma⟩
  have hpos_ge : wsz ≤ (st3.scratch.wsort[dsp.toNat - 1]?.getD 0#32).toNat := by
    rw [← hpos_get, ← hsz_get]; exact m6_bv_ult_false_ge hc
  have hscan : ∀ v, activeEdge s0 lit.toNat v → onScc st3 v →
      (st3.scratch.tarjan_reach[lit.toNat]?.getD 0#32).toNat ≤
        (st3.scratch.tarjan_reach[v]?.getD 0#32).toNat := by
    intro v hv hov; obtain ⟨_, _, sc, hseq, hsok⟩ := hslc3
    have h0 : wsz - (st3.scratch.wsort[dsp.toNat - 1]?.getD 0#32).toNat = 0 := by omega
    rw [h0] at hseq
    rw [show sliceBinsFrom s0.core.wstk _ 0 = [] from rfl, List.append_nil] at hseq
    exact (hsok v (hseq ▸ hv.2.2) hv.2.1).2.1 hov (fun h => by omega)
  let rlit := st3.scratch.tarjan_reach[lit.toNat]'(by omega)
  have hrlit_eq : rlit = st3.scratch.tarjan_reach[lit.toNat]?.getD 0#32 := by
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
  have htrc_lit_get :
      st3.scratch.tarjan_reach[(BitVec.setWidth 64 lit).toNat]'(by rw [hz_lit]; omega) = rlit :=
    getElem_congr_idx _ _ hz_lit
  have htmk_lit_get :
      st3.scratch.tarjan_mark[(BitVec.setWidth 64 lit).toNat]'(by rw [hz_lit]; omega) =
      st3.scratch.tarjan_mark[lit.toNat]?.getD 0#32 := by
    have hlt : lit.toNat < st3.scratch.tarjan_mark.length := by omega
    rw [List.getElem?_eq_getElem hlt, Option.getD_some]
    exact getElem_congr_idx _ _ hz_lit
  dsimp only [lit] at htrc_lit_get htmk_lit_get
  scc_to_group
  refine wp_join_group (ts := [.bool])
    (fun (failb', ()) mj => ∃ st4 : FullState, TarjanLoopBase c F_cur s0 st4 ∧
      (st4.core.inconsistent = 0#64 →
        M6TarjanDfsInv c F0 F_cur s0 root.toNat (reached.toNat + 1) rch.toNat (dsp.toNat - 1) st4 ∧
        M6TarjanDfsInv.measure c s0 st4 rch.toNat (dsp.toNat - 1) <
          M6TarjanDfsInv.measure c s0 st3 rch.toNat dsp.toNat ∧
        (dsp.toNat - 1 = 0 → st4.core.tmp_cnt = 0)) ∧ (FullMem c st4 ⋆ R) mj) ?_ ?_
  · rintro _ ⟨failb', ⟨⟩⟩ mj ⟨st4, hbase4, hd4, hmj⟩; scc_steps
    by_cases hinc40 : st4.core.inconsistent = 0#64
    · obtain ⟨hd4', hm4', htop4'⟩ := hd4 hinc40
      exact hJ3 _ (rch, failb', dsp - (1 : BitVec 64), ()) mj hm4' ⟨st4, hbase4, fun _ =>
        ⟨by rw [hdsp_sub], by rwa [hdsp_sub], fun h => htop4' (by rwa [hdsp_sub] at h)⟩, hmj⟩
    · exact hJ3 0 (rch, failb', dsp - (1 : BitVec 64), ()) mj (M6TarjanDfsInv.measure_pos hdsp_pos)
        ⟨st4, hbase4, fun h => absurd h hinc40, hmj⟩
  intro Jpop hPopJ; scc_split
  · have hne_tmk : rlit.toNat ≠ (st3.scratch.tarjan_mark[lit.toNat]?.getD 0#32).toNat := by
      have hne : rlit ≠ st3.scratch.tarjan_mark[lit.toNat]?.getD 0#32 := by
        rw [← htmk_lit_get]; (try rw [← htrc_lit_get]); exact hc
      exact fun heq => hne (BitVec.eq_of_toNat_eq heq)
    obtain ⟨hdsp_gt1, hpop_upd⟩ := m6_tarjan_pop_nonroot (rlit := rlit) hw0 hdm0 hd3 hdsp_pos
      (by rw [← hlit_get]; exact hrlit_eq) (by rw [← hlit_get]; exact hpos_ge)
      (by rw [← hlit_get]; exact hne_tmk)
    have hpar_idx : (dsp - (1 : BitVec 64) - (1 : BitVec 64)).toNat = dsp.toNat - 2 := by
      rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by rw [hdsp_sub]; change 1 ≤ _; omega)),
        hdsp_sub]; rfl
    have hpar_lt_stk : dsp.toNat - 2 < st3.scratch.work_stk2.length := by omega
    have hpar_stk_lt : (dsp - (1 : BitVec 64) - (1 : BitVec 64)).toNat <
        st3.scratch.work_stk2.length := by rw [hpar_idx]; exact hpar_lt_stk
    let par := st3.scratch.work_stk2[(dsp - (1 : BitVec 64) - (1 : BitVec 64)).toNat]'hpar_stk_lt
    have hpar_get : par.toNat = (st3.scratch.work_stk2[dsp.toNat - 2]?.getD 0#32).toNat := by
      dsimp only [par]
      rw [List.getElem?_eq_getElem hpar_lt_stk, Option.getD_some]
      exact congrArg BitVec.toNat (getElem_congr_idx _ _ hpar_idx)
    have hpar_lt_cv : par.toNat < 2 * s0.core.cur_vars := by
      rw [hpar_get]; exact hd3.dv_lt (by omega)
    have hz_par : (BitVec.setWidth 64 par).toNat = par.toNat := zext_toNat par (by decide)
    have hpar_trc_lt : (BitVec.setWidth 64 par).toNat < st3.scratch.tarjan_reach.length := by
      rw [hz_par]; omega
    scc_steps; scc_split
    · have hz_lit_trc_lt : (BitVec.setWidth 64 lit).toNat < st3.scratch.tarjan_reach.length := by
        dsimp only [lit]; rw [htrc_l3]; exact hz_lit_lt
      rw [list_set_getElem_self_eq hz_lit_trc_lt] at hm
      scc_split
      · scc_steps
        have htrc_par_get : st3.scratch.tarjan_reach[(BitVec.setWidth 64 par).toNat]'hpar_trc_lt =
            st3.scratch.tarjan_reach[par.toNat]'(by omega) := getElem_congr_idx _ _ hz_par
        have hlt_par : rlit.toNat <
            (st3.scratch.tarjan_reach[(st3.scratch.work_stk2[dsp.toNat - 2]?.getD
              0#32).toNat]?.getD 0#32).toNat := by
          have h1 := BitVec.lt_def.mp (BitVec.ult_iff_lt.mp hc)
          rw [htrc_lit_get, htrc_par_get] at h1
          rw [← hpar_get, List.getElem?_eq_getElem (by omega), Option.getD_some]
          exact h1
        obtain ⟨hd4, hm4⟩ := hpop_upd true (fun _ => hlt_par) (fun h => by cases h)
        rw [ite_eq_left rfl] at hd4 hm4
        let st4 : FullState := { st3 with scratch := { st3.scratch with
          tarjan_reach := st3.scratch.tarjan_reach.set
            (st3.scratch.work_stk2[dsp.toNat - 2]?.getD 0#32).toNat rlit } }
        have hm4' : (FullMem c st4 ⋆ R) m := by
          dsimp only [st4]; rw [hz_par, hpar_get] at hm; exact hm
        exact hPopJ (failb, ()) m ⟨st4, hd4.toBase, fun _ => ⟨hd4, hm4, fun h => by omega⟩, hm4'⟩
      · have hge_par :
            (st3.scratch.tarjan_reach[(st3.scratch.work_stk2[dsp.toNat - 2]?.getD
              0#32).toNat]?.getD 0#32).toNat ≤ rlit.toNat := by
          have h1 := m6_bv_ult_false_ge hc
          have hgetp : st3.scratch.tarjan_reach[(BitVec.setWidth 64 par).toNat]'hpar_trc_lt =
              st3.scratch.tarjan_reach[par.toNat]'(by omega) := getElem_congr_idx _ _ hz_par
          rw [htrc_lit_get, hgetp] at h1
          rw [← hpar_get, List.getElem?_eq_getElem (by omega), Option.getD_some]
          exact h1
        obtain ⟨hd4, hm4⟩ := hpop_upd false (fun h => by cases h) (fun _ => hge_par)
        rw [ite_eq_right Bool.false_ne_true] at hd4 hm4
        scc_steps
        exact hPopJ (failb, ()) m ⟨st3, hd4.toBase, fun _ => ⟨hd4, hm4, fun h => by omega⟩, hm⟩
  have hr_eq_bv : rlit = st3.scratch.tarjan_mark[lit.toNat]?.getD 0#32 := by
    rw [← htmk_lit_get]; (try rw [← htrc_lit_get]); exact Classical.not_not.mp hc
  have hr_eq : rlit.toNat = (st3.scratch.tarjan_mark[lit.toNat]?.getD 0#32).toNat :=
    congrArg BitVec.toNat hr_eq_bv
  obtain ⟨k0, hk0_lt, hk0_bv, hk0_uniq, hk0_zero, hk0_eqv⟩ :=
    hd3.scc_pop_equiv hw0 hdm0 hdsp_pos
      (by rw [← hlit_get, ← hrlit_eq, ← hr_eq])
      (by rw [← hlit_get]; intro v hv hov
          exact Nat.le_trans (Nat.le_of_eq (hr_eq ▸ hrlit_eq ▸ rfl)) (hscan v hv hov))
  have hmr_reach : reached + (1 : BitVec 32) ≠ 0xFFFFFFFF#32 →
      (∀ j, k0 ≤ j → j < st3.core.tmp_cnt → BinReach (cnfOfClauses F_cur)
        (BitVec.setWidth 32 root).toNat (st3.scratch.work_stk1[j]?.getD 0#32).toNat) ∧
      (∀ l < 2 * st3.core.cur_vars,
        (reached + (1 : BitVec 32)).toNat ≤
          (st3.scratch.tarjan_mark[l]?.getD 0#32).toNat →
        BinReach (cnfOfClauses F_cur) (BitVec.setWidth 32 root).toNat l) := fun _ => by
    rw [hr1_nat, bv32_trunc_toNat (x := root) (by omega)]
    exact ⟨fun j _ hj => hd3.mroot_reach hdsp_pos (st3.scratch.work_stk1[j]?.getD 0#32).toNat
        (hd3.scc_lt j hj) (hd3.scc_tmk_ge j hj).2,
      fun l hl hge => hd3.mroot_reach hdsp_pos l (by omega) hge⟩
  scc_steps
  · refine m6_tarjan_pop_scc_call_wp hPop hw0 hinc30 hdsp_pos hrt_lt hlit_lt hd3 hlit_get
      hk0_lt hk0_bv hk0_uniq hk0_zero hk0_eqv (fun h => absurd rfl h) hm3 (fun b mj h => ?_)
    dsimp only; scc_steps; first | exact h | exact hPopJ (b, ()) mj h
  · refine m6_tarjan_pop_scc_call_wp hPop hw0 hinc30 hdsp_pos hrt_lt hlit_lt hd3 hlit_get
      hk0_lt hk0_bv hk0_uniq hk0_zero hk0_eqv hmr_reach hm3 (fun b mj h => ?_)
    dsimp only; scc_steps; first | exact h | exact hPopJ (b, ()) mj h

theorem full_tarjan_scc_wp (Γ : Env)
    (hPop : ∀ args m Q X, Full.fullTarjanPopSccSpec args m Q X →
      Γ "full_tarjan_pop_scc" [i64, i32, i32, i32] [.bool] args m Q X) :
    ∀ args m Q X, fullTarjanSccSpec args m Q X →
      Func.wp Γ full_tarjan_scc_body args m Q X := fun _ m Q X hs =>
  full_tarjan_scc_fast_wp Γ hPop _ m Q X (fullTarjanSccFastSpec_of_canon hs)

end TarjanSccProof

/-! ## 2. 2-Round `full_substitute_wp` (`Full.fullSubstituteSpec`) -/

section SubstituteProof

open LeanQbe.T.C0HeadStep
open scoped FullArenaTactics FullSubstTactics

private theorem m6_level0_fcur_unsat_of_confl {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hw : Full.FullWitnessInv c F0 F_cur s.core)
    (_hl0 : s.core.cur_level = 0) (hc : Full.FullConflictOkW F_cur s) :
    (cnfOfClauses F_cur).Unsat := by
  rcases hc with ⟨_, h0lt, h1lt, hf0, hf1, hent⟩ | ⟨_, href, hng, hfals⟩
  · refine unsat_of_entails_nil (entails_of_mem_or_false hent fun l hl => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    right; rcases hl with rfl | rfl
    · obtain ⟨i, hi, heq⟩ := (hw.vals_false_iff _ h0lt).mp hf0
      have hs := hw.level0_sound i hi (by have := hw.lvl_le i hi; omega)
      rwa [heq] at hs
    · obtain ⟨i, hi, heq⟩ := (hw.vals_false_iff _ h1lt).mp hf1
      have hs := hw.level0_sound i hi (by have := hw.lvl_le i hi; omega)
      rwa [heq] at hs
  · refine unsat_of_entails_nil
      (entails_of_mem_or_false (hw.arena.entails _ href hng) fun l hl => ?_)
    right
    have hlt := hw.arena.lits_lt _ href hng l hl
    obtain ⟨i, hi, heq⟩ := (hw.vals_false_iff l hlt).mp (hfals l hl)
    have hs := hw.level0_sound i hi (by have := hw.lvl_le i hi; omega)
    rwa [heq] at hs

private theorem m6_level0_unsat_of_confl {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hw : Full.FullWitnessInv c F0 F_cur s.core)
    (hl0 : s.core.cur_level = 0) (hc : Full.FullConflictOkW F_cur s) : F0.Unsat :=
  hw.ext_sound.2 (m6_level0_fcur_unsat_of_confl hw hl0 hc)

private theorem m6SparseInvW_after_bt0 {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s s' : FullState} (hsp : Full.FullSparseInvW c F0 F_cur s)
    (hlen' : s'.LengthsOk c) (hw' : Full.FullWitnessInv c F0 F_cur s'.core)
    (hpres : Full.FullExtScratchPres s s') (hmrk : s'.core.mrk = s.core.mrk)
    (hlm : s'.core.lit_mark = s.core.lit_mark) (har : s'.core.arena = s.core.arena)
    (hal : s'.core.arena_len = s.core.arena_len) (hdm : s'.core.dense_mode = s.core.dense_mode) :
    Full.FullSparseInvW c F0 F_cur s' := by
  refine ⟨hlen', hw',
    ⟨fun v hv => by rw [hmrk]; exact hsp.2.2.1.1 v hv,
     fun l hl => by rw [hlm]; exact hsp.2.2.1.2 l hl⟩, ?_, ?_, hdm.trans hsp.2.2.2.2.2⟩
  · intro r hr hng
    have hr0 : r ∈ fullArenaClauseRefsCore s.core := by
      change r ∈ fullArenaClauseRefsCore s'.core at hr
      unfold fullArenaClauseRefsCore at hr ⊢; rw [har, hal] at hr; exact hr
    have hng0 : fullArenaClauseGarb s r = false := by
      unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore at hng ⊢
      rwa [har] at hng
    have hl : fullArenaClauseLits s' r = fullArenaClauseLits s r := by
      unfold fullArenaClauseLits fullArenaClauseLitsCore fullArenaClauseSizeCore; rw [har]
    rw [hl]; exact hsp.2.2.2.1 r hr0 hng0
  · exact hsp.2.2.2.2.1.of_pres hpres fun ref href => by
      change ref ∈ fullArenaClauseRefsCore s'.core
      unfold fullArenaClauseRefsCore; rw [har, hal]; exact href

private theorem m6SparseInvW_of_perm {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s s' : FullState} (hsp : Full.FullSparseInvW c F0 F_cur s)
    (hlen' : s'.LengthsOk c) (hw' : Full.FullWitnessInv c F0 F_cur s'.core)
    (hperm : Full.FullArenaPermEq s.core s'.core) (hmrk : s'.core.mrk = s.core.mrk)
    (hlm : s'.core.lit_mark = s.core.lit_mark) (hdm : s'.core.dense_mode = s.core.dense_mode)
    (hpres : Full.FullExtScratchPres s s') : Full.FullSparseInvW c F0 F_cur s' := by
  refine ⟨hlen', hw',
    ⟨fun v hv => by rw [hmrk]; exact hsp.2.2.1.1 v hv,
     fun l hl => by rw [hlm]; exact hsp.2.2.1.2 l hl⟩, ?_, ?_, hdm.trans hsp.2.2.2.2.2⟩
  · intro r hr hng
    have hr0 : r ∈ fullArenaClauseRefsCore s.core := by rw [← hperm.2.1]; exact hr
    obtain ⟨_, hgb, hp⟩ := hperm.2.2 r hr0
    exact (hsp.2.2.2.1 r hr0 (hgb.symm.trans hng)).perm (hp.symm.map (· / 2))
  · exact hsp.2.2.2.2.1.of_pres hpres fun r hr => by
      change r ∈ fullArenaClauseRefsCore s'.core; rw [hperm.2.1]; exact hr

private theorem m6SparseInvW_after_sweep {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s s' : FullState} (hsp : Full.FullSparseInvW c F0 F_cur s)
    (hlen' : s'.LengthsOk c) (hw' : Full.FullWitnessInv c F0 F_cur s'.core)
    (hnd' : Full.FullArenaVarsNodup s') (hll' : Full.FullLastLearnedWf s')
    (hext' : s'.scratch.extend_len = s.scratch.extend_len)
    (hmrk : s'.core.mrk = s.core.mrk) (hlm : s'.core.lit_mark = s.core.lit_mark)
    (hdm : s'.core.dense_mode = s.core.dense_mode) : Full.FullSparseInvW c F0 F_cur s' :=
  ⟨hlen', hw',
    ⟨fun v hv => by rw [hmrk]; exact hsp.2.2.1.1 v hv,
     fun l hl => by rw [hlm]; exact hsp.2.2.1.2 l hl⟩,
    hnd', ⟨hll', hext' ▸ hsp.2.2.2.2.1.2⟩, hdm.trans hsp.2.2.2.2.2⟩

theorem full_substitute_wp (Γ : Env)
    (hBacktrack : ∀ a m Q X, fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hTarjan : ∀ a m Q X, fullTarjanSccSpec a m Q X → Γ "full_tarjan_scc" [i64] [i64] a m Q X)
    (hElimVars : ∀ a m Q X, fullSubstElimVarsSpec a m Q X →
      Γ "full_subst_elim_vars" [i64, i64] [.bool] a m Q X)
    (hRewriteBins : ∀ a m Q X, fullSubstRewriteBinsSpec a m Q X →
      Γ "full_subst_rewrite_bins" [i64] [.bool] a m Q X)
    (hRewriteAr : ∀ a m Q X, fullSubstRewriteArSpec a m Q X →
      Γ "full_subst_rewrite_ar" [i64] [.bool] a m Q X)
    (hArenaSweep : ∀ a m Q X, fullArenaSweepSpec a m Q X →
      Γ "full_arena_sweep" [i64] [i64] a m Q X)
    (hProp : ∀ a m Q X, fullPropagateSpec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X) :
    ∀ a m Q X, fullSubstituteSpec a m Q X → Func.wp Γ full_substitute_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, s0, R, rfl, hsp0, hm, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  obtain ⟨F_cur0, hw0⟩ := hsp0.exists_witness
  have hcl0 := hsp0.1.lengths.core_ok
  have hclv_lt : s0.core.cur_level < 2 ^ 64 := by
    have := hw0.2.1.cur_level_le; have := hcl0.trail_end_le; have := hcl0.cur_vars_le; omega
  unfold Func.wp full_substitute_body
  c0_hsteps_nogrp
  refine wp_join_state0 (α := FullState)
    (fun st m1 => Full.FullSparseInv c F0 st ∧ st.core.cur_level = 0 ∧
      st.core.fuel.toNat ≤ s0.core.fuel.toNat ∧ (FullMem c st ⋆ R) m1) ?_ ?_
  · rintro _ st1 m1 ⟨hsp1, hl01, hfl1, hm1⟩
    c0_hsplit
    · c0_hsteps
      exact hQ 1#64 st1 m1 hsp1 hl01 hfl1 (Or.inl rfl) (fun h => by cases h) hm1
    · c0_hsplit
      · c0_hsteps
        exact hQ 1#64 st1 m1 hsp1 hl01 hfl1 (Or.inl rfl) (fun h => by cases h) hm1
      · c0_hsteps_nogrp
        refine wp_while_break_state (α := BitVec 64 × FullState) (β := BitVec 64 × FullState)
          (fun p => (p.1, ()))
          (fun p mb => Full.FullSparseInv c F0 p.2 ∧ p.2.core.cur_level = 0 ∧
            p.2.core.fuel.toNat ≤ s0.core.fuel.toNat ∧ (FullMem c p.2 ⋆ R) mb)
          (fun p => (p.1, ()))
          (fun p => 2 - p.1.toNat)
          (fun p ml => Full.FullSparseInv c F0 p.2 ∧ p.2.core.cur_level = 0 ∧
            p.2.core.fuel.toNat ≤ s0.core.fuel.toNat ∧ p.1.toNat ≤ 2 ∧ (FullMem c p.2 ⋆ R) ml)
          ?_ ?_ ?_
        · rintro _ ⟨_r, stb⟩ mb ⟨hspb, hl0b, hflb, hmb⟩
          c0_hsteps
          exact hQ 1#64 stb mb hspb hl0b hflb (Or.inl rfl) (fun h => by cases h) hmb
        · rintro B L ⟨round, st⟩ ml hB hL ⟨hsp, hl0_st, hfl_st, hr_le, hml⟩
          c0_hsplit
          · have hr_lt : round.toNat < 2 := hc
            have hr1 : (round + 1#64).toNat = round.toNat + 1 := by bv_omega
            c0_hsplit
            · c0_hsplit
              · obtain ⟨F_cur, hspw⟩ := hsp.exists_witness
                c0_hsteps; c0_call hTarjan
                refine ⟨c, F0, F_cur, st, R, rfl, hspw, hl0_st, hml, ?_⟩
                intro ucnt _ _ inc1 _ _ _ _ _ sstk1 _ m1 st1 hspw1 huc_le hus1 hrepr1 hm1
                have hl01' : st1.core.cur_level = 0 := hl0_st
                have hfl1' : st1.core.fuel.toNat ≤ s0.core.fuel.toNat := hfl_st
                c0_hsplit
                · c0_hsteps; exact hQ 20#64 st1 m1 hspw1.toSparse hl01' hfl1' (Or.inr rfl)
                    (fun _ => hspw1.2.1.ext_sound.2 (hspw1.2.1.inconsistent_sound hc)) hm1
                · c0_hsteps; c0_call hElimVars
                  refine ⟨c, F0, F_cur, st1, R, rfl, hspw1, hl01', hrepr1 hc, huc_le, hus1, hm1, ?_⟩
                  intro ok2 st2 m2 hspw2 hl02 _ hfl2 hrepr2 hfail2 hm2
                  have hfl2' : st2.core.fuel.toNat ≤ s0.core.fuel.toNat := by omega
                  c0_hsplit
                  · c0_hsteps_nogrp
                    refine wp_join_group (ts := []) (fun () m_c => m_c = m2) ?_ ?_
                    · rintro _ ⟨⟩ m_c rfl
                      c0_hsteps; c0_call hRewriteBins
                      refine ⟨c, F0, F_cur, st2, R, rfl, hspw2, hl02, hrepr2, hm2, ?_⟩
                      intro ok3 st3 m3 hspw3 hl03 _ hfl3 hrepr3 hfail3 hm3
                      have hfl3' : st3.core.fuel.toNat ≤ s0.core.fuel.toNat := by
                        rw [hfl3]; exact hfl2'
                      c0_hsplit
                      · c0_hsplit
                        · c0_hsteps
                          exact hQ 1#64 st3 m3 hspw3.toSparse hl03 hfl3' (Or.inl rfl)
                            (fun h => by cases h) hm3
                        · c0_hsteps; c0_call hRewriteAr
                          refine ⟨c, F0, F_cur, st3, R, rfl, hspw3, hl03, hrepr3, hm3, ?_⟩
                          intro ok4 st4 m4 hspw4 hl04 _ hfl4 hfail4 hm4
                          have hfl4' : st4.core.fuel.toNat ≤ s0.core.fuel.toNat := hfl4 ▸ hfl3'
                          c0_hsplit
                          · c0_hsplit
                            · c0_hsteps
                              exact hQ 1#64 st4 m4 hspw4.toSparse hl04 hfl4' (Or.inl rfl)
                                (fun h => by cases h) hm4
                            · c0_hsteps; c0_call hArenaSweep
                              refine ⟨c, F0, F_cur, st4, R, rfl, hspw4.1, hspw4.2.1,
                                hspw4.2.2.2.1, hspw4.2.2.2.2.2, fun hpos => by omega,
                                hm4, ?_⟩
                              intro sr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sc5 m5 st5
                                hlen5 _ hext5 _ hll5 hw5 hnd5 _ _ _ hsr2 _ hm5
                              have hspw5 := m6SparseInvW_after_sweep
                                hspw4 hlen5 hw5 hnd5 hll5 hext5 rfl rfl rfl
                              have hl05 : st5.core.cur_level = 0 := hl04
                              c0_hsplit
                              · c0_hsteps
                                exact hQ 20#64 st5 m5 hspw5.toSparse hl05 hfl4' (Or.inr rfl)
                                  (fun _ => (hsr2 hc).2) hm5
                              · c0_hsplit
                                · c0_hsteps
                                  exact hQ 1#64 st5 m5 hspw5.toSparse hl05 hfl4' (Or.inl rfl)
                                    (fun h => by cases h) hm5
                                · c0_hsplit
                                  · c0_hsteps
                                    exact hQ 1#64 st5 m5 hspw5.toSparse hl05 hfl4' (Or.inl rfl)
                                      (fun h => by cases h) hm5
                                  · c0_hsteps; c0_call hProp
                                    refine ⟨c, F0, F_cur, st5, R, rfl, hspw5.1, hspw5.2.1,
                                      hspw5.2.2.2.2.2, hm5, ?_⟩
                                    intro pr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fuel6 _ _ _ _ _ _ _ _
                                      m6 st6 hlen6 hw6 _ hperm6 hfl6 _ _ hpr1 _ _ hm6
                                    have hspw6 := m6SparseInvW_of_perm
                                      hspw5 hlen6 hw6 hperm6 rfl rfl rfl ⟨rfl, rfl⟩
                                    have hfl6' : st6.core.fuel.toNat ≤ s0.core.fuel.toNat := by
                                      have h5 : st5.core.fuel.toNat ≤ s0.core.fuel.toNat := hfl4'
                                      dsimp only [st6]; omega
                                    c0_hsplit
                                    · c0_hsteps
                                      exact hQ 20#64 st6 m6 hspw6.toSparse hl05 hfl6'
                                        (Or.inr rfl) (fun _ =>
                                          m6_level0_unsat_of_confl hw6 hl05 (hpr1 hc).2.2) hm6
                                    · c0_hsteps
                                      exact hL (round + 1#64, st6) m6 (by dsimp only; omega)
                                        ⟨hspw6.toSparse, hl05, hfl6', by dsimp only; omega, hm6⟩
                          · c0_hsteps; exact hQ 20#64 st4 m4 hspw4.toSparse hl04 hfl4' (Or.inr rfl)
                              (fun _ => hfail4 (by
                                cases ok4 <;>
                                  first | rfl | contradiction | exact absurd rfl hc)) hm4
                      · c0_hsteps; exact hQ 20#64 st3 m3 hspw3.toSparse hl03 hfl3' (Or.inr rfl)
                          (fun _ => hfail3 (by
                            cases ok3 <;> first | rfl | contradiction | exact absurd rfl hc)) hm3
                    · intro Jc hJc
                      c0_hsplit
                      · c0_hsplit
                        · c0_hsteps_nogrp
                          first
                          | exact hJc () m2 rfl
                          | exact hB (round, st2) m2 ⟨hspw2.toSparse, hl02, hfl2', hm2⟩
                        · c0_hsteps_nogrp
                          first
                          | exact hJc () m2 rfl
                          | exact hB (round, st2) m2 ⟨hspw2.toSparse, hl02, hfl2', hm2⟩
                      · c0_hsteps_nogrp; exact hJc () m2 rfl
                  · c0_hsteps; exact hQ 20#64 st2 m2 hspw2.toSparse hl02 hfl2' (Or.inr rfl)
                      (fun _ => hfail2 (by
                        cases ok2 <;> first | rfl | contradiction | exact absurd rfl hc)) hm2
              · c0_hsteps; exact hB (round, st) ml ⟨hsp, hl0_st, hfl_st, hml⟩
            · c0_hsteps; exact hB (round, st) ml ⟨hsp, hl0_st, hfl_st, hml⟩
          · c0_hsteps; exact hB (round, st) ml ⟨hsp, hl0_st, hfl_st, hml⟩
        · intro B L _ hL; c0_hsteps
          exact hL (0#64, st1) m1 ⟨hsp1, hl01, hfl1, Nat.zero_le _, hm1⟩
  · intro Jbt hJbt; c0_hsplit
    · c0_hsteps; c0_call hBacktrack
      refine ⟨c, s0, R, rfl, hsp0.1.lengths, hclv_lt, fun _ => by
        have := hw0.2.1.cur_level_le; have := hcl0.trail_end_le; have := hcl0.cur_vars_le; omega,
        hw0.2.1.trail_lits_lt, hm, ?_⟩
      intro _ _ _ _ _ _ _ cl1 _ sc1 m1 st1 hlen1 _ _ hcl1 hprsc1 _ _ _ hw_le _ hm1
      have hw1 := hw_le F0 F_cur0 hw0.2.1 (Nat.zero_le _)
      have hl01 : st1.core.cur_level = 0 := by dsimp only [st1]; rw [hcl1]; simp
      c0_hsteps; exact hJbt st1 m1
        ⟨(m6SparseInvW_after_bt0
          hw0 hlen1 hw1 hprsc1.1 rfl rfl rfl rfl rfl).toSparse,
         hl01, Nat.le_refl _, hm1⟩
    · have hl00 : s0.core.cur_level = 0 := by
        have hnat := congrArg BitVec.toNat hc
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hclv_lt] at hnat; exact hnat
      c0_hsteps; exact hJbt s0 m ⟨hsp0, hl00, Nat.le_refl _, hm⟩

end SubstituteProof

end LeanQbe.T.Examples.Kissat.FullM6CongSubst
