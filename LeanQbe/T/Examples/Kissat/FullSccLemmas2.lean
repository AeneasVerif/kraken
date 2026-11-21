module

public import LeanQbe.T.Examples.Kissat.FullSccLemmas1
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Full` Tarjan SCC & Equivalent Literal Substitution — Part 2 (`Stage 4`)

Proves:
1. Tarjan DFS pure transition lemmas (`tarjan_init_root`, `tarjan_advance_dpos`,
   `tarjan_discover_node`, `tarjan_pop_nonroot`, `tarjan_pop_root_after`).
2. `full_tarjan_scc_wp` (`Full3.lean` #25).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat Kraken.Bedrock2.Test
open FullSccSpecs FullSccHelpers
open scoped FullArenaTactics FullSccTactics

/-! ## 1. Tarjan DFS Pure Step Transition Lemmas (`FullSccHelpers`) -/

namespace FullSccHelpers

section TarjanTransitions

attribute [local grind =] List.getElem?_set_self List.getElem?_set_ne Option.getD_some

variable {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
  {s0 st : FullState} {root mroot reached dsp : Nat}

private theorem getElem_congr_idx {α : Type} {xs : List α} {i j : Nat}
    (hi : i < xs.length) (hj : j < xs.length) (h : i = j) : xs[i] = xs[j] := by subst h; rfl

theorem tarjan_discover_node (hw0 : FullWitnessInv c F0 F_cur s0.core)
    (hdm : s0.core.dense_mode = 0#64)
    (h : TarjanDfsInv c F0 F_cur s0 root mroot reached dsp st)
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
          x = ot.toNat ∨ 1 ≤ (st.scratch.tarjan_mark[x]?.getD 0#32).toNat) :
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
    TarjanDfsInv c F0 F_cur s0 root mroot reached' (dsp + 1) st' ∧
    TarjanDfsInv.measure c s0 st' reached' (dsp + 1) <
      TarjanDfsInv.measure c s0 st reached dsp := by
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
  have hne_rt : ot.toNat ≠ root := fun he => by rw [← he, h0] at h0r; omega
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
  have hinv' : TarjanDfsInv c F0 F_cur s0 root mroot (reached + 1) (dsp + 1) st' := {
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
      dv_trc_eq := fun i hi => by
        dsimp only [st']; by_cases hid : i = dsp; · subst i; grind
        · have := hdv_ne i (by omega); have := h.dv_trc_eq i (by omega); grind
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
            by_cases hxo : x = ot.toNat; · subst hxo; dsimp only [st']; grind
            · dsimp only [st']; rw [List.getElem?_set_ne (Ne.symm hxo)]
              exact (hsok x hx hax).elim (fun he => absurd he hxo) id
          · have hdp_i : (st'.scratch.wsort[i]?.getD 0#32).toNat =
                (st.scratch.wsort[i]?.getD 0#32).toNat := by
              dsimp only [st']
              rw [List.getElem?_set_ne (Ne.symm hid), List.getElem?_set_ne (Ne.symm hip)]
            rw [hdp_i]; obtain ⟨hle, hslc, sc, hseq, hsok⟩ := h.dpos_slice i (by omega)
            refine ⟨hle, hslc, sc, hseq, fun x hx hax => ?_⟩
            by_cases hxo : x = ot.toNat; · subst hxo; dsimp only [st']; grind
            · dsimp only [st']; rw [List.getElem?_set_ne (Ne.symm hxo)]; exact hsok x hx hax
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
  refine ⟨by omega, hinv', ?_⟩; unfold TarjanDfsInv.measure
  have hsum1 : dvWorkSum s0 st' (dsp + 1) =
      dvWorkSum s0 st' dsp + (fullWatchSizeCore s0.core (ot.toNat ^^^ 1) + 1) := by
    conv => lhs; unfold dvWorkSum
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

theorem tarjan_pop_nonroot (h : TarjanDfsInv c F0 F_cur s0 root mroot reached dsp st)
    (hdsp : 0 < dsp) {rlit : BitVec 32}
    (hpos_ge : fullWatchSizeCore s0.core
      ((st.scratch.work_stk2[dsp - 1]?.getD 0#32).toNat ^^^ 1) ≤
      (st.scratch.wsort[dsp - 1]?.getD 0#32).toNat)
    (hr_ge : mroot ≤ rlit.toNat)
    (hr_lt : rlit.toNat <
      (st.scratch.tarjan_mark[(st.scratch.work_stk2[dsp - 1]?.getD 0#32).toNat]?.getD 0#32).toNat)
    (hr_min : ∀ v, activeEdge s0 (st.scratch.work_stk2[dsp - 1]?.getD 0#32).toNat v →
      onScc st v → rlit.toNat ≤ (st.scratch.tarjan_reach[v]?.getD 0#32).toNat)
    (hr_wit : ∃ w < 2 * s0.core.cur_vars, onScc st w ∧
      (st.scratch.tarjan_mark[w]?.getD 0#32).toNat = rlit.toNat ∧
      BinReach (cnfOfClauses F_cur) (st.scratch.work_stk2[dsp - 1]?.getD 0#32).toNat w) :
    let lit := (st.scratch.work_stk2[dsp - 1]?.getD 0#32).toNat
    let st' : FullState := { st with scratch :=
      { st.scratch with tarjan_reach := st.scratch.tarjan_reach.set lit rlit } }
    1 < dsp ∧ TarjanDfsInv c F0 F_cur s0 root mroot reached (dsp - 1) st' ∧
    TarjanDfsInv.measure c s0 st' reached (dsp - 1) <
      TarjanDfsInv.measure c s0 st reached dsp := by
  intro lit st'
  have hlit_lt : lit < 2 * s0.core.cur_vars := h.dv_lt (by omega)
  have htrc_l := h.len_ok.scratch_ok.tarjan_reach_len; have hcv_le := h.len_ok.core_ok.cur_vars_le
  have hcv_eq := h.agrees.get (·.core.cur_vars)
  have hr_lt' : rlit.toNat < (st.scratch.tarjan_mark[lit]?.getD 0#32).toNat := hr_lt
  have hdsp_gt1 : 1 < dsp := Classical.byContradiction fun hle => by
    have h1 : dsp = 1 := by omega
    have h0r := h.dv0_root hdsp; have hl : lit = root := by dsimp only [lit]; rw [h1]; exact h0r.1
    rw [hl, h0r.2.2.1] at hr_lt'; omega
  have hlit_ne_dv : ∀ i < dsp - 1, (st.scratch.work_stk2[i]?.getD 0#32).toNat ≠ lit :=
    fun i hi heq => by
      have hmt := h.dv_tmk_mono i (dsp - 1) hi (by omega); dsimp only [lit] at heq; rw [heq] at hmt
      omega
  have hlit_vis : ∀ v, activeEdge s0 lit v → 1 ≤ (st.scratch.tarjan_mark[v]?.getD 0#32).toNat := by
    intro v hv; obtain ⟨_, _, sc, hseq, hsok⟩ := h.dpos_slice (dsp - 1) (by omega)
    have h0 : fullWatchSizeCore s0.core (lit ^^^ 1) -
        (st.scratch.wsort[dsp - 1]?.getD 0#32).toNat = 0 := by dsimp only [lit]; omega
    rw [h0] at hseq; simp only [sliceBinsFrom, List.append_nil] at hseq
    exact hsok v (hseq ▸ hv.2.2) hv.2.1
  have hr_ne_ff : rlit ≠ 0xFFFFFFFF#32 := fun heq => by
    have hmx := c.hmaxv; unfold dimacsBound at hmx
    have := h.tmk_le lit hlit_lt; have := h.reached_le
    rw [heq] at hr_lt'; revert hr_lt'; simp; omega
  have hndv_old : ∀ u, u ≠ lit → ¬ onDv st' (dsp - 1) u → ¬ onDv st dsp u :=
    fun u hne hnd ⟨i, hi, heq⟩ => by
      by_cases hid : i = dsp - 1; · subst i; exact hne heq.symm
      · exact hnd ⟨i, by omega, heq⟩
  refine ⟨hdsp_gt1, { h with
      agrees := h.agrees.update _
      len_ok := ⟨h.len_ok.core_ok,
        { h.len_ok.scratch_ok with tarjan_reach_len := by simp [st', htrc_l] }⟩
      scc_iff_trc := fun l hl => by
        by_cases hll : l = lit
        · subst hll; have hon := h.dv_on_scc (dsp - 1) (by omega)
          exact ⟨fun _ => ⟨((h.scc_iff_trc lit hl).mp hon).1, by dsimp only [st']; grind⟩,
            fun _ => hon⟩
        · dsimp only [st']; rw [List.getElem?_set_ne (Ne.symm hll)]; exact h.scc_iff_trc l hl
      trc_range := fun i hi => by
        dsimp only [st']; by_cases hxl : (st.scratch.work_stk1[i]?.getD 0#32).toNat = lit
        · rw [hxl, List.getElem?_set_self (by omega), Option.getD_some]; exact ⟨hr_ge, by omega⟩
        · have := h.trc_range i hi; grind
      trc_witness := fun i hi => by
        dsimp only [st']; by_cases hxl : (st.scratch.work_stk1[i]?.getD 0#32).toNat = lit
        · rw [hxl, List.getElem?_set_self (by omega), Option.getD_some]; exact hr_wit
        · rw [List.getElem?_set_ne (Ne.symm hxl)]; exact h.trc_witness i hi
      dsp_le := by dsimp only [st']; have := h.dsp_le; omega
      dv_on_scc := fun i hi => h.dv_on_scc i (by omega)
      dv_tmk_mono := fun i j hij hj => h.dv_tmk_mono i j hij (by omega)
      dv0_root := fun _ => h.dv0_root hdsp
      dv_trc_eq := fun i hi => by
        have := hlit_ne_dv i hi; have := h.dv_trc_eq i (by omega); dsimp only [st']; grind
      dpos_slice := fun i hi => h.dpos_slice i (by omega)
      pop_trc_lt := fun u hu hnd => by
        dsimp only [st']; by_cases hul : u = lit
        · subst hul; rw [List.getElem?_set_self (by omega), Option.getD_some]; exact hr_lt'
        · have := h.pop_trc_lt u hu (hndv_old u hul hnd); grind
      pop_edges_vis := fun u v hu hnd huv => by
        by_cases hul : u = lit; · subst hul; exact hlit_vis v huv
        · exact h.pop_edges_vis u v hu (hndv_old u hul hnd) huv
      pop_trc_fwd := fun u v hu hnd huv hv htlt => by
        dsimp only [st']; by_cases hul : u = lit
        · subst hul; have hnv : v ≠ lit := fun he => by subst he; omega
          have := hr_min v huv hv; grind
        · have hnd0 := hndv_old u hul hnd
          have hnv : v ≠ lit := fun he => by
            subst he; have hmt := h.pop_dv_order u (dsp - 1) hu hnd0 (by omega) huv
            dsimp only [st', lit] at htlt; omega
          have := h.pop_trc_fwd u v hu hnd0 huv hv htlt; grind
      pop_dv_order := fun u i hu hnd hi huv => by
        by_cases hul : u = lit; · subst hul; exact h.dv_tmk_mono i (dsp - 1) hi (by omega)
        · exact h.pop_dv_order u i hu (hndv_old u hul hnd) (by omega) huv
      scc_parent_ge := fun j hj d hd hlt => h.scc_parent_ge j hj d (by omega) hlt
      mroot_reach := fun _ => h.mroot_reach hdsp }, ?_⟩
  have hcongr : dvWorkSum s0 st' (dsp - 1) = dvWorkSum s0 st (dsp - 1) :=
    dvWorkSum_congr (dsp - 1) fun _ _ => ⟨rfl, rfl⟩
  unfold TarjanDfsInv.measure; rw [dvWorkSum_split (st := st) hdsp, hcongr]; omega

theorem tarjan_pop_root_after (h : TarjanDfsInv c F0 F_cur s0 root mroot reached dsp st)
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
    TarjanDfsInv c F0 F_cur s0 root mroot reached (dsp - 1) st' ∧
    TarjanDfsInv.measure c s0 st' reached (dsp - 1) <
      TarjanDfsInv.measure c s0 st reached dsp := by
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
      dv_trc_eq := fun i hi => by
        obtain ⟨j, hj, hje⟩ := hdv_k0 i hi
        simp only [htmk_eq, hdv_eq]; rw [← hje, hkeep j hj, hje]; exact h.dv_trc_eq i (by omega)
      dpos_slice := fun i hi => by
        simp only [htmk_eq, hdv_eq, hdp_eq]; exact h.dpos_slice i (by omega)
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
  unfold TarjanDfsInv.measure; rw [dvWorkSum_split (st := st) hdsp, hcongr]; omega

end TarjanTransitions

/-! ## 2. `full_tarjan_scc` `Func.wp` Proof (`Full3.lean` #25) -/

private theorem dpos_step_nonbin {F_cur : List (List Nat)} {s0 st : FullState}
    {nl off sz pos pos2 : Nat} (hpos_lt : pos < sz) (hpos2 : pos2 = pos + 2)
    (hslc : WatchSliceOk F_cur s0.core nl (off + pos) (sz - pos))
    (hflag0 : (s0.core.wstk[off + pos]?.getD 0#32 &&& 0x80000000#32) = 0#32)
    (hsc : ∃ sc, sliceBinsFrom s0.core.wstk off sz =
        sc ++ sliceBinsFrom s0.core.wstk (off + pos) (sz - pos) ∧
      ∀ x ∈ sc, activeLit s0 x → 1 ≤ (st.scratch.tarjan_mark[x]?.getD 0#32).toNat) :
    pos2 ≤ sz ∧ WatchSliceOk F_cur s0.core nl (off + pos2) (sz - pos2) ∧
    ∃ sc, sliceBinsFrom s0.core.wstk off sz =
        sc ++ sliceBinsFrom s0.core.wstk (off + pos2) (sz - pos2) ∧
      ∀ x ∈ sc, activeLit s0 x → 1 ≤ (st.scratch.tarjan_mark[x]?.getD 0#32).toNat := by
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
      ∀ x ∈ sc, activeLit s0 x → 1 ≤ (st.scratch.tarjan_mark[x]?.getD 0#32).toNat) :
    ∃ w0, s0.core.wstk[off + pos]? = some w0 ∧
      (w0 &&& 0x7FFFFFFF#32).toNat < 2 * s0.core.cur_vars ∧
      (w0 &&& 0x7FFFFFFF#32).toNat ∈ sliceBinsFrom s0.core.wstk off sz ∧
      pos1 ≤ sz ∧ WatchSliceOk F_cur s0.core nl (off + pos1) (sz - pos1) ∧
      ∃ sc, sliceBinsFrom s0.core.wstk off sz =
          sc ++ sliceBinsFrom s0.core.wstk (off + pos1) (sz - pos1) ∧
        ∀ x ∈ sc, activeLit s0 x →
          x = (w0 &&& 0x7FFFFFFF#32).toNat ∨ 1 ≤ (st.scratch.tarjan_mark[x]?.getD 0#32).toNat := by
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

end FullSccHelpers

private theorem bv64_add_toNat {x y : BitVec 64} (h : x.toNat + y.toNat < 2 ^ 64) :
    (x + y).toNat = x.toNat + y.toNat := by rw [BitVec.toNat_add, Nat.mod_eq_of_lt h]
private theorem bv64_add1_toNat {x : BitVec 64} (h : x.toNat + 1 < 2 ^ 64) :
    (x + 1#64).toNat = x.toNat + 1 :=
  (bv64_add_toNat (y := 1#64) (by simpa using h)).trans (by simp)
private theorem bv32_add1_toNat {x : BitVec 32} (h : x.toNat + 1 < 2 ^ 32) :
    (x + 1#32).toNat = x.toNat + 1 := by
  rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl, Nat.mod_eq_of_lt h]
private theorem bv32_add2_toNat {x : BitVec 32} (h : x.toNat + 2 < 2 ^ 32) :
    (x + 2#32).toNat = x.toNat + 2 := by
  rw [BitVec.toNat_add, show (2#32 : BitVec 32).toNat = 2 from rfl, Nat.mod_eq_of_lt h]
private theorem bv_ult_false_ge {w : Nat} {x y : BitVec w} (h : x.ult y = false) :
    y.toNat ≤ x.toNat :=
  Nat.le_of_not_lt fun hlt => by
    have := BitVec.ult_iff_lt.mpr (BitVec.lt_def.mpr hlt); rw [this] at h; cases h

private theorem tarjan_pop_scc_call_wp {Γ : Env} {Q : Post [i64]} {X : XPost}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s0 st3 : FullState}
    {R : Mem 64 → Prop} {m3 : Mem 64} {root dsp : BitVec 64} {reached rch lit mr : BitVec 32}
    {failb : Bool} {k0 : Nat} {Jpop : Cont [.bool]}
    (hPop : ∀ args m Q X, fullTarjanPopSccSpec args m Q X →
      Γ "full_tarjan_pop_scc" [i64, i32, i32, i32] [.bool] args m Q X)
    (hw0 : FullWitnessInv c F0 F_cur s0.core) (hinc30 : st3.core.inconsistent = 0#64)
    (hdsp_pos : 0 < dsp.toNat) (hrt_lt : root.toNat < 2 * s0.core.cur_vars)
    (hlit_lt : lit.toNat < 2 * s0.core.cur_vars)
    (hd3 : TarjanDfsInv c F0 F_cur s0 root.toNat (reached.toNat + 1) rch.toNat dsp.toNat st3)
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
        TarjanDfsInv c F0 F_cur s0 root.toNat (reached.toNat + 1) rch.toNat (dsp.toNat - 1) st4 ∧
        TarjanDfsInv.measure c s0 st4 rch.toNat (dsp.toNat - 1) <
          TarjanDfsInv.measure c s0 st3 rch.toNat dsp.toNat ∧
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
      TarjanDfsInv c F0 F_cur s0 root.toNat (reached.toNat + 1) rch.toNat (dsp.toNat - 1) st4 ∧
      TarjanDfsInv.measure c s0 st4 rch.toNat (dsp.toNat - 1) <
        TarjanDfsInv.measure c s0 st3 rch.toNat dsp.toNat ∧
      (dsp.toNat - 1 = 0 → st4.core.tmp_cnt = 0) := fun h40 => by
    obtain ⟨hset, hkeep⟩ := hinc4_eff h40
    obtain ⟨hd4, hm4_lt⟩ := tarjan_pop_root_after hd3 hdsp_pos hk0_lt
      (by rw [hk0_nat, ← hlit_get]) hag_p htop4 hlen4 h40 hrsz4 hpr4 hus4
      (fun j h1 h2 => (hset j h1 h2).2) (fun l hl hall => (hkeep l (by omega) hall).2)
    exact ⟨hd4, hm4_lt, fun hz => by rw [htop4]; exact hk0_zero (by omega)⟩
  scc_steps
  · exact hPopJ true m4 ⟨st4, hbase4, hd4_fn, hm4⟩
  · exact hPopJ failb m4 ⟨st4, hbase4, hd4_fn, hm4⟩

theorem full_tarjan_scc_wp (Γ : Env)
    (hPop : ∀ args m Q X, fullTarjanPopSccSpec args m Q X →
      Γ "full_tarjan_pop_scc" [i64, i32, i32, i32] [.bool] args m Q X) :
    ∀ args m Q X, fullTarjanSccSpec args m Q X →
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
    have hi1 : (i + 1#64).toNat = i.toNat + 1 := bv64_add1_toNat (by omega)
    scc_steps
    let st1 : FullState :=
      { st with core := { st.core with repr := st.core.repr.set i.toNat 0xFFFFFFFF#32 }
                scratch := { st.scratch with
                  tarjan_mark := st.scratch.tarjan_mark.set i.toNat 0#32
                  tarjan_reach := st.scratch.tarjan_reach.set i.toNat 0#32 } }
    refine hJ (i + 1#64, ()) _ (by dsimp only; omega) ⟨st1, hag.update _,
      ⟨{ hlen.core_ok with repr_len := by simp [st1, hrp_l] },
       { hlen.scratch_ok with
         tarjan_mark_len := by simp [st1, htmk_l], tarjan_reach_len := by simp [st1, htrc_l] }⟩,
      hinc_st, by omega, fun l hl => ?_, hm⟩
    by_cases hli : l = i.toNat
    · subst hli; dsimp only [st1]
      rw [List.getElem?_set_self (by omega), List.getElem?_set_self (by omega),
        List.getElem?_set_self (by omega)]; exact ⟨rfl, rfl, rfl⟩
    · dsimp only [st1]; rw [List.getElem?_set_ne (Ne.symm hli), List.getElem?_set_ne (Ne.symm hli),
        List.getElem?_set_ne (Ne.symm hli)]; exact hinit l (by omega)
  have hi_eq : i.toNat = 2 * s0.core.cur_vars := by have := bv_ult_false_ge hc; omega
  scc_to_group
  refine wp_loop_inv
    (fun (reached, root, ()) ml => ∃ st : FullState,
      root.toNat ≤ 2 * s0.core.cur_vars ∧ TarjanLoopBase c F_cur s0 st ∧
      (st.core.inconsistent = 0#64 →
        st.core.tmp_cnt = 0 ∧ TarjanDfsInv c F0 F_cur s0 0 1 reached.toNat 0 st) ∧
      (FullMem c st ⋆ R) ml)
    (fun (_, root, ()) _ => 2 * s0.core.cur_vars - root.toNat) ?_ ?_
  · intro J2 hJ2; scc_steps
    let st1 : FullState := { st with core := { st.core with tmp_cnt := 0 }
                                     scratch := { st.scratch with res_sz := 0#64 } }
    have hag1 : AgreesExcept tarjanSccMask s0 st1 := hag.update _
    have hlen1 : st1.LengthsOk c :=
      ⟨{ hlen.core_ok with vals_len := hlen.core_ok.vals_len },
       { hlen.scratch_ok with work_stk1_len := hlen.scratch_ok.work_stk1_len }⟩
    have hpr1 : PartialReprInv F_cur st1.core := fun l hl hne => by
      rw [hag1.get (·.core.cur_vars)] at hl; exact absurd (hinit l (by omega)).1 hne
    have hinc_u1 : st1.core.inconsistent ≠ 0#64 → (cnfOfClauses F_cur).Unsat := fun hne => by
      dsimp only [st1] at hne; rw [hinc_st] at hne; exact hw0.inconsistent_sound hne
    have h032 : (0#32 : BitVec 32).toNat = 0 := rfl
    refine hJ2 (0#32, 0#64, ()) _ ⟨st1, Nat.zero_le _,
      ⟨hag1, hlen1, by simp [st1], hpr1, fun _ h => by simp [st1] at h, hinc_u1⟩,
      fun h0 => ⟨rfl, {
        agrees := hag1, len_ok := hlen1, inc0 := h0, rsz_le := by simp [st1]
        partial_repr := hpr1, units_ok := fun _ h => by simp [st1] at h
        reached_le := Nat.zero_le _, top_le := by dsimp only [st1]; omega
        tmk_le := fun l hl => by dsimp only [st1]; rw [(hinit l (by omega)).2.1]; omega
        tmk_inj := fun a _ ha _ hp => by
          dsimp only [st1] at hp; rw [(hinit a (by omega)).2.1] at hp; omega
        tmk_surj := by omega
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
        dv_trc_eq := by omega, dpos_slice := by omega, scc_parent_ge := by omega
        mroot_reach := by omega
        pop_trc_lt := fun _ ⟨_, h, _⟩ => by dsimp only [st1] at h; omega
        pop_edges_vis := fun _ _ ⟨_, h, _⟩ => by dsimp only [st1] at h; omega
        pop_trc_fwd := fun _ _ ⟨_, h, _⟩ => by dsimp only [st1] at h; omega
        pop_dv_order := fun _ _ ⟨_, h, _⟩ => by dsimp only [st1] at h; omega }⟩, hm⟩
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
        (∀ l < idx.toNat, st4.core.repr[l]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32) ∧
        (FullMem c st4 ⋆ R) mk)
      (fun (idx, ()) _ => 2 * s0.core.cur_vars - idx.toNat) ?_ ?_
    · intro J4 hJ4; scc_steps
      exact hJ4 (0#64, ()) mj ⟨stf, hagf, hlenf, rfl, rfl, rfl, Nat.zero_le _, hprf,
        fun _ h => by simp at h, hmj⟩
    rintro J4 ⟨idx, ⟨⟩⟩ mk ⟨st4, hag4, hlen4, hinc4, hrsz4, hsh4, hidx_le, hpr4, hfill4, hmk⟩ hJ4
    have hrp4 := hlen4.core_ok.repr_len; have hcv4 := hag4.get (·.core.cur_vars)
    scc_split
    · have hidx_lt : idx.toNat < 2 * s0.core.cur_vars := by
        have := BitVec.lt_def.mp (BitVec.ult_iff_lt.mp hc); rwa [hnl_eq] at this
      have hidx1 : (idx + 1#64).toNat = idx.toNat + 1 := bv64_add1_toNat (by omega)
      have hidx_lt32 : idx.toNat < 2 ^ 32 := by omega
      scc_steps
      · let st5 : FullState := { st4 with core := { st4.core with
            repr := st4.core.repr.set idx.toNat (BitVec.setWidth 32 idx) } }
        have hpr5 : PartialReprInv F_cur st5.core := fun l hl hne => by
          dsimp only [st5] at hl ⊢; by_cases hli : l = idx.toNat
          · subst hli; rw [List.getElem?_set_self (by omega), Option.getD_some,
              bv32_trunc_toNat hidx_lt32]; exact ⟨by omega, LitEquiv.refl _ _⟩
          · rw [List.getElem?_set_ne (Ne.symm hli)] at hne ⊢; exact hpr4 l hl hne
        have hfill5 : ∀ l < (idx + 1#64).toNat,
            st5.core.repr[l]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := fun l hl => by
          dsimp only [st5]; by_cases hli : l = idx.toNat
          · subst hli; rw [List.getElem?_set_self (by omega), Option.getD_some]; intro heq
            have := congrArg BitVec.toNat heq; rw [bv32_trunc_toNat hidx_lt32] at this
            revert this; simp; omega
          · rw [List.getElem?_set_ne (Ne.symm hli)]; exact hfill4 l (by omega)
        exact hJ4 (idx + 1#64, ()) _ (by dsimp only; omega)
          ⟨st5, hag4.update _,
           ⟨{ hlen4.core_ok with repr_len := by simp [st5, hrp4] }, hlen4.scratch_ok⟩,
           hinc4, hrsz4, hsh4, by omega, hpr5, hfill5, hm⟩
      · have hne_idx : st4.core.repr[idx.toNat]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := by
          rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; assumption
        exact hJ4 (idx + 1#64, ()) _ (by dsimp only; omega)
          ⟨st4, hag4, hlen4, hinc4, hrsz4, hsh4, by omega, hpr4, fun l hl => by
            by_cases hli : l = idx.toNat; · subst hli; exact hne_idx
            · exact hfill4 l (by omega), hmk⟩
    · have hidx_eq : idx.toNat = 2 * s0.core.cur_vars := by have := bv_ult_false_ge hc; omega
      scc_steps
      have hsp4 := tarjanScc_preserves_sparse hsp0 hag4 hlen4 (fun h => hincf (hinc4 ▸ h))
      have hrepr4 : FullReprEquiv F_cur st4 := fun l hl => by
        have hget : st4.core.repr[l]?.getD 0#32 = st4.core.repr[l]?.getD 0xFFFFFFFF#32 := by
          rw [List.getElem?_eq_getElem (by omega), Option.getD_some, Option.getD_some]
        obtain ⟨hr_lt, h1, h2⟩ := hpr4 l hl (hfill4 l (by omega))
        rw [hget]; exact ⟨hr_lt, h2, h1⟩
      have hus4 : ∀ k < st4.scratch.res_sz.toNat,
          (st4.scratch.shrink_stk[k]?.getD 0#32).toNat < 2 * s0.core.cur_vars ∧
          (cnfOfClauses F_cur).EntailsClause
            (cnfClause [(st4.scratch.shrink_stk[k]?.getD 0#32).toNat]) := fun k hk => by
        rw [hrsz4] at hk; rw [hsh4]; have := husf k hk
        rwa [hagf.get (·.core.cur_vars)] at this
      have heq4 := agrees_tarjanSccMask_eq hag4
      exact hQ st4.scratch.res_sz st4.core.repr st4.core.tmp_cnt st4.core.inconsistent
        st4.scratch.tarjan_mark st4.scratch.tarjan_reach st4.scratch.work_stk1 st4.scratch.work_stk2
        st4.scratch.wsort st4.scratch.shrink_stk st4.scratch.res_sz mk
        (heq4.symm ▸ hsp4) (by rw [hrsz4]; exact hrszf) hus4
        (fun _ => heq4.symm ▸ hrepr4) (heq4.symm ▸ hmk)
  intro Jexit hExit; scc_split; rotate_left
  · scc_steps; exact hExit () ml ⟨st, ⟨hag, hlen, hrsz, hpr, hus, hinc_u⟩, hml⟩
  have hrt_lt : root.toNat < 2 * s0.core.cur_vars := by
    have := BitVec.lt_def.mp (BitVec.ult_iff_lt.mp hc); rwa [hnl_eq] at this
  have hrt1 : (root + 1#64).toNat = root.toNat + 1 := bv64_add1_toNat (by omega)
  scc_split; rotate_left
  · scc_steps; exact hExit () ml ⟨st, ⟨hag, hlen, hrsz, hpr, hus, hinc_u⟩, hml⟩
  have hst_inc0 : st.core.inconsistent = 0#64 := hc; obtain ⟨htop0, hdfs⟩ := hinc_dfs hst_inc0
  scc_to_group
  refine wp_join_group (ts := [i32])
    (fun (rch', ()) mj => ∃ st' : FullState, TarjanLoopBase c F_cur s0 st' ∧
      (st'.core.inconsistent = 0#64 →
        st'.core.tmp_cnt = 0 ∧ TarjanDfsInv c F0 F_cur s0 0 1 rch'.toNat 0 st') ∧
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
  have hr1_nat : (reached + (1 : BitVec 32)).toNat = reached.toNat + 1 := bv32_add1_toNat (by omega)
  have hrt32_eq : BitVec.setWidth 32 root = BitVec.ofNat 32 root.toNat :=
    BitVec.eq_of_toNat_eq (by
      rw [bv32_trunc_toNat (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])
  have hr32_eq : reached + (1 : BitVec 32) = BitVec.ofNat 32 (reached.toNat + 1) :=
    BitVec.eq_of_toNat_eq (by rw [hr1_nat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])
  have hinit_dfs := tarjan_init_root hw0 hdm0 hdfs htop0 hact_rt htmk_rt0
  have hpos_mv : 0 < 2 * c.max_vars := by omega
  scc_to_group
  refine wp_loop_group (ts := [i32, .bool, i64])
    (fun n (rch, _failb, dsp, ()) m3 => ∃ st3 : FullState, TarjanLoopBase c F_cur s0 st3 ∧
      (st3.core.inconsistent = 0#64 →
        n = TarjanDfsInv.measure c s0 st3 rch.toNat dsp.toNat ∧
        TarjanDfsInv c F0 F_cur s0 root.toNat (reached.toNat + 1) rch.toNat dsp.toNat st3 ∧
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
      have := bv_ult_false_ge hc; rw [show (0 : BitVec 64).toNat = 0 from rfl] at this; omega
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
    (bv64_add1_toNat (by rw [hnl2]; omega)).trans (by rw [hnl2])
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
  scc_split
  · have hpos_lt : pos32.toNat < wsz := by
      rw [← hsz_get]; exact BitVec.lt_def.mp (BitVec.ult_iff_lt.mp hc)
    have hidx_eq : (BitVec.setWidth 64 off32 + BitVec.setWidth 64 pos32).toNat =
        woff + pos32.toNat := by
      rw [bv64_add_toNat (by rw [zext_toNat _ (by decide), zext_toNat _ (by decide)]; omega),
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
      have hp2 : (pos32 + (2 : BitVec 32)).toNat = pos32.toNat + 2 := bv32_add2_toNat (by omega)
      have hslc_nb := dpos_step_nonbin hpos_lt hp2 (hpos_get ▸ hslc3.2.1)
        hflag0 (hpos_get ▸ hslc3.2.2)
      obtain ⟨hd4, hmeas4⟩ := tarjan_advance_dpos (pos' := pos32 + (2 : BitVec 32)) hd3 hdsp_pos
        (by rw [← hpos_get, hp2]; omega) (by rw [← hlit_get]; exact hslc_nb)
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
    have hp1 : (pos32 + (1 : BitVec 32)).toNat = pos32.toNat + 1 := bv32_add1_toNat (by omega)
    obtain ⟨w0, hw0_eq, hot_lt, hbins_ot, hslc_b1⟩ :=
      dpos_step_bin hpos_lt hp1 (hpos_get ▸ hslc3.2.1) hflag1 (hpos_get ▸ hslc3.2.2)
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
        TarjanDfsInv c F0 F_cur s0 root.toNat (reached.toNat + 1) rch'.toNat dsp'.toNat st4 ∧
        TarjanDfsInv.measure c s0 st4 rch'.toNat dsp'.toNat <
          TarjanDfsInv.measure c s0 st3 rch.toNat dsp.toNat ∧ (FullMem c st4 ⋆ R) mj) ?_ ?_
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
        1 ≤ (st3.scratch.tarjan_mark[ot.toNat]?.getD 0#32).toNat) →
        TarjanDfsInv c F0 F_cur s0 root.toNat (reached.toNat + 1) rch.toNat dsp.toNat st3a ∧
        TarjanDfsInv.measure c s0 st3a rch.toNat dsp.toNat <
          TarjanDfsInv.measure c s0 st3 rch.toNat dsp.toNat := by
      intro hsk; obtain ⟨hle, hslc, sc, hseq, hsok⟩ := hslc_b1
      exact tarjan_advance_dpos (pos' := pos32 + (1 : BitVec 32)) hd3 hdsp_pos
        (by rw [← hpos_get, hp1]; omega)
        (by rw [← hlit_get]; refine ⟨hle, hslc, sc, hseq, fun x hx hax => ?_⟩
            rcases hsok x hx hax with rfl | hpos
            · exact hsk.elim (fun hna => absurd hax hna) id
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
    dsimp only [off32, pos32, lit] at hflag_ot htmk_ot
    scc_split; rotate_left
    · exfalso; rw [hw0_get] at hc; have := bv_ult_false_ge hc; rw [hnl_eq, hz_ot] at this; omega
    scc_split; rotate_left
    · have hna : ¬ activeLit s0 ot.toNat := fun hact => hact.2 (by
        rw [← hfl3, List.getElem?_eq_getElem (by omega), Option.getD_some]
        dsimp only [st3a] at hc; rw [hflag_ot] at hc; exact Classical.not_not.mp hc)
      obtain ⟨hd4, hm4⟩ := hskip_ok (Or.inl hna)
      scc_steps; exact hJb (rch, dsp, ()) m ⟨st3a, hdsp_pos, hd4, hm4, hma⟩
    have hact_ot : activeLit s0 ot.toNat := ⟨hot_lt', by
      rw [← hfl3, List.getElem?_eq_getElem (by omega), Option.getD_some]
      dsimp only [st3a] at hc; rw [hflag_ot] at hc; exact hc⟩
    scc_split; rotate_left
    · have htmk_pos : 1 ≤ (st3.scratch.tarjan_mark[ot.toNat]?.getD 0#32).toNat := by
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
        dsimp only [st3a] at hc; rw [htmk_ot] at hc
        exact Nat.pos_of_ne_zero fun h0 => hc (BitVec.eq_of_toNat_eq (by simpa using h0))
      obtain ⟨hd4, hm4⟩ := hskip_ok (Or.inr htmk_pos)
      scc_steps; exact hJb (rch, dsp, ()) m ⟨st3a, hdsp_pos, hd4, hm4, hma⟩
    have htmk_ot0 : (st3.scratch.tarjan_mark[ot.toNat]?.getD 0#32).toNat = 0 := by
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      dsimp only [st3a] at hc; rw [htmk_ot] at hc; rw [hc]; rfl
    have hr_lt3 := hd3.reached_lt_of_unvisited hot_lt' htmk_ot0
    have htop_lt3 : st3.core.tmp_cnt < 2 * s0.core.cur_vars := by have := hd3.top_le; omega
    have hdsp_lt3' : dsp.toNat < 2 * s0.core.cur_vars := by have := hd3.dsp_le; omega
    have hr1_3 : (rch + (1 : BitVec 32)).toNat = rch.toNat + 1 := bv32_add1_toNat (by omega)
    have hr32_3 : rch + (1 : BitVec 32) = BitVec.ofNat 32 (rch.toNat + 1) :=
      BitVec.eq_of_toNat_eq (by rw [hr1_3, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])
    have hdsp1 : (dsp + (1 : BitVec 64)).toNat = dsp.toNat + 1 := bv64_add1_toNat (by omega)
    have htc_mod : (BitVec.ofNat 64 st3.core.tmp_cnt).toNat = st3.core.tmp_cnt := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have htc_mod_a : (BitVec.ofNat 64 st3a.core.tmp_cnt).toNat = st3.core.tmp_cnt := htc_mod
    have htc1_a : (BitVec.ofNat 64 st3a.core.tmp_cnt + (1 : BitVec 64)).toNat =
        st3.core.tmp_cnt + 1 := (bv64_add1_toNat (by rw [htc_mod_a]; omega)).trans (by
          rw [htc_mod_a])
    obtain ⟨_, hdisc, hm_disc⟩ := tarjan_discover_node hw0 hdm0 hd3 hdsp_pos
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
      have hot_eq : (st3.core.wstk[(BitVec.setWidth 64 off32 +
          BitVec.setWidth 64 pos32).toNat]'hidx_lt &&& (2147483647 : BitVec 32)) = ot := by
        dsimp only [off32, pos32, lit]; rw [hw0_get]
      dsimp only [off32, pos32, lit] at hot_eq; dsimp only [st4, st3a] at hm ⊢
      rw [hot_eq, hz_ot, hr32_3, htc1_a, htc_mod_a] at hm; exact hm
    exact hJb (rch + (1 : BitVec 32), dsp + (1 : BitVec 64), ()) m
      ⟨st4, by rw [hdsp1]; omega, by rw [hr1_3, hdsp1]; exact hdisc,
       by rw [hr1_3, hdsp1]; exact hm_disc, hm_d⟩
  have hpos_ge : wsz ≤ (st3.scratch.wsort[dsp.toNat - 1]?.getD 0#32).toNat := by
    rw [← hpos_get, ← hsz_get]; exact bv_ult_false_ge hc
  have hlit_vis : ∀ v, activeEdge s0 lit.toNat v →
      1 ≤ (st3.scratch.tarjan_mark[v]?.getD 0#32).toNat := by
    intro v hv; obtain ⟨_, _, sc, hseq, hsok⟩ := hslc3
    have h0 : wsz - (st3.scratch.wsort[dsp.toNat - 1]?.getD 0#32).toNat = 0 := by omega
    rw [h0] at hseq; simp only [sliceBinsFrom, List.append_nil] at hseq
    exact hsok v (hseq ▸ hv.2.2) hv.2.1
  have hlit_tmk_eq : (st3.scratch.tarjan_reach[lit.toNat]?.getD 0#32).toNat =
      (st3.scratch.tarjan_mark[lit.toNat]?.getD 0#32).toNat := by
    have := hd3.dv_trc_eq (dsp.toNat - 1) (by omega); rwa [← hlit_get] at this
  have hlit_mroot : reached.toNat + 1 ≤ (st3.scratch.tarjan_mark[lit.toNat]?.getD 0#32).toNat := by
    obtain ⟨j, hj, hje⟩ := hd3.dv_on_scc (dsp.toNat - 1) (by omega)
    rw [← hlit_get] at hje; have := (hd3.scc_tmk_ge j hj).2; rwa [hje] at this
  have hz_lit : (BitVec.setWidth 64 lit).toNat = lit.toNat := zext_toNat lit (by decide)
  have hz_lit_u : (BitVec.setWidth 64
      (st3.scratch.work_stk2[(dsp - (1 : BitVec 64)).toNat]'(by rw [hdsp_sub]; omega))).toNat =
      lit.toNat := hz_lit
  have hz_lit_lt : (BitVec.setWidth 64
      (st3.scratch.work_stk2[(dsp - (1 : BitVec 64)).toNat]'(by rw [hdsp_sub]; omega))).toNat <
      2 * c.max_vars := by rw [hz_lit_u]; omega
  scc_to_group
  refine wp_loop_inv
    (fun (p, rlit, ()) mp => m3 = mp ∧ p.toNat ≤ wsz ∧
      WatchSliceOk F_cur s0.core (lit.toNat ^^^ 1) (woff + p.toNat) (wsz - p.toNat) ∧
      reached.toNat + 1 ≤ rlit.toNat ∧
      rlit.toNat ≤ (st3.scratch.tarjan_mark[lit.toNat]?.getD 0#32).toNat ∧
      (rlit.toNat < (st3.scratch.tarjan_mark[lit.toNat]?.getD 0#32).toNat →
        ∃ w < 2 * s0.core.cur_vars, onScc st3 w ∧
          (st3.scratch.tarjan_mark[w]?.getD 0#32).toNat = rlit.toNat ∧
          BinReach (cnfOfClauses F_cur) lit.toNat w) ∧
      ∃ sc, sliceBinsFrom s0.core.wstk woff wsz =
        sc ++ sliceBinsFrom s0.core.wstk (woff + p.toNat) (wsz - p.toNat) ∧
        ∀ ot ∈ sc, activeLit s0 ot → onScc st3 ot →
          rlit.toNat ≤ (st3.scratch.tarjan_reach[ot]?.getD 0#32).toNat)
    (fun (p, _, ()) _ => wsz - p.toNat) ?_ ?_
  · intro Jp hJp; scc_steps
    have htrc_get :
        st3.scratch.tarjan_reach[(BitVec.setWidth 64 lit).toNat]'(by rw [hz_lit]; omega) =
        st3.scratch.tarjan_reach[lit.toNat]?.getD 0#32 := by
      have hlt : lit.toNat < st3.scratch.tarjan_reach.length := by omega
      simp only [hz_lit, List.getElem?_eq_getElem hlt, Option.getD_some]
    dsimp only [lit] at htrc_get
    exact hJp (0#32, _, ()) m3 ⟨rfl, Nat.zero_le _, by
        rw [show (0#32 : BitVec 32).toNat = 0 from rfl, Nat.add_zero, Nat.sub_zero]
        exact hwat0.slices _ hnl_lt_nat,
      by rw [htrc_get, hlit_tmk_eq]; exact hlit_mroot,
      by rw [htrc_get, hlit_tmk_eq]; exact Nat.le_refl _,
      fun hlt => by rw [htrc_get, hlit_tmk_eq] at hlt; omega,
      [], by simp, fun _ hm => nomatch hm⟩
  rintro Jp ⟨p, rlit, ⟨⟩⟩ mp ⟨rfl, hp_le, hslc_p, hr_ge, hr_le, hr_wit, sc, hseq, hsok⟩ hJp
  scc_split
  · have hp_lt : p.toNat < wsz := by
      rw [← hsz_get]; exact BitVec.lt_def.mp (BitVec.ult_iff_lt.mp hc)
    have hidx_eq : (BitVec.setWidth 64 off32 + BitVec.setWidth 64 p).toNat = woff + p.toNat := by
      rw [bv64_add_toNat (by rw [zext_toNat _ (by decide), zext_toNat _ (by decide)]; omega),
        zext_toNat _ (by decide), zext_toNat _ (by decide), hoff_get]
    have hidx_lt : (BitVec.setWidth 64 off32 + BitVec.setWidth 64 p).toNat <
        st3.core.wstk.length := by rw [hidx_eq]; omega
    have hidx_lt_u : (BitVec.setWidth 64 off32 + BitVec.setWidth 64 p).toNat < c.wcap := by
      rw [hidx_eq]; omega
    dsimp only [off32, lit] at hidx_lt_u
    scc_split
    · have hflag0 : (s0.core.wstk[woff + p.toNat]?.getD 0#32 &&& 0x80000000#32) = 0#32 := by
        rw [← hws3, List.getElem?_eq_getElem (by omega), Option.getD_some]
        dsimp only [off32, lit] at hidx_eq; simp only [hidx_eq] at hc; exact hc
      obtain ⟨_, _, h2le, _, _, _, _, _, hrest, hbins_eq⟩ :=
        watchSlice_step_nonbin hslc_p (by omega) hflag0
      have hp2 : (p + (2 : BitVec 32)).toNat = p.toNat + 2 := bv32_add2_toNat (by omega)
      scc_steps; exact hJp (p + (2 : BitVec 32), rlit, ()) m3 (by dsimp only; omega)
        ⟨rfl, by omega, by rw [hp2, ← Nat.add_assoc, Nat.sub_add_eq]; exact hrest, hr_ge, hr_le,
         hr_wit, sc, by rw [hseq, hbins_eq, hp2, ← Nat.add_assoc, Nat.sub_add_eq], hsok⟩
    have hflag1 : (s0.core.wstk[woff + p.toNat]?.getD 0#32 &&& 0x80000000#32) ≠ 0#32 := by
      rw [← hws3, List.getElem?_eq_getElem (by omega), Option.getD_some]
      dsimp only [off32, lit] at hidx_eq; simp only [hidx_eq] at hc; exact hc
    obtain ⟨w0, hw0_eq, _, _, hot_lt, _, hrest, hbins_eq⟩ :=
      watchSlice_step_bin hslc_p (by omega) hflag1
    have hw0_get : st3.core.wstk[(BitVec.setWidth 64 off32 +
        BitVec.setWidth 64 p).toNat]'hidx_lt = w0 := by
      have h1 := hw0_eq; rw [← hws3, List.getElem?_eq_getElem (by omega)] at h1
      simpa only [hidx_eq] using Option.some.inj h1
    dsimp only [off32, lit] at hw0_get
    let ot := w0 &&& (2147483647 : BitVec 32)
    have hot_lt' : ot.toNat < 2 * s0.core.cur_vars := hot_lt
    have hz_ot : (BitVec.setWidth 64 ot).toNat = ot.toNat := zext_toNat ot (by decide)
    have hdiv_ot : (BitVec.setWidth 64 (ot >>> (BitVec.toNat (1 : BitVec 32) % 32))).toNat =
        ot.toNat / 2 := by
      rw [zext_toNat _ (by decide), show BitVec.toNat (1 : BitVec 32) % 32 = 1 from rfl,
        FullSccTactics.bv32_ushr1_nat]
    have hot_z_lt : (BitVec.setWidth 64 (st3.core.wstk[(BitVec.setWidth 64 off32 +
        BitVec.setWidth 64 p).toNat]'hidx_lt &&& (2147483647 : BitVec 32))).toNat <
        2 * c.max_vars := by
      dsimp only [off32, lit]; rw [hw0_get]; change (BitVec.setWidth 64 ot).toNat < _
      rw [hz_ot]; omega
    have hot_div_lt : (BitVec.setWidth 64 ((st3.core.wstk[(BitVec.setWidth 64 off32 +
        BitVec.setWidth 64 p).toNat]'hidx_lt &&& (2147483647 : BitVec 32)) >>>
          (BitVec.toNat (1 : BitVec 32) % 32))).toNat < c.max_vars := by
      dsimp only [off32, lit]; rw [hw0_get]
      change (BitVec.setWidth 64 (ot >>> (BitVec.toNat (1 : BitVec 32) % 32))).toNat < _
      rw [hdiv_ot]; omega
    have hflag_ot : st3.core.flags[(BitVec.setWidth 64 ((st3.core.wstk[(BitVec.setWidth 64 off32 +
        BitVec.setWidth 64 p).toNat]'hidx_lt &&& (2147483647 : BitVec 32)) >>>
          (BitVec.toNat (1 : BitVec 32) % 32))).toNat]'(
            by rw [hfl_l3]; dsimp only [off32, lit]; exact hot_div_lt) =
        st3.core.flags[ot.toNat / 2]'(by omega) :=
      getElem_congr_idx _ _ (by dsimp only [off32, lit]; rw [hw0_get]; exact hdiv_ot)
    have htrc_ot : st3.scratch.tarjan_reach[(BitVec.setWidth 64 (st3.core.wstk[(BitVec.setWidth 64
        off32 + BitVec.setWidth 64 p).toNat]'hidx_lt &&& (2147483647 : BitVec 32))).toNat]'(
          by rw [htrc_l3]; dsimp only [off32, lit]; exact hot_z_lt) =
        st3.scratch.tarjan_reach[ot.toNat]'(by omega) :=
      getElem_congr_idx _ _ (by dsimp only [off32, lit]; rw [hw0_get]; exact hz_ot)
    dsimp only [off32, lit] at hot_z_lt hot_div_lt hflag_ot htrc_ot
    have hp1 : (p + (1 : BitVec 32)).toNat = p.toNat + 1 := bv32_add1_toNat (by omega)
    have hbins_ot : ot.toNat ∈ sliceBinsFrom s0.core.wstk woff wsz := by
      rw [hseq, hbins_eq, List.mem_append, List.mem_cons]; exact Or.inr (Or.inl rfl)
    have hstep_rlit : ∀ (rlit' : BitVec 32), rlit'.toNat ≤ rlit.toNat →
        reached.toNat + 1 ≤ rlit'.toNat →
        (rlit'.toNat < (st3.scratch.tarjan_mark[lit.toNat]?.getD 0#32).toNat →
          ∃ w < 2 * s0.core.cur_vars, onScc st3 w ∧
            (st3.scratch.tarjan_mark[w]?.getD 0#32).toNat = rlit'.toNat ∧
            BinReach (cnfOfClauses F_cur) lit.toNat w) →
        (activeLit s0 ot.toNat → onScc st3 ot.toNat →
          rlit'.toNat ≤ (st3.scratch.tarjan_reach[ot.toNat]?.getD 0#32).toNat) →
        Jp (p + (1 : BitVec 32), rlit', ()) m3 := fun rlit' h1 h2 hw1 hot1 =>
      hJp (p + (1 : BitVec 32), rlit', ()) m3 (by dsimp only; omega)
        ⟨rfl, by omega, by rw [hp1, ← Nat.add_assoc, Nat.sub_add_eq]; exact hrest, h2, by omega,
         hw1, sc ++ [ot.toNat],
         by rw [hseq, hbins_eq, List.append_assoc, List.singleton_append, hp1, ← Nat.add_assoc,
              Nat.sub_add_eq]; rfl,
         fun x hx hax hox => by
           rcases List.mem_append.mp hx with ha | hb
           · exact Nat.le_trans h1 (hsok x ha hax hox)
           · simp only [List.mem_singleton] at hb; subst hb; exact hot1 hax hox⟩
    scc_to_group; scc_step; scc_split; rotate_left
    · exfalso; rw [hw0_get] at hc; have := bv_ult_false_ge hc; rw [hnl_eq, hz_ot] at this; omega
    scc_split; rotate_left
    · have hna : ¬ activeLit s0 ot.toNat := fun hact => hact.2 (by
        rw [← hfl3, List.getElem?_eq_getElem (by omega), Option.getD_some]
        rw [hflag_ot] at hc; exact Classical.not_not.mp hc)
      scc_steps; exact hstep_rlit rlit (Nat.le_refl _) hr_ge hr_wit (fun ha _ => absurd ha hna)
    have hact_ot : activeLit s0 ot.toNat := ⟨hot_lt', by
      rw [← hfl3, List.getElem?_eq_getElem (by omega), Option.getD_some]
      rw [hflag_ot] at hc; exact hc⟩
    scc_split; rotate_left
    · have hge : rlit.toNat ≤ (st3.scratch.tarjan_reach[ot.toNat]?.getD 0#32).toNat := by
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; rw [htrc_ot] at hc
        exact bv_ult_false_ge hc
      scc_steps; exact hstep_rlit rlit (Nat.le_refl _) hr_ge hr_wit (fun _ _ => hge)
    have htrc_lt : (st3.scratch.tarjan_reach[ot.toNat]?.getD 0#32).toNat < rlit.toNat := by
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; rw [htrc_ot] at hc
      exact BitVec.lt_def.mp (BitVec.ult_iff_lt.mp hc)
    have hot_vis := hlit_vis ot.toNat ⟨hlit_act, hact_ot, hbins_ot⟩
    have htrc_ne_ff : st3.scratch.tarjan_reach[ot.toNat]?.getD 0#32 ≠ 0xFFFFFFFF#32 := fun heq => by
      have := hd3.tmk_le lit.toNat hlit_lt; have := hd3.reached_le
      rw [heq] at htrc_lt; revert htrc_lt; simp; omega
    obtain ⟨jot, hjot, hjoteq⟩ := (hd3.scc_iff_trc ot.toNat hot_lt').mpr ⟨hot_vis, htrc_ne_ff⟩
    have hot_rng := hd3.trc_range jot hjot; rw [hjoteq] at hot_rng
    obtain ⟨w, hw_lt, hwon, hwtmk, hwbr⟩ := hd3.trc_witness jot hjot; rw [hjoteq] at hwtmk hwbr
    scc_steps; rw [htrc_ot]
    have htrc_some : st3.scratch.tarjan_reach[ot.toNat]'(by omega) =
        st3.scratch.tarjan_reach[ot.toNat]?.getD 0#32 := by
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    rw [htrc_some]
    exact hstep_rlit _ (by omega) hot_rng.1
      (fun _ => ⟨w, hw_lt, hwon, hwtmk, binReach_trans
        (BinReach.step (activeEdge_binEdge hw0 hdm0 ⟨hlit_act, hact_ot, hbins_ot⟩)
          (BinReach.refl _)) hwbr⟩) (fun _ _ => Nat.le_refl _)
  have hp_eq : p.toNat = wsz := by have := bv_ult_false_ge hc; rw [hsz_get] at this; omega
  have hscan : ∀ v, activeEdge s0 lit.toNat v → onScc st3 v →
      rlit.toNat ≤ (st3.scratch.tarjan_reach[v]?.getD 0#32).toNat := by
    intro v hv hov; have h0 : wsz - p.toNat = 0 := by omega
    rw [h0] at hseq; simp only [sliceBinsFrom, List.append_nil] at hseq
    exact hsok v (hseq ▸ hv.2.2) hv.2.1 hov
  have htmk_lit_get :
      st3.scratch.tarjan_mark[(BitVec.setWidth 64 lit).toNat]'(by rw [hz_lit]; omega) =
      st3.scratch.tarjan_mark[lit.toNat]?.getD 0#32 := by
    have hlt : lit.toNat < st3.scratch.tarjan_mark.length := by omega
    simp only [hz_lit, List.getElem?_eq_getElem hlt, Option.getD_some]
  dsimp only [lit] at htmk_lit_get
  scc_to_group
  refine wp_join_group (ts := [.bool])
    (fun (failb', ()) mj => ∃ st4 : FullState, TarjanLoopBase c F_cur s0 st4 ∧
      (st4.core.inconsistent = 0#64 →
        TarjanDfsInv c F0 F_cur s0 root.toNat (reached.toNat + 1) rch.toNat (dsp.toNat - 1) st4 ∧
        TarjanDfsInv.measure c s0 st4 rch.toNat (dsp.toNat - 1) <
          TarjanDfsInv.measure c s0 st3 rch.toNat dsp.toNat ∧
        (dsp.toNat - 1 = 0 → st4.core.tmp_cnt = 0)) ∧ (FullMem c st4 ⋆ R) mj) ?_ ?_
  · rintro _ ⟨failb', ⟨⟩⟩ mj ⟨st4, hbase4, hd4, hmj⟩; scc_steps
    by_cases hinc40 : st4.core.inconsistent = 0#64
    · obtain ⟨hd4', hm4', htop4'⟩ := hd4 hinc40
      exact hJ3 _ (rch, failb', dsp - (1 : BitVec 64), ()) mj hm4' ⟨st4, hbase4, fun _ =>
        ⟨by rw [hdsp_sub], by rwa [hdsp_sub], fun h => htop4' (by rwa [hdsp_sub] at h)⟩, hmj⟩
    · exact hJ3 0 (rch, failb', dsp - (1 : BitVec 64), ()) mj (TarjanDfsInv.measure_pos hdsp_pos)
        ⟨st4, hbase4, fun h => absurd h hinc40, hmj⟩
  intro Jpop hPopJ; scc_split
  · have hr_lt : rlit.toNat < (st3.scratch.tarjan_mark[lit.toNat]?.getD 0#32).toNat := by
      have hne : rlit ≠ st3.scratch.tarjan_mark[lit.toNat]?.getD 0#32 := by
        rw [← htmk_lit_get]; exact hc
      exact Nat.lt_of_le_of_ne hr_le fun heq => hne (BitVec.eq_of_toNat_eq heq)
    obtain ⟨hdsp_gt1, hd4, hm4⟩ := tarjan_pop_nonroot hd3 hdsp_pos
      (by rw [← hlit_get]; exact hpos_ge) hr_ge (by rw [← hlit_get]; exact hr_lt)
      (by rw [← hlit_get]; exact hscan) (by rw [← hlit_get]; exact hr_wit hr_lt)
    rw [← hlit_get] at hd4 hm4; scc_steps
    let st4 : FullState := { st3 with scratch := { st3.scratch with
      tarjan_reach := st3.scratch.tarjan_reach.set lit.toNat rlit } }
    have hm4' : (FullMem c st4 ⋆ R) m := by dsimp only [st4]; rw [hz_lit_u] at hm; exact hm
    exact hPopJ (failb, ()) m ⟨st4, hd4.toBase, fun _ => ⟨hd4, hm4, fun h => by omega⟩, hm4'⟩
  have hr_eq : rlit.toNat = (st3.scratch.tarjan_mark[lit.toNat]?.getD 0#32).toNat := by
    rw [← htmk_lit_get]; exact congrArg BitVec.toNat (Classical.not_not.mp hc)
  obtain ⟨k0, hk0_lt, hk0_bv, hk0_uniq, hk0_zero, hk0_eqv⟩ :=
    hd3.scc_pop_equiv hw0 hdm0 hdsp_pos (by rw [← hlit_get, ← hr_eq]; exact hscan)
  have hmr_reach : reached + (1 : BitVec 32) ≠ 0xFFFFFFFF#32 →
      (∀ j, k0 ≤ j → j < st3.core.tmp_cnt → BinReach (cnfOfClauses F_cur)
        (BitVec.setWidth 32 root).toNat (st3.scratch.work_stk1[j]?.getD 0#32).toNat) ∧
      (∀ l < 2 * st3.core.cur_vars,
        (reached + (1 : BitVec 32)).toNat ≤
          (st3.scratch.tarjan_mark[l]?.getD 0#32).toNat →
        BinReach (cnfOfClauses F_cur) (BitVec.setWidth 32 root).toNat l) := fun _ => by
    simp only [hr1_nat, bv32_trunc_toNat (x := root) (by omega)]
    exact ⟨fun j _ hj => hd3.mroot_reach hdsp_pos _ (hd3.scc_lt j hj) (hd3.scc_tmk_ge j hj).2,
      fun l hl hge => hd3.mroot_reach hdsp_pos l (by omega) hge⟩
  scc_steps
  · refine tarjan_pop_scc_call_wp hPop hw0 hinc30 hdsp_pos hrt_lt hlit_lt hd3 hlit_get hk0_lt
      hk0_bv hk0_uniq hk0_zero hk0_eqv (fun h => absurd rfl h) hm3 (fun b mj h => ?_)
    dsimp only; scc_steps; first | exact h | exact hPopJ (b, ()) mj h
  · refine tarjan_pop_scc_call_wp hPop hw0 hinc30 hdsp_pos hrt_lt hlit_lt hd3 hlit_get hk0_lt
      hk0_bv hk0_uniq hk0_zero hk0_eqv hmr_reach hm3 (fun b mj h => ?_)
    dsimp only; scc_steps; first | exact h | exact hPopJ (b, ()) mj h

end LeanQbe.T.Examples.Kissat.Full
