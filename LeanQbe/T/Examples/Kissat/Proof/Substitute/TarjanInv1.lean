/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Substitute.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Substitute.TarjanInv0

/-!
# Tarjan SCC DFS Discovery, Pop & Fill Transitions (`Proof.Substitute.TarjanInv1`)

Proves the node-discovery, non-root pop, root-pop aftermath, `full_tarjan_pop_scc` WP
adapter, empty DFS initialization, and final `repr`/`tarjan_*` fill transitions.
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

attribute [local grind =] List.getElem?_set_self List.getElem?_set_ne Option.getD_some

theorem m6_tarjan_discover_node {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
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

theorem m6_tarjan_pop_nonroot {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
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

theorem m6_tarjan_pop_root_after {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st : FullState} {root mroot reached dsp : Nat}
    (h : M6TarjanDfsInv c F0 F_cur s0 root mroot reached dsp st)
    (hdsp : 0 < dsp) {k0 : Nat} {st' : FullState} (hk0_lt : k0 < st.core.tmp_cnt)
    (hk0_eq : (st.scratch.work_stk1[k0]?.getD 0#32).toNat =
      (st.scratch.work_stk2[dsp - 1]?.getD 0#32).toNat)
    (hag_pop : AgreesExcept fullPopSccMask st st') (htop' : st'.core.tmp_cnt = k0)
    (hlen' : st'.LengthsOk c) (hinc0' : st'.core.inconsistent = 0#64)
    (hrsz' : st'.scratch.res_sz.toNat ≤ c.max_vars)
    (hpr' : FullPartialReprInv F_cur st'.core)
    (hus' : FullUnitsSoundInv F_cur st' st'.scratch.res_sz.toNat)
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

theorem m6_tarjan_pop_scc_call_wp {Γ : Env} {Q : Post [i64]} {X : XPost}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s0 st3 : FullState}
    {R : Mem 64 → Prop} {m3 : Mem 64} {root dsp : BitVec 64} {reached rch lit mr : BitVec 32}
    {failb : Bool} {k0 : Nat} {Jpop : Cont [.bool]}
    (hPop : Γ.Has "full_tarjan_pop_scc" fullTarjanPopSccSpec)
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
  c0_call hPop
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
  c0_hsteps
  · exact hPopJ true m4 ⟨st4, hbase4, hd4_fn, hm4⟩
  · exact hPopJ failb m4 ⟨st4, hbase4, hd4_fn, hm4⟩

theorem m6_tarjan_empty_dfs_inv {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st : FullState} (hsp0 : FullSparseInvW c F0 F_cur s0)
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
  have hpr1 : FullPartialReprInv F_cur st1.core := fun l hl hne => by
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

theorem m6_tarjan_fill_finish {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 stf st4 : FullState} (hsp0 : FullSparseInvW c F0 F_cur s0)
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
    (hpr4 : FullPartialReprInv F_cur st4.core)
    (hfill4 : ∀ l < 2 * s0.core.cur_vars,
      st4.core.repr[l]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 ∧
      st4.scratch.tarjan_mark[l]?.getD 0#32 = 0#32 ∧
      st4.scratch.tarjan_reach[l]?.getD 0#32 = 0#32) :
    FullSparseInvW c F0 F_cur st4 ∧
    (∀ (_ : Nat), FullReprEquiv F_cur st4) ∧
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
  have hrepr4 : FullReprEquiv F_cur st4 := fun l hl => by
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

end

end LeanQbe.T.Examples.Kissat.Proof.Substitute
