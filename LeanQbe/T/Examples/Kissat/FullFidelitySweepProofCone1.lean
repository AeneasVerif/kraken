/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelitySweep
public import LeanQbe.T.Examples.Kissat.FullM6SweepProofSpec
import LeanQbe.T.Examples.Kissat.FullFidelitySweepProofCone0
import LeanQbe.T.Examples.Kissat.FullM8SweepV2ConeProof
import LeanQbe.T.Examples.Kissat.FullM6SweepProofConeLemmas

/-!
# Kissat Full-Fidelity Sweep — `full_m6_sweep_cone` (`GAP-SWP-01`) `Func.wp` Proof (`Cone1`)

Proves `fid_sweep_cone_wp : m6SweepConeSpec` for `FullFidelitySweep.full_m6_sweep_cone_body`
with upstream Kissat 4.0.4 `sweep.c:107-138` geometric cone escalation (`vlim = 256 << comp`,
`clim = 1024 << comp`, `depth_lim = (comp > 0) ? 3 : 2`, clamped to `mv` / `3 * mv`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelitySweep

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full LeanQbe.T.Examples.Kissat.FullM4Sweep
open LeanQbe.T.Examples.Kissat.FullM6Sweep LeanQbe.T.Examples.Kissat.FullM8SweepV2
open Kraken.Bedrock2.Test
open FullArenaTactics
open scoped FullArenaTactics M6SweepTactics

theorem fid_sweep_cone_wp (Γ : Env)
    (hMaxV : M6EnvSpec Γ "full_m6_max_v" m6MaxVSpec)
    (hInit : M6EnvSpec Γ "full_k6_init" k6InitSpec)
    (hAddCl : M6EnvSpec Γ "full_k6_add_clause" k6AddClauseSpec) :
    ∀ args m Q X, m6SweepConeSpec args m Q X →
      Func.wp Γ FullFidelitySweep.full_m6_sweep_cone_body args m Q X := by
  rintro ⟨h, root_v, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hdw, hcap, hroot, htmk, hm, hQ⟩
  have hlen := hdw.1; have hw := hdw.2.1; have hnd := hdw.2.2.2.1
  have hcl0 := hdw.2.2.2.2.2.1; have hdm := hdw.2.2.2.2.2.2
  have hcv_le := hlen.core_ok.cur_vars_le
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hdwatches : DenseWatchesInv F_cur s.core := by
    have hmw := hw.watches; unfold ModeWatchesInv at hmw; rwa [ite_eq_right hdm] at hmw
  obtain ⟨L, hL_def⟩ : ∃ L : K6Layout, L = k6LayoutOfCap c.scratch_cap hcap c.hscr := ⟨_, rfl⟩
  have hL_len : L.scrLen = c.scratch_cap := by rw [hL_def]; exact k6LayoutOfCap_scrLen hcap c.hscr
  have hL_mv : L.maxV = k6MaxV c.scratch_cap := by rw [hL_def]; rfl
  clear hL_def
  have hmL := L.hmaxV
  have hmL_lo : 512 ≤ L.maxV := hmL.1
  have hmL_hi : L.maxV ≤ 8192 := hmL.2
  have hmv_bounds := k6MaxV_bounds hcap
  have hmv64_lt : k6MaxV c.scratch_cap < 2 ^ 32 := by omega
  let mv : BitVec 32 := (BitVec.ofNat 64 (k6MaxV c.scratch_cap)).setWidth 32
  have hmv_eq : mv = L.mv32 := by
    apply BitVec.eq_of_toNat_eq
    simp only [mv, K6PtrTactics.k6_mv32_toNat, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), hL_mv]
  have hmv_nat : mv.toNat = L.maxV := by rw [hmv_eq, K6PtrTactics.k6_mv32_toNat]
  have hmo_nat : (mv * 3#32).toNat = L.maxOrig := by
    unfold K6Layout.maxOrig; bv_omega
  have hkptr_rw : c.pScratchBuf + (1280#32 + (mv <<< (1 : Nat))).setWidth 64 * 4 =
      L.kPtr c.pScratchBuf := by
    rw [hmv_eq, k6_ptr_base_k6Base]
  have hm_shl1 : ∀ x : BitVec 32, x <<< (1 : BitVec 32) = x <<< (1 : Nat) := fun _ => rfl
  have hkptr_c0 : c.pScratchBuf + BitVec.setWidth 64
      ((1280 : BitVec 32) + (BitVec.setWidth 32 (BitVec.ofNat 64 (k6MaxV c.scratch_cap)) <<<
        (1 : BitVec 32))) * 4 = L.kPtr c.pScratchBuf := by
    rw [hm_shl1]; exact hkptr_rw
  have hkptr_c0_nat : c.pScratchBuf + BitVec.setWidth 64
      ((1280 : BitVec 32) + (BitVec.setWidth 32 (BitVec.ofNat 64 (k6MaxV c.scratch_cap)) <<<
        (1 : Nat))) * 4 = L.kPtr c.pScratchBuf := hkptr_rw
  have hmv_c0 : (BitVec.ofNat 64 (k6MaxV c.scratch_cap)).setWidth 32 = L.mv32 := hmv_eq
  have hqnext_c0 : L.kPtr c.pScratchBuf + BitVec.setWidth 64
      ((32 : BitVec 32) + (3 : BitVec 32) *
        (BitVec.ofNat 64 (k6MaxV c.scratch_cap)).setWidth 32) * 4 =
      L.kPtr c.pScratchBuf + BitVec.ofNat 64 (4 * L.oQNext) := by
    rw [hmv_c0]; simpa [K6Layout.oQNext] using k6_ptr_add_mul L (L.kPtr c.pScratchBuf) 3 (by decide)
  unfold Func.wp FullFidelitySweep.full_m6_sweep_cone_body
  m6_steps
  refine fid_call_max_v hMaxV (c := c) rfl ?_
  m6_split
  · exfalso
    have hz : mv = 0#32 := hc
    rw [hmv_eq] at hz
    have h0 := congrArg BitVec.toNat hz
    simp only [BitVec.toNat_ofNat, K6PtrTactics.k6_mv32_toNat] at h0; omega
  have hgu28 := fid_gu28_lt hlen
  have hgu28' := fid_gu28_lt64 hlen
  c0_hsteps_nogrp
  m6_to_group
  refine wp_join_group (ts := [i32])
    (fun (comp, ()) m_c => comp.toNat ≤ 5 ∧ (FullMem c s ⋆ R) m_c) ?_
    (fun _ hJ_comp => by
      m6_split
      · m6_steps; exact hJ_comp (5#32, ()) _ ⟨by decide, hm⟩
      · m6_steps; exact hJ_comp (_, ()) _ ⟨Nat.le_of_not_lt hc, hm⟩)
  rintro _ ⟨comp, ⟨⟩⟩ m_c ⟨hcomp_le, hm_c⟩
  obtain ⟨hvlim_lo, hvlim_hi, hclim_lo, hclim_hi⟩ := fid_comp_vlim_clim hcomp_le
  c0_hsteps_nogrp
  m6_to_group
  refine wp_join_group (ts := [i32])
    (fun (depth_lim, ()) m_d =>
      2 ≤ depth_lim.toNat ∧ depth_lim.toNat ≤ 3 ∧ (FullMem c s ⋆ R) m_d) ?_
    (fun _ hJ_dep => by
      m6_split
      · m6_steps; exact hJ_dep (3#32, ()) _ ⟨by decide, by decide, hm_c⟩
      · m6_steps; exact hJ_dep (2#32, ()) _ ⟨by decide, by decide, hm_c⟩)
  rintro _ ⟨depth_lim, ⟨⟩⟩ m_d ⟨hdep_lim_lo, hdep_lim_hi, hm_d⟩
  c0_hsteps_nogrp
  m6_to_group
  refine wp_join_group (ts := [i32])
    (fun (mv_c, ()) mm => 256 ≤ mv_c.toNat ∧ mv_c.toNat ≤ L.maxV ∧ (FullMem c s ⋆ R) mm) ?_ ?_
  · rintro _ ⟨mv_c, ⟨⟩⟩ mm ⟨hmv_c_lo, hmv_c_le, hmm⟩
    c0_hsteps_nogrp
    m6_to_group
    refine wp_join_group (ts := [i32])
      (fun (mc_c, ()) mm2 => mc_c.toNat ≤ L.maxOrig ∧ (FullMem c s ⋆ R) mm2) ?_ ?_
    · rintro _ ⟨mc_c, ⟨⟩⟩ mm2 ⟨hmc_c_le, hmm2⟩
      m6_steps
      m6_call hInit
      refine ⟨c, s, R, rfl, hlen, hmm2, ?_⟩
      refine fid_if_false_prop ?_ ?_
      · dsimp only [Arg.val_var, Prod.fst]
        rw [← hL_mv]; omega
      intro L0 scr0 m0 hL0_len hL0_mv
      dsimp only
      intro hlen0 _hpre0 hK0 hsy0 hnv0 hnc0 hlvl0 _hpr0 htr0 _hun0 _hin0 hna0 _hst0 _ho0 _hnq0 hm0
      have hL0_eq : L0 = L :=
        K6Layout.eq_of_scrLen_maxV (hL0_len.trans hL_len.symm) (hL0_mv.trans hL_mv.symm)
      subst L0
      let s0 : FullState := { s with scratch := { s.scratch with scratch_buf := scr0 } }
      have hscr0 : scr0.length = c.scratch_cap := hlen0.scratch_ok.scratch_buf_len
      have hscr0_L : s0.scratch.scratch_buf.length = L.scrLen := hscr0.trans hL_len.symm
      have hkb_le0 : L.k6Base ≤ s0.scratch.scratch_buf.length := by
        rw [hscr0_L]; unfold K6Layout.scrLen; omega
      let seed25 : BitVec 32 := (root_v ^^^ 0x9E3779B9#32) ||| 1#32
      let ks0 := k6StateOfScratch L scr0
      let ks0' := k6Set25 ks0 seed25
      have hm0_ka : (K6MemA L (L.kPtr c.pScratchBuf) ks0 ⋆ (FullK6Frame c L s0 ⋆ R)) m0 := by
        rw [fullMem_eq_k6Frame hscr0_L] at hm0
        exact k6Mem_to_amem (hK0 (fun _ => True)).shapes (sep_ac hm0)
      obtain ⟨hok25, hm1_ka⟩ := k6Set25_store seed25 hm0_ka
      let scr1 := s0.scratch.scratch_buf.take L.k6Base ++ ks0'.toSlab
      let s1 : FullState := { s0 with scratch := { s0.scratch with scratch_buf := scr1 } }
      have hm1 : (FullMem c s1 ⋆ R)
          (storeMem m0 i32 (L.kPtr c.pScratchBuf + BitVec.ofNat 64 25 * 4) seed25) := by
        obtain ⟨_, hkm1⟩ := k6MemA_to_mem hm1_ka
        exact fullMem_join_k6 (c := c) (L := L) (s := s0) hkb_le0
          (k6Set25_shapes (hK0 (fun _ => True)).shapes seed25) (sep_ac hkm1)
      have hscr1_len : scr1.length = c.scratch_cap := by
        dsimp only [scr1]
        rw [List.length_append, List.length_take_of_le hkb_le0,
          ks0'.toSlab_length (k6Set25_shapes (hK0 (fun _ => True)).shapes seed25), ← hL_len]
        unfold K6Layout.scrLen; omega
      have hof1 : k6StateOfScratch L scr1 = ks0' := by
        unfold k6StateOfScratch; dsimp only [scr1]
        rw [k6_slab_drop_exact _ _ (List.length_take_of_le hkb_le0)]
        exact K6State.ofSlab_toSlab (k6Set25_shapes (hK0 (fun _ => True)).shapes seed25)
      have hlen1_s : s1.LengthsOk c :=
        ⟨hlen0.core_ok, { hlen0.scratch_ok with scratch_buf_len := hscr1_len }⟩
      have hK1 : ∀ P, K6Inv L P (k6StateOfScratch L scr1) := fun P =>
        hof1 ▸ k6Set25_inv (hK0 P) seed25
      have hsy1 : K6TrailSynced (k6StateOfScratch L scr1) :=
        hof1 ▸ k6Set25_sync hsy0 seed25
      have hnv1 : (k6StateOfScratch L scr1).nv = mv_c := by rw [hof1]; exact hnv0
      have hnc1 : (k6StateOfScratch L scr1).nc = 0#32 := by rw [hof1]; exact hnc0
      have hlvl1 : (k6StateOfScratch L scr1).lvl = 0#32 := by rw [hof1]; exact hlvl0
      have htr1 : (k6StateOfScratch L scr1).trl_end = 0#32 := by rw [hof1]; exact htr0
      have hna1 : (k6StateOfScratch L scr1).nassump = 0#32 := by rw [hof1]; exact hna0
      have h0_wk0 : (BitVec.signExtend 64 (0 : BitVec 32)).toNat < s1.scratch.work_stk1.length := by
        rw [hlen1_s.scratch_ok.work_stk1_len,
          show (BitVec.signExtend 64 (0 : BitVec 32)).toNat = 0 from rfl]; omega
      let s1w : FullState :=
        { s1 with scratch := { s1.scratch with
            work_stk1 :=
              s1.scratch.work_stk1.set (BitVec.signExtend 64 (0 : BitVec 32)).toNat root_v } }
      have hrt_tm0 : (BitVec.setWidth 64 root_v).toNat < s1w.scratch.tarjan_mark.length := by
        rw [hlen1_s.scratch_ok.tarjan_mark_len, bv_c0_zext32_64]; omega
      obtain ⟨hlen1, hag1, hcone1⟩ :=
        fidConeInv_init (F_cur := F_cur) hlen hL_len (by omega) hmv_c_le hroot htmk hscr1_len
          hK1 hsy1 hnv1 hnc1 hlvl1 htr1 hna1
      clear hm
      change wp _ _ _ _ _
      c0_hsteps_nogrp
      dsimp only [Prod.fst]
      first | rw [hkptr_c0] | rw [hkptr_c0_nat]
      try rw [show (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 25) : BitVec 64) = 25#64 from rfl]
      try rw [show (BitVec.signExtend 64 (25 : BitVec 32) : BitVec 64) = 25#64 from rfl]
      try rw [show (root_v ^^^ 2654435769 ||| 1 : BitVec 32) = seed25 from rfl]
      refine ⟨hok25, ?_⟩
      clear hm0 hm0_ka hm1_ka hok25
      change wp _ _ _ _ _
      dsimp only [Arg.val_var]
      have hm_s1 : (FullMem c s1 ⋆ R) _ := hm1
      m6_steps
      obtain ⟨st0, hst0_def⟩ : ∃ st0 : FullState, st0 =
        { s1w with scratch :=
          { s1w.scratch with
            tarjan_mark := s1w.scratch.tarjan_mark.set (BitVec.setWidth 64 root_v).toNat 1#32 } } :=
        ⟨_, rfl⟩
      -- Outer BFS loop: `while (qi < nv && depth < depth_lim && !limit_reached && nc < mc_c)`
      refine wp_loop_inv (ts := [i32, i32, i32, i32, .bool])
        (fun (nv, nc, qi, depth, _lim, ()) mo =>
          qi.toNat ≤ nv.toNat ∧ depth.toNat ≤ depth_lim.toNat ∧ ∃ st : FullState,
            st.LengthsOk c ∧ AgreesExcept fidConeMask s st ∧
            FidConeInv F_cur L mv_c st nv.toNat nc.toNat ∧ (FullMem c st ⋆ R) mo)
        (fun (_, _, _, depth, _, ()) _ => depth_lim.toNat - depth.toNat) ?_ ?_
      · intro _ hJ_out
        m6_steps
        refine hJ_out (1#32, 0#32, 0#32, 0#32, false, ()) _
          ⟨Nat.zero_le _, Nat.zero_le _, _, hlen1, hag1, hcone1, ?_⟩
        simpa only [hst0_def, s1w, s1, s0,
          show (BitVec.signExtend 64 (0 : BitVec 32)).toNat = 0 from rfl,
          bv_c0_zext32_64] using (by assumption : (FullMem c _ ⋆ R) _)
      rintro _ ⟨nv, nc, qi, depth, lim, ⟨⟩⟩ mo
        ⟨hqi_le, hdep_le, st, hlen_st, hag_st, hcone_st, hmo⟩ hJ_out
      clear hm hm_c hm_d hm1 hmm hmm2 hm_s1 hst0_def st0 hcone1 hag1 hlen1 hrt_tm0 s1w h0_wk0
        hK1 hsy1 hnv1 hnc1 hlvl1 htr1 hna1 hlen1_s hof1 hscr1_len s1 scr1 ks0' ks0 seed25
        hkb_le0 hscr0_L s0 hscr0 _hpre0 _hpr0 _hun0 _hin0 _hst0 _ho0 _hnq0
        hlen0 hK0 hsy0 hnv0 hnc0 hlvl0 htr0 hna0 hL0_len hL0_mv scr0
        hgu28 hgu28' hcomp_le hvlim_lo hvlim_hi hclim_lo hclim_hi hdep_lim_lo hmv_c_lo hmv_c_le
        hmv_nat hmL_lo hmL_hi comp
      m6_to_group
      refine wp_join_group (ts := [])
        (fun () m_ex => ∃ st_e : FullState,
          st_e.LengthsOk c ∧ AgreesExcept fidConeMask s st_e ∧
          FidConeInv F_cur L mv_c st_e nv.toNat nc.toNat ∧ (FullMem c st_e ⋆ R) m_ex)
        (fun _ () m_ex ⟨st_e, hlen_e, hag_e, hcone_e, hm_e⟩ => by
          clear hJ_out hmo hqi_le hdep_le hlen_st hag_st hcone_st
          have hscr_e := hcone_e.scr_len
          have hkb_le : L.k6Base ≤ st_e.scratch.scratch_buf.length := by
            rw [hscr_e]; unfold K6Layout.scrLen; omega
          let ks_e := k6StateOfScratch L st_e.scratch.scratch_buf
          have hte_le : ks_e.trl_end.toNat ≤ nv.toNat :=
            m6_trl_end_le_of_bdd hcone_e.k6_inv hcone_e.k6_trl_bdd
          have hnv_ge1 : 1 ≤ nv.toNat := hcone_e.nv_ge1
          have hnv_leMax : nv.toNat ≤ L.maxV := hcone_e.nv_leMax
          change wp _ _ _ _ _
          c0_hsteps
          obtain ⟨Rfr, hRfr⟩ : ∃ Rfr : Mem 64 → Prop, Rfr = (FullK6Frame c L st_e ⋆ R) := ⟨_, rfl⟩
          have hm_ka : (K6MemA L (L.kPtr c.pScratchBuf) ks_e ⋆ Rfr) m_ex := by
            rw [fullMem_eq_k6Frame hscr_e] at hm_e
            rw [hRfr]
            exact k6Mem_to_amem hcone_e.k6_inv.shapes (sep_ac hm_e)
          clear hm_e
          dsimp only [Prod.fst]
          try (first | rw [hkptr_c0] | rw [hkptr_c0_nat])
          try rw [hqnext_c0]
          open scoped K6MemATactics K6PtrTactics in c0_hsteps_nogrp
          m6_to_group
          refine wp_join_group (ts := [i32])
            (fun (un_v, ()) mu => un_v = nv - ks_e.trl_end ∧
              (K6MemA L (L.kPtr c.pScratchBuf) (ks_e.putHdr .nv nv) ⋆ Rfr) mu)
            (fun _ (un_v, ()) mu ⟨hun_eq, hmu⟩ => by
              subst hun_eq
              have hnv_pos : 0 < nv.toNat := by omega
              have hnv_sub_bv : (nv - (1 : BitVec 32)).toNat = nv.toNat - 1 := by bv_omega
              have hnv_subMax : (nv - (1 : BitVec 32)).toNat < K6MemATactics.szV L := by
                dsimp only [K6MemATactics.szV]; rw [hnv_sub_bv]; omega
              open scoped K6MemATactics K6PtrTactics in m6_to_group
              refine wp_join_group (ts := [])
                (fun () mf =>
                  (K6MemA L (L.kPtr c.pScratchBuf)
                    ((((((ks_e.putHdr .nv nv).putHdr .unass (nv - ks_e.trl_end)).putHdr .qlast
                      (nv - 1#32)).putHdr .qsearch (nv - 1#32)).putHdr .qstamp nv).putArr .qnext
                        (nv.toNat - 1) 0xFFFFFFFF#32) ⋆ Rfr) mf)
                (fun _ () mf hmf => by
                  m6_steps
                  rw [hRfr] at hmf
                  exact fid_cone_exit_post hdw hcap hL_len hL_mv hlen_e hag_e hcone_e hmf hQ)
                (fun _ hJ_nv0 => by
                  m6_split
                  · c0_hsteps
                    try rw [hqnext_c0]
                    open scoped K6MemATactics K6PtrTactics in c0_hsteps!
                    rw [hnv_sub_bv, show (1 : BitVec 32) = 1#32 from rfl,
                      show (4294967295 : BitVec 32) = 0xFFFFFFFF#32 from rfl] at hm
                    exact hJ_nv0 () _ hm
                  · exfalso; have : nv = 0#32 := by bv_omega
                    have h0 := congrArg BitVec.toNat this; simp at h0; omega))
            (fun _ hJ_ter => by
              m6_split
              · m6_steps; exact hJ_ter (nv - ks_e.trl_end, ()) _ ⟨rfl, by assumption⟩
              · exfalso
                have hgt : nv.toNat < ks_e.trl_end.toNat := by bv_omega
                omega))
        (fun _ hJ_ex => by
          clear hQ hInit hMaxV
          m6_split; rotate_left
          · m6_steps; exact hJ_ex () mo ⟨st, hlen_st, hag_st, hcone_st, hmo⟩
          have hqi_lt : qi.toNat < nv.toNat := hc
          m6_split; rotate_left
          · m6_steps; exact hJ_ex () mo ⟨st, hlen_st, hag_st, hcone_st, hmo⟩
          have hdep_lt : depth.toNat < depth_lim.toNat := hc
          m6_split
          · m6_steps; exact hJ_ex () mo ⟨st, hlen_st, hag_st, hcone_st, hmo⟩
          have hlim_f : lim = false := by cases lim <;> simp at hc ⊢
          m6_split; rotate_left
          · m6_steps; exact hJ_ex () mo ⟨st, hlen_st, hag_st, hcone_st, hmo⟩
          have hnc_lt : nc.toNat < L.maxOrig := Nat.lt_of_lt_of_le hc hmc_c_le
          have hdep1 : (depth + 1#32).toNat = depth.toNat + 1 :=
            m6_bv32_add1 (by omega)
          obtain ⟨layer_end, hle_def⟩ : ∃ layer_end : BitVec 32, layer_end = nv := ⟨_, rfl⟩
          -- Layer loop: `while (qi < layer_end && !limit_reached && nc < max_orig)`
          m6_to_group
          refine wp_loop_inv (ts := [i32, i32, i32, .bool])
            (fun (nv_l, nc_l, qi_l, lim_l, ()) ml =>
              qi_l.toNat ≤ layer_end.toNat ∧ layer_end.toNat ≤ nv_l.toNat ∧ ∃ st_l : FullState,
                st_l.LengthsOk c ∧ AgreesExcept fidConeMask s st_l ∧
                FidConeInv F_cur L mv_c st_l nv_l.toNat nc_l.toNat ∧ (FullMem c st_l ⋆ R) ml)
            (fun (_, _, qi_l, _, ()) _ => layer_end.toNat - qi_l.toNat)
            (fun _ hJ_in => by
              m6_steps
              exact hJ_in (nv, nc, qi, lim, ()) mo
                ⟨hle_def ▸ hqi_le, hle_def ▸ le_refl _, st, hlen_st, hag_st, hcone_st, hmo⟩)
            (fun _ (nv_l, nc_l, qi_l, lim_l, ()) ml
                ⟨hqi_l_le, hle_nv_l, st_l, hlen_l, hag_l, hcone_l, hml⟩ hJ_in => by
              clear hJ_ex hmo hlen_st hag_st hcone_st
              m6_split; rotate_left
              · m6_steps
                exact hJ_out (nv_l, nc_l, qi_l, depth + 1#32, lim_l, ()) ml
                  (by dsimp only; exact m6_nat_sub1_lt hdep_lt hdep1)
                  ⟨Nat.le_trans hqi_l_le hle_nv_l, by rw [hdep1]; exact hdep_lt, st_l,
                    hlen_l, hag_l, hcone_l, hml⟩
              have hqi_l_lt : qi_l.toNat < layer_end.toNat := hle_def ▸ hc
              m6_split
              · m6_steps
                exact hJ_out (nv_l, nc_l, qi_l, depth + 1#32, lim_l, ()) ml
                  (by dsimp only; exact m6_nat_sub1_lt hdep_lt hdep1)
                  ⟨Nat.le_trans hqi_l_le hle_nv_l, by rw [hdep1]; exact hdep_lt, st_l,
                    hlen_l, hag_l, hcone_l, hml⟩
              m6_split; rotate_left
              · m6_steps
                exact hJ_out (nv_l, nc_l, qi_l, depth + 1#32, lim_l, ()) ml
                  (by dsimp only; exact m6_nat_sub1_lt hdep_lt hdep1)
                  ⟨Nat.le_trans hqi_l_le hle_nv_l, by rw [hdep1]; exact hdep_lt, st_l,
                    hlen_l, hag_l, hcone_l, hml⟩
              clear hle_def
              have hwk_l := hlen_l.scratch_ok.work_stk1_len
              have htm_l := hlen_l.scratch_ok.tarjan_mark_len
              have hnv_l_max := hcone_l.nv_leMax
              have hqi_z : (BitVec.setWidth 64 qi_l).toNat = qi_l.toNat := bv_c0_zext32_64 qi_l
              have hqi_ws : (BitVec.setWidth 64 qi_l).toNat < st_l.scratch.work_stk1.length := by
                have := hcone_l.nv_le_cv; have := hlen_l.core_ok.cur_vars_le
                rw [hqi_z, hwk_l]; omega
              obtain ⟨cv, hcv_def⟩ : ∃ cv : BitVec 32,
                  cv = st_l.scratch.work_stk1[(BitVec.setWidth 64 qi_l).toNat]'hqi_ws := ⟨_, rfl⟩
              have hwk_qi : st_l.scratch.work_stk1[qi_l.toNat]?.getD 0#32 = cv := by
                rw [hcv_def, List.getElem?_eq_getElem (by rw [hwk_l]; omega), Option.getD_some]
                exact m6_list_getElem_congr hqi_z.symm _ _
              have hcv_lt_s : cv.toNat < s.core.cur_vars := by
                have hf := (hcone_l.fwd qi_l.toNat (by omega)).1
                rw [hwk_qi, fid_hag_cur_vars hag_l] at hf; exact hf
              have hcv_idx : st_l.scratch.tarjan_mark[cv.toNat]?.getD 0#32 =
                  BitVec.ofNat 32 (qi_l.toNat + 1) := by
                have hf := (hcone_l.fwd qi_l.toNat (by omega)).2
                rw [hwk_qi] at hf; exact hf
              have hcv_tmk : (BitVec.setWidth 64 cv).toNat < st_l.scratch.tarjan_mark.length := by
                rw [htm_l, bv_c0_zext32_64]; omega
              have hqi1 : (qi_l + 1#32).toNat = qi_l.toNat + 1 :=
                m6_bv32_add1 (by omega)
              m6_steps
              have hcur_tmk : st_l.scratch.tarjan_mark[(BitVec.setWidth 64 cv).toNat]'hcv_tmk =
                  BitVec.ofNat 32 (qi_l.toNat + 1) := by
                rw [← Option.getD_some (a :=
                    st_l.scratch.tarjan_mark[(BitVec.setWidth 64 cv).toNat]'hcv_tmk),
                  ← List.getElem?_eq_getElem hcv_tmk, bv_c0_zext32_64, hcv_idx]
              have hmap_c : ((st_l.scratch.tarjan_mark[(BitVec.setWidth 64 cv).toNat]'hcv_tmk) -
                  1#32) = qi_l := by
                rw [hcur_tmk]; exact m6_bv32_ofNat_add1_sub1 qi_l
              have hcv_qi : ∀ (h : qi_l.toNat < st_l.scratch.work_stk1.length),
                  st_l.scratch.work_stk1[qi_l.toNat]'h = cv := fun h => by
                rw [hcv_def]; exact m6_list_getElem_congr hqi_z.symm h hqi_ws
              have hqi_ws0 : qi_l.toNat < st_l.scratch.work_stk1.length := by
                have h1 := hcone_l.nv_le_cv
                have h2 := fid_hag_cur_vars hag_l
                rw [hwk_l]; omega
              have hcv_qi0 : st_l.scratch.work_stk1[qi_l.toNat]'hqi_ws0 = cv := hcv_qi hqi_ws0
              -- Pass 1: Binary `pol` loop `while (pol < 2u && !limit_reached && nc < max_orig)`
              m6_to_group
              refine wp_loop_inv (ts := [i32, i32, .bool, i32])
                (fun (nv_p, nc_p, _lim_p, pol, ()) mp =>
                  pol.toNat ≤ 2 ∧ layer_end.toNat ≤ nv_p.toNat ∧ ∃ st_p : FullState,
                    FidConeBase F_cur L mv_c c s cv qi_l nv_p.toNat nc_p.toNat st_p ∧
                    (FullMem c st_p ⋆ R) mp)
                (fun (_, _, _, pol, ()) _ => 2 - pol.toNat)
                (fun _ hJ_bpol => by
                  m6_steps
                  exact hJ_bpol (nv_l, nc_l, lim_l, 0#32, ()) ml
                    ⟨Nat.zero_le _, hle_nv_l, st_l,
                     ⟨hlen_l, hag_l, hcone_l, hcv_idx, by rw [hwk_qi]⟩, hml⟩)
                (fun _ (nv_p, nc_p, lim_p, pol, ()) mp
                    ⟨hpol_le, hle_nv_p, st_p, hb_p, hmp⟩ hJ_bpol => by
                  m6_to_group
                  refine wp_join_group (ts := [])
                    (fun () mp_ex => layer_end.toNat ≤ nv_p.toNat ∧ ∃ st_p2 : FullState,
                      FidConeBase F_cur L mv_c c s cv qi_l nv_p.toNat nc_p.toNat st_p2 ∧
                      (FullMem c st_p2 ⋆ R) mp_ex)
                    (fun _ () mp_ex ⟨hle_nv2, st_p2, hb_p2, hm2⟩ => by
                      -- Pass 2: Long `pol` loop `while (pol < 2u && !limit_reached && ...)`
                      clear hJ_bpol hmp hpol_le hle_nv_p hb_p hJ_out hm_shl1 hqnext_c0 hdw hroot
                        htmk hcur_tmk hcv_idx hle_nv_l hlen_l hag_l hcone_l hmv_c0
                        hmv_bounds hmv64_lt hdep1 hdep_lt hlim_f hqi_lt hqi_le hdep_le hnc_lt
                        hdep_lim_hi
                      m6_steps
                      refine wp_loop_inv (ts := [i32, i32, .bool, i32])
                        (fun (nv_q, nc_q, _lim_q, pol_q, ()) mq =>
                          pol_q.toNat ≤ 2 ∧ layer_end.toNat ≤ nv_q.toNat ∧ ∃ st_q : FullState,
                            FidConeBase F_cur L mv_c c s cv qi_l nv_q.toNat nc_q.toNat st_q ∧
                            (FullMem c st_q ⋆ R) mq)
                        (fun (_, _, _, pol_q, ()) _ => 2 - pol_q.toNat)
                        (fun _ hJ_lpol => by
                          m6_steps
                          exact hJ_lpol (nv_p, nc_p, lim_p, 0#32, ()) mp_ex
                            ⟨Nat.zero_le _, hle_nv2, st_p2, hb_p2, hm2⟩)
                        (fun _ (nv_q, nc_q, lim_q, pol_q, ()) mq
                            ⟨hpolq_le, hle_nv_q, st_q, hb_q, hmq⟩ hJ_lpol => by
                          m6_split; rotate_left
                          · m6_steps
                            exact hJ_in (nv_q, nc_q, qi_l + 1#32, lim_q, ()) mq
                              (by dsimp only; rw [hqi1]; exact m6_nat_sub1_lt hqi_l_lt rfl)
                              ⟨by rw [hqi1]; exact hqi_l_lt, hle_nv_q, st_q,
                               hb_q.hlen, hb_q.hag, hb_q.hcone, hmq⟩
                          have hpolq_lt : pol_q.toNat < 2 := hc
                          m6_split
                          · m6_steps
                            exact hJ_in (nv_q, nc_q, qi_l + 1#32, lim_q, ()) mq
                              (by dsimp only; rw [hqi1]; exact m6_nat_sub1_lt hqi_l_lt rfl)
                              ⟨by rw [hqi1]; exact hqi_l_lt, hle_nv_q, st_q,
                               hb_q.hlen, hb_q.hag, hb_q.hcone, hmq⟩
                          m6_split; rotate_left
                          · m6_steps
                            exact hJ_in (nv_q, nc_q, qi_l + 1#32, lim_q, ()) mq
                              (by dsimp only; rw [hqi1]; exact m6_nat_sub1_lt hqi_l_lt rfl)
                              ⟨by rw [hqi1]; exact hqi_l_lt, hle_nv_q, st_q,
                               hb_q.hlen, hb_q.hag, hb_q.hcone, hmq⟩
                          have hncq_lt : nc_q.toNat < L.maxOrig :=
                            Nat.lt_of_lt_of_le hc hmc_c_le
                          obtain ⟨lit, hlit_def⟩ : ∃ lit : BitVec 32,
                              lit = ((cv <<< (1 : Nat)) ||| pol_q) := ⟨_, rfl⟩
                          have hlit_eq : lit.toNat = 2 * cv.toNat + pol_q.toNat := by
                            rw [hlit_def]
                            exact m6_bv32_shl1_or_pol cv pol_q (by omega) hpolq_lt
                          have hlit_lt : lit.toNat < 2 * s.core.cur_vars := by omega
                          obtain ⟨hwo, hwsz, hend_eq, hwo_le, hrem_eq, hend_ws, h2l_mod, h2l1_mod⟩
                            := fid_cone_wvec_facts hlen hb_q.hlen hb_q.hag hdwatches hlit_lt
                          have hwvec_q := hb_q.hlen.core_ok.wvec_len
                          have h2l_bd : (BitVec.setWidth 64 lit <<< (1 : Nat)).toNat <
                              st_q.core.wvec.length := by
                            rw [hwvec_q, m6_bv64_shl1]; omega
                          have h2l1_bd : ((BitVec.setWidth 64 lit <<< (1 : Nat)) + 1#64).toNat <
                              st_q.core.wvec.length := by
                            rw [hwvec_q, m6_bv64_shl1_add1]; omega
                          obtain ⟨wOff, hwOff_def⟩ : ∃ wOff : BitVec 64,
                              wOff = (st_q.core.wvec[(BitVec.setWidth 64 lit <<<
                                (1 : Nat)).toNat]'h2l_bd).setWidth 64 := ⟨_, rfl⟩
                          obtain ⟨wSz, hwSz_def⟩ : ∃ wSz : BitVec 64,
                              wSz = (st_q.core.wvec[((BitVec.setWidth 64 lit <<< (1 : Nat)) +
                                1#64).toNat]'h2l1_bd).setWidth 64 := ⟨_, rfl⟩
                          obtain ⟨wEnd, hwEnd⟩ : ∃ wEnd : BitVec 64, wEnd = wOff + wSz := ⟨_, rfl⟩
                          have hend_ws : wEnd.toNat ≤ s.core.wstk.length := by
                            rw [hwEnd, hwOff_def, hwSz_def]; exact hend_ws
                          have hwOff_n : wOff.toNat = fullWatchOffCore s.core lit.toNat := by
                            rw [hwOff_def]; exact hwo
                          have hwSz_n : wSz.toNat = fullWatchSizeCore s.core lit.toNat := by
                            rw [hwSz_def]; exact hwsz
                          have hend_n : wEnd.toNat =
                              fullWatchOffCore s.core lit.toNat +
                                fullWatchSizeCore s.core lit.toNat := by
                            rw [hwEnd, hwOff_def, hwSz_def]; exact hend_eq
                          have hpol1 : (pol_q + 1#32).toNat = pol_q.toNat + 1 :=
                            m6_bv32_add1 (Nat.lt_trans hpolq_lt (by decide))
                          have hwv0_eq :
                              ∀ (h : (2 * lit.toNat) % 2 ^ 64 < st_q.core.wvec.length),
                              st_q.core.wvec[(2 * lit.toNat) % 2 ^ 64]'h =
                                st_q.core.wvec[(BitVec.setWidth 64 lit <<< (1 : Nat)).toNat]'
                                  h2l_bd := fun h => m6_list_getElem_congr h2l_mod h _
                          have hwv1_eq :
                              ∀ (h : (2 * lit.toNat + (1#64).toNat) % 2 ^ 64 <
                                  st_q.core.wvec.length),
                                st_q.core.wvec[(2 * lit.toNat +
                                  (1#64).toNat) % 2 ^ 64]'h =
                                  st_q.core.wvec[((BitVec.setWidth 64 lit <<< (1 : Nat)) +
                                    1#64).toNat]'h2l1_bd := fun h =>
                            m6_list_getElem_congr
                              (by rw [show (1#64).toNat = 1 from rfl]; exact h2l1_mod) h _
                          have h2l_bd_ws :
                              (BitVec.setWidth 64 ((st_l.scratch.work_stk1[
                                (BitVec.setWidth 64 qi_l).toNat]'hqi_ws <<< (1 : Nat)) |||
                                pol_q) <<< (1 : Nat)).toNat < st_q.core.wvec.length := by
                            rw [← hcv_def, ← hlit_def]; exact h2l_bd
                          have h2l1_bd_ws :
                              ((BitVec.setWidth 64 ((st_l.scratch.work_stk1[
                                (BitVec.setWidth 64 qi_l).toNat]'hqi_ws <<< (1 : Nat)) |||
                                pol_q) <<< (1 : Nat)) + 1#64).toNat < st_q.core.wvec.length := by
                            rw [← hcv_def, ← hlit_def]; exact h2l1_bd
                          have hw0_ws :
                              ∀ (h : (BitVec.setWidth 64 ((st_l.scratch.work_stk1[
                                  (BitVec.setWidth 64 qi_l).toNat]'hqi_ws <<< (1 : Nat)) |||
                                  pol_q) <<< (1 : Nat)).toNat < st_q.core.wvec.length),
                                (st_q.core.wvec[(BitVec.setWidth 64 ((st_l.scratch.work_stk1[
                                  (BitVec.setWidth 64 qi_l).toNat]'hqi_ws <<< (1 : Nat)) |||
                                  pol_q) <<< (1 : Nat)).toNat]'h).setWidth 64 = wOff := fun h => by
                            rw [hwOff_def]; congr 1
                            exact m6_list_getElem_congr (by rw [← hcv_def, ← hlit_def]) h h2l_bd
                          have hw1_ws :
                              ∀ (h : ((BitVec.setWidth 64 ((st_l.scratch.work_stk1[
                                  (BitVec.setWidth 64 qi_l).toNat]'hqi_ws <<< (1 : Nat)) |||
                                  pol_q) <<< (1 : Nat)) + 1#64).toNat < st_q.core.wvec.length),
                                (st_q.core.wvec[((BitVec.setWidth 64 ((st_l.scratch.work_stk1[
                                  (BitVec.setWidth 64 qi_l).toNat]'hqi_ws <<< (1 : Nat)) |||
                                  pol_q) <<< (1 : Nat)) + 1#64).toNat]'h).setWidth 64 =
                                  wSz := fun h => by
                            rw [hwSz_def]; congr 1
                            exact m6_list_getElem_congr (by rw [← hcv_def, ← hlit_def]) h h2l1_bd
                          have hw0_eq_nat : ∀ (h : (BitVec.setWidth 64 lit <<< (1 : Nat)).toNat <
                                st_q.core.wvec.length),
                              (st_q.core.wvec[(BitVec.setWidth 64 lit <<< (1 : Nat)).toNat]'h).toNat
                                = wOff.toNat := fun h => by rw [hwOff_def, bv_c0_zext32_64]
                          have hw1_eq_nat : ∀ (h : ((BitVec.setWidth 64 lit <<< (1 : Nat)) +
                                1#64).toNat < st_q.core.wvec.length),
                              (st_q.core.wvec[((BitVec.setWidth 64 lit <<< (1 : Nat)) +
                                1#64).toNat]'h).toNat = wSz.toNat := fun h => by
                            rw [hwSz_def, bv_c0_zext32_64]
                          -- Long watch loop join (`pol_q = pol_q + 1u`)
                          m6_to_group
                          refine wp_join_group (ts := [i32, i32, .bool, i64])
                            (fun (nv_e, nc_e, _lim_e, _, ()) m_we =>
                              layer_end.toNat ≤ nv_e.toNat ∧ ∃ st_we : FullState,
                                FidConeBase F_cur L mv_c c s cv qi_l nv_e.toNat nc_e.toNat st_we ∧
                                (FullMem c st_we ⋆ R) m_we)
                            (fun _ (nv_e, nc_e, lim_e, _, ()) m_we ⟨hnve, st_we, hb_e, hm_e⟩ => by
                              m6_steps
                              exact hJ_lpol (nv_e, nc_e, lim_e, pol_q + 1#32, ()) m_we
                                (by dsimp only; rw [hpol1]; exact m6_nat_sub1_lt hpolq_lt rfl)
                                ⟨by rw [hpol1]; exact hpolq_lt, hnve, st_we, hb_e, hm_e⟩)
                            (fun _ hJ_we => by
                              m6_to_group
                              refine wp_loop_inv (ts := [i32, i32, .bool, i64])
                                (fun (nv_w, nc_w, _lim_w, p, ()) mw =>
                                  p.toNat ≤ wEnd.toNat ∧ layer_end.toNat ≤ nv_w.toNat ∧
                                  DenseWatchSliceOk F_cur s.core lit.toNat p.toNat
                                    (wEnd.toNat - p.toNat) ∧
                                  ∃ st_w : FullState,
                                    FidConeBase F_cur L mv_c c s cv qi_l nv_w.toNat
                                      nc_w.toNat st_w ∧
                                    (FullMem c st_w ⋆ R) mw)
                                (fun (_, _, _, p, ()) _ => wEnd.toNat - p.toNat)
                                (fun _ hJ_w => by
                                  m6_steps
                                  refine hJ_w (nv_q, nc_q, lim_q, _, ()) mq
                                    ⟨?_, hle_nv_q, ?_, st_q, hb_q, hmq⟩
                                  · try rw [hw0_ws]
                                    rw [hwEnd, hwOff_def, hwSz_def]; exact hwo_le
                                  · try rw [hw0_ws]
                                    rw [hwEnd, hwOff_def, hwSz_def, hrem_eq, hwo]
                                    exact hdwatches.slices lit.toNat hlit_lt)
                                (fun J_w (nv_w, nc_w, lim_w, p, ()) mw
                                    ⟨hp_le, hnv_w_mono, hslice, st_w, hb_w, hmw⟩ hJ_w => by
                                  clear hJ_lpol hmq hpol1 hle_nv2 hb_p2 hm2 hpolq_le hle_nv_q
                                    hncq_lt hpolq_lt hwo hwsz hend_eq hwo_le hrem_eq
                                    hwOff_n hwSz_n
                                  m6_split; rotate_left
                                  · m6_steps; exact hJ_we (nv_w, nc_w, lim_w, p, ()) mw
                                      ⟨hnv_w_mono, st_w, hb_w, hmw⟩
                                  have hp_lt : p.toNat < wEnd.toNat := by
                                    simp only [hcv_qi0] at hc
                                    repeat rw [m6_getElem_eq_getD st_q.core.wvec (d := 0#32)] at hc
                                    rw [fid_hag_wvec hb_q.hag] at hc
                                    change p.toNat <
                                      ((s.core.wvec[2 * (cv <<< (1 : Nat) ||| pol_q).toNat %
                                          2 ^ 64]?.getD 0#32).toNat +
                                        (s.core.wvec[(2 * (cv <<< (1 : Nat) ||| pol_q).toNat +
                                            1) % 2 ^ 64]?.getD 0#32).toNat) % 2 ^ 64 at hc
                                    rw [← hlit_def,
                                      show 2 * lit.toNat % 2 ^ 64 = 2 * lit.toNat from
                                        Nat.mod_eq_of_lt (by omega),
                                      show (2 * lit.toNat + 1) % 2 ^ 64 = 2 * lit.toNat + 1 from
                                        Nat.mod_eq_of_lt (by omega)] at hc
                                    change p.toNat <
                                      (fullWatchOffCore s.core lit.toNat +
                                        fullWatchSizeCore s.core lit.toNat) % 2 ^ 64 at hc
                                    have hw_lt : wEnd.toNat < 2 ^ 64 := wEnd.isLt
                                    rw [← hend_n, Nat.mod_eq_of_lt (by omega)] at hc
                                    exact hc
                                  m6_split
                                  · m6_steps; exact hJ_we (nv_w, nc_w, lim_w, p, ()) mw
                                      ⟨hnv_w_mono, st_w, hb_w, hmw⟩
                                  m6_split; rotate_left
                                  · m6_steps; exact hJ_we (nv_w, nc_w, lim_w, p, ()) mw
                                      ⟨hnv_w_mono, st_w, hb_w, hmw⟩
                                  have hncw_lt : nc_w.toNat < L.maxOrig :=
                                    Nat.lt_of_lt_of_le hc hmc_c_le
                                  have hwstk_eq : st_w.core.wstk = s.core.wstk :=
                                    fid_hag_wstk hb_w.hag
                                  have hcv_w : st_w.core.cur_vars = s.core.cur_vars :=
                                    fid_hag_cur_vars hb_w.hag
                                  have hp_wstk_w : p.toNat < st_w.core.wstk.length :=
                                    fid_cone_hp_wstk hwstk_eq hp_lt hend_ws
                                  have hp1 : (p + 1#64).toNat = p.toNat + 1 :=
                                    m6_bv64_add1 (by omega)
                                  obtain ⟨w0, hw0_def⟩ : ∃ w0 : BitVec 32,
                                      w0 = st_w.core.wstk[p.toNat]'hp_wstk_w := ⟨_, rfl⟩
                                  have hw0_s : s.core.wstk[p.toNat]? = some w0 := by
                                    rw [hw0_def, List.getElem?_eq_getElem (hwstk_eq ▸ hp_wstk_w)]
                                    exact congrArg some (by simp [hwstk_eq])
                                  m6_split
                                  · have hbin : (w0 &&& 0x80000000#32) ≠ 0#32 := by
                                      rw [hw0_def]; exact hc
                                    obtain ⟨_, _, _, hslice1⟩ :=
                                      m6_denseSlice_step_bin hslice (Nat.sub_pos_of_lt hp_lt)
                                        hw0_s hbin
                                    m6_steps
                                    exact hJ_w (nv_w, nc_w, lim_w, p + 1#64, ()) mw
                                      (by dsimp only; rw [hp1]; exact m6_nat_sub1_lt hp_lt rfl)
                                      ⟨by rw [hp1]; exact hp_lt, hnv_w_mono,
                                        by rw [hp1, fid_cone_sub_sub_eq]; exact hslice1,
                                        st_w, hb_w, hmw⟩
                                  · have hocc : (w0 &&& 0x80000000#32) = 0#32 := by
                                      rw [hw0_def]; exact hc
                                    obtain ⟨hrem2, _, cr, hcr_s, hcr_lt, hcr_ref, hslice2⟩ :=
                                      m6_denseSlice_step_occ hslice (Nat.sub_pos_of_lt hp_lt)
                                        hw0_s hocc
                                    m6_split
                                    · exfalso
                                      have hge : wEnd.toNat ≤ (p + 1#64).toNat := by
                                        simp only [hcv_qi0] at hc
                                        repeat rw [m6_getElem_eq_getD st_q.core.wvec
                                          (d := 0#32)] at hc
                                        rw [fid_hag_wvec hb_q.hag] at hc
                                        change ((s.core.wvec[2 * (cv <<< (1 : Nat) |||
                                            pol_q).toNat % 2 ^ 64]?.getD 0#32).toNat +
                                          (s.core.wvec[(2 * (cv <<< (1 : Nat) ||| pol_q).toNat +
                                              1) % 2 ^ 64]?.getD 0#32).toNat) % 2 ^ 64 ≤
                                          (p.toNat + 1) % 2 ^ 64 at hc
                                        rw [← hlit_def,
                                          show 2 * lit.toNat % 2 ^ 64 = 2 * lit.toNat from
                                            Nat.mod_eq_of_lt (by omega),
                                          show (2 * lit.toNat + 1) % 2 ^ 64 = 2 * lit.toNat + 1 from
                                            Nat.mod_eq_of_lt (by omega)] at hc
                                        change (fullWatchOffCore s.core lit.toNat +
                                          fullWatchSizeCore s.core lit.toNat) % 2 ^ 64 ≤
                                          (p.toNat + 1) % 2 ^ 64 at hc
                                        have hw_lt : wEnd.toNat < 2 ^ 64 := wEnd.isLt
                                        rw [← hend_n, Nat.mod_eq_of_lt (by omega), ← hp1,
                                          Nat.mod_eq_of_lt (p + 1#64).isLt] at hc
                                        exact hc
                                      omega
                                    have hp2 : (p + 1#64 + 1#64).toNat = p.toNat + 2 := by
                                      rw [m6_bv64_add1 (by rw [hp1]; omega), hp1]
                                    have hp2_le : (p + 1#64 + 1#64).toNat ≤ wEnd.toNat := by
                                      rw [hp2]; omega
                                    have har_s := hlen.core_ok.arena_len_arr
                                    have hcr_wf := hw.arena.refs_wf cr.toNat hcr_ref
                                    have hacap_lt := c.harena; unfold dimacsBound at hacap_lt
                                    have hal_le := hlen.core_ok.arena_len_le
                                    have hp1_lt_end : (p + 1#64).toNat < wEnd.toNat := by
                                      rw [hp1]; omega
                                    have hp1_wstk : (p + 1#64).toNat < st_w.core.wstk.length :=
                                      fid_cone_hp_wstk hwstk_eq hp1_lt_end hend_ws
                                    have hcr_eq : st_w.core.wstk[p.toNat + 1]'(hp1 ▸ hp1_wstk) =
                                        cr := by
                                      have hcr_w : st_w.core.wstk[p.toNat + 1]? = some cr :=
                                        hwstk_eq ▸ hcr_s
                                      rw [List.getElem?_eq_getElem (hp1 ▸ hp1_wstk)] at hcr_w
                                      exact Option.some.inj hcr_w
                                    have hcr_idx :
                                        ∀ {j : Nat} (hj : j < st_w.core.wstk.length),
                                          j = p.toNat + 1 → st_w.core.wstk[j]'hj = cr :=
                                      fun _ hij => by subst hij; exact hcr_eq
                                    have hcr2_lt : (BitVec.setWidth 64 cr + 2#64).toNat =
                                        cr.toNat + 2 := by
                                      simp only [BitVec.toNat_add, bv_c0_zext32_64,
                                        show (2#64 : BitVec 64).toNat = 2 from rfl]; omega
                                    have har_eq : st_w.core.arena = s.core.arena :=
                                      fid_hag_arena hb_w.hag
                                    have har_cr_bd : cr.toNat < st_w.core.arena.length := by
                                      rw [har_eq, har_s]; omega
                                    have har_cr2_bd : (BitVec.setWidth 64 cr + 2#64).toNat <
                                        st_w.core.arena.length := by
                                      rw [har_eq, har_s, hcr2_lt]; omega
                                    obtain ⟨sz, hsz_def⟩ : ∃ sz : BitVec 32,
                                        sz = st_w.core.arena[(BitVec.setWidth 64 cr + 2#64).toNat]'
                                          har_cr2_bd := ⟨_, rfl⟩
                                    have har_cr_idx :
                                        ∀ {k : Nat} (hk : k < st_w.core.arena.length), k = cr.toNat
                                          → st_w.core.arena[k]'hk =
                                            st_w.core.arena[cr.toNat]'har_cr_bd :=
                                      fun _ hkeq => Option.some.inj (by subst hkeq; rfl)
                                    have har_sz_idx :
                                        ∀ {k : Nat} (hk : k < st_w.core.arena.length),
                                          k = (BitVec.setWidth 64 cr + 2#64).toNat →
                                          st_w.core.arena[k]'hk = sz :=
                                      fun _ hkeq => Option.some.inj (by subst hkeq; rw [hsz_def])
                                    have hsz_core : sz.toNat =
                                        fullArenaClauseSizeCore s.core cr.toNat := by
                                      unfold fullArenaClauseSizeCore; rw [hsz_def]
                                      rw [List.getElem?_eq_getElem (by rw [har_s]; omega),
                                        Option.getD_some]
                                      simp only [har_eq, hcr2_lt]
                                    have hstep_occ : ∀ (nv_x nc_x : BitVec 32) (lim_x : Bool)
                                        (st_x : FullState) (mx : Mem 64),
                                        layer_end.toNat ≤ nv_x.toNat →
                                        FidConeBase F_cur L mv_c c s cv qi_l nv_x.toNat
                                          nc_x.toNat st_x →
                                        (FullMem c st_x ⋆ R) mx →
                                        J_w (nv_x, nc_x, lim_x, p + 1#64 + 1#64, ()) mx :=
                                      fun nv_x nc_x lim_x st_x mx hnvx hbx hmx =>
                                        hJ_w (nv_x, nc_x, lim_x, p + 1#64 + 1#64, ()) mx
                                          (by dsimp only; exact m6_nat_sub2_lt hp_lt hp2_le hp2)
                                          ⟨hp2_le, hnvx,
                                            by rw [hp2, fid_cone_sub_sub_eq]; exact hslice2,
                                            st_x, hbx, hmx⟩
                                    have hocc_done : J_w (nv_w, nc_w, lim_w, p + 1#64 + 1#64, ())
                                      mw := hstep_occ nv_w nc_w lim_w st_w mw hnv_w_mono hb_w hmw
                                    have hp_mod :
                                        (p.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 =
                                          p.toNat + 1 :=
                                      fid_cone_wstk_p_toNat_eq p (by omega)
                                    have hcr_w_p1 : st_w.core.wstk[(p + 1#64).toNat]'hp1_wstk =
                                        cr :=
                                      hcr_idx _ hp1
                                    have har_cr_bd' :
                                        (BitVec.setWidth 64
                                          (st_w.core.wstk[(p + 1#64).toNat]'hp1_wstk)).toNat <
                                          st_w.core.arena.length := by
                                      rw [hcr_w_p1, bv_c0_zext32_64]; exact har_cr_bd
                                    m6_split; · m6_steps; exact hocc_done
                                    have har_cr2_bd' :
                                        (BitVec.setWidth 64
                                          (st_w.core.wstk[(p + 1#64).toNat]'hp1_wstk) +
                                            2#64).toNat < st_w.core.arena.length := by
                                      rw [hcr_w_p1]; exact har_cr2_bd
                                    m6_split; · m6_steps; exact hocc_done
                                    have hgr0 : (st_w.core.arena[cr.toNat]'har_cr_bd &&&
                                        (0x00080000#32 ||| 0x00400000#32)) = 0#32 := by
                                      rw [har_cr_idx] at hc
                                      · exact hc
                                      · rw [hcr_idx _ hp_mod]
                                    m6_split; · m6_steps; exact hocc_done
                                    have hsz_ge3 : 3 ≤ sz.toNat := by
                                      rw [har_sz_idx] at hc
                                      · exact Nat.le_of_not_lt hc
                                      · rw [hcr_idx]
                                        · rw [hcr2_lt,
                                            show BitVec.toNat (2 : BitVec 64) =
                                                        2 from rfl,
                                            Nat.mod_eq_of_lt (by omega)]
                                        · exact hp_mod
                                    m6_split; · m6_steps; exact hocc_done
                                    obtain ⟨hng, hcr_sz_le, hsz_cv, hcr3_bd⟩ :=
                                      m6_cone_occ_hdr_ok hlen hw hnd har_eq hcr_ref hsz_core hgr0
                                    have hsz_ar :
                                        (s.core.arena[cr.toNat + 2]?.getD 0#32).toNat = sz.toNat :=
                                      hsz_core.symm
                                    have hnd_cl : ((fullArenaClauseLits s cr.toNat).map (· /
                                      2)).Nodup := hnd cr.toNat hcr_ref hng
                                    obtain ⟨saved_nv, hsav_eq⟩ : ∃ saved_nv : BitVec 32,
                                        saved_nv = nv_w := ⟨_, rfl⟩
                                    obtain ⟨scr_sav, hscr_sav_eq⟩ : ∃ scr_sav : List (BitVec 32),
                                        scr_sav = st_w.scratch.scratch_buf := ⟨_, rfl⟩
                                    have hsav_ge1 : 1 ≤ saved_nv.toNat :=
                                      hsav_eq ▸ hb_w.hcone.nv_ge1
                                    have hbdd_sav : K6LitsBounded saved_nv.toNat
                                        (k6StateOfScratch L scr_sav) :=
                                      hsav_eq ▸ hscr_sav_eq ▸ hb_w.hcone.k6_bdd
                                    have htrl_sav : ∀ l ∈ k6TrailLits (k6StateOfScratch L scr_sav),
                                        l < 2 * saved_nv.toNat :=
                                      hsav_eq ▸ hscr_sav_eq ▸ hb_w.hcone.k6_trl_bdd
                                    clear hslice hslice2 hw0_s hocc hwv0_eq hwv1_eq h2l_mod
                                      h2l1_mod hsz_def
                                    m6_to_group
                                    refine wp_join_group (ts := [i32, .bool, .bool, i32, i32])
                                      (fun (nv_e, _lim_e, drop_e, cnt_e, idx_e, ()) m_e =>
                                        ∃ st_e : FullState,
                                          FidConeSavedBase F_cur L mv_c c s cv qi_l saved_nv
                                            st_w.scratch.work_stk1 scr_sav
                                            nv_e.toNat nc_w.toNat st_e
                                          ∧ (drop_e = false →
                                            idx_e.toNat = sz.toNat ∧ cnt_e.toNat ≤ idx_e.toNat ∧
                                            (∀ j < cnt_e.toNat,
                                              (st_e.core.tmp[j]?.getD 0#32).toNat <
                                                2 * nv_e.toNat) ∧
                                            (∀ i < idx_e.toNat,
                                              let l := (s.core.arena[cr.toNat + 3 + i]?.getD
                                                0#32).toNat
                                              s.core.vals[l]?.getD 0#8 = 0xFF#8 ∨
                                              l ∈ (st_e.core.tmp.take cnt_e.toNat).map
                                                (fun x => m6ConeLift
                                                  st_e.scratch.work_stk1 x.toNat)) ∧
                                            (∀ j1 j2, j1 < cnt_e.toNat → j2 < cnt_e.toNat →
                                              j1 ≠ j2 →
                                              (st_e.core.tmp[j1]?.getD 0#32).toNat / 2 ≠
                                                (st_e.core.tmp[j2]?.getD 0#32).toNat / 2)) ∧
                                          (FullMem c st_e ⋆ R) m_e)
                                      (fun _ (nv_e, lim_e, drop_e, cnt_e, idx_e, ()) m_e
                                          ⟨st_e, hs_e, hndrop, hme⟩ => by
                                        m6_split
                                        · -- `drop = true`: rollback `while (nv > saved_nv)`
                                          m6_to_group
                                          refine wp_loop_inv (ts := [i32])
                                            (fun (nv_r, ()) mr =>
                                              nv_r.toNat ≤ nv_e.toNat ∧ ∃ st_r : FullState,
                                                FidConeSavedBase F_cur L mv_c c s cv qi_l saved_nv
                                                  st_w.scratch.work_stk1 scr_sav nv_r.toNat
                                                  nc_w.toNat st_r ∧
                                                (FullMem c st_r ⋆ R) mr)
                                            (fun (nv_r, ()) _ => nv_r.toNat - saved_nv.toNat)
                                            (fun _ hJr => by
                                              m6_steps
                                              exact hJr (nv_e, ()) m_e
                                                ⟨le_refl _, st_e, hs_e, hme⟩)
                                            (fun _ (nv_r, ()) mr ⟨hle_e, st_r, hs_r, hmr⟩ hJr => by
                                              m6_split
                                              · have hsav_lt : saved_nv.toNat < nv_r.toNat := by
                                                  rw [hsav_eq]; exact hc
                                                obtain ⟨hnv1, hvr_lt, hstep⟩ :=
                                                  fid_coneBase_of_rollback_step hs_r
                                                    hsav_ge1 hsav_lt
                                                    (by
                                                      rw [hsav_eq]
                                                      exact Nat.lt_of_lt_of_le
                                                        hqi_l_lt hnv_w_mono)
                                                    hbdd_sav htrl_sav
                                                obtain ⟨hvr_tmk_bd, hs'⟩ := hstep hvr_lt
                                                m6_steps
                                                refine hJr (nv_r - 1#32, ()) _
                                                  (by
                                                    dsimp only
                                                    exact m6_nat_sub_lo1_lt hsav_lt hnv1)
                                                  ⟨hnv1 ▸ le_trans (Nat.sub_le _ _) hle_e,
                                                    _, hs', ?_⟩
                                                try rw [m6_tmk_set_mod64] at hm
                                                exact fid_cone_rollback_mem_step _ hvr_lt
                                                  (m6_bv32_sub1_zext_toNat nv_r) hm
                                              · have hnv_le_sav : nv_r.toNat ≤ saved_nv.toNat := by
                                                  rw [hsav_eq]; exact Nat.le_of_not_lt hc
                                                m6_steps
                                                have hnv_eq : nv_r = saved_nv :=
                                                  BitVec.eq_of_toNat_eq
                                                    (Nat.le_antisymm hnv_le_sav hs_r.hsav_le)
                                                have hle_nv_r : layer_end.toNat ≤ nv_r.toNat := by
                                                  rw [hnv_eq, hsav_eq]; exact hnv_w_mono
                                                exact hstep_occ nv_r nc_w lim_e st_r mr
                                                  hle_nv_r (hnv_eq ▸ hs_r.toFidConeBase) hmr)
                                        · -- `drop = false`: call `full_k6_add_clause`
                                          obtain ⟨hk_eq, hcnt_le, hlts_e, hcov_e, hnd_e⟩ :=
                                            hndrop (by cases drop_e <;> simp at hc ⊢)
                                          have hcnt_le_nv : cnt_e.toNat ≤ nv_e.toNat :=
                                            m6_cone_cnt_le_nv hlts_e hnd_e
                                          have hnv_e_max := hs_e.hcone.nv_leMax
                                          have hcnt_le28 : cnt_e.toNat < 2 ^ 28 := by omega
                                          have hcnt_tmp : cnt_e.toNat ≤ st_e.core.tmp.length := by
                                            rw [hs_e.hlen.core_ok.tmp_len_arr]
                                            exact Nat.le_trans hcnt_le_nv
                                              (Nat.le_trans hs_e.hcone.nv_le_cv (by
                                                rw [fid_hag_cur_vars hs_e.hag]; exact hcv_le))
                                          have hent_ke : (cnfOfClauses F_cur).EntailsClause
                                              (cnfClause ((st_e.core.tmp.take cnt_e.toNat).map
                                                (fun x => m6ConeLift
                                                  st_e.scratch.work_stk1 x.toNat))) := by
                                            refine m6_cone_clause_entails_filtered hw hcl0 hcr_ref
                                              hng fun l hl => ?_
                                            obtain ⟨i, hi, rfl⟩ :=
                                              (m6_arenaClauseLitsCore_mem_iff
                                                (by rw [hsz_ar]; exact hcr3_bd)).mp hl
                                            rw [hsz_ar] at hi
                                            exact hcov_e i (hk_eq.symm ▸ hi)
                                          m6_steps
                                          refine fid_cone_call_add_clause hAddCl
                                            (aSz := Arg.var cnt_e) rfl hL_len hL_mv hs_e.hlen
                                            hs_e.hag hs_e.hcone hncw_lt hcnt_le28 hcnt_tmp hlts_e
                                            hent_ke hme
                                            (fun ok st' m' hl' ha' hc' hfalse_scr ht_eq hw_eq hm'
                                              => by
                                              m6_split
                                              · have hic := (fid_cone_load_kptr_hdr hc' hm').1
                                                m6_to_group
                                                refine wp_join_group (ts := [.bool])
                                                  (fun (_lim', ()) m'' => m'' = m')
                                                  (fun _ (lim', ()) m'' hm'' => by
                                                    subst m''
                                                    m6_steps
                                                    exact hstep_occ nv_e (nc_w + 1#32) lim' st' m'
                                                      (Nat.le_trans hnv_w_mono
                                                        (hsav_eq ▸ hs_e.hsav_le))
                                                      ⟨hl', ha', by simpa only [hc, ↓reduceIte]
                                                        using hc', ht_eq ▸ hs_e.htmk,
                                                        hw_eq ▸ hs_e.hwk⟩
                                                      hm')
                                                  (fun _ hJ_inc => by
                                                    change wp _ _ _ _ _
                                                    c0_hsteps
                                                    dsimp only [Prod.fst]
                                                    try (first | rw [hkptr_c0] | rw [hkptr_c0_nat])
                                                    try rw [show (BitVec.ofNat (OfNat.ofNat 64)
                                                      (OfNat.ofNat 6) : BitVec 64) = 6#64 from rfl]
                                                    refine head_wp_load rfl hic ?_
                                                    m6_split
                                                    · m6_steps; exact hJ_inc (true, ()) m' rfl
                                                    · m6_steps; exact hJ_inc (lim_e, ()) m' rfl)
                                              · have hs'_saved :
                                                    FidConeSavedBase F_cur L mv_c c s cv qi_l
                                                    saved_nv st_w.scratch.work_stk1 scr_sav
                                                    nv_e.toNat nc_w.toNat st' :=
                                                  ⟨⟨hl', ha', by simpa only [hc, Bool.false_eq_true,
                                                      ↓reduceIte] using hc', ht_eq ▸ hs_e.htmk,
                                                      hw_eq ▸ hs_e.hwk⟩,
                                                    hs_e.hsav_le,
                                                    (hfalse_scr (by cases ok <;> simp at hc ⊢)
                                                      ).trans
                                                      hs_e.hscr,
                                                    hw_eq ▸ hs_e.hws⟩
                                                m6_to_group
                                                refine wp_loop_inv (ts := [i32])
                                                  (fun (nv_r, ()) mr =>
                                                    nv_r.toNat ≤ nv_e.toNat ∧ ∃ st_r : FullState,
                                                      FidConeSavedBase F_cur L mv_c c s cv
                                                        qi_l saved_nv
                                                        st_w.scratch.work_stk1 scr_sav nv_r.toNat
                                                        nc_w.toNat st_r ∧
                                                      (FullMem c st_r ⋆ R) mr)
                                                  (fun (nv_r, ()) _ => nv_r.toNat - saved_nv.toNat)
                                                  (fun _ hJr => by
                                                    m6_steps
                                                    exact hJr (nv_e, ()) m'
                                                      ⟨le_refl _, st', hs'_saved, hm'⟩)
                                                  (fun _ (nv_r, ()) mr ⟨hle_e, st_r, hs_r, hmr⟩
                                                      hJr => by
                                                    m6_split
                                                    · have hsav_lt :
                                                          saved_nv.toNat < nv_r.toNat := by
                                                        rw [hsav_eq]; exact hc
                                                      obtain ⟨hnv1, hvr_lt, hstep⟩ :=
                                                        fid_coneBase_of_rollback_step hs_r hsav_ge1
                                                          hsav_lt (by
                                                            rw [hsav_eq]
                                                            exact
                                                              Nat.lt_of_lt_of_le hqi_l_lt
                                                                hnv_w_mono)
                                                          hbdd_sav htrl_sav
                                                      obtain ⟨hvr_tmk_bd, hs'⟩ := hstep hvr_lt
                                                      m6_steps
                                                      refine hJr (nv_r - 1#32, ()) _
                                                        (by
                                                          dsimp only
                                                          exact m6_nat_sub_lo1_lt hsav_lt hnv1)
                                                        ⟨hnv1 ▸ le_trans (Nat.sub_le _ _) hle_e,
                                                          _, hs', ?_⟩
                                                      try rw [m6_tmk_set_mod64] at hm
                                                      exact fid_cone_rollback_mem_step _ hvr_lt
                                                        (m6_bv32_sub1_zext_toNat nv_r) hm
                                                    · have hnv_le_sav :
                                                          nv_r.toNat ≤ saved_nv.toNat := by
                                                        rw [hsav_eq]; exact Nat.le_of_not_lt hc
                                                      m6_steps
                                                      have hnv_eq : nv_r = saved_nv :=
                                                        BitVec.eq_of_toNat_eq
                                                          (Nat.le_antisymm hnv_le_sav hs_r.hsav_le)
                                                      have hle_nv_r :
                                                          layer_end.toNat ≤ nv_r.toNat := by
                                                        rw [hnv_eq, hsav_eq]; exact hnv_w_mono
                                                      exact hstep_occ nv_r nc_w true st_r mr
                                                        hle_nv_r
                                                        (hnv_eq ▸ hs_r.toFidConeBase) hmr)))
                                      (fun _ hJ_occ => by
                                        m6_to_group
                                        refine wp_loop_inv (ts := [i32, i32, i32])
                                          (fun (nv_k, cnt, idx, ()) mk =>
                                            idx.toNat ≤ sz.toNat ∧ cnt.toNat ≤ idx.toNat ∧
                                            ∃ st_k : FullState,
                                              FidConeScanBase F_cur L mv_c c s cv qi_l saved_nv
                                                st_w.scratch.work_stk1 scr_sav cr nv_k.toNat
                                                nc_w.toNat cnt.toNat idx.toNat st_k ∧
                                              (FullMem c st_k ⋆ R) mk)
                                          (fun (_, _, idx, ()) _ => sz.toNat - idx.toNat)
                                          (fun _ hJ_k => by
                                            m6_steps
                                            exact hJ_k (nv_w, 0#32, 0#32, ()) mw
                                              ⟨Nat.zero_le _, Nat.zero_le _, st_w,
                                               ⟨⟨hb_w, hsav_eq ▸ le_refl _, hscr_sav_eq.symm,
                                                 fun _ _ => rfl⟩,
                                                fun _ hj => by simp at hj,
                                                fun _ hi => by simp at hi,
                                                fun _ hj => by simp at hj,
                                                fun _ _ h1 => by simp at h1⟩, hmw⟩)
                                          (fun _ (nv_k, cnt, idx, ()) mk
                                              ⟨hk_le, hcnt_le, st_k, hs_k, hmk⟩ hJ_k => by
                                            clear hJ_in hJ_we hJ_w hstep_occ
                                              hocc_done hsav_ge1 hbdd_sav htrl_sav
                                              hL_len hL_mv hAddCl hmo_nat
                                              hmv_eq hqi1 hcv_lt_s hmL hmx
                                            try clear hcv_qi
                                            m6_split; rotate_left
                                            · have hidx_ge : sz.toNat ≤ idx.toNat := by
                                                rw [har_sz_idx] at hc
                                                · exact Nat.le_of_not_lt hc
                                                · rw [hcr_idx]
                                                  · rw [hcr2_lt,
                                                      show BitVec.toNat (2 : BitVec 64) =
                                                        2 from rfl,
                                                      Nat.mod_eq_of_lt (by omega)]
                                                  · exact hp_mod
                                              have hk_eq : idx.toNat = sz.toNat :=
                                                Nat.le_antisymm hk_le hidx_ge
                                              m6_steps
                                              exact hJ_occ (nv_k, lim_w, false, cnt, idx, ()) mk
                                                ⟨st_k, hs_k.toFidConeSavedBase,
                                                 fun _ => ⟨hk_eq, hcnt_le, hs_k.hlts, hs_k.hcov,
                                                   hs_k.hnd⟩, hmk⟩
                                            · -- Body of `idx < sz` loop
                                              have hk_lt : idx.toNat < sz.toNat := by
                                                rw [har_sz_idx] at hc
                                                · exact hc
                                                · rw [hcr_idx]
                                                  · rw [hcr2_lt,
                                                      show BitVec.toNat (2 : BitVec 64) =
                                                        2 from rfl,
                                                      Nat.mod_eq_of_lt (by omega)]
                                                  · exact hp_mod
                                              have hae_k := fid_hag_arena hs_k.hag
                                              have hve_k := fid_hag_vals hs_k.hag
                                              have har_k := hs_k.hlen.core_ok.arena_len_arr
                                              have hvals_k := hs_k.hlen.core_ok.vals_len
                                              have hidx_k : (BitVec.setWidth 64 cr + 3#64 +
                                                  BitVec.setWidth 64 idx).toNat =
                                                  cr.toNat + 3 + idx.toNat := by
                                                simp only [bv_c0_zext32_64, BitVec.toNat_add,
                                                  show (3#64 : BitVec 64).toNat = 3 from rfl]
                                                omega
                                              have hidx_bd : (BitVec.setWidth 64 cr + 3#64 +
                                                  BitVec.setWidth 64 idx).toNat <
                                                  st_k.core.arena.length := by
                                                rw [har_k, hidx_k]; omega
                                              have hl_in_cl :
                                                  (st_k.core.arena[cr.toNat + 3 + idx.toNat]'(by
                                                      rw [har_k]; omega)).toNat ∈
                                                    fullArenaClauseLitsCore s.core cr.toNat := by
                                                rw [m6_arenaClauseLitsCore_mem_iff
                                                  (by rw [hsz_ar]; exact hcr3_bd)]
                                                refine ⟨idx.toNat, by rw [hsz_ar]; exact hk_lt, ?_⟩
                                                rw [List.getElem?_eq_getElem
                                                    (by rw [← hae_k, har_k]; omega),
                                                  Option.getD_some]
                                                simp [hae_k]
                                              obtain ⟨lit_k, hlit_k_def⟩ : ∃ lit_k : BitVec 32,
                                                  lit_k = st_k.core.arena[(BitVec.setWidth 64 cr +
                                                    3#64 + BitVec.setWidth 64 idx).toNat]'hidx_bd
                                                := ⟨_, rfl⟩
                                              have hl_lt_s : lit_k.toNat < 2 * s.core.cur_vars := by
                                                rw [hlit_k_def]
                                                simpa only [hidx_k] using
                                                  hw.arena.lits_lt cr.toNat hcr_ref hng _ hl_in_cl
                                              have hval_bd : lit_k.toNat < st_k.core.vals.length :=
                                                by rw [hvals_k]; omega
                                              have hk1 : (idx + 1#32).toNat = idx.toNat + 1 :=
                                                m6_bv32_add1 (by omega)
                                              have hlit_ar : (s.core.arena[cr.toNat + 3 +
                                                  idx.toNat]?.getD 0#32).toNat = lit_k.toNat := by
                                                rw [List.getElem?_eq_getElem
                                                    (by rw [← hae_k, har_k]; omega),
                                                  Option.getD_some]
                                                simp only [hlit_k_def, hidx_k, hae_k]
                                              have har_hc_idx :
                                                  (cr.toNat + BitVec.toNat (3 : BitVec 64) +
                                                    BitVec.toNat idx) % 2 ^ 64 =
                                                    cr.toNat + 3 + idx.toNat := by
                                                rw [show BitVec.toNat (3 : BitVec 64) = 3 from rfl,
                                                  Nat.mod_eq_of_lt (by omega)]
                                              have hidx_bd_w : (BitVec.setWidth 64
                                                  (st_w.core.wstk[(p + 1#64).toNat]'hp1_wstk) +
                                                    3#64 + BitVec.setWidth 64 idx).toNat <
                                                  st_k.core.arena.length := by
                                                rw [hcr_w_p1]; exact hidx_bd
                                              have h_ar_lk_w :
                                                  st_k.core.arena[(BitVec.setWidth 64
                                                      (st_w.core.wstk[(p + 1#64).toNat]'hp1_wstk) +
                                                      3#64 + BitVec.setWidth 64 idx).toNat]'
                                                      hidx_bd_w = lit_k :=
                                                hlit_k_def ▸ m6_list_getElem_congr
                                                  (by rw [hcr_w_p1])
                                                  hidx_bd_w hidx_bd
                                              have h_ar_lk_w1 : ∀ {pf1 pf2},
                                                  st_k.core.arena[(BitVec.setWidth 64
                                                      (st_w.core.wstk[(p +
                                                        (1 : BitVec 64)).toNat]'pf1) +
                                                      (3 : BitVec 64) +
                                                      BitVec.setWidth 64 idx).toNat]'pf2 = lit_k :=
                                                fun {pf1 _} =>
                                                  have hw1 :
                                                      st_w.core.wstk[(p +
                                                        (1 : BitVec 64)).toNat]'pf1 = cr :=
                                                    (m6_list_getElem_congr rfl pf1
                                                      hp1_wstk).trans hcr_w_p1
                                                  hlit_k_def ▸ m6_list_getElem_congr
                                                    (by rw [hw1]; rfl) _ hidx_bd
                                              have hval_bd_w : (BitVec.setWidth 64
                                                  (st_k.core.arena[(BitVec.setWidth 64
                                                    (st_w.core.wstk[(p + 1#64).toNat]'hp1_wstk) +
                                                    3#64 + BitVec.setWidth 64
                                                      idx).toNat]'hidx_bd_w)).toNat <
                                                  st_k.core.vals.length := by
                                                rw [bv_c0_zext32_64, h_ar_lk_w]; exact hval_bd
                                              m6_split
                                              · m6_steps
                                                exact hJ_occ (nv_k, lim_w, true, cnt, idx, ()) mk
                                                  ⟨st_k, hs_k.toFidConeSavedBase,
                                                   (fun h => by cases h), hmk⟩
                                              have hnot_pos : s.core.vals[lit_k.toNat]?.getD
                                                  0#8 ≠ 1#8 := fun h1 => by
                                                rw [m6_getElem_eq_getD st_k.core.vals (d := 0#8),
                                                  m6_getElem_eq_getD st_k.core.arena (d := 0#32),
                                                  hcr_idx _ hp_mod, har_hc_idx, hae_k, hlit_ar,
                                                  hve_k, h1] at hc
                                                exact absurd hc (by decide)
                                              m6_to_group
                                              refine wp_join_group (ts := [i32, .bool, .bool, i32])
                                                (fun (nv_u, lim_u, drop_u, cnt_u, ()) m_u =>
                                                  lim_u = lim_w ∧ drop_u = false ∧
                                                  cnt.toNat ≤ cnt_u.toNat ∧
                                                  cnt_u.toNat ≤ idx.toNat + 1 ∧
                                                  ∃ st_u' : FullState,
                                                    FidConeScanBase F_cur L mv_c c s cv
                                                      qi_l saved_nv
                                                      st_w.scratch.work_stk1 scr_sav cr nv_u.toNat
                                                      nc_w.toNat cnt_u.toNat (idx.toNat + 1) st_u'
                                                    ∧ (FullMem c st_u' ⋆ R) m_u)
                                                (fun _ (nv_u, lim_u, drop_u, cnt_u, ()) m_u
                                                    ⟨_, _, _, hc1, st_u', hs_u', hmu'⟩ => by
                                                  m6_steps
                                                  refine hJ_k (nv_u, cnt_u, idx + 1#32, ()) m_u
                                                    (by
                                                      dsimp only; rw [hk1]
                                                      exact m6_nat_sub1_lt hk_lt rfl)
                                                    ⟨by rw [hk1]; exact hk_lt,
                                                     by rw [hk1]; exact hc1, st_u',
                                                     by rw [hk1]; exact hs_u', hmu'⟩)
                                                (fun _ hJ_lv => by
                                                  m6_split
                                                  · have hl_zero : s.core.vals[lit_k.toNat]?.getD
                                                        0#8 = 0#8 := by
                                                      rcases hw.vals_domain lit_k.toNat hl_lt_s
                                                        with h0 | h1 | hf
                                                      · exact h0
                                                      · exact absurd h1 hnot_pos
                                                      · rw [m6_getElem_eq_getD st_k.core.vals
                                                            (d := 0#8),
                                                          m6_getElem_eq_getD st_k.core.arena
                                                            (d := 0#32),
                                                          hcr_idx _ hp_mod, har_hc_idx, hae_k,
                                                          hlit_ar, hve_k, hf] at hc
                                                        exact absurd hc (by decide)
                                                    have hlv_eq : (lit_k >>> (1 : Nat)).toNat =
                                                        lit_k.toNat / 2 :=
                                                      m6_bv32_shr1_toNat lit_k
                                                    have hlv_lt : (lit_k >>> (1 : Nat)).toNat <
                                                        s.core.cur_vars := by omega
                                                    have hlv_tm_k : (BitVec.setWidth 64
                                                        (lit_k >>> (1 : Nat))).toNat <
                                                        st_k.scratch.tarjan_mark.length := by
                                                      rw [hs_k.hlen.scratch_ok.tarjan_mark_len,
                                                        bv_c0_zext32_64]; omega
                                                    have hlv_tm_k_w : (BitVec.setWidth 64
                                                        (st_k.core.arena[(BitVec.setWidth 64
                                                          (st_w.core.wstk[(p +
                                                            1#64).toNat]'hp1_wstk) + 3#64 +
                                                            BitVec.setWidth 64 idx).toNat]'
                                                            hidx_bd_w >>> (1 : Nat))).toNat <
                                                        st_k.scratch.tarjan_mark.length := by
                                                      rw [h_ar_lk_w]; exact hlv_tm_k
                                                    have hfl_k := hs_k.hlen.core_ok.flags_len
                                                    have hlv_fl_k : (BitVec.setWidth 64
                                                        (lit_k >>> (1 : Nat))).toNat <
                                                        st_k.core.flags.length := by
                                                      rw [hfl_k, bv_c0_zext32_64]; omega
                                                    have hlv_fl_k_w : (BitVec.setWidth 64
                                                        (st_k.core.arena[(BitVec.setWidth 64
                                                          (st_w.core.wstk[(p +
                                                            1#64).toNat]'hp1_wstk) + 3#64 +
                                                            BitVec.setWidth 64 idx).toNat]'
                                                            hidx_bd_w >>> (1 : Nat))).toNat <
                                                        st_k.core.flags.length := by
                                                      rw [h_ar_lk_w]; exact hlv_fl_k
                                                    m6_split
                                                    · m6_steps
                                                      exact hJ_occ (nv_k, lim_w, true, cnt, idx,
                                                        ()) mk
                                                        ⟨st_k, hs_k.toFidConeSavedBase,
                                                         (fun h => by cases h), hmk⟩
                                                    m6_to_group
                                                    refine wp_join_group (ts := [])
                                                      (fun () m_d => m_d = mk)
                                                      (fun _ () m_d hmd => by
                                                        subst m_d
                                                        m6_to_group
                                                        refine wp_join_group (ts := [])
                                                          (fun () m_c => m_c = mk)
                                                          (fun _ () m_c hmc => by
                                                            subst m_c
                                                            m6_to_group
                                                            refine wp_join_group
                                                              (ts := [i32, .bool, .bool])
                                                              (fun (nv_u, lim_u, drop_u, ()) m_u =>
                                                                lim_u = lim_w ∧ drop_u = false ∧
                                                                nv_k.toNat ≤ nv_u.toNat ∧
                                                                ∃ st_u : FullState,
                                                                  FidConeSavedBase F_cur L mv_c
                                                                    c s cv
                                                                    qi_l saved_nv
                                                                    st_w.scratch.work_stk1 scr_sav
                                                                    nv_u.toNat nc_w.toNat st_u ∧
                                                                  st_u.core.tmp = st_k.core.tmp ∧
                                                                  (∀ j < nv_k.toNat,
                                                                    st_u.scratch.work_stk1[j]? =
                                                                      st_k.scratch.work_stk1[j]?) ∧
                                                                  st_u.scratch.tarjan_mark[(lit_k
                                                                    >>> (1 : Nat)).toNat]?.getD
                                                                    0#32 ≠ 0#32 ∧
                                                                  (FullMem c st_u ⋆ R) m_u)
                                                              (fun _ (nv_u, lim_u, drop_u, ()) m_u
                                                                  ⟨hlim_u, hdrop_u, hnvku, st_u,
                                                                   hs_u, htmpu, hwku, htlv, hmu⟩ =>
                                                                     by
                                                                have htm_u :=
                                                                  hs_u.hlen.2.tarjan_mark_len
                                                                have htmp_u :=
                                                                  hs_u.hlen.core_ok.tmp_len_arr
                                                                have hcv_u :=
                                                                  fid_hag_cur_vars hs_u.hag
                                                                rcases hs_u.hcone.rev
                                                                  (lit_k >>> (1 : Nat)).toNat
                                                                    (by rw [hcv_u]; exact hlv_lt)
                                                                      with
                                                                  hz | ⟨ilv, hilv, hwlv, htlv_v⟩
                                                                · exact absurd hz htlv
                                                                have hnv_u_max :=
                                                                  hs_u.hcone.nv_leMax
                                                                obtain ⟨hcnt1, hlu', hlts_u',
                                                                    hcov_u', hvars_u', hnd_u'⟩ :=
                                                                  fid_cone_k_unassigned_step
                                                                  hs_u.hlen
                                                                    htmpu hwku hnvku hnv_u_max
                                                                    hk_lt hsz_cv hcv_le hcnt_le
                                                                    hlit_ar hilv (hlv_eq ▸ hwlv)
                                                                    (hlv_eq ▸ htlv_v) hs_k.hlts
                                                                    hs_k.hcov hs_k.hvars hs_k.hnd
                                                                    hnd_cl hcr3_bd hsz_core
                                                                    hs_u.hcone
                                                                have hcnt_tmp : (BitVec.setWidth 64
                                                                    cnt).toNat <
                                                                    st_u.core.tmp.length := by
                                                                  rw [htmp_u, bv_c0_zext32_64]
                                                                  omega
                                                                have hcnt_tmp' : cnt.toNat <
                                                                    st_u.core.tmp.length := by
                                                                  rw [← bv_c0_zext32_64 cnt]
                                                                  exact hcnt_tmp
                                                                have hlv_tm_u_w : (BitVec.setWidth
                                                                    64 (st_k.core.arena[
                                                                    (BitVec.setWidth 64
                                                                    (st_w.core.wstk[(p +
                                                                      1#64).toNat]'hp1_wstk) +
                                                                    3#64 + BitVec.setWidth 64
                                                                      idx).toNat]'hidx_bd_w >>>
                                                                    (1 : Nat))).toNat <
                                                                    List.length
                                                                      st_u.scratch.tarjan_mark
                                                                    := by
                                                                  rw [h_ar_lk_w, htm_u,
                                                                    bv_c0_zext32_64]; omega
                                                                m6_steps
                                                                have htm_u_lk : ∀ {pf1 pf2 pf3},
                                                                    st_u.scratch.tarjan_mark[
                                                                      (BitVec.setWidth 64
                                                                      (st_k.core.arena[
                                                                        (BitVec.setWidth 64
                                                                          (st_w.core.wstk[(p +
                                                                            (1 : BitVec
                                                                              64)).toNat]'pf1) +
                                                                          (3 : BitVec 64) +
                                                                          BitVec.setWidth 64
                                                                            idx).toNat]'pf2 >>>
                                                                        (OfNat.ofNat 1 :
                                                                          Nat))).toNat]'pf3 =
                                                                      st_u.scratch.tarjan_mark[
                                                                        lit_k.toNat / 2]?.getD
                                                                        0#32 :=
                                                                  fun {_ _ _} => by
                                                                  have hlen_t :
                                                                      lit_k.toNat / 2 <
                                                                        List.length
                                                                          st_u.scratch.tarjan_mark
                                                                        := by rw [htm_u]; omega
                                                                  rw [List.getElem?_eq_getElem
                                                                    hlen_t, Option.getD_some]
                                                                  exact m6_list_getElem_congr
                                                                    (by
                                                                      rw [h_ar_lk_w1,
                                                                        bv_c0_zext32_64]
                                                                      exact hlv_eq) _ _
                                                                have hcnt_n : (BitVec.setWidth 64
                                                                    cnt).toNat = cnt.toNat :=
                                                                  bv_c0_zext32_64 cnt
                                                                let nl_u :=
                                                                  ((st_u.scratch.tarjan_mark[
                                                                    lit_k.toNat / 2]?.getD
                                                                    0#32 - 1#32) <<< (1 : Nat)) |||
                                                                    (lit_k &&& 1#32)
                                                                let st_u' : FullState :=
                                                                  { st_u with core :=
                                                                    { st_u.core with
                                                                      tmp :=
                                                                        st_u.core.tmp.set
                                                                          cnt.toNat nl_u } }
                                                                have hm_u' : (FullMem c st_u' ⋆
                                                                    R) m := by
                                                                  have hm' := hm
                                                                  dsimp only [LeanQbe.T.lift2,
                                                                    Arg.val_var, Arg.val_imm,
                                                                    Prod.fst] at hm'
                                                                  rw [hcnt_n, htm_u_lk,
                                                                    h_ar_lk_w1] at hm'
                                                                  exact hm'
                                                                refine hJ_lv (nv_u, lim_u, drop_u,
                                                                  cnt + 1#32, ()) m
                                                                  ⟨hlim_u, hdrop_u, by omega,
                                                                   by rw [hcnt1]; omega, st_u',
                                                                   ⟨⟨⟨hlu',
                                                                      fidConeMask_upd_tmp _
                                                                        hs_u.hag,
                                                                      fidConeInv_tmp_irrel
                                                                       hs_u.hcone,
                                                                      hs_u.htmk, hs_u.hwk⟩,
                                                                    hs_u.hsav_le, hs_u.hscr,
                                                                    hs_u.hws⟩,
                                                                   hlts_u',
                                                                   by simpa only [hk1] using
                                                                     hcov_u',
                                                                   by simpa only [hk1] using
                                                                     hvars_u',
                                                                   hnd_u'⟩, hm_u'⟩)
                                                              (fun _ hJ_u => by
                                                                have htm_k :=
                                                                  hs_k.hlen.2.tarjan_mark_len
                                                                have hwk_k_len :=
                                                                  hs_k.hlen.scratch_ok.work_stk1_len
                                                                m6_split
                                                                · have hmiss :
                                                                      st_k.scratch.tarjan_mark[
                                                                        (lit_k >>>
                                                                          (1 : Nat)).toNat]?.getD
                                                                        0#32 = 0#32 := by
                                                                    rw [m6_getElem_eq_getD
                                                                        st_k.scratch.tarjan_mark
                                                                        (d := 0#32),
                                                                      m6_getElem_eq_getD
                                                                        st_k.core.arena (d := 0#32),
                                                                      hcr_idx _ hp_mod, har_hc_idx,
                                                                      hae_k, hlit_ar, ← hlv_eq]
                                                                      at hc
                                                                    exact hc
                                                                  m6_split
                                                                  · m6_steps
                                                                    exact hJ_occ (nv_k, true, true,
                                                                      cnt, idx, ()) mk
                                                                      ⟨st_k,
                                                                       hs_k.toFidConeSavedBase,
                                                                       (fun h => by cases h), hmk⟩
                                                                  · have hnv_k_max :
                                                                        nv_k.toNat <
                                                                          mv_c.toNat := by
                                                                      have :
                                                                          ¬ mv_c.toNat ≤
                                                                            nv_k.toNat := hc
                                                                      omega
                                                                    have hqi_nv_k :
                                                                        qi_l.toNat < nv_k.toNat :=
                                                                      Nat.lt_of_lt_of_le
                                                                        (hsav_eq ▸
                                                                          Nat.lt_of_lt_of_le
                                                                            hqi_l_lt hnv_w_mono)
                                                                        hs_k.hsav_le
                                                                    rcases fid_cone_push_var_base_ok
                                                                        hs_k.toFidConeSavedBase
                                                                        hnv_k_max hlv_lt hmiss
                                                                        hqi_nv_k with
                                                                      ⟨hnv_k_lt, hnv1, hne_nv_qi,
                                                                        hne_cv, hs_u, htlvu⟩
                                                                    have hnv_ws :
                                                                        (BitVec.setWidth 64
                                                                          ((nv_k + 1#32) -
                                                                            1#32)).toNat <
                                                                          List.length
                                                                            st_k.scratch.work_stk1
                                                                          := by
                                                                      rw [hwk_k_len,
                                                                        bv_c0_zext32_64,
                                                                        m6_bv32_add1_sub1_eq nv_k]
                                                                      omega
                                                                    have hnv_ws0 : (BitVec.setWidth
                                                                        64 nv_k).toNat <
                                                                        List.length
                                                                          st_k.scratch.work_stk1
                                                                        := by
                                                                      rw [hwk_k_len,
                                                                        bv_c0_zext32_64]; omega
                                                                    have hnv_ws1 : nv_k.toNat <
                                                                        List.length
                                                                          st_k.scratch.work_stk1
                                                                        := by
                                                                      rw [hwk_k_len]; omega
                                                                    m6_steps
                                                                    let st_u : FullState :=
                                                                      { st_k with scratch :=
                                                                        { st_k.scratch with
                                                                          tarjan_mark := List.set
                                                                            st_k.scratch.tarjan_mark
                                                                            (lit_k >>>
                                                                              (1 : Nat)).toNat
                                                                            (nv_k + 1#32)
                                                                          work_stk1 := List.set
                                                                            st_k.scratch.work_stk1
                                                                            nv_k.toNat (lit_k >>>
                                                                              (1 : Nat)) } }
                                                                    have h2 :=
                                                                      m6_bv32_add1_sub1_toNat nv_k
                                                                    have htm_idx :
                                                                        (BitVec.setWidth 64
                                                                          (lit_k >>> (OfNat.ofNat 1
                                                                            : Nat))).toNat =
                                                                          (lit_k >>> (1 :
                                                                            Nat)).toNat :=
                                                                      bv_c0_zext32_64 _
                                                                    have hm_u :
                                                                        (FullMem c st_u ⋆ R) m := by
                                                                      have hm' := hm
                                                                      dsimp only [LeanQbe.T.lift2,
                                                                        Arg.val_var, Arg.val_imm,
                                                                        Prod.fst] at hm'
                                                                      rw [h_ar_lk_w1, htm_idx,
                                                                        bv_c0_zext32_64] at hm'
                                                                      try rw [h2] at hm'
                                                                      exact (congrArg (fun stx =>
                                                                        (FullMem c stx ⋆ R) m)
                                                                        rfl).mp hm'
                                                                    exact hJ_u (nv_k + 1#32, lim_w,
                                                                      false, ()) m
                                                                      ⟨rfl, rfl,
                                                                       by rw [hnv1]; exact
                                                                         Nat.le_succ _,
                                                                       st_u, hs_u, rfl,
                                                                       fun j _ => by
                                                                         dsimp only [st_u]
                                                                         exact List.getElem?_set_ne
                                                                           (by omega),
                                                                       htlvu, hm_u⟩
                                                                · have hne_ov :
                                                                      st_k.scratch.tarjan_mark[
                                                                        (lit_k >>>
                                                                          (1 : Nat)).toNat]?.getD
                                                                        0#32 ≠ 0#32 := by
                                                                    rw [m6_getElem_eq_getD
                                                                        st_k.scratch.tarjan_mark
                                                                        (d := 0#32),
                                                                      m6_getElem_eq_getD
                                                                        st_k.core.arena (d := 0#32),
                                                                      hcr_idx _ hp_mod, har_hc_idx,
                                                                      hae_k, hlit_ar, ← hlv_eq]
                                                                      at hc
                                                                    exact hc
                                                                  m6_steps
                                                                  exact hJ_u (nv_k, lim_w, false,
                                                                    ()) mk
                                                                    ⟨rfl, rfl, le_refl _, st_k,
                                                                     hs_k.toFidConeSavedBase, rfl,
                                                                     fun _ _ => rfl, hne_ov, hmk⟩))
                                                          (fun _ hJcont => by
                                                            m6_split
                                                            · m6_split
                                                              · m6_steps
                                                                exact hJ_occ (nv_k, lim_w, true,
                                                                  cnt, idx, ()) mk
                                                                  ⟨st_k, hs_k.toFidConeSavedBase,
                                                                   (fun h => by cases h), hmk⟩
                                                              · m6_steps; exact hJcont () mk rfl
                                                            · m6_steps; exact hJcont () mk rfl))
                                                      (fun _ hJdup => by
                                                        m6_split
                                                        · m6_split
                                                          · m6_steps
                                                            exact hJ_occ (nv_k, lim_w, true, cnt,
                                                              idx, ()) mk
                                                              ⟨st_k, hs_k.toFidConeSavedBase,
                                                               (fun h => by cases h), hmk⟩
                                                          · m6_steps; exact hJdup () mk rfl
                                                        · m6_steps; exact hJdup () mk rfl)
                                                  · have hne0 : s.core.vals[lit_k.toNat]?.getD
                                                        0#8 ≠ 0#8 := fun h0 => by
                                                      rw [m6_getElem_eq_getD st_k.core.vals
                                                          (d := 0#8),
                                                        m6_getElem_eq_getD st_k.core.arena
                                                          (d := 0#32),
                                                        hcr_idx _ hp_mod, har_hc_idx, hae_k,
                                                        hlit_ar, hve_k, h0] at hc
                                                      exact absurd (by decide) hc
                                                    have hfals_k : s.core.vals[lit_k.toNat]?.getD
                                                        0#8 = 0xFF#8 :=
                                                      (hw.vals_domain lit_k.toNat hl_lt_s).elim
                                                        (absurd · hne0)
                                                        (·.elim (absurd · hnot_pos) id)
                                                    m6_steps
                                                    refine hJ_lv (nv_k, lim_w, false, cnt, ()) mk
                                                      ⟨rfl, rfl, le_refl _, by omega,
                                                       st_k, ⟨hs_k.toFidConeSavedBase, hs_k.hlts,
                                                        fun i hi => ?_, fun j hj => ?_, hs_k.hnd⟩,
                                                       hmk⟩
                                                    · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with
                                                        hlt | rfl
                                                      · exact hs_k.hcov i hlt
                                                      · left; rwa [hlit_ar]
                                                    · obtain ⟨p, hp, hpeq⟩ := hs_k.hvars j hj
                                                      exact ⟨p, Nat.lt_succ_of_lt hp, hpeq⟩)))))))
                    (fun _ hJ_bp => by
                      clear hJ_out hJ_in hcur_tmk hcv_idx hdw hroot htmk hm_shl1 hqnext_c0
                        hmv_c0 hmv_bounds hmv64_lt hdep1 hdep_lt hlim_f hqi_lt hqi_le hdep_le
                        hdep_lim_hi hmo_nat
                      m6_split; rotate_left
                      · m6_steps; exact hJ_bp () mp ⟨hle_nv_p, st_p, hb_p, hmp⟩
                      have hpol_lt : pol.toNat < 2 := hc
                      m6_split
                      · m6_steps; exact hJ_bp () mp ⟨hle_nv_p, st_p, hb_p, hmp⟩
                      m6_split; rotate_left
                      · m6_steps; exact hJ_bp () mp ⟨hle_nv_p, st_p, hb_p, hmp⟩
                      have hncp_lt : nc_p.toNat < L.maxOrig :=
                        Nat.lt_of_lt_of_le hc hmc_c_le
                      obtain ⟨lit, hlit_def⟩ : ∃ lit : BitVec 32,
                          lit = ((cv <<< (1 : Nat)) ||| pol) := ⟨_, rfl⟩
                      have hlit_eq : lit.toNat = 2 * cv.toNat + pol.toNat := by
                        rw [hlit_def]; exact m6_bv32_shl1_or_pol cv pol (by omega) hpol_lt
                      have hlit_lt : lit.toNat < 2 * s.core.cur_vars := by omega
                      obtain ⟨hwo, hwsz, hend_eq, hwo_le, hrem_eq, hend_ws, h2l_mod, h2l1_mod⟩ :=
                        fid_cone_wvec_facts hlen hb_p.hlen hb_p.hag hdwatches hlit_lt
                      have hwvec_p := hb_p.hlen.core_ok.wvec_len
                      have h2l_bd : (BitVec.setWidth 64 lit <<< (1 : Nat)).toNat <
                          st_p.core.wvec.length := by
                        rw [hwvec_p, m6_bv64_shl1]; omega
                      have h2l1_bd : ((BitVec.setWidth 64 lit <<< (1 : Nat)) + 1#64).toNat <
                          st_p.core.wvec.length := by
                        rw [hwvec_p, m6_bv64_shl1_add1]; omega
                      obtain ⟨wOff, hwOff_def⟩ : ∃ wOff : BitVec 64,
                          wOff = (st_p.core.wvec[(BitVec.setWidth 64 lit <<< (1 : Nat)).toNat]'
                            h2l_bd).setWidth 64 := ⟨_, rfl⟩
                      obtain ⟨wSz, hwSz_def⟩ : ∃ wSz : BitVec 64,
                          wSz = (st_p.core.wvec[((BitVec.setWidth 64 lit <<< (1 : Nat)) +
                            1#64).toNat]'h2l1_bd).setWidth 64 := ⟨_, rfl⟩
                      obtain ⟨wEnd, hwEnd⟩ : ∃ wEnd : BitVec 64, wEnd = wOff + wSz := ⟨_, rfl⟩
                      have hend_ws : wEnd.toNat ≤ s.core.wstk.length := by
                        rw [hwEnd, hwOff_def, hwSz_def]; exact hend_ws
                      have hend_n : wEnd.toNat =
                          fullWatchOffCore s.core lit.toNat +
                            fullWatchSizeCore s.core lit.toNat := by
                        rw [hwEnd, hwOff_def, hwSz_def]; exact hend_eq
                      have hpol1 : (pol + 1#32).toNat = pol.toNat + 1 :=
                        m6_bv32_add1 (Nat.lt_trans hpol_lt (by decide))
                      have hwv0_eq :
                          ∀ (h : (2 * lit.toNat) % 2 ^ 64 < st_p.core.wvec.length),
                          st_p.core.wvec[(2 * lit.toNat) % 2 ^ 64]'h =
                            st_p.core.wvec[(BitVec.setWidth 64 lit <<< (1 : Nat)).toNat]'h2l_bd :=
                        fun h => m6_list_getElem_congr h2l_mod h _
                      have hwv1_eq :
                          ∀ (h : (2 * lit.toNat + (1#64).toNat) % 2 ^ 64 <
                              st_p.core.wvec.length),
                            st_p.core.wvec[(2 * lit.toNat + (1#64).toNat) % 2 ^ 64]'h =
                              st_p.core.wvec[((BitVec.setWidth 64 lit <<< (1 : Nat)) +
                                1#64).toNat]'h2l1_bd := fun h =>
                        m6_list_getElem_congr
                          (by rw [show (1#64).toNat = 1 from rfl]; exact h2l1_mod) h _
                      have h2l_bd_ws :
                          (BitVec.setWidth 64 ((st_l.scratch.work_stk1[
                            (BitVec.setWidth 64 qi_l).toNat]'hqi_ws <<< (1 : Nat)) ||| pol) <<<
                            (1 : Nat)).toNat < st_p.core.wvec.length := by
                        rw [← hcv_def, ← hlit_def]; exact h2l_bd
                      have h2l1_bd_ws :
                          ((BitVec.setWidth 64 ((st_l.scratch.work_stk1[
                            (BitVec.setWidth 64 qi_l).toNat]'hqi_ws <<< (1 : Nat)) ||| pol) <<<
                            (1 : Nat)) + 1#64).toNat < st_p.core.wvec.length := by
                        rw [← hcv_def, ← hlit_def]; exact h2l1_bd
                      have hw0_ws :
                          ∀ (h : (BitVec.setWidth 64 ((st_l.scratch.work_stk1[
                              (BitVec.setWidth 64 qi_l).toNat]'hqi_ws <<< (1 : Nat)) ||| pol) <<<
                              (1 : Nat)).toNat < st_p.core.wvec.length),
                            (st_p.core.wvec[(BitVec.setWidth 64 ((st_l.scratch.work_stk1[
                              (BitVec.setWidth 64 qi_l).toNat]'hqi_ws <<< (1 : Nat)) ||| pol) <<<
                              (1 : Nat)).toNat]'h).setWidth 64 = wOff := fun h => by
                        rw [hwOff_def]; congr 1
                        exact m6_list_getElem_congr (by rw [← hcv_def, ← hlit_def]) h h2l_bd
                      have hw1_ws :
                          ∀ (h : ((BitVec.setWidth 64 ((st_l.scratch.work_stk1[
                              (BitVec.setWidth 64 qi_l).toNat]'hqi_ws <<< (1 : Nat)) ||| pol) <<<
                              (1 : Nat)) + 1#64).toNat < st_p.core.wvec.length),
                            (st_p.core.wvec[((BitVec.setWidth 64 ((st_l.scratch.work_stk1[
                              (BitVec.setWidth 64 qi_l).toNat]'hqi_ws <<< (1 : Nat)) ||| pol) <<<
                              (1 : Nat)) + 1#64).toNat]'h).setWidth 64 = wSz := fun h => by
                        rw [hwSz_def]; congr 1
                        exact m6_list_getElem_congr (by rw [← hcv_def, ← hlit_def]) h h2l1_bd
                      have hw0_eq_nat : ∀ (h : (BitVec.setWidth 64 lit <<< (1 : Nat)).toNat <
                            st_p.core.wvec.length),
                          (st_p.core.wvec[(BitVec.setWidth 64 lit <<< (1 : Nat)).toNat]'h).toNat =
                            wOff.toNat := fun h => by rw [hwOff_def, bv_c0_zext32_64]
                      have hw1_eq_nat : ∀ (h : ((BitVec.setWidth 64 lit <<< (1 : Nat)) +
                            1#64).toNat < st_p.core.wvec.length),
                          (st_p.core.wvec[((BitVec.setWidth 64 lit <<< (1 : Nat)) +
                            1#64).toNat]'h).toNat = wSz.toNat := fun h => by
                        rw [hwSz_def, bv_c0_zext32_64]
                      m6_to_group
                      refine wp_join_group (ts := [i32, i32, .bool, i64])
                        (fun (nv_e, nc_e, _lim_e, _, ()) m_we =>
                          layer_end.toNat ≤ nv_e.toNat ∧ ∃ st_we : FullState,
                            FidConeBase F_cur L mv_c c s cv qi_l nv_e.toNat nc_e.toNat st_we ∧
                            (FullMem c st_we ⋆ R) m_we)
                        (fun _ (nv_e, nc_e, lim_e, _, ()) m_we ⟨hnve, st_we, hb_e, hm_e⟩ => by
                          m6_steps
                          exact hJ_bpol (nv_e, nc_e, lim_e, pol + 1#32, ()) m_we
                            (by dsimp only; rw [hpol1]; exact m6_nat_sub1_lt hpol_lt rfl)
                            ⟨by rw [hpol1]; exact hpol_lt, hnve, st_we, hb_e, hm_e⟩)
                        (fun _ hJ_we => by
                          m6_to_group
                          refine wp_loop_inv (ts := [i32, i32, .bool, i64])
                            (fun (nv_w, nc_w, _lim_w, p, ()) mw =>
                              p.toNat ≤ wEnd.toNat ∧ layer_end.toNat ≤ nv_w.toNat ∧
                              DenseWatchSliceOk F_cur s.core lit.toNat p.toNat
                                (wEnd.toNat - p.toNat) ∧
                              ∃ st_w : FullState,
                                FidConeBase F_cur L mv_c c s cv qi_l nv_w.toNat nc_w.toNat st_w ∧
                                (FullMem c st_w ⋆ R) mw)
                            (fun (_, _, _, p, ()) _ => wEnd.toNat - p.toNat)
                            (fun _ hJ_w => by
                              m6_steps
                              refine hJ_w (nv_p, nc_p, lim_p, _, ()) mp
                                ⟨?_, hle_nv_p, ?_, st_p, hb_p, hmp⟩
                              · try rw [hw0_ws]
                                rw [hwEnd, hwOff_def, hwSz_def]; exact hwo_le
                              · try rw [hw0_ws]
                                rw [hwEnd, hwOff_def, hwSz_def, hrem_eq, hwo]
                                exact hdwatches.slices lit.toNat hlit_lt)
                            (fun J_w (nv_w, nc_w, lim_w, p, ()) mw
                                ⟨hp_le, hnv_w_mono, hslice, st_w, hb_w, hmw⟩ hJ_w => by
                              clear hJ_bpol hmp hpol1 hle_nv_l hlen_l hag_l hcone_l
                                hqi1 hnc_lt hncp_lt hpol_le hcv_lt_s hwo_le hrem_eq
                              m6_split; rotate_left
                              · m6_steps; exact hJ_we (nv_w, nc_w, lim_w, p, ()) mw
                                  ⟨hnv_w_mono, st_w, hb_w, hmw⟩
                              have hp_lt : p.toNat < wEnd.toNat := by
                                simp only [hcv_qi0] at hc
                                repeat rw [m6_getElem_eq_getD st_p.core.wvec (d := 0#32)] at hc
                                rw [fid_hag_wvec hb_p.hag] at hc
                                change p.toNat <
                                  ((s.core.wvec[2 * (cv <<< (1 : Nat) ||| pol).toNat %
                                      2 ^ 64]?.getD 0#32).toNat +
                                    (s.core.wvec[(2 * (cv <<< (1 : Nat) ||| pol).toNat +
                                        1) % 2 ^ 64]?.getD 0#32).toNat) % 2 ^ 64 at hc
                                rw [← hlit_def,
                                  show 2 * lit.toNat % 2 ^ 64 = 2 * lit.toNat from
                                    Nat.mod_eq_of_lt (by omega),
                                  show (2 * lit.toNat + 1) % 2 ^ 64 = 2 * lit.toNat + 1 from
                                    Nat.mod_eq_of_lt (by omega)] at hc
                                change p.toNat <
                                  (fullWatchOffCore s.core lit.toNat +
                                    fullWatchSizeCore s.core lit.toNat) % 2 ^ 64 at hc
                                have hw_lt : wEnd.toNat < 2 ^ 64 := wEnd.isLt
                                rw [← hend_n, Nat.mod_eq_of_lt (by omega)] at hc
                                exact hc
                              m6_split
                              · m6_steps; exact hJ_we (nv_w, nc_w, lim_w, p, ()) mw
                                  ⟨hnv_w_mono, st_w, hb_w, hmw⟩
                              m6_split; rotate_left
                              · m6_steps; exact hJ_we (nv_w, nc_w, lim_w, p, ()) mw
                                  ⟨hnv_w_mono, st_w, hb_w, hmw⟩
                              have hncw_lt : nc_w.toNat < L.maxOrig :=
                                Nat.lt_of_lt_of_le hc hmc_c_le
                              have hwstk_eq : st_w.core.wstk = s.core.wstk :=
                                fid_hag_wstk hb_w.hag
                              have hcv_w : st_w.core.cur_vars = s.core.cur_vars :=
                                fid_hag_cur_vars hb_w.hag
                              have hp_wstk_w : p.toNat < st_w.core.wstk.length :=
                                fid_cone_hp_wstk hwstk_eq hp_lt hend_ws
                              have hp1 : (p + 1#64).toNat = p.toNat + 1 := m6_bv64_add1 (by omega)
                              obtain ⟨w0, hw0_def⟩ : ∃ w0 : BitVec 32,
                                  w0 = st_w.core.wstk[p.toNat]'hp_wstk_w := ⟨_, rfl⟩
                              have hw0_s : s.core.wstk[p.toNat]? = some w0 := by
                                rw [hw0_def, List.getElem?_eq_getElem (hwstk_eq ▸ hp_wstk_w)]
                                exact congrArg some (by simp [hwstk_eq])
                              m6_split
                              · have hocc : (w0 &&& 0x80000000#32) = 0#32 := by
                                  rw [hw0_def]; exact hc
                                obtain ⟨_, _, _, _, _, _, hslice1⟩ :=
                                  m6_denseSlice_step_occ hslice (Nat.sub_pos_of_lt hp_lt) hw0_s
                                    hocc
                                have hp2 : (p + 1#64 + 1#64).toNat = p.toNat + 2 := by
                                  rw [m6_bv64_add1 (by rw [hp1]; omega), hp1]
                                have hp2_le : (p + 1#64 + 1#64).toNat ≤ wEnd.toNat := by
                                  rw [hp2]; omega
                                m6_steps
                                exact hJ_w (nv_w, nc_w, lim_w, p + 1#64 + 1#64, ()) mw
                                  (by dsimp only; exact m6_nat_sub2_lt hp_lt hp2_le hp2)
                                  ⟨hp2_le, hnv_w_mono,
                                    by rw [hp2, fid_cone_sub_sub_eq]; exact hslice1,
                                    st_w, hb_w, hmw⟩
                              · have hbin : (w0 &&& 0x80000000#32) ≠ 0#32 := by
                                  rw [hw0_def]; exact hc
                                obtain ⟨_, hot_lt, hent_bin, hslice1⟩ :=
                                  m6_denseSlice_step_bin hslice (Nat.sub_pos_of_lt hp_lt) hw0_s
                                    hbin
                                obtain ⟨ot, hot_def⟩ : ∃ ot : BitVec 32,
                                    ot = (w0 &&& 0x7FFFFFFF#32) := ⟨_, rfl⟩
                                have hot_lt' : ot.toNat < 2 * s.core.cur_vars :=
                                  hot_def ▸ hot_lt
                                obtain ⟨ov, hov_def⟩ : ∃ ov : BitVec 32,
                                    ov = (ot >>> (1 : Nat)) := ⟨_, rfl⟩
                                have hov_eq : ov.toNat = ot.toNat / 2 := by
                                  rw [hov_def]; exact m6_bv32_shr1_toNat ot
                                have hov_lt : ov.toNat < s.core.cur_vars := by omega
                                have hvals_w := hb_w.hlen.core_ok.vals_len
                                have hfl_w := hb_w.hlen.core_ok.flags_len
                                have htm_w := hb_w.hlen.scratch_ok.tarjan_mark_len
                                have hwk_w_len := hb_w.hlen.scratch_ok.work_stk1_len
                                have hcv_w' := fid_hag_cur_vars hb_w.hag
                                have hov_fl : (BitVec.setWidth 64 ov).toNat <
                                    st_w.core.flags.length := by
                                  rw [hfl_w, bv_c0_zext32_64]; omega
                                have hov_fl_p : (BitVec.setWidth 64
                                    ((st_w.core.wstk[p.toNat]'hp_wstk_w &&&
                                      (2147483647 : BitVec 32)) >>> (1 : Nat))).toNat <
                                    st_w.core.flags.length := by
                                  rw [← hw0_def,
                                    show (2147483647 : BitVec 32) = 0x7FFFFFFF#32 from rfl,
                                    ← hot_def, ← hov_def]
                                  exact hov_fl
                                have hot_vals : (BitVec.setWidth 64 ot).toNat <
                                    st_w.core.vals.length := by
                                  rw [hvals_w, bv_c0_zext32_64]; omega
                                have hot_vals_p : (BitVec.setWidth 64
                                    (st_w.core.wstk[p.toNat]'hp_wstk_w &&&
                                      (2147483647 : BitVec 32))).toNat < st_w.core.vals.length := by
                                  rw [← hw0_def,
                                    show (2147483647 : BitVec 32) = 0x7FFFFFFF#32 from rfl,
                                    ← hot_def]
                                  exact hot_vals
                                have hstep_bin : ∀ nv_b nc_b lim_b st_b m_b,
                                    layer_end.toNat ≤ BitVec.toNat nv_b →
                                    FidConeBase F_cur L mv_c c s cv qi_l nv_b.toNat
                                      nc_b.toNat st_b →
                                    (FullMem c st_b ⋆ R) m_b →
                                    J_w (nv_b, nc_b, lim_b, p + 1#64, ()) m_b :=
                                  fun nv_b nc_b lim_b st_b m_b hnvb hbb hmb =>
                                    hJ_w (nv_b, nc_b, lim_b, p + 1#64, ()) m_b
                                      (by dsimp only; rw [hp1]; exact m6_nat_sub1_lt hp_lt rfl)
                                      ⟨by rw [hp1]; exact hp_lt, hnvb,
                                        by rw [hp1, fid_cone_sub_sub_eq]; exact hslice1,
                                        st_b, hbb, hmb⟩
                                -- `if ((u64)ov >= h->cur_vars || (fl[ov] & FL_ACTIVE) == 0u)`
                                m6_split
                                · exfalso
                                  have hge_cv : st_w.core.cur_vars ≤ ov.toNat := by
                                    rw [← hov_def, ← hot_def, ← hw0_def] at *; bv_omega
                                  omega
                                m6_split
                                · m6_steps
                                  exact hstep_bin nv_w nc_w lim_w st_w mw hnv_w_mono hb_w hmw
                                -- `if (ovv > 0) continue`
                                m6_split
                                · m6_steps
                                  exact hstep_bin nv_w nc_w lim_w st_w mw hnv_w_mono hb_w hmw
                                have hnot_pos : s.core.vals[ot.toNat]?.getD 0#8 ≠ 1#8 :=
                                  fun h1 => by
                                    have h1' : s.core.vals[(st_w.core.wstk[p.toNat]'hp_wstk_w &&&
                                        (2147483647 : BitVec 32)).toNat]?.getD 0#8 = 1#8 := by
                                      rw [← hw0_def,
                                        show (2147483647 : BitVec 32) = 0x7FFFFFFF#32 from rfl,
                                        ← hot_def]
                                      exact h1
                                    rw [m6_getElem_eq_getD st_w.core.vals (d := 0#8),
                                      fid_hag_vals hb_w.hag, h1'] at hc
                                    exact absurd hc (by decide)
                                -- `if (ov == cv)`
                                m6_split
                                · m6_to_group
                                  refine wp_join_group (ts := [i32, .bool])
                                    (fun (nc_b, _lim_b, ()) m_b => ∃ st_b : FullState,
                                      FidConeBase F_cur L mv_c c s cv qi_l nv_w.toNat
                                        nc_b.toNat st_b ∧
                                      (FullMem c st_b ⋆ R) m_b)
                                    (fun _ (nc_b, lim_b, ()) m_b ⟨st_b, hbb, hmb⟩ => by
                                      m6_steps
                                      exact hstep_bin nv_w nc_b lim_b st_b m_b hnv_w_mono hbb hmb)
                                    (fun _ hJ_ov => by
                                      m6_split; rotate_left
                                      · m6_steps; exact hJ_ov (nc_w, lim_w, ()) mw ⟨st_w, hb_w, hmw⟩
                                      have hot_eq_lit : ot = lit := by
                                        rw [hot_def, hw0_def]
                                        simp only [hcv_qi0] at hc
                                        change (st_w.core.wstk[p.toNat]'hp_wstk_w &&&
                                          0x7FFFFFFF#32) = (cv <<< (1 : Nat) ||| pol) at hc
                                        rw [← hlit_def] at hc
                                        exact hc
                                      have hnv_w_max := hb_w.hcone.nv_leMax
                                      have htmp_w0 : 0 < st_w.core.tmp.length := by
                                        rw [hb_w.hlen.core_ok.tmp_len_arr]; omega
                                      have hent_self : (cnfOfClauses F_cur).EntailsClause
                                          (cnfClause [lit.toNat]) := by
                                        apply m6_entails_singleton_of_dup
                                        simpa only [← hot_def, ← hot_eq_lit] using hent_bin
                                      have hmap_lp : ((qi_l <<< (1 : Nat)) ||| pol).toNat =
                                          2 * qi_l.toNat + pol.toNat :=
                                        m6_bv32_shl1_or_pol qi_l pol (by omega) hpol_lt
                                      obtain ⟨hl_st, hlts_u, hent_u⟩ :=
                                        m6_cone_unit_tmp_prep (nv := nv_w) (qi0 := qi_l)
                                          (pol := pol) (u := (qi_l <<< (1 : Nat)) ||| pol) hb_w.hlen
                                          htmp_w0 (by omega) (by omega) hpol_lt (by omega)
                                          hmap_lp
                                          (by rw [hb_w.hwk, ← hlit_eq]) hent_self
                                      m6_to_group
                                      try refine wp_unroll_group fun _ _ => ?_
                                      m6_steps
                                      have hcv_q' :
                                          st_l.scratch.work_stk1[(BitVec.setWidth 64 qi_l).toNat]'
                                            hqi_ws = cv := hcv_def.symm
                                      have hm_tmk0 :
                                          st_l.scratch.tarjan_mark[(BitVec.setWidth 64
                                            (st_l.scratch.work_stk1[(BitVec.setWidth 64
                                              qi_l).toNat]'hqi_ws)).toNat]'(by
                                                rw [hcv_q']; exact hcv_tmk) - 1#32 = qi_l := by
                                        rw [m6_list_getElem_congr
                                          (congrArg (fun x => (BitVec.setWidth 64 x).toNat) hcv_q')
                                          _ hcv_tmk, hmap_c]
                                      refine fid_cone_call_add_clause hAddCl (aSz := Arg.imm 1)
                                        (sz := 1#32) rfl hL_len hL_mv hl_st
                                        (fidConeMask_upd_tmp _ hb_w.hag)
                                        (fidConeInv_tmp_irrel hb_w.hcone) hncw_lt (by decide)
                                        (by
                                          rw [hl_st.core_ok.tmp_len_arr,
                                            ← hb_w.hlen.core_ok.tmp_len_arr]
                                          exact htmp_w0)
                                        hlts_u hent_u
                                        (m6_fullMem_tmp0_congr
                                          (congrArg (fun x : BitVec 32 =>
                                            (x <<< (1 : Nat)) ||| pol) hm_tmk0)
                                          hm)
                                        (fun ok st' m' hl' ha' hc' _ ht' hw' hm' => by
                                          m6_split
                                          · have hic := (fid_cone_load_kptr_hdr hc' hm').1
                                            m6_to_group
                                            refine wp_join_group (ts := [.bool])
                                              (fun (_lim', ()) m'' => m'' = m')
                                              (fun _ (lim', ()) m'' hm'' => by
                                                subst m''
                                                m6_steps
                                                exact hJ_ov (nc_w + 1#32, lim', ()) m'
                                                  ⟨st', ⟨hl', ha', by simpa only [hc, ↓reduceIte]
                                                    using hc', ht' ▸ hb_w.htmk, hw' ▸ hb_w.hwk⟩,
                                                   hm'⟩)
                                              (fun _ hJ_inc => by
                                                change wp _ _ _ _ _; c0_hsteps
                                                dsimp only [Prod.fst]
                                                try (first | rw [hkptr_c0] | rw [hkptr_c0_nat])
                                                try rw [show (BitVec.ofNat (OfNat.ofNat 64)
                                                    (OfNat.ofNat 6) : BitVec 64) = 6#64 from rfl]
                                                refine head_wp_load rfl hic ?_
                                                m6_split
                                                · m6_steps; exact hJ_inc (true, ()) m' rfl
                                                · m6_steps; exact hJ_inc (lim_w, ()) m' rfl)
                                          · m6_steps
                                            exact hJ_ov (nc_w, true, ()) m'
                                              ⟨st', ⟨hl', ha', by simpa only [hc,
                                                Bool.false_eq_true,
                                                ↓reduceIte] using hc', ht' ▸ hb_w.htmk,
                                                hw' ▸ hb_w.hwk⟩, hm'⟩))
                                -- `if (ovv < 0)`
                                have hov_ne_cv : ov ≠ cv := by
                                  rw [hov_def, hot_def, hw0_def]
                                  simp only [hcv_qi0] at hc
                                  change ¬((st_w.core.wstk[p.toNat]'hp_wstk_w &&&
                                    0x7FFFFFFF#32) >>> (1 : Nat) = cv) at hc
                                  exact hc
                                m6_split
                                · have htmp_w0 : 0 < st_w.core.tmp.length := by
                                    rw [hb_w.hlen.core_ok.tmp_len_arr]; omega
                                  m6_to_group
                                  refine wp_join_group (ts := [i32, .bool])
                                    (fun (nc_b, _lim_b, ()) m_b => ∃ st_b : FullState,
                                      FidConeBase F_cur L mv_c c s cv qi_l nv_w.toNat
                                        nc_b.toNat st_b ∧
                                      (FullMem c st_b ⋆ R) m_b)
                                    (fun _ (nc_b, lim_b, ()) m_b ⟨st_b, hbb, hmb⟩ => by
                                      m6_steps
                                      exact hstep_bin nv_w nc_b lim_b st_b m_b hnv_w_mono hbb hmb)
                                    (fun _ hJ_ov => by
                                      have hne0 : s.core.vals[ot.toNat]?.getD 0#8 ≠ 0#8 :=
                                        fun h0 => by
                                          have h0' : s.core.vals[(st_w.core.wstk[p.toNat]'hp_wstk_w
                                              &&& (2147483647 : BitVec 32)).toNat]?.getD 0#8 =
                                              0#8 := by
                                            rw [← hw0_def,
                                              show (2147483647 : BitVec 32) = 0x7FFFFFFF#32 from
                                                rfl, ← hot_def]
                                            exact h0
                                          rw [m6_getElem_eq_getD st_w.core.vals (d := 0#8),
                                            fid_hag_vals hb_w.hag, h0'] at hc
                                          exact absurd hc (by decide)
                                      have hfals_ot : s.core.vals[ot.toNat]?.getD 0#8 = 0xFF#8 :=
                                        (hw.vals_domain ot.toNat hot_lt').elim
                                          (absurd · hne0) (·.elim (absurd · hnot_pos) id)
                                      have hnv_w_max := hb_w.hcone.nv_leMax
                                      have hent_unit : (cnfOfClauses F_cur).EntailsClause
                                          (cnfClause [lit.toNat]) :=
                                        m6_entails_fst_of_snd_false hw hcl0 hot_lt' hfals_ot
                                          (hot_def ▸ hent_bin)
                                      have hmap_lp : ((qi_l <<< (1 : Nat)) ||| pol).toNat =
                                          2 * qi_l.toNat + pol.toNat :=
                                        m6_bv32_shl1_or_pol qi_l pol (by omega) hpol_lt
                                      obtain ⟨hl_st, hlts_u, hent_u⟩ :=
                                        m6_cone_unit_tmp_prep (nv := nv_w) (qi0 := qi_l)
                                          (pol := pol) (u := (qi_l <<< (1 : Nat)) ||| pol) hb_w.hlen
                                          htmp_w0 (by omega) (by omega) hpol_lt (by omega) hmap_lp
                                          (by rw [hb_w.hwk]; exact hlit_eq.symm) hent_unit
                                      m6_steps
                                      have hcv_q' :
                                          st_l.scratch.work_stk1[(BitVec.setWidth 64 qi_l).toNat]'
                                            hqi_ws = cv := hcv_def.symm
                                      have hm_tmk0 :
                                          st_l.scratch.tarjan_mark[(BitVec.setWidth 64
                                            (st_l.scratch.work_stk1[(BitVec.setWidth 64
                                              qi_l).toNat]'hqi_ws)).toNat]'(by
                                                rw [hcv_q']; exact hcv_tmk) - 1#32 = qi_l := by
                                        rw [m6_list_getElem_congr
                                          (congrArg (fun x => (BitVec.setWidth 64 x).toNat) hcv_q')
                                          _ hcv_tmk, hmap_c]
                                      refine fid_cone_call_add_clause hAddCl (aSz := Arg.imm 1)
                                        (sz := 1#32) rfl hL_len hL_mv hl_st
                                        (fidConeMask_upd_tmp _ hb_w.hag)
                                        (fidConeInv_tmp_irrel hb_w.hcone) hncw_lt (by decide)
                                        (by
                                          rw [hl_st.core_ok.tmp_len_arr,
                                            ← hb_w.hlen.core_ok.tmp_len_arr]
                                          exact htmp_w0)
                                        hlts_u hent_u
                                        (m6_fullMem_tmp0_congr
                                          (congrArg (fun x : BitVec 32 =>
                                            (x <<< (1 : Nat)) ||| pol) hm_tmk0) hm)
                                        (fun ok st' m' hl' ha' hc' _ ht' hw' hm' => by
                                          m6_split
                                          · have hic := (fid_cone_load_kptr_hdr hc' hm').1
                                            m6_to_group
                                            refine wp_join_group (ts := [.bool])
                                              (fun (_lim', ()) m'' => m'' = m')
                                              (fun _ (lim', ()) m'' hm'' => by
                                                subst m''
                                                m6_steps
                                                exact hJ_ov (nc_w + 1#32, lim', ()) m'
                                                  ⟨st', ⟨hl', ha', by simpa only [hc, ↓reduceIte]
                                                    using hc', ht' ▸ hb_w.htmk, hw' ▸ hb_w.hwk⟩,
                                                   hm'⟩)
                                              (fun _ hJ_inc => by
                                                change wp _ _ _ _ _; c0_hsteps
                                                dsimp only [Prod.fst]
                                                try (first | rw [hkptr_c0] | rw [hkptr_c0_nat])
                                                try rw [show (BitVec.ofNat (OfNat.ofNat 64)
                                                    (OfNat.ofNat 6) : BitVec 64) = 6#64 from rfl]
                                                refine head_wp_load rfl hic ?_
                                                m6_split
                                                · m6_steps; exact hJ_inc (true, ()) m' rfl
                                                · m6_steps; exact hJ_inc (lim_w, ()) m' rfl)
                                          · m6_steps
                                            exact hJ_ov (nc_w, true, ()) m'
                                              ⟨st', ⟨hl', ha', by simpa only [hc,
                                                Bool.false_eq_true,
                                                ↓reduceIte] using hc', ht' ▸ hb_w.htmk,
                                                hw' ▸ hb_w.hwk⟩, hm'⟩))
                                · -- Unassigned `ov`
                                  have hov_tmk : (BitVec.setWidth 64 ov).toNat <
                                      st_w.scratch.tarjan_mark.length := by
                                    rw [htm_w, bv_c0_zext32_64]; omega
                                  have htm_w_idx :
                                      ∀ {j : Nat} (hj : j < st_w.scratch.tarjan_mark.length),
                                        j = ov.toNat →
                                        st_w.scratch.tarjan_mark[j]'hj =
                                          st_w.scratch.tarjan_mark[ov.toNat]'(by omega) :=
                                    fun _ hij => Option.some.inj (by subst hij; rfl)
                                  have hov_tmk_ws :
                                      (BitVec.setWidth 64
                                        ((st_w.core.wstk[p.toNat]'hp_wstk_w &&&
                                          (2147483647 : BitVec 32)) >>> (1 : Nat))).toNat <
                                        st_w.scratch.tarjan_mark.length := by
                                    rw [← hw0_def, show (2147483647 : BitVec 32) = 0x7FFFFFFF#32
                                        from rfl, ← hot_def, ← hov_def]
                                    exact hov_tmk
                                  m6_to_group
                                  refine wp_join_group (ts := [])
                                    (fun () md => md = mw)
                                    (fun _ () md hmd => by
                                      subst md
                                      clear hslice hslice1 hwv0_eq hwv1_eq h2l_mod h2l1_mod
                                        hw0_s hbin hnot_pos
                                      obtain ⟨saved_nv, hsav_eq⟩ : ∃ saved_nv : BitVec 32,
                                          saved_nv = nv_w := ⟨_, rfl⟩
                                      obtain ⟨scr_sav, hscr_sav_eq⟩ :
                                          ∃ scr_sav : List (BitVec 32),
                                            scr_sav = st_w.scratch.scratch_buf := ⟨_, rfl⟩
                                      have hsav_ge1 : 1 ≤ saved_nv.toNat :=
                                        hsav_eq ▸ hb_w.hcone.nv_ge1
                                      have hbdd_sav : K6LitsBounded saved_nv.toNat
                                          (k6StateOfScratch L scr_sav) :=
                                        hsav_eq ▸ hscr_sav_eq ▸ hb_w.hcone.k6_bdd
                                      have htrl_sav : ∀ l ∈ k6TrailLits (k6StateOfScratch L
                                          scr_sav), l < 2 * saved_nv.toNat :=
                                        hsav_eq ▸ hscr_sav_eq ▸ hb_w.hcone.k6_trl_bdd
                                      m6_to_group
                                      refine wp_join_group (ts := [i32, .bool])
                                        (fun (nv_a, _lim_a, ()) m_a => ∃ st_a : FullState,
                                          FidConeSavedBase F_cur L mv_c c s cv qi_l saved_nv
                                            st_w.scratch.work_stk1 scr_sav
                                            nv_a.toNat nc_w.toNat st_a
                                          ∧ st_a.scratch.tarjan_mark[ov.toNat]?.getD 0#32 ≠ 0#32 ∧
                                          (FullMem c st_a ⋆ R) m_a)
                                        (fun _ (nv_a, lim_a, ()) m_a ⟨st_a, hs_a, htoa, hma⟩ => by
                                          have htm_a := hs_a.hlen.scratch_ok.tarjan_mark_len
                                          have htmp_a := hs_a.hlen.core_ok.tmp_len_arr
                                          have hcv_a := fid_hag_cur_vars hs_a.hag
                                          rcases hs_a.hcone.rev ov.toNat
                                              (by rw [hcv_a]; exact hov_lt)
                                            with hz | ⟨iov, hiov, hwov, htov⟩
                                          · exact absurd hz htoa
                                          obtain ⟨hl0_lt, hl1_lt, hlift0, hlift1⟩ :=
                                            m6_cone_bin_lits_ok (Nat.lt_of_lt_of_le
                                              (by omega : qi_l.toNat < nv_w.toNat)
                                              (hsav_eq ▸ hs_a.hsav_le))
                                              (by have := hs_a.hcone.nv_leMax; omega)
                                              hpol_lt hlit_eq
                                              hov_eq hiov hs_a.htmk hs_a.hwk htov hwov
                                          have hcv_tm : cv.toNat <
                                              st_a.scratch.tarjan_mark.length := by omega
                                          have hov_tm : ov.toNat <
                                              st_a.scratch.tarjan_mark.length := by omega
                                          have hov_tm_a : (BitVec.setWidth 64 ov).toNat <
                                              st_a.scratch.tarjan_mark.length := by
                                            rw [htm_a, bv_c0_zext32_64]; omega
                                          rw [List.getElem?_eq_getElem hcv_tm, Option.getD_some]
                                            at hl0_lt hlift0
                                          rw [List.getElem?_eq_getElem hov_tm, Option.getD_some]
                                            at hl1_lt hlift1
                                          let l0_b := (qi_l <<< (1 : Nat)) ||| pol
                                          let l1_b := ((st_a.scratch.tarjan_mark[(BitVec.setWidth
                                            64 ov).toNat]'hov_tm_a - 1#32) <<< (1 : Nat)) |||
                                            (ot &&& 1#32)
                                          have htmp_a1 : 1 < st_a.core.tmp.length := by
                                            have := hs_a.hcone.nv_le_cv
                                            have := hs_a.hlen.core_ok.cur_vars_le
                                            have hne_cv_ov : cv.toNat ≠ ov.toNat := fun heq =>
                                              hov_ne_cv (BitVec.eq_of_toNat_eq heq.symm)
                                            omega
                                          let st_ab : FullState :=
                                            { st_a with core := { st_a.core with
                                              tmp := (st_a.core.tmp.set 0 l0_b).set 1 l1_b } }
                                          have hl0_eq : l0_b =
                                              ((st_a.scratch.tarjan_mark[cv.toNat]'hcv_tm -
                                                1#32) <<< (1 : Nat)) ||| pol := by
                                            dsimp only [l0_b]
                                            have ha : st_a.scratch.tarjan_mark[cv.toNat]'hcv_tm =
                                                BitVec.ofNat 32 (qi_l.toNat + 1) := by
                                              simpa only [List.getElem?_eq_getElem hcv_tm,
                                                Option.getD_some] using hs_a.htmk
                                            rw [ha, m6_bv32_ofNat_add1_sub1]
                                          have htm_ov_idx : st_a.scratch.tarjan_mark[
                                              (BitVec.setWidth 64 ov).toNat]'hov_tm_a =
                                              st_a.scratch.tarjan_mark[ov.toNat]'hov_tm :=
                                            m6_list_getElem_congr (bv_c0_zext32_64 ov)
                                              hov_tm_a hov_tm
                                          obtain ⟨hlen_ab, hlts_ab, hent_ab⟩ :=
                                            m6_cone_bin_tmp_prep (l1_b := l1_b) hs_a.hlen htmp_a1
                                              (hl0_eq ▸ hl0_lt)
                                              (by dsimp only [l1_b]; rw [htm_ov_idx]; exact hl1_lt)
                                              (hl0_eq ▸ hlift0)
                                              (by
                                                dsimp only [l1_b]
                                                rw [htm_ov_idx, hlift1, hot_def])
                                              hent_bin
                                          have htmp_a0 : 0 < st_a.core.tmp.length :=
                                            Nat.lt_trans Nat.zero_lt_one htmp_a1
                                          have hov_tm_a_ws :
                                              (BitVec.setWidth 64
                                                ((st_w.core.wstk[p.toNat]'hp_wstk_w &&&
                                                  (2147483647 : BitVec 32)) >>> (1 : Nat))).toNat <
                                                st_a.scratch.tarjan_mark.length := by
                                            rw [← hw0_def, show (2147483647 : BitVec 32) =
                                                0x7FFFFFFF#32 from rfl, ← hot_def, ← hov_def]
                                            exact hov_tm_a
                                          m6_to_group
                                          refine wp_join_group (ts := [i32, i32, .bool])
                                              (fun (nv_b, nc_b, _lim_b, ()) m_b =>
                                                layer_end.toNat ≤ nv_b.toNat ∧ ∃ st_b : FullState,
                                                  FidConeBase F_cur L mv_c c s cv qi_l nv_b.toNat
                                                    nc_b.toNat st_b ∧
                                                  (FullMem c st_b ⋆ R) m_b) ?_ ?_
                                          · rintro _ ⟨nv_b, nc_b, lim_b, ⟨⟩⟩ m_b
                                              ⟨hnvb, st_b, hbb, hmb⟩
                                            m6_steps
                                            exact hstep_bin nv_b nc_b lim_b st_b m_b hnvb hbb hmb
                                          · intro _ hJ_bin
                                            m6_steps
                                            have hcv_q' :
                                                st_l.scratch.work_stk1[(BitVec.setWidth 64
                                                  qi_l).toNat]'hqi_ws = cv := hcv_def.symm
                                            have hm_tmk0 :
                                                st_l.scratch.tarjan_mark[(BitVec.setWidth 64
                                                  (st_l.scratch.work_stk1[(BitVec.setWidth 64
                                                    qi_l).toNat]'hqi_ws)).toNat]'(by
                                                      rw [hcv_q']
                                                      exact hcv_tmk) - 1#32 = qi_l := by
                                              rw [m6_list_getElem_congr
                                                (congrArg (fun x => (BitVec.setWidth 64 x).toNat)
                                                  hcv_q')
                                                _ hcv_tmk, hmap_c]
                                            have hl1_c0 : ∀ {pf1 pf2},
                                                ((st_a.scratch.tarjan_mark[(BitVec.setWidth 64
                                                  ((st_w.core.wstk[p.toNat]'pf1 &&&
                                                    2147483647#32) >>> OfNat.ofNat 1)).toNat]'pf2 -
                                                  1#32) <<< (1 : Nat)) |||
                                                  ((st_w.core.wstk[p.toNat]'pf1 &&&
                                                    2147483647#32) &&& 1#32) = l1_b := by
                                              intro pf1 pf2
                                              have hidx : (BitVec.setWidth 64
                                                  ((st_w.core.wstk[p.toNat]'pf1 &&&
                                                    2147483647#32) >>> OfNat.ofNat 1)).toNat =
                                                  (BitVec.setWidth 64 ov).toNat := by
                                                rw [← hw0_def, show (2147483647#32 : BitVec 32) =
                                                    0x7FFFFFFF#32 from rfl, ← hot_def]
                                                change (BitVec.setWidth 64 (ot >>>
                                                  (1 : Nat))).toNat = (BitVec.setWidth 64 ov).toNat
                                                rw [← hov_def]
                                              have hot1 : ((st_w.core.wstk[p.toNat]'pf1 &&&
                                                  2147483647#32) &&& 1#32) = (ot &&& 1#32) := by
                                                rw [← hw0_def, show (2147483647#32 : BitVec 32) =
                                                    0x7FFFFFFF#32 from rfl, ← hot_def]
                                              dsimp only [l1_b]
                                              rw [m6_list_getElem_congr hidx pf2 hov_tm_a, hot1]
                                            refine fid_cone_call_add_clause hAddCl
                                              (aSz := Arg.imm 2) (sz := 2#32) rfl hL_len hL_mv
                                              hlen_ab (fidConeMask_upd_tmp _ hs_a.hag)
                                              (fidConeInv_tmp_irrel hs_a.hcone) hncw_lt (by decide)
                                              (by
                                                rw [hlen_ab.core_ok.tmp_len_arr, ← htmp_a]
                                                exact htmp_a1)
                                              hlts_ab hent_ab
                                              (m6_fullMem_tmp01_congr
                                                (congrArg (fun x : BitVec 32 =>
                                                  (x <<< (1 : Nat)) ||| pol) hm_tmk0)
                                                hl1_c0 ‹(FullMem c _ ⋆ R) _›)
                                              (fun ok st' m' hl' ha' hc' hfalse_scr ht' hw'
                                                hm' => by
                                                m6_split
                                                · m6_steps
                                                  exact hJ_bin (nv_a, nc_w + (1 : BitVec 32),
                                                      lim_a, ())
                                                    m' ⟨Nat.le_trans hnv_w_mono
                                                        (hsav_eq ▸ hs_a.hsav_le),
                                                      st', ⟨hl', ha',
                                                        by
                                                          rw [show (1 : BitVec 32) = 1#32 from rfl]
                                                          simpa only [hc, ↓reduceIte] using hc',
                                                        ht' ▸ hs_a.htmk, hw' ▸ hs_a.hwk⟩, hm'⟩
                                                · have hs'_saved : FidConeSavedBase F_cur L mv_c c s
                                                      cv qi_l saved_nv st_w.scratch.work_stk1
                                                      scr_sav nv_a.toNat nc_w.toNat st' :=
                                                    ⟨⟨hl', ha', by simpa only
                                                        [hc, Bool.false_eq_true, ↓reduceIte]
                                                        using hc', ht' ▸ hs_a.htmk,
                                                        hw' ▸ hs_a.hwk⟩,
                                                      hs_a.hsav_le,
                                                      (hfalse_scr (by cases ok <;> simp at hc ⊢)
                                                        ).trans hs_a.hscr,
                                                      hw' ▸ hs_a.hws⟩
                                                  m6_to_group
                                                  refine wp_loop_inv (ts := [i32])
                                                    (fun (nv_r, ()) mr =>
                                                      nv_r.toNat ≤ nv_a.toNat ∧
                                                      ∃ st_r : FullState,
                                                        FidConeSavedBase F_cur L mv_c c s cv qi_l
                                                          saved_nv st_w.scratch.work_stk1
                                                          scr_sav nv_r.toNat nc_w.toNat st_r ∧
                                                        (FullMem c st_r ⋆ R) mr)
                                                    (fun (nv_r, ()) _ =>
                                                      nv_r.toNat - saved_nv.toNat)
                                                    (fun _ hJr => by
                                                      m6_steps
                                                      exact hJr (nv_a, ()) m'
                                                        ⟨le_refl _, st', hs'_saved, hm'⟩)
                                                    (fun _ (nv_r, ()) mr ⟨hle_a, st_r, hs_r,
                                                        hmr⟩ hJr => by
                                                      m6_split
                                                      · have hsav_lt :
                                                          saved_nv.toNat < nv_r.toNat := by
                                                          rw [hsav_eq]; exact hc
                                                        obtain ⟨hnv1, hvr_lt, hstep⟩ :=
                                                          fid_coneBase_of_rollback_step hs_r
                                                            hsav_ge1 hsav_lt
                                                            (by
                                                              rw [hsav_eq]
                                                              exact Nat.lt_of_lt_of_le hqi_l_lt
                                                                hnv_w_mono)
                                                            hbdd_sav htrl_sav
                                                        obtain ⟨hvr_tmk_bd, hs'⟩ := hstep hvr_lt
                                                        m6_steps
                                                        refine hJr (nv_r - 1#32, ()) _
                                                          (by
                                                            dsimp only
                                                            exact m6_nat_sub_lo1_lt hsav_lt
                                                              hnv1)
                                                          ⟨hnv1 ▸ le_trans (Nat.sub_le _ _)
                                                            hle_a, _, hs', ?_⟩
                                                        try rw [m6_tmk_set_mod64] at hm
                                                        exact fid_cone_rollback_mem_step _ hvr_lt
                                                          (m6_bv32_sub1_zext_toNat nv_r) hm
                                                      · have hnv_le_sav :
                                                          nv_r.toNat ≤ saved_nv.toNat := by
                                                          rw [hsav_eq]
                                                          exact Nat.le_of_not_lt hc
                                                        m6_steps
                                                        have hnv_eq : nv_r = saved_nv :=
                                                          BitVec.eq_of_toNat_eq
                                                            (Nat.le_antisymm hnv_le_sav
                                                              hs_r.hsav_le)
                                                        have hle_nv_r :
                                                            layer_end.toNat ≤ nv_r.toNat := by
                                                          rw [hnv_eq, hsav_eq]; exact hnv_w_mono
                                                        exact hJ_bin (nv_r, nc_w, true, ()) mr
                                                          ⟨hle_nv_r, st_r,
                                                           hnv_eq ▸ hs_r.toFidConeBase, hmr⟩)))
                                        (fun _ hJ_a => by
                                          m6_split
                                          · have hmiss : st_w.scratch.tarjan_mark[ov.toNat]?.getD
                                                0#32 = 0#32 := by
                                              rw [List.getElem?_eq_getElem (by omega),
                                                Option.getD_some]
                                              rw [htm_w_idx _ (by
                                                rw [← hw0_def,
                                                  show (2147483647 : BitVec 32) = 0x7FFFFFFF#32
                                                    from rfl,
                                                  ← hot_def]
                                                change (BitVec.setWidth 64 (ot >>>
                                                  (1 : Nat))).toNat = ov.toNat
                                                rw [← hov_def, bv_c0_zext32_64])] at hc
                                              exact hc
                                            m6_split
                                            · m6_steps
                                              exact hJ_we (nv_w, nc_w, true, p + 1#64, ()) mw
                                                ⟨hnv_w_mono, st_w, hb_w, hmw⟩
                                            · have hnv_lt_max : nv_w.toNat < mv_c.toNat := by
                                                have : ¬ mv_c.toNat ≤ nv_w.toNat := hc
                                                omega
                                              have hqi_nv_w : qi_l.toNat < nv_w.toNat :=
                                                Nat.lt_of_lt_of_le hqi_l_lt hnv_w_mono
                                              have hs_w_sav :
                                                  FidConeSavedBase F_cur L mv_c c s cv qi_l
                                                  saved_nv st_w.scratch.work_stk1 scr_sav
                                                  nv_w.toNat nc_w.toNat st_w :=
                                                ⟨hb_w, hsav_eq ▸ le_refl _, hscr_sav_eq.symm,
                                                 fun _ _ => rfl⟩
                                              obtain ⟨hnv_w_lt, hnv1, hne_nv_qi, hne_cv, hs_a,
                                                htlva⟩ :=
                                                fid_cone_push_var_base_ok hs_w_sav hnv_lt_max
                                                  hov_lt hmiss hqi_nv_w
                                              have hnv_ws : (BitVec.setWidth 64 ((nv_w + 1#32) -
                                                  1#32)).toNat < st_w.scratch.work_stk1.length := by
                                                rw [hwk_w_len, bv_c0_zext32_64,
                                                  m6_bv32_add1_sub1_eq nv_w]; omega
                                              m6_steps
                                              let st_a : FullState :=
                                                { st_w with scratch :=
                                                  { st_w.scratch with
                                                    tarjan_mark := st_w.scratch.tarjan_mark.set
                                                      ov.toNat (nv_w + 1#32)
                                                    work_stk1 := st_w.scratch.work_stk1.set
                                                      nv_w.toNat ov } }
                                              have h2 := m6_bv32_add1_sub1_toNat nv_w
                                              have htm_idx : (BitVec.setWidth 64
                                                  ((st_w.core.wstk[p.toNat]'hp_wstk_w &&&
                                                    2147483647#32) >>> OfNat.ofNat 1)).toNat =
                                                  ov.toNat := by
                                                rw [← hw0_def, show (2147483647#32 : BitVec 32) =
                                                    0x7FFFFFFF#32 from rfl, ← hot_def]
                                                change (BitVec.setWidth 64 (ot >>>
                                                  (1 : Nat))).toNat = ov.toNat
                                                rw [← hov_def, bv_c0_zext32_64]
                                              have hws_val :
                                                  ((st_w.core.wstk[p.toNat]'hp_wstk_w &&&
                                                    2147483647#32) >>> OfNat.ofNat 1) = ov := by
                                                rw [← hw0_def, show (2147483647#32 : BitVec 32) =
                                                    0x7FFFFFFF#32 from rfl, ← hot_def]
                                                exact hov_def.symm
                                              have hm_a : (FullMem c st_a ⋆ R) m := by
                                                have hm' := hm
                                                dsimp only [LeanQbe.T.lift2, Arg.val_var,
                                                  Arg.val_imm] at hm'
                                                try rw [show (2147483647 : BitVec 32) =
                                                    2147483647#32 from rfl] at hm'
                                                try rw [hws_val] at hm'
                                                try rw [show (1 : BitVec 32) = 1#32 from rfl] at hm'
                                                try rw [htm_idx] at hm'
                                                repeat rw [bv_c0_zext32_64] at hm'
                                                try rw [h2] at hm'
                                                exact hm'
                                              exact hJ_a (nv_w + 1#32, lim_w, ()) m
                                                ⟨st_a, hnv1 ▸ hs_a, htlva, hm_a⟩
                                          · have hne_ov : st_w.scratch.tarjan_mark[ov.toNat]?.getD
                                                0#32 ≠ 0#32 := by
                                              rw [List.getElem?_eq_getElem (by omega),
                                                Option.getD_some]
                                              rw [htm_w_idx _ (by
                                                rw [← hw0_def,
                                                  show (2147483647 : BitVec 32) = 0x7FFFFFFF#32
                                                    from rfl,
                                                  ← hot_def]
                                                change (BitVec.setWidth 64 (ot >>>
                                                  (1 : Nat))).toNat = ov.toNat
                                                rw [← hov_def, bv_c0_zext32_64])] at hc
                                              exact hc
                                            m6_steps
                                            exact hJ_a (nv_w, lim_w, ()) mw
                                              ⟨st_w, ⟨hb_w, hsav_eq ▸ le_refl _, hscr_sav_eq.symm,
                                                fun _ _ => rfl⟩, hne_ov, hmw⟩))
                                    (fun _ hJ_d => by
                                      m6_split
                                      · m6_split
                                        · m6_steps
                                          exact hstep_bin nv_w nc_w lim_w st_w mw hnv_w_mono
                                            hb_w hmw
                                        · m6_steps; exact hJ_d () mw rfl
                                      · m6_steps; exact hJ_d () mw rfl)))))))

    · intro _ hJ_mc
      m6_split
      · m6_steps
        exact hJ_mc (mv * 3#32, ()) _ ⟨by rw [hmo_nat]; exact Nat.le_refl _, hmm⟩
      · m6_steps
        refine hJ_mc (_, ()) _ ⟨?_, hmm⟩
        have hnot := hc
        have h3 : (3 : BitVec 32).toNat = 3 := rfl
        unfold K6Layout.maxOrig
        rw [hL_mv]
        rw [h3, Nat.mod_eq_of_lt (by omega : k6MaxV c.scratch_cap < 2 ^ 64),
          Nat.mod_eq_of_lt (by omega : k6MaxV c.scratch_cap < 2 ^ 32),
          Nat.mod_eq_of_lt (by omega : k6MaxV c.scratch_cap * 3 < 2 ^ 32)] at hnot
        omega
  · intro _ hJ_mv
    m6_split
    · m6_steps
      exact hJ_mv (mv, ()) _ ⟨by rw [hmv_nat]; omega, by rw [hmv_nat]; exact Nat.le_refl _, hm_d⟩
    · m6_steps
      have hsh : ((256 : BitVec 32) <<< (comp.toNat % 32)) = 256#32 <<< comp := by
        rw [Nat.mod_eq_of_lt (by omega : comp.toNat < 32)]; rfl
      refine hJ_mv (_, ()) _ ⟨by rw [hsh]; exact hvlim_lo, ?_, hm_d⟩
      have hnot := hc
      rw [hL_mv]
      rw [Nat.mod_eq_of_lt (by omega : k6MaxV c.scratch_cap < 2 ^ 64),
        Nat.mod_eq_of_lt (by omega : k6MaxV c.scratch_cap < 2 ^ 32)] at hnot
      omega

end LeanQbe.T.Examples.Kissat.FullFidelitySweep

end
