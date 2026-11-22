module

public import LeanQbe.T.Examples.Kissat.FullBvaHeapSpec
import LeanQbe.T.Logic.ControlComb
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Full` 3-Hop BVA & Max-Degree Binary Heap Factoring — `full_factor_wp` (`Part 6`)

Extracted from `FullBvaHeapLemmas.lean` so `full_factor_wp` compiles in parallel with
`FullBvaHeapLemmas{1..5}`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullBvaHeap

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.C0Step LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test
open FullBvaHeapTactics FullBvaHeapHelpers FullBvaHeapScanHelpers
open scoped FullArenaTactics FullBvaHeapTactics


section FullFactorHelpers

private def FullMemFheapRest (c : FullCfg) (s : FullState) : Mem 64 → Prop :=
  dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
  array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆
  FullCoreByteArrs c s.core ⋆ FullCoreU32A c s.core ⋆
  (array (t := i32) c.pFrameTrail s.core.frame_trail ⋆
   array (t := i32) c.pFrameDec s.core.frame_dec ⋆
   array (t := i32) c.pRepr s.core.repr ⋆ array (t := i32) c.pMinStk s.core.min_stk) ⋆
  FullCoreDynArrs c s.core ⋆
  FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆
  (array (t := i32) c.pWsort s.scratch.wsort ⋆
   array (t := i32) c.pWorkStk1 s.scratch.work_stk1 ⋆
   array (t := i32) c.pWorkStk2 s.scratch.work_stk2) ⋆
  FullScrMetaArrs c s.scratch ⋆ FullScrDynArrs c s.scratch ⋆ c.pad

private theorem focus_fheap {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem c s ⋆ R) m) :
    (array (t := i32) c.pTarjanMark s.scratch.tarjan_mark ⋆
     array (t := i32) c.pTarjanReach s.scratch.tarjan_reach ⋆
     array (t := i32) c.pWvec s.core.wvec ⋆
     (FullMemFheapRest c s ⋆ R)) m := by
  unfold FullMem FullCoreArrays FullCoreU32B FullScratchArrays FullScrWksArrs at hm
  unfold FullMemFheapRest
  exact sep_ac hm

private theorem unfocus_fheap {c : FullCfg} {s : FullState} {hp' ps' : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (array (t := i32) c.pTarjanMark hp' ⋆
           array (t := i32) c.pTarjanReach ps' ⋆
           array (t := i32) c.pWvec s.core.wvec ⋆
           (FullMemFheapRest c s ⋆ R)) m) :
    (FullMem c { s with scratch :=
      { s.scratch with tarjan_mark := hp', tarjan_reach := ps' } } ⋆ R) m := by
  unfold FullMem FullCoreArrays FullCoreU32B FullScratchArrays FullScrWksArrs
  unfold FullMemFheapRest at hm
  exact sep_ac hm

private theorem fullDenseInv_set_fheap {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hinv : FullDenseInv c F0 s) {hp' ps' : List (BitVec 32)}
    (hhp : hp'.length = 2 * c.max_vars) (hps : ps'.length = 2 * c.max_vars) :
    FullDenseInv c F0
      { s with scratch := { s.scratch with tarjan_mark := hp', tarjan_reach := ps' } } := by
  obtain ⟨_F_cur, hw⟩ := hinv.exists_witness
  exact (fullDenseInv_with_core_aux (tc' := s.core.tmp_cnt) (tl' := s.core.tmp_len)
    (sc' := { s.scratch with tarjan_mark := hp', tarjan_reach := ps' }) hw
    hw.1.core_ok.repr_len hw.1.core_ok.min_clr_len_arr hw.1.core_ok.tmp_len_arr
    hw.1.core_ok.flags_len hw.1.core_ok.tmp_len_le
    { hw.1.scratch_ok with tarjan_mark_len := hhp, tarjan_reach_len := hps } rfl rfl).toDense

private theorem fullDenseInv_set_flags_d {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hinv : FullDenseInv c F0 s) {fl' : List (BitVec 32)} (hfl : fl'.length = c.max_vars) :
    FullDenseInv c F0 { s with core := { s.core with flags := fl' } } := by
  obtain ⟨_F_cur, hw⟩ := hinv.exists_witness
  exact (fullDenseInv_with_core_aux (tc' := s.core.tmp_cnt) (tl' := s.core.tmp_len)
    (sc' := s.scratch) hw hw.1.core_ok.repr_len hw.1.core_ok.min_clr_len_arr
    hw.1.core_ok.tmp_len_arr hfl hw.1.core_ok.tmp_len_le hw.1.scratch_ok rfl rfl).toDense

private theorem extract_flags_upd {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    {fl2 : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64}
    (hinv : FullDenseInv c F0 s) (hfl : fl2.length = c.max_vars)
    (hm : (FullMem c { s with core := { s.core with flags := fl2 } } ⋆ R) m) :
    ∃ st2 : FullState, FullDenseInv c F0 st2 ∧
      st2.core.cur_vars = s.core.cur_vars ∧ st2.core.fuel = s.core.fuel ∧
      st2.scratch.tarjan_mark = s.scratch.tarjan_mark ∧
      st2.scratch.tarjan_reach = s.scratch.tarjan_reach ∧
      (FullMem c st2 ⋆ R) m :=
  ⟨_, fullDenseInv_set_flags_d hinv hfl, rfl, rfl, rfl, rfl, hm⟩

end FullFactorHelpers

theorem full_factor_wp (Γ : Env)
    (hUp : ∀ args m Q X, fullFheapUpSpec args m Q X →
      Γ "full_fheap_up" [i64, i64, i64, i32] [] args m Q X)
    (hDown : ∀ args m Q X, fullFheapDownSpec args m Q X →
      Γ "full_fheap_down" [i64, i64, i64, i32, i32] [] args m Q X)
    (hTryLit : ∀ args m Q X, fullBvaTryLitHeapSpec args m Q X →
      Γ "full_bva_try_lit" [i64, i32, i64] [.bool] args m Q X) :
    ∀ args m Q X, fullFactorHeapSpec args m Q X →
      Func.wp Γ full_factor_body args m Q X := by
  rintro ⟨h, budget0, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv0, hm, hQ⟩
  obtain ⟨F_cur0, hw0⟩ := hinv0.exists_witness
  have hmx := c.hmaxv; have hscr_b := c.hscr; unfold dimacsBound at hmx hscr_b
  have hcl := hw0.1.core_ok; have hsc := hw0.1.scratch_ok
  have hcv_le := hcl.cur_vars_le; have hwv_len := hcl.wvec_len
  have hvals_len := hcl.vals_len; have hfl_len := hcl.flags_len
  have hrepr_len := hcl.repr_len; have hsig_len := hsc.sim_sig_len
  have hws_len := hsc.wsort_len; have htm_len := hsc.tarjan_mark_len
  have htr_len := hsc.tarjan_reach_len
  c0_hsteps
  · exact hQ 1#64 s m hw0.toDense (Nat.le_refl _) rfl rfl hm
  · exact hQ 1#64 s m hw0.toDense (Nat.le_refl _) rfl rfl hm
  · exact hQ 1#64 s m hw0.toDense (Nat.le_refl _) rfl rfl hm
  · -- Guard passed: zero `cnt`/`hp`/`ps`, zero `s1`/`s2`, build heap, main loop, zero `hp`/`ps`
    have hcv_lt : s.core.cur_vars < c.max_vars := by
      have h1 : ¬ c.max_vars % 2 ^ 64 ≤ s.core.cur_vars % 2 ^ 64 := by assumption
      omega
    have hmx2 : (BitVec.ofNat 64 c.max_vars <<< (1 : Nat)).toNat = 2 * c.max_vars := by
      rw [bv64_shl1_nat, BitVec.toNat_ofNat]; omega
    have hnl_lt : 2 * c.max_vars < 2 ^ 30 := by omega
    -- Loop 1: zero `cnt[0..2*max_vars)`, `hp[0..2*max_vars)`, `ps[0..2*max_vars)`
    refine wp_loop_inv
      (fun (i, ()) mi => ∃ wsi hpi psi : List (BitVec 32),
        i.toNat ≤ 2 * c.max_vars ∧
        wsi.length = 2 * c.max_vars ∧ hpi.length = 2 * c.max_vars ∧ psi.length = 2 * c.max_vars ∧
        (FullMem c { s with scratch :=
          { s.scratch with wsort := wsi, tarjan_mark := hpi, tarjan_reach := psi } } ⋆ R) mi)
      (fun (i, _) _ => 2 * c.max_vars - i.toNat)
      (fun J1 hJ1 => by
        c0_hfast; exact hJ1 (0#64, ()) m ⟨s.scratch.wsort, s.scratch.tarjan_mark,
          s.scratch.tarjan_reach, Nat.zero_le _, hws_len, htm_len, htr_len, hm⟩)
      (fun J1 (i, ()) mi ⟨wsi, hpi, psi, hi_le, hwsi_l, hhpi_l, hpsi_l, hmi⟩ ih1 => ?_)
    clear m hm
    c0_hsplit
    · have hi_lt : i.toNat < 2 * c.max_vars := by
        have h1 : i.toNat < (BitVec.ofNat 64 c.max_vars <<< (1 : Nat)).toNat := by assumption
        rwa [hmx2] at h1
      have hi1 : (i + 1#64).toNat = i.toNat + 1 := by simp only [bv_c0]; omega
      c0_hfast
      exact ih1 (i + 1#64, ()) m (by dsimp only; rw [hi1]; omega)
        ⟨_, _, _, by rw [hi1]; omega, by simp [hwsi_l], by simp [hhpi_l], by simp [hpsi_l], hm⟩
    · -- Loop 2: zero `s1[0..max_vars)`, `s2[0..max_vars)`
      refine wp_loop_inv
        (fun (i, ()) mi2 => ∃ (rpi : List (BitVec 32)) (sigi : List (BitVec 64)),
          i.toNat ≤ c.max_vars ∧ rpi.length = 2 * c.max_vars ∧ sigi.length = c.max_vars ∧
          (FullMem c { core := { s.core with repr := rpi }
                       scratch := { s.scratch with wsort := wsi, tarjan_mark := hpi,
                                                   tarjan_reach := psi, sim_sig := sigi } } ⋆
            R) mi2)
        (fun (i, _) _ => c.max_vars - i.toNat)
        (fun J2 hJ2 => by
          c0_hfast; exact hJ2 (0#64, ()) mi ⟨s.core.repr, s.scratch.sim_sig, Nat.zero_le _,
            hrepr_len, hsig_len, hmi⟩)
        (fun J2 (i, ()) mi2 ⟨rpi, sigi, hi_le, hrpi_l, hsigi_l, hmi2⟩ ih2 => ?_)
      c0_hsplit
      · have hi_lt : i.toNat < c.max_vars := by
          have h1 : i.toNat < c.max_vars % 2 ^ 64 := by assumption
          omega
        have hi1 : (i + 1#64).toNat = i.toNat + 1 := by simp only [bv_c0]; omega
        c0_hfast
        exact ih2 (i + 1#64, ()) m (by dsimp only; rw [hi1]; omega)
          ⟨_, _, by rw [hi1]; omega, by rw [repr64Set_length, hrpi_l], by simp [hsigi_l], hm⟩
      · -- Loop 3: build initial max-degree heap over `v < init_cv`
        let st_z : FullState :=
          { core := { s.core with repr := rpi }
            scratch := { s.scratch with wsort := wsi, tarjan_mark := hpi,
                                        tarjan_reach := psi, sim_sig := sigi } }
        have hfl_stz : st_z.core.flags.length = c.max_vars := hfl_len
        have hvals_stz : st_z.core.vals.length = 2 * c.max_vars := hvals_len
        have hwv_stz : st_z.core.wvec.length = 4 * c.max_vars := hwv_len
        have hinv_z : FullDenseInv c F0 st_z :=
          (fullDenseInv_with_core_aux (tc' := s.core.tmp_cnt) (tl' := s.core.tmp_len)
            (sc' := st_z.scratch) hw0 hrpi_l hcl.min_clr_len_arr hcl.tmp_len_arr hfl_len
            hcl.tmp_len_le
            { hsc with wsort_len := hwsi_l, tarjan_mark_len := hhpi_l,
                       tarjan_reach_len := hpsi_l, sim_sig_len := hsigi_l } rfl rfl).toDense
        refine wp_loop_inv
          (fun (hlen, v, ()) mv => ∃ hpv psv : List (BitVec 32),
            v.toNat ≤ s.core.cur_vars ∧ hlen.toNat ≤ 2 * v.toNat ∧
            hpv.length = 2 * c.max_vars ∧ psv.length = 2 * c.max_vars ∧
            (∀ k < hlen.toNat, (hpv[k]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
            (FullMem c { st_z with scratch :=
              { st_z.scratch with tarjan_mark := hpv, tarjan_reach := psv } } ⋆ R) mv)
          (fun (_, v, _) _ => s.core.cur_vars - v.toNat)
          (fun Jv hJv => by
            c0_hfast
            exact hJv (0#32, 0#64, ()) mi2 ⟨hpi, psi, Nat.zero_le _, by decide, hhpi_l, hpsi_l,
              fun _ h => by simp only [BitVec.toNat_ofNat] at h; omega, hmi2⟩)
          (fun Jv (hlen, v, ()) mv ⟨hpv, psv, hv_le, hhl_le, hhpv_l, hpsv_l, hhpv_ok, hmv⟩
              ihv => ?_)
        c0_hsplit
        · have hv_lt : v.toNat < s.core.cur_vars := by
            have h1 : v.toNat < s.core.cur_vars % 2 ^ 64 := by assumption
            omega
          have hv1 : (v + 1#64).toNat = v.toNat + 1 := by simp only [bv_c0]; omega
          have hv2_lt : (v <<< (1 : Nat)).toNat < st_z.core.vals.length := by
            rw [hvals_stz, bv64_shl1_nat]; omega
          have hpl_nat : (BitVec.setWidth 32 (v <<< (1 : Nat))).toNat = 2 * v.toNat := by
            simp only [BitVec.toNat_setWidth, bv64_shl1_nat]; omega
          have hnl_nat : ((BitVec.setWidth 32 (v <<< (1 : Nat))) ||| 1#32).toNat =
              2 * v.toNat + 1 := by
            rw [FullBvaFwdTactics.bv32_or1_of_even (by rw [hpl_nat]; omega), hpl_nat]
          c0_hstep
          c0_hsteps_nogrp
          · -- Active & unassigned: check `FL_FACT_P` then `FL_FACT_N`
            have hwv_pl : ((BitVec.setWidth 64 (BitVec.setWidth 32 (v <<< (1 : Nat))) <<<
                (1 : Nat)) + 1).toNat < st_z.core.wvec.length := by
              change ((BitVec.setWidth 64 _ <<< (1 : Nat)) + 1#64).toNat < _
              rw [hwv_stz, BitVec.toNat_add, bv64_shl1_nat, bv64_setWidth_32, hpl_nat,
                show (1#64).toNat = 1 from rfl]; omega
            have hwv_nl : ((BitVec.setWidth 64 ((BitVec.setWidth 32 (v <<< (1 : Nat))) |||
                1#32) <<< (1 : Nat)) + 1).toNat < st_z.core.wvec.length := by
              change ((BitVec.setWidth 64 _ <<< (1 : Nat)) + 1#64).toNat < _
              rw [hwv_stz, BitVec.toNat_add, bv64_shl1_nat, bv64_setWidth_32, hnl_nat,
                show (1#64).toNat = 1 from rfl]; omega
            refine wp_join_state1 (t := i32)
              (α := BitVec 32 × List (BitVec 32) × List (BitVec 32))
              (fun x => x.1)
              (fun ⟨hl1, hp1, ps1⟩ m1 =>
                (FullMem c { st_z with scratch :=
                  { st_z.scratch with tarjan_mark := hp1, tarjan_reach := ps1 } } ⋆ R) m1 ∧
                hl1.toNat ≤ 2 * v.toNat + 1 ∧
                hp1.length = 2 * c.max_vars ∧ ps1.length = 2 * c.max_vars ∧
                (∀ k < hl1.toNat, (hp1[k]?.getD 0#32).toNat < 2 * s.core.cur_vars))
              (fun _ ⟨hl1, hp1, ps1⟩ m1 ⟨hm1, hhl1_le, hhp1_l, hps1_l, hhp1_ok⟩ => ?_)
              (fun Jp1 hJp1 => ?_)
            · -- Check `FL_FACT_N`
              have hnl_ps : (BitVec.setWidth 64 ((BitVec.setWidth 32 (v <<< (1 : Nat))) |||
                  1#32)).toNat < ps1.length := by rw [bv64_setWidth_32, hnl_nat, hps1_l]; omega
              have hhl1_hp : (BitVec.setWidth 64 hl1).toNat < hp1.length := by
                rw [bv64_setWidth_32, hhp1_l]; omega
              c0_hfast
              · have hhl2 : (hl1 + 1#32).toNat = hl1.toNat + 1 := by simp only [bv_c0]; omega
                let nl_bv := (BitVec.setWidth 32 (v <<< (1 : Nat))) ||| 1#32
                let hp1a := hp1.set hl1.toNat nl_bv
                let ps1a := ps1.set nl_bv.toNat hl1
                have hm1a : (FullMem c { st_z with scratch :=
                    { st_z.scratch with tarjan_mark := hp1a, tarjan_reach := ps1a } } ⋆ R) m := by
                  simp only [hp1a, ps1a, nl_bv, bv64_setWidth_32] at hm ⊢; exact hm
                c0_call hUp
                refine ⟨2 * c.max_vars, hp1a, ps1a, st_z.core.wvec,
                  FullMemFheapRest c st_z ⋆ R,
                  by simp [hp1a, hhp1_l], by simp [ps1a, hps1_l],
                  by dsimp only [st_z]; omega, hnl_lt, by omega,
                  fun i hi => by
                    dsimp only [hp1a]
                    by_cases hie : i = hl1.toNat
                    · subst hie; rw [List.getElem?_set_self (by omega), Option.getD_some]
                      dsimp only [nl_bv]; rw [hnl_nat]; omega
                    · rw [List.getElem?_set_ne (Ne.symm hie)]
                      have := hhp1_ok i (by omega); omega,
                  focus_fheap hm1a,
                  fun hp2 ps2 m2 hhp2_l hps2_l hsub2 _ hm2 => ?_⟩
                c0_hfast
                refine ihv (hl1 + 1#32, v + 1#64, ()) m2 (by dsimp only; rw [hv1]; omega)
                  ⟨hp2, ps2, by rw [hv1]; omega, by rw [hv1, hhl2]; omega,
                   by simp [hp1a, hhp1_l] at hhp2_l; exact hhp2_l,
                   by simp [ps1a, hps1_l] at hps2_l; exact hps2_l, fun k hk => ?_,
                   unfocus_fheap hm2⟩
                rw [hhl2] at hk
                obtain ⟨j, hj, heq⟩ := hsub2 k (by omega)
                rw [heq]; dsimp only [hp1a]
                by_cases hje : j = hl1.toNat
                · subst hje; rw [List.getElem?_set_self (by omega), Option.getD_some]
                  dsimp only [nl_bv]; rw [hnl_nat]; omega
                · rw [List.getElem?_set_ne (Ne.symm hje)]; exact hhp1_ok j (by omega)
              all_goals
                exact ihv (hl1, v + 1#64, ()) m1 (by dsimp only; rw [hv1]; omega)
                  ⟨hp1, ps1, by rw [hv1]; omega, by rw [hv1]; omega, hhp1_l, hps1_l, hhp1_ok, hm1⟩
            · -- Check `FL_FACT_P`
              have hpl_ps : (BitVec.setWidth 64 (BitVec.setWidth 32 (v <<< (1 : Nat)))).toNat <
                  psv.length := by rw [bv64_setWidth_32, hpl_nat, hpsv_l]; omega
              have hhl_hp : (BitVec.setWidth 64 hlen).toNat < hpv.length := by
                rw [bv64_setWidth_32, hhpv_l]; omega
              c0_hfast
              · have hhl1 : (hlen + 1#32).toNat = hlen.toNat + 1 := by simp only [bv_c0]; omega
                let pl_bv := BitVec.setWidth 32 (v <<< (1 : Nat))
                let hp0a := hpv.set hlen.toNat pl_bv
                let ps0a := psv.set pl_bv.toNat hlen
                have hm0a : (FullMem c { st_z with scratch :=
                    { st_z.scratch with tarjan_mark := hp0a, tarjan_reach := ps0a } } ⋆ R) m := by
                  simp only [hp0a, ps0a, pl_bv, bv64_setWidth_32] at hm ⊢; exact hm
                c0_call hUp
                refine ⟨2 * c.max_vars, hp0a, ps0a, st_z.core.wvec,
                  FullMemFheapRest c st_z ⋆ R,
                  by simp [hp0a, hhpv_l], by simp [ps0a, hpsv_l],
                  by dsimp only [st_z]; omega, hnl_lt, by omega,
                  fun i hi => by
                    dsimp only [hp0a]
                    by_cases hie : i = hlen.toNat
                    · subst hie; rw [List.getElem?_set_self (by omega), Option.getD_some]
                      dsimp only [pl_bv]; rw [hpl_nat]; omega
                    · rw [List.getElem?_set_ne (Ne.symm hie)]
                      have := hhpv_ok i (by omega); omega,
                  focus_fheap hm0a,
                  fun hp1 ps1 m1 hhp1_l hps1_l hsub1 _ hm1 => ?_⟩
                c0_hfast
                refine hJp1 ⟨hlen + 1#32, hp1, ps1⟩ m1
                  ⟨unfocus_fheap hm1, by rw [hhl1]; omega,
                   by simp [hp0a, hhpv_l] at hhp1_l; exact hhp1_l,
                   by simp [ps0a, hpsv_l] at hps1_l; exact hps1_l, fun k hk => ?_⟩
                rw [hhl1] at hk
                obtain ⟨j, hj, heq⟩ := hsub1 k (by omega)
                rw [heq]; dsimp only [hp0a]
                by_cases hje : j = hlen.toNat
                · subst hje; rw [List.getElem?_set_self (by omega), Option.getD_some]
                  dsimp only [pl_bv]; rw [hpl_nat]; omega
                · rw [List.getElem?_set_ne (Ne.symm hje)]; exact hhpv_ok j (by omega)
              all_goals
                exact hJp1 ⟨hlen, hpv, psv⟩ mv ⟨hmv, by omega, hhpv_l, hpsv_l, hhpv_ok⟩
          all_goals
            exact ihv (hlen, v + 1#64, ()) mv (by dsimp only; rw [hv1]; omega)
              ⟨hpv, psv, by rw [hv1]; omega, by rw [hv1]; omega, hhpv_l, hpsv_l, hhpv_ok, hmv⟩
        · -- Main factoring loop `while (hlen > 0 && cur_vars < max_vars && budget > 0 && oom == 0)`
          let st_init : FullState :=
            { st_z with scratch := { st_z.scratch with tarjan_mark := hpv, tarjan_reach := psv } }
          refine wp_loop_inv
            (fun (budget, hlen, ()) ml => ∃ stl : FullState,
              (FullMem c stl ⋆ R) ml ∧
              FullDenseInv c F0 stl ∧
              s.core.cur_vars ≤ stl.core.cur_vars ∧ stl.core.fuel = s.core.fuel ∧
              hlen.toNat ≤ 2 * c.max_vars ∧
              (∀ k < hlen.toNat,
                (stl.scratch.tarjan_mark[k]?.getD 0#32).toNat < 2 * stl.core.cur_vars))
            (fun (budget, hlen, _) _ => budget.toNat * (2 * c.max_vars + 1) + hlen.toNat)
            (fun Jm hJm => by
              c0_hfast
              exact hJm (budget0, hlen, ()) mv
                ⟨st_init, hmv, fullDenseInv_set_fheap hinv_z hhpv_l hpsv_l,
                 Nat.le_refl _, rfl, by omega, hhpv_ok⟩)
            (fun Jm (budget, hlen, ()) ml
                ⟨stl, hml, hinvl, hcv_ge, hfuell, hhl_le, hhp_ok⟩ ihm => ?_)
          clear st_init hmv hhpv_ok hhpv_l hpsv_l hinv_z hfl_stz hvals_stz hwv_stz hrpi_l hsigi_l
            hwsi_l hhpi_l hpsi_l hw0 hcl hsc hcv_le hwv_len hvals_len hfl_len hrepr_len hsig_len
            hws_len htm_len htr_len ihv ih2 ih1
          obtain ⟨F_l, hwl⟩ := hinvl.exists_witness
          have hcll := hwl.1.core_ok; have hscl := hwl.1.scratch_ok
          have hcvl_le := hcll.cur_vars_le
          -- Exit join point `Jmain` inside loop body (from `&&` condition)
          refine wp_join_state0 (α := Unit)
            (fun _ mf => mf = ml)
            (fun _ _ mf hmf => ?_)
            (fun Jmain hJmain => ?_)
          · -- Exit main loop (elaborated once!): zero `hp[0..2*cur_vars)` & `ps`, return `1ULL`
            subst mf
            have h2cvl : (BitVec.ofNat 64 stl.core.cur_vars <<< (1 : Nat)).toNat =
                2 * stl.core.cur_vars := by
              have := hcll.cur_vars_le; rw [bv64_shl1_nat, BitVec.toNat_ofNat]; omega
            refine wp_loop_inv
              (fun (i, ()) mfi => ∃ hpf psf : List (BitVec 32),
                i.toNat ≤ 2 * stl.core.cur_vars ∧
                hpf.length = 2 * c.max_vars ∧ psf.length = 2 * c.max_vars ∧
                (FullMem c { stl with scratch :=
                  { stl.scratch with tarjan_mark := hpf, tarjan_reach := psf } } ⋆ R) mfi)
              (fun (i, _) _ => 2 * stl.core.cur_vars - i.toNat)
              (fun Jf hJf => by
                c0_hfast
                exact hJf (0#64, ()) ml ⟨stl.scratch.tarjan_mark, stl.scratch.tarjan_reach,
                  Nat.zero_le _, hscl.tarjan_mark_len, hscl.tarjan_reach_len, hml⟩)
              (fun Jf (i, ()) mfi ⟨hpf, psf, hi_le, hhpf_l, hpsf_l, hmfi⟩ ihf => ?_)
            c0_hsplit
            · have hi_lt : i.toNat < 2 * stl.core.cur_vars := by
                have h1 : i.toNat < (BitVec.ofNat 64 stl.core.cur_vars <<< (1 : Nat)).toNat := by
                  assumption
                rwa [h2cvl] at h1
              have hi1 : (i + 1#64).toNat = i.toNat + 1 := by simp only [bv_c0]; omega
              c0_hfast
              exact ihf (i + 1#64, ()) m (by dsimp only; rw [hi1]; omega)
                ⟨_, _, by rw [hi1]; omega, by simp [hhpf_l], by simp [hpsf_l], hm⟩
            · let st_f : FullState :=
                { stl with scratch := { stl.scratch with tarjan_mark := hpf, tarjan_reach := psf } }
              have hinv_f : FullDenseInv c F0 st_f :=
                fullDenseInv_set_fheap hwl.toDense hhpf_l hpsf_l
              c0_hsteps_nogrp
              refine wp_join_state0 (α := FullState)
                (fun stq mq => FullDenseInv c F0 stq ∧ stq.core.cur_vars = stl.core.cur_vars ∧
                  stq.core.fuel = stl.core.fuel ∧ (FullMem c stq ⋆ R) mq)
                (fun _ stq mq ⟨hinvq, hcvq, hfuelq, hmq⟩ => by
                  c0_hfast; exact hQ 1#64 stq mq hinvq (by omega) (hfuelq.trans hfuell) rfl hmq)
                (fun Jq hJq => ?_)
              c0_hsplit
              · have hqn_l := hscl.q_next_len; have hqs_l := hscl.q_stamp_len
                c0_hsteps_nogrp
                refine wp_loop_inv
                  (fun (qst, qidx, ()) mqi => ∃ qsi : List (BitVec 32),
                    qst.toNat ≤ stl.core.cur_vars ∧ qsi.length = c.max_vars ∧
                    (FullMem c { st_f with scratch := { st_f.scratch with q_stamp := qsi } } ⋆
                      R) mqi)
                  (fun (qst, _, _) _ => stl.core.cur_vars - qst.toNat)
                  (fun Jql hJql => by
                    c0_hfast
                    exact hJql (0#64, _, ()) mfi ⟨st_f.scratch.q_stamp, Nat.zero_le _, hqs_l, hmfi⟩)
                  (fun Jql (qst, qidx, ()) mqi ⟨qsi, hqst_le, hqsi_l, hmqi⟩ ihql => ?_)
                refine wp_join_state0 (α := Unit) (fun _ mx => mx = mqi)
                  (fun _ _ mx hmx => ?_) (fun Jqx hJqx => ?_)
                · subst mx
                  c0_hsteps_nogrp
                  refine wp_join_state0 (α := FullState)
                    (fun stq mq => FullDenseInv c F0 stq ∧ stq.core.cur_vars = stl.core.cur_vars ∧
                      stq.core.fuel = stl.core.fuel ∧ (FullMem c stq ⋆ R) mq)
                    (fun _ stq mq h => hJq stq mq h)
                    (fun Jql2 hJql2 => ?_)
                  c0_hsplit
                  · have hql_lt : st_f.scratch.q_last.toNat < stl.core.cur_vars := by
                      have h1 : st_f.scratch.q_last.toNat < stl.core.cur_vars % 2 ^ 64 := by
                        assumption
                      omega
                    have hql_qs : st_f.scratch.q_last.toNat < qsi.length := by omega
                    c0_hfast
                    let sc' : FullScratch :=
                      { st_f.scratch with
                        q_stamp := qsi, q_cur_stamp := qst,
                        q_search_idx := st_f.scratch.q_last,
                        q_search_stamp :=
                          BitVec.setWidth 64 (qsi[st_f.scratch.q_last.toNat]'hql_qs) }
                    exact hJql2 _ m
                      ⟨(fullDenseInv_with_core_aux (tc' := stl.core.tmp_cnt)
                          (tl' := stl.core.tmp_len) (sc' := sc')
                          hwl hcll.repr_len hcll.min_clr_len_arr hcll.tmp_len_arr hcll.flags_len
                          hcll.tmp_len_le
                          { hscl with tarjan_mark_len := hhpf_l, tarjan_reach_len := hpsf_l,
                                      q_stamp_len := hqsi_l } rfl rfl).toDense,
                       rfl, rfl, hm⟩
                  · c0_hfast
                    exact hJql2 _ m
                      ⟨(fullDenseInv_with_core_aux (tc' := stl.core.tmp_cnt)
                          (tl' := stl.core.tmp_len)
                          (sc' := { st_f.scratch with q_stamp := qsi, q_cur_stamp := qst })
                          hwl hcll.repr_len hcll.min_clr_len_arr hcll.tmp_len_arr hcll.flags_len
                          hcll.tmp_len_le
                          { hscl with tarjan_mark_len := hhpf_l, tarjan_reach_len := hpsf_l,
                                      q_stamp_len := hqsi_l } rfl rfl).toDense,
                       rfl, rfl, hm⟩
                · c0_hsplit
                  · c0_hsplit
                    · have hqidx_lt : qidx.toNat < stl.core.cur_vars := by
                        have h1 : qidx.toNat < stl.core.cur_vars % 2 ^ 64 := by assumption
                        omega
                      have hqst_lt : qst.toNat < stl.core.cur_vars := by
                        have h1 : qst.toNat < stl.core.cur_vars % 2 ^ 64 := by assumption
                        omega
                      have hqst1 : (qst + 1#64).toNat = qst.toNat + 1 := by simp only [bv_c0]; omega
                      have hqi_qs : qidx.toNat < qsi.length := by omega
                      have hqi_qn : qidx.toNat < st_f.scratch.q_next.length := by
                        dsimp only [st_f]; omega
                      c0_hfast
                      exact ihql (qst + 1#64, _, ()) m (by dsimp only; rw [hqst1]; omega)
                        ⟨_, by rw [hqst1]; omega, by simp [hqsi_l], hm⟩
                    · c0_hfast; exact hJqx () mqi rfl
                  · c0_hfast; exact hJqx () mqi rfl
              · c0_hfast; exact hJq st_f mfi ⟨hinv_f, rfl, rfl, hmfi⟩
          · c0_hsplit
            · c0_hsplit
              · c0_hsplit
                · c0_hsplit
                  · -- Body of main loop: pop `f0 = hp[0]`, sift down, check & `try_lit`
                    have hhl_pos : 0 < hlen.toNat := by
                      have h1 : (0 : BitVec 32).toNat < hlen.toNat := by assumption
                      exact h1
                    have hcv_lt_l : stl.core.cur_vars < c.max_vars := by
                      have h1 : stl.core.cur_vars % 2 ^ 64 < c.max_vars % 2 ^ 64 := by assumption
                      omega
                    have hbud_pos : 0 < budget.toNat := by
                      have h1 : (0 : BitVec 64).toNat < budget.toNat := by assumption
                      exact h1
                    have hhl1 : (hlen - 1#32).toNat = hlen.toNat - 1 := by
                      simp only [BitVec.toNat_sub_of_le
                          (show (1#32).toNat ≤ hlen.toNat from hhl_pos),
                        show (1#32).toNat = 1 from rfl]
                    have hbud1 : (budget - 1#64).toNat = budget.toNat - 1 := by
                      simp only [BitVec.toNat_sub_of_le
                          (show (1#64).toNat ≤ budget.toNat from hbud_pos),
                        show (1#64).toNat = 1 from rfl]
                    have hf0_lt : (stl.scratch.tarjan_mark[0]'(by
                        rw [hscl.tarjan_mark_len]; omega)).toNat < 2 * stl.core.cur_vars := by
                      have := hhp_ok 0 hhl_pos
                      rwa [List.getElem?_eq_getElem (by rw [hscl.tarjan_mark_len]; omega),
                        Option.getD_some] at this
                    have htm_l := hscl.tarjan_mark_len; have htr_l := hscl.tarjan_reach_len
                    have hhp0_lt : (BitVec.ofNat 64 0).toNat < stl.scratch.tarjan_mark.length := by
                      simp only [BitVec.toNat_ofNat]; rw [htm_l]; omega
                    let f0 := stl.scratch.tarjan_mark[0]'(by rw [htm_l]; omega)
                    have hf0_ps : (BitVec.setWidth 64 f0).toNat <
                        stl.scratch.tarjan_reach.length := by
                      dsimp only [f0]; rw [bv64_setWidth_32, htr_l]; omega
                    c0_hsteps_nogrp
                    -- Join point `Jpop` after optional `if (hlen > 0u) { ... full_fheap_down ... }`
                    refine wp_join_state0 (α := List (BitVec 32) × List (BitVec 32))
                      (fun ⟨hp1, ps1⟩ m1 =>
                        (FullMem c { stl with scratch :=
                          { stl.scratch with tarjan_mark := hp1, tarjan_reach := ps1 } } ⋆ R) m1 ∧
                        hp1.length = 2 * c.max_vars ∧ ps1.length = 2 * c.max_vars ∧
                        (∀ k < (hlen - 1#32).toNat,
                          (hp1[k]?.getD 0#32).toNat < 2 * stl.core.cur_vars))
                      (fun _ ⟨hp1, ps1⟩ m1 ⟨hm1, hhp1_l, hps1_l, hhp1_ok⟩ => ?_)
                      (fun Jpop hJpop => ?_)
                    · -- After pop: compute `fbit`, check active/flag/vals, maybe `full_bva_try_lit`
                      let st1 : FullState :=
                        { stl with scratch :=
                          { stl.scratch with tarjan_mark := hp1, tarjan_reach := ps1 } }
                      have hinv1 : FullDenseInv c F0 st1 :=
                        fullDenseInv_set_fheap hwl.toDense hhp1_l hps1_l
                      c0_hsteps_nogrp
                      refine wp_join_state1 (t := i32) (α := BitVec 32) (fun b => b)
                        (fun _ mf => mf = m1)
                        (fun _ fbit mf hmf => ?_)
                        (fun Jfb hJfb => ?_)
                      · subst mf
                        have hfv_lt_sw : (BitVec.setWidth 64 (f0 >>> (1 : Nat))).toNat <
                            stl.core.flags.length := by
                          dsimp only [f0]
                          rw [bv64_setWidth_32, hcll.flags_len, bv32_lshr1_nat]; omega
                        have hf0_v : (BitVec.setWidth 64 f0).toNat < stl.core.vals.length := by
                          dsimp only [f0]; rw [hcll.vals_len, bv64_setWidth_32]; omega
                        c0_hfast
                        · -- `continue` (`active == 0`)
                          exact ihm (budget, hlen - 1#32, ()) m1 (by dsimp only; rw [hhl1]; omega)
                            ⟨st1, hm1, hinv1, hcv_ge, hfuell, by rw [hhl1]; omega, hhp1_ok⟩
                        · -- `continue` (`fbit == 0`)
                          exact ihm (budget, hlen - 1#32, ()) m1 (by dsimp only; rw [hhl1]; omega)
                            ⟨st1, hm1, hinv1, hcv_ge, hfuell, by rw [hhl1]; omega, hhp1_ok⟩
                        · -- `continue` (`vals[f0] != 0`)
                          exact ihm (budget, hlen - 1#32, ()) m1 (by dsimp only; rw [hhl1]; omega)
                            ⟨st1, hm1, hinv1, hcv_ge, hfuell, by rw [hhl1]; omega, hhp1_ok⟩
                        · -- Clear `fbit`, `budget--`, call `full_bva_try_lit(h, f0, before_cv)`
                          obtain ⟨st2, hinv2, hcv2, hfuel2, htm2, htr2, hm2⟩ :=
                            extract_flags_upd hinv1 (by simp [hcll.flags_len]) hm
                          c0_call hTryLit
                          refine ⟨c, F0, st2, R, rfl, hinv2,
                            by rw [hcv2]; exact hf0_lt, hm2,
                            fun ok st3 m3 hinv3 hcv3 hfuel3 htm3 htr3 hm3 => ?_⟩
                          clear hm
                          obtain ⟨F_3, hw3⟩ := hinv3.exists_witness
                          have hcl3 := hw3.1.core_ok; have hsc3 := hw3.1.scratch_ok
                          have hcv3_le := hcl3.cur_vars_le; have hvals3_l := hcl3.vals_len
                          have hfl3_l := hcl3.flags_len; have hwv3_l := hcl3.wvec_len
                          have hhp3_ok : ∀ k < (hlen - 1#32).toNat,
                              (st3.scratch.tarjan_mark[k]?.getD 0#32).toNat <
                                2 * st3.core.cur_vars := by
                            intro k hk; rw [htm3, htm2]; have := hhp1_ok k hk
                            dsimp only [st1] at hcv2 ⊢; omega
                          c0_hsplit
                          · -- `try_lit == true`: re-insert active flagged literals
                            have h2cv3 : (BitVec.ofNat 64 st3.core.cur_vars <<< (1 : Nat)).toNat =
                                2 * st3.core.cur_vars := by
                              have := hcl3.cur_vars_le
                              rw [bv64_shl1_nat, BitVec.toNat_ofNat]; omega
                            c0_hsteps_nogrp
                            refine wp_loop_inv
                              (fun (hlc, ci, ()) mc => ∃ hpc psc : List (BitVec 32),
                                ci.toNat ≤ 2 * st3.core.cur_vars ∧ hlc.toNat ≤ 2 * c.max_vars ∧
                                hpc.length = 2 * c.max_vars ∧ psc.length = 2 * c.max_vars ∧
                                (∀ k < hlc.toNat,
                                  (hpc[k]?.getD 0#32).toNat < 2 * st3.core.cur_vars) ∧
                                (FullMem c { st3 with scratch :=
                                  { st3.scratch with tarjan_mark := hpc,
                                                     tarjan_reach := psc } } ⋆ R) mc)
                              (fun (_, ci, _) _ => 2 * st3.core.cur_vars - ci.toNat)
                              (fun Jci hJci => by
                                c0_hfast
                                exact hJci (hlen - 1#32, 0#64, ()) m3
                                  ⟨st3.scratch.tarjan_mark, st3.scratch.tarjan_reach, Nat.zero_le _,
                                   by rw [hhl1]; omega, hsc3.tarjan_mark_len, hsc3.tarjan_reach_len,
                                   hhp3_ok, hm3⟩)
                              (fun Jci (hlc, ci, ()) mc
                                  ⟨hpc, psc, hci_le, hhlc_le, hhpc_l, hpsc_l, hhpc_ok, hmc⟩
                                  ihci => ?_)
                            have hExit : wp Γ Q X (Expr.jump J (Arg.var hlc, ())) mc := by
                              c0_hfast
                              exact ihm (budget - 1#64, hlc, ()) mc
                                (by dsimp only; rw [hbud1]
                                    have hm1 : (budget.toNat - 1) * (2 * c.max_vars + 1) +
                                        (2 * c.max_vars + 1) =
                                        budget.toNat * (2 * c.max_vars + 1) := by
                                      rw [← Nat.add_one_mul, Nat.sub_add_cancel (by omega)]
                                    omega)
                                ⟨{ st3 with scratch :=
                                    { st3.scratch with tarjan_mark := hpc, tarjan_reach := psc } },
                                 hmc, fullDenseInv_set_fheap hw3.toDense hhpc_l hpsc_l,
                                 by dsimp only [st1] at hcv2 ⊢; omega,
                                 hfuel3.trans (hfuel2.trans hfuell), hhlc_le, hhpc_ok⟩
                            c0_hsplit
                            · c0_hsplit
                              · have hci_lt : ci.toNat < 2 * st3.core.cur_vars := by
                                  have h1 : ci.toNat <
                                      (BitVec.ofNat 64 st3.core.cur_vars <<< (1 : Nat)).toNat :=
                                    by assumption
                                  rwa [h2cv3] at h1
                                have hhlc_lt : hlc.toNat < 2 * c.max_vars := by
                                  have h1 : (BitVec.setWidth 64 hlc).toNat <
                                      (BitVec.ofNat 64 c.max_vars <<< (1 : Nat)).toNat := by
                                    assumption
                                  rwa [bv64_setWidth_32, hmx2] at h1
                                have hci1 : (ci + 1#64).toNat = ci.toNat + 1 := by
                                  simp only [bv_c0]; omega
                                have hhlc1 : (hlc + 1#32).toNat = hlc.toNat + 1 := by
                                  simp only [bv_c0]; omega
                                c0_hsteps_nogrp
                                refine wp_join_state1 (t := i32) (α := BitVec 32) (fun b => b)
                                  (fun _ mcb => mcb = mc)
                                  (fun _ cbit mcb hmcb => ?_)
                                  (fun Jcb hJcb => ?_)
                                · subst mcb
                                  have hcvi_lt : (BitVec.setWidth 64
                                      (BitVec.setWidth 32 (ci >>> (1 : Nat)))).toNat <
                                      st3.core.flags.length := by
                                    rw [bv64_setWidth_32, hcl3.flags_len]
                                    have := hcl3.cur_vars_le
                                    simp only [BitVec.toNat_setWidth, bv64_lshr1_nat]; omega
                                  have hwv_ci : ((ci <<< (1 : Nat)) + 1).toNat <
                                      st3.core.wvec.length := by
                                    change ((ci <<< (1 : Nat)) + 1#64).toNat < _
                                    rw [hcl3.wvec_len, BitVec.toNat_add, bv64_shl1_nat,
                                      show (1#64).toNat = 1 from rfl]
                                    have := hcl3.cur_vars_le; omega
                                  have hhlc_hp : (BitVec.setWidth 64 hlc).toNat < hpc.length := by
                                    rw [bv64_setWidth_32, hhpc_l]; exact hhlc_lt
                                  have hci_ps : ci.toNat < psc.length := by omega
                                  have hci_vals : ci.toNat < st3.core.vals.length := by omega
                                  c0_hfast
                                  · -- Insert `ci` into heap and call `full_fheap_up`
                                    have hci32_nat : (BitVec.setWidth 32 ci).toNat = ci.toNat :=
                                      by have := hcl3.cur_vars_le
                                         simp only [BitVec.toNat_setWidth]; omega
                                    let hpca := hpc.set hlc.toNat (BitVec.setWidth 32 ci)
                                    let psca := psc.set ci.toNat hlc
                                    have hmca : (FullMem c { st3 with scratch :=
                                        { st3.scratch with tarjan_mark := hpca,
                                                           tarjan_reach := psca } } ⋆ R) m := by
                                      simp only [hpca, psca, bv64_setWidth_32] at hm ⊢; exact hm
                                    c0_call hUp
                                    refine ⟨2 * c.max_vars, hpca, psca, st3.core.wvec,
                                      FullMemFheapRest c st3 ⋆ R,
                                      by simp [hpca, hhpc_l], by simp [psca, hpsc_l],
                                      by rw [hcl3.wvec_len]; omega, hnl_lt, hhlc_lt,
                                      fun i hi => by
                                        dsimp only [hpca]
                                        by_cases hie : i = hlc.toNat
                                        · subst hie
                                          rw [List.getElem?_set_self (by omega), Option.getD_some,
                                            hci32_nat]
                                          have := hcl3.cur_vars_le; omega
                                        · rw [List.getElem?_set_ne (Ne.symm hie)]
                                          have := hhpc_ok i (by omega)
                                          have := hcl3.cur_vars_le; omega,
                                      focus_fheap hmca,
                                      fun hpc' psc' mc' hhpc'_l hpsc'_l hsubc _ hmc' => ?_⟩
                                    c0_hfast
                                    refine ihci (hlc + 1#32, ci + 1#64, ()) mc'
                                      (by dsimp only; rw [hci1]; omega)
                                      ⟨hpc', psc', by rw [hci1]; omega, by rw [hhlc1]; omega,
                                       by simp [hpca, hhpc_l] at hhpc'_l; exact hhpc'_l,
                                       by simp [psca, hpsc_l] at hpsc'_l; exact hpsc'_l,
                                       fun k hk => ?_, unfocus_fheap hmc'⟩
                                    rw [hhlc1] at hk
                                    obtain ⟨j, hj, heq⟩ := hsubc k (by omega)
                                    rw [heq]; dsimp only [hpca]
                                    by_cases hje : j = hlc.toNat
                                    · subst hje
                                      rw [List.getElem?_set_self (by omega), Option.getD_some,
                                        hci32_nat]; exact hci_lt
                                    · rw [List.getElem?_set_ne (Ne.symm hje)]
                                      exact hhpc_ok j (by omega)
                                  all_goals
                                    exact ihci (hlc, ci + 1#64, ()) mc
                                      (by dsimp only; rw [hci1]; omega)
                                      ⟨hpc, psc, by rw [hci1]; omega, hhlc_le, hhpc_l, hpsc_l,
                                       hhpc_ok, hmc⟩
                                · c0_hfast
                                  · exact hJcb 64#32 mc rfl
                                  · exact hJcb 32#32 mc rfl
                              · exact hExit
                            · exact hExit
                          · -- `try_lit == false`
                            c0_hfast
                            exact ihm (budget - 1#64, hlen - 1#32, ()) m3
                              (by dsimp only; rw [hbud1, hhl1]
                                  have hm1 : (budget.toNat - 1) * (2 * c.max_vars + 1) +
                                      (2 * c.max_vars + 1) =
                                      budget.toNat * (2 * c.max_vars + 1) := by
                                    rw [← Nat.add_one_mul, Nat.sub_add_cancel (by omega)]
                                  omega)
                              ⟨st3, hm3, hw3.toDense, by dsimp only [st1] at hcv2; omega,
                               hfuel3.trans (hfuel2.trans hfuell), by rw [hhl1]; omega, hhp3_ok⟩
                      · c0_hfast
                        · exact hJfb 64#32 m1 rfl
                        · exact hJfb 32#32 m1 rfl
                    · -- `if (hlen > 0u)` sift-down branch
                      c0_hsplit
                      · have hhl_gt1 : 0 < (hlen - 1#32).toNat := by
                          have h1 : (0 : BitVec 32).toNat < (hlen - 1#32).toNat := by assumption
                          exact h1
                        have hhl1_hp : (BitVec.setWidth 64 (hlen - 1#32)).toNat <
                            stl.scratch.tarjan_mark.length := by
                          rw [bv64_setWidth_32, htm_l, hhl1]; omega
                        have htop_lt : (stl.scratch.tarjan_mark[(hlen - 1#32).toNat]'(by
                            rw [htm_l]; omega)).toNat < 2 * stl.core.cur_vars := by
                          have := hhp_ok (hlen - 1#32).toNat (by omega)
                          rwa [List.getElem?_eq_getElem (by rw [htm_l]; omega),
                            Option.getD_some] at this
                        let hp_s := stl.scratch.tarjan_mark.set 0
                          (stl.scratch.tarjan_mark[(hlen - 1#32).toNat]'(by rw [htm_l]; omega))
                        let ps_s := (stl.scratch.tarjan_reach.set f0.toNat 0xFFFFFFFF#32).set
                          (stl.scratch.tarjan_mark[(hlen - 1#32).toNat]'(by
                            rw [htm_l]; omega)).toNat 0#32
                        have hhp0_s : (BitVec.ofNat 64 0).toNat <
                            (stl.scratch.tarjan_mark.set (BitVec.ofNat 64 0).toNat
                              (stl.scratch.tarjan_mark[(BitVec.setWidth 64
                                (hlen - 1#32)).toNat]'hhl1_hp)).length := by
                          simp [htm_l]; omega
                        have hhl1' : (hlen - (1 : BitVec 32)).toNat = hlen.toNat - 1 := hhl1
                        have htop_b : (BitVec.setWidth 64
                            ((stl.scratch.tarjan_mark.set (BitVec.ofNat 64 0).toNat
                              (stl.scratch.tarjan_mark[(BitVec.setWidth 64
                                (hlen - 1#32)).toNat]'hhl1_hp))[(BitVec.ofNat 64 0).toNat]'hhp0_s)
                            ).toNat <
                            (stl.scratch.tarjan_reach.set (BitVec.setWidth 64 f0).toNat
                              0xFFFFFFFF#32).length := by
                          rw [bv64_setWidth_32, List.length_set, htr_l,
                            List.getElem_set_self hhp0_s]
                          simp only [bv64_setWidth_32]; omega
                        c0_hfast
                        have hm_s : (FullMem c { stl with scratch :=
                            { stl.scratch with tarjan_mark := hp_s,
                                               tarjan_reach := ps_s } } ⋆ R) m := by
                          simp only [hp_s, ps_s, f0, bv64_setWidth_32,
                            show (0#64).toNat = 0 from rfl,
                            show (1 : BitVec 32) = 1#32 from rfl,
                            show (0 : BitVec 32) = 0#32 from rfl,
                            show (4294967295 : BitVec 32) = 0xFFFFFFFF#32 from rfl] at hm ⊢
                          rw [List.getElem_set_self (by simp [htm_l]; omega)] at hm
                          exact hm
                        c0_call hDown
                        refine ⟨2 * c.max_vars, hp_s, ps_s, stl.core.wvec,
                          FullMemFheapRest c stl ⋆ R,
                          by simp [hp_s, htm_l],
                          by simp [ps_s, htr_l],
                          by rw [hcll.wvec_len]; omega, hnl_lt, by simpa using hhl_gt1, by omega,
                          fun i hi => by
                            dsimp only [hp_s]
                            by_cases hi0 : i = 0
                            · subst hi0
                              rw [List.getElem?_set_self (by rw [htm_l]; omega),
                                Option.getD_some]; omega
                            · rw [List.getElem?_set_ne (Ne.symm hi0)]
                              have := hhp_ok i (by omega); omega,
                          focus_fheap hm_s,
                          fun hp1 ps1 m1 hhp1_l hps1_l hsub1 _ hm1 => ?_⟩
                        c0_hfast
                        refine hJpop ⟨hp1, ps1⟩ m1 ⟨unfocus_fheap hm1,
                          by simp [hp_s, htm_l] at hhp1_l; exact hhp1_l,
                          by simp [ps_s, htr_l] at hps1_l; exact hps1_l,
                          fun k hk => ?_⟩
                        obtain ⟨j, hj, heq⟩ := hsub1 k hk
                        rw [heq]; dsimp only [hp_s]
                        by_cases hj0 : j = 0
                        · subst hj0
                          rw [List.getElem?_set_self (by rw [htm_l]; omega),
                            Option.getD_some]; exact htop_lt
                        · rw [List.getElem?_set_ne (Ne.symm hj0)]; exact hhp_ok j (by omega)
                      · c0_hfast
                        exact hJpop ⟨stl.scratch.tarjan_mark,
                            stl.scratch.tarjan_reach.set f0.toNat 0xFFFFFFFF#32⟩ m
                          ⟨by simp only [f0, bv64_setWidth_32] at hm ⊢; exact hm,
                           htm_l, by simp [htr_l],
                           fun k hk => by
                             have h1 : ¬ (0 : BitVec 32).toNat < (hlen - 1#32).toNat := by
                               assumption
                             change ¬ 0 < (hlen - 1#32).toNat at h1; omega⟩
                  · c0_hfast; exact hJmain () ml rfl
                · c0_hfast; exact hJmain () ml rfl
              · c0_hfast; exact hJmain () ml rfl
            · c0_hfast; exact hJmain () ml rfl


end LeanQbe.T.Examples.Kissat.FullBvaHeap
