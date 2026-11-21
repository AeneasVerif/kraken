module

public import LeanQbe.T.Examples.Kissat.FullBvaHeapLemmas4
public import LeanQbe.T.Examples.Kissat.FullBvaHeapLemmas5
public import LeanQbe.T.Examples.Kissat.FullDeduce1UipNv
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Full` 3-Hop BVA & Max-Degree Binary Heap Factoring — Top Proofs & Non-Vacuity

Re-exports per-function `Func.wp` proofs from `FullBvaHeapLemmas{1..5}`, and completes:
1. `full_factor_wp` (`fullFactorHeapSpec`): max-degree binary heap factoring driver
   (`full_fheap_up`, `full_fheap_down`, `full_bva_try_lit`) with lexicographic termination measure.
2. `bvaHeapSpecTable`, `bvaHeapEnv`, and `bvaHeap_moduleOk : ModuleOk bvaHeapEnv bvaHeapModule`
   against canonical `FullSpec2`/`FullSpec3` external contracts.
3. Concrete `Mem 64` UNSAT non-vacuity (`XPost := fun _ _ _ _ => False`, zero SAT proofs).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullBvaHeap

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.C0Step
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test
open FullBvaHeapTactics
open FullBvaHeapHelpers
open FullBvaHeapScanHelpers
open scoped FullArenaTactics FullBvaHeapTactics

/-! ## 4. Max-Degree Binary Heap Factoring Driver (`full_factor_wp`) -/

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
            · c0_hfast
              exact hQ 1#64 _ mfi (fullDenseInv_set_fheap hwl.toDense hhpf_l hpsf_l) hcv_ge hfuell
                rfl hmfi
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

/-! ## 5. Closed `bvaHeapEnv` & `bvaHeap_moduleOk` -/

/-- Specification table matching `bvaHeap_fns` (`13` rows) plus the `6` canonical `Full` externs
(`full_alloc_cl`, `full_wstack_defrag`, `full_watch_push`, `full_unwatch_large`, `full_add_bin`,
`full_delete_binary`). -/
def bvaHeapSpecTable : List SpecEntry :=
  [ ⟨"full_init_fresh_var", [i64, i32], [], fullInitFreshVarHeapSpec, true⟩
  , ⟨"full_bva_hop1", [i64, i32, i32], [i64], fullBvaHop1Spec, true⟩
  , ⟨"full_bva_hop2", [i64, i32, i32], [i64], fullBvaHop2Spec, true⟩
  , ⟨"full_bva_hop3", [i64, i32, i32], [i64], fullBvaHop3Spec, true⟩
  , ⟨"full_bva_match_large", [i64, i32, i32, i32], [.bool], fullBvaMatchLargeSpec, true⟩
  , ⟨"full_bva_scan_cands", [i64, i32, i32, i64], [i32], fullBvaScanCandsSpec, true⟩
  , ⟨"full_bva_pick_cand", [i64, i32, i32], [i32], fullBvaPickCandSpec, true⟩
  , ⟨"full_bva_filter_row", [i64, i32, i32, i32, i32, i32], [i32], fullBvaFilterRowSpec, true⟩
  , ⟨"full_bva_commit", [i64, i32], [.bool], fullBvaCommitSpec, true⟩
  , ⟨"full_bva_try_lit", [i64, i32, i64], [.bool], fullBvaTryLitHeapSpec, true⟩
  , ⟨"full_fheap_up", [i64, i64, i64, i32], [], fullFheapUpSpec, true⟩
  , ⟨"full_fheap_down", [i64, i64, i64, i32, i32], [], fullFheapDownSpec, true⟩
  , ⟨"full_factor", [i64, i64], [i64], fullFactorHeapSpec, true⟩
  , ⟨"full_alloc_cl", [i64, i32, i32, .bool], [i64], fullAllocClSpec, true⟩
  , ⟨"full_wstack_defrag", [i64], [], fullWstackDefragSpec, true⟩
  , ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool], fullWatchPushSpec, true⟩
  , ⟨"full_unwatch_large", [i64, i32, i32], [], fullUnwatchLargeSpec, true⟩
  , ⟨"full_add_bin", [i64, i32, i32], [i64], fullAddBinSpec, true⟩
  , ⟨"full_delete_binary", [i64, i32, i32], [], fullDeleteBinarySpec, true⟩
  ]

/-- Closed specification environment for `bvaHeapModule`. -/
def bvaHeapEnv : Env := Env.ofTable bvaHeapSpecTable

theorem bvaHeapSpecTable_names_nodup : (bvaHeapSpecTable.map SpecEntry.name).Nodup := by
  decide

theorem bvaHeapSpecTable_noExit : ∀ e ∈ bvaHeapSpecTable, e.noExit = true := by
  intro e he
  have hall : bvaHeapSpecTable.all (fun x => x.noExit) = true := by t_kernel_rfl
  exact List.all_eq_true.mp hall e he

theorem bvaHeapEnv_noExit :
    ∀ f as bs xs m Q X X', bvaHeapEnv f as bs xs m Q X → bvaHeapEnv f as bs xs m Q X' :=
  Env.ofTable_noExit bvaHeapSpecTable_noExit

private theorem bvaHeapEnv_mem {e : SpecEntry} (he : e ∈ bvaHeapSpecTable)
    {xs : Tup Val e.as} {m : Mem 64} {Q : Post e.rs} {X : XPost}
    (h : e.spec xs m Q (fun _ _ _ _ => False)) : bvaHeapEnv e.name e.as e.rs xs m Q X := by
  have hno := bvaHeapSpecTable_noExit e he
  exact Env.ofTable_of_mem he bvaHeapSpecTable_names_nodup
    (by simp only [SpecEntry.eff, hno, ↓reduceIte]; exact h)

private theorem bvaHeap_allFns_wf : AllFns Fn.Wf bvaHeapModule.fns :=
  ⟨full_init_fresh_var_wf, full_bva_hop1_wf, full_bva_hop2_wf, full_bva_hop3_wf,
   full_bva_match_large_wf, full_bva_scan_cands_wf, full_bva_pick_cand_wf,
   full_bva_filter_row_wf, full_bva_commit_wf, full_bva_try_lit_wf,
   full_fheap_up_wf, full_fheap_down_wf, full_factor_wf, trivial⟩

/-- Closed `ModuleOk` theorem for all `13` 3-hop BVA & binary-heap factoring functions in
`bvaHeapModule`, parameterized over `full_bva_commit_wp`. -/
theorem bvaHeap_moduleOk_of_commit
    (hCommitWp : ∀ (Γ : Env),
      (∀ xs m Q X, fullWstackDefragSpec xs m Q X → Γ "full_wstack_defrag" [i64] [] xs m Q X) →
      (∀ xs m Q X, fullInitFreshVarHeapSpec xs m Q X →
        Γ "full_init_fresh_var" [i64, i32] [] xs m Q X) →
      (∀ xs m Q X, fullAddBinSpec xs m Q X → Γ "full_add_bin" [i64, i32, i32] [i64] xs m Q X) →
      (∀ xs m Q X, fullAllocClSpec xs m Q X →
        Γ "full_alloc_cl" [i64, i32, i32, .bool] [i64] xs m Q X) →
      (∀ xs m Q X, fullWatchPushSpec xs m Q X →
        Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] xs m Q X) →
      (∀ xs m Q X, fullDeleteBinarySpec xs m Q X →
        Γ "full_delete_binary" [i64, i32, i32] [] xs m Q X) →
      (∀ xs m Q X, fullUnwatchLargeSpec xs m Q X →
        Γ "full_unwatch_large" [i64, i32, i32] [] xs m Q X) →
      ∀ xs m Q X, fullBvaCommitSpec xs m Q X →
        Func.wp Γ full_bva_commit_body xs m Q X) :
    ModuleOk bvaHeapEnv bvaHeapModule := by
  refine Env.ofTable_moduleOk bvaHeap_acyclic bvaHeap_allFns_wf ?_
  have hInit : ∀ xs m Q X, fullInitFreshVarHeapSpec xs m Q X →
      bvaHeapEnv "full_init_fresh_var" [i64, i32] [] xs m Q X :=
    fun _ _ _ _ h => bvaHeapEnv_mem (e := ⟨"full_init_fresh_var", [i64, i32], [],
      fullInitFreshVarHeapSpec, true⟩) (by simp [bvaHeapSpecTable]) h
  have hHop1 : ∀ xs m Q X, fullBvaHop1Spec xs m Q X →
      bvaHeapEnv "full_bva_hop1" [i64, i32, i32] [i64] xs m Q X :=
    fun _ _ _ _ h => bvaHeapEnv_mem (e := ⟨"full_bva_hop1", [i64, i32, i32], [i64],
      fullBvaHop1Spec, true⟩) (by simp [bvaHeapSpecTable]) h
  have hHop2 : ∀ xs m Q X, fullBvaHop2Spec xs m Q X →
      bvaHeapEnv "full_bva_hop2" [i64, i32, i32] [i64] xs m Q X :=
    fun _ _ _ _ h => bvaHeapEnv_mem (e := ⟨"full_bva_hop2", [i64, i32, i32], [i64],
      fullBvaHop2Spec, true⟩) (by simp [bvaHeapSpecTable]) h
  have hHop3 : ∀ xs m Q X, fullBvaHop3Spec xs m Q X →
      bvaHeapEnv "full_bva_hop3" [i64, i32, i32] [i64] xs m Q X :=
    fun _ _ _ _ h => bvaHeapEnv_mem (e := ⟨"full_bva_hop3", [i64, i32, i32], [i64],
      fullBvaHop3Spec, true⟩) (by simp [bvaHeapSpecTable]) h
  have hMatch : ∀ xs m Q X, fullBvaMatchLargeSpec xs m Q X →
      bvaHeapEnv "full_bva_match_large" [i64, i32, i32, i32] [.bool] xs m Q X :=
    fun _ _ _ _ h => bvaHeapEnv_mem (e := ⟨"full_bva_match_large", [i64, i32, i32, i32], [.bool],
      fullBvaMatchLargeSpec, true⟩) (by simp [bvaHeapSpecTable]) h
  have hScan : ∀ xs m Q X, fullBvaScanCandsSpec xs m Q X →
      bvaHeapEnv "full_bva_scan_cands" [i64, i32, i32, i64] [i32] xs m Q X :=
    fun _ _ _ _ h => bvaHeapEnv_mem (e := ⟨"full_bva_scan_cands", [i64, i32, i32, i64], [i32],
      fullBvaScanCandsSpec, true⟩) (by simp [bvaHeapSpecTable]) h
  have hPick : ∀ xs m Q X, fullBvaPickCandSpec xs m Q X →
      bvaHeapEnv "full_bva_pick_cand" [i64, i32, i32] [i32] xs m Q X :=
    fun _ _ _ _ h => bvaHeapEnv_mem (e := ⟨"full_bva_pick_cand", [i64, i32, i32], [i32],
      fullBvaPickCandSpec, true⟩) (by simp [bvaHeapSpecTable]) h
  have hFilter : ∀ xs m Q X, fullBvaFilterRowSpec xs m Q X →
      bvaHeapEnv "full_bva_filter_row" [i64, i32, i32, i32, i32, i32] [i32] xs m Q X :=
    fun _ _ _ _ h => bvaHeapEnv_mem (e := ⟨"full_bva_filter_row", [i64, i32, i32, i32, i32, i32],
      [i32], fullBvaFilterRowSpec, true⟩) (by simp [bvaHeapSpecTable]) h
  have hCommit : ∀ xs m Q X, fullBvaCommitSpec xs m Q X →
      bvaHeapEnv "full_bva_commit" [i64, i32] [.bool] xs m Q X :=
    fun _ _ _ _ h => bvaHeapEnv_mem (e := ⟨"full_bva_commit", [i64, i32], [.bool],
      fullBvaCommitSpec, true⟩) (by simp [bvaHeapSpecTable]) h
  have hTryLit : ∀ xs m Q X, fullBvaTryLitHeapSpec xs m Q X →
      bvaHeapEnv "full_bva_try_lit" [i64, i32, i64] [.bool] xs m Q X :=
    fun _ _ _ _ h => bvaHeapEnv_mem (e := ⟨"full_bva_try_lit", [i64, i32, i64], [.bool],
      fullBvaTryLitHeapSpec, true⟩) (by simp [bvaHeapSpecTable]) h
  have hUp : ∀ xs m Q X, fullFheapUpSpec xs m Q X →
      bvaHeapEnv "full_fheap_up" [i64, i64, i64, i32] [] xs m Q X :=
    fun _ _ _ _ h => bvaHeapEnv_mem (e := ⟨"full_fheap_up", [i64, i64, i64, i32], [],
      fullFheapUpSpec, true⟩) (by simp [bvaHeapSpecTable]) h
  have hDown : ∀ xs m Q X, fullFheapDownSpec xs m Q X →
      bvaHeapEnv "full_fheap_down" [i64, i64, i64, i32, i32] [] xs m Q X :=
    fun _ _ _ _ h => bvaHeapEnv_mem (e := ⟨"full_fheap_down", [i64, i64, i64, i32, i32], [],
      fullFheapDownSpec, true⟩) (by simp [bvaHeapSpecTable]) h
  have hAllocCl : ∀ xs m Q X, fullAllocClSpec xs m Q X →
      bvaHeapEnv "full_alloc_cl" [i64, i32, i32, .bool] [i64] xs m Q X :=
    fun _ _ _ _ h => bvaHeapEnv_mem (e := ⟨"full_alloc_cl", [i64, i32, i32, .bool], [i64],
      fullAllocClSpec, true⟩) (by simp [bvaHeapSpecTable]) h
  have hDefrag : ∀ xs m Q X, fullWstackDefragSpec xs m Q X →
      bvaHeapEnv "full_wstack_defrag" [i64] [] xs m Q X :=
    fun _ _ _ _ h => bvaHeapEnv_mem (e := ⟨"full_wstack_defrag", [i64], [],
      fullWstackDefragSpec, true⟩) (by simp [bvaHeapSpecTable]) h
  have hWPush : ∀ xs m Q X, fullWatchPushSpec xs m Q X →
      bvaHeapEnv "full_watch_push" [i64, i32, i32, i32, i32] [.bool] xs m Q X :=
    fun _ _ _ _ h => bvaHeapEnv_mem (e := ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool],
      fullWatchPushSpec, true⟩) (by simp [bvaHeapSpecTable]) h
  have hUnwatch : ∀ xs m Q X, fullUnwatchLargeSpec xs m Q X →
      bvaHeapEnv "full_unwatch_large" [i64, i32, i32] [] xs m Q X :=
    fun _ _ _ _ h => bvaHeapEnv_mem (e := ⟨"full_unwatch_large", [i64, i32, i32], [],
      fullUnwatchLargeSpec, true⟩) (by simp [bvaHeapSpecTable]) h
  have hAddBin : ∀ xs m Q X, fullAddBinSpec xs m Q X →
      bvaHeapEnv "full_add_bin" [i64, i32, i32] [i64] xs m Q X :=
    fun _ _ _ _ h => bvaHeapEnv_mem (e := ⟨"full_add_bin", [i64, i32, i32], [i64],
      fullAddBinSpec, true⟩) (by simp [bvaHeapSpecTable]) h
  have hDelBin : ∀ xs m Q X, fullDeleteBinarySpec xs m Q X →
      bvaHeapEnv "full_delete_binary" [i64, i32, i32] [] xs m Q X :=
    fun _ _ _ _ h => bvaHeapEnv_mem (e := ⟨"full_delete_binary", [i64, i32, i32], [],
      fullDeleteBinarySpec, true⟩) (by simp [bvaHeapSpecTable]) h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
  · exact SpecEntry.Impl.of (full_init_fresh_var_heap_wp bvaHeapEnv)
  · exact SpecEntry.Impl.of (full_bva_hop1_wp bvaHeapEnv)
  · exact SpecEntry.Impl.of (full_bva_hop2_wp bvaHeapEnv hHop1)
  · exact SpecEntry.Impl.of (full_bva_hop3_wp bvaHeapEnv hHop2)
  · exact SpecEntry.Impl.of (full_bva_match_large_wp bvaHeapEnv)
  · exact SpecEntry.Impl.of (full_bva_scan_cands_wp bvaHeapEnv)
  · exact SpecEntry.Impl.of (full_bva_pick_cand_wp bvaHeapEnv hHop3)
  · exact SpecEntry.Impl.of (full_bva_filter_row_wp bvaHeapEnv hMatch)
  · exact SpecEntry.Impl.of (hCommitWp bvaHeapEnv hDefrag hInit hAddBin hAllocCl
      hWPush hDelBin hUnwatch)
  · exact SpecEntry.Impl.of (full_bva_try_lit_wp bvaHeapEnv hScan hPick hFilter hCommit)
  · exact SpecEntry.Impl.of (full_fheap_up_wp bvaHeapEnv)
  · exact SpecEntry.Impl.of (full_fheap_down_wp bvaHeapEnv)
  · exact SpecEntry.Impl.of (full_factor_wp bvaHeapEnv hUp hDown hTryLit)

/-- Closed unconditional `ModuleOk` theorem for all `13` 3-hop BVA & binary-heap factoring
functions in `bvaHeapModule` against canonical `FullSpec2`/`FullSpec3` external contracts. -/
theorem bvaHeap_moduleOk : ModuleOk bvaHeapEnv bvaHeapModule :=
  bvaHeap_moduleOk_of_commit full_bva_commit_wp

/-! ## 6. Concrete `Mem 64` UNSAT Non-Vacuity (`XPost := False`, `0` SAT proofs) -/

section ConcreteUnsatNonVacuity

/-- Concrete dense-mode UNSAT state (`dense_mode = 1`, `inconsistent = 1`) on `nvOneLitCfg`
for the UNSAT formula `nvOneLitF0 = {(x0), (¬x0)}`. -/
def nvBvaDenseState : FullState :=
  { nvOneLitState with
    core := { nvOneLitState.core with dense_mode := 1#64, inconsistent := 1#64 } }

/-- Concrete `1756`-byte arena image encoding `nvOneLitCfg` and `nvBvaDenseState`. -/
def nvBvaDenseBytes : List UInt8 :=
  (bytes64 [1#64, 2#64, 0#64, 0#64] ++ bytes64 (Full.hdrTailWords nvOneLitCfg nvBvaDenseState)) ++
    nvBlockBytes ++ nvBlockU32A ++ nvBlockU32B ++ nvBlockU32C ++ nvBlockWvec ++ nvBlockTail

/-- Concrete `Mem 64` heap mapped at `nvOneLitCfg.hdr` (`0x1000#64`). -/
def nvBvaDenseMem : Mem 64 := nvBvaDenseBytes.At nvOneLitCfg.hdr

theorem nvBvaDenseBytes_length : nvBvaDenseBytes.length = 1756 := by
  simp only [nvBvaDenseBytes, nvBlockBytes, nvBlockU32A, nvBlockU32B, nvBlockU32C, nvBlockWvec,
    nvBlockTail, nvBvaDenseState, nvOneLitState, nvOneLitScratch, List.length_append,
    List.length_replicate, bytesOf_length, bytes64_length, Full.hdrTailWords_length,
    List.length_cons, List.length_nil]
  decide

private theorem array64_unique {a : BitVec 64} {xs : List (BitVec 64)} {m1 m2 : Mem 64}
    (h1 : array64 a xs m1) (h2 : array64 a xs m2) : m1 = m2 := by
  induction xs generalizing a m1 m2 with
  | nil => exact h1.trans h2.symm
  | cons x xs ih =>
    obtain ⟨p1, q1, rfl, _, hp1, hq1⟩ := h1
    obtain ⟨p2, q2, rfl, _, hp2, hq2⟩ := h2
    rw [hp1.symm.trans hp2, ih hq1 hq2]

private theorem union_cancel_left {m1 m2 m2' : Mem 64}
    (hu : m1.union m2 = m1.union m2') (hd1 : m1.inter m2 = ∅) (hd2 : m1.inter m2' = ∅) :
    m2 = m2' := by
  apply ExtHashMap.ext_getElem?; intro k
  have h1 := congrArg (·[k]?) hu; simp only [union_eq, getElem?_union] at h1
  have d1 := eq_empty_iff_forall_not_mem.mp hd1 k
  have d2 := eq_empty_iff_forall_not_mem.mp hd2 k
  simp only [inter_eq, mem_inter_iff] at d1 d2
  cases hm1 : m1[k]? with
  | none => simpa only [hm1, Option.or_none] using h1
  | some _ =>
    have hmem : k ∈ m1 := mem_iff_isSome_getElem?.mpr (by simp [hm1])
    have hn1 : m2[k]? = none := Option.eq_none_iff_forall_ne_some.mpr fun _ hv =>
      d1 ⟨hmem, mem_iff_isSome_getElem?.mpr (by simp [hv])⟩
    have hn2 : m2'[k]? = none := Option.eq_none_iff_forall_ne_some.mpr fun _ hv =>
      d2 ⟨hmem, mem_iff_isSome_getElem?.mpr (by simp [hv])⟩
    rw [hn1, hn2]

theorem nvBvaDenseMem_ok : FullMem nvOneLitCfg nvBvaDenseState nvBvaDenseMem := by
  let c := nvOneLitCfg; let s := nvBvaDenseState
  let bHdr0 := bytes64 [1#64, 2#64, 0#64, 0#64] ++ bytes64 (Full.hdrTailWords c nvOneLitState)
  let bHdr1 := bytes64 [1#64, 2#64, 0#64, 0#64] ++ bytes64 (Full.hdrTailWords c s)
  let bRest := nvBlockBytes ++ nvBlockU32A ++ nvBlockU32B ++ nvBlockU32C ++
    nvBlockWvec ++ nvBlockTail
  have hhdr_len0 : bHdr0.length = 1152 := by
    simp only [bHdr0, List.length_append, bytes64_length, Full.hdrTailWords_length]; decide
  have hrest_len : bRest.length = 604 := by
    simp only [bRest, nvBlockBytes, nvBlockU32A, nvBlockU32B, nvBlockU32C, nvBlockWvec,
      nvBlockTail, nvOneLitState, nvOneLitScratch, List.length_append, List.length_replicate,
      bytesOf_length, bytes64_length, List.length_cons, List.length_nil]
    decide
  have hHdr0 : bHdr0.length = 1152 ∧
      (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc)
        nvOneLitState.core.d_cur nvOneLitState.core.d_val ⋆
        array64 (c.hdr + 32) (Full.hdrTailWords c nvOneLitState)) (bHdr0.At c.hdr) :=
    nv_join_pair
      (nv_arr64_p (a := c.hdr) (xs := [1#64, 2#64, 0#64, 0#64]) 32 rfl (by decide))
      (nv_arr64_p (a := c.hdr + 32) (xs := Full.hdrTailWords c nvOneLitState) 1120
        (by rw [Full.hdrTailWords_length]) (by decide)) (by decide) (by decide)
  have hHdr1 : bHdr1.length = 1152 ∧
      (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc)
        s.core.d_cur s.core.d_val ⋆ array64 (c.hdr + 32) (Full.hdrTailWords c s))
        (bHdr1.At c.hdr) :=
    nv_join_pair
      (nv_arr64_p (a := c.hdr) (xs := [1#64, 2#64, 0#64, 0#64]) 32 rfl (by decide))
      (nv_arr64_p (a := c.hdr + 32) (xs := Full.hdrTailWords c s) 1120
        (by rw [Full.hdrTailWords_length]) (by decide)) (by decide) (by decide)
  have hmem0 : FullMem c nvOneLitState ((bHdr0 ++ bRest).At c.hdr) := by
    have h0 := nvOneLitMem_ok
    unfold nvOneLitMem nvOneLitBytes nvBlockHdr at h0
    simpa only [bHdr0, bRest, List.append_assoc] using h0
  have hsep0 : ((dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc)
        nvOneLitState.core.d_cur nvOneLitState.core.d_val ⋆
        array64 (c.hdr + 32) (Full.hdrTailWords c nvOneLitState)) ⋆
      (FullCoreArrays c nvOneLitState.core ⋆ FullScratchArrays c nvOneLitState.scratch ⋆ c.pad))
      ((bHdr0 ++ bRest).At c.hdr) := by
    unfold FullMem at hmem0; exact sep_ac hmem0
  have hEqRest : (FullCoreArrays c nvOneLitState.core ⋆
      FullScratchArrays c nvOneLitState.scratch ⋆ c.pad) (bRest.At (c.hdr + 1152#64)) := by
    have hsplit := congrFun (Mem.At_append_sep bHdr0 bRest c.hdr (by omega))
      ((bHdr0 ++ bRest).At c.hdr)
    have hm12 := hsplit.mp rfl
    obtain ⟨m1, m2, huni, hdisj, ⟨a1, b1, rfl, _, ha1, hb1⟩, hm2⟩ := hsep0
    obtain ⟨m1', m2', huni', hdisj', rfl, rfl⟩ := hm12
    obtain ⟨a0, b0, h0_eq, _, ha0, hb0⟩ := hHdr0.2
    have ha_eq : a1 = a0 := array64_unique (a := c.hdr) (xs := [1#64, 2#64, 0#64, 0#64]) ha1 ha0
    have hb_eq : b1 = b0 :=
      array64_unique (a := c.hdr + 32) (xs := Full.hdrTailWords c nvOneLitState) hb1 hb0
    have hm1_eq : a1.union b1 = bHdr0.At c.hdr := by rw [ha_eq, hb_eq, h0_eq]
    rw [hm1_eq] at huni hdisj
    have hm2_eq : m2 = bRest.At (c.hdr + BitVec.ofNat 64 bHdr0.length) :=
      union_cancel_left (huni.trans huni'.symm) hdisj hdisj'
    rw [hm2_eq, hhdr_len0] at hm2; exact hm2
  have hfin := nv_join_pair hHdr1 ⟨hrest_len, hEqRest⟩ (by decide) (by decide)
  have hfin' : FullMem c s ((bHdr1 ++ bRest).At c.hdr) := by
    unfold FullMem; exact sep_ac hfin.2
  simpa only [nvBvaDenseMem, nvBvaDenseBytes, bHdr1, bRest, List.append_assoc] using hfin'

theorem nvBvaDense_invW :
    FullDenseInvW nvOneLitCfg nvOneLitF0 [[0], [1]] nvBvaDenseState := by
  have hmv : nvOneLitCfg.max_vars = 1 := rfl
  have hcv : nvBvaDenseState.core.cur_vars = 1 := rfl
  have hte : nvBvaDenseState.core.trail_end = 1 := rfl
  have hcl : nvBvaDenseState.core.cur_level = 0 := rfl
  have hdm : nvBvaDenseState.core.dense_mode ≠ 0#64 := by decide
  have hrefs : fullArenaClauseRefsCore nvBvaDenseState.core = [] := rfl
  have hwat : ModeWatchesInv [[0], [1]] nvBvaDenseState.core := by
    unfold ModeWatchesInv; rw [ite_eq_right hdm]
    refine DenseWatchesInv.of_slices (fun l hl => ?_) (fun l hl hp => ?_)
      (fun l1 _ h1 _ _ hp => ?_) (fun l hl => ?_)
    · rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> decide
    · rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;>
        (simp [fullWatchSizeCore, nvBvaDenseState, nvOneLitState] at hp)
    · rw [hcv] at h1; rcases (by omega : l1 = 0 ∨ l1 = 1) with rfl | rfl <;>
        (simp [fullWatchSizeCore, nvBvaDenseState, nvOneLitState] at hp)
    · rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;>
        exact DenseWatchSliceOk.empty
  have hent0 : (cnfOfClauses [[0], [1]]).EntailsClause (cnfClause [0]) := by
    rw [CNF.entails_clause_def]; intro α hα
    exact (CNF.sat_iff_all_mem_sat.mp hα) _ (CNF.Internal.mem_iff.mpr (by simp [cnfOfClauses]))
  have hw : FullWitnessInv nvOneLitCfg nvOneLitF0 [[0], [1]] nvBvaDenseState.core :=
    { ext_sound := ⟨(varsBoundedBool_iff 1 [[0], [1]]).mp rfl, id⟩
      inconsistent_sound := fun _ => nvDeduceF0_unsat
      arena := ⟨Or.inl rfl, fun r hr => by simp [hrefs] at hr, fun r hr => by simp [hrefs] at hr,
        fun r hr => by simp [hrefs] at hr, fun r hr => by simp [hrefs] at hr⟩
      watches := hwat, cur_level_le := Nat.zero_le _
      trail_lits_lt := fun i hi => by rw [hte] at hi; obtain rfl : i = 0 := (by omega); decide
      trail_vars_nodup := fun i j hi hj _ => by rw [hte] at hi hj; omega
      vals_domain := fun l hl => by
        rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;>
          simp [nvBvaDenseState, nvOneLitState]
      vals_true_iff := fun l hl => by
        rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
        · exact ⟨fun _ => ⟨0, Nat.zero_lt_one, rfl⟩, fun _ => rfl⟩
        · exact ⟨(fun h => by cases h), (fun ⟨i, hi, h⟩ => by
            rw [hte] at hi; obtain rfl : i = 0 := (by omega); cases h)⟩
      vals_false_iff := fun l hl => by
        rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
        · exact ⟨(fun h => by cases h), (fun ⟨i, hi, h⟩ => by
            rw [hte] at hi; obtain rfl : i = 0 := (by omega); cases h)⟩
        · exact ⟨fun _ => ⟨0, Nat.zero_lt_one, rfl⟩, fun _ => rfl⟩
      lvl_le := fun i hi => by rw [hte] at hi; obtain rfl : i = 0 := (by omega); exact Nat.le_refl 0
      dec_earliest := fun _ j _ hj _ hpos => by
        rw [hte] at hj; obtain rfl : j = 0 := (by omega); exact absurd hpos.1 (by decide)
      levels_inhabited := fun _ _ h2 => by rw [hcl] at h2; omega
      level0_sound := fun i hi _ => by rw [hte] at hi; obtain rfl : i = 0 := (by omega); exact hent0
      trail_pos_inv := fun i hi => by rw [hte] at hi; obtain rfl : i = 0 := (by omega); rfl
      level0_rsn_none := fun i hi _ => by rw [hte] at hi; obtain rfl : i = 0 := (by omega); rfl
      frame_trail_lt := fun L hL => by rw [hcl] at hL; obtain rfl : L = 0 := (by omega); decide
      frame_trail_mono := fun L1 L2 _ hL2 => by
        rw [hcl] at hL2; obtain rfl : L1 = 0 := (by omega); obtain rfl : L2 = 0 := (by omega)
        exact Nat.le_refl _
      frame_trail_before_lt := fun _ _ h2 => by rw [hcl] at h2; omega
      frame_dec_lt := fun _ _ h2 => by rw [hcl] at h2; omega
      reason_inv := fun i hi hne => by
        rw [hte] at hi; obtain rfl : i = 0 := (by omega); exact absurd rfl hne
      reason_lit_mem := fun i hi hne => by
        rw [hte] at hi; obtain rfl : i = 0 := (by omega); exact absurd rfl hne }
  refine ⟨⟨{ nvOneLit_lengths.core_ok with vals_len := nvOneLit_lengths.core_ok.vals_len },
      nvOneLit_lengths.scratch_ok⟩, hw, ⟨fun v hv => ?_, fun l hl => ?_⟩, fun r hr => ?_,
    ⟨FullLastLearnedWf.of_cleared fun i hi => by
      simp only [nvBvaDenseState, nvOneLitState, nvOneLitScratch, List.getElem?_replicate,
        show i < 16 by omega, ↓reduceIte, Option.getD_some], Nat.le_refl 0⟩, rfl, hdm⟩
  · rw [hmv] at hv; obtain rfl : v = 0 := (by omega); rfl
  · rw [hmv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> rfl
  · have : fullArenaClauseRefs nvBvaDenseState = [] := rfl; simp [this] at hr

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_factor`. -/
theorem nv_bva_factor :
    Func.wp bvaHeapEnv full_factor_body
      (nvOneLitCfg.hdr, 10#64, ()) nvBvaDenseMem
      (fun (r, ()) m' => ∃ s',
        FullDenseInv nvOneLitCfg nvOneLitF0 s' ∧ r = 1#64 ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvOneLitCfg nvBvaDenseState ⋆ emp) nvBvaDenseMem := by
    rw [sep_emp]; exact nvBvaDenseMem_ok
  have hUp : ∀ xs m Q X, fullFheapUpSpec xs m Q X →
      bvaHeapEnv "full_fheap_up" [i64, i64, i64, i32] [] xs m Q X :=
    fun _ _ _ _ h => bvaHeapEnv_mem (e := ⟨"full_fheap_up", [i64, i64, i64, i32], [],
      fullFheapUpSpec, true⟩) (by simp [bvaHeapSpecTable]) h
  have hDown : ∀ xs m Q X, fullFheapDownSpec xs m Q X →
      bvaHeapEnv "full_fheap_down" [i64, i64, i64, i32, i32] [] xs m Q X :=
    fun _ _ _ _ h => bvaHeapEnv_mem (e := ⟨"full_fheap_down", [i64, i64, i64, i32, i32], [],
      fullFheapDownSpec, true⟩) (by simp [bvaHeapSpecTable]) h
  have hTryLit : ∀ xs m Q X, fullBvaTryLitHeapSpec xs m Q X →
      bvaHeapEnv "full_bva_try_lit" [i64, i32, i64] [.bool] xs m Q X :=
    fun _ _ _ _ h => bvaHeapEnv_mem (e := ⟨"full_bva_try_lit", [i64, i32, i64], [.bool],
      fullBvaTryLitHeapSpec, true⟩) (by simp [bvaHeapSpecTable]) h
  exact full_factor_wp bvaHeapEnv hUp hDown hTryLit _ _ _ _
    ⟨nvOneLitCfg, nvOneLitF0, nvBvaDenseState, emp, rfl, nvBvaDense_invW.toDense, hm,
      fun r s' m' hd _ _ hr hm' => by
        rw [sep_emp] at hm'; exact ⟨s', hd, hr, nvDeduceF0_unsat, hm'⟩⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_bva_try_lit`. -/
theorem nv_bva_try_lit :
    Func.wp bvaHeapEnv full_bva_try_lit_body
      (nvOneLitCfg.hdr, 0#32, 1#64, ()) nvBvaDenseMem
      (fun (_ok, ()) m' => ∃ s',
        FullDenseInv nvOneLitCfg nvOneLitF0 s' ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvOneLitCfg nvBvaDenseState ⋆ emp) nvBvaDenseMem := by
    rw [sep_emp]; exact nvBvaDenseMem_ok
  have hScan : ∀ xs m Q X, fullBvaScanCandsSpec xs m Q X →
      bvaHeapEnv "full_bva_scan_cands" [i64, i32, i32, i64] [i32] xs m Q X :=
    fun _ _ _ _ h => bvaHeapEnv_mem (e := ⟨"full_bva_scan_cands", [i64, i32, i32, i64], [i32],
      fullBvaScanCandsSpec, true⟩) (by simp [bvaHeapSpecTable]) h
  have hPick : ∀ xs m Q X, fullBvaPickCandSpec xs m Q X →
      bvaHeapEnv "full_bva_pick_cand" [i64, i32, i32] [i32] xs m Q X :=
    fun _ _ _ _ h => bvaHeapEnv_mem (e := ⟨"full_bva_pick_cand", [i64, i32, i32], [i32],
      fullBvaPickCandSpec, true⟩) (by simp [bvaHeapSpecTable]) h
  have hFilter : ∀ xs m Q X, fullBvaFilterRowSpec xs m Q X →
      bvaHeapEnv "full_bva_filter_row" [i64, i32, i32, i32, i32, i32] [i32] xs m Q X :=
    fun _ _ _ _ h => bvaHeapEnv_mem (e := ⟨"full_bva_filter_row", [i64, i32, i32, i32, i32, i32],
      [i32], fullBvaFilterRowSpec, true⟩) (by simp [bvaHeapSpecTable]) h
  have hCommit : ∀ xs m Q X, fullBvaCommitSpec xs m Q X →
      bvaHeapEnv "full_bva_commit" [i64, i32] [.bool] xs m Q X :=
    fun _ _ _ _ h => bvaHeapEnv_mem (e := ⟨"full_bva_commit", [i64, i32], [.bool],
      fullBvaCommitSpec, true⟩) (by simp [bvaHeapSpecTable]) h
  exact full_bva_try_lit_wp bvaHeapEnv hScan hPick hFilter hCommit _ _ _ _
    ⟨nvOneLitCfg, nvOneLitF0, nvBvaDenseState, emp, rfl, nvBvaDense_invW.toDense, by decide, hm,
      fun _ s' m' hd _ _ _ _ hm' => by
        rw [sep_emp] at hm'; exact ⟨s', hd, nvDeduceF0_unsat, hm'⟩⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_init_fresh_var`. -/
theorem nv_bva_init_fresh_var :
    Func.wp bvaHeapEnv full_init_fresh_var_body
      (nvOneLitCfg.hdr, 0#32, ()) nvBvaDenseMem
      (fun () m' => ∃ s',
        s'.LengthsOk nvOneLitCfg ∧ s'.core.vals[0]?.getD 1#8 = 0#8 ∧
        s'.core.vals[1]?.getD 1#8 = 0#8 ∧ nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvOneLitCfg nvBvaDenseState ⋆ emp) nvBvaDenseMem := by
    rw [sep_emp]; exact nvBvaDenseMem_ok
  exact full_init_fresh_var_heap_wp bvaHeapEnv _ _ _ _
    ⟨nvOneLitCfg, nvBvaDenseState, emp, rfl, nvBvaDense_invW.1, by decide, hm,
      fun _ _ _ _ _ _ _ _ m' hlen _ _ _ _ _ _ hv0 hv1 _ _ _ _ _ _ _ _ _ hm' => by
        rw [sep_emp] at hm'; exact ⟨_, hlen, hv0, hv1, nvDeduceF0_unsat, hm'⟩⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_bva_hop3`. -/
theorem nv_bva_hop3 :
    Func.wp bvaHeapEnv full_bva_hop3_body
      (nvOneLitCfg.hdr, 0#32, 0#32, ()) nvBvaDenseMem
      (fun (_r, ()) m' => ∃ s',
        FullDenseInvNoLm nvOneLitCfg nvOneLitF0 [[0], [1]] s' ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvOneLitCfg nvBvaDenseState ⋆ emp) nvBvaDenseMem := by
    rw [sep_emp]; exact nvBvaDenseMem_ok
  have hHop2 : ∀ xs m Q X, fullBvaHop2Spec xs m Q X →
      bvaHeapEnv "full_bva_hop2" [i64, i32, i32] [i64] xs m Q X :=
    fun _ _ _ _ h => bvaHeapEnv_mem (e := ⟨"full_bva_hop2", [i64, i32, i32], [i64],
      fullBvaHop2Spec, true⟩) (by simp [bvaHeapSpecTable]) h
  exact full_bva_hop3_wp bvaHeapEnv hHop2 _ _ _ _
    ⟨nvOneLitCfg, nvOneLitF0, [[0], [1]], nvBvaDenseState, emp, rfl,
      FullDenseInvW.toNoLm nvBvaDense_invW,
      by decide, hm, fun _ _ _ _ _ _ m' hnl hm' => by
        rw [sep_emp] at hm'; exact ⟨_, hnl, nvDeduceF0_unsat, hm'⟩⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_bva_scan_cands`. -/
theorem nv_bva_scan_cands :
    Func.wp bvaHeapEnv full_bva_scan_cands_body
      (nvOneLitCfg.hdr, 0#32, 0#32, 2#64, ()) nvBvaDenseMem
      (fun (n, ()) m' => ∃ s',
        s'.LengthsOk nvOneLitCfg ∧ n.toNat ≤ 2 ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvOneLitCfg nvBvaDenseState ⋆ emp) nvBvaDenseMem := by
    rw [sep_emp]; exact nvBvaDenseMem_ok
  exact full_bva_scan_cands_wp bvaHeapEnv _ _ _ _
    ⟨nvOneLitCfg, nvOneLitF0, [[0], [1]], nvBvaDenseState, emp, rfl, nvBvaDense_invW.1,
      nvBvaDense_invW.2.1, nvBvaDense_invW.2.2.2.1, nvBvaDense_invW.2.2.2.2.1,
      nvBvaDense_invW.2.2.2.2.2.1, nvBvaDense_invW.2.2.2.2.2.2, by decide,
      fun l hl => by rw [nvBvaDense_invW.2.2.1.2 l hl]; decide,
      by decide, by decide, fun _ h => by simp at h, hm,
      fun n _ _ _ m' hlen hn _ hm' => by
        rw [sep_emp] at hm'; exact ⟨_, hlen, hn, nvDeduceF0_unsat, hm'⟩⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_bva_pick_cand`. -/
theorem nv_bva_pick_cand :
    Func.wp bvaHeapEnv full_bva_pick_cand_body
      (nvOneLitCfg.hdr, 0#32, 0#32, ()) nvBvaDenseMem
      (fun (r, ()) m' => ∃ s',
        FullDenseInvNoLm nvOneLitCfg nvOneLitF0 [[0], [1]] s' ∧
        (r = 0xFFFFFFFF#32 ∨ r.toNat < 2) ∧ nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvOneLitCfg nvBvaDenseState ⋆ emp) nvBvaDenseMem := by
    rw [sep_emp]; exact nvBvaDenseMem_ok
  have hHop3 : ∀ xs m Q X, fullBvaHop3Spec xs m Q X →
      bvaHeapEnv "full_bva_hop3" [i64, i32, i32] [i64] xs m Q X :=
    fun _ _ _ _ h => bvaHeapEnv_mem (e := ⟨"full_bva_hop3", [i64, i32, i32], [i64],
      fullBvaHop3Spec, true⟩) (by simp [bvaHeapSpecTable]) h
  exact full_bva_pick_cand_wp bvaHeapEnv hHop3 _ _ _ _
    ⟨nvOneLitCfg, nvOneLitF0, [[0], [1]], nvBvaDenseState, emp, rfl,
      FullDenseInvW.toNoLm nvBvaDense_invW,
      by decide, by decide, fun _ h => by simp at h, hm,
      fun r _ _ _ _ _ _ _ _ m' hnl hr hm' => by
        rw [sep_emp] at hm'; exact ⟨_, hnl, hr, nvDeduceF0_unsat, hm'⟩⟩

end ConcreteUnsatNonVacuity

end LeanQbe.T.Examples.Kissat.FullBvaHeap
