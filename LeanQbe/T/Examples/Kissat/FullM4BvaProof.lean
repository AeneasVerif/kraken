module

public import LeanQbe.T.Examples.Kissat.FullM4BvaLemmas3
public import LeanQbe.T.Examples.Kissat.FullM3Proof
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Full` M4d BVA & Elim Scheduling — Top Proofs, `ModuleOk`, & Non-Vacuity

Completes the verified M4d BVA/factoring & elim scheduling stack:
1. `m4_factor_wp` (`fullFactorHeapSpec`): max-degree binary heap factoring driver (`16448`-word
   scratch guard, `init_cv` original-variable scan, bottom-up heapify resift after `try_lit`).
2. `m4_eliminate_wp` (`FullFastSched.schedEliminateSpec`): square-root-capped elim interval,
   pre-BVE + post-BVE `full_factor` (with `TmkZero` init before `full_elim_bve`).
3. `m4_preprocess_wp` (`Full.fullPreprocessSpec`): capped initial `elim_limit` (`min(_, 6000)`).
4. Standalone `m4BvaSpecTable`, `m4BvaEnv`, `m4Bva_moduleOk : ModuleOk m4BvaEnv m4BvaModule`.
5. Closed `204`-function `m4BvaFullSpecTable`, `mkM4BvaFullEnv`, `m4BvaFullEnv`,
   `m4BvaFullUnsatEnv`, `mkM4BvaFullEnv_moduleOk`, `m4BvaFullEnv_moduleOk`,
   `m4BvaFullUnsatEnv_moduleOk` via `wp_env_agree_of_callsOk` from `FullM3.mkM3Env_moduleOk`.
6. Headline UNSAT soundness `m4_bva_solve_bytes_correct` and concrete `Mem 64` UNSAT non-vacuity
   (`XPost := False`, zero SAT/model-finding proofs).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM4Bva

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.C0Step LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullBvaHeap
open LeanQbe.T.Examples.Kissat.FullBvaHeap.FullBvaHeapHelpers
open LeanQbe.T.Examples.Kissat.FullBvaHeap.FullBvaHeapTactics
open LeanQbe.T.Examples.Kissat.FullFastBveBudgets
open LeanQbe.T.Examples.Kissat.FullFastSched
open Kraken.Bedrock2.Test
open scoped FullArenaTactics FullBvaHeapTactics

/-! ## 1. Max-Degree Binary Heap Factoring Driver (`m4_factor_wp`) -/

section M4FactorHelpers

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

end M4FactorHelpers

theorem m4_factor_wp (Γ : Env)
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
    have h2init : (BitVec.ofNat 64 s.core.cur_vars <<< (1 : Nat)).toNat = 2 * s.core.cur_vars := by
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
          · -- Exit main loop: zero `hp[0..2*cur_vars)` & `ps`, return `1ULL`
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
                        · -- Clear `fbit`, `budget--`, call `full_bva_try_lit(h, f0, init_cv)`
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
                          have hcv3_ge_init : s.core.cur_vars ≤ st3.core.cur_vars := by
                            dsimp only [st1] at hcv2; omega
                          have hhp3_ok : ∀ k < (hlen - 1#32).toNat,
                              (st3.scratch.tarjan_mark[k]?.getD 0#32).toNat <
                                2 * st3.core.cur_vars := by
                            intro k hk; rw [htm3, htm2]; have := hhp1_ok k hk
                            dsimp only [st1] at hcv2 ⊢; omega
                          c0_hsplit
                          · -- `try_lit == true`: touched-literal sift & re-insert over `work_stk2`
                            c0_hsteps_nogrp
                            refine wp_join_state1 (t := i64) (α := BitVec 64) (fun x => x)
                              (fun ntv mnt => ntv.toNat ≤ 2 * s.core.cur_vars ∧ mnt = m3)
                              (fun _ nt mnt ⟨hnt_le, hmnt⟩ => ?_)
                              (fun Jnt hJnt => ?_)
                            · rcases hmnt.symm with rfl
                              c0_hsteps_nogrp
                              refine wp_loop_inv
                                (fun (hlc, ti, ()) mc => ∃ hpc psc : List (BitVec 32),
                                  ti.toNat ≤ nt.toNat ∧ hlc.toNat ≤ 2 * c.max_vars ∧
                                  hpc.length = 2 * c.max_vars ∧ psc.length = 2 * c.max_vars ∧
                                  (∀ k < hlc.toNat,
                                    (hpc[k]?.getD 0#32).toNat < 2 * st3.core.cur_vars) ∧
                                  (FullMem c { st3 with scratch :=
                                    { st3.scratch with tarjan_mark := hpc,
                                                       tarjan_reach := psc } } ⋆ R) mc)
                                (fun (_, ti, _) _ => nt.toNat - ti.toNat)
                                (fun Jti hJti => by
                                  c0_hfast
                                  exact hJti (hlen - 1#32, 0#64, ()) m3
                                    ⟨st3.scratch.tarjan_mark, st3.scratch.tarjan_reach,
                                     Nat.zero_le _, by rw [hhl1]; omega, hsc3.tarjan_mark_len,
                                     hsc3.tarjan_reach_len, hhp3_ok, hm3⟩)
                                (fun Jti (hlc, ti, ()) mc
                                    ⟨hpc, psc, hti_le, hhlc_le, hhpc_l, hpsc_l, hhpc_ok, hmc⟩
                                    ihti => ?_)
                              c0_hsplit
                              · have hti_lt : ti.toNat < nt.toNat := by assumption
                                have hti1 : (ti + 1#64).toNat = ti.toNat + 1 := by
                                  simp only [bv_c0]; omega
                                have hti_ws2 : ti.toNat < st3.scratch.work_stk2.length := by
                                  have := hsc3.work_stk2_len; omega
                                let tl := st3.scratch.work_stk2[ti.toNat]'hti_ws2
                                c0_hsteps_nogrp
                                refine wp_join_state1 (t := i32)
                                  (α := BitVec 32 × List (BitVec 32) × List (BitVec 32))
                                  (fun x => x.1)
                                  (fun ⟨hlc', hpc', psc'⟩ mc' =>
                                    hlc'.toNat ≤ 2 * c.max_vars ∧
                                    hpc'.length = 2 * c.max_vars ∧
                                    psc'.length = 2 * c.max_vars ∧
                                    (∀ k < hlc'.toNat,
                                      (hpc'[k]?.getD 0#32).toNat < 2 * st3.core.cur_vars) ∧
                                    (FullMem c { st3 with scratch :=
                                      { st3.scratch with tarjan_mark := hpc',
                                                         tarjan_reach := psc' } } ⋆ R) mc')
                                  (fun _ ⟨hlc', hpc', psc'⟩ mc'
                                      ⟨hhlc', hhpc', hpsc', hhpc_ok', hmc'⟩ => by
                                    c0_hsteps_nogrp
                                    exact ihti (hlc', ti + 1#64, ()) mc'
                                      (by dsimp only; rw [hti1]; omega)
                                      ⟨hpc', psc', by rw [hti1]; omega, hhlc', hhpc', hpsc',
                                       hhpc_ok', hmc'⟩)
                                  (fun Jtl hJtl => ?_)
                                c0_hsplit
                                · have htl_lt : tl.toNat < 2 * s.core.cur_vars := by
                                    have h1 : (BitVec.setWidth 64 tl).toNat <
                                        (BitVec.ofNat 64 s.core.cur_vars <<< (1 : Nat)).toNat := by
                                      assumption
                                    rwa [bv64_setWidth_32, h2init] at h1
                                  have htl_lt3 : tl.toNat < 2 * st3.core.cur_vars := by omega
                                  have htl_ps : (BitVec.setWidth 64 tl).toNat < psc.length := by
                                    rw [bv64_setWidth_32]; omega
                                  c0_hsteps_nogrp; c0_hstep; c0_hsplit
                                  · -- `pos_tl < hlen`: sift up, then re-read `pos2` and sift down
                                    have hptl_lt :
                                        (psc[(BitVec.setWidth 64 tl).toNat]'htl_ps).toNat <
                                          hlc.toNat := by assumption
                                    dsimp only [tl] at hptl_lt
                                    have hptl_lt2 :
                                        (psc[(st3.scratch.work_stk2[ti.toNat]'hti_ws2).toNat]'(by
                                          rw [bv64_setWidth_32] at htl_ps; exact htl_ps)).toNat <
                                          hlc.toNat := by
                                      simpa only [bv64_setWidth_32] using hptl_lt
                                    c0_hsteps_nogrp
                                    c0_call hUp
                                    refine ⟨2 * c.max_vars, hpc, psc, st3.core.wvec,
                                      FullMemFheapRest c st3 ⋆ R,
                                      Nat.le_of_eq hhpc_l.symm, Nat.le_of_eq hpsc_l.symm,
                                      by rw [hcl3.wvec_len]; omega, hnl_lt, by omega,
                                      fun i hi => by have := hhpc_ok i (by omega); omega,
                                      focus_fheap hmc,
                                      fun hpc1 psc1 m1 hhpc1_l hpsc1_l hsub1 hhi1 hm1 => ?_⟩
                                    have hhpc1_ok : ∀ k < hlc.toNat,
                                        (hpc1[k]?.getD 0#32).toNat < 2 * st3.core.cur_vars := by
                                      intro k hk
                                      by_cases hkle : k ≤
                                          (psc[(BitVec.setWidth 64
                                            (st3.scratch.work_stk2[ti.toNat]'hti_ws2)).toNat]'
                                              htl_ps).toNat
                                      · obtain ⟨j, hj, heq⟩ := hsub1 k hkle
                                        rw [heq]; exact hhpc_ok j (by omega)
                                      · rw [hhi1 k (by omega)]; exact hhpc_ok k hk
                                    have hmc1 := unfocus_fheap hm1
                                    have htl_ps1 : (BitVec.setWidth 64 tl).toNat < psc1.length := by
                                      rw [hpsc1_l]; exact htl_ps
                                    c0_hsteps_nogrp; c0_hstep; c0_hsplit
                                    · have hp2_lt :
                                          (psc1[(BitVec.setWidth 64 tl).toNat]'htl_ps1).toNat <
                                            hlc.toNat := by assumption
                                      c0_hsteps_nogrp
                                      c0_call hDown
                                      refine ⟨2 * c.max_vars, hpc1, psc1, st3.core.wvec,
                                        FullMemFheapRest c st3 ⋆ R,
                                        by omega, by omega, by rw [hcl3.wvec_len]; omega, hnl_lt,
                                        hp2_lt, hhlc_le,
                                        fun i hi => by have := hhpc1_ok i hi; omega,
                                        focus_fheap hmc1,
                                        fun hpc2 psc2 m2 hhpc2_l hpsc2_l hsub2 _ hm2 => ?_⟩
                                      c0_hfast
                                      refine hJtl ⟨hlc, hpc2, psc2⟩ m2
                                        ⟨hhlc_le, hhpc2_l.trans (hhpc1_l.trans hhpc_l),
                                         hpsc2_l.trans (hpsc1_l.trans hpsc_l),
                                         fun k hk => by
                                           obtain ⟨j, hj, heq⟩ := hsub2 k hk
                                           rw [heq]; exact hhpc1_ok j hj,
                                         unfocus_fheap hm2⟩
                                    · c0_hfast
                                      exact hJtl ⟨hlc, hpc1, psc1⟩ m1
                                        ⟨hhlc_le, hhpc1_l.trans hhpc_l, hpsc1_l.trans hpsc_l,
                                         hhpc1_ok, hmc1⟩
                                  · -- `else if (hlen < mx_lits)`: check active/flag/deg/val/unpush
                                    c0_hsteps_nogrp; c0_hstep; c0_hsplit
                                    · have hhlc_lt : hlc.toNat < 2 * c.max_vars := by
                                        have h1 : (BitVec.setWidth 64 hlc).toNat <
                                            (BitVec.ofNat 64 c.max_vars <<< (1 : Nat)).toNat := by
                                          assumption
                                        rwa [bv64_setWidth_32, hmx2] at h1
                                      have hhlc1 : (hlc + 1#32).toNat = hlc.toNat + 1 := by
                                        simp only [bv_c0]; omega
                                      c0_hsteps_nogrp
                                      refine wp_join_state1 (t := i32) (α := BitVec 32) (fun b => b)
                                        (fun _ mcb => mcb = mc)
                                        (fun _ tbit mcb hmcb => ?_)
                                        (fun Jtb hJtb => ?_)
                                      · subst mcb
                                        have htv_fl :
                                            (BitVec.setWidth 64 (tl >>> (1 : Nat))).toNat <
                                              st3.core.flags.length := by
                                          rw [bv64_setWidth_32, hcl3.flags_len, bv32_lshr1_nat]
                                          omega
                                        have htl_wv : ((BitVec.setWidth 64 tl <<< (1 : Nat)) +
                                            1).toNat < st3.core.wvec.length := by
                                          change ((BitVec.setWidth 64 tl <<< (1 : Nat)) +
                                            1#64).toNat < _
                                          rw [hcl3.wvec_len, BitVec.toNat_add, bv64_shl1_nat,
                                            bv64_setWidth_32, show (1#64).toNat = 1 from rfl]; omega
                                        have htl_v : (BitVec.setWidth 64 tl).toNat <
                                            st3.core.vals.length := by
                                          rw [bv64_setWidth_32, hcl3.vals_len]; omega
                                        have hhlc_hp : (BitVec.setWidth 64 hlc).toNat <
                                            hpc.length := by
                                          rw [bv64_setWidth_32, hhpc_l]; exact hhlc_lt
                                        c0_hfast
                                        · let hpca := hpc.set hlc.toNat tl
                                          let psca := psc.set tl.toNat hlc
                                          have hmca : (FullMem c { st3 with scratch :=
                                              { st3.scratch with tarjan_mark := hpca,
                                                                 tarjan_reach := psca } } ⋆ R) m :=
                                            by simp only [hpca, psca, bv64_setWidth_32] at hm ⊢
                                               exact hm
                                          c0_call hUp
                                          refine ⟨2 * c.max_vars, hpca, psca, st3.core.wvec,
                                            FullMemFheapRest c st3 ⋆ R,
                                            by simp [hpca, hhpc_l], by simp [psca, hpsc_l],
                                            by rw [hcl3.wvec_len]; omega, hnl_lt, hhlc_lt,
                                            fun i hi => by
                                              dsimp only [hpca]
                                              by_cases hie : i = hlc.toNat
                                              · subst hie
                                                rw [List.getElem?_set_self (by omega),
                                                  Option.getD_some]; omega
                                              · rw [List.getElem?_set_ne (Ne.symm hie)]
                                                have := hhpc_ok i (by omega); omega,
                                            focus_fheap hmca,
                                            fun hpc' psc' mc' hhpc'_l hpsc'_l hsubc _ hmc' => ?_⟩
                                          c0_hfast
                                          refine hJtl ⟨hlc + 1#32, hpc', psc'⟩ mc'
                                            ⟨by rw [hhlc1]; omega,
                                             by simp [hpca, hhpc_l] at hhpc'_l; exact hhpc'_l,
                                             by simp [psca, hpsc_l] at hpsc'_l; exact hpsc'_l,
                                             fun k hk => ?_, unfocus_fheap hmc'⟩
                                          rw [hhlc1] at hk
                                          obtain ⟨j, hj, heq⟩ := hsubc k (by omega)
                                          rw [heq]; dsimp only [hpca]
                                          by_cases hje : j = hlc.toNat
                                          · subst hje
                                            rw [List.getElem?_set_self (by omega), Option.getD_some]
                                            exact htl_lt3
                                          · rw [List.getElem?_set_ne (Ne.symm hje)]
                                            exact hhpc_ok j (by omega)
                                        all_goals
                                          exact hJtl ⟨hlc, hpc, psc⟩ mc
                                            ⟨hhlc_le, hhpc_l, hpsc_l, hhpc_ok, hmc⟩
                                      · c0_hfast
                                        · exact hJtb 64#32 mc rfl
                                        · exact hJtb 32#32 mc rfl
                                    · c0_hfast
                                      exact hJtl ⟨hlc, hpc, psc⟩ mc
                                        ⟨hhlc_le, hhpc_l, hpsc_l, hhpc_ok, hmc⟩
                                · c0_hfast
                                  exact hJtl ⟨hlc, hpc, psc⟩ mc
                                    ⟨hhlc_le, hhpc_l, hpsc_l, hhpc_ok, hmc⟩
                              · c0_hfast
                                exact ihm (budget - 1#64, hlc, ()) mc
                                  (by dsimp only; rw [hbud1]
                                      have hm1 : (budget.toNat - 1) * (2 * c.max_vars + 1) +
                                          (2 * c.max_vars + 1) =
                                          budget.toNat * (2 * c.max_vars + 1) := by
                                        rw [← Nat.add_one_mul, Nat.sub_add_cancel (by omega)]
                                      omega)
                                  ⟨{ st3 with scratch :=
                                      { st3.scratch with tarjan_mark := hpc,
                                                         tarjan_reach := psc } },
                                   hmc, fullDenseInv_set_fheap hw3.toDense hhpc_l hpsc_l,
                                   hcv3_ge_init, hfuel3.trans (hfuel2.trans hfuell), hhlc_le,
                                   hhpc_ok⟩
                            · c0_hfast
                              · exact hJnt _ m3 ⟨by rw [h2init]; exact Nat.le_refl _, rfl⟩
                              · exact hJnt _ m3 ⟨by
                                  have h1 :
                                      ¬ (BitVec.ofNat 64 s.core.cur_vars <<< (1 : Nat)).toNat <
                                        st3.scratch.res_sz.toNat := by assumption
                                  rw [h2init] at h1; omega, rfl⟩
                          · -- `try_lit == false`
                            c0_hfast
                            exact ihm (budget - 1#64, hlen - 1#32, ()) m3
                              (by dsimp only; rw [hbud1, hhl1]
                                  have hm1 : (budget.toNat - 1) * (2 * c.max_vars + 1) +
                                      (2 * c.max_vars + 1) =
                                      budget.toNat * (2 * c.max_vars + 1) := by
                                    rw [← Nat.add_one_mul, Nat.sub_add_cancel (by omega)]
                                  omega)
                              ⟨st3, hm3, hw3.toDense, hcv3_ge_init,
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

/-! ## 2. Upgraded Elim & Preprocess Orchestrators (`m4_eliminate_wp`, `m4_preprocess_wp`) -/

section M4Orchestrators

private theorem m4_sparseInv_with_scratch_keep {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseInv c F0 s) {sc' : FullScratch} (hok : sc'.LengthsOk c)
    (hll : sc'.last_learned = s.scratch.last_learned)
    (hext : sc'.extend_len = s.scratch.extend_len) :
    FullSparseInv c F0 { s with scratch := sc' } :=
  h.of_safetySlice (h.lengths.with_scratch hok) rfl ⟨hll, hext⟩

private theorem m4_denseInv_with_scratch_keep {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullDenseInv c F0 s) {sc' : FullScratch} (hok : sc'.LengthsOk c)
    (hll : sc'.last_learned = s.scratch.last_learned)
    (hext : sc'.extend_len = s.scratch.extend_len) :
    FullDenseInv c F0 { s with scratch := sc' } :=
  h.of_safetySlice (h.lengths.with_scratch hok) rfl ⟨hll, hext⟩

private theorem m4_tmkZero_of_init_loop {s : FullState}
    {tmki : List (BitVec 32)} (hinit : ∀ k < s.core.cur_vars, tmki[k]?.getD 0#32 = 0#32) :
    TmkZero { s with scratch := { s.scratch with tarjan_mark := tmki } } :=
  fun v hv => hinit v hv

/-- Upgraded `full_eliminate`: square-root-capped elim interval, pre-BVE + post-BVE `full_factor`
with `TmkZero` init right before `full_elim_bve`, against `FullFastSched.schedEliminateSpec`. -/
theorem m4_eliminate_wp (Γ : Env)
    (hDticks : ∀ a m Q X, schedElimDticksSpec a m Q X →
      Γ "full_elim_dticks" [i64, .bool] [i64] a m Q X)
    (hIlog : ∀ a m Q X, fullIlog10Spec a m Q X → Γ "full_ilog10" [i64] [i64] a m Q X)
    (hIsqrt : ∀ a m Q X, Full.fullIsqrtSpec a m Q X → Γ "full_isqrt" [i64] [i64] a m Q X)
    (hScale : ∀ a m Q X, schedScaleDeltaSpec a m Q X →
      Γ "full_scale_delta" [i64, i64] [i64] a m Q X)
    (hEnter : ∀ a m Q X, schedEnterDenseSpec a m Q X →
      Γ "full_enter_dense" [i64] [.bool] a m Q X)
    (hFwd : ∀ a m Q X, fullForwardSubFastSpec a m Q X →
      Γ "full_forward_sub" [i64, i64] [i64] a m Q X)
    (hMin : ∀ a m Q X, schedMinU64Spec a m Q X → Γ "full_min_u64" [i64, i64] [i64] a m Q X)
    (hBve : ∀ a m Q X, FullM3CongBva.m3ElimBveSpec a m Q X →
      Γ "full_elim_bve" [i64, i64] [i64] a m Q X)
    (hFact : ∀ a m Q X, fullFactorHeapSpec a m Q X → Γ "full_factor" [i64, i64] [i64] a m Q X)
    (hReb : ∀ a m Q X, fullRebuildWatchesSpec a m Q X →
      Γ "full_rebuild_watches" [i64] [i64] a m Q X) :
    ∀ a m Q X, schedEliminateSpec a m Q X → Func.wp Γ full_eliminate_body a m Q X := by
  rintro ⟨h, initial, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hcl0, hm, hQ⟩
  unfold Func.wp full_eliminate_body
  c0_hsteps; c0_call hDticks; refine ⟨c, s, R, rfl, hinv.lengths, hm, ?_⟩
  intro dticks
  c0_hsteps_nogrp
  -- Join 1: after `if (!initial)` square-root-capped limit/bound update
  refine wp_join_state0 (α := FullState)
    (fun s0 m0 => FullSparseInv c F0 s0 ∧ s0.core.cur_level = 0 ∧
      s0.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c s0 ⋆ R) m0)
    (fun _ s0 m0 ⟨hinv0, _, hfu0, hm0⟩ => by
      c0_hsteps; c0_call hEnter; refine ⟨c, F0, s0, R, rfl, hinv0, hm0, ?_⟩
      intro ok s1 m1 hcl1 hfu1 hok_d hfail_s hm1
      c0_hsplit
      · have hden1 : FullDenseInv c F0 s1 := hok_d hc
        c0_hsteps_nogrp
        refine wp_join_state_pure (ts := [i64]) (α := BitVec 64)
          (fun b => (b, ())) (fun _ => True)
          (fun _ fbud _ => by
            c0_hsteps; c0_call hMin; intro _ _
            c0_hsteps; c0_call hFwd; refine ⟨c, F0, s1, R, rfl, hden1, hm1, ?_⟩
            intro fs s2 m2 hden2 _ hfu2 _ huf2 hm2
            let s2r : FullState :=
              { s2 with scratch := { s2.scratch with fwd_sub_cnt := s1.scratch.fwd_sub_cnt } }
            have hden2r : FullDenseInv c F0 s2r :=
              m4_denseInv_with_scratch_keep hden2 { hden2.lengths.scratch_ok with } rfl rfl
            have hfu2r : s2r.core.fuel.toNat ≤ s.core.fuel.toNat := by
              change s2.core.fuel.toNat ≤ s.core.fuel.toNat; rw [hfu2]; omega
            c0_hsplit
            · c0_hsteps; c0_call hReb; refine ⟨c, F0, s2r, R, rfl, hden2r, hm, ?_⟩
              intro _ s3 m3 hsp3 hcl3 hfu3 _ _ hm3; c0_hsteps
              exact hQ 20#64 s3 m3 hsp3 hcl3 (by omega) (Or.inr rfl) (fun _ => huf2 hc) hm3
            · -- Compute `fact_bud`, run optional pre-BVE `full_factor(h, fact_bud)`
              c0_hsteps_nogrp
              refine wp_join_state_pure (ts := [i64]) (α := BitVec 64)
                (fun b => (b, ())) (fun _ => True)
                (fun _ _ _ => by
                  c0_hsteps; c0_call hMin; intro fact_bud _
                  c0_hsteps_nogrp
                  refine wp_join_state0 (α := FullState)
                    (fun s2f m2f => FullDenseInv c F0 s2f ∧
                      s2f.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c s2f ⋆ R) m2f)
                    (fun _ s2f m2f ⟨hden2f, hfu2f, hm2f⟩ => by
                      -- Zero `tmk[0..cv)` before `full_elim_bve`
                      let cv2 := s2f.core.cur_vars
                      have hcv2_le : cv2 ≤ c.max_vars := hden2f.lengths.core_ok.cur_vars_le
                      have hmx := c.hmaxv; unfold dimacsBound at hmx
                      have hcv2_64 : cv2 < 2 ^ 64 := by omega
                      have htl2 := hden2f.lengths.scratch_ok.tarjan_mark_len
                      c0_hsteps_nogrp
                      refine wp_loop_inv
                        (fun (ti, ()) mt => ∃ tmki : List (BitVec 32),
                          tmki.length = 2 * c.max_vars ∧ ti.toNat ≤ cv2 ∧
                          (∀ k < ti.toNat, tmki[k]?.getD 0#32 = 0#32) ∧
                          (FullMem c { s2f with scratch :=
                            { s2f.scratch with tarjan_mark := tmki } } ⋆ R) mt)
                        (fun (ti, ()) _ => cv2 - ti.toNat)
                        (fun Jt hJt => by
                          c0_hfast; exact hJt (0#64, ()) m2f
                            ⟨s2f.scratch.tarjan_mark, htl2, Nat.zero_le _,
                             fun _ h => by simp at h, hm2f⟩)
                        (fun Jt (ti, ()) mt ⟨tmki, htli, hti_le, hinit, hmt⟩ iht => ?_)
                      c0_hsplit
                      · have hti_lt : ti.toNat < cv2 := by
                          have hlt : ti.toNat < (BitVec.ofNat 64 cv2).toNat := by assumption
                          rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcv2_64] at hlt
                        have hti_arr : ti.toNat < tmki.length := by omega
                        have hti1 : (ti + 1#64).toNat = ti.toNat + 1 := by simp only [bv_c0]; omega
                        c0_hfast
                        exact iht (ti + 1#64, ()) m (by dsimp only; omega)
                          ⟨tmki.set ti.toNat 0#32, by simp [htli], by omega,
                           fun k hk => by
                             rw [hti1] at hk
                             by_cases hkt : k = ti.toNat
                             · subst hkt; rw [List.getElem?_set_self (by omega), Option.getD_some]
                             · rw [List.getElem?_set_ne (Ne.symm hkt)]; exact hinit k (by omega),
                           hm⟩
                      · have hti_eq : ti.toNat = cv2 := by
                          have hnot : ¬ ti.toNat < (BitVec.ofNat 64 cv2).toNat := by assumption
                          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcv2_64] at hnot
                          omega
                        rw [hti_eq] at hinit
                        let s2t : FullState :=
                          { s2f with scratch := { s2f.scratch with tarjan_mark := tmki } }
                        have hden2t : FullDenseInv c F0 s2t :=
                          m4_denseInv_with_scratch_keep hden2f
                            { hden2f.lengths.scratch_ok with tarjan_mark_len := htli } rfl rfl
                        have htmk2 : TmkZero s2t := m4_tmkZero_of_init_loop hinit
                        have hfu2t : s2t.core.fuel.toNat ≤ s.core.fuel.toNat := hfu2f
                        c0_hsteps_nogrp
                        refine wp_join_state_pure (ts := [i64]) (α := BitVec 64)
                          (fun b => (b, ())) (fun _ => True)
                          (fun _ bve_lim _ => by
                            c0_hsteps; c0_call hBve
                            refine ⟨c, F0, s2t, R, rfl, hden2t, htmk2, hmt, ?_⟩
                            intro res s3 m3 hden3 _ hfu3 _ hres_u hm3
                            c0_hsteps_nogrp
                            -- Join after optional post-BVE `full_factor(h, fact_bud)`
                            refine wp_join_state0 (α := FullState)
                              (fun sf mf => FullDenseInv c F0 sf ∧
                                sf.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c sf ⋆ R) mf)
                              (fun _ sf mf ⟨hdenf, hfuf, hmf⟩ => by
                                c0_hsteps; c0_call hReb
                                refine ⟨c, F0, sf, R, rfl, hdenf, hmf, ?_⟩
                                intro rr se me hspe hcle hfue _ hue hme
                                let se' : FullState :=
                                  { se with scratch :=
                                    { se.scratch with fwd_str_cnt := se.scratch.search_ticks } }
                                have hspe' : FullSparseInv c F0 se' :=
                                  m4_sparseInv_with_scratch_keep hspe
                                    { hspe.lengths.scratch_ok with } rfl rfl
                                have hfue' : se'.core.fuel.toNat ≤ s.core.fuel.toNat := by
                                  change se.core.fuel.toNat ≤ s.core.fuel.toNat; omega
                                c0_hsteps
                                · exact hQ 20#64 se' _ hspe' hcle hfue' (Or.inr rfl)
                                    (fun _ => hres_u hc) hm
                                · exact hQ 20#64 se' _ hspe' hcle hfue' (Or.inr rfl)
                                    (fun _ => hue hc) hm
                                · exact hQ 20#64 se' _ hspe' hcle hfue' (Or.inr rfl)
                                    (fun _ => hspe'.inconsistent_unsat hc) hm
                                · exact hQ 1#64 se' _ hspe' hcle hfue' (Or.inl rfl)
                                    (fun h => by cases h) hm)
                              (fun Jf hJf => by
                                c0_hsplit
                                · c0_hsteps_nogrp
                                  refine wp_join_state0 (α := FullState)
                                    (fun sg mg => FullDenseInv c F0 sg ∧
                                      sg.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                                      (FullMem c sg ⋆ R) mg)
                                    (fun _ sg mg ⟨hdeng, hfug, hmg⟩ => by
                                      c0_hsteps; c0_call hFact
                                      refine ⟨c, F0, sg, R, rfl, hdeng, hmg, ?_⟩
                                      intro _ sf mf hdenf _ hfuf _ hmf
                                      exact hJf sf mf ⟨hdenf, by rw [hfuf]; exact hfug, hmf⟩)
                                    (fun Jdo hJdo => by
                                      c0_hsteps
                                      · exact hJdo s3 m3 ⟨hden3, by omega, hm3⟩
                                      · exact hJdo s3 m3 ⟨hden3, by omega, hm3⟩
                                      · exact hJf s3 m3 ⟨hden3, by omega, hm3⟩)
                                · c0_hsteps; exact hJf s3 m3 ⟨hden3, by omega, hm3⟩))
                          (fun Jb hJb => by
                            c0_hsteps
                            · exact hJb _ trivial
                            · c0_call hMin; intro b _; exact hJb b trivial))
                    (fun Jf1 hJf1 => by
                      c0_hsteps_nogrp
                      refine wp_join_state0 (α := FullState)
                        (fun sg mg => FullDenseInv c F0 sg ∧
                          sg.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c sg ⋆ R) mg)
                        (fun _ sg mg ⟨hdeng, hfug, hmg⟩ => by
                          c0_hsteps; c0_call hFact
                          refine ⟨c, F0, sg, R, rfl, hdeng, hmg, ?_⟩
                          intro _ sf mf hdenf _ hfuf _ hmf
                          exact hJf1 sf mf ⟨hdenf, by rw [hfuf]; exact hfug, hmf⟩)
                        (fun Jdo1 hJdo1 => by
                          c0_hsteps
                          · exact hJdo1 s2r m ⟨hden2r, hfu2r, hm⟩
                          · exact hJdo1 s2r m ⟨hden2r, hfu2r, hm⟩
                          · exact hJf1 s2r m ⟨hden2r, hfu2r, hm⟩)))
                (fun Jfb hJfb => by c0_hsteps <;> exact hJfb _ trivial))
          (fun Jfb hJfb => by c0_hsteps <;> exact hJfb _ trivial)
      · have hsp1 : FullSparseInv c F0 s1 := hfail_s hc
        let s1' : FullState :=
          { s1 with scratch := { s1.scratch with fwd_str_cnt := s1.scratch.search_ticks } }
        have hsp1' : FullSparseInv c F0 s1' :=
          m4_sparseInv_with_scratch_keep hsp1 { hsp1.lengths.scratch_ok with } rfl rfl
        have hfu1' : s1'.core.fuel.toNat ≤ s.core.fuel.toNat := by
          change s1.core.fuel.toNat ≤ s.core.fuel.toNat; omega
        c0_hsteps
        · exact hQ 20#64 s1' _ hsp1' hcl1 hfu1' (Or.inr rfl)
            (fun _ => hsp1'.inconsistent_unsat hc) hm
        · exact hQ 1#64 s1' _ hsp1' hcl1 hfu1' (Or.inl rfl) (fun h => by cases h) hm)
    (fun J1 hJ1 => by
      c0_hsplit
      · c0_hsteps; exact hJ1 s m ⟨hinv, hcl0, Nat.le_refl _, hm⟩
      · c0_hsteps
        let s0a : FullState :=
          { s with scratch := { s.scratch with eliminations := s.scratch.eliminations + 1#64 } }
        have hlen0a : s0a.LengthsOk c :=
          ⟨hinv.lengths.core_ok, { hinv.lengths.scratch_ok with }⟩
        c0_call hIlog; intro loge _ _
        c0_hsteps; c0_call hScale; refine ⟨c, s0a, R, rfl, hlen0a, hm, ?_⟩
        intro d_scale
        c0_hsteps; c0_call hIsqrt; intro sq _ _ _
        c0_hsteps; c0_call hMin; intro delta _
        let s0b : FullState :=
          { s0a with scratch := { s0a.scratch with elim_limit := s0a.scratch.conflicts + delta } }
        have hinv0b : FullSparseInv c F0 s0b :=
          m4_sparseInv_with_scratch_keep hinv { hinv.lengths.scratch_ok with } rfl rfl
        let s0c : FullState :=
          { s0b with scratch :=
            { s0b.scratch with elim_bound := s0b.scratch.elim_bound + 2#64 } }
        have hinv0c : FullSparseInv c F0 s0c :=
          m4_sparseInv_with_scratch_keep hinv0b { hinv0b.lengths.scratch_ok with } rfl rfl
        c0_hsteps
        · exact hJ1 s0c _ ⟨hinv0c, hcl0, Nat.le_refl _, hm⟩
        · exact hJ1 s0b _ ⟨hinv0b, hcl0, Nat.le_refl _, hm⟩
        · exact hJ1 s0b _ ⟨hinv0b, hcl0, Nat.le_refl _, hm⟩)

/-- Upgraded `full_preprocess`: caps initial `elim_limit` via `full_min_u64(_, 6000ULL)` against
canonical `Full.fullPreprocessSpec`. -/
theorem m4_preprocess_wp (Γ : Env)
    (hProp : ∀ a m Q X, fullPropagateSpec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X)
    (hSweep : ∀ a m Q X, fullArenaSweepSpec a m Q X → Γ "full_arena_sweep" [i64] [i64] a m Q X)
    (hScale : ∀ a m Q X, schedScaleDeltaSpec a m Q X →
      Γ "full_scale_delta" [i64, i64] [i64] a m Q X)
    (hMin : ∀ a m Q X, schedMinU64Spec a m Q X → Γ "full_min_u64" [i64, i64] [i64] a m Q X)
    (hProbe : ∀ a m Q X, schedProbeSpec a m Q X → Γ "full_probe" [i64, .bool] [i64] a m Q X)
    (hElim : ∀ a m Q X, schedEliminateSpec a m Q X →
      Γ "full_eliminate" [i64, .bool] [i64] a m Q X) :
    ∀ a m Q X, fullPreprocessSpec a m Q X → Func.wp Γ full_preprocess_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hcl0, hm, hQ⟩
  obtain ⟨F_cur, hspW⟩ := hinv.exists_witness
  unfold Func.wp full_preprocess_body
  c0_hsteps; c0_call hProp
  refine ⟨c, F0, F_cur, s, R, rfl, hspW.1, hspW.2.1, hspW.2.2.2.2.2, hm, ?_⟩
  intro pr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 s1
    hlen1 hw1 _ hperm1 hfu1 _ _ hpr1 _ _ hm1
  have hspW1 : FullSparseInvW c F0 F_cur s1 :=
    ⟨hlen1, hw1, ⟨fun v hv => hspW.2.2.1.1 v hv, fun l hl => hspW.2.2.1.2 l hl⟩,
     fun ref href hng => by
       have href0 : ref ∈ fullArenaClauseRefsCore s.core := hperm1.2.1 ▸ href
       obtain ⟨_, hgb, hp⟩ := hperm1.2.2 ref href0
       exact (hp.map (· / 2)).nodup_iff.mpr (hspW.2.2.2.1 ref href0 (hgb.symm.trans hng)),
     hspW.2.2.2.2.1.of_pres ⟨rfl, rfl⟩ fun ref href => by
       change ref ∈ fullArenaClauseRefsCore s1.core; rw [hperm1.2.1]; exact href,
     hspW.2.2.2.2.2⟩
  have hcl1 : s1.core.cur_level = 0 := hcl0
  c0_hsplit
  · c0_hsteps
    exact hQ 20#64 s1 m1 hlen1 (Or.inr (Or.inr (Or.inr rfl))) hfu1
      (fun _ => level0_unsat_of_conflict_okW (s := s1) hw1 hcl1 (hpr1 hc).2.2)
      (fun h => by cases h) (fun h => by cases h) hm1
  c0_hsplit
  · c0_hsteps
    exact hQ 0#64 s1 m1 hlen1 (Or.inl rfl) hfu1 (fun h => by cases h) (fun h => by cases h)
      (fun h => by cases h) hm1
  c0_hsplit
  · c0_hsteps
    exact hQ 0#64 s1 m1 hlen1 (Or.inl rfl) hfu1 (fun h => by cases h) (fun h => by cases h)
      (fun h => by cases h) hm1
  -- Join after `if (h->unflushed > 0ULL)`
  c0_hsteps_nogrp
  refine wp_join_state0 (α := FullState)
    (fun s2 m2 => FullSparseInv c F0 s2 ∧ s2.core.cur_level = 0 ∧
      s2.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c s2 ⋆ R) m2)
    (fun _ s2 m2 ⟨hinv2, hcl2, hfu2, hm2⟩ => by
      c0_hsplit
      · c0_hsteps
        exact hQ 10#64 s2 m2 hinv2.lengths (Or.inr (Or.inr (Or.inl rfl))) hfu2
          (fun h => by cases h) (fun h => by cases h) (fun _ => hinv2.2.2.2.1.2) hm2
      c0_hsteps; c0_call hScale; refine ⟨c, s2, R, rfl, hinv2.lengths, hm2, ?_⟩
      intro plim
      c0_hsteps
      let s2a : FullState := { s2 with scratch := { s2.scratch with probe_limit := plim } }
      have hinv2a : FullSparseInv c F0 s2a :=
        m4_sparseInv_with_scratch_keep hinv2 { hinv2.lengths.scratch_ok with } rfl rfl
      c0_call hScale; refine ⟨c, s2a, R, rfl, hinv2a.lengths, hm, ?_⟩
      intro elim_raw
      c0_hsteps; c0_call hMin; intro elim _
      c0_hsteps
      let s2b : FullState := { s2a with scratch := { s2a.scratch with elim_limit := elim } }
      have hinv2b : FullSparseInv c F0 s2b :=
        m4_sparseInv_with_scratch_keep hinv2a { hinv2a.lengths.scratch_ok with } rfl rfl
      have hfu2b : s2b.core.fuel.toNat ≤ s.core.fuel.toNat := hfu2
      c0_call hProbe; refine ⟨c, F0, s2b, R, rfl, hinv2b, hcl2, hm, ?_⟩
      intro rp s3 m3 hlen3 hfu3 hrp_dom hup3 hsp3 hm3
      have hfu3' : s3.core.fuel.toNat ≤ s.core.fuel.toNat := by omega
      c0_hsteps
      · exact hQ 20#64 s3 m3 hlen3 (Or.inr (Or.inr (Or.inr rfl))) hfu3'
          (fun _ => hup3 hc) (fun h => by cases h) (fun h => by cases h) hm3
      · exact hQ 0#64 s3 m3 hlen3 (Or.inl rfl) hfu3' (fun h => by cases h)
          (fun h => by cases h) (fun h => by cases h) hm3
      · exact hQ 0#64 s3 m3 hlen3 (Or.inl rfl) hfu3' (fun h => by cases h)
          (fun h => by cases h) (fun h => by cases h) hm3
      obtain ⟨hinv3, hcl3⟩ := hsp3 (hrp_dom.resolve_right (by assumption))
      c0_call hElim; refine ⟨c, F0, s3, R, rfl, hinv3, hcl3, hm3, ?_⟩
      intro re s4 m4 hinv4 hcl4 hfu4 _ hue4 hm4
      have hfu4' : s4.core.fuel.toNat ≤ s.core.fuel.toNat := by omega
      c0_hsteps
      · exact hQ 20#64 s4 m4 hinv4.lengths (Or.inr (Or.inr (Or.inr rfl))) hfu4'
          (fun _ => hue4 hc) (fun h => by cases h) (fun h => by cases h) hm4
      · exact hQ 20#64 s4 m4 hinv4.lengths (Or.inr (Or.inr (Or.inr rfl))) hfu4'
          (fun _ => hinv4.inconsistent_unsat hc) (fun h => by cases h) (fun h => by cases h) hm4
      · exact hQ 0#64 s4 m4 hinv4.lengths (Or.inl rfl) hfu4' (fun h => by cases h)
          (fun h => by cases h) (fun h => by cases h) hm4
      · exact hQ 10#64 s4 m4 hinv4.lengths (Or.inr (Or.inr (Or.inl rfl))) hfu4'
          (fun h => by cases h) (fun h => by cases h) (fun _ => hinv4.2.2.2.1.2) hm4
      c0_call hScale; refine ⟨c, s4, R, rfl, hinv4.lengths, hm4, ?_⟩
      intro plim2
      c0_hsteps
      let s4a : FullState := { s4 with scratch := { s4.scratch with probe_limit := plim2 } }
      have hinv4a : FullSparseInv c F0 s4a :=
        m4_sparseInv_with_scratch_keep hinv4 { hinv4.lengths.scratch_ok with } rfl rfl
      c0_call hScale; refine ⟨c, s4a, R, rfl, hinv4a.lengths, hm, ?_⟩
      intro elim2_raw
      c0_hsteps; c0_call hMin; intro elim2 _
      c0_hsteps
      let s4b : FullState := { s4a with scratch := { s4a.scratch with elim_limit := elim2 } }
      have hinv4b : FullSparseInv c F0 s4b :=
        m4_sparseInv_with_scratch_keep hinv4a { hinv4a.lengths.scratch_ok with } rfl rfl
      exact hQ 1#64 s4b _ hinv4b.lengths (Or.inr (Or.inl rfl)) hfu4'
        (fun h => by cases h) (fun _ => ⟨hinv4b, hcl4⟩) (fun h => by cases h) hm)
    (fun Ju hJu => by
      c0_hsplit
      · c0_hsteps; c0_call hSweep
        refine ⟨c, F0, F_cur, s1, R, rfl, hspW1.1, hspW1.2.1, hspW1.2.2.2.1, hspW1.2.2.2.2.2,
          fun hpos => by omega, hm1, ?_⟩
        intro sr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sc1a m1a s1a
          hlen1a _ hext1a _ hll1a hw1a hnd1a _ _ _ hsr2 _ hm1a
        have hspW1a : FullSparseInvW c F0 F_cur s1a :=
          ⟨hlen1a, hw1a, hspW1.2.2.1, hnd1a,
           ⟨hll1a, hext1a.symm ▸ hspW1.2.2.2.2.1.2⟩, hspW1.2.2.2.2.2⟩
        have hcl1a : s1a.core.cur_level = 0 := hcl1
        c0_hsteps
        · exact hQ 20#64 s1a m1a hlen1a (Or.inr (Or.inr (Or.inr rfl))) hfu1
            (fun _ => (hsr2 hc).2) (fun h => by cases h) (fun h => by cases h) hm1a
        c0_call hProp
        refine ⟨c, F0, F_cur, s1a, R, rfl, hspW1a.1, hspW1a.2.1, hspW1a.2.2.2.2.2, hm1a, ?_⟩
        intro pr1b _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fuel1b _ _ _ _ _ _ _ _ m1b s1b
          hlen1b hw1b _ hperm1b hfl1b _ _ hpr1b_1 _ _ hm1b
        have hspW1b : FullSparseInvW c F0 F_cur s1b :=
          ⟨hlen1b, hw1b, hspW1a.2.2.1,
           fun ref href hng => by
             have href0 : ref ∈ fullArenaClauseRefsCore s1a.core := hperm1b.2.1 ▸ href
             obtain ⟨_, hgb, hp⟩ := hperm1b.2.2 ref href0
             exact (hp.map (· / 2)).nodup_iff.mpr (hspW1a.2.2.2.1 ref href0 (hgb.symm.trans hng)),
           hspW1a.2.2.2.2.1.of_pres ⟨rfl, rfl⟩ fun ref href => by
             change ref ∈ fullArenaClauseRefsCore s1b.core; rw [hperm1b.2.1]; exact href,
           hspW1a.2.2.2.2.2⟩
        have hfu1b : s1b.core.fuel.toNat ≤ s.core.fuel.toNat := by
          have h1 : s1a.core.fuel.toNat ≤ s.core.fuel.toNat := hfu1
          dsimp only [s1b]; omega
        c0_hsteps
        · exact hQ 20#64 s1b m1b hlen1b (Or.inr (Or.inr (Or.inr rfl))) hfu1b
            (fun _ => level0_unsat_of_conflict_okW (s := s1b) hw1b hcl1a (hpr1b_1 hc).2.2)
            (fun h => by cases h) (fun h => by cases h) hm1b
        have hspW1c : FullSparseInvW c F0 F_cur
            { s1b with core := { s1b.core with unflushed := 0#64 } } :=
          ⟨⟨{ hspW1b.1.core_ok with }, hspW1b.1.scratch_ok⟩,
           { hspW1b.2.1 with
             arena := { hspW1b.2.1.arena with len_ok := hspW1b.2.1.arena.len_ok }
             watches := hspW1b.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) },
           hspW1b.2.2.1, hspW1b.2.2.2.1, hspW1b.2.2.2.2.1, hspW1b.2.2.2.2.2⟩
        exact hJu _ _ ⟨hspW1c.toSparse, hcl1a, hfu1b, hm⟩
      · c0_hsteps; exact hJu s1 m1 ⟨hspW1.toSparse, hcl1, hfu1, hm1⟩)

end M4Orchestrators

/-! ## 3. Standalone `m4BvaEnv` & `m4Bva_moduleOk` (`10` Upgraded Functions + `23` Externs) -/

/-- Specification table for standalone `m4BvaModule` (`10` upgraded functions + `23` externs). -/
def m4BvaSpecTable : List SpecEntry :=
  [ ⟨"full_bva_hop1", [i64, i32, i32], [i64], fullBvaHop1Spec, true⟩
  , ⟨"full_bva_hop2", [i64, i32, i32], [i64], fullBvaHop2Spec, true⟩
  , ⟨"full_bva_hop3", [i64, i32, i32], [i64], m4BvaHop3Spec, true⟩
  , ⟨"full_bva_pick_cand", [i64, i32, i32], [i32], fullBvaPickCandSpec, true⟩
  , ⟨"full_bva_filter_row", [i64, i32, i32, i32, i32, i32], [i32], m4BvaFilterRowSpec, true⟩
  , ⟨"full_bva_commit", [i64, i32], [.bool], m4BvaCommitSpec, true⟩
  , ⟨"full_bva_try_lit", [i64, i32, i64], [.bool], fullBvaTryLitHeapSpec, true⟩
  , ⟨"full_factor", [i64, i64], [i64], fullFactorHeapSpec, true⟩
  , ⟨"full_eliminate", [i64, .bool], [i64], schedEliminateSpec, true⟩
  , ⟨"full_preprocess", [i64], [i64], fullPreprocessSpec, true⟩
  , ⟨"full_isqrt", [i64], [i64], Full.fullIsqrtSpec, true⟩
  , ⟨"full_ilog10", [i64], [i64], fullIlog10Spec, true⟩
  , ⟨"full_alloc_cl", [i64, i32, i32, .bool], [i64], fullAllocClSpec, true⟩
  , ⟨"full_wstack_defrag", [i64], [], fullWstackDefragSpec, true⟩
  , ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool], fullWatchPushSpec, true⟩
  , ⟨"full_unwatch_large", [i64, i32, i32], [], fullUnwatchLargeSpec, true⟩
  , ⟨"full_add_bin", [i64, i32, i32], [i64], fullAddBinSpec, true⟩
  , ⟨"full_delete_binary", [i64, i32, i32], [], fullDeleteBinarySpec, true⟩
  , ⟨"full_init_fresh_var", [i64, i32], [], fullInitFreshVarHeapSpec, true⟩
  , ⟨"full_bva_match_large", [i64, i32, i32, i32], [.bool], fullBvaMatchLargeSpec, true⟩
  , ⟨"full_bva_scan_cands", [i64, i32, i32, i64], [i32], m4BvaScanCandsSpec, true⟩
  , ⟨"full_fheap_up", [i64, i64, i64, i32], [], fullFheapUpSpec, true⟩
  , ⟨"full_fheap_down", [i64, i64, i64, i32, i32], [], fullFheapDownSpec, true⟩
  , ⟨"full_scale_delta", [i64, i64], [i64], schedScaleDeltaSpec, true⟩
  , ⟨"full_min_u64", [i64, i64], [i64], schedMinU64Spec, true⟩
  , ⟨"full_elim_dticks", [i64, .bool], [i64], schedElimDticksSpec, true⟩
  , ⟨"full_enter_dense", [i64], [.bool], schedEnterDenseSpec, true⟩
  , ⟨"full_forward_sub", [i64, i64], [i64], fullForwardSubFastSpec, true⟩
  , ⟨"full_elim_bve", [i64, i64], [i64], FullM3CongBva.m3ElimBveSpec, true⟩
  , ⟨"full_rebuild_watches", [i64], [i64], fullRebuildWatchesSpec, true⟩
  , ⟨"full_propagate", [i64], [i64], fullPropagateSpec, true⟩
  , ⟨"full_arena_sweep", [i64], [i64], fullArenaSweepSpec, true⟩
  , ⟨"full_probe", [i64, .bool], [i64], schedProbeSpec, true⟩
  ]

/-- Closed specification environment for standalone `m4BvaModule`. -/
def m4BvaEnv : Env := Env.ofTable m4BvaSpecTable

theorem m4BvaSpecTable_names_nodup : (m4BvaSpecTable.map SpecEntry.name).Nodup := by
  decide

theorem m4BvaSpecTable_noExit : ∀ e ∈ m4BvaSpecTable, e.noExit = true := by
  intro e he
  have hall : m4BvaSpecTable.all (fun x => x.noExit) = true := by t_kernel_rfl
  exact List.all_eq_true.mp hall e he

theorem m4BvaEnv_noExit :
    ∀ f as bs xs m Q X X', m4BvaEnv f as bs xs m Q X → m4BvaEnv f as bs xs m Q X' :=
  Env.ofTable_noExit m4BvaSpecTable_noExit

private theorem m4BvaEnv_row_at (i : Nat) (e : SpecEntry)
    (hi : m4BvaSpecTable[i]? = some e := by rfl)
    (hno : ∀ xs m Q X, e.spec xs m Q X → e.eff xs m Q X := by intro _ _ _ _ h; exact h) :
    ∀ xs m Q X, e.spec xs m Q X → m4BvaEnv e.name e.as e.rs xs m Q X :=
  fun xs m Q X h =>
    Env.ofTable_of_mem (List.mem_of_getElem? hi) m4BvaSpecTable_names_nodup (hno xs m Q X h)

private theorem m4Bva_allFns_wf : AllFns Fn.Wf m4BvaModule.fns :=
  ⟨full_bva_hop1_wf, full_bva_hop2_wf, full_bva_hop3_wf, full_bva_pick_cand_wf,
   full_bva_filter_row_wf, full_bva_commit_wf, full_bva_try_lit_wf, full_factor_wf,
   full_eliminate_wf, full_preprocess_wf, trivial⟩

/-- Unconditional standalone `ModuleOk` certifying all `10` upgraded M4d BVA/elim functions. -/
theorem m4Bva_moduleOk : ModuleOk m4BvaEnv m4BvaModule := by
  refine Env.ofTable_moduleOk m4Bva_acyclic m4Bva_allFns_wf ?_
  let hHop1 := m4BvaEnv_row_at 0 ⟨"full_bva_hop1", [i64, i32, i32], [i64], fullBvaHop1Spec, true⟩
  let hHop2 := m4BvaEnv_row_at 1 ⟨"full_bva_hop2", [i64, i32, i32], [i64], fullBvaHop2Spec, true⟩
  let hHop3 := m4BvaEnv_row_at 2 ⟨"full_bva_hop3", [i64, i32, i32], [i64], m4BvaHop3Spec, true⟩
  let hPick := m4BvaEnv_row_at 3
    ⟨"full_bva_pick_cand", [i64, i32, i32], [i32], fullBvaPickCandSpec, true⟩
  let hFilt := m4BvaEnv_row_at 4
    ⟨"full_bva_filter_row", [i64, i32, i32, i32, i32, i32], [i32], m4BvaFilterRowSpec, true⟩
  let hComm := m4BvaEnv_row_at 5 ⟨"full_bva_commit", [i64, i32], [.bool], m4BvaCommitSpec, true⟩
  let hTry := m4BvaEnv_row_at 6
    ⟨"full_bva_try_lit", [i64, i32, i64], [.bool], fullBvaTryLitHeapSpec, true⟩
  let hFact := m4BvaEnv_row_at 7 ⟨"full_factor", [i64, i64], [i64], fullFactorHeapSpec, true⟩
  let hElim := m4BvaEnv_row_at 8 ⟨"full_eliminate", [i64, .bool], [i64], schedEliminateSpec, true⟩
  let hIsqrt := m4BvaEnv_row_at 10 ⟨"full_isqrt", [i64], [i64], Full.fullIsqrtSpec, true⟩
  let hIlog := m4BvaEnv_row_at 11 ⟨"full_ilog10", [i64], [i64], fullIlog10Spec, true⟩
  let hAlloc := m4BvaEnv_row_at 12
    ⟨"full_alloc_cl", [i64, i32, i32, .bool], [i64], fullAllocClSpec, true⟩
  let hDefrag := m4BvaEnv_row_at 13 ⟨"full_wstack_defrag", [i64], [], fullWstackDefragSpec, true⟩
  let hWPush := m4BvaEnv_row_at 14
    ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool], fullWatchPushSpec, true⟩
  let hUnw := m4BvaEnv_row_at 15
    ⟨"full_unwatch_large", [i64, i32, i32], [], fullUnwatchLargeSpec, true⟩
  let hAddB := m4BvaEnv_row_at 16 ⟨"full_add_bin", [i64, i32, i32], [i64], fullAddBinSpec, true⟩
  let hDelB := m4BvaEnv_row_at 17
    ⟨"full_delete_binary", [i64, i32, i32], [], fullDeleteBinarySpec, true⟩
  let hInit := m4BvaEnv_row_at 18
    ⟨"full_init_fresh_var", [i64, i32], [], fullInitFreshVarHeapSpec, true⟩
  let hMatch := m4BvaEnv_row_at 19
    ⟨"full_bva_match_large", [i64, i32, i32, i32], [.bool], fullBvaMatchLargeSpec, true⟩
  let hScan := m4BvaEnv_row_at 20
    ⟨"full_bva_scan_cands", [i64, i32, i32, i64], [i32], m4BvaScanCandsSpec, true⟩
  let hUp := m4BvaEnv_row_at 21
    ⟨"full_fheap_up", [i64, i64, i64, i32], [], fullFheapUpSpec, true⟩
  let hDown := m4BvaEnv_row_at 22
    ⟨"full_fheap_down", [i64, i64, i64, i32, i32], [], fullFheapDownSpec, true⟩
  let hScale := m4BvaEnv_row_at 23
    ⟨"full_scale_delta", [i64, i64], [i64], schedScaleDeltaSpec, true⟩
  let hMin := m4BvaEnv_row_at 24 ⟨"full_min_u64", [i64, i64], [i64], schedMinU64Spec, true⟩
  let hDt := m4BvaEnv_row_at 25
    ⟨"full_elim_dticks", [i64, .bool], [i64], schedElimDticksSpec, true⟩
  let hEnt := m4BvaEnv_row_at 26 ⟨"full_enter_dense", [i64], [.bool], schedEnterDenseSpec, true⟩
  let hFwd := m4BvaEnv_row_at 27
    ⟨"full_forward_sub", [i64, i64], [i64], fullForwardSubFastSpec, true⟩
  let hBve := m4BvaEnv_row_at 28
    ⟨"full_elim_bve", [i64, i64], [i64], FullM3CongBva.m3ElimBveSpec, true⟩
  let hReb := m4BvaEnv_row_at 29
    ⟨"full_rebuild_watches", [i64], [i64], fullRebuildWatchesSpec, true⟩
  let hProp := m4BvaEnv_row_at 30 ⟨"full_propagate", [i64], [i64], fullPropagateSpec, true⟩
  let hSwp := m4BvaEnv_row_at 31 ⟨"full_arena_sweep", [i64], [i64], fullArenaSweepSpec, true⟩
  let hPrb := m4BvaEnv_row_at 32 ⟨"full_probe", [i64, .bool], [i64], schedProbeSpec, true⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
  · exact SpecEntry.Impl.of (m4_bva_hop1_wp m4BvaEnv)
  · exact SpecEntry.Impl.of (m4_bva_hop2_wp m4BvaEnv hHop1)
  · exact SpecEntry.Impl.of (m4_bva_hop3_wp m4BvaEnv hHop2)
  · exact SpecEntry.Impl.of (m4_bva_pick_cand_wp m4BvaEnv hHop3)
  · exact SpecEntry.Impl.of (m4_bva_filter_row_wp m4BvaEnv hMatch)
  · exact SpecEntry.Impl.of
      (m4_bva_commit_wp m4BvaEnv hDefrag hInit hAddB hAlloc hWPush hDelB hUnw)
  · exact SpecEntry.Impl.of (m4_bva_try_lit_wp m4BvaEnv hScan hPick hFilt hComm)
  · exact SpecEntry.Impl.of (m4_factor_wp m4BvaEnv hUp hDown hTry)
  · exact SpecEntry.Impl.of
      (m4_eliminate_wp m4BvaEnv hDt hIlog hIsqrt hScale hEnt hFwd hMin hBve hFact hReb)
  · exact SpecEntry.Impl.of (m4_preprocess_wp m4BvaEnv hProp hSwp hScale hMin hPrb hElim)

/-! ## 4. Closed `204`-Function `m4BvaFullEnv_moduleOk`, Soundness & Non-Vacuity -/

/-- Name-directed spec splice updating the `4` internal BVA helper specs in `FullM3.m3SpecTable`. -/
def m4BvaFullSpecSplice (e : SpecEntry) : SpecEntry :=
  if e.name = "full_bva_hop3" then
    ⟨"full_bva_hop3", [i64, i32, i32], [i64], m4BvaHop3Spec, true⟩
  else if e.name = "full_bva_scan_cands" then
    ⟨"full_bva_scan_cands", [i64, i32, i32, i64], [i32], m4BvaScanCandsSpec, true⟩
  else if e.name = "full_bva_filter_row" then
    ⟨"full_bva_filter_row", [i64, i32, i32, i32, i32, i32], [i32], m4BvaFilterRowSpec, true⟩
  else if e.name = "full_bva_commit" then
    ⟨"full_bva_commit", [i64, i32], [.bool], m4BvaCommitSpec, true⟩
  else e

/-- Complete `204`-row specification table aligned 1-to-1 with `m4BvaFullFns`. -/
def m4BvaFullSpecTable (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) : List SpecEntry :=
  (FullM3.m3SpecTable mainSpec).map m4BvaFullSpecSplice

def mkM4BvaFullEnv (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) : Env :=
  Env.ofTable (m4BvaFullSpecTable mainSpec)

/-- Headline `204`-function UNSAT-only environment for `m4BvaFullModule`. -/
def m4BvaFullEnv : Env := mkM4BvaFullEnv fullSolveBytesSpec

/-- Concrete `204`-function UNSAT non-vacuity environment (`fullUnsatWitnessSpec`, `20#64`). -/
def m4BvaFullUnsatEnv : Env := mkM4BvaFullEnv fullUnsatWitnessSpec

private theorem m4BvaFullSpecSplice_name (e : SpecEntry) :
    (m4BvaFullSpecSplice e).name = e.name := by
  unfold m4BvaFullSpecSplice
  split; · next h => exact h.symm
  split; · next h => exact h.symm
  split; · next h => exact h.symm
  split; · next h => exact h.symm
  rfl

private theorem m4BvaFullSpecSplice_noExit {e : SpecEntry} (h : e.noExit = true) :
    (m4BvaFullSpecSplice e).noExit = true := by
  unfold m4BvaFullSpecSplice
  split; · rfl
  split; · rfl
  split; · rfl
  split; · rfl
  exact h

theorem m4BvaFullSpecTable_noExit (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    ∀ e ∈ m4BvaFullSpecTable mainSpec, e.noExit = true := by
  intro e he
  obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he
  exact m4BvaFullSpecSplice_noExit (FullM3.m3SpecTable_noExit mainSpec e0 he0)

theorem mkM4BvaFullEnv_noExit (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    ∀ f as bs xs m Q X X',
      mkM4BvaFullEnv mainSpec f as bs xs m Q X → mkM4BvaFullEnv mainSpec f as bs xs m Q X' :=
  Env.ofTable_noExit (m4BvaFullSpecTable_noExit mainSpec)

theorem m4BvaFullEnv_noExit :
    ∀ f as bs xs m Q X X', m4BvaFullEnv f as bs xs m Q X → m4BvaFullEnv f as bs xs m Q X' :=
  mkM4BvaFullEnv_noExit fullSolveBytesSpec

theorem m4BvaFullUnsatEnv_noExit :
    ∀ f as bs xs m Q X X',
      m4BvaFullUnsatEnv f as bs xs m Q X → m4BvaFullUnsatEnv f as bs xs m Q X' :=
  mkM4BvaFullEnv_noExit fullUnsatWitnessSpec

private theorem m4BvaFullSpecTable_names_eq (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    (m4BvaFullSpecTable mainSpec).map SpecEntry.name =
      (FullM3.m3SpecTable mainSpec).map SpecEntry.name := by
  unfold m4BvaFullSpecTable
  rw [List.map_map]
  apply List.map_congr_left
  intro e _; exact m4BvaFullSpecSplice_name e

private theorem m4BvaFullSpecTable_nodup (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    ((m4BvaFullSpecTable mainSpec).map SpecEntry.name).Nodup := by
  rw [m4BvaFullSpecTable_names_eq]
  have hs := congrArg (List.map Prod.fst) (FullM3.m3SpecTable_sigs mainSpec)
  simp only [List.map_map, Function.comp_def] at hs
  rw [hs]
  have hchk := FullM3.m3_acyclic
  simp only [FullM3.m3Module, Module.checkAcyclic, Bool.and_eq_true] at hchk
  exact (List.nodup_append.mp (Module.namesNodup_of_checkNamesNodup hchk.1)).1

private theorem ofTable_iff_of_mem {tbl : List SpecEntry} {e : SpecEntry} (he : e ∈ tbl)
    (hnd : (tbl.map SpecEntry.name).Nodup) {xs : Tup Val e.as} {m : Mem 64} {Q : Post e.rs}
    {X : XPost} :
    Env.ofTable tbl e.name e.as e.rs xs m Q X ↔ e.eff xs m Q X := by
  induction tbl with
  | nil => nomatch he
  | cons e' es ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp he with rfl | hmem
    · exact Env.ofTable_cons_self _ _ _ _ _ _
    · have hne : e'.name ≠ e.name := fun h' => hnd.1 (h' ▸ List.mem_map_of_mem hmem)
      exact (Env.ofTable_cons_ne hne _ _ _ _).trans (ih hmem hnd.2)

private theorem ofTable_map_agree {tbl : List SpecEntry} {g : SpecEntry → SpecEntry}
    (hg_name : ∀ e ∈ tbl, (g e).name = e.name)
    {f : Sym} (hg_eq : ∀ e ∈ tbl, e.name = f → g e = e)
    {as bs : List Ty} (xs : Tup Val as) (m : Mem 64) (Q : Post bs) (X : XPost) :
    Env.ofTable (tbl.map g) f as bs xs m Q X ↔ Env.ofTable tbl f as bs xs m Q X := by
  induction tbl with
  | nil => exact Iff.rfl
  | cons e es ih =>
    rw [List.map_cons]
    by_cases hne : e.name = f
    · rw [hg_eq e List.mem_cons_self hne]
      have htail := ih (fun x hx => hg_name x (List.mem_cons_of_mem _ hx))
        (fun x hx => hg_eq x (List.mem_cons_of_mem _ hx))
      unfold Env.ofTable
      exact or_congr Iff.rfl (and_congr Iff.rfl htail)
    · have hne' : (g e).name ≠ f := (hg_name e List.mem_cons_self).symm ▸ hne
      rw [Env.ofTable_cons_ne hne', Env.ofTable_cons_ne hne]
      exact ih (fun x hx => hg_name x (List.mem_cons_of_mem _ hx))
        (fun x hx => hg_eq x (List.mem_cons_of_mem _ hx))

private theorem mkM4BvaFullEnv_row_at {mainSpec : Spec [i64, i64, i64, i64, i64] [i64]}
    (i : Nat) (e : SpecEntry)
    (hi : (m4BvaFullSpecTable mainSpec)[i]? = some e := by rfl)
    (hno : ∀ xs m Q X, e.spec xs m Q X → e.eff xs m Q X := by intro _ _ _ _ h; exact h) :
    ∀ xs m Q X, e.spec xs m Q X → mkM4BvaFullEnv mainSpec e.name e.as e.rs xs m Q X :=
  fun xs m Q X h =>
    Env.ofTable_of_mem (List.mem_of_getElem? hi) (m4BvaFullSpecTable_nodup mainSpec)
      (hno xs m Q X h)

private theorem mkM4BvaFullEnv_row_elim {mainSpec : Spec [i64, i64, i64, i64, i64] [i64]}
    (i : Nat) (e : SpecEntry)
    (hi : (m4BvaFullSpecTable mainSpec)[i]? = some e := by rfl)
    (hno : e.noExit = true := by rfl) {xs : Tup Val e.as} {m : Mem 64} {Q : Post e.rs} {X : XPost}
    (hs : mkM4BvaFullEnv mainSpec e.name e.as e.rs xs m Q X) :
    e.spec xs m Q (fun _ _ _ _ => False) := by
  have heff := (ofTable_iff_of_mem (List.mem_of_getElem? hi)
    (m4BvaFullSpecTable_nodup mainSpec)).mp hs
  simpa only [SpecEntry.eff, hno, ↓reduceIte] using heff

private def m4Respecced4 : List Sym :=
  ["full_bva_hop3", "full_bva_scan_cands", "full_bva_filter_row", "full_bva_commit"]

private def m4Changed11 : List Sym :=
  [ "full_bva_hop1", "full_bva_hop2", "full_bva_hop3", "full_bva_scan_cands"
  , "full_bva_pick_cand", "full_bva_filter_row", "full_bva_commit", "full_bva_try_lit"
  , "full_factor", "full_eliminate", "full_preprocess" ]

private def m4UnchangedAllowed : List SigEntry :=
  (FullM3.m3Fns.filter (fun fn => !m4Respecced4.contains fn.name)).map Fn.sig

private theorem m4Unchanged_callsOk :
    (FullM3.m3Fns.filter (fun fn => !m4Changed11.contains fn.name)).all
      (fun fn => fn.checkCallsOk m4UnchangedAllowed []) = true := by
  t_kernel_rfl

private theorem m4BvaFullEnv_agree_of_not_respecced
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) {f : Sym}
    (hf : m4Respecced4.contains f = false)
    {as bs : List Ty} (xs : Tup Val as) (m : Mem 64) (Q : Post bs) (X : XPost) :
    mkM4BvaFullEnv mainSpec f as bs xs m Q X ↔ FullM3.mkM3Env mainSpec f as bs xs m Q X := by
  refine ofTable_map_agree (fun e _ => m4BvaFullSpecSplice_name e) (fun e _ he => ?_) xs m Q X
  subst he
  have h1 : e.name ≠ "full_bva_hop3" := by intro h; rw [h] at hf; cases hf
  have h2 : e.name ≠ "full_bva_scan_cands" := by intro h; rw [h] at hf; cases hf
  have h3 : e.name ≠ "full_bva_filter_row" := by intro h; rw [h] at hf; cases hf
  have h4 : e.name ≠ "full_bva_commit" := by intro h; rw [h] at hf; cases hf
  simp [m4BvaFullSpecSplice, h1, h2, h3, h4]

private theorem fn_eq_of_mem_nodup {fs : List Fn} (hnd : (fs.map Fn.name).Nodup)
    {f g : Fn} (hf : f ∈ fs) (hg : g ∈ fs) (hnm : f.name = g.name) : f = g := by
  induction fs with
  | nil => nomatch hf
  | cons x xs ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hf with rfl | hf' <;> rcases List.mem_cons.mp hg with rfl | hg'
    · rfl
    · exact absurd (hnm ▸ List.mem_map_of_mem hg') hnd.1
    · exact absurd (hnm.symm ▸ List.mem_map_of_mem hf') hnd.1
    · exact ih hnd.2 hf' hg'

private theorem m3Fns_nodup' : (FullM3.m3Fns.map Fn.name).Nodup := by
  have hchk := FullM3.m3_acyclic
  simp only [FullM3.m3Module, Module.checkAcyclic, Bool.and_eq_true] at hchk
  exact (List.nodup_append.mp (Module.namesNodup_of_checkNamesNodup hchk.1)).1

private def m4ScanCandsFn : Fn :=
  ⟨"full_bva_scan_cands", [i64, i32, i32, i64], [i32], FullBvaHeap.full_bva_scan_cands_body⟩

private theorem m3Fns_180 : FullM3.m3Fns[180]? = some m4ScanCandsFn := by
  rfl

private theorem wp_noExit_lift {Γ : Env} {rs : List Ty} {e : Expr Val Cont rs} {m : Mem 64}
    {Q : Post rs} {X : XPost} (h : wp Γ Q (fun _ _ _ _ => False) e m) :
    wp Γ Q X e m :=
  wp_mono (fun _ _ hq => hq) (fun _ _ _ _ hf => hf.elim) e m h

/-- Unconditional closed `204/204` `ModuleOk` for `m4BvaFullModule` under `mkM4BvaFullEnv`:
transports all `193` unchanged functions directly from `FullM3.mkM3Env_moduleOk` via
`wp_env_agree_of_callsOk`, and discharges all `11` upgraded/re-specced M4d BVA/elim functions. -/
theorem mkM4BvaFullEnv_moduleOk
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hweaken : ∀ a m Q X, mainSpec a m Q X → fullSolveBytesCoreSpec a m Q X) :
    ModuleOk (mkM4BvaFullEnv mainSpec) m4BvaFullModule := by
  let Γ := mkM4BvaFullEnv mainSpec
  let hM3 := FullM3.mkM3Env_moduleOk mainSpec hweaken
  refine Module.moduleOk_of_checkAcyclic m4BvaFull_acyclic m4BvaFullFns_wf ?_
  intro fn hfn
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hfn
  -- Discharge the 10 spliced M4d functions and the 1 re-specced scanner (`full_bva_scan_cands`)
  let hIsqrt := mkM4BvaFullEnv_row_at (mainSpec := mainSpec) 8
    ⟨"full_isqrt", [i64], [i64], Full.fullIsqrtSpec, true⟩
  let hIlog := mkM4BvaFullEnv_row_at (mainSpec := mainSpec) 9
    ⟨"full_ilog10", [i64], [i64], fullIlog10Spec, true⟩
  let hAlloc := mkM4BvaFullEnv_row_at (mainSpec := mainSpec) 12
    ⟨"full_alloc_cl", [i64, i32, i32, .bool], [i64], fullAllocClSpec, true⟩
  let hDefrag := mkM4BvaFullEnv_row_at (mainSpec := mainSpec) 14
    ⟨"full_wstack_defrag", [i64], [], fullWstackDefragSpec, true⟩
  let hWPush := mkM4BvaFullEnv_row_at (mainSpec := mainSpec) 15
    ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool], fullWatchPushSpec, true⟩
  let hProp := mkM4BvaFullEnv_row_at (mainSpec := mainSpec) 50
    ⟨"full_propagate", [i64], [i64], fullPropagateSpec, true⟩
  let hUnw := mkM4BvaFullEnv_row_at (mainSpec := mainSpec) 57
    ⟨"full_unwatch_large", [i64, i32, i32], [], fullUnwatchLargeSpec, true⟩
  let hSwp := mkM4BvaFullEnv_row_at (mainSpec := mainSpec) 61
    ⟨"full_arena_sweep", [i64], [i64], fullArenaSweepSpec, true⟩
  let hAddB := mkM4BvaFullEnv_row_at (mainSpec := mainSpec) 99
    ⟨"full_add_bin", [i64, i32, i32], [i64], fullAddBinSpec, true⟩
  let hDelB := mkM4BvaFullEnv_row_at (mainSpec := mainSpec) 101
    ⟨"full_delete_binary", [i64, i32, i32], [], fullDeleteBinarySpec, true⟩
  let hEnt := mkM4BvaFullEnv_row_at (mainSpec := mainSpec) 127
    ⟨"full_enter_dense", [i64], [.bool], schedEnterDenseSpec, true⟩
  let hReb := mkM4BvaFullEnv_row_at (mainSpec := mainSpec) 128
    ⟨"full_rebuild_watches", [i64], [i64], fullRebuildWatchesSpec, true⟩
  let hFwd := mkM4BvaFullEnv_row_at (mainSpec := mainSpec) 164
    ⟨"full_forward_sub", [i64, i64], [i64], fullForwardSubFastSpec, true⟩
  let hInit := mkM4BvaFullEnv_row_at (mainSpec := mainSpec) 175
    ⟨"full_init_fresh_var", [i64, i32], [], fullInitFreshVarHeapSpec, true⟩
  let hHop1 := mkM4BvaFullEnv_row_at (mainSpec := mainSpec) 176
    ⟨"full_bva_hop1", [i64, i32, i32], [i64], fullBvaHop1Spec, true⟩
  let hHop2 := mkM4BvaFullEnv_row_at (mainSpec := mainSpec) 177
    ⟨"full_bva_hop2", [i64, i32, i32], [i64], fullBvaHop2Spec, true⟩
  let hHop3 := mkM4BvaFullEnv_row_at (mainSpec := mainSpec) 178
    ⟨"full_bva_hop3", [i64, i32, i32], [i64], m4BvaHop3Spec, true⟩
  let hMatch := mkM4BvaFullEnv_row_at (mainSpec := mainSpec) 179
    ⟨"full_bva_match_large", [i64, i32, i32, i32], [.bool], fullBvaMatchLargeSpec, true⟩
  let hScan := mkM4BvaFullEnv_row_at (mainSpec := mainSpec) 180
    ⟨"full_bva_scan_cands", [i64, i32, i32, i64], [i32], m4BvaScanCandsSpec, true⟩
  let hPick := mkM4BvaFullEnv_row_at (mainSpec := mainSpec) 181
    ⟨"full_bva_pick_cand", [i64, i32, i32], [i32], fullBvaPickCandSpec, true⟩
  let hFilt := mkM4BvaFullEnv_row_at (mainSpec := mainSpec) 182
    ⟨"full_bva_filter_row", [i64, i32, i32, i32, i32, i32], [i32], m4BvaFilterRowSpec, true⟩
  let hComm := mkM4BvaFullEnv_row_at (mainSpec := mainSpec) 183
    ⟨"full_bva_commit", [i64, i32], [.bool], m4BvaCommitSpec, true⟩
  let hTry := mkM4BvaFullEnv_row_at (mainSpec := mainSpec) 184
    ⟨"full_bva_try_lit", [i64, i32, i64], [.bool], fullBvaTryLitHeapSpec, true⟩
  let hUp := mkM4BvaFullEnv_row_at (mainSpec := mainSpec) 185
    ⟨"full_fheap_up", [i64, i64, i64, i32], [], fullFheapUpSpec, true⟩
  let hDown := mkM4BvaFullEnv_row_at (mainSpec := mainSpec) 186
    ⟨"full_fheap_down", [i64, i64, i64, i32, i32], [], fullFheapDownSpec, true⟩
  let hFact := mkM4BvaFullEnv_row_at (mainSpec := mainSpec) 187
    ⟨"full_factor", [i64, i64], [i64], fullFactorHeapSpec, true⟩
  let hScale := mkM4BvaFullEnv_row_at (mainSpec := mainSpec) 188
    ⟨"full_scale_delta", [i64, i64], [i64], schedScaleDeltaSpec, true⟩
  let hMin := mkM4BvaFullEnv_row_at (mainSpec := mainSpec) 189
    ⟨"full_min_u64", [i64, i64], [i64], schedMinU64Spec, true⟩
  let hPrb := mkM4BvaFullEnv_row_at (mainSpec := mainSpec) 195
    ⟨"full_probe", [i64, .bool], [i64], schedProbeSpec, true⟩
  let hDt := mkM4BvaFullEnv_row_at (mainSpec := mainSpec) 196
    ⟨"full_elim_dticks", [i64, .bool], [i64], schedElimDticksSpec, true⟩
  let hBve := mkM4BvaFullEnv_row_at (mainSpec := mainSpec) 198
    ⟨"full_elim_bve", [i64, i64], [i64], FullM3CongBva.m3ElimBveSpec, true⟩
  let hElim := mkM4BvaFullEnv_row_at (mainSpec := mainSpec) 199
    ⟨"full_eliminate", [i64, .bool], [i64], schedEliminateSpec, true⟩
  by_cases h1 : f.name = "full_bva_hop1"
  · rw [show m4BvaSplice f = m4Hop1Fn by simp [m4BvaSplice, h1]]
    intro xs m Q X hs
    exact wp_noExit_lift (m4_bva_hop1_wp Γ xs m Q _
      (mkM4BvaFullEnv_row_elim 176 ⟨"full_bva_hop1", [i64, i32, i32], [i64], fullBvaHop1Spec,
        true⟩ rfl rfl hs))
  by_cases h2 : f.name = "full_bva_hop2"
  · rw [show m4BvaSplice f = m4Hop2Fn by simp [m4BvaSplice, h2]]
    intro xs m Q X hs
    exact wp_noExit_lift (m4_bva_hop2_wp Γ hHop1 xs m Q _
      (mkM4BvaFullEnv_row_elim 177 ⟨"full_bva_hop2", [i64, i32, i32], [i64], fullBvaHop2Spec,
        true⟩ rfl rfl hs))
  by_cases h3 : f.name = "full_bva_hop3"
  · rw [show m4BvaSplice f = m4Hop3Fn by simp [m4BvaSplice, h3]]
    intro xs m Q X hs
    exact wp_noExit_lift (m4_bva_hop3_wp Γ hHop2 xs m Q _
      (mkM4BvaFullEnv_row_elim 178 ⟨"full_bva_hop3", [i64, i32, i32], [i64], m4BvaHop3Spec,
        true⟩ rfl rfl hs))
  by_cases h4 : f.name = "full_bva_pick_cand"
  · rw [show m4BvaSplice f = m4PickCandFn by simp [m4BvaSplice, h4]]
    intro xs m Q X hs
    exact wp_noExit_lift (m4_bva_pick_cand_wp Γ hHop3 xs m Q _
      (mkM4BvaFullEnv_row_elim 181 ⟨"full_bva_pick_cand", [i64, i32, i32], [i32],
        fullBvaPickCandSpec, true⟩ rfl rfl hs))
  by_cases h5 : f.name = "full_bva_filter_row"
  · rw [show m4BvaSplice f = m4FilterRowFn by simp [m4BvaSplice, h5]]
    intro xs m Q X hs
    exact wp_noExit_lift (m4_bva_filter_row_wp Γ hMatch xs m Q _
      (mkM4BvaFullEnv_row_elim 182 ⟨"full_bva_filter_row", [i64, i32, i32, i32, i32, i32], [i32],
        m4BvaFilterRowSpec, true⟩ rfl rfl hs))
  by_cases h6 : f.name = "full_bva_commit"
  · rw [show m4BvaSplice f = m4CommitFn by simp [m4BvaSplice, h6]]
    intro xs m Q X hs
    exact wp_noExit_lift (m4_bva_commit_wp Γ hDefrag hInit hAddB hAlloc hWPush hDelB hUnw xs m Q _
      (mkM4BvaFullEnv_row_elim 183 ⟨"full_bva_commit", [i64, i32], [.bool], m4BvaCommitSpec,
        true⟩ rfl rfl hs))
  by_cases h7 : f.name = "full_bva_try_lit"
  · rw [show m4BvaSplice f = m4TryLitFn by simp [m4BvaSplice, h7]]
    intro xs m Q X hs
    exact wp_noExit_lift (m4_bva_try_lit_wp Γ hScan hPick hFilt hComm xs m Q _
      (mkM4BvaFullEnv_row_elim 184 ⟨"full_bva_try_lit", [i64, i32, i64], [.bool],
        fullBvaTryLitHeapSpec, true⟩ rfl rfl hs))
  by_cases h8 : f.name = "full_factor"
  · rw [show m4BvaSplice f = m4FactorFn by simp [m4BvaSplice, h8]]
    intro xs m Q X hs
    exact wp_noExit_lift (m4_factor_wp Γ hUp hDown hTry xs m Q _
      (mkM4BvaFullEnv_row_elim 187 ⟨"full_factor", [i64, i64], [i64], fullFactorHeapSpec,
        true⟩ rfl rfl hs))
  by_cases h9 : f.name = "full_eliminate"
  · rw [show m4BvaSplice f = m4EliminateFn by simp [m4BvaSplice, h9]]
    intro xs m Q X hs
    exact wp_noExit_lift
      (m4_eliminate_wp Γ hDt hIlog hIsqrt hScale hEnt hFwd hMin hBve hFact hReb xs m Q _
        (mkM4BvaFullEnv_row_elim 199 ⟨"full_eliminate", [i64, .bool], [i64], schedEliminateSpec,
          true⟩ rfl rfl hs))
  by_cases h10 : f.name = "full_preprocess"
  · rw [show m4BvaSplice f = m4PreprocessFn by simp [m4BvaSplice, h10]]
    intro xs m Q X hs
    exact wp_noExit_lift (m4_preprocess_wp Γ hProp hSwp hScale hMin hPrb hElim xs m Q _
      (mkM4BvaFullEnv_row_elim 200 ⟨"full_preprocess", [i64], [i64], fullPreprocessSpec,
        true⟩ rfl rfl hs))
  -- Not spliced: `m4BvaSplice f = f`
  have hsp_eq : m4BvaSplice f = f := by
    simp [m4BvaSplice, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
  rw [hsp_eq]
  by_cases h11 : f.name = "full_bva_scan_cands"
  · have hfeq : f = m4ScanCandsFn :=
      fn_eq_of_mem_nodup m3Fns_nodup' hf (List.mem_of_getElem? m3Fns_180) h11
    subst hfeq
    intro xs m Q X hs
    exact wp_noExit_lift (m4_bva_scan_cands_wp Γ xs m Q _
      (mkM4BvaFullEnv_row_elim 180 ⟨"full_bva_scan_cands", [i64, i32, i32, i64], [i32],
        m4BvaScanCandsSpec, true⟩ rfl rfl hs))
  -- All 193 remaining unchanged functions: transport from `FullM3.mkM3Env_moduleOk`
  intro xs m Q X hs
  have hnot_chg : m4Changed11.contains f.name = false := by
    simp [m4Changed11, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
  have hnot_rsp : m4Respecced4.contains f.name = false := by
    simp [m4Respecced4, h3, h5, h6, h11]
  have hmem_filt : f ∈ FullM3.m3Fns.filter (fun fn => !m4Changed11.contains fn.name) :=
    List.mem_filter.mpr ⟨hf, by rw [hnot_chg]; rfl⟩
  have hcalls : f.callsOk m4UnchangedAllowed [] :=
    Fn.callsOk_of_checkCallsOk (List.all_eq_true.mp m4Unchanged_callsOk f hmem_filt)
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hf
  have ⟨hwf, _, hwp0⟩ := hM3.fnsOk pre f post hsplit
  have hs0 : FullM3.mkM3Env mainSpec f.name f.as f.rs xs m Q X :=
    (m4BvaFullEnv_agree_of_not_respecced mainSpec hnot_rsp xs m Q X).mp hs
  refine wp_env_agree_of_callsOk (hwf Val (fun _ => Unit) Cont (fun _ => Unit) xs (Tup.units f.as))
    hcalls (fun g as bs hmem ys m' P E hG => ?_) m (hwp0 xs m Q X hs0)
  obtain ⟨fn', hfn', hsig⟩ := List.mem_map.mp hmem
  have hfn'_f := (List.mem_filter.mp hfn').2
  have hg_nr : m4Respecced4.contains g = false := by
    have hgn : fn'.name = g := congrArg Prod.fst hsig
    rw [← hgn]; simpa using hfn'_f
  exact (m4BvaFullEnv_agree_of_not_respecced mainSpec hg_nr ys m' P E).mpr hG

/-- Unconditional `ModuleOk m4BvaFullEnv m4BvaFullModule` (`204/204`, UNSAT-only). -/
theorem m4BvaFullEnv_moduleOk : ModuleOk m4BvaFullEnv m4BvaFullModule :=
  mkM4BvaFullEnv_moduleOk fullSolveBytesSpec (fun _ _ _ _ => fullSolveBytesCoreSpec_of_spec)

/-- Unconditional `ModuleOk m4BvaFullUnsatEnv m4BvaFullModule` (`204/204`, concrete UNSAT). -/
theorem m4BvaFullUnsatEnv_moduleOk : ModuleOk m4BvaFullUnsatEnv m4BvaFullModule :=
  mkM4BvaFullEnv_moduleOk fullUnsatWitnessSpec
    (fun _ _ _ _ => fullSolveBytesCoreSpec_of_unsatWitness)

/-- Headline source-level UNSAT-only soundness of M4d `kissat_solve_bytes` under closed
`204`-function `m4BvaFullEnv` (`0` SAT/model proofs). -/
theorem m4_bva_solve_bytes_correct
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8} {wlen : Nat}
    {R : Mem 64 → Prop} {m : Mem 64} {X : XPost}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp m4BvaFullEnv Full.kissat_solve_bytes_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun (r, ()) m' =>
        (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
        (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m') X :=
  FullFastSched.sched_kissat_solve_bytes_wp m4BvaFullEnv
    (mkM4BvaFullEnv_row_at (mainSpec := fullSolveBytesSpec) 41
      ⟨"full_init_state", [i64, i64, i64, i64, i64], [.bool], fullInitStateSpec, true⟩)
    (mkM4BvaFullEnv_row_at (mainSpec := fullSolveBytesSpec) 44
      ⟨"full_parse_body", [i64, i64], [i64], fullParseBodySpec, true⟩)
    (mkM4BvaFullEnv_row_at (mainSpec := fullSolveBytesSpec) 200
      ⟨"full_preprocess", [i64], [i64], fullPreprocessSpec, true⟩)
    (mkM4BvaFullEnv_row_at (mainSpec := fullSolveBytesSpec) 202
      ⟨"full_search", [i64], [i64], fullSearchSpec, true⟩)
    (mkM4BvaFullEnv_row_at (mainSpec := fullSolveBytesSpec) 97
      ⟨"full_extend", [i64], [], fullExtendSpec, true⟩)
    (mkM4BvaFullEnv_row_at (mainSpec := fullSolveBytesSpec) 7
      ⟨"kissat_check_model", [i64, i64, i64, i64, i64], [i64], kissatCheckModelExactSpec, true⟩)
    _ m _ X
    ⟨cnfBytes, wlen, R, rfl, rfl, hcfit, hwfit, hm, fun _ _ hdom hu hm' => ⟨hdom, hu, hm'⟩⟩

/-! ## 5. Concrete `Mem 64` UNSAT Non-Vacuity (`XPost := False`, `0` SAT proofs) -/

section ConcreteUnsatNonVacuity

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) under closed `204`-function
`m4BvaFullUnsatEnv`: `kissat_solve_bytes` returns `20#64` and proves `fullNvUnsatCnf.Unsat` on
`fullNvUnsatBytes` with `4096`-byte workspace and `fuel = 16`. -/
theorem m4_bva_unsat_nonvacuous :
    let m0 : Mem 64 := (fullPayload fullNvUnsatBytes).At fullNvCnfPtr
    Func.wp m4BvaFullUnsatEnv Full.kissat_solve_bytes_body
      (fullNvCnfPtr, BitVec.ofNat 64 fullNvUnsatBytes.length,
        fullNvWorkPtr fullNvUnsatBytes, 4096#64, 16#64, ()) m0
      (fun (r, ()) m' =>
        r = 20#64 ∧ fullNvUnsatCnf.Unsat ∧
        (bytes fullNvCnfPtr fullNvUnsatBytes ⋆
          region (fullNvWorkPtr fullNvUnsatBytes) 4096 ⋆ emp) m')
      (fun _ _ _ _ => False) :=
  FullFastSched.sched_kissat_solve_bytes_core_wp m4BvaFullUnsatEnv
    (mkM4BvaFullEnv_row_at (mainSpec := fullUnsatWitnessSpec) 41
      ⟨"full_init_state", [i64, i64, i64, i64, i64], [.bool], fullInitStateSpec, true⟩)
    (mkM4BvaFullEnv_row_at (mainSpec := fullUnsatWitnessSpec) 44
      ⟨"full_parse_body", [i64, i64], [i64], fullParseBodySpec, true⟩)
    (mkM4BvaFullEnv_row_at (mainSpec := fullUnsatWitnessSpec) 200
      ⟨"full_preprocess", [i64], [i64], fullPreprocessSpec, true⟩)
    (mkM4BvaFullEnv_row_at (mainSpec := fullUnsatWitnessSpec) 202
      ⟨"full_search", [i64], [i64], fullSearchSpec, true⟩)
    (mkM4BvaFullEnv_row_at (mainSpec := fullUnsatWitnessSpec) 97
      ⟨"full_extend", [i64], [], fullExtendSpec, true⟩)
    (mkM4BvaFullEnv_row_at (mainSpec := fullUnsatWitnessSpec) 7
      ⟨"kissat_check_model", [i64, i64, i64, i64, i64], [i64], kissatCheckModelExactSpec, true⟩)
    _ _ _ _
    (fullSolveBytesCoreSpec_of_unsatWitness
      ⟨emp, by decide, by decide, rfl, rfl, rfl, by decide, by decide,
        by rw [sep_emp]; exact fullPayload_sep fullNvUnsatBytes (by decide),
        fun _ huns hm' => ⟨rfl, huns, hm'⟩⟩)

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_factor` (`full_bva_m4`). -/
theorem nv_m4_factor :
    Func.wp m4BvaEnv full_factor_body
      (nvOneLitCfg.hdr, 10#64, ()) nvBvaDenseMem
      (fun (r, ()) m' => ∃ s',
        FullDenseInv nvOneLitCfg nvOneLitF0 s' ∧ r = 1#64 ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvOneLitCfg nvBvaDenseState ⋆ emp) nvBvaDenseMem := by
    rw [sep_emp]; exact nvBvaDenseMem_ok
  exact m4_factor_wp m4BvaEnv
    (m4BvaEnv_row_at 21 ⟨"full_fheap_up", [i64, i64, i64, i32], [], fullFheapUpSpec, true⟩)
    (m4BvaEnv_row_at 22 ⟨"full_fheap_down", [i64, i64, i64, i32, i32], [], fullFheapDownSpec, true⟩)
    (m4BvaEnv_row_at 6 ⟨"full_bva_try_lit", [i64, i32, i64], [.bool], fullBvaTryLitHeapSpec, true⟩)
    _ _ _ _
    ⟨nvOneLitCfg, nvOneLitF0, nvBvaDenseState, emp, rfl, nvBvaDense_invW.toDense, hm,
      fun r s' m' hd _ _ hr hm' => by
        rw [sep_emp] at hm'; exact ⟨s', hd, hr, nvDeduceF0_unsat, hm'⟩⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_bva_try_lit`. -/
theorem nv_m4_bva_try_lit :
    Func.wp m4BvaEnv full_bva_try_lit_body
      (nvOneLitCfg.hdr, 0#32, 1#64, ()) nvBvaDenseMem
      (fun (_ok, ()) m' => ∃ s',
        FullDenseInv nvOneLitCfg nvOneLitF0 s' ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvOneLitCfg nvBvaDenseState ⋆ emp) nvBvaDenseMem := by
    rw [sep_emp]; exact nvBvaDenseMem_ok
  exact m4_bva_try_lit_wp m4BvaEnv
    (m4BvaEnv_row_at 20 ⟨"full_bva_scan_cands", [i64, i32, i32, i64], [i32],
      m4BvaScanCandsSpec, true⟩)
    (m4BvaEnv_row_at 3 ⟨"full_bva_pick_cand", [i64, i32, i32], [i32], fullBvaPickCandSpec, true⟩)
    (m4BvaEnv_row_at 4 ⟨"full_bva_filter_row", [i64, i32, i32, i32, i32, i32], [i32],
      m4BvaFilterRowSpec, true⟩)
    (m4BvaEnv_row_at 5 ⟨"full_bva_commit", [i64, i32], [.bool], m4BvaCommitSpec, true⟩)
    _ _ _ _
    ⟨nvOneLitCfg, nvOneLitF0, nvBvaDenseState, emp, rfl, nvBvaDense_invW.toDense, by decide, hm,
      fun _ s' m' hd _ _ _ _ hm' => by
        rw [sep_emp] at hm'; exact ⟨s', hd, nvDeduceF0_unsat, hm'⟩⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for shared-cache `full_bva_hop3`. -/
theorem nv_m4_bva_hop3 :
    Func.wp m4BvaEnv full_bva_hop3_body
      (nvOneLitCfg.hdr, 0#32, 0#32, ()) nvBvaDenseMem
      (fun (_r, ()) m' => ∃ s',
        FullDenseInvNoLm nvOneLitCfg nvOneLitF0 [[0], [1]] s' ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvOneLitCfg nvBvaDenseState ⋆ emp) nvBvaDenseMem := by
    rw [sep_emp]; exact nvBvaDenseMem_ok
  exact m4_bva_hop3_wp m4BvaEnv
    (m4BvaEnv_row_at 1 ⟨"full_bva_hop2", [i64, i32, i32], [i64], fullBvaHop2Spec, true⟩)
    _ _ _ _
    ⟨nvOneLitCfg, nvOneLitF0, [[0], [1]], nvBvaDenseState, emp, rfl,
      FullDenseInvW.toNoLm nvBvaDense_invW, by decide, Nat.zero_le _, Nat.zero_le _,
      (fun _ h => by simp [nvBvaDenseState, nvOneLitState] at h),
      (fun _ h => by simp [nvBvaDenseState, nvOneLitState] at h), hm,
      fun _ _ _ _ _ _ _ _ m' hnl _ _ _ _ _ hm' => by
        rw [sep_emp] at hm'; exact ⟨_, hnl, nvDeduceF0_unsat, hm'⟩⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_bva_pick_cand`. -/
theorem nv_m4_bva_pick_cand :
    Func.wp m4BvaEnv full_bva_pick_cand_body
      (nvOneLitCfg.hdr, 0#32, 0#32, ()) nvBvaDenseMem
      (fun (r, ()) m' => ∃ s',
        FullDenseInvNoLm nvOneLitCfg nvOneLitF0 [[0], [1]] s' ∧
        (r = 0xFFFFFFFF#32 ∨ r.toNat < 2) ∧ nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvOneLitCfg nvBvaDenseState ⋆ emp) nvBvaDenseMem := by
    rw [sep_emp]; exact nvBvaDenseMem_ok
  exact m4_bva_pick_cand_wp m4BvaEnv
    (m4BvaEnv_row_at 2 ⟨"full_bva_hop3", [i64, i32, i32], [i64], m4BvaHop3Spec, true⟩)
    _ _ _ _
    ⟨nvOneLitCfg, nvOneLitF0, [[0], [1]], nvBvaDenseState, emp, rfl,
      FullDenseInvW.toNoLm nvBvaDense_invW, by decide, by decide, fun _ h => by simp at h, hm,
      fun r _ _ _ _ _ _ _ _ m' hnl hr hm' => by
        rw [sep_emp] at hm'; exact ⟨_, hnl, hr, nvDeduceF0_unsat, hm'⟩⟩

end ConcreteUnsatNonVacuity

end LeanQbe.T.Examples.Kissat.FullM4Bva
