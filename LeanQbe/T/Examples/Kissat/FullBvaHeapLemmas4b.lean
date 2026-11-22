module

public import LeanQbe.T.Examples.Kissat.FullBvaHeapCommitSpec
import LeanQbe.T.Logic.ControlComb
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Full` 3-Hop BVA — Matrix Commit Deletion & Tail Sub-Proofs (`Part 4b`)
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

theorem commit_del_loop_wp {Γ : Env} {Q : Post [.bool]} {X : XPost}
    (hDelBin : ∀ args m Q X, Full.fullDeleteBinarySpec args m Q X →
      Γ "full_delete_binary" [i64, i32, i32] [] args m Q X)
    (hUnwatch : ∀ args m Q X, Full.fullUnwatchLargeSpec args m Q X →
      Γ "full_unwatch_large" [i64, i32, i32] [] args m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur F_next : List (List Nat)} {s st1 : FullState}
    {R : Mem 64 → Prop} {best_k mi : Val i32} {Jm : Cont [i32]} {m1 : Mem 64}
    (hinv : FullDenseInvW c F0 F_cur s)
    (hbk1 : 1 ≤ best_k.toNat) (hbk16 : best_k.toNat < 16)
    (hmat : BvaMatrixInv c F_cur s (best_k.toNat + 1))
    (hmi_lt : mi.toNat < (s.scratch.scratch_buf[16 + best_k.toNat]?.getD 0#32).toNat)
    (hm1 : (FullMem c st1 ⋆ R) m1) (hinv1 : FullDenseInvW c F0 F_next st1)
    (hcv1 : st1.core.cur_vars = s.core.cur_vars + 1)
    (hfuel1 : st1.core.fuel = s.core.fuel)
    (hsb1 : st1.scratch.scratch_buf = s.scratch.scratch_buf)
    (htm1 : st1.scratch.tarjan_mark = s.scratch.tarjan_mark)
    (htr1 : st1.scratch.tarjan_reach = s.scratch.tarjan_reach)
    (hmono1 : ArenaMono s.core st1.core)
    (hNext : ∀ st2 m2,
      FullDenseInvW c F0 F_next st2 →
      st2.core.cur_vars = s.core.cur_vars + 1 → st2.core.fuel = s.core.fuel →
      st2.scratch.scratch_buf = s.scratch.scratch_buf →
      st2.scratch.tarjan_mark = s.scratch.tarjan_mark →
      st2.scratch.tarjan_reach = s.scratch.tarjan_reach →
      ArenaMono s.core st2.core → (FullMem c st2 ⋆ R) m2 →
      Jm (mi + 1#32, ()) m2) :
    wp Γ Q X (commitDelLoopExpr c.hdr c.pArena c.pScratchBuf c.pFlags best_k mi Jm) m1 := by
  have hmx := c.hmaxv; have har_b := c.harena; have hscr_b := c.hscr
  unfold dimacsBound at hmx har_b hscr_b
  have hcl := hinv.1.core_ok; have hsc := hinv.1.scratch_ok
  have hcv_le := hcl.cur_vars_le; have hsb_len := hsc.scratch_buf_len
  have hscr2304 := hmat.1
  let old_cv := s.core.cur_vars
  dsimp only [commitDelLoopExpr, eSteps, eStep, eLoad64, eGrp0_0, eGrp0_1, eThen, eElse,
    full_bva_commit_body]
  refine wp_join_group
    (fun (_ : Tup Val [i32, i32]) m2 => ∃ st2 : FullState,
      (FullMem c st2 ⋆ R) m2 ∧ FullDenseInvW c F0 F_next st2 ∧
      st2.core.cur_vars = old_cv + 1 ∧ st2.core.fuel = s.core.fuel ∧
      st2.scratch.scratch_buf = s.scratch.scratch_buf ∧
      st2.scratch.tarjan_mark = s.scratch.tarjan_mark ∧
      st2.scratch.tarjan_reach = s.scratch.tarjan_reach ∧ ArenaMono s.core st2.core)
    (fun _ _ m2 ⟨st2, hm2, hinv2, hcv2, hfuel2, hsb2, htm2, htr2, hmono2⟩ => by
      c0_hsteps
      exact hNext st2 m2 hinv2 hcv2 hfuel2 hsb2 htm2 htr2 hmono2 hm2)
    (fun Jdel hJdel => ?_)
  refine wp_loop_inv
    (fun (idx, sv, ()) msv => ∃ stv : FullState,
      sv.toNat ≤ best_k.toNat ∧
      idx.toNat < (s.scratch.scratch_buf[16 + sv.toNat]?.getD 0#32).toNat ∧
      FullDenseInvW c F0 F_next stv ∧ stv.core.cur_vars = old_cv + 1 ∧
      stv.core.fuel = s.core.fuel ∧ stv.scratch.scratch_buf = s.scratch.scratch_buf ∧
      stv.scratch.tarjan_mark = s.scratch.tarjan_mark ∧
      stv.scratch.tarjan_reach = s.scratch.tarjan_reach ∧
      ArenaMono s.core stv.core ∧ (FullMem c stv ⋆ R) msv)
    (fun (_, sv, _) _ => sv.toNat)
    (fun Jd hJd => by
      c0_hsteps
      exact hJd (mi, best_k, ()) m1 ⟨st1, Nat.le_refl _, hmi_lt,
        hinv1, hcv1, hfuel1, hsb1, htm1, htr1, hmono1, hm1⟩)
    (fun Jd (idx, sv, ()) msv ⟨stv, hsv_le, hidx_lt, hinvv, hcvv, hfuelv, hsbv, htmv, htrv,
        hmonov, hmsv⟩ ihd => ?_)
  have hclv := hinvv.1.core_ok; have hscv := hinvv.1.scratch_ok
  have hsv_row := hmat.2.2.2 sv.toNat (by omega)
  obtain ⟨hfsv_lt, hqsv_lo, hqsv_hi, hsv_entries⟩ := hsv_row
  obtain ⟨resv, _, _, hcs_ok, _, hpar_ok⟩ := hsv_entries idx.toNat hidx_lt
  have hcs_idx : (64 + sv * 64 + idx).toNat = 64 + sv.toNat * 64 + idx.toNat := by
    change (64#32 + sv * 64#32 + idx).toNat = _; c0_bound
  have hcs_sb : (BitVec.setWidth 64 (64 + sv * 64 + idx)).toNat <
      stv.scratch.scratch_buf.length := by
    rw [bv64_setWidth_32, hcs_idx, hscv.scratch_buf_len]; omega
  have hsv_sb : (BitVec.setWidth 64 sv).toNat < stv.scratch.scratch_buf.length := by
    rw [bv64_setWidth_32, hscv.scratch_buf_len]; omega
  let cs := s.scratch.scratch_buf[64 + sv.toNat * 64 + idx.toNat]'(by omega)
  have hcs_eq : stv.scratch.scratch_buf[(BitVec.setWidth 64
      (64 + sv * 64 + idx)).toNat]'hcs_sb = cs := by
    dsimp only [cs]; simp only [hsbv, bv64_setWidth_32, hcs_idx]
  have hcs_mod_n : (64 + sv.toNat * 64 + idx.toNat) % 2 ^ 32 = 64 + sv.toNat * 64 + idx.toNat :=
    Nat.mod_eq_of_lt (by omega)
  have hcs_mod : stv.scratch.scratch_buf[(BitVec.toNat (64 : BitVec 32) +
      sv.toNat * BitVec.toNat (64 : BitVec 32) + idx.toNat) % 2 ^ 32]'(by
      rw [show BitVec.toNat (64 : BitVec 32) = 64 from rfl, hcs_mod_n,
        hscv.scratch_buf_len]; omega) = cs := by
    dsimp only [cs]; simp only [hsbv, show BitVec.toNat (64 : BitVec 32) = 64 from rfl, hcs_mod_n]
  have hcs_getD : s.scratch.scratch_buf[64 + sv.toNat * 64 + idx.toNat]?.getD 0#32 = cs := by
    dsimp only [cs]; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
  rw [hcs_getD] at hcs_ok
  c0_hsteps_nogrp
  · refine wp_join_state0 (α := FullState)
      (fun stc mc =>
        (FullMem c stc ⋆ R) mc ∧ FullDenseInvW c F0 F_next stc ∧
        stc.core.cur_vars = old_cv + 1 ∧ stc.core.fuel = s.core.fuel ∧
        stc.scratch.scratch_buf = s.scratch.scratch_buf ∧
        stc.scratch.tarjan_mark = s.scratch.tarjan_mark ∧
        stc.scratch.tarjan_reach = s.scratch.tarjan_reach ∧ ArenaMono s.core stc.core)
      (fun _ stc mc ⟨hmc, hinvc, hcvc, hfuelc, hsbc, htmc, htrc, hmonoc⟩ => ?_)
      (fun Jcs hJcs => ?_)
    · -- Check `if (sv == 0) break; else idx = scr[1088 + sv * 64 + idx]; sv = sv - 1;`
      have hscc := hinvc.1.scratch_ok
      c0_hsteps
      · exact hJdel (idx, sv, ()) mc ⟨stc, hmc, hinvc, hcvc, hfuelc, hsbc, htmc, htrc, hmonoc⟩
      · have hsv_pos : 0 < sv.toNat := by c0_bound
        have hsv1 : (sv - 1#32).toNat = sv.toNat - 1 := by c0_bound
        have hpar_idx : (1088 + sv * 64 + idx).toNat = 1088 + sv.toNat * 64 + idx.toNat := by
          change (1088#32 + sv * 64#32 + idx).toNat = _; c0_bound
        have hpar_sb : (BitVec.setWidth 64 (1088 + sv * 64 + idx)).toNat <
            stc.scratch.scratch_buf.length := by
          rw [bv64_setWidth_32, hpar_idx, hscc.scratch_buf_len]; omega
        have hpi_lt := (hpar_ok hsv_pos).1
        c0_hsteps
        refine ihd (_, sv - 1#32, ()) mc (by dsimp only; rw [hsv1]; omega)
          ⟨stc, by rw [hsv1]; omega, ?_, hinvc, hcvc, hfuelc, hsbc, htmc, htrc, hmonoc, hmc⟩
        rw [hsv1]
        have h1 : stc.scratch.scratch_buf[(BitVec.setWidth 64
            (1088 + sv * 64 + idx)).toNat]'hpar_sb =
            s.scratch.scratch_buf[1088 + sv.toNat * 64 + idx.toNat]?.getD 0#32 := by
          have heq : stc.scratch.scratch_buf[(BitVec.setWidth 64
              (1088 + sv * 64 + idx)).toNat]? =
              s.scratch.scratch_buf[1088 + sv.toNat * 64 + idx.toNat]? := by
            rw [hsbc, bv64_setWidth_32, hpar_idx]
          rw [← heq, List.getElem?_eq_getElem hpar_sb, Option.getD_some]
        rw [h1]; exact hpi_lt
    · -- Delete binary or large `cs`
      c0_hsteps
      · -- Binary `cs`: `full_delete_binary(h, fs, q); fl[q >> 1] |= ...`
        have hbin_cs : (cs &&& 0x80000000#32) ≠ 0#32 := by
          simpa only [← hcs_mod] using (by assumption : _)
        unfold BvaRowEntryOk at hcs_ok; rw [ite_eq_left hbin_cs] at hcs_ok
        have hq_lt : (cs &&& 0x7FFFFFFF#32).toNat < 2 * old_cv := hcs_ok.1
        c0_call hDelBin
        refine ⟨c, stv, R, rfl, hinvv.1, hinvv.2.1.watches.layout, hmsv,
          fun wvec' wstk' wu' nb' md1 hlen_d _ hwat_d hmd1 => ?_⟩
        have hinv_d := fullDenseInvW_of_delBin hinvv hlen_d (hwat_d F_next hinvv.2.1.watches)
        have hq_shr : (BitVec.setWidth 64 ((stv.scratch.scratch_buf[(BitVec.setWidth 64
            (64 + sv * 64 + idx)).toNat]'hcs_sb &&& 0x7FFFFFFF#32) >>> (1 : BitVec 32))).toNat <
            stv.core.flags.length := by
          rw [bv64_setWidth_32, hcs_eq, bv32_lshr1_bv, hclv.flags_len]; omega
        have hq_shr_n : (BitVec.setWidth 64 ((stv.scratch.scratch_buf[(BitVec.setWidth 64
            (64 + sv * 64 + idx)).toNat]'hcs_sb &&& 0x7FFFFFFF#32) >>> (1 : Nat))).toNat <
            stv.core.flags.length := by
          rw [bv64_setWidth_32, hcs_eq, bv32_lshr1_nat, hclv.flags_len]; omega
        c0_hsteps
        all_goals
          exact hJcs _ m ⟨hm, fullDenseInvW_set_flags hinv_d (by simp [hlen_d.core_ok.flags_len]),
            hcvv, hfuelv, hsbv, htmv, htrv, hmonov⟩
      · -- Large `cs`: `unwatch_large` loop, then `ar[cs] |= PH_GARB; arena_garbage += 3+csz`
        have hbin_cs : (cs &&& 0x80000000#32) = 0#32 := by
          simpa only [← hcs_mod] using (by assumption : _)
        unfold BvaRowEntryOk at hcs_ok; rw [ite_eq_right (fun h' => h' hbin_cs)] at hcs_ok
        obtain ⟨hcs_ref0, hcs_ng0, hcs_sz3, hcs_sz5, _, _, _⟩ := hcs_ok
        obtain ⟨hcs_refv, hcs_szv, hcs_litsv⟩ := hmonov cs.toNat hcs_ref0
        have hcs_wfv := hinvv.2.1.arena.refs_wf cs.toNat hcs_refv
        have hcs2_n : (BitVec.setWidth 64 cs + 2).toNat = cs.toNat + 2 := by
          change (BitVec.setWidth 64 cs + 2#64).toNat = _; c0_bound
        have hcs_b2_sb : (BitVec.setWidth 64 (stv.scratch.scratch_buf[(BitVec.setWidth 64
            (64 + sv * 64 + idx)).toNat]'hcs_sb) + 2).toNat < stv.core.arena.length := by
          rw [hcs_eq, hcs2_n]; have := hclv.arena_len_le; have := hclv.arena_len_arr; omega
        have hcsz_eq : (stv.core.arena[cs.toNat + 2]'(by
            have := hclv.arena_len_le; have := hclv.arena_len_arr; omega)).toNat =
            fullArenaClauseSizeCore s.core cs.toNat := by
          rw [← hcs_szv]; unfold fullArenaClauseSizeCore
          rw [List.getElem?_eq_getElem (by
            have := hclv.arena_len_le; have := hclv.arena_len_arr; omega), Option.getD_some]
        let csz_bv := stv.core.arena[cs.toNat + 2]'(by
          have := hclv.arena_len_le; have := hclv.arena_len_arr; omega)
        have hcsz_s : csz_bv.toNat = fullArenaClauseSizeCore s.core cs.toNat := hcsz_eq
        c0_hsteps_nogrp
        refine wp_loop_inv
          (fun (k, ()) mk => ∃ stk : FullState,
            k.toNat ≤ csz_bv.toNat ∧ FullDenseInvW c F0 F_next stk ∧
            stk.core.cur_vars = old_cv + 1 ∧ stk.core.fuel = s.core.fuel ∧
            stk.core.arena = stv.core.arena ∧ stk.core.arena_len = stv.core.arena_len ∧
            stk.scratch.scratch_buf = s.scratch.scratch_buf ∧
            stk.scratch.tarjan_mark = s.scratch.tarjan_mark ∧
            stk.scratch.tarjan_reach = s.scratch.tarjan_reach ∧
            ArenaMono s.core stk.core ∧ (FullMem c stk ⋆ R) mk)
          (fun (k, _) _ => csz_bv.toNat - k.toNat)
          (fun Jk hJk => by
            c0_hsteps
            exact hJk (0#32, ()) msv ⟨stv, Nat.zero_le _, hinvv, hcvv, hfuelv, rfl, rfl,
              hsbv, htmv, htrv, hmonov, hmsv⟩)
          (fun Jk (k, ()) mk ⟨stk, hk_le, hinvk, hcvk, hfuelk, hark, halk, hsbk, htmk, htrk,
              hmonok, hmk⟩ ihk => ?_)
        have hclk := hinvk.1.core_ok
        c0_hsteps
        · have hcs2_mod : (cs.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64 = cs.toNat + 2 := by
            rw [show BitVec.toNat (2 : BitVec 64) = 2 from rfl]; omega
          have hk_lt : k.toNat < csz_bv.toNat := by
            dsimp only [csz_bv]
            have h1 : k.toNat < (stv.core.arena[(cs.toNat + BitVec.toNat (2 : BitVec 64)) %
                2 ^ 64]'(by
                  rw [hcs2_mod]
                  have := hclv.arena_len_le; have := hclv.arena_len_arr; omega)).toNat :=
              by simpa only [← hcs_mod] using (by assumption : _)
            simpa only [hcs2_mod] using h1
          have hk1 : (k + 1#32).toNat = k.toNat + 1 := by c0_bound
          have hcsk_n : (BitVec.setWidth 64 cs + 3 + BitVec.setWidth 64 k).toNat =
              cs.toNat + 3 + k.toNat := by
            change (BitVec.setWidth 64 cs + 3#64 + BitVec.setWidth 64 k).toNat = _; c0_bound
          have hdl_ar : cs.toNat + 3 + k.toNat < stk.core.arena.length := by
            have := hclv.arena_len_le; have := hclv.arena_len_arr; rw [hark]; omega
          have hdl_ar_sb : (BitVec.setWidth 64 (stv.scratch.scratch_buf[(BitVec.setWidth 64
              (64 + sv * 64 + idx)).toNat]'hcs_sb) + 3 + BitVec.setWidth 64 k).toNat <
              stk.core.arena.length := by rw [hcs_eq, hcsk_n]; exact hdl_ar
          have hdl_mem : (stk.core.arena[cs.toNat + 3 + k.toNat]'hdl_ar).toNat ∈
              fullArenaClauseLitsCore s.core cs.toNat := by
            rw [← hcs_litsv]
            have h1 := FullBvaFwdHelpers.fullArenaClauseLitsCore_getElem (k := stv.core)
              (r := cs.toNat) (j := k.toNat) (by rw [hcs_szv]; omega)
              (by rw [← hark]; exact hdl_ar)
            have h2 := List.mem_of_getElem? h1
            simpa only [hark] using h2
          have hdl_lt : (stk.core.arena[cs.toNat + 3 + k.toNat]'hdl_ar).toNat < 2 * old_cv :=
            hinv.2.1.arena.lits_lt cs.toNat hcs_ref0 hcs_ng0 _ hdl_mem
          c0_hsteps
          c0_call hUnwatch
          refine ⟨c, stk, R, rfl, hinvk.1, hinvk.2.1.watches.layout, hmk,
            fun wvec' wstk' wu' mu hlen_u _ hwat_u hmu => ?_⟩
          have hinv_u := fullDenseInvW_of_unwatchLarge hinvk hlen_u
            (hwat_u F_next hinvk.2.1.watches)
          have hdl_shr : (BitVec.setWidth 64 ((stk.core.arena[(BitVec.setWidth 64
              (stv.scratch.scratch_buf[(BitVec.setWidth 64 (64 + sv * 64 + idx)).toNat]'hcs_sb) +
              3 + BitVec.setWidth 64 k).toNat]'hdl_ar_sb) >>> (1 : BitVec 32))).toNat <
              stk.core.flags.length := by
            rw [bv64_setWidth_32, hclk.flags_len]
            simp only [hcs_eq, hcsk_n, bv32_lshr1_bv]; omega
          have hdl_shr_n : (BitVec.setWidth 64 ((stk.core.arena[(BitVec.setWidth 64
              (stv.scratch.scratch_buf[(BitVec.setWidth 64 (64 + sv * 64 + idx)).toNat]'hcs_sb) +
              3 + BitVec.setWidth 64 k).toNat]'hdl_ar_sb) >>> (1 : Nat))).toNat <
              stk.core.flags.length := by
            rw [bv64_setWidth_32, hclk.flags_len]
            simp only [hcs_eq, hcsk_n, bv32_lshr1_nat]; omega
          c0_hsteps
          all_goals
            exact ihk (k + 1#32, ()) m (by dsimp only; rw [hk1]; omega)
              ⟨_, by rw [hk1]; omega,
               fullDenseInvW_set_flags hinv_u (by simp [hlen_u.core_ok.flags_len]),
               hcvk, hfuelk, hark, halk, hsbk, htmk, htrk, hmonok, hm⟩
        · -- Exit `k < csz` -> `ar[cs] |= PH_GARB; arena_garbage += 3 + csz`
          have hcs_refk : cs.toNat ∈ fullArenaClauseRefsCore stk.core :=
            (hmonok cs.toNat hcs_ref0).1
          have hcs_lt_k : cs.toNat < stk.core.arena.length := by
            have := hclv.arena_len_le; have := hclv.arena_len_arr; rw [hark]; omega
          have hcs_lt_sb : (BitVec.setWidth 64 (stv.scratch.scratch_buf[(BitVec.setWidth 64
              (64 + sv * 64 + idx)).toNat]'hcs_sb)).toNat < stk.core.arena.length := by
            rw [hcs_eq, bv64_setWidth_32]; exact hcs_lt_k
          c0_hsteps
          have ⟨hinv_g, hmono_g⟩ := fullDenseInvW_of_markGarb hinvk hcs_refk
            (stk.core.arena_garbage + 3#64 + BitVec.setWidth 64
              (stv.core.arena[(BitVec.setWidth 64 cs + 2).toNat]'(by
                rw [hcs2_n]; have := hclv.arena_len_le; have := hclv.arena_len_arr; omega)))
          have hm_g : (FullMem c { stk with
              core := { stk.core with
                arena := stk.core.arena.set cs.toNat
                  (fullArenaHdrCore stk.core cs.toNat ||| 0x00080000#32)
                arena_garbage := stk.core.arena_garbage + 3#64 + BitVec.setWidth 64
                  (stv.core.arena[(BitVec.setWidth 64 cs + 2).toNat]'(by
                    rw [hcs2_n]; have := hclv.arena_len_le; have := hclv.arena_len_arr
                    omega)) } } ⋆ R) m := by
            have hhdr : fullArenaHdrCore stk.core cs.toNat =
                stk.core.arena[cs.toNat]'hcs_lt_k := by
              unfold fullArenaHdrCore
              rw [List.getElem?_eq_getElem hcs_lt_k, Option.getD_some]
            rw [hhdr]
            simp only [hcs_eq] at hm
            simp only [bv64_setWidth_32] at hm
            exact hm
          exact hJcs _ m ⟨hm_g, hinv_g, hcvk, hfuelk, hsbk, htmk, htrk,
            arenaMono_trans hmonok hmono_g⟩
  · cases (by assumption : true = false)


theorem commit_tail_wp {Γ : Env} {Q : Post [.bool]} {X : XPost}
    (hAddBin : ∀ args m Q X, Full.fullAddBinSpec args m Q X →
      Γ "full_add_bin" [i64, i32, i32] [i64] args m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_next : List (List Nat)} {s stm : FullState}
    {R : Mem 64 → Prop} {best_k dm_bv fresh : Val i32} {mm : Mem 64}
    (hbk16 : best_k.toNat < 16) (hscr2304 : 2304 ≤ c.scratch_cap)
    (hdm_eq : dm_bv.toNat = best_k.toNat + 1)
    (hfresh_nat : fresh.toNat = 2 * s.core.cur_vars)
    (hL_lt : ∀ t < best_k.toNat + 1,
      (s.scratch.scratch_buf[t]?.getD 0#32).toNat < 2 * s.core.cur_vars)
    (hpos_ent : ∀ t < best_k.toNat + 1,
      (cnfOfClauses F_next).EntailsClause
        (cnfClause [2 * s.core.cur_vars, (s.scratch.scratch_buf[t]?.getD 0#32).toNat]))
    (hinvm : FullDenseInvW c F0 F_next stm)
    (hcvm : stm.core.cur_vars = s.core.cur_vars + 1) (hfuelm : stm.core.fuel = s.core.fuel)
    (hsbm : stm.scratch.scratch_buf = s.scratch.scratch_buf)
    (htmm : stm.scratch.tarjan_mark = s.scratch.tarjan_mark)
    (htrm : stm.scratch.tarjan_reach = s.scratch.tarjan_reach)
    (hmm : (FullMem c stm ⋆ R) mm)
    (hQ : ∀ (ok : Bool) (s' : FullState) (m' : Mem 64),
      FullDenseInv c F0 s' → s.core.cur_vars ≤ s'.core.cur_vars →
      s'.core.fuel = s.core.fuel →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    wp Γ Q X (commitTailExpr c.hdr c.pScratchBuf c.pWsort c.pFlags best_k dm_bv fresh) mm := by
  have hmx := c.hmaxv; have hscr_b := c.hscr; unfold dimacsBound at hmx hscr_b
  let old_cv := s.core.cur_vars; let dm := best_k.toNat + 1
  have hcv_le := hinvm.1.core_ok.cur_vars_le
  dsimp only [commitTailExpr, eSteps, eStep, eLet32, eLoad64, eGrp0_0, eGrp0_1, eElse,
    full_bva_commit_body]
  refine wp_loop_inv
    (fun (si, ()) msi => ∃ sts : FullState,
      si.toNat ≤ dm ∧ FullDenseInvW c F0 F_next sts ∧
      sts.core.cur_vars = old_cv + 1 ∧ sts.core.fuel = s.core.fuel ∧
      sts.scratch.scratch_buf = s.scratch.scratch_buf ∧
      sts.scratch.tarjan_mark = s.scratch.tarjan_mark ∧
      sts.scratch.tarjan_reach = s.scratch.tarjan_reach ∧ (FullMem c sts ⋆ R) msi)
    (fun (si, _) _ => dm - si.toNat)
    (fun Js hJs => by
      c0_hsteps; exact hJs (0#32, ()) mm ⟨stm, Nat.zero_le _, hinvm, hcvm, hfuelm, hsbm,
        htmm, htrm, hmm⟩)
    (fun Js (si, ()) msi ⟨sts, hsi_le, hinvs, hcvs, hfuels, hsbs, htms, htrs, hmsi⟩ ihs => ?_)
  have hcls := hinvs.1.core_ok; have hscs := hinvs.1.scratch_ok
  c0_hsteps
  · have hsi_lt : si.toNat < dm := by
      have h1 : si.toNat < dm_bv.toNat := by assumption
      omega
    have hsi1 : (si + 1#32).toNat = si.toNat + 1 := by simp only [bv_c0]; omega
    have hfs_sb : (BitVec.setWidth 64 si).toNat < sts.scratch.scratch_buf.length := by
      rw [bv64_setWidth_32, hscs.scratch_buf_len]; omega
    have hfs_getD : (sts.scratch.scratch_buf[(BitVec.setWidth 64 si).toNat]'hfs_sb).toNat =
        (s.scratch.scratch_buf[si.toNat]?.getD 0#32).toNat := by
      have h1 : sts.scratch.scratch_buf[(BitVec.setWidth 64 si).toNat]? =
          s.scratch.scratch_buf[si.toNat]? := by rw [hsbs, bv64_setWidth_32]
      rw [← h1, List.getElem?_eq_getElem hfs_sb, Option.getD_some]
    have hfs_lt : (sts.scratch.scratch_buf[(BitVec.setWidth 64 si).toNat]'hfs_sb).toNat <
        2 * old_cv := by rw [hfs_getD]; exact hL_lt si.toNat hsi_lt
    c0_hsteps
    c0_call hAddBin
    refine ⟨c, F0, F_next, sts, R, rfl, hinvs.1, hinvs.2.1, hinvs.2.2.2.2.2.1,
      fun _ _ => by rw [hfresh_nat, hfs_getD]; exact hpos_ent si.toNat hsi_lt, hmsi,
      fun _ _ fl_s1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ms1 hlen_s1 hw_s1 _ _ _ hms1 => ?_⟩
    have hinv_s1 := fullDenseInvW_of_addBin hinvs hlen_s1 hw_s1
    have hfs_shr : (BitVec.setWidth 64 ((sts.scratch.scratch_buf[(BitVec.setWidth 64
        si).toNat]'hfs_sb) >>> (1 : BitVec 32))).toNat < fl_s1.length := by
      rw [bv64_setWidth_32, bv32_lshr1_bv, hlen_s1.core_ok.flags_len]; omega
    have hfs_shr_n : (BitVec.setWidth 64 ((sts.scratch.scratch_buf[(BitVec.setWidth 64
        si).toNat]'hfs_sb) >>> (1 : Nat))).toNat < fl_s1.length := by
      rw [bv64_setWidth_32, bv32_lshr1_nat, hlen_s1.core_ok.flags_len]; omega
    c0_hsteps
    exact ihs (si + 1#32, ()) m (by dsimp only; rw [hsi1]; omega)
      ⟨_, by rw [hsi1]; omega,
       fullDenseInvW_set_flags hinv_s1 (by simp [hlen_s1.core_ok.flags_len]),
       hcvs, hfuels, hsbs, htms, htrs, hm⟩
  · -- Cleanup `cnt[0..2*cur_vars) = 0`, `bva_cnt++`, `return true`
    have h2cv :
        (BitVec.ofNat 64 sts.core.cur_vars <<< (1 : Nat)).toNat = 2 * (old_cv + 1) := by
      rw [hcvs]; simp only [bv_c0]; omega
    refine wp_loop_inv
      (fun (zi, ()) mzi => ∃ wsz : List (BitVec 32),
        zi.toNat ≤ 2 * (old_cv + 1) ∧ wsz.length = 2 * c.max_vars ∧
        (FullMem c { sts with scratch := { sts.scratch with wsort := wsz } } ⋆ R) mzi)
      (fun (zi, _) _ => 2 * (old_cv + 1) - zi.toNat)
      (fun Jz hJz => by
        c0_hsteps; exact hJz (0#64, ()) msi ⟨sts.scratch.wsort, Nat.zero_le _, hscs.wsort_len,
          hmsi⟩)
      (fun Jz (zi, ()) mzi ⟨wsz, hzi_le, hwsz_l, hmzi⟩ ihz => ?_)
    c0_hsteps
    · have hzi_lt : zi.toNat < 2 * (old_cv + 1) := by
        have h1 : zi.toNat < (BitVec.ofNat 64 sts.core.cur_vars <<< (1 : Nat)).toNat :=
          by assumption
        rwa [h2cv] at h1
      have hzi1 : (zi + 1#64).toNat = zi.toNat + 1 := by simp only [bv_c0]; omega
      c0_hsteps
      exact ihz (zi + 1#64, ()) m (by dsimp only; rw [hzi1]; omega)
        ⟨_, by rw [hzi1]; omega, by simp [hwsz_l], hm⟩
    · c0_hsteps
      have hinv_fin := fullDenseInv_with_core_aux (tc' := sts.core.tmp_cnt)
        (tl' := sts.core.tmp_len)
        (sc' := { sts.scratch with wsort := wsz, bva_cnt := sts.scratch.bva_cnt + 1#64 })
        hinvs hcls.repr_len hcls.min_clr_len_arr hcls.tmp_len_arr hcls.flags_len
        hcls.tmp_len_le { hscs with wsort_len := hwsz_l } rfl rfl
      exact hQ true _ m hinv_fin.toDense (by dsimp only; omega) hfuels htms htrs hm


end LeanQbe.T.Examples.Kissat.FullBvaHeap
