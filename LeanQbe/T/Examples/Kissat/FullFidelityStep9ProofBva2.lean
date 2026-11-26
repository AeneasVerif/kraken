/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep9
public import LeanQbe.T.Examples.Kissat.FullFidelityStep9ProofBva0
public import LeanQbe.T.Examples.Kissat.FullFidelityStep9ProofBva1
public import LeanQbe.T.Examples.Kissat.FullFidelityStep7Proof2a0
public import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullM4BvaLemmas2
import LeanQbe.T.Examples.Kissat.FullBvaFwdLemmas1
import LeanQbe.T.Examples.Kissat.FullBvaHeapLemmas3
import LeanQbe.T.Examples.Kissat.FullBvaFwdLemmas
import LeanQbe.T.Examples.Kissat.FullAnalyzeLemmas5
import LeanQbe.T.Examples.Kissat.FullPropDecLemmas
import LeanQbe.T.Examples.Kissat.FullBridgeLemmas3
import LeanQbe.T.Examples.Kissat.FullIngestLemmas2
import LeanQbe.T.Logic.C0Agrees
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Fidelity Step-9 BVA Commit WP Proofs — Part 2 (`FullFidelityStep9ProofBva2`)

Parametric `(Γ : Env)` WP proofs (`0` `import all`, `public section`, `0` `@[expose]` on
theorems/lemmas, `XPost`-polymorphic) for Step-9 `FullFidelityStep9.full_bva_commit_body` Phase 1:
- `s9_phase1b_wp`
- `s9_post_defrag_wp`
- `s9_pre_exit_wp`
-/

set_option autoImplicit false

local elab "c0_hsteps_np" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { pruneJnz := false } 10000
local elab "c0_hstep_np" : tactic => LeanQbe.T.C0HeadStep.headSteps { pruneJnz := false } 1
local elab "c0_hsteps_nogrp_np" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { unrollGroup := false, pruneJnz := false } 10000

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep9

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.C0Step LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Full
open FullArenaTactics
open FullBvaHeap FullBvaHeap.FullBvaHeapHelpers FullBvaHeap.FullBvaHeapTactics
open FullBvaHeap.FullBvaHeapScanHelpers FullM4Bva
open LeanQbe.T.Examples.Kissat.FullFidelityBva
open LeanQbe.T.Examples.Kissat.FullFidelityStep7
open LeanQbe.T.Examples.Kissat.FullFidelityStep7Proof2a
open scoped FullArenaTactics FullBvaHeapTactics

@[local bv_c0] private theorem bv64_one_toNat : (1 : BitVec 64).toNat = 1 := rfl
@[local bv_c0] private theorem bv32_one_toNat : (1 : BitVec 32).toNat = 1 := rfl
@[local bv_c0] private theorem bv64_two_toNat : (2 : BitVec 64).toNat = 2 := rfl
@[local bv_c0] private theorem bv64_three_toNat : (3 : BitVec 64).toNat = 3 := rfl

/-! ## 1. Phase 1b Negative Clauses & Deferred Rollback Flush -/

private theorem s9_phase1b_wp {Γ : Env} {Q : Post [.bool]} {X : XPost}
    (hFillU64 : FidFillU64Hyp Γ)
    (hAddBin : FidAddBinHyp Γ) (hAllocCl : FidAllocClHyp Γ) (hWPush : FidWPushHyp Γ)
    (hDelBin : FidDelBinHyp Γ) (hUnwatch : FidUnwatchHyp Γ)
    {c : FullCfg} {F0 : CNF Nat} {F_cur F_next : List (List Nat)} {s st1a : FullState}
    {R : Mem 64 → Prop} {best_k sc dm_bv brow_off mn_bv fresh : Val i32}
    {dd1a ok1a : Val .bool} {m1a : Mem 64} {bump : Nat}
    (hinv : FullDenseInvW c F0 F_cur s)
    (hbk1 : 1 ≤ best_k.toNat) (hbk_sc : best_k.toNat < fidStepsCap c.scratch_cap)
    (hmat : FidBvaMatrixInv c F_cur s (best_k.toNat + 1) bump)
    (hlay : Step7BvaLayout c s (best_k.toNat + 1))
    (hres : s.scratch.res_sz = BitVec.ofNat 64 best_k.toNat)
    (hsc_eq : sc.toNat = fidStepsCap c.scratch_cap)
    (hbo_getD : (s.scratch.scratch_buf[sc.toNat + best_k.toNat]?.getD 0#32).toNat = brow_off.toNat)
    (hmn_getD : (s.scratch.scratch_buf[2 * sc.toNat + best_k.toNat]?.getD 0#32).toNat = mn_bv.toNat)
    (hfresh_nat : fresh.toNat = 2 * s.core.cur_vars)
    (hfresh1 : (fresh ^^^ 1#32).toNat = 2 * s.core.cur_vars + 1)
    (resAt : Nat → List Nat)
    (hresAt : ∀ idx < mn_bv.toNat,
      (∀ x ∈ resAt idx, x < 2 * s.core.cur_vars) ∧ ((resAt idx).map (· / 2)).Nodup ∧
      FidBvaRowEntryOk F_cur s (s.scratch.scratch_buf[best_k.toNat]?.getD 0#32).toNat
        (s.scratch.scratch_buf[brow_off.toNat + idx]?.getD 0#32) (resAt idx) ∧
      (cnfOfClauses F_next).EntailsClause (cnfClause ((2 * s.core.cur_vars + 1) :: resAt idx)))
    (hst1a : S7StOk c F0 F_next s st1a) (hm1a : (FullMem c st1a ⋆ R) m1a)
    (hQ : ∀ ok s' m', FullDenseInv c F0 s' → s.core.cur_vars ≤ s'.core.cur_vars →
      (ok = true → s.core.cur_vars < s'.core.cur_vars) →
      (ok = true → Step7BvaCommittedOk c s' best_k.toNat) → s'.core.fuel = s.core.fuel →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach → (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    wp Γ Q X (s9Phase1bExpr c.hdr c.pArena c.pScratchBuf c.pWsort c.pFlags c.pWvec c.pRepr
      c.pTmp best_k sc dm_bv brow_off mn_bv fresh dd1a ok1a) m1a := by
  have hmx := c.hmaxv; have hwcap := c.hwcap; have har_b := c.harena; have hscr_b := c.hscr
  unfold dimacsBound at hmx hwcap har_b hscr_b
  have hcl := hinv.1.core_ok; have hsc := hinv.1.scratch_ok
  have hcv_le := hcl.cur_vars_le; have hsb_len := hsc.scratch_buf_len
  let old_cv := s.core.cur_vars
  have hsc_pos := hmat.1; have hbump_ge := hmat.2.2.2.1; have hbump_le := hmat.2.2.2.2.1
  have hsc4 := fidStepsCap_mul4_le c.scratch_cap
  have hbk_row := hmat.2.2.2.2.2 best_k.toNat (by omega)
  obtain ⟨hfbk_lt, hro_ge, hmn_lo, hro_mn, _, hbk_entries⟩ := hbk_row
  rw [← hsc_eq] at hro_ge hmn_lo hro_mn hbk_entries
  rw [hbo_getD] at hro_ge hro_mn hbk_entries
  rw [hmn_getD] at hmn_lo hro_mn hbk_entries
  have heq1b : ∀ ok_v : Val .bool,
      s9Phase1bExpr c.hdr c.pArena c.pScratchBuf c.pWsort c.pFlags c.pWvec c.pRepr c.pTmp
        best_k sc dm_bv brow_off mn_bv fresh dd1a ok_v =
      s9Phase1bExpr c.hdr c.pArena c.pScratchBuf c.pWsort c.pFlags c.pWvec c.pRepr c.pTmp
        best_k sc dm_bv brow_off mn_bv fresh dd1a ok_v := fun _ => rfl
  conv at heq1b =>
    intro ok_v; rhs
    unfold s9Phase1bExpr s9PostDefragExpr s9MidExpr s9PreMidExpr s9HdrExpr
    delta FullFidelityStep9.full_bva_commit_body
    dsimp only [sSteps, sStep, sLet32, sLd64, sLd32, sCall32, sGrpb, sGrp64_32, sGrp64_64_32,
      sGrp32bb, sThen, sElse, sDummyTup, sDummyVal, i64, i32]
  refine (congrArg (fun e => wp Γ Q X e m1a) (heq1b ok1a)).mpr ?_
  refine wp_join_group (ts := [i32, .bool, .bool, i64, i64])
    (fun (_, _, _ok1b, _, _, ()) m1b => ∃ st1b : FullState,
      S7StOk c F0 F_next s st1b ∧ (FullMem c st1b ⋆ R) m1b)
    (fun _ (mi1b, dd1b, ok1b, ga1b, ir1b, ()) m1b ⟨st1b, hst1b, hm1b⟩ => ?_)
    (fun J1b hJ1b => ?_)
  · c0_hsplit
    · have hp2 := s9_phase2_wp (Γ := Γ) (Q := Q) (X := X) hFillU64 hDelBin hUnwatch
        (F_next := F_next) (dm_bv := dm_bv) (brow_off := brow_off) (mn_bv := mn_bv)
        (fresh := fresh) (mi0 := mi1b) (dd1a := dd1a) (dd1b := dd1b)
        (garb_add0 := ga1b) (irred_add0 := ir1b)
        hinv hbk1 hbk_sc hmat hlay hres hsc_eq hmn_getD hfresh_nat
        hfresh1 hst1b hm1b hQ
      unfold s9Phase2Expr at hp2
      replace hp2 := (congrArg (fun e => wp Γ Q X
        (e |> sGrp32bb6464 (fun (_ : Tup Val [i32, .bool, .bool, i64, i64]) (_ : Mem 64) => True)
          mi1b dd1b true ga1b ir1b |> sThen) m1b) (heq1b true)).mp hp2
      dsimp only [sGrp32bb6464, sThen, sDummyTup, sDummyVal, i64, i32] at hp2
      exact hp2
    · clear heq1b
      refine wp_join0
        (fun mg => ∃ stg : FullState, S7StOk c F0 F_next s stg ∧ (FullMem c stg ⋆ R) mg)
        (fun _ mg ⟨stg, hstg, hmg⟩ => ?_) (fun Jg hJg => ?_)
      · refine wp_join0
          (fun mi_m => ∃ sti : FullState, S7StOk c F0 F_next s sti ∧ (FullMem c sti ⋆ R) mi_m)
          (fun _ mi_m ⟨sti, hsti, hmi_m⟩ => ?_) (fun Ji hJi => ?_)
        · obtain ⟨hinvi, hcvi, hfueli, hsbi, htmi, htri, hmonoi, hresi⟩ := hsti
          have hcli := hinvi.1.core_ok; have hsci := hinvi.1.scratch_ok
          refine wp_join_state0 (α := List (BitVec 32))
            (fun wsz mzi => wsz.length = 2 * c.max_vars ∧
              (FullMem c { sti with scratch := { sti.scratch with wsort := wsz } } ⋆ R) mzi)
            (fun _ wsz mzi ⟨hwsz_l, hmzi⟩ => by
              c0_hsteps
              exact hQ false _ mzi (s9_fullDenseInvW_set_wsort hinvi hwsz_l).toDense
                (by dsimp only; omega) (fun h => absurd h (by decide))
                (fun h => absurd h (by decide)) hfueli htmi htri hmzi)
            (fun Jw hJw => by
              c0_hsplit
              · c0_hsteps_nogrp
                refine s9_call_fill_u64_wsort hFillU64 hsci.wsort_len hcli.cur_vars_le
                  rfl rfl (by decide) hmi_m fun ws' m' hws'_l hm' => ?_
                c0_hstep; exact hJw ws' m' ⟨hws'_l, hm'⟩
              · c0_hstep; exact hJw sti.scratch.wsort mi_m ⟨hsci.wsort_len, hmi_m⟩)
        · obtain ⟨hinvg, hcvg, hfuelg, hsbg, htmg, htrg, hmonog, hresg⟩ := hstg
          c0_hsplit
          · c0_hsteps
            exact hJi m
              ⟨{ stg with core := { stg.core with num_irred := stg.core.num_irred + ir1b } },
               ⟨s9_fullDenseInvW_with_num_irred hinvg _, hcvg, hfuelg, hsbg, htmg, htrg, hmonog,
                hresg⟩, hm⟩
          · c0_hstep
            exact hJi mg
              ⟨stg, ⟨hinvg, hcvg, hfuelg, hsbg, htmg, htrg, hmonog, hresg⟩, hmg⟩
      · obtain ⟨hinv1b, hcv1b, hfuel1b, hsb1b, htm1b, htr1b, hmono1b, hres1b⟩ := hst1b
        c0_hsplit
        · c0_hsteps
          exact hJg m
            ⟨{ st1b with core :=
                { st1b.core with arena_garbage := st1b.core.arena_garbage + ga1b } },
             ⟨s9_fullDenseInvW_with_garb hinv1b _, hcv1b, hfuel1b, hsb1b, htm1b, htr1b, hmono1b,
              hres1b⟩, hm⟩
        · c0_hstep
          exact hJg m1b
            ⟨st1b, ⟨hinv1b, hcv1b, hfuel1b, hsb1b, htm1b, htr1b, hmono1b, hres1b⟩, hm1b⟩
  · clear heq1b
    refine wp_loop_inv
      (fun (mi, _ddm, okm, _gam, _iam, ()) mm => ∃ stm : FullState, mi.toNat ≤ mn_bv.toNat ∧
        S7StOk c F0 F_next s stm ∧ (FullMem c stm ⋆ R) mm)
      (fun (mi, _, _, _, _, _) _ => mn_bv.toNat - mi.toNat) (fun J1bl hJ1bl => by
        c0_hsteps; exact hJ1bl (0#32, dd1a, ok1a, 0#64, 0#64, ()) m1a
          ⟨st1a, Nat.zero_le _, hst1a, hm1a⟩)
      (fun J1bl (mi, ddm, okm, ga, ia, ()) mm ⟨stm, hmi_le, hstm, hmm⟩ ihm => ?_)
    obtain ⟨hinvm, hcvm, hfuelm, hsbm, htmm, htrm, hmono, hresm⟩ := hstm
    have hclm := hinvm.1.core_ok; have hscm := hinvm.1.scratch_ok; c0_hsteps_nogrp
    · have hmi_lt : mi.toNat < mn_bv.toNat := by assumption
      have hokm_t : okm = true := by assumption
      subst hokm_t; have hmi1 : (mi + 1#32).toNat = mi.toNat + 1 := by c0_bound
      have hctop_idx : (brow_off + mi).toNat = brow_off.toNat + mi.toNat := by
        have h1 : (brow_off + mi).toNat = (brow_off + mi : BitVec 32).toNat := rfl
        rw [h1, BitVec.toNat_add]; apply Nat.mod_eq_of_lt; omega
      have hctop_sb : (BitVec.setWidth 64 (brow_off + mi)).toNat <
          stm.scratch.scratch_buf.length := by
        rw [bv64_setWidth_32, hctop_idx, hscm.scratch_buf_len]; omega
      let c_top := s.scratch.scratch_buf[brow_off.toNat + mi.toNat]'(by omega)
      have hctop_eq : stm.scratch.scratch_buf[(BitVec.setWidth 64
          (brow_off + mi)).toNat]'hctop_sb = c_top := by
        dsimp only [c_top]; simp only [hsbm, bv64_setWidth_32, hctop_idx]
      have hctop_mod_n : (brow_off.toNat + mi.toNat) % 2 ^ 32 =
          brow_off.toNat + mi.toNat := Nat.mod_eq_of_lt (by omega)
      have hctop_mod : stm.scratch.scratch_buf[(brow_off.toNat + mi.toNat) % 2 ^ 32]'(by
          rw [hctop_mod_n, hscm.scratch_buf_len]; omega) = c_top := by
        dsimp only [c_top]; simp only [hsbm, hctop_mod_n]
      obtain ⟨hresm_lt, hresm_nd, hctop_ok0, hresm_ent⟩ := hresAt mi.toNat hmi_lt
      let resm := resAt mi.toNat
      have hctop_getD : s.scratch.scratch_buf[brow_off.toNat + mi.toNat]?.getD 0#32 =
          c_top := by
        dsimp only [c_top]; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      have hctop_ok : FidBvaRowEntryOk F_cur s
          (s.scratch.scratch_buf[best_k.toNat]?.getD 0#32).toNat c_top resm :=
        hctop_getD ▸ hctop_ok0
      c0_hsteps_nogrp; refine wp_join_group (ts := [.bool, .bool, i64, i64])
        (fun (_dd', _ok', _ga', _ia', ()) m1 => ∃ st1 : FullState, (FullMem c st1 ⋆ R) m1 ∧
          S7StOk c F0 F_next s st1)
        (fun _ (dd', ok', ga', ia', ()) m1 ⟨st1, hm1, hst1⟩ => by
          c0_hsteps; exact ihm (mi + 1#32, dd', ok', ga', ia', ()) m1
            (by dsimp only; rw [hmi1]; omega) ⟨st1, by rw [hmi1]; omega, hst1, hm1⟩)
        (fun Jtop hJtop => ?_)
      c0_hsplit
      · have hbin_ct : (c_top &&& 0x80000000#32) ≠ 0#32 := by
          simpa only [← hctop_mod] using (by assumption : _)
        unfold FidBvaRowEntryOk at hctop_ok; rw [ite_eq_left hbin_ct] at hctop_ok
        obtain ⟨hq_lt, hres_q, _⟩ := hctop_ok
        c0_hsteps_nogrp
        refine wp_join_group (ts := [.bool]) (fun (_, ()) md' => md' = mm)
          (fun _ (dd', ()) md' hmd' => ?_) (fun Jdd hJdd => ?_)
        · subst md'; c0_hsteps; c0_call hAddBin
          refine ⟨c, F0, F_next, stm, R, rfl, hinvm.1, hinvm.2.1, hinvm.2.2.2.2.2.1,
            fun _ _ => ?_, hmm,
            fun _ _ fl1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 hlen1' hw1' _ _ _ hms1' => ?_⟩
          · rw [hctop_eq]; dsimp only [resm] at hres_q; rw [hres_q] at hresm_ent
            simpa only [show (1 : BitVec 32) = 1#32 from rfl, hfresh1,
              show (2147483647 : BitVec 32) = 0x7FFFFFFF#32 from rfl] using hresm_ent
          · have hinv1' := s9_fullDenseInvW_of_addBin hinvm hlen1' hw1'
            have hfl1 : fl1.length = c.max_vars := hlen1'.core_ok.flags_len
            have hcvm_lt : old_cv < c.max_vars := by have := hclm.cur_vars_le; omega
            have hfr_shr : (BitVec.setWidth 64 (fresh >>> (1 : BitVec 32))).toNat < fl1.length := by
              rw [bv64_setWidth_32, bv32_lshr1_bv, hfl1, hfresh_nat]; omega
            have hfr_shr_n : (BitVec.setWidth 64 (fresh >>> (1 : Nat))).toNat < fl1.length := by
              rw [bv64_setWidth_32, bv32_lshr1_nat, hfl1, hfresh_nat]; omega
            have hq_shr : (BitVec.setWidth 64 ((stm.scratch.scratch_buf[(BitVec.setWidth 64
                (brow_off + mi)).toNat]'hctop_sb &&& 2147483647) >>> (1 : BitVec 32))).toNat <
                c.max_vars := by
              rw [bv64_setWidth_32, hctop_eq, bv32_lshr1_bv,
                show (2147483647 : BitVec 32) = 0x7FFFFFFF#32 from rfl]; omega
            have hq_shr_n : (BitVec.setWidth 64 ((stm.scratch.scratch_buf[(BitVec.setWidth 64
                (brow_off + mi)).toNat]'hctop_sb &&& 2147483647) >>> (1 : Nat))).toNat <
                c.max_vars := by
              rw [bv64_setWidth_32, hctop_eq, bv32_lshr1_nat,
                show (2147483647 : BitVec 32) = 0x7FFFFFFF#32 from rfl]; omega
            have hlen2 : ∀ (i j : Nat) (v w : BitVec 32),
                ((fl1.set i v).set j w).length = c.max_vars := fun _ _ _ _ => by simp [hfl1]
            c0_hsteps_nogrp
            refine wp_join_group (ts := [i32]) (fun (_, ()) mf => mf = m)
              (fun _ _ mf hmf => ?_) (fun Jt hJt => by
                c0_hsteps
                · exact hJt _ m rfl
                · exact hJt _ m rfl)
            subst hmf
            c0_hsteps
            all_goals first
              | exact hJ1b (mi, dd', false, ga, ia, ()) _ ⟨_, ⟨fullDenseInvW_set_flags hinv1'
                  (hlen2 _ _ _ _), hcvm, hfuelm, hsbm, htmm, htrm, hmono, hresm⟩, hm⟩
              | exact hJtop (dd', true, ga, ia, ()) _ ⟨_, hm, fullDenseInvW_set_flags hinv1'
                  (hlen2 _ _ _ _), hcvm, hfuelm, hsbm, htmm, htrm, hmono, hresm⟩
        · c0_hsplit
          · c0_hsteps; exact hJdd (ddm, ()) mm rfl
          · have hcvm_lt : old_cv < c.max_vars := by have := hclm.cur_vars_le; omega
            have hnf_wv : ((BitVec.setWidth 64 (fresh ^^^ 1#32) <<< (1 : Nat)) + 1).toNat <
                stm.core.wvec.length := by
              rw [hclm.wvec_len]
              simp only [bv_c0, show (1 : BitVec 64).toNat = 1 from rfl]; omega
            have hq_wv : ((BitVec.setWidth 64 (stm.scratch.scratch_buf[(BitVec.setWidth 64
                (brow_off + mi)).toNat]'hctop_sb &&& 2147483647) <<< (1 : Nat)) + 1).toNat <
                stm.core.wvec.length := by
              rw [hclm.wvec_len, hctop_eq, show (2147483647 : BitVec 32) = 0x7FFFFFFF#32 from rfl]
              simp only [bv_c0, show (1 : BitVec 64).toNat = 1 from rfl]; omega
            c0_hsteps_nogrp
            refine wp_join_group (ts := [i64]) (fun _ ma => ma = mm)
              (fun _ _ ma hma => by
                subst ma; c0_hsteps_nogrp
                refine wp_join_group (ts := [i64]) (fun _ mb => mb = mm)
                  (fun _ _ mb hmb => by
                    subst mb; c0_hsteps_nogrp
                    refine wp_join_group (ts := [.bool]) (fun _ mc => mc = mm)
                      (fun _ (b, ()) mc hmc => by subst mc; c0_hsteps; exact hJdd (b, ()) mm rfl)
                      (fun Jc hJc => by c0_hfast <;> exact hJc _ mm rfl))
                  (fun Jb hJb => by c0_hfast <;> exact hJb _ mm rfl))
              (fun Ja hJa => by c0_hfast <;> exact hJa _ mm rfl)
      · have hbin_ct : (c_top &&& 0x80000000#32) = 0#32 := by
          simpa only [← hctop_mod] using (by assumption : _)
        unfold FidBvaRowEntryOk at hctop_ok
        rw [ite_eq_right (fun h' => h' hbin_ct)] at hctop_ok
        obtain ⟨hct_ref0, hct_ng0, hct_sz3, _, hfbk_mem, hres_perm_f, _⟩ := hctop_ok
        obtain ⟨hct_refm, hct_szm, _⟩ := hmono c_top.toNat hct_ref0
        have hct_wf := hinv.2.1.arena.refs_wf c_top.toNat hct_ref0
        have hct_wfm := hinvm.2.1.arena.refs_wf c_top.toNat hct_refm
        have hct2_n : (BitVec.setWidth 64 c_top + 2).toNat = c_top.toNat + 2 := by
          change (BitVec.setWidth 64 c_top + 2#64).toNat = _; c0_bound
        have hct2_ar : (BitVec.setWidth 64 (stm.scratch.scratch_buf[(BitVec.setWidth 64
            (brow_off + mi)).toNat]'hctop_sb) + 2).toNat < stm.core.arena.length := by
          rw [hctop_eq, hct2_n]; have := hclm.arena_len_le; have := hclm.arena_len_arr; omega
        have hbk_sb : (BitVec.setWidth 64 best_k).toNat < stm.scratch.scratch_buf.length := by
          rw [bv64_setWidth_32, hscm.scratch_buf_len]; omega
        c0_hsteps_nogrp
        let csz_bv := stm.core.arena[(BitVec.setWidth 64 (stm.scratch.scratch_buf[(BitVec.setWidth
          64 (brow_off + mi)).toNat]'hctop_sb) + 2).toNat]'hct2_ar
        let flit_bv := stm.scratch.scratch_buf[(BitVec.setWidth 64 best_k).toNat]'hbk_sb
        have hcsz_eq : csz_bv.toNat = fullArenaClauseSizeCore s.core c_top.toNat := by
          dsimp only [csz_bv]; simp only [hctop_eq, hct2_n]
          have h1 : fullArenaClauseSizeCore stm.core c_top.toNat =
              fullArenaClauseSizeCore s.core c_top.toNat := hct_szm
          rw [← h1]; unfold fullArenaClauseSizeCore
          rw [List.getElem?_eq_getElem (by
            have := hclm.arena_len_le; have := hclm.arena_len_arr; omega), Option.getD_some]
        have hflit_eq : flit_bv = s.scratch.scratch_buf[best_k.toNat]?.getD 0#32 := by
          have h1 : some flit_bv = s.scratch.scratch_buf[best_k.toNat]? := by
            dsimp only [flit_bv]
            rw [← List.getElem?_eq_getElem hbk_sb, hsbm, bv64_setWidth_32]
          rw [← h1, Option.getD_some]
        refine wp_join_group (ts := [.bool]) (fun (_, ()) md' => md' = mm)
          (fun _ (dd', ()) md' hmd' => ?_) (fun Jdd hJdd => ?_)
        · subst md'
          have hlt := s9_bva_large_top_wp (Γ := Γ) (Q := Q) (X := X) hAllocCl hWPush hUnwatch
            (F_next := F_next) (best_k := best_k) (mi := mi) (resm := resm)
            (c_top := stm.scratch.scratch_buf[(BitVec.setWidth 64
              (brow_off + mi)).toNat]'hctop_sb)
            (csz := csz_bv) (flit := flit_bv) (fresh := fresh) (dd := dd')
            (garb_add := ga) (irred_add := ia) (J1b := J1b) (Jtop := Jtop)
            hinv (by rwa [hctop_eq]) hflit_eq hfresh1 hresm_lt
            hresm_nd hresm_ent (by rwa [hctop_eq]) (by rwa [hctop_eq]) (by rwa [hctop_eq])
            (by rwa [hctop_eq]) (by rwa [hctop_eq]) hmm
            ⟨hinvm, hcvm, hfuelm, hsbm, htmm, htrm, hmono, hresm⟩
            (fun st1 m1 hm1 hst1 => hJ1b (mi, dd', false, ga, ia, ()) m1 ⟨st1, hst1, hm1⟩)
            (fun ok' ga' ia' st1 m1 hm1 hst1 =>
              hJtop (dd', ok', ga', ia', ()) m1 ⟨st1, hm1, hst1⟩)
          unfold s9BvaLargeTopExpr s9BvaLargeWatchExpr s9BvaCopyExpr
            s9BZext s9BOp64 s9BOp32 s9BCmp32 s9BPtr32 s9BLd32 at hlt
          exact hlt
        · c0_hsplit
          · c0_hsteps; exact hJdd (ddm, ()) mm rfl
          · have hcvm_lt : old_cv < c.max_vars := by have := hclm.cur_vars_le; omega
            have hnf_wv : ((BitVec.setWidth 64 (fresh ^^^ 1#32) <<< (1 : Nat)) + 1).toNat <
                stm.core.wvec.length := by
              rw [hclm.wvec_len]
              simp only [bv_c0, show (1 : BitVec 64).toNat = 1 from rfl]; omega
            c0_hsteps_nogrp
            refine wp_join_group (ts := [i64]) (fun _ ma => ma = mm)
              (fun _ (snw0, ()) ma hma => by
                subst ma
                refine wp_loop_inv (fun (_nw, dj, ()) mdj => mdj = mm ∧ dj.toNat ≤ csz_bv.toNat)
                  (fun (_, dj, _) _ => csz_bv.toNat - dj.toNat)
                  (fun Jd hJd => by c0_hsteps; exact hJd (snw0, 0#32, ()) mm ⟨rfl, Nat.zero_le _⟩)
                  (fun Jd (nwj, dj, ()) mdj ⟨hmdj, hdj_le⟩ ihd => ?_)
                rcases hmdj with rfl; c0_hsteps_nogrp
                · have hct2_mod : (c_top.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64 =
                      c_top.toNat + 2 := by
                    rw [show BitVec.toNat (2 : BitVec 64) = 2 from rfl]; omega
                  have hdj_lt : dj.toNat < csz_bv.toNat := by
                    have h1 : dj.toNat < (stm.core.arena[(BitVec.setWidth 64
                        (stm.scratch.scratch_buf[(BitVec.setWidth 64
                          (brow_off + mi)).toNat]'hctop_sb) + 2).toNat]'hct2_ar).toNat := by
                      assumption
                    exact h1
                  have hdj1 : (dj + 1#32).toNat = dj.toNat + 1 := by c0_bound
                  have hctj_n : (BitVec.setWidth 64 c_top + 3 + BitVec.setWidth 64 dj).toNat =
                      c_top.toNat + 3 + dj.toNat := by
                    change (BitVec.setWidth 64 c_top + 3#64 + BitVec.setWidth 64 dj).toNat = _
                    c0_bound
                  have hctj_ar : c_top.toNat + 3 + dj.toNat < stm.core.arena.length := by
                    have := hclm.arena_len_le; have := hclm.arena_len_arr; omega
                  have hctj_ar_sb : (BitVec.setWidth 64 (stm.scratch.scratch_buf[(BitVec.setWidth 64
                      (brow_off + mi)).toNat]'hctop_sb) + 3 + BitVec.setWidth 64 dj).toNat <
                      stm.core.arena.length := by rw [hctop_eq, hctj_n]; exact hctj_ar
                  have hlj_lt : (stm.core.arena[c_top.toNat + 3 + dj.toNat]'hctj_ar).toNat <
                      2 * s.core.cur_vars := by
                    have hsar_len : c_top.toNat + 3 + dj.toNat < s.core.arena.length := by
                      have := hct_wf.2.2.1; have := hct_wf.2.2.2.1
                      have := hcl.arena_len_le; have := hcl.arena_len_arr; omega
                    have h1 := FullBvaFwdHelpers.fullArenaClauseLitsCore_getElem (k := s.core)
                      (r := c_top.toNat) (j := dj.toNat) (by rw [← hcsz_eq]; exact hdj_lt)
                      hsar_len
                    have h2 : stm.core.arena[c_top.toNat + 3 + dj.toNat]'hctj_ar =
                        s.core.arena[c_top.toNat + 3 + dj.toNat]'hsar_len := by
                      have hl0 := (hmono c_top.toNat hct_ref0).2.2
                      have he1 := FullBvaFwdHelpers.fullArenaClauseLitsCore_getElem (k := stm.core)
                        (r := c_top.toNat) (j := dj.toNat)
                        (by rw [hct_szm, ← hcsz_eq]; exact hdj_lt) hctj_ar
                      rw [hl0, h1] at he1
                      have hget : some (stm.core.arena[c_top.toNat + 3 + dj.toNat]'hctj_ar).toNat =
                          some (s.core.arena[c_top.toNat + 3 + dj.toNat]'hsar_len).toNat :=
                        he1.symm
                      exact BitVec.eq_of_toNat_eq (Option.some.inj hget)
                    rw [h2]
                    exact hinv.2.1.arena.lits_lt c_top.toNat hct_ref0 hct_ng0 _
                      (List.mem_of_getElem? h1)
                  c0_hsteps_nogrp
                  refine wp_join_state_pure (ts := [i64]) (α := BitVec 64)
                    (fun x => (x, ())) (fun _ => True) (fun _ nw' _ => by
                      c0_hsteps; exact ihd (nw', dj + 1#32, ()) mdj
                        (by dsimp only; rw [hdj1]; omega) ⟨rfl, by rw [hdj1]; omega⟩)
                    (fun Jlf hJlf => ?_)
                  c0_hsplit
                  · have hlj_wv : ((BitVec.setWidth 64 (stm.core.arena[(BitVec.setWidth 64
                        (stm.scratch.scratch_buf[(BitVec.setWidth 64
                          (brow_off + mi)).toNat]'hctop_sb) +
                        3 + BitVec.setWidth 64 dj).toNat]'hctj_ar_sb) <<< (1 : Nat)) + 1).toNat <
                        stm.core.wvec.length := by
                      have hlj_eq : stm.core.arena[(BitVec.setWidth 64
                          (stm.scratch.scratch_buf[(BitVec.setWidth 64
                            (brow_off + mi)).toNat]'hctop_sb) + 3 +
                          BitVec.setWidth 64 dj).toNat]'hctj_ar_sb =
                          stm.core.arena[c_top.toNat + 3 + dj.toNat]'hctj_ar := by
                        simp only [hctop_eq, hctj_n]
                      rw [hlj_eq, hclm.wvec_len]
                      simp only [bv_c0, show (1 : BitVec 64).toNat = 1 from rfl]; omega
                    c0_hsteps_nogrp
                    refine wp_join_group (ts := [i64]) (fun _ ml => ml = mdj)
                      (fun _ (addw, ()) ml hml => by
                        subst ml; c0_hsteps; exact hJlf (nwj + addw) trivial)
                      (fun Jl hJl => by c0_hfast <;> exact hJl _ mdj rfl)
                  · c0_hsteps; exact hJlf nwj trivial
                · c0_hsteps_nogrp
                  refine wp_join_group (ts := [.bool]) (fun _ mc => mc = mdj)
                    (fun _ (b, ()) mc hmc => by subst mc; c0_hsteps; exact hJdd (b, ()) mdj rfl)
                    (fun Jc hJc => by c0_hfast <;> exact hJc _ mdj rfl))
              (fun Ja hJa => by
                c0_hsplit
                · c0_hsteps; exact hJa (2#64, ()) mm rfl
                · c0_hfast <;> exact hJa _ mm rfl)
    · exact hJ1b (mi, ddm, okm, ga, ia, ()) mm
        ⟨stm, ⟨hinvm, hcvm, hfuelm, hsbm, htmm, htrm, hmono, hresm⟩, hmm⟩
    · exact hJ1b (mi, ddm, okm, ga, ia, ()) mm
        ⟨stm, ⟨hinvm, hcvm, hfuelm, hsbm, htmm, htrm, hmono, hresm⟩, hmm⟩

/-! ## 2. Post-Defrag Fresh-Var Init & Phase 1a Positive Clauses -/

private theorem s9_post_defrag_wp {Γ : Env} {Q : Post [.bool]} {X : XPost}
    (hFillU64 : FidFillU64Hyp Γ)
    (hInitFresh : ∀ args m Q X, step7InitFreshVarSpec args m Q X →
      Γ "full_init_fresh_var" [i64, i32] [] args m Q X)
    (hAddBin : FidAddBinHyp Γ) (hAllocCl : FidAllocClHyp Γ) (hWPush : FidWPushHyp Γ)
    (hDelBin : FidDelBinHyp Γ) (hUnwatch : FidUnwatchHyp Γ)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s sd : FullState}
    {R : Mem 64 → Prop} {best_k sc dm_bv brow_off mn_bv : Val i32} {dd : Val .bool}
    {md : Mem 64} {bump : Nat}
    (hinv : FullDenseInvW c F0 F_cur s)
    (hbk1 : 1 ≤ best_k.toNat) (hbk_sc : best_k.toNat < fidStepsCap c.scratch_cap)
    (hmat : FidBvaMatrixInv c F_cur s (best_k.toNat + 1) bump)
    (hlay : Step7BvaLayout c s (best_k.toNat + 1))
    (hres : s.scratch.res_sz = BitVec.ofNat 64 best_k.toNat)
    (hcv_lt : s.core.cur_vars < c.max_vars)
    (hsc_eq : sc.toNat = fidStepsCap c.scratch_cap)
    (hdm_bv : dm_bv.toNat = best_k.toNat + 1)
    (hbo_getD : (s.scratch.scratch_buf[sc.toNat + best_k.toNat]?.getD 0#32).toNat = brow_off.toNat)
    (hmn_getD : (s.scratch.scratch_buf[2 * sc.toNat + best_k.toNat]?.getD 0#32).toNat = mn_bv.toNat)
    (hmd : (FullMem c sd ⋆ R) md) (hsd : S9PreOk c F0 F_cur s sd)
    (hQ : ∀ ok s' m', FullDenseInv c F0 s' → s.core.cur_vars ≤ s'.core.cur_vars →
      (ok = true → s.core.cur_vars < s'.core.cur_vars) →
      (ok = true → Step7BvaCommittedOk c s' best_k.toNat) → s'.core.fuel = s.core.fuel →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach → (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    wp Γ Q X (s9PostDefragExpr c.hdr c.pArena c.pScratchBuf c.pWsort c.pFlags c.pWvec
      best_k sc dm_bv brow_off mn_bv dd) md := by
  obtain ⟨hinvd, hcvd, hfueld, hard, hald, hsbd, htmd, htrd, hresd⟩ := hsd
  have hmx := c.hmaxv; have hwcap := c.hwcap; have har_b := c.harena; have hscr_b := c.hscr
  unfold dimacsBound at hmx hwcap har_b hscr_b
  have hcl := hinv.1.core_ok; have hsc := hinv.1.scratch_ok
  have hcv_le := hcl.cur_vars_le; have hsb_len := hsc.scratch_buf_len
  have hsc_pos := hmat.1; have hbump_ge := hmat.2.2.2.1; have hbump_le := hmat.2.2.2.2.1
  have hsc4 := fidStepsCap_mul4_le c.scratch_cap
  have hbk_row := hmat.2.2.2.2.2 best_k.toNat (by omega)
  obtain ⟨hfbk_lt, hro_ge, hmn_lo, hro_mn, _, hbk_entries⟩ := hbk_row
  rw [← hsc_eq] at hro_ge hmn_lo hro_mn hbk_entries
  rw [hbo_getD] at hro_ge hro_mn hbk_entries
  rw [hmn_getD] at hmn_lo hro_mn hbk_entries
  let dm := best_k.toNat + 1
  have hcld := hinvd.1.core_ok; have hscd := hinvd.1.scratch_ok; let old_cv := s.core.cur_vars
  have hfv_nat : (BitVec.setWidth 32 (BitVec.ofNat 64 sd.core.cur_vars)).toNat = old_cv := by
    rw [hcvd]; c0_bound
  have hcv1_nat : (BitVec.ofNat 64 sd.core.cur_vars + 1).toNat = old_cv + 1 := by
    change (BitVec.ofNat 64 sd.core.cur_vars + 1#64).toNat = _; rw [hcvd]; c0_bound
  have heqpd : ∀ dd_v : Val .bool,
      s9PostDefragExpr c.hdr c.pArena c.pScratchBuf c.pWsort c.pFlags c.pWvec
        best_k sc dm_bv brow_off mn_bv dd_v =
      s9PostDefragExpr c.hdr c.pArena c.pScratchBuf c.pWsort c.pFlags c.pWvec
        best_k sc dm_bv brow_off mn_bv dd_v := fun _ => rfl
  conv at heqpd =>
    intro dd_v; rhs
    unfold s9PostDefragExpr s9MidExpr s9PreMidExpr s9HdrExpr
    delta FullFidelityStep9.full_bva_commit_body
    dsimp only [sSteps, sStep, sLet32, sLd64, sLd32, sCall32, sGrpb, sGrp64_32, sGrp64_64_32, sThen,
      sElse, sDummyTup, sDummyVal, i64, i32]
  refine (congrArg (fun e => wp Γ Q X e md) (heqpd dd)).mpr ?_
  c0_hsteps
  let sd_inc : FullState := { sd with core := { sd.core with cur_vars := old_cv + 1 } }
  have hmd_inc : (FullMem c sd_inc ⋆ R) m := by dsimp only [sd_inc]; rw [hcv1_nat] at hm; exact hm
  c0_call hInitFresh; refine ⟨c, sd_inc, R, rfl, ⟨{ hcld with
         cur_vars_ge := by have := hcld.cur_vars_ge; dsimp only [sd_inc, old_cv]; omega
         cur_vars_le := by dsimp only [sd_inc, old_cv]; omega
         trail_end_le := by have := hcld.trail_end_le; dsimp only [sd_inc, old_cv]; omega },
     hscd⟩,
    by dsimp only [sd_inc, old_cv]; rw [hfv_nat]; omega, hmd_inc,
    fun vals' mrk' fl' lvl' rsns' wvec' unass' sc' m1 hlen1 hext1 hsb1 hws1 htm1 htr1 hss1 hres1
      hv0 hv1 hv_oth hm0 hm_oth hl0 hl_oth hr0 hr_oth hw0 hw_oth hm1 => ?_⟩
  let L : List Nat := (List.range dm).map fun t => (s.scratch.scratch_buf[t]?.getD 0#32).toNat
  let resAt (idx : Nat) : List Nat :=
    if h : idx < mn_bv.toNat then Classical.choose (hbk_entries idx h) else []
  let Qs : List (List Nat) := (List.range mn_bv.toNat).map resAt
  have hL_lt : ∀ f ∈ L, f < 2 * old_cv := by
    intro f hf; obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hf
    rw [List.mem_range] at ht; exact (hmat.2.2.2.2.2 t (by omega)).1
  have hQ_lt : ∀ C ∈ Qs, ∀ l ∈ C, l < 2 * old_cv := by
    intro C hC l hl; obtain ⟨idx, hidx, rfl⟩ := List.mem_map.mp hC
    rw [List.mem_range] at hidx; dsimp only [resAt] at hl; rw [dite_eq_left hidx] at hl
    exact (Classical.choose_spec (hbk_entries idx hidx)).1 l hl
  have hprod : ∀ f ∈ L, ∀ C ∈ Qs, (cnfOfClauses F_cur).EntailsClause (cnfClause (f :: C)) := by
    intro f hf C hC; obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hf; rw [List.mem_range] at ht
    obtain ⟨idx, hidx, rfl⟩ := List.mem_map.mp hC; rw [List.mem_range] at hidx
    dsimp only [resAt]; rw [dite_eq_left hidx]
    exact (Classical.choose_spec (hbk_entries idx hidx)).2.2.2.1 t (by omega)
  let F_next := bvaExtendGen old_cv L Qs F_cur
  let s1 : FullState :=
    { sd_inc with core := { sd_inc.core with vals := vals', mrk := mrk', flags := fl', lvl := lvl',
                                             rsns := rsns', wvec := wvec', unassigned := unass' }
                  scratch := sc' }
  have hcore1 : s1.core =
      { sd.core with cur_vars := sd.core.cur_vars + 1, vals := vals', mrk := mrk',
                     flags := fl', lvl := lvl', rsns := rsns', wvec := wvec',
                     unassigned := unass' } := by dsimp only [s1, sd_inc, old_cv]; rw [hcvd]
  have ⟨hw1, hd1⟩ := fullDenseInv_add_fresh_var_gen (s := sd) (s' := s1)
    hinvd.1 hinvd.2.1 hinvd.2.2.1 hinvd.2.2.2.1 hinvd.2.2.2.2.1 hinvd.2.2.2.2.2.1
    hinvd.2.2.2.2.2.2 (by rw [hcvd]; exact hcv_lt)
    (by rw [hcvd]; exact hL_lt) (by rw [hcvd]; exact hQ_lt) hprod hlen1 hcore1
    (by rw [hfv_nat] at hv0; rwa [hcvd]) (by rw [hfv_nat] at hv1; rwa [hcvd])
    (by intro l hl hne; exact hv_oth l hl (by rw [hfv_nat]; dsimp only [old_cv]; rwa [← hcvd]))
    (by rw [hfv_nat] at hm0; rwa [hcvd])
    (by intro v hv hne; exact hm_oth v hv (by rw [hfv_nat]; dsimp only [old_cv]; rwa [← hcvd]))
    (by intro v hv hne; exact hl_oth v hv (by rw [hfv_nat]; dsimp only [old_cv]; rwa [← hcvd]))
    (by intro v hv hne; exact hr_oth v hv (by rw [hfv_nat]; dsimp only [old_cv]; rwa [← hcvd]))
    (by intro k hk; rw [hfv_nat] at hw0; rw [hcvd]; exact hw0 k hk)
    (by intro i hi hne; exact hw_oth i hi (by rw [hfv_nat]; dsimp only [old_cv]; rwa [← hcvd]))
    hext1.1 hext1.2
  have hinv1 : FullDenseInvW c F0 F_next s1 :=
    ⟨hlen1, by rwa [hcvd] at hw1, hd1.2.1, hd1.2.2.1, hd1.2.2.2.1, hd1.2.2.2.2.1, hd1.2.2.2.2.2⟩
  have hpos_ent : ∀ f ∈ L, (cnfOfClauses F_next).EntailsClause (cnfClause [2 * old_cv, f]) :=
    fun _ hf => bvaExtendGen_entails_pos hf
  have hneg_ent : ∀ R ∈ Qs, (cnfOfClauses F_next).EntailsClause (cnfClause ((2 * old_cv + 1) ::
    R)) :=
    fun _ hR => bvaExtendGen_entails_neg hR
  let fv_bv := BitVec.setWidth 32 (BitVec.ofNat 64 sd.core.cur_vars)
  have hfresh_nat : (fv_bv <<< (1 : Nat)).toNat = 2 * old_cv := by
    rw [bv32_shl1_nat, hfv_nat, Nat.mod_eq_of_lt (by omega)]
  have hfresh_bv : (fv_bv <<< (1 : BitVec 32)).toNat = 2 * old_cv := by
    rw [bv32_shl1_bv, hfv_nat, Nat.mod_eq_of_lt (by omega)]
  have hfresh1_nat : ((fv_bv <<< (1 : Nat)) ^^^ 1#32).toNat = 2 * old_cv + 1 := by
    rw [s9_bv32_shl1_xor1 (by rw [hfv_nat]; omega), hfv_nat]
  have hfresh1_bv : ((fv_bv <<< (1 : BitVec 32)) ^^^ (1 : BitVec 32)).toNat = 2 * old_cv + 1 := by
    have hev : (fv_bv <<< (1 : BitVec 32)) = fv_bv <<< (1 : Nat) := by
      apply BitVec.eq_of_toNat_eq; rw [bv32_shl1_bv, bv32_shl1_nat]
    rw [hev]; exact hfresh1_nat
  have hfv2_rp_bv : (BitVec.setWidth 64 (fv_bv <<< (1 : BitVec 32))).toNat <
      sd.core.repr.length := by
    rw [bv64_setWidth_32, hfresh_bv, hcld.repr_len]; omega
  have hfv2_rp_n : (BitVec.setWidth 64 (fv_bv <<< (1 : Nat))).toNat < sd.core.repr.length := by
    rw [bv64_setWidth_32, hfresh_nat, hcld.repr_len]; omega
  have hfv21_rp :
      (BitVec.setWidth 64 ((fv_bv <<< (1 : BitVec 32)) ||| 1#32)).toNat < sd.core.repr.length := by
    have hev : (fv_bv <<< (1 : BitVec 32)) = fv_bv <<< (1 : Nat) := by
      apply BitVec.eq_of_toNat_eq; rw [bv32_shl1_bv, bv32_shl1_nat]
    rw [hev, bv64_setWidth_32, s9_bv32_shl1_or1 (by rw [hfv_nat]; omega), hfv_nat, hcld.repr_len]
    omega
  have hfv21_rp_n :
      (BitVec.setWidth 64 ((fv_bv <<< (1 : Nat)) ||| 1#32)).toNat < sd.core.repr.length := by
    rw [bv64_setWidth_32, s9_bv32_shl1_or1 (by rw [hfv_nat]; omega), hfv_nat, hcld.repr_len]
    omega
  have hfv2_ws : (BitVec.setWidth 64 (fv_bv <<< (1 : BitVec 32))).toNat < sc'.wsort.length := by
    rw [bv64_setWidth_32, hfresh_bv, hlen1.scratch_ok.wsort_len]; omega
  have hfv2_ws_n : (BitVec.setWidth 64 (fv_bv <<< (1 : Nat))).toNat < sc'.wsort.length := by
    rw [bv64_setWidth_32, hfresh_nat, hlen1.scratch_ok.wsort_len]; omega
  have hfv21_ws :
      (BitVec.setWidth 64 ((fv_bv <<< (1 : BitVec 32)) ||| 1#32)).toNat < sc'.wsort.length := by
    have hev : (fv_bv <<< (1 : BitVec 32)) = fv_bv <<< (1 : Nat) := by
      apply BitVec.eq_of_toNat_eq; rw [bv32_shl1_bv, bv32_shl1_nat]
    rw [hev, bv64_setWidth_32, s9_bv32_shl1_or1 (by rw [hfv_nat]; omega), hfv_nat,
      hlen1.scratch_ok.wsort_len]
    omega
  have hfv21_ws_n :
      (BitVec.setWidth 64 ((fv_bv <<< (1 : Nat)) ||| 1#32)).toNat < sc'.wsort.length := by
    rw [bv64_setWidth_32, s9_bv32_shl1_or1 (by rw [hfv_nat]; omega), hfv_nat,
      hlen1.scratch_ok.wsort_len]
    omega
  have hfv21_rp_set :
      (BitVec.setWidth 64 ((fv_bv <<< (1 : BitVec 32)) ||| 1#32)).toNat <
      (sd.core.repr.set (BitVec.setWidth 64 (fv_bv <<< (OfNat.ofNat 1 : BitVec 32))).toNat
        0#32).length := by
    simpa [List.length_set] using hfv21_rp
  have hfv21_ws_set :
      (BitVec.setWidth 64 ((fv_bv <<< (1 : BitVec 32)) ||| 1#32)).toNat <
      (sc'.wsort.set (BitVec.setWidth 64 (fv_bv <<< (OfNat.ofNat 1 : BitVec 32))).toNat
        0#32).length := by
    simpa [List.length_set] using hfv21_ws
  c0_hsteps_nogrp
  let repr0 :=
    (sd.core.repr.set (BitVec.setWidth 64 (fv_bv <<< (OfNat.ofNat 1 : BitVec 32))).toNat 0#32).set
      (BitVec.setWidth 64 ((fv_bv <<< (OfNat.ofNat 1 : BitVec 32)) ||| 1#32)).toNat 0#32
  let wsort0 :=
    (sc'.wsort.set (BitVec.setWidth 64 (fv_bv <<< (OfNat.ofNat 1 : BitVec 32))).toNat 0#32).set
      (BitVec.setWidth 64 ((fv_bv <<< (OfNat.ofNat 1 : BitVec 32)) ||| 1#32)).toNat 0#32
  let st0 : FullState :=
    { core := { sd.core with cur_vars := old_cv + 1, vals := vals', mrk := mrk', flags := fl',
                             lvl := lvl', rsns := rsns', wvec := wvec', unassigned := unass',
                             repr := repr0 }
      scratch := { sc' with wsort := wsort0 } }
  have hrp0_len : repr0.length = 2 * c.max_vars := by
    dsimp only [repr0]; simp [hcld.repr_len]
  have hws0_len : wsort0.length = 2 * c.max_vars := by
    dsimp only [wsort0]; simp [hlen1.scratch_ok.wsort_len]
  have hinv0 : FullDenseInvW c F0 F_next st0 :=
    fullDenseInv_with_core_aux (tc' := sd.core.tmp_cnt) (tl' := sd.core.tmp_len)
      hinv1 hrp0_len hcld.min_clr_len_arr hcld.tmp_len_arr hlen1.core_ok.flags_len hcld.tmp_len_le
      { hlen1.scratch_ok with wsort_len := hws0_len } rfl rfl
  have hmono0 : FidBvaArenaMono s.core st0.core := fun r hr => by
    change r ∈ fullArenaClauseRefsCore { sd.core with arena := sd.core.arena } ∧ _
    have h1 : fullArenaClauseRefsCore { sd.core with arena := sd.core.arena } =
        fullArenaClauseRefsCore s.core := by unfold fullArenaClauseRefsCore; rw [hard, hald]
    refine ⟨by rw [h1]; exact hr, ?_, ?_⟩
    · unfold fullArenaClauseSizeCore; rw [hard]
    · unfold fullArenaClauseLitsCore fullArenaClauseSizeCore; rw [hard]
  refine wp_join_group (ts := [i32, .bool, .bool])
    (fun (_, _dd1a, ok1a, ()) m1a => ∃ st1a : FullState,
      S7StOk c F0 F_next s st1a ∧ (FullMem c st1a ⋆ R) m1a)
    (fun _ (_, dd1a, ok1a, ()) m1a ⟨st1a, hst1a, hm1a⟩ => ?_) (fun J1a hJ1a => ?_)
  · have hp1b := s9_phase1b_wp (Γ := Γ) (Q := Q) (X := X)
      hFillU64 hAddBin hAllocCl hWPush hDelBin hUnwatch (F_next := F_next)
      (dm_bv := dm_bv) (brow_off := brow_off) (mn_bv := mn_bv)
      (fresh := fv_bv <<< (OfNat.ofNat 1 : BitVec 32)) (dd1a := dd1a) (ok1a := ok1a)
      hinv hbk1 hbk_sc hmat hlay hres hsc_eq hbo_getD hmn_getD hfresh_bv hfresh1_bv resAt
      (fun idx hidx => by
        have hspec := Classical.choose_spec (hbk_entries idx hidx)
        have heq : resAt idx = Classical.choose (hbk_entries idx hidx) := by
          dsimp only [resAt]; rw [dite_eq_left hidx]
        rw [heq]; refine ⟨hspec.1, hspec.2.1, hspec.2.2.1, ?_⟩
        have hmem : resAt idx ∈ Qs := List.mem_map.mpr ⟨idx, List.mem_range.mpr hidx, rfl⟩
        have h1 := hneg_ent (resAt idx) hmem; rwa [heq] at h1)
      hst1a hm1a hQ
    unfold s9Phase1bExpr at hp1b
    replace hp1b := (congrArg (fun e => wp Γ Q X
      (e |> sSteps 10 |> sLd64 c.pRepr |> sSteps 22 |>
        sLet32 (fv_bv <<< (OfNat.ofNat 1 : BitVec 32)) |> sStep |> sLd64 c.pTmp |>
        sGrp32bb (fun (_ : Tup Val [i32, .bool, .bool]) (_ : Mem 64) => True) 0#32 dd1a ok1a)
      m1a) (heqpd dd1a)).mp hp1b
    dsimp only [sSteps, sStep, sLet32, sLd64, sGrp32bb, sDummyTup, sDummyVal, i64, i32] at hp1b
    exact hp1b
  · clear heqpd hmat hlay hneg_ent hprod hQ_lt hcore1 hrp0_len hws0_len
    clear hv0 hv1 hv_oth hm0 hm_oth hl0 hl_oth hr0 hr_oth hw0 hw_oth hext1 hinv1
    clear hfv2_rp_bv hfv2_rp_n hfv21_rp hfv21_rp_n hfv2_ws hfv2_ws_n hfv21_ws hfv21_ws_n
    clear hfv21_rp_set hfv21_ws_set hfbk_lt hro_ge hmn_lo hro_mn
    refine wp_loop_inv
      (fun (si, _dds, ()) msi => ∃ sts : FullState, si.toNat ≤ dm ∧
        S7StOk c F0 F_next s sts ∧ (FullMem c sts ⋆ R) msi)
      (fun (si, _, _) _ => dm - si.toNat) (fun Js hJs => by
        c0_hfast; exact hJs (0#32, dd, ()) m ⟨st0, Nat.zero_le _,
          ⟨hinv0, rfl, hfueld, hsb1.trans hsbd, htm1.trans htmd, htr1.trans htrd, hmono0,
            hres1.trans hresd⟩, hm⟩)
      (fun Js (si, dds, ()) msi ⟨sts, hsi_le, hsts, hmsi⟩ ihs => ?_)
    obtain ⟨hinvs, hcvs, hfuels, hsbs, htms, htrs, hmonos, hress⟩ := hsts
    have hcls := hinvs.1.core_ok; have hscs := hinvs.1.scratch_ok; c0_hsplit
    · have hsi_lt : si.toNat < dm := by
        have h1 : si.toNat < dm_bv.toNat := (by assumption); omega
      have hsi1 : (si + 1#32).toNat = si.toNat + 1 := by simp only [bv_c0]; omega
      have hfs_sb : (BitVec.setWidth 64 si).toNat < sts.scratch.scratch_buf.length := by
        rw [bv64_setWidth_32, hscs.scratch_buf_len]; omega
      have hfs_getD : (sts.scratch.scratch_buf[(BitVec.setWidth 64 si).toNat]'hfs_sb).toNat =
          (s.scratch.scratch_buf[si.toNat]?.getD 0#32).toNat := by
        have h1 : sts.scratch.scratch_buf[(BitVec.setWidth 64 si).toNat]? =
            s.scratch.scratch_buf[si.toNat]? := by rw [hsbs, bv64_setWidth_32]
        rw [← h1, List.getElem?_eq_getElem hfs_sb, Option.getD_some]
      have hfs_lt : (sts.scratch.scratch_buf[(BitVec.setWidth 64 si).toNat]'hfs_sb).toNat <
          2 * old_cv := by
        rw [hfs_getD]; exact hL_lt _ (List.mem_map.mpr ⟨si.toNat, List.mem_range.mpr hsi_lt, rfl⟩)
      c0_hsteps_nogrp
      refine wp_join_group (ts := [.bool]) (fun (_, ()) md' => md' = msi)
        (fun _ (dd', ()) md' hmd' => ?_) (fun Jdd hJdd => ?_)
      · subst md'
        c0_hfast; c0_call hAddBin
        refine ⟨c, F0, F_next, sts, R, rfl, hinvs.1, hinvs.2.1, hinvs.2.2.2.2.2.1,
          fun _ _ => by
            have hfr_g : (BitVec.setWidth 32 (BitVec.ofNat 64 sd.core.cur_vars) <<<
                OfNat.ofNat 1).toNat = 2 * old_cv := hfresh_bv
            rw [hfr_g, hfs_getD]
            exact hpos_ent _ (List.mem_map.mpr ⟨si.toNat, List.mem_range.mpr hsi_lt, rfl⟩),
          hmsi, fun _ _ fl_s1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ms1 hlen_s1 hw_s1 _ _ _ hms1 => ?_⟩
        have hinv_s1 := s9_fullDenseInvW_of_addBin hinvs hlen_s1 hw_s1
        have hfl_s1 : fl_s1.length = c.max_vars := hlen_s1.core_ok.flags_len
        have hfs_shr : (BitVec.setWidth 64 ((sts.scratch.scratch_buf[(BitVec.setWidth 64
            si).toNat]'hfs_sb) >>> (1 : BitVec 32))).toNat < fl_s1.length := by
          rw [bv64_setWidth_32, bv32_lshr1_bv, hfl_s1]; omega
        have hfs_shr_n : (BitVec.setWidth 64 ((sts.scratch.scratch_buf[(BitVec.setWidth 64
            si).toNat]'hfs_sb) >>> (1 : Nat))).toNat < fl_s1.length := by
          rw [bv64_setWidth_32, bv32_lshr1_nat, hfl_s1]; omega
        have hfr_shr : (BitVec.setWidth 64 ((fv_bv <<< (OfNat.ofNat 1 : BitVec 32)) >>>
            (1 : BitVec 32))).toNat < c.max_vars := by
          rw [bv64_setWidth_32, bv32_lshr1_bv, hfresh_bv]; omega
        have hfr_shr_n : (BitVec.setWidth 64 ((fv_bv <<< (OfNat.ofNat 1 : BitVec 32)) >>>
            (1 : Nat))).toNat < c.max_vars := by
          rw [bv64_setWidth_32, bv32_lshr1_nat, hfresh_bv]; omega
        have hfl_s1_len2 : ∀ k v, (fl_s1.set k v).length = c.max_vars :=
          fun _ _ => by simp [hfl_s1]
        c0_hfast
        all_goals first
          | exact hJ1a (si, dd', false, ()) ms1
              ⟨_, ⟨hinv_s1, hcvs, hfuels, hsbs, htms, htrs, hmonos, hress⟩, hms1⟩
          | exact ihs (si + 1#32, dd', ()) m (by dsimp only; rw [hsi1]; omega)
              ⟨_, by rw [hsi1]; omega,
               ⟨fullDenseInvW_set_flags hinv_s1 (by simp [hfl_s1]),
                hcvs, hfuels, hsbs, htms, htrs, hmonos, hress⟩, hm⟩
      · c0_hsplit
        · c0_hsteps; exact hJdd (dds, ()) msi rfl
        · have hfr_nat :
              (BitVec.setWidth 64 (fv_bv <<< (OfNat.ofNat 1 : BitVec 32))).toNat = 2 * old_cv := by
            rw [bv64_setWidth_32]; exact hfresh_bv
          have hfr_wv : ((BitVec.setWidth 64 (fv_bv <<< (OfNat.ofNat 1 : BitVec 32)) <<<
              (1 : Nat)) + 1).toNat < sts.core.wvec.length := by
            rw [hcls.wvec_len]; simp only [bv_c0, show (1 : BitVec 64).toNat = 1 from rfl, hfr_nat]
            omega
          have hfs_wv : ((BitVec.setWidth 64 (sts.scratch.scratch_buf[(BitVec.setWidth 64
              si).toNat]'hfs_sb) <<< (1 : Nat)) + 1).toNat < sts.core.wvec.length := by
            rw [hcls.wvec_len]
            generalize sts.scratch.scratch_buf[(BitVec.setWidth 64 si).toNat]'hfs_sb =
              fs_bv at hfs_lt ⊢
            simp only [bv_c0, show (1 : BitVec 64).toNat = 1 from rfl]; omega
          c0_hsteps_nogrp
          refine wp_join_group (ts := [i64]) (fun _ ma => ma = msi)
            (fun _ _ ma hma => by
              subst ma; c0_hsteps_nogrp
              refine wp_join_group (ts := [i64]) (fun _ mb => mb = msi)
                (fun _ _ mb hmb => by
                  subst mb; c0_hsteps_nogrp
                  refine wp_join_group (ts := [.bool]) (fun _ mc => mc = msi)
                    (fun _ (b, ()) mc hmc => by subst mc; c0_hsteps; exact hJdd (b, ()) msi rfl)
                    (fun Jc hJc => by c0_hfast <;> exact hJc _ msi rfl))
                (fun Jb hJb => by c0_hfast <;> exact hJb _ msi rfl))
            (fun Ja hJa => by c0_hfast <;> exact hJa _ msi rfl)
    · exact hJ1a (si, dds, true, ()) msi
        ⟨sts, ⟨hinvs, hcvs, hfuels, hsbs, htms, htrs, hmonos, hress⟩, hmsi⟩

/-! ## 3. Pre-Commit Defrag Check & Exit Bridge (`s9_pre_exit_wp`) -/

theorem s9_pre_exit_wp {Γ : Env} {Q : Post [.bool]} {X : XPost}
    (hFillU64 : FidFillU64Hyp Γ)
    (hDefrag : ∀ args m Q X, Full.fullWstackDefragSpec args m Q X →
      Γ "full_wstack_defrag" [i64] [] args m Q X)
    (hInitFresh : ∀ args m Q X, step7InitFreshVarSpec args m Q X →
      Γ "full_init_fresh_var" [i64, i32] [] args m Q X)
    (hAddBin : FidAddBinHyp Γ) (hAllocCl : FidAllocClHyp Γ) (hWPush : FidWPushHyp Γ)
    (hDelBin : FidDelBinHyp Γ) (hUnwatch : FidUnwatchHyp Γ)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {R : Mem 64 → Prop} {best_k sc dm_bv brow_off mn_bv : Val i32}
    {need_ar need_w : Val i64} {m : Mem 64} {bump : Nat}
    (hinv : FullDenseInvW c F0 F_cur s)
    (hbk1 : 1 ≤ best_k.toNat) (hbk_sc : best_k.toNat < fidStepsCap c.scratch_cap)
    (hmat : FidBvaMatrixInv c F_cur s (best_k.toNat + 1) bump)
    (hlay : Step7BvaLayout c s (best_k.toNat + 1))
    (hres : s.scratch.res_sz = BitVec.ofNat 64 best_k.toNat)
    (hsc_eq : sc.toNat = fidStepsCap c.scratch_cap)
    (hdm_bv : dm_bv.toNat = best_k.toNat + 1)
    (hbo_getD :
      (s.scratch.scratch_buf[sc.toNat + best_k.toNat]?.getD 0#32).toNat = brow_off.toNat)
    (hmn_getD :
      (s.scratch.scratch_buf[2 * sc.toNat + best_k.toNat]?.getD 0#32).toNat = mn_bv.toNat)
    (hm : (FullMem c s ⋆ R) m) (hcv_lt : s.core.cur_vars < c.max_vars)
    (hQ : ∀ ok s' m', FullDenseInv c F0 s' → s.core.cur_vars ≤ s'.core.cur_vars →
      (ok = true → s.core.cur_vars < s'.core.cur_vars) →
      (ok = true → Step7BvaCommittedOk c s' best_k.toNat) → s'.core.fuel = s.core.fuel →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach → (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    wp Γ Q X (s9PreExitExpr c.hdr c.pArena c.pScratchBuf c.pWsort c.pFlags c.pWvec
      best_k sc dm_bv brow_off mn_bv need_ar need_w) m := by
  have hmx := c.hmaxv; have hwcap := c.hwcap; have har_b := c.harena; have hscr_b := c.hscr
  unfold dimacsBound at hmx hwcap har_b hscr_b
  unfold s9PreExitExpr s9PreMidExpr s9HdrExpr
  delta FullFidelityStep9.full_bva_commit_body
  dsimp only [sSteps, sStep, sLet32, sLd64, sLd32, sCall32, sGrpb, sGrp64_32,
    sGrp64_64_32, sGrp64_64_32v, sThen, sElse, sDummyTup, sDummyVal, i64, i32]
  refine wp_join_group (ts := [.bool]) (fun _ md => ∃ sd : FullState,
    (FullMem c sd ⋆ R) md ∧ S9PreOk c F0 F_cur s sd)
    (fun _ (dd, ()) md ⟨sd, hmd, hsd⟩ => ?_) (fun Jdef hJdef => ?_)
  · have hpd := s9_post_defrag_wp (Γ := Γ) (Q := Q) (X := X)
      hFillU64 hInitFresh hAddBin hAllocCl hWPush hDelBin hUnwatch
      (sc := sc) (dm_bv := dm_bv) (brow_off := brow_off) (mn_bv := mn_bv) (dd := dd)
      hinv hbk1 hbk_sc hmat hlay hres hcv_lt hsc_eq hdm_bv hbo_getD hmn_getD hmd hsd hQ
    unfold s9PostDefragExpr s9MidExpr s9PreMidExpr s9HdrExpr at hpd
    delta FullFidelityStep9.full_bva_commit_body at hpd
    dsimp only [sSteps, sStep, sLet32, sLd64, sLd32, sCall32, sGrpb, sGrp64_32,
      sGrp64_64_32, sThen, sElse, sDummyTup, sDummyVal, i64, i32] at hpd
    exact hpd
  · refine wp_join_state0 (α := Unit) (fun _ md => md = m)
      (fun _ _ md hmd => ?_) (fun Jneed hJneed => ?_)
    · subst md; refine wp_join_group (ts := [.bool])
        (fun _ md => ∃ sd : FullState, (FullMem c sd ⋆ R) md ∧ S9PreOk c F0 F_cur s sd)
        (fun _ (dd1, ()) md ⟨sd, hmd, hinvd, hcvd, hfueld, hard, hald, hsbd, htmd, htrd, hresd⟩ =>
          ?_)
        (fun Jd1 hJd1 => ?_)
      · refine wp_join_state0 (α := Unit) (fun _ mf => mf = md)
          (fun _ _ mf hmf => ?_) (fun Jfail hJfail => ?_)
        · subst mf
          refine wp_join_state0 (α := List (BitVec 32))
            (fun wsz mzi => wsz.length = 2 * c.max_vars ∧
              (FullMem c { sd with scratch := { sd.scratch with wsort := wsz } } ⋆ R) mzi)
            (fun _ wsz mzi ⟨hwsz_l, hmzi⟩ => by
              c0_hfast
              exact hQ false _ mzi (s9_fullDenseInvW_set_wsort hinvd hwsz_l).toDense
                (by dsimp only; omega) (fun h => absurd h (by decide))
                (fun h => absurd h (by decide))
                hfueld htmd htrd hmzi)
            (fun Jw hJw => by
              c0_hsplit
              · c0_hsteps_nogrp
                refine s9_call_fill_u64_wsort hFillU64 hinvd.1.scratch_ok.wsort_len
                  hinvd.1.core_ok.cur_vars_le rfl rfl (by decide) hmd fun ws' m' hws'_l hm' => ?_
                c0_hstep; exact hJw ws' m' ⟨hws'_l, hm'⟩
              · c0_hstep; exact hJw sd.scratch.wsort md ⟨hinvd.1.scratch_ok.wsort_len, hmd⟩)
        · c0_hfast
          · exact hJfail () md rfl
          · exact hJfail () md rfl
          · exact hJdef (dd1, ()) md
              ⟨sd, hmd, hinvd, hcvd, hfueld, hard, hald, hsbd, htmd, htrd, hresd⟩
      · c0_hsplit
        · c0_call hDefrag
          refine ⟨c, s, R, rfl, hinv.1, hinv.2.1.watches.layout, hm,
            fun wvec' wstk' wlen' wsort' md hlen' hlay' _ hsl' hmd =>
              hJd1 (true, ()) md ⟨_, hmd, s9_fullDenseInvW_of_defrag hinv hlen' hlay' hsl',
                rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
        · c0_hstep
          exact hJd1 (false, ()) m ⟨s, hm, hinv, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · c0_hsplit
      · c0_hstep
        exact hJneed () m rfl
      · c0_hsplit
        · c0_hstep
          exact hJneed () m rfl
        · c0_hstep
          exact hJdef (false, ()) m ⟨s, hm, hinv, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end LeanQbe.T.Examples.Kissat.FullFidelityStep9

end
