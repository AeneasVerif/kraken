/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Src.Factor
public import LeanQbe.T.Examples.Kissat.Proof.Factor.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Factor.Helpers
public import LeanQbe.T.Examples.Kissat.Proof.Factor.Wp0
public import LeanQbe.T.Examples.Kissat.Proof.Factor.WpCommit0
public import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts1
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts3
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts4
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics1
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# BVA Commit Phase 1, Phase 3, Phase 4 & Epilogue WP (`Proof.Factor.WpCommit1`)

Zero-legacy (`0` `Full*` imports, `0` placeholders, `XPost`-polymorphic) sub-phase WP proofs for
`full_bva_commit`:
1. `cmt_p4_epilogue_wp`: Phase 4 old-binary deletion + large-clause unwatch/garbage-marking +
   epilogue (`arena_garbage`, `num_irred`, `full_fill_u64_m7`, `deg[fresh/fresh^1]`, `bva_cnt`).
2. `cmt_ok_exit_wp` & `cmt_p2_exit_wp`: Phase 3 reverse compaction + composition with Phase 4 and
   failure exit (`cmt_fail_exit_wp`).
3. `cmt_phase1_wp`: Phase 1 loop adding `[2*fv, f_i]` binary clauses.
-/

set_option autoImplicit false

local macro "fid_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

namespace LeanQbe.T.Examples.Kissat.Proof.Factor

public section

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.C0Step LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Factor
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Spec.FullBvaHeapHelpers
open LeanQbe.T.Examples.Kissat.Proof.Spec.FullBvaHeapTactics
open LeanQbe.T.Examples.Kissat.Proof.Factor.Spec
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics

@[local bv_c0] private theorem cmt1_bv64_one : (1 : BitVec 64).toNat = 1 := rfl
@[local bv_c0] private theorem cmt1_bv32_one : (1 : BitVec 32).toNat = 1 := rfl
@[local bv_c0] private theorem cmt1_bv32_two : (2 : BitVec 32).toNat = 2 := rfl
@[local bv_c0] private theorem cmt1_bv32_three : (3 : BitVec 32).toNat = 3 := rfl

private theorem cmt1_getElem_eq {α : Type} {xs : List α} {i j : Nat}
    {hi : i < xs.length} {hj : j < xs.length} (h : i = j) : xs[i]'hi = xs[j]'hj := by
  subst h; rfl

/-! ## 1. Phase 4 Deletion/Garbage-Marking & Epilogue WP -/

private theorem cmt_p4_epilogue_wp {Γ : Env} {Q : Post [.bool]} {X : XPost}
    (hFill : ∀ a m Q X, Limits.Spec.m7FillU64Spec a m Q X →
      Γ "full_fill_u64_m7" [i64, i64, i64] [] a m Q X)
    (hDelBin : ∀ a m Q X, Watch.Spec.fullDeleteBinarySpec a m Q X →
      Γ "full_delete_binary" [i64, i32, i32] [] a m Q X)
    (hUnwatch : ∀ a m Q X, fullUnwatchLargeSpec a m Q X →
      Γ "full_unwatch_large" [i64, i32, i32] [] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_next : List (List Nat)} {s0 s_p3 : FullState}
    {R : Mem 64 → Prop} {best_k sc brow_off mn si m_v fs_i : Val i32}
    {dd0 dd1 ok1 dd2 ok2 : Bool} {cv64 garb irred : Val i64} {m3 : Mem 64}
    (hinv_p3 : FullDenseInvW c F0 F_next s_p3)
    (hcom_p3 : Step7BvaCommittedOk c s_p3 best_k.toNat)
    (hcv_eq : s_p3.core.cur_vars = s0.core.cur_vars + 1)
    (hcv64 : cv64 = BitVec.ofNat 64 s0.core.cur_vars)
    (hbk_sc : best_k.toNat < fidStepsCap c.scratch_cap)
    (hsc_eq : sc = BitVec.ofNat 32 (fidStepsCap c.scratch_cap))
    (hqn_all : ∀ q ≤ best_k.toNat,
      (s_p3.scratch.scratch_buf[2 * fidStepsCap c.scratch_cap + q]?.getD 0#32).toNat = mn.toNat)
    (hres : s_p3.scratch.res_sz = BitVec.ofNat 64 best_k.toNat)
    (hfuel : s_p3.core.fuel = s0.core.fuel)
    (htm : s_p3.scratch.tarjan_mark = s0.scratch.tarjan_mark)
    (htr : s_p3.scratch.tarjan_reach = s0.scratch.tarjan_reach)
    (hm3 : (FullMem c s_p3 ⋆ R) m3)
    (hQ : ∀ (ok : Bool) s' m',
      FullDenseInv c F0 s' → s0.core.cur_vars ≤ s'.core.cur_vars →
      (ok = true → s0.core.cur_vars < s'.core.cur_vars) →
      (ok = true → Step7BvaCommittedOk c s' best_k.toNat) →
      s'.core.fuel = s0.core.fuel →
      s'.scratch.tarjan_mark = s0.scratch.tarjan_mark →
      s'.scratch.tarjan_reach = s0.scratch.tarjan_reach →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    wp Γ Q X (cmtP4Expr c.hdr best_k sc c.pArena c.pScratchBuf c.pWsort c.pFlags
      c.pWvec brow_off mn dd0 cv64 c.pRepr c.pTmp si dd1 ok1 m_v dd2 ok2 garb irred fs_i) m3 := by
  have hscr := c.hscr; have har_b := c.harena; have hmx := c.hmaxv; unfold dimacsBound at *
  have hsc_le := fidStepsCap_le_256 c.scratch_cap
  have h4sc := fidStepsCap_mul4_le c.scratch_cap
  have hsc_nat : sc.toNat = fidStepsCap c.scratch_cap := by
    rw [hsc_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hbk1_32 : (best_k + 1#32).toNat = best_k.toNat + 1 := by c0_bound
  have hfv_lt : s0.core.cur_vars < c.max_vars := by have := hinv_p3.1.core_ok.cur_vars_le; omega
  have hfresh_nat : ((cv64.setWidth 32) <<< (1 : BitVec 32)).toNat = 2 * s0.core.cur_vars := by
    rw [hcv64]
    change ((BitVec.ofNat 64 s0.core.cur_vars).setWidth 32 <<< (1 : Nat)).toNat = _
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  have hfresh1_nat : (((cv64.setWidth 32) <<< (1 : BitVec 32)) ^^^ 1#32).toNat =
      2 * s0.core.cur_vars + 1 := by
    rw [hcv64]; exact FullBvaFwdHelpers.bva_bv32_shl1_xor1 (by omega)
  let sb := s_p3.scratch.scratch_buf
  refine head_wp_add rfl rfl ?_
  refine wp_while_state (α := BitVec 32 × BitVec 64 × BitVec 32 × FullState)
    (fun x => (x.1, x.2.1, x.2.2.1, ()))
    (fun x => x.2.2.1.toNat)
    (fun (_, ga, qs, sq) mq =>
      qs.toNat ≤ best_k.toNat + 1 ∧
      FullDenseInvW c F0 F_next sq ∧ Step7BvaCommittedOk c sq best_k.toNat ∧
      sq.core.cur_vars = s_p3.core.cur_vars ∧ sq.core.fuel = s0.core.fuel ∧
      sq.scratch.scratch_buf = sb ∧ sq.scratch.res_sz = BitVec.ofNat 64 best_k.toNat ∧
      sq.scratch.tarjan_mark = s0.scratch.tarjan_mark ∧
      sq.scratch.tarjan_reach = s0.scratch.tarjan_reach ∧
      (FullMem c sq ⋆ R) mq)
    (fun J4 hJ4 => by
      c0_hfast
      exact hJ4 (m_v, garb, best_k + 1#32, s_p3) m3
        ⟨by rw [hbk1_32]; exact Nat.le_refl _, hinv_p3, hcom_p3, rfl, hfuel, rfl,
          hres, htm, htr, hm3⟩)
    (fun J4 (m_cur, ga, qs, sq) mq
        ⟨hqs_le, hinv_q, hcom_q, hcv_q, hfl_q, hsb_q, hrs_q, htm_q, htr_q, hmq⟩ ih4 => ?_)
  clear hm3
  c0_hfast_nogrp
  · have hqs_pos : 0 < qs.toNat := by assumption
    have hqs1 : (qs - 1).toNat = qs.toNat - 1 := s9_bv32_sub1 hqs_pos
    have hq_le : qs.toNat - 1 ≤ best_k.toNat := by omega
    have hsq_sb_l := hinv_q.1.scratch_ok.scratch_buf_len
    have hro_i : (BitVec.setWidth 64 (sc + (qs - 1))).toNat <
        sq.scratch.scratch_buf.length := by rw [fid_bv64_32, hsq_sb_l]; c0_bound
    have hfs_i : (BitVec.setWidth 64 (qs - 1)).toNat <
        sq.scratch.scratch_buf.length := by rw [fid_bv64_32, hsq_sb_l]; c0_bound
    c0_hfast_nogrp
    let ro_q := sq.scratch.scratch_buf[(BitVec.setWidth 64 (sc + (qs - 1))).toNat]'hro_i
    let fs_q := sq.scratch.scratch_buf[(BitVec.setWidth 64 (qs - 1)).toNat]'hfs_i
    have hro_q_eq : ro_q.toNat =
        (sq.scratch.scratch_buf[fidStepsCap c.scratch_cap + (qs.toNat - 1)]?.getD 0#32).toNat := by
      have hi : (BitVec.setWidth 64 (sc + (qs - 1))).toNat =
          fidStepsCap c.scratch_cap + (qs.toNat - 1) := by rw [fid_bv64_32]; c0_bound
      dsimp only [ro_q]; rw [← hi, List.getElem?_eq_getElem hro_i, Option.getD_some]
    have hfs_q_eq : fs_q.toNat =
        (sq.scratch.scratch_buf[qs.toNat - 1]?.getD 0#32).toNat := by
      have hi : (BitVec.setWidth 64 (qs - 1)).toNat = qs.toNat - 1 := by
        rw [fid_bv64_32, hqs1]
      dsimp only [fs_q]; rw [← hi, List.getElem?_eq_getElem hfs_i, Option.getD_some]
    have hq_row := hcom_q.2.2 (qs.toNat - 1) hq_le
    have hq_qn_eq : (sq.scratch.scratch_buf[2 * fidStepsCap c.scratch_cap +
        (qs.toNat - 1)]?.getD 0#32).toNat = mn.toNat := by rw [hsb_q]; exact hqn_all _ hq_le
    refine wp_while_state (α := BitVec 32 × BitVec 64 × FullState)
      (fun x => (x.1, x.2.1, ()))
      (fun x => mn.toNat - x.1.toNat)
      (fun (mi, gai, sm) mm =>
        mi.toNat ≤ mn.toNat ∧
        FullDenseInvW c F0 F_next sm ∧ Step7BvaCommittedOk c sm best_k.toNat ∧
        sm.core.cur_vars = s_p3.core.cur_vars ∧ sm.core.fuel = s0.core.fuel ∧
        sm.scratch.scratch_buf = sb ∧ sm.scratch.res_sz = BitVec.ofNat 64 best_k.toNat ∧
        sm.scratch.tarjan_mark = s0.scratch.tarjan_mark ∧
        sm.scratch.tarjan_reach = s0.scratch.tarjan_reach ∧
        (FullMem c sm ⋆ R) mm)
      (fun Jm hJm => by
        c0_hfast
        exact hJm (0#32, ga, sq) mq
          ⟨Nat.zero_le _, hinv_q, hcom_q, hcv_q, hfl_q, hsb_q, hrs_q, htm_q, htr_q, hmq⟩)
      (fun Jm (mi, gai, sm) mm
          ⟨hmi_le, hinv_m, hcom_m, hcv_m, hfl_m, hsb_m, hrs_m, htm_m, htr_m, hmm⟩ ihm => ?_)
    c0_hfast_nogrp
    · have hmi_lt : mi.toNat < mn.toNat := by assumption
      have hsm_sb_l := hinv_m.1.scratch_ok.scratch_buf_len
      have hro_mi_lt : (BitVec.setWidth 64 (ro_q + mi)).toNat <
          sm.scratch.scratch_buf.length := by
        rw [fid_bv64_32, hsm_sb_l]
        have := hq_row.2.1; rw [hq_qn_eq, ← hro_q_eq] at this; c0_bound
      have hmi1 : (mi + 1#32).toNat = mi.toNat + 1 := by
        have := hq_row.2.1; rw [hq_qn_eq, ← hro_q_eq] at this; c0_bound
      c0_hfast_nogrp
      let cs := sm.scratch.scratch_buf[(BitVec.setWidth 64 (ro_q + mi)).toNat]'hro_mi_lt
      have hcs_ok : Step7RowRefOk sm cs := by
        have h1 := (hcom_m.2.2 (qs.toNat - 1) hq_le).2.2 mi.toNat
          (by rw [hsb_m, hqn_all _ hq_le]; exact hmi_lt)
        have hidx : (BitVec.setWidth 64 (ro_q + mi)).toNat =
            (sm.scratch.scratch_buf[fidStepsCap c.scratch_cap +
              (qs.toNat - 1)]?.getD 0#32).toNat + mi.toNat := by
          rw [fid_bv64_32]; have := hq_row.2.1; rw [hq_qn_eq, ← hro_q_eq] at this
          rw [hsb_m, ← hsb_q, ← hro_q_eq]; c0_bound
        have hceq : cs = sm.scratch.scratch_buf[(sm.scratch.scratch_buf[fidStepsCap c.scratch_cap +
            (qs.toNat - 1)]?.getD 0#32).toNat + mi.toNat]?.getD 0#32 := by
          dsimp only [cs]; rw [← hidx, List.getElem?_eq_getElem hro_mi_lt, Option.getD_some]
        rw [hceq]; exact h1
      refine wp_join_state1 (t := i64) (α := BitVec 64 × FullState) (fun x => x.1)
        (fun (ga', sm') mm' =>
          FullDenseInvW c F0 F_next sm' ∧ Step7BvaCommittedOk c sm' best_k.toNat ∧
          sm'.core.cur_vars = s_p3.core.cur_vars ∧ sm'.core.fuel = s0.core.fuel ∧
          sm'.scratch.scratch_buf = sb ∧ sm'.scratch.res_sz = BitVec.ofNat 64 best_k.toNat ∧
          sm'.scratch.tarjan_mark = s0.scratch.tarjan_mark ∧
          sm'.scratch.tarjan_reach = s0.scratch.tarjan_reach ∧
          (FullMem c sm' ⋆ R) mm')
        (fun _ (ga', sm') mm' ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ => by
          c0_hfast
          exact ihm (mi + 1#32, ga', sm') mm' (by dsimp only; rw [hmi1]; omega)
            ⟨by rw [hmi1]; omega, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩)
        (fun Jga hJga => ?_)
      c0_hfast_nogrp
      · have hbin : (cs &&& 0x80000000#32) ≠ 0#32 := by
          have h1 : (BitVec.setWidth 64 (sc + (qs - 1))).toNat =
              (sc.toNat + (2 ^ 32 - 1 + qs.toNat)) % 2 ^ 32 := by rw [fid_bv64_32]; c0_bound
          have h2 : (BitVec.setWidth 64 (ro_q + mi)).toNat =
              ((sq.scratch.scratch_buf[(sc.toNat + (2 ^ 32 - 1 + qs.toNat)) % 2 ^ 32]'(by
                rw [← h1]; exact hro_i)).toNat + mi.toNat) % 2 ^ 32 := by
            rw [fid_bv64_32, BitVec.toNat_add]; congr 1; congr 1; congr 1
            dsimp only [ro_q]; exact cmt1_getElem_eq h1
          have hcs_eq : cs = sm.scratch.scratch_buf[((sq.scratch.scratch_buf[(sc.toNat +
              (2 ^ 32 - 1 + qs.toNat)) % 2 ^ 32]'(by rw [← h1]; exact hro_i)).toNat +
              mi.toNat) % 2 ^ 32]'(by rw [← h2]; exact hro_mi_lt) := by
            dsimp only [cs]; exact cmt1_getElem_eq h2
          rw [hcs_eq]; exact hc
        have hq_lt : (cs &&& 0x7FFFFFFF#32).toNat < 2 * sm.core.cur_vars := by
          unfold Step7RowRefOk at hcs_ok; rwa [ite_eq_left hbin] at hcs_ok
        have hfs_lt : fs_q.toNat < 2 * c.max_vars := by
          have := hq_row.1; rw [← hfs_q_eq, hcv_q] at this
          have := hinv_p3.1.core_ok.cur_vars_le; omega
        have hq_lt_mx : (cs &&& 0x7FFFFFFF#32).toNat < 2 * c.max_vars := by
          have := hinv_m.1.core_ok.cur_vars_le; omega
        fid_call hDelBin
        refine ⟨c, sm, R, rfl, hinv_m.1, (m6_denseWatchesInv_of_w hinv_m).layout,
          hfs_lt, hq_lt_mx, hmm, fun fl' wv' ws' wu' nb' mm' hlen' _ hwat hmm' => ?_⟩
        c0_hfast
        exact hJga (gai, _) mm'
          ⟨cmt_fullDenseInvW_delBin hinv_m hlen' (hwat F_next hinv_m.2.1.watches),
           hcom_m.congr rfl rfl rfl rfl rfl, hcv_m, hfl_m, hsb_m, hrs_m, htm_m, htr_m, hmm'⟩
      · have h1 : (BitVec.setWidth 64 (sc + (qs - 1))).toNat =
            (sc.toNat + (2 ^ 32 - 1 + qs.toNat)) % 2 ^ 32 := by rw [fid_bv64_32]; c0_bound
        have h2 : (BitVec.setWidth 64 (ro_q + mi)).toNat =
            ((sq.scratch.scratch_buf[(sc.toNat + (2 ^ 32 - 1 + qs.toNat)) % 2 ^ 32]'(by
              rw [← h1]; exact hro_i)).toNat + mi.toNat) % 2 ^ 32 := by
          rw [fid_bv64_32, BitVec.toNat_add]; congr 1; congr 1; congr 1
          dsimp only [ro_q]; exact cmt1_getElem_eq h1
        have hcs_eq : cs = sm.scratch.scratch_buf[((sq.scratch.scratch_buf[(sc.toNat +
            (2 ^ 32 - 1 + qs.toNat)) % 2 ^ 32]'(by rw [← h1]; exact hro_i)).toNat +
            mi.toNat) % 2 ^ 32]'(by rw [← h2]; exact hro_mi_lt) := by
          dsimp only [cs]; exact cmt1_getElem_eq h2
        have hnb : (cs &&& 0x80000000#32) = 0#32 := by rw [hcs_eq]; exact hc
        have hlar := hcs_ok
        unfold Step7RowRefOk at hlar; rw [ite_eq_right (fun h => h hnb)] at hlar
        obtain ⟨hcs_ref, hcs_bd, hcs_lits⟩ := hlar
        have hcs2_lt : (BitVec.setWidth 64 cs + 2#64).toNat < sm.core.arena.length := by
          rw [hinv_m.1.core_ok.arena_len_arr]; have := hinv_m.1.core_ok.arena_len_le
          have : cs.toNat + 2 < sm.core.arena_len := by omega
          c0_bound
        c0_hfast_nogrp
        let csz := sm.core.arena[(BitVec.setWidth 64 cs + 2#64).toNat]'hcs2_lt
        have hcsz_eq : csz.toNat = fullArenaClauseSize sm cs.toNat := by
          have h2 : (BitVec.setWidth 64 cs + 2#64).toNat = cs.toNat + 2 := by
            have := hinv_m.1.core_ok.arena_len_le; c0_bound
          unfold fullArenaClauseSize fullArenaClauseSizeCore
          apply congrArg BitVec.toNat; apply Option.some.inj
          rw [← List.getElem?_eq_getElem hcs2_lt, h2,
            List.getElem?_eq_getElem (by rw [hinv_m.1.core_ok.arena_len_arr]
                                         have := hinv_m.1.core_ok.arena_len_le; omega),
            Option.getD_some]
        refine wp_while_state1 (t := i32) (α := BitVec 32 × FullState) (fun x => x.1)
          (fun x => csz.toNat - x.1.toNat)
          (fun (k, sk) mk =>
            k.toNat ≤ csz.toNat ∧
            FullDenseInvW c F0 F_next sk ∧ Step7BvaCommittedOk c sk best_k.toNat ∧
            sk.core.cur_vars = s_p3.core.cur_vars ∧ sk.core.fuel = s0.core.fuel ∧
            sk.core.arena = sm.core.arena ∧ sk.core.arena_len = sm.core.arena_len ∧
            sk.scratch.scratch_buf = sb ∧ sk.scratch.res_sz = BitVec.ofNat 64 best_k.toNat ∧
            sk.scratch.tarjan_mark = s0.scratch.tarjan_mark ∧
            sk.scratch.tarjan_reach = s0.scratch.tarjan_reach ∧
            (FullMem c sk ⋆ R) mk)
          (fun Jk hJk => by
            c0_hfast
            exact hJk (0#32, sm) mm
              ⟨Nat.zero_le _, hinv_m, hcom_m, hcv_m, hfl_m, rfl, rfl,
               hsb_m, hrs_m, htm_m, htr_m, hmm⟩)
          (fun Jk (k, sk) mk
              ⟨hk_le, hinv_k, hcom_k, hcv_k, hfl_k, har_k, hal_k,
               hsb_k, hrs_k, htm_k, htr_k, hmk⟩ ihk => ?_)
        c0_hfast_nogrp
        · have hk_lt : k.toNat < csz.toNat := by
            have h3 : (BitVec.setWidth 64 cs + 2#64).toNat =
                ((sm.scratch.scratch_buf[((sq.scratch.scratch_buf[(sc.toNat +
                  (2 ^ 32 - 1 + qs.toNat)) % 2 ^ 32]'(by rw [← h1]; exact hro_i)).toNat +
                  mi.toNat) % 2 ^ 32]'(by rw [← h2]; exact hro_mi_lt)).toNat +
                  (2 : BitVec 64).toNat) % 2 ^ 64 := by
              rw [BitVec.toNat_add, fid_bv64_32, hcs_eq]; rfl
            have heq : csz = sm.core.arena[((sm.scratch.scratch_buf[((sq.scratch.scratch_buf[(
                sc.toNat + (2 ^ 32 - 1 + qs.toNat)) % 2 ^ 32]'(by rw [← h1]; exact hro_i)).toNat +
                mi.toNat) % 2 ^ 32]'(by rw [← h2]; exact hro_mi_lt)).toNat +
                (2 : BitVec 64).toNat) % 2 ^ 64]'(by rw [← h3]; exact hcs2_lt) := by
              dsimp only [csz]; exact cmt1_getElem_eq h3
            rw [heq]; exact hc
          have hidx_k : (BitVec.setWidth 64 cs + 3#64 + BitVec.setWidth 64 k).toNat <
              sk.core.arena.length := by
            rw [hinv_k.1.core_ok.arena_len_arr]
            have := hinv_k.1.core_ok.arena_len_le; c0_bound
          have hidx_k_eq : (BitVec.setWidth 64 cs + 3#64 + BitVec.setWidth 64 k).toNat =
              cs.toNat + 3 + k.toNat := by
            have := hinv_k.1.core_ok.arena_len_le; c0_bound
          have hdl_lt : (sk.core.arena[(BitVec.setWidth 64 cs + 3#64 +
              BitVec.setWidth 64 k).toNat]'hidx_k).toNat < 2 * sm.core.cur_vars := by
            have hlt_sm : cs.toNat + 3 + k.toNat < sm.core.arena.length := by
              rw [← har_k, ← hidx_k_eq]; exact hidx_k
            have hmem : (sk.core.arena[(BitVec.setWidth 64 cs + 3#64 +
                BitVec.setWidth 64 k).toNat]'hidx_k).toNat ∈ fullArenaClauseLits sm cs.toNat := by
              have h1 := fullArenaClauseLitsCore_getElem (k := sm.core) (r := cs.toNat)
                (j := k.toNat)
                (by change k.toNat < fullArenaClauseSize sm cs.toNat; rw [← hcsz_eq]; exact hk_lt)
                hlt_sm
              have h2 : sk.core.arena[(BitVec.setWidth 64 cs + 3#64 +
                  BitVec.setWidth 64 k).toNat]'hidx_k =
                  sm.core.arena[cs.toNat + 3 + k.toNat]'hlt_sm := by
                apply Option.some.inj
                rw [← List.getElem?_eq_getElem hidx_k, hidx_k_eq, har_k,
                  List.getElem?_eq_getElem]
              rw [h2]; exact List.mem_of_getElem? h1
            exact hcs_lits _ hmem
          have hdl_v : (BitVec.setWidth 64 ((sk.core.arena[(BitVec.setWidth 64 cs + 3#64 +
              BitVec.setWidth 64 k).toNat]'hidx_k) >>> (1 : Nat))).toNat <
              sk.core.flags.length := by
            rw [fid_bv64_32, bv32_lshr_1, hinv_k.1.core_ok.flags_len]
            have := hinv_m.1.core_ok.cur_vars_le; omega
          have hk1 : (k + 1#32).toNat = k.toNat + 1 := by
            have := hinv_k.1.core_ok.arena_len_le; c0_bound
          c0_hfast_nogrp
          obtain ⟨fl', hfl'_l, hm_fl⟩ : ∃ fl', fl'.length = c.max_vars ∧
              (FullMem c { sk with core := { sk.core with flags := fl' } } ⋆ R) m :=
            ⟨_, by simp only [List.length_set]; exact hinv_k.1.core_ok.flags_len, hm⟩
          let sk_fl : FullState := { sk with core := { sk.core with flags := fl' } }
          have hinv_kfl : FullDenseInvW c F0 F_next sk_fl :=
            cmt_fullDenseInvW_set_flags hinv_k hfl'_l
          fid_call hUnwatch
          refine ⟨c, sk_fl, R, rfl, hinv_kfl.1, (m6_denseWatchesInv_of_w hinv_kfl).layout, hm_fl,
            fun wv' ws' wu' mk' hlen' _ hwat hmk' => ?_⟩
          c0_hfast
          exact ihk (k + 1#32, _) mk' (by dsimp only; rw [hk1]; omega)
            ⟨by rw [hk1]; omega,
             cmt_fullDenseInvW_unwatch hinv_kfl hlen' (hwat F_next hinv_kfl.2.1.watches),
             hcom_k.congr rfl rfl rfl rfl rfl, hcv_k, hfl_k, har_k, hal_k,
             hsb_k, hrs_k, htm_k, htr_k, hmk'⟩
        · have hcs_ar_lt : (BitVec.setWidth 64 cs).toNat < sk.core.arena.length := by
            rw [fid_bv64_32, hinv_k.1.core_ok.arena_len_arr]
            have := hinv_k.1.core_ok.arena_len_le; omega
          have hcs_ref_k : cs.toNat ∈ fullArenaClauseRefs sk := by
            unfold fullArenaClauseRefs fullArenaClauseRefsCore
            rw [har_k, hal_k]; exact hcs_ref
          c0_hfast
          have hset_mg : sk.core.arena.set (BitVec.setWidth 64 cs).toNat
                (sk.core.arena[(BitVec.setWidth 64 cs).toNat]'hcs_ar_lt ||| 524288) =
              sk.core.arena.set cs.toNat (fullArenaHdr sk cs.toNat ||| 0x00080000#32) := by
            have hlt2 : cs.toNat < sk.core.arena.length := by rwa [fid_bv64_32] at hcs_ar_lt
            have hget : sk.core.arena[(BitVec.setWidth 64 cs).toNat]'hcs_ar_lt =
                fullArenaHdr sk cs.toNat := by
              unfold fullArenaHdr fullArenaHdrCore
              rw [List.getElem?_eq_getElem hlt2, Option.getD_some]
              exact cmt1_getElem_eq (fid_bv64_32 cs)
            rw [hget, fid_bv64_32]; rfl
          dsimp only [cs, ro_q] at hset_mg; dsimp only at hm; rw [hset_mg] at hm
          exact hJga (gai + 3#64 + BitVec.setWidth 64 csz, _) m
            ⟨(cmt_fullDenseInvW_markGarb hinv_k hcs_ref_k).1,
             Step7BvaCommittedOk.of_markGarb hinv_k hcs_ref_k hcom_k,
             hcv_k, hfl_k, hsb_k, hrs_k, htm_k, htr_k, hm⟩
    · c0_hfast
      exact ih4 (mi, gai, qs - 1, sm) mm (by dsimp only; rw [hqs1]; omega)
        ⟨by rw [hqs1]; omega, hinv_m, hcom_m, hcv_m, hfl_m, hsb_m, hrs_m, htm_m, htr_m, hmm⟩
  -- Epilogue
  refine wp_join0 (fun m1 => ∃ ag1,
      let s1 := { sq with core := { sq.core with arena_garbage := ag1 } }
      FullDenseInvW c F0 F_next s1 ∧ Step7BvaCommittedOk c s1 best_k.toNat ∧ (FullMem c s1 ⋆ R) m1)
    (fun _ m1 ⟨ag1, hinv1, hcom1, hm1⟩ => ?_)
    (fun J1 hJ1 => by
      c0_hfast_nogrp
      · c0_hfast
        exact hJ1 m ⟨sq.core.arena_garbage + ga, cmt_fullDenseInvW_set_garb hinv_q _,
          hcom_q.congr rfl rfl rfl rfl rfl, hm⟩
      · c0_hfast; exact hJ1 mq ⟨sq.core.arena_garbage, hinv_q, hcom_q, hmq⟩)
  let s1 : FullState := { sq with core := { sq.core with arena_garbage := ag1 } }
  refine wp_join0 (fun m2 => ∃ ni2,
      let s2 := { s1 with core := { s1.core with num_irred := ni2 } }
      FullDenseInvW c F0 F_next s2 ∧ Step7BvaCommittedOk c s2 best_k.toNat ∧ (FullMem c s2 ⋆ R) m2)
    (fun _ m2 ⟨ni2, hinv2, hcom2, hm2⟩ => ?_)
    (fun J2 hJ2 => by
      c0_hfast_nogrp
      · c0_hfast
        exact hJ2 m ⟨s1.core.num_irred + irred, cmt_fullDenseInvW_set_irred hinv1 _,
          hcom1.congr rfl rfl rfl rfl rfl, hm⟩
      · c0_hfast; exact hJ2 m1 ⟨s1.core.num_irred, hinv1, hcom1, hm1⟩)
  let s2 : FullState := { s1 with core := { s1.core with num_irred := ni2 } }
  refine wp_join0 (fun m3 => ∃ ws3,
      let s3 := { s2 with scratch := { s2.scratch with wsort := ws3 } }
      FullDenseInvW c F0 F_next s3 ∧ Step7BvaCommittedOk c s3 best_k.toNat ∧ (FullMem c s3 ⋆ R) m3)
    (fun _ m3 ⟨ws3, hinv3, hcom3, hm3⟩ => ?_)
    (fun J3 hJ3 => by
      c0_hfast_nogrp
      · fid_call hFill
        refine cmt_fill_wsort_spec hinv2.1 hm2 fun ws3 m3 hws3 hm3 => ?_
        c0_hfast
        exact hJ3 m3 ⟨ws3, cmt_fullDenseInvW_set_wsort hinv2 hws3,
          hcom2.congr rfl rfl rfl rfl rfl, hm3⟩
      · c0_hfast; exact hJ3 m2 ⟨s2.scratch.wsort, hinv2, hcom2, hm2⟩)
  let s3 : FullState := { s2 with scratch := { s2.scratch with wsort := ws3 } }
  have hfr0_rp : (BitVec.setWidth 64 ((cv64.setWidth 32) <<< (1 : BitVec 32))).toNat <
      s3.core.repr.length := by
    rw [fid_bv64_32, hfresh_nat, hinv3.1.core_ok.repr_len]; omega
  have hfr1_rp : (BitVec.setWidth 64 (((cv64.setWidth 32) <<< (1 : BitVec 32)) ^^^ 1#32)).toNat <
      (s3.core.repr.set (BitVec.setWidth 64 ((cv64.setWidth 32) <<< (1 : BitVec 32))).toNat
        (best_k + 1#32)).length := by
    rw [List.length_set, fid_bv64_32, hfresh1_nat, hinv3.1.core_ok.repr_len]; omega
  c0_hfast
  refine hQ true _ m ?_ ?_ ?_ ?_ ?_ ?_ ?_ hm
  · exact (cmt_fullDenseInvW_set_bva_cnt
      (fullDenseInvW_set_repr hinv3 (by simp [hinv3.1.core_ok.repr_len])) _).toDense
  · dsimp only [s3, s2, s1]; omega
  · intro _; dsimp only [s3, s2, s1]; omega
  · intro _; exact hcom3.congr rfl rfl rfl rfl rfl
  · exact hfl_q
  · exact htm_q
  · exact htr_q

/-! ## 2. Phase 3 Reverse Compaction & Combined Exit WP -/

private theorem cmt_ok_exit_wp {Γ : Env} {Q : Post [.bool]} {X : XPost}
    (hFill : ∀ a m Q X, Limits.Spec.m7FillU64Spec a m Q X →
      Γ "full_fill_u64_m7" [i64, i64, i64] [] a m Q X)
    (hDelBin : ∀ a m Q X, Watch.Spec.fullDeleteBinarySpec a m Q X →
      Γ "full_delete_binary" [i64, i32, i32] [] a m Q X)
    (hUnwatch : ∀ a m Q X, fullUnwatchLargeSpec a m Q X →
      Γ "full_unwatch_large" [i64, i32, i32] [] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur F_next : List (List Nat)} {s0 s : FullState}
    {R : Mem 64 → Prop} {best_k sc brow_off mn si m_v : Val i32}
    {dd0 dd1 ok1 dd2 ok2 : Bool} {cv64 garb irred : Val i64} {bump : Nat} {mp : Mem 64}
    (hl0 : s0.LengthsOk c) (hw0 : FullWitnessInv c F0 F_cur s0.core)
    (hinv : FullDenseInvW c F0 F_next s) (hext : CommitArenaExt s0 s)
    (hcv_eq : s.core.cur_vars = s0.core.cur_vars + 1)
    (hcv64 : cv64 = BitVec.ofNat 64 s0.core.cur_vars)
    (hbk1 : 1 ≤ best_k.toNat) (hbk_sc : best_k.toNat < fidStepsCap c.scratch_cap)
    (hsc_eq : sc = BitVec.ofNat 32 (fidStepsCap c.scratch_cap))
    (hmn_eq : mn.toNat = (s0.scratch.scratch_buf[2 * fidStepsCap c.scratch_cap +
      best_k.toNat]?.getD 0#32).toNat)
    (hmat : Step7BvaMatrixInv c F_cur s0 (best_k.toNat + 1) bump)
    (hsb_eq : s.scratch.scratch_buf = s0.scratch.scratch_buf)
    (hres : s.scratch.res_sz = BitVec.ofNat 64 best_k.toNat)
    (hfuel : s.core.fuel = s0.core.fuel)
    (htm : s.scratch.tarjan_mark = s0.scratch.tarjan_mark)
    (htr : s.scratch.tarjan_reach = s0.scratch.tarjan_reach)
    (hmp : (FullMem c s ⋆ R) mp)
    (hQ : ∀ (ok : Bool) s' m',
      FullDenseInv c F0 s' → s0.core.cur_vars ≤ s'.core.cur_vars →
      (ok = true → s0.core.cur_vars < s'.core.cur_vars) →
      (ok = true → Step7BvaCommittedOk c s' best_k.toNat) →
      s'.core.fuel = s0.core.fuel →
      s'.scratch.tarjan_mark = s0.scratch.tarjan_mark →
      s'.scratch.tarjan_reach = s0.scratch.tarjan_reach →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    wp Γ Q X (cmtThen (cmtP2ExitExpr c.hdr best_k sc c.pArena c.pScratchBuf c.pWsort c.pFlags
      c.pWvec brow_off mn dd0 cv64 c.pRepr c.pTmp si dd1 ok1 m_v dd2 ok2 garb irred)) mp := by
  have hscr := c.hscr; have hsc_le := fidStepsCap_le_256 c.scratch_cap
  have h4sc := fidStepsCap_mul4_le c.scratch_cap; unfold dimacsBound at *
  have hsc_nat : sc.toNat = fidStepsCap c.scratch_cap := by
    rw [hsc_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine wp_while_state1 (t := i32) (α := BitVec 32 × List (BitVec 32)) (fun x => x.1)
    (fun x => x.1.toNat)
    (fun (fs_i, sb) m3 =>
      fs_i.toNat ≤ best_k.toNat ∧
      Step7BvaCompactInv c s0 s best_k.toNat mn.toNat fs_i.toNat sb ∧
      (FullMem c { s with scratch := { s.scratch with scratch_buf := sb } } ⋆ R) m3)
    (fun J3 hJ3 => by
      c0_hfast
      have hc0 := step7BvaCompactInv_init hl0 hinv.1 hw0 hext (by omega) hbk_sc hmat
      dsimp only at hc0; rw [← hmn_eq] at hc0
      exact hJ3 (best_k, s0.scratch.scratch_buf) mp ⟨Nat.le_refl _, hc0, by rwa [← hsb_eq]⟩)
    (fun J3 (fs_i, sb) m3 ⟨hfs_le, hcomp, hm3⟩ ih3 => ?_)
  clear hmp
  c0_hfast_nogrp
  · have hfs_pos : 0 < fs_i.toNat := by assumption
    have hsb_l := hcomp.1
    have hfs_sub : (fs_i - 1#32).toNat = fs_i.toNat - 1 := s9_bv32_sub1 hfs_pos
    have hro_idx : (BitVec.setWidth 64 (sc + (fs_i - 1))).toNat < sb.length := by
      rw [fid_bv64_32, hsb_l]; c0_bound
    have hpo_idx : (BitVec.setWidth 64 (3 * sc + fs_i)).toNat < sb.length := by
      rw [fid_bv64_32, hsb_l]; c0_bound
    let ro_prev := sb[(BitVec.setWidth 64 (sc + (fs_i - 1))).toNat]'hro_idx
    let po_s := sb[(BitVec.setWidth 64 (3 * sc + fs_i)).toNat]'hpo_idx
    have hro_nat : ro_prev.toNat =
        (s0.scratch.scratch_buf[fidStepsCap c.scratch_cap +
          (fs_i.toNat - 1)]?.getD 0#32).toNat := by
      have hi : (BitVec.setWidth 64 (sc + (fs_i - 1))).toNat =
          fidStepsCap c.scratch_cap + (fs_i.toNat - 1) := by rw [fid_bv64_32]; c0_bound
      dsimp only [ro_prev]; apply congrArg BitVec.toNat; apply Option.some.inj
      rw [← List.getElem?_eq_getElem hro_idx, hi, hcomp.2.2.1 (fs_i.toNat - 1) (by omega),
        List.getElem?_eq_getElem (by rw [hl0.scratch_ok.scratch_buf_len]; omega), Option.getD_some]
    have hpo_nat : po_s.toNat =
        (s0.scratch.scratch_buf[3 * fidStepsCap c.scratch_cap + fs_i.toNat]?.getD 0#32).toNat := by
      have hi : (BitVec.setWidth 64 (3 * sc + fs_i)).toNat =
          3 * fidStepsCap c.scratch_cap + fs_i.toNat := by rw [fid_bv64_32]; c0_bound
      dsimp only [po_s]; apply congrArg BitVec.toNat; apply Option.some.inj
      rw [← List.getElem?_eq_getElem hpo_idx, hi, hcomp.2.2.2.1 fs_i.toNat hfs_le,
        List.getElem?_eq_getElem (by rw [hl0.scratch_ok.scratch_buf_len]; omega), Option.getD_some]
    c0_hfast_nogrp
    refine wp_join_state1 (t := i32) (α := BitVec 32) id
      (fun po_prev mp0 => mp0 = m3 ∧
        (1 < fs_i.toNat → po_prev.toNat =
          (s0.scratch.scratch_buf[3 * fidStepsCap c.scratch_cap +
            (fs_i.toNat - 1)]?.getD 0#32).toNat))
      (fun _ po_prev mp0 ⟨hmp0, hpop_nat⟩ => ?_)
      (fun Jpop hJpop => by
        c0_hfast_nogrp
        · have hfs1 : 1 < fs_i.toNat := by assumption
          have hpop_idx : (BitVec.setWidth 64 (3 * sc + (fs_i - 1))).toNat < sb.length := by
            rw [fid_bv64_32, hsb_l]; c0_bound
          c0_hfast
          refine hJpop _ m3 ⟨rfl, fun _ => ?_⟩
          have hi : (BitVec.setWidth 64 (3 * sc + (fs_i - 1))).toNat =
              3 * fidStepsCap c.scratch_cap + (fs_i.toNat - 1) := by rw [fid_bv64_32]; c0_bound
          dsimp only; apply congrArg BitVec.toNat; apply Option.some.inj
          rw [← List.getElem?_eq_getElem hpop_idx, hi, hcomp.2.2.2.1 (fs_i.toNat - 1) (by omega),
            List.getElem?_eq_getElem (by rw [hl0.scratch_ok.scratch_buf_len]; omega),
            Option.getD_some]
        · have hfs1 : ¬ (1 < fs_i.toNat) := by assumption
          c0_hfast; exact hJpop 0#32 m3 ⟨rfl, fun h => absurd h hfs1⟩)
    rw [hmp0]
    have hmn_le_s : mn.toNat ≤
        (s0.scratch.scratch_buf[2 * fidStepsCap c.scratch_cap + fs_i.toNat]?.getD 0#32).toNat := by
      by_cases hfb : fs_i.toNat = best_k.toNat
      · rw [hmn_eq, hfb]; exact Nat.le_refl _
      · rw [hmn_eq]; exact (hmat.2.2 fs_i.toNat best_k.toNat (by omega) (by omega)).1
    have hmn_le_p : mn.toNat ≤
        (s0.scratch.scratch_buf[2 * fidStepsCap c.scratch_cap +
          (fs_i.toNat - 1)]?.getD 0#32).toNat := by
      rw [hmn_eq]; exact (hmat.2.2 (fs_i.toNat - 1) best_k.toNat (by omega) (by omega)).1
    have hrow_s := hmat.1.2.2.2.2.2 fs_i.toNat (by omega)
    have hrow_p := hmat.1.2.2.2.2.2 (fs_i.toNat - 1) (by omega)
    refine wp_while_state1 (t := i32) (α := BitVec 32 × List (BitVec 32)) (fun x => x.1)
      (fun x => mn.toNat - x.1.toNat)
      (fun (fi, sbi) mfi =>
        fi.toNat ≤ mn.toNat ∧
        Step7BvaCompactInv c s0 s best_k.toNat mn.toNat fs_i.toNat sbi ∧
        (FullMem c { s with scratch := { s.scratch with scratch_buf := sbi } } ⋆ R) mfi)
      (fun Jfi hJfi => by c0_hfast; exact hJfi (0#32, sb) m3 ⟨Nat.zero_le _, hcomp, hm3⟩)
      (fun Jfi (fi, sbi) mfi ⟨hfi_le, hci, hmfi⟩ ihfi => ?_)
    have hsbi_l := hci.1
    c0_hfast_nogrp
    · have hfi_lt : fi.toNat < mn.toNat := by assumption
      have hpo_fi_lt : (BitVec.setWidth 64 (po_s + fi)).toNat < sbi.length := by
        rw [fid_bv64_32, hsbi_l]
        have := (hrow_s.2.2.2.2.1 hfs_pos).2; have := hmat.1.2.2.2.2.1; c0_bound
      c0_hfast_nogrp
      let fj := sbi[(BitVec.setWidth 64 (po_s + fi)).toNat]'hpo_fi_lt
      have hfj_lt : fj.toNat <
          (s0.scratch.scratch_buf[2 * fidStepsCap c.scratch_cap +
            (fs_i.toNat - 1)]?.getD 0#32).toNat := by
        have hi : (BitVec.setWidth 64 (po_s + fi)).toNat =
            (s0.scratch.scratch_buf[3 * fidStepsCap c.scratch_cap + fs_i.toNat]?.getD 0#32).toNat +
              fi.toNat := by
          rw [fid_bv64_32, ← hpo_nat]; have := (hrow_s.2.2.2.2.1 hfs_pos).2
          have := hmat.1.2.2.2.2.1; c0_bound
        have h1 := (hci.2.2.2.2.2 fs_i.toNat hfs_le).2 hfs_pos fi.toNat (by omega)
        have h2 : fj = sbi[(s0.scratch.scratch_buf[3 * fidStepsCap c.scratch_cap +
            fs_i.toNat]?.getD 0#32).toNat + fi.toNat]?.getD 0#32 := by
          dsimp only [fj]; rw [← hi, List.getElem?_eq_getElem hpo_fi_lt, Option.getD_some]
        rw [h2]; exact h1
      refine wp_join0 (fun mfj => ∃ sbi1,
          Step7BvaCompactInv c s0 s best_k.toNat mn.toNat fs_i.toNat sbi1 ∧
          (FullMem c { s with scratch := { s.scratch with scratch_buf := sbi1 } } ⋆ R) mfj)
        (fun _ mfj ⟨sbi1, hci1, hmfj⟩ => by
          have hsbi1_l := hci1.1
          have hro_fi : (BitVec.setWidth 64 (ro_prev + fi)).toNat < sbi1.length := by
            rw [fid_bv64_32, hsbi1_l]; have := hrow_p.2.2.2.1; have := hmat.1.2.2.2.2.1; c0_bound
          have hro_fj : (BitVec.setWidth 64 (ro_prev + fj)).toNat < sbi1.length := by
            rw [fid_bv64_32, hsbi1_l]; have := hrow_p.2.2.2.1; have := hmat.1.2.2.2.2.1; c0_bound
          have hfi1 : (fi + 1#32).toNat = fi.toNat + 1 := by
            have := hrow_p.2.2.2.1; have := hmat.1.2.2.2.2.1; c0_bound
          c0_hfast
          have hset_eq : sbi1.set (BitVec.setWidth 64 (ro_prev + fi)).toNat
                (sbi1[(BitVec.setWidth 64 (ro_prev + fj)).toNat]'hro_fj) =
              sbi1.set ((s0.scratch.scratch_buf[fidStepsCap c.scratch_cap +
                (fs_i.toNat - 1)]?.getD 0#32).toNat + fi.toNat)
                (sbi1[(s0.scratch.scratch_buf[fidStepsCap c.scratch_cap +
                  (fs_i.toNat - 1)]?.getD 0#32).toNat + fj.toNat]?.getD 0#32) := by
            have h1 : (BitVec.setWidth 64 (ro_prev + fi)).toNat =
                (s0.scratch.scratch_buf[fidStepsCap c.scratch_cap +
                  (fs_i.toNat - 1)]?.getD 0#32).toNat + fi.toNat := by
              rw [fid_bv64_32, ← hro_nat]; have := hrow_p.2.2.2.1
              have := hmat.1.2.2.2.2.1; c0_bound
            have h2 : (BitVec.setWidth 64 (ro_prev + fj)).toNat =
                (s0.scratch.scratch_buf[fidStepsCap c.scratch_cap +
                  (fs_i.toNat - 1)]?.getD 0#32).toNat + fj.toNat := by
              rw [fid_bv64_32, ← hro_nat]; have := hrow_p.2.2.2.1
              have := hmat.1.2.2.2.2.1; c0_bound
            rw [← h1, ← h2, List.getElem?_eq_getElem hro_fj, Option.getD_some]
          dsimp only [ro_prev, po_s, fj] at hset_eq; dsimp only at hm; rw [hset_eq] at hm
          exact ihfi (fi + 1#32, _) m (by dsimp only; rw [hfi1]; omega)
            ⟨by rw [hfi1]; omega,
             step7BvaCompactInv_set_row hmat hci1 (by omega) (by omega) hfj_lt, hm⟩)
        (fun Jp hJp => by
          c0_hfast_nogrp
          · have hfs1 : 1 < fs_i.toNat := by assumption
            have hpp := hpop_nat hfs1
            have hpop_fi : (BitVec.setWidth 64 (po_prev + fi)).toNat < sbi.length := by
              rw [fid_bv64_32, hsbi_l]; have := (hrow_p.2.2.2.2.1 (by omega)).2
              have := hmat.1.2.2.2.2.1; c0_bound
            have hpop_fj : (BitVec.setWidth 64 (po_prev + fj)).toNat < sbi.length := by
              rw [fid_bv64_32, hsbi_l]; have := (hrow_p.2.2.2.2.1 (by omega)).2
              have := hmat.1.2.2.2.2.1; c0_bound
            c0_hfast
            have hset_eq : sbi.set (BitVec.setWidth 64 (po_prev + fi)).toNat
                  (sbi[(BitVec.setWidth 64 (po_prev + fj)).toNat]'hpop_fj) =
                sbi.set ((s0.scratch.scratch_buf[3 * fidStepsCap c.scratch_cap +
                  (fs_i.toNat - 1)]?.getD 0#32).toNat + fi.toNat)
                  (sbi[(s0.scratch.scratch_buf[3 * fidStepsCap c.scratch_cap +
                    (fs_i.toNat - 1)]?.getD 0#32).toNat + fj.toNat]?.getD 0#32) := by
              have h1 : (BitVec.setWidth 64 (po_prev + fi)).toNat =
                  (s0.scratch.scratch_buf[3 * fidStepsCap c.scratch_cap +
                    (fs_i.toNat - 1)]?.getD 0#32).toNat + fi.toNat := by
                rw [fid_bv64_32, ← hpp]; have := (hrow_p.2.2.2.2.1 (by omega)).2
                have := hmat.1.2.2.2.2.1; c0_bound
              have h2 : (BitVec.setWidth 64 (po_prev + fj)).toNat =
                  (s0.scratch.scratch_buf[3 * fidStepsCap c.scratch_cap +
                    (fs_i.toNat - 1)]?.getD 0#32).toNat + fj.toNat := by
                rw [fid_bv64_32, ← hpp]; have := (hrow_p.2.2.2.2.1 (by omega)).2
                have := hmat.1.2.2.2.2.1; c0_bound
              rw [← h1, ← h2, List.getElem?_eq_getElem hpop_fj, Option.getD_some]
            dsimp only [po_s, fj] at hset_eq; dsimp only [id] at hm; rw [hset_eq] at hm
            exact hJp m ⟨_, step7BvaCompactInv_set_par hmat hci (by omega) (by omega)
              (by omega) hfj_lt, hm⟩
          · c0_hfast; exact hJp mfi ⟨sbi, hci, hmfi⟩)
    · have hlen_idx : (BitVec.setWidth 64 (2 * sc + (fs_i - 1))).toNat < sbi.length := by
        rw [fid_bv64_32, hsbi_l]; c0_bound
      c0_hfast
      have hset_eq : sbi.set (BitVec.setWidth 64 (2 * sc + (fs_i - 1))).toNat mn =
          sbi.set (2 * fidStepsCap c.scratch_cap + (fs_i.toNat - 1))
            (BitVec.ofNat 32 mn.toNat) := by
        have h1 : (BitVec.setWidth 64 (2 * sc + (fs_i - 1))).toNat =
            2 * fidStepsCap c.scratch_cap + (fs_i.toNat - 1) := by rw [fid_bv64_32]; c0_bound
        have h2 : BitVec.ofNat 32 mn.toNat = mn := BitVec.eq_of_toNat_eq (by simp)
        rw [h1, h2]
      dsimp only at hm; rw [hset_eq] at hm
      exact ih3 (fs_i - 1#32, _) m (by dsimp only; rw [hfs_sub]; omega)
        ⟨by rw [hfs_sub]; omega,
         by rw [hfs_sub]; exact step7BvaCompactInv_set_len hmat hci hfs_pos hfs_le, hm⟩
  have hfs_zero : fs_i.toNat = 0 := by
    have : ¬ (0 < fs_i.toNat) := by assumption
    omega
  rw [hfs_zero] at hcomp
  let s_p3 : FullState := { s with scratch := { s.scratch with scratch_buf := sb } }
  have hinv_p3 : FullDenseInvW c F0 F_next s_p3 := cmt_fullDenseInvW_set_sb hinv hcomp.1
  have hcom_p3 : Step7BvaCommittedOk c s_p3 best_k.toNat :=
    step7BvaCompactInv_done hmat hcomp (by omega) hmn_eq hres
  have hqn_all : ∀ q ≤ best_k.toNat,
      (s_p3.scratch.scratch_buf[2 * fidStepsCap c.scratch_cap + q]?.getD 0#32).toNat =
        mn.toNat := fun q hq => by
    dsimp only [s_p3]
    rw [hcomp.2.2.2.2.1 q hq, ite_eq_left (Nat.zero_le _), Option.getD_some,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt mn.isLt]
  exact cmt_p4_epilogue_wp (brow_off := brow_off) (si := si) (dd0 := dd0) (dd1 := dd1)
    (ok1 := ok1) (dd2 := dd2) (ok2 := ok2) (m_v := m_v) (garb := garb) (irred := irred)
    (fs_i := fs_i) hFill hDelBin hUnwatch hinv_p3 hcom_p3 hcv_eq hcv64 hbk_sc hsc_eq
    hqn_all hres hfuel htm htr hm3 hQ

theorem cmt_p2_exit_wp {Γ : Env} {Q : Post [.bool]} {X : XPost}
    (hFill : ∀ a m Q X, Limits.Spec.m7FillU64Spec a m Q X →
      Γ "full_fill_u64_m7" [i64, i64, i64] [] a m Q X)
    (hDelBin : ∀ a m Q X, Watch.Spec.fullDeleteBinarySpec a m Q X →
      Γ "full_delete_binary" [i64, i32, i32] [] a m Q X)
    (hUnwatch : ∀ a m Q X, fullUnwatchLargeSpec a m Q X →
      Γ "full_unwatch_large" [i64, i32, i32] [] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur F_next : List (List Nat)} {s0 s : FullState}
    {R : Mem 64 → Prop} {best_k sc brow_off mn si m_v : Val i32}
    {dd0 dd1 ok1 dd2 ok2 : Bool} {cv64 garb irred : Val i64} {bump : Nat} {mp : Mem 64}
    (hl0 : s0.LengthsOk c) (hw0 : FullWitnessInv c F0 F_cur s0.core)
    (hinv : FullDenseInvW c F0 F_next s) (hext : CommitArenaExt s0 s)
    (hcv_eq : s.core.cur_vars = s0.core.cur_vars + 1)
    (hcv64 : cv64 = BitVec.ofNat 64 s0.core.cur_vars)
    (hbk1 : 1 ≤ best_k.toNat) (hbk_sc : best_k.toNat < fidStepsCap c.scratch_cap)
    (hsc_eq : sc = BitVec.ofNat 32 (fidStepsCap c.scratch_cap))
    (hmn_eq : mn.toNat = (s0.scratch.scratch_buf[2 * fidStepsCap c.scratch_cap +
      best_k.toNat]?.getD 0#32).toNat)
    (hmat : Step7BvaMatrixInv c F_cur s0 (best_k.toNat + 1) bump)
    (hsb_eq : s.scratch.scratch_buf = s0.scratch.scratch_buf)
    (hres : s.scratch.res_sz = BitVec.ofNat 64 best_k.toNat)
    (hfuel : s.core.fuel = s0.core.fuel)
    (htm : s.scratch.tarjan_mark = s0.scratch.tarjan_mark)
    (htr : s.scratch.tarjan_reach = s0.scratch.tarjan_reach)
    (hmp : (FullMem c s ⋆ R) mp)
    (hQ : ∀ (ok : Bool) s' m',
      FullDenseInv c F0 s' → s0.core.cur_vars ≤ s'.core.cur_vars →
      (ok = true → s0.core.cur_vars < s'.core.cur_vars) →
      (ok = true → Step7BvaCommittedOk c s' best_k.toNat) →
      s'.core.fuel = s0.core.fuel →
      s'.scratch.tarjan_mark = s0.scratch.tarjan_mark →
      s'.scratch.tarjan_reach = s0.scratch.tarjan_reach →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    wp Γ Q X (cmtP2ExitExpr c.hdr best_k sc c.pArena c.pScratchBuf c.pWsort c.pFlags
      c.pWvec brow_off mn dd0 cv64 c.pRepr c.pTmp si dd1 ok1 m_v dd2 ok2 garb irred) mp := by
  rw [cmt_p2_exit_eq_ite]
  c0_hfast_nogrp
  · exact cmt_ok_exit_wp hFill hDelBin hUnwatch hl0 hw0 hinv hext hcv_eq hcv64 hbk1 hbk_sc
      hsc_eq hmn_eq hmat hsb_eq hres hfuel htm htr hmp hQ
  · exact cmt_fail_exit_wp hFill hinv (by omega) hfuel htm htr hmp hQ

/-! ## 3. Phase 1 Binary Loop WP (`[2*fv, f_i]`) -/

theorem cmt_phase1_wp {Γ : Env} {Q : Post [.bool]} {X : XPost}
    (hAddBin : ∀ a m Q X, fullAddBinSpec a m Q X →
      Γ "full_add_bin" [i64, i32, i32] [i64] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur F_next : List (List Nat)} {s0 s : FullState}
    {R : Mem 64 → Prop} {best_k sc brow_off mn : Val i32} {dd0 : Bool} {cv64 : Val i64}
    {J_p1 : Cont [i32, .bool, .bool]} {bump : Nat} {mp : Mem 64}
    (hl0 : s0.LengthsOk c) (hinv : FullDenseInvW c F0 F_next s)
    (hcv_eq : s.core.cur_vars = s0.core.cur_vars + 1)
    (hcv64 : cv64 = BitVec.ofNat 64 s0.core.cur_vars)
    (hbk1 : 1 ≤ best_k.toNat) (hbk_sc : best_k.toNat < fidStepsCap c.scratch_cap)
    (hmat : Step7BvaMatrixInv c F_cur s0 (best_k.toNat + 1) bump)
    (hent_pos : ∀ t ≤ best_k.toNat,
      (cnfOfClauses F_next).EntailsClause
        (cnfClause [2 * s0.core.cur_vars, (s0.scratch.scratch_buf[t]?.getD 0#32).toNat]))
    (har_eq : s.core.arena = s0.core.arena) (hal_eq : s.core.arena_len = s0.core.arena_len)
    (hsb_eq : s.scratch.scratch_buf = s0.scratch.scratch_buf)
    (hres : s.scratch.res_sz = BitVec.ofNat 64 best_k.toNat)
    (hfuel : s.core.fuel = s0.core.fuel)
    (htm : s.scratch.tarjan_mark = s0.scratch.tarjan_mark)
    (htr : s.scratch.tarjan_reach = s0.scratch.tarjan_reach)
    (hmp : (FullMem c s ⋆ R) mp)
    (hExit : ∀ (si' : BitVec 32) (dd' ok' : Bool) (s' : FullState) (m' : Mem 64),
      FullDenseInvW c F0 F_next s' →
      s'.core.cur_vars = s0.core.cur_vars + 1 →
      s'.core.arena = s0.core.arena → s'.core.arena_len = s0.core.arena_len →
      s'.scratch.scratch_buf = s0.scratch.scratch_buf →
      s'.scratch.res_sz = BitVec.ofNat 64 best_k.toNat →
      s'.core.fuel = s0.core.fuel →
      s'.scratch.tarjan_mark = s0.scratch.tarjan_mark →
      s'.scratch.tarjan_reach = s0.scratch.tarjan_reach →
      (FullMem c s' ⋆ R) m' → J_p1 (si', dd', ok', ()) m') :
    wp Γ Q X (cmtP1GrpExpr c.hdr best_k sc c.pArena c.pScratchBuf c.pWsort c.pFlags
      c.pWvec brow_off mn dd0 cv64 c.pRepr c.pTmp |> cmtGrpK3 J_p1) mp := by
  have hscr := c.hscr; have hmx := c.hmaxv; unfold dimacsBound at *
  have hsc_le := fidStepsCap_le_256 c.scratch_cap
  have h4sc := fidStepsCap_mul4_le c.scratch_cap
  have hfv_lt : s0.core.cur_vars < c.max_vars := by have := hinv.1.core_ok.cur_vars_le; omega
  have hdm_nat : (best_k + 1#32).toNat = best_k.toNat + 1 := by c0_bound
  have hfresh_nat : ((cv64.setWidth 32) <<< (1 : BitVec 32)).toNat = 2 * s0.core.cur_vars := by
    rw [hcv64]
    change ((BitVec.ofNat 64 s0.core.cur_vars).setWidth 32 <<< (1 : Nat)).toNat = _
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  refine wp_while_state (α := BitVec 32 × Bool × FullState) (fun x => (x.1, x.2.1, ()))
    (fun x => best_k.toNat + 1 - x.1.toNat)
    (fun (si, dd, sc1) mc1 =>
      si.toNat ≤ best_k.toNat + 1 ∧
      FullDenseInvW c F0 F_next sc1 ∧
      sc1.core.cur_vars = s0.core.cur_vars + 1 ∧
      sc1.core.arena = s0.core.arena ∧ sc1.core.arena_len = s0.core.arena_len ∧
      sc1.scratch.scratch_buf = s0.scratch.scratch_buf ∧
      sc1.scratch.res_sz = BitVec.ofNat 64 best_k.toNat ∧
      sc1.core.fuel = s0.core.fuel ∧
      sc1.scratch.tarjan_mark = s0.scratch.tarjan_mark ∧
      sc1.scratch.tarjan_reach = s0.scratch.tarjan_reach ∧
      (FullMem c sc1 ⋆ R) mc1)
    (fun J1 hJ1 => by
      c0_hfast
      exact hJ1 (0#32, dd0, s) mp
        ⟨Nat.zero_le _, hinv, hcv_eq, har_eq, hal_eq, hsb_eq, hres, hfuel, htm, htr, hmp⟩)
    (fun J1 (si, dd, sc1) mc1
        ⟨hsi_le, hinv1, hcv1, har1, hal1, hsb1, hrs1, hfl1, htm1, htr1, hmc1⟩ ih1 => ?_)
  clear hmp
  c0_hfast_nogrp
  rotate_left 1
  · c0_hfast
    exact hExit si dd true sc1 mc1 hinv1 hcv1 har1 hal1 hsb1 hrs1 hfl1 htm1 htr1 hmc1
  have hsi_lt : si.toNat < best_k.toNat + 1 := by
    have : si.toNat < (best_k + 1#32).toNat := by assumption
    rwa [hdm_nat] at this
  have ht_eq : (best_k + 1 - 1 - si).toNat = best_k.toNat - si.toNat := by c0_bound
  have ht_sb : (BitVec.setWidth 64 (best_k + 1 - 1 - si)).toNat <
      sc1.scratch.scratch_buf.length := by
    rw [fid_bv64_32, ht_eq, hinv1.1.scratch_ok.scratch_buf_len]; omega
  c0_hfast_nogrp
  let fs := sc1.scratch.scratch_buf[(BitVec.setWidth 64 (best_k + 1 - 1 - si)).toNat]'ht_sb
  have hfs_eq : fs.toNat = (s0.scratch.scratch_buf[best_k.toNat - si.toNat]?.getD 0#32).toNat := by
    dsimp only [fs]; apply congrArg BitVec.toNat; apply Option.some.inj
    rw [← List.getElem?_eq_getElem ht_sb, fid_bv64_32, ht_eq, hsb1,
      List.getElem?_eq_getElem (by rw [hl0.scratch_ok.scratch_buf_len]; omega), Option.getD_some]
  have hfs_lt : fs.toNat < 2 * s0.core.cur_vars := by
    rw [hfs_eq]; exact (hmat.1.2.2.2.2.2 (best_k.toNat - si.toNat) (by omega)).1
  have hfr_wv : ((BitVec.setWidth 64 ((cv64.setWidth 32) <<< (1 : BitVec 32)) <<< (1 : Nat)) +
      1#64).toNat < sc1.core.wvec.length := by
    rw [hinv1.1.core_ok.wvec_len, BitVec.toNat_add, BitVec.toNat_shiftLeft, fid_bv64_32,
      hfresh_nat, show (1#64 : BitVec 64).toNat = 1 from rfl, Nat.shiftLeft_eq]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
  have hfs_wv : ((BitVec.setWidth 64 fs <<< (1 : Nat)) + 1#64).toNat < sc1.core.wvec.length := by
    rw [hinv1.1.core_ok.wvec_len, BitVec.toNat_add, BitVec.toNat_shiftLeft, fid_bv64_32,
      show (1#64 : BitVec 64).toNat = 1 from rfl, Nat.shiftLeft_eq]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
  -- Pure read-only `if (!defrag_dirty)` check
  refine wp_join_state1 (t := .bool) (α := Bool) id (fun _ m' => m' = mc1)
    (fun _ dd_a m' hm' => ?_)
    (fun Jdd hJdd => by
      c0_hfast_nogrp
      · c0_hfast; exact hJdd dd mc1 rfl
      · c0_hfast_nogrp
        refine wp_join_state1 (t := i64) (α := BitVec 64) id (fun _ m' => m' = mc1)
          (fun _ na m' hm' => by
            rw [hm']
            refine wp_join_state1 (t := i64) (α := BitVec 64) id (fun _ m' => m' = mc1)
              (fun _ nb m' hm' => by
                rw [hm']
                refine wp_join_state1 (t := .bool) (α := Bool) id (fun _ m' => m' = mc1)
                  (fun _ ddi m' hm' => by rw [hm']; c0_hfast; exact hJdd ddi mc1 rfl)
                  (fun Jdi hJdi => by
                    c0_hfast_nogrp
                    · c0_hfast; exact hJdi true mc1 rfl
                    · c0_hfast; exact hJdi true mc1 rfl
                    · c0_hfast; exact hJdi true mc1 rfl
                    · c0_hfast; exact hJdi true mc1 rfl
                    · refine wp_join0 (fun m' => m' = mc1)
                        (fun _ m' hm' => by
                          rw [hm']; c0_hfast_nogrp <;> (c0_hfast; exact hJdi _ mc1 rfl))
                        (fun Jef hJef => by
                          c0_hfast_nogrp
                          · c0_hfast; exact hJef mc1 rfl
                          · c0_hfast; exact hJef mc1 rfl
                          · c0_hfast; exact hJdi dd mc1 rfl)))
              (fun Jnb hJnb => by
                c0_hfast_nogrp <;> (c0_hfast; exact hJnb _ mc1 rfl)))
          (fun Jna hJna => by
            c0_hfast_nogrp <;> (c0_hfast; exact hJna _ mc1 rfl)))
  rw [hm']
  c0_hfast_nogrp
  fid_call hAddBin
  refine ⟨c, F0, F_next, sc1, R, rfl, hinv1.1, hinv1.2.1, hinv1.2.2.2.2.2.1,
    fun _ _ => by
      change (cnfOfClauses F_next).EntailsClause
        (cnfClause [((cv64.setWidth 32) <<< (1 : BitVec 32)).toNat, fs.toNat])
      rw [hfresh_nat, hfs_eq]
      exact hent_pos (best_k.toNat - si.toNat) (by omega),
    hmc1, fun br vals' fl' lvl' rsns' trl' tp' te' unass' unfl' wv' ws' wl' wu' nb' oom' inc'
      ph' wso' m2 hlen2 hw2 _ _ _ hm2 => ?_⟩
  let sc2 : FullState :=
    { sc1 with
      core :=
        { sc1.core with
          vals := vals', flags := fl', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
          trail_end := te', unassigned := unass', unflushed := unfl', wvec := wv', wstk := ws',
          wlen := wl', wusable := wu', num_binary := nb', oom := oom', inconsistent := inc' }
      scratch := { sc1.scratch with phases := ph', wsort := wso' } }
  have hinv2 : FullDenseInvW c F0 F_next sc2 := cmt_fullDenseInvW_addBin hinv1 hlen2 hw2
  refine wp_join_state1 (t := .bool) (α := Bool) id (fun _ m' => m' = m2)
    (fun _ dd_b m' hm' => ?_)
    (fun Jddb hJddb => by
      c0_hfast_nogrp <;> (c0_hfast; exact hJddb _ m2 rfl))
  rw [hm']
  c0_hfast_nogrp
  · c0_hfast
    exact hExit si dd_b false sc2 m2 hinv2 hcv1 har1 hal1 hsb1 hrs1 hfl1 htm1 htr1 hm2
  · c0_hfast
    exact hExit si dd_b false sc2 m2 hinv2 hcv1 har1 hal1 hsb1 hrs1 hfl1 htm1 htr1 hm2
  · c0_hfast
    exact hExit si dd_b false sc2 m2 hinv2 hcv1 har1 hal1 hsb1 hrs1 hfl1 htm1 htr1 hm2
  refine wp_join_state1 (t := i32) (α := BitVec 32) (fun x => x) (fun _ m' => m' = m2)
    (fun _ fbit m' hm' => ?_)
    (fun Jfb hJfb => by
      c0_hfast_nogrp <;> (c0_hfast; exact hJfb _ m2 rfl))
  rw [hm']
  have hfs_v : (BitVec.setWidth 64 (fs >>> (1 : Nat))).toNat < sc2.core.flags.length := by
    rw [fid_bv64_32, bv32_lshr_1, hinv2.1.core_ok.flags_len]; omega
  have hfr_v : (BitVec.setWidth 64 (((cv64.setWidth 32) <<< (1 : BitVec 32)) >>> (1 : Nat))).toNat <
      (sc2.core.flags.set (BitVec.setWidth 64 (fs >>> (1 : Nat))).toNat
        (sc2.core.flags[(BitVec.setWidth 64 (fs >>> (1 : Nat))).toNat]'hfs_v ||| 8 ||| 16 |||
          fbit)).length := by
    rw [List.length_set, fid_bv64_32, bv32_lshr_1, hfresh_nat, hinv2.1.core_ok.flags_len]; omega
  have hsi1 : (si + 1#32).toNat = si.toNat + 1 := by c0_bound
  c0_hfast
  refine ih1 (si + 1#32, dd_b, _) m (by dsimp only; rw [hsi1]; omega)
    ⟨by rw [hsi1]; omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hm⟩
  · exact cmt_fullDenseInvW_set_flags hinv2
      (by simp only [List.length_set]; exact hinv2.1.core_ok.flags_len)
  · exact hcv1
  · exact har1
  · exact hal1
  · exact hsb1
  · exact hrs1
  · exact hfl1
  · exact htm1
  · exact htr1

end

end LeanQbe.T.Examples.Kissat.Proof.Factor
