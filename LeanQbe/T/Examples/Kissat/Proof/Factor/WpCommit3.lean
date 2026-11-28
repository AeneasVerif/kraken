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
public import LeanQbe.T.Examples.Kissat.Proof.Factor.WpCommit1
public import LeanQbe.T.Examples.Kissat.Proof.Factor.WpCommit2
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
# Top-Level `full_bva_commit_wp` (`Proof.Factor.WpCommit3`)

Zero-legacy (`0` `Full*` imports, `0` placeholders, `XPost`-polymorphic) top-level certification
of `full_bva_commit` (`13/15` in `Src.Factor`), composing `cmt_phase1_wp`, `cmt_phase2_wp`, and
`cmt_p2_exit_wp`.
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

@[local bv_c0] private theorem cmt3_bv64_one : (1 : BitVec 64).toNat = 1 := rfl
@[local bv_c0] private theorem cmt3_bv64_two : (2 : BitVec 64).toNat = 2 := rfl
@[local bv_c0] private theorem cmt3_bv64_three : (3 : BitVec 64).toNat = 3 := rfl
@[local bv_c0] private theorem cmt3_bv32_one : (1 : BitVec 32).toNat = 1 := rfl

private theorem cmt3_getElem_eq {α : Type} {xs : List α} {i j : Nat}
    {hi : i < xs.length} {hj : j < xs.length} (h : i = j) : xs[i]'hi = xs[j]'hj := by
  subst h; rfl

private theorem cmt_rowEntry_of_eq {F_cur : List (List Nat)} {s0 s1 : FullState}
    (hcv : s1.core.cur_vars = s0.core.cur_vars)
    (har : s1.core.arena = s0.core.arena) (hal : s1.core.arena_len = s0.core.arena_len)
    {fr : Nat} {w : BitVec 32} {res : List Nat} (hr : FidBvaRowEntryOk F_cur s0 fr w res) :
    FidBvaRowEntryOk F_cur s1 fr w res := by
  unfold FidBvaRowEntryOk at hr ⊢
  split at hr
  · rename_i hb; rw [ite_eq_left hb]; rwa [hcv]
  · rename_i hnb; rw [ite_eq_right hnb]
    simp only [fullArenaClauseRefs, fullArenaClauseRefsCore, fullArenaClauseGarb,
      fullArenaClauseGarbCore, fullArenaHdrCore, fullArenaClauseSize, fullArenaClauseSizeCore,
      fullArenaClauseLits, fullArenaClauseLitsCore, har, hal] at hr ⊢
    exact hr

private theorem cmt_matrix_of_eq {c : FullCfg} {F_cur : List (List Nat)} {s0 s1 : FullState}
    {step bump : Nat} (h : Step7BvaMatrixInv c F_cur s0 step bump)
    (hcv : s1.core.cur_vars = s0.core.cur_vars)
    (har : s1.core.arena = s0.core.arena) (hal : s1.core.arena_len = s0.core.arena_len)
    (hsb : s1.scratch.scratch_buf = s0.scratch.scratch_buf) :
    Step7BvaMatrixInv c F_cur s1 step bump := by
  refine ⟨⟨h.1.1, h.1.2.1, h.1.2.2.1, h.1.2.2.2.1, h.1.2.2.2.2.1, fun r hr => ?_⟩,
    h.2.congr hsb⟩
  have h1 := h.1.2.2.2.2.2 r hr
  rw [hcv, hsb]
  refine ⟨h1.1, h1.2.1, h1.2.2.1, h1.2.2.2.1, h1.2.2.2.2.1, fun m hm => ?_⟩
  obtain ⟨res, hlt, hnd, hok, hent, hpar⟩ := h1.2.2.2.2.2 m hm
  exact ⟨res, hlt, hnd, cmt_rowEntry_of_eq hcv har hal hok, hent, fun hr0 =>
    let hp := hpar hr0; ⟨hp.1, cmt_rowEntry_of_eq hcv har hal hp.2⟩⟩

private theorem cmt_phases_wp {Γ : Env} {Q : Post [.bool]} {X : XPost}
    (hFill : Γ.Has "full_fill_u64_m7" Limits.Spec.m7FillU64Spec)
    (hAddBin : Γ.Has "full_add_bin" fullAddBinSpec)
    (hAllocCl : Γ.Has "full_alloc_cl" fullAllocClSpec)
    (hWatchPush : Γ.Has "full_watch_push" fullWatchPushSpec)
    (hUnwatch : Γ.Has "full_unwatch_large" fullUnwatchLargeSpec)
    (hDelBin : Γ.Has "full_delete_binary" Watch.Spec.fullDeleteBinarySpec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur F_next : List (List Nat)} {s0 s_z : FullState}
    {R : Mem 64 → Prop} {best_k sc brow_off mn : Val i32} {dd0 : Bool} {cv64 : Val i64}
    {bump : Nat} {mz : Mem 64}
    (hl0 : s0.LengthsOk c) (hw0 : FullWitnessInv c F0 F_cur s0.core)
    (hinv_z : FullDenseInvW c F0 F_next s_z)
    (hcv_z : s_z.core.cur_vars = s0.core.cur_vars + 1)
    (hcv64 : cv64 = BitVec.ofNat 64 s0.core.cur_vars)
    (hbk1 : 1 ≤ best_k.toNat) (hbk_sc : best_k.toNat < fidStepsCap c.scratch_cap)
    (hsc : sc = BitVec.ofNat 32 (fidStepsCap c.scratch_cap))
    (hbro_eq : brow_off.toNat =
      (s0.scratch.scratch_buf[fidStepsCap c.scratch_cap + best_k.toNat]?.getD 0#32).toNat)
    (hmn_eq : mn.toNat =
      (s0.scratch.scratch_buf[2 * fidStepsCap c.scratch_cap + best_k.toNat]?.getD 0#32).toNat)
    (hmat : Step7BvaMatrixInv c F_cur s0 (best_k.toNat + 1) bump)
    (hent_pos : ∀ t ≤ best_k.toNat,
      (cnfOfClauses F_next).EntailsClause
        (cnfClause [2 * s0.core.cur_vars, (s0.scratch.scratch_buf[t]?.getD 0#32).toNat]))
    (hrow_res0 : ∀ m < mn.toNat, ∃ res : List Nat,
      (∀ x ∈ res, x < 2 * s0.core.cur_vars) ∧ (res.map (· / 2)).Nodup ∧
      FidBvaRowEntryOk F_cur s0 (s0.scratch.scratch_buf[best_k.toNat]?.getD 0#32).toNat
        (s0.scratch.scratch_buf[brow_off.toNat + m]?.getD 0#32) res ∧
      (cnfOfClauses F_next).EntailsClause (cnfClause ((2 * s0.core.cur_vars + 1) :: res)))
    (har_z : s_z.core.arena = s0.core.arena) (hal_z : s_z.core.arena_len = s0.core.arena_len)
    (hsb_z : s_z.scratch.scratch_buf = s0.scratch.scratch_buf)
    (hrs_z : s_z.scratch.res_sz = BitVec.ofNat 64 best_k.toNat)
    (hfl_z : s_z.core.fuel = s0.core.fuel)
    (htm_z : s_z.scratch.tarjan_mark = s0.scratch.tarjan_mark)
    (htr_z : s_z.scratch.tarjan_reach = s0.scratch.tarjan_reach)
    (hm_z : (FullMem c s_z ⋆ R) mz)
    (hQ : ∀ (ok : Bool) s' m',
      FullDenseInv c F0 s' → s0.core.cur_vars ≤ s'.core.cur_vars →
      (ok = true → s0.core.cur_vars < s'.core.cur_vars) →
      (ok = true → Step7BvaCommittedOk c s' best_k.toNat) →
      s'.core.fuel = s0.core.fuel →
      s'.scratch.tarjan_mark = s0.scratch.tarjan_mark →
      s'.scratch.tarjan_reach = s0.scratch.tarjan_reach →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    wp Γ Q X (cmtP1GrpExpr c.hdr best_k sc c.pArena c.pScratchBuf c.pWsort c.pFlags
      c.pWvec brow_off mn dd0 cv64 c.pRepr c.pTmp) mz := by
  refine wp_join_state (α := BitVec 32 × Bool × Bool × FullState)
    (fun x => (x.1, x.2.1, x.2.2.1, ()))
    (fun (_, _, _, s1) m1 =>
      FullDenseInvW c F0 F_next s1 ∧
      s1.core.cur_vars = s0.core.cur_vars + 1 ∧
      s1.core.arena = s0.core.arena ∧ s1.core.arena_len = s0.core.arena_len ∧
      s1.scratch.scratch_buf = s0.scratch.scratch_buf ∧
      s1.scratch.res_sz = BitVec.ofNat 64 best_k.toNat ∧
      s1.core.fuel = s0.core.fuel ∧
      s1.scratch.tarjan_mark = s0.scratch.tarjan_mark ∧
      s1.scratch.tarjan_reach = s0.scratch.tarjan_reach ∧
      (FullMem c s1 ⋆ R) m1)
    (fun _ (si1, dd1, ok1, s1) m1
        ⟨hinv1, hcv1, har1, hal1, hsb1, hrs1, hfl1, htm1, htr1, hm1⟩ => by
      refine wp_join_state (α := BitVec 32 × Bool × Bool × BitVec 64 × BitVec 64 × FullState)
        (fun x => (x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, ()))
        (fun (_, _, _, _, _, s2) m2 =>
          FullDenseInvW c F0 F_next s2 ∧ CommitArenaExt s0 s2 ∧
          s2.core.cur_vars = s0.core.cur_vars + 1 ∧
          s2.scratch.scratch_buf = s0.scratch.scratch_buf ∧
          s2.scratch.res_sz = BitVec.ofNat 64 best_k.toNat ∧
          s2.core.fuel = s0.core.fuel ∧
          s2.scratch.tarjan_mark = s0.scratch.tarjan_mark ∧
          s2.scratch.tarjan_reach = s0.scratch.tarjan_reach ∧
          (FullMem c s2 ⋆ R) m2)
        (fun _ (mv, dd2, ok2, ga, ir, s2) m2
            ⟨hinv2, hext2, hcv2, hsb2, hrs2, hfl2, htm2, htr2, hm2⟩ =>
          cmt_p2_exit_wp (best_k := best_k) (sc := sc) (brow_off := brow_off) (mn := mn)
            (dd0 := dd0) (cv64 := cv64) (si := si1) (dd1 := dd1) (ok1 := ok1)
            (m_v := mv) (dd2 := dd2) (ok2 := ok2) (garb := ga) (irred := ir)
            hFill hDelBin hUnwatch hl0 hw0 hinv2 hext2 hcv2
            hcv64 hbk1 hbk_sc hsc hmn_eq hmat hsb2 hrs2 hfl2 htm2 htr2 hm2 hQ)
        (fun J_p2 hJ_p2 =>
          cmt_phase2_wp (best_k := best_k) (sc := sc) (brow_off := brow_off) (mn := mn)
            (dd0 := dd0) (cv64 := cv64) (si := si1) (dd1 := dd1) (ok1 := ok1) (J_p2 := J_p2)
            hAddBin hAllocCl hWatchPush hUnwatch hl0 hw0 hinv1 hcv1
            hcv64 hbk1 hbk_sc hbro_eq hmn_eq hmat hrow_res0 har1 hal1 hsb1 hrs1 hfl1
            htm1 htr1 hm1 fun mv dd2 ok2 ga ir s2 m2 h1 h2 h3 h4 h5 h6 h7 h8 h9 =>
              hJ_p2 (mv, dd2, ok2, ga, ir, s2) m2 ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩))
    (fun J_p1 hJ_p1 =>
      cmt_phase1_wp (best_k := best_k) (sc := sc) (brow_off := brow_off) (mn := mn)
        (dd0 := dd0) (cv64 := cv64) (J_p1 := J_p1)
        hAddBin hl0 hinv_z hcv_z hcv64 hbk1 hbk_sc hmat hent_pos
        har_z hal_z hsb_z hrs_z hfl_z htm_z htr_z hm_z
        fun si1 dd1 ok1 s1 m1 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 =>
          hJ_p1 (si1, dd1, ok1, s1) m1 ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩)

private theorem cmt_call_steps_cap {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    (hStepsCap : Γ.Has "full_bva_steps_cap_fid" fidBvaStepsCapSpec)
    {cap : Nat} (hcap : cap < 2 ^ 64) {k : Tup Val [i32] → Expr Val Cont rs}
    (hk : wp Γ Q X (k (BitVec.ofNat 32 (fidStepsCap cap), ())) m) :
    wp Γ Q X (.call (as := [i64]) (bs := [i32]) "full_bva_steps_cap_fid"
      (Arg.var (BitVec.ofNat 64 cap), ()) k) m := by
  refine wp_call_of_spec _ _ (hStepsCap _ _ _ _ ?_)
  dsimp only [fidBvaStepsCapSpec, vals, Arg.val]
  rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcap]

theorem full_bva_commit_wp (Γ : Env)
    (hStepsCap : Γ.Has "full_bva_steps_cap_fid" fidBvaStepsCapSpec)
    (hDefrag : Γ.Has "full_wstack_defrag" fullWstackDefragSpec)
    (hFill : Γ.Has "full_fill_u64_m7" Limits.Spec.m7FillU64Spec)
    (hInitFresh : Γ.Has "full_init_fresh_var" Internal.Spec.fullInitFreshVarSpec)
    (hAddBin : Γ.Has "full_add_bin" fullAddBinSpec)
    (hAllocCl : Γ.Has "full_alloc_cl" fullAllocClSpec)
    (hWatchPush : Γ.Has "full_watch_push" fullWatchPushSpec)
    (hUnwatch : Γ.Has "full_unwatch_large" fullUnwatchLargeSpec)
    (hDelBin : Γ.Has "full_delete_binary" Watch.Spec.fullDeleteBinarySpec) :
    ∀ a m Q X, step7BvaCommitSpec a m Q X → Func.wp Γ full_bva_commit_body a m Q X := by
  rintro ⟨h, best_k, ⟨⟩⟩ m0 Q X
    ⟨c, F0, F_cur, s0, R, bump, rfl, hinv0, hbk1, hbk_sc, hmat, hres0, hm0, hQ⟩
  unfold Func.wp full_bva_commit_body
  have hscr := c.hscr; have har_b := c.harena; have hmx := c.hmaxv; unfold dimacsBound at *
  have hsc_le := fidStepsCap_le_256 c.scratch_cap
  have h4sc := fidStepsCap_mul4_le c.scratch_cap
  have hsc_pos : 0 < fidStepsCap c.scratch_cap := hmat.1.1
  have hfail : ∀ s' m', FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s0.core.cur_vars →
      s'.core.fuel = s0.core.fuel → s'.scratch.tarjan_mark = s0.scratch.tarjan_mark →
      s'.scratch.tarjan_reach = s0.scratch.tarjan_reach → (FullMem c s' ⋆ R) m' →
      Q (false, ()) m' := fun s' m' hi hcv hfl htm htr hm' =>
    hQ false s' m' hi.toDense (by omega) (fun h => by cases h) (fun h => by cases h)
      hfl htm htr hm'
  c0_hfast_nogrp
  · c0_hfast; exact hfail s0 m0 hinv0 rfl rfl rfl rfl hm0
  refine cmt_call_steps_cap hStepsCap (by omega) ?_
  let sc := BitVec.ofNat 32 (fidStepsCap c.scratch_cap)
  have hsc_nat : sc.toNat = fidStepsCap c.scratch_cap := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  c0_hfast_nogrp
  · c0_hfast; exact hfail s0 m0 hinv0 rfl rfl rfl rfl hm0
  · c0_hfast; exact hfail s0 m0 hinv0 rfl rfl rfl rfl hm0
  have hsb0_l := hinv0.1.scratch_ok.scratch_buf_len
  have hbro_i : (BitVec.setWidth 64 (sc + best_k)).toNat < s0.scratch.scratch_buf.length := by
    rw [fid_bv64_32, hsb0_l]; c0_bound
  have hmn_i : (BitVec.setWidth 64 (2 * sc + best_k)).toNat < s0.scratch.scratch_buf.length := by
    rw [fid_bv64_32, hsb0_l]; c0_bound
  c0_hfast_nogrp
  let brow_off := s0.scratch.scratch_buf[(BitVec.setWidth 64 (sc + best_k)).toNat]'hbro_i
  let mn := s0.scratch.scratch_buf[(BitVec.setWidth 64 (2 * sc + best_k)).toNat]'hmn_i
  have hbro_eq : brow_off.toNat =
      (s0.scratch.scratch_buf[fidStepsCap c.scratch_cap + best_k.toNat]?.getD 0#32).toNat := by
    have hi : (BitVec.setWidth 64 (sc + best_k)).toNat =
        fidStepsCap c.scratch_cap + best_k.toNat := by rw [fid_bv64_32]; c0_bound
    dsimp only [brow_off]; rw [← hi, List.getElem?_eq_getElem hbro_i, Option.getD_some]
  have hmn_eq : mn.toNat =
      (s0.scratch.scratch_buf[2 * fidStepsCap c.scratch_cap + best_k.toNat]?.getD 0#32).toNat := by
    have hi : (BitVec.setWidth 64 (2 * sc + best_k)).toNat =
        2 * fidStepsCap c.scratch_cap + best_k.toNat := by rw [fid_bv64_32]; c0_bound
    dsimp only [mn]; rw [← hi, List.getElem?_eq_getElem hmn_i, Option.getD_some]
  have hdm_nat : (best_k + 1#32).toNat = best_k.toNat + 1 := by c0_bound
  have hbk_row := hmat.1.2.2.2.2.2 best_k.toNat (by omega)
  -- Cost Loop A: pure read-only over `si < dm`
  refine wp_while_state (α := BitVec 64 × BitVec 32) (fun x => (x.1, x.2, ()))
    (fun x => best_k.toNat + 1 - x.2.toNat)
    (fun (_, si) m' => si.toNat ≤ best_k.toNat + 1 ∧ m' = m0)
    (fun Ja hJa => by c0_hfast; exact hJa (_, 0#32) m0 ⟨Nat.zero_le _, rfl⟩)
    (fun Ja (nw, si) m' ⟨hsi_le, hm'⟩ iha => ?_)
  rw [hm']; c0_hfast_nogrp
  · have hsi_lt : si.toNat < best_k.toNat + 1 := by
      have : si.toNat < (best_k + 1#32).toNat := by assumption
      rwa [hdm_nat] at this
    have hsi_sb : (BitVec.setWidth 64 si).toNat < s0.scratch.scratch_buf.length := by
      rw [fid_bv64_32, hsb0_l]; omega
    have hfs_lt : (s0.scratch.scratch_buf[(BitVec.setWidth 64 si).toNat]'hsi_sb).toNat <
        2 * s0.core.cur_vars := by
      have h1 := (hmat.1.2.2.2.2.2 si.toNat hsi_lt).1
      rw [List.getElem?_eq_getElem (by rw [hsb0_l]; omega), Option.getD_some] at h1
      rwa [show s0.scratch.scratch_buf[(BitVec.setWidth 64 si).toNat]'hsi_sb =
        s0.scratch.scratch_buf[si.toNat]'(by rw [hsb0_l]; omega) from
        cmt3_getElem_eq (fid_bv64_32 si)]
    have hfs_wv : ((BitVec.setWidth 64
        (s0.scratch.scratch_buf[(BitVec.setWidth 64 si).toNat]'hsi_sb) <<< (1 : Nat)) +
        1#64).toNat < s0.core.wvec.length := by
      rw [hinv0.1.core_ok.wvec_len, BitVec.toNat_add, BitVec.toNat_shiftLeft, fid_bv64_32,
        show (1#64 : BitVec 64).toNat = 1 from rfl, Nat.shiftLeft_eq]
      have := hinv0.1.core_ok.cur_vars_le
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
    have hsi1 : (si + 1#32).toNat = si.toNat + 1 := by c0_bound
    c0_hfast
    exact iha (_, si + 1#32) m0 (by dsimp only; rw [hsi1]; omega) ⟨by rw [hsi1]; omega, rfl⟩
  -- Cost Loop B: pure read-only over `m < mn`
  refine wp_while_state (α := BitVec 64 × BitVec 64 × BitVec 32) (fun x => (x.1, x.2.1, x.2.2, ()))
    (fun x => mn.toNat - x.2.2.toNat)
    (fun (_, _, mi) m' => mi.toNat ≤ mn.toNat ∧ m' = m0)
    (fun Jb hJb => by c0_hfast; exact hJb (16#64, nw, 0#32) m0 ⟨Nat.zero_le _, rfl⟩)
    (fun Jb (nar, nw_b, mi) m' ⟨hmi_le, hm'⟩ ihb => ?_)
  rw [hm']; c0_hfast_nogrp
  · have hmi_lt : mi.toNat < mn.toNat := by
      have hi : (BitVec.setWidth 64 (2 * sc + best_k)).toNat =
          ((2 : BitVec 32).toNat * (fidStepsCap c.scratch_cap % 2 ^ 32) + best_k.toNat) %
            2 ^ 32 := by
        rw [fid_bv64_32]; c0_bound
      have hmn_hc : mn = s0.scratch.scratch_buf[((2 : BitVec 32).toNat *
          (fidStepsCap c.scratch_cap % 2 ^ 32) + best_k.toNat) % 2 ^ 32]'(by
            rw [← hi]; exact hmn_i) := by
        dsimp only [mn]; exact cmt3_getElem_eq hi
      rw [hmn_hc]; exact hc
    have hbro_mi : (BitVec.setWidth 64 (brow_off + mi)).toNat < s0.scratch.scratch_buf.length := by
      rw [fid_bv64_32, hsb0_l]; have := hbk_row.2.2.2.1; have := hmat.1.2.2.2.2.1; c0_bound
    have hmi1 : (mi + 1#32).toNat = mi.toNat + 1 := by
      have := hbk_row.2.2.2.1; have := hmat.1.2.2.2.2.1; c0_bound
    c0_hfast_nogrp
    let c_top := s0.scratch.scratch_buf[(BitVec.setWidth 64 (brow_off + mi)).toNat]'hbro_mi
    have hct_eq : c_top = s0.scratch.scratch_buf[brow_off.toNat + mi.toNat]?.getD 0#32 := by
      have hi : (BitVec.setWidth 64 (brow_off + mi)).toNat = brow_off.toNat + mi.toNat := by
        rw [fid_bv64_32]; have := hbk_row.2.2.2.1; have := hmat.1.2.2.2.2.1; c0_bound
      dsimp only [c_top]; rw [← hi, List.getElem?_eq_getElem hbro_mi, Option.getD_some]
    obtain ⟨res, _, _, hres_ok, _, _⟩ := hbk_row.2.2.2.2.2 mi.toNat (by rwa [← hmn_eq])
    rw [← hbro_eq, ← hct_eq] at hres_ok
    have hbi1 : (BitVec.setWidth 64 (sc + best_k)).toNat =
        (fidStepsCap c.scratch_cap + best_k.toNat) % 2 ^ 32 := by
      rw [fid_bv64_32, BitVec.toNat_add, hsc_nat]
    have hbi2 : (BitVec.setWidth 64 (brow_off + mi)).toNat =
        ((s0.scratch.scratch_buf[(fidStepsCap c.scratch_cap + best_k.toNat) % 2 ^ 32]'(by
          rw [← hbi1]; exact hbro_i)).toNat + mi.toNat) % 2 ^ 32 := by
      rw [fid_bv64_32, BitVec.toNat_add, show brow_off =
        s0.scratch.scratch_buf[(fidStepsCap c.scratch_cap + best_k.toNat) % 2 ^ 32]'(by
          rw [← hbi1]; exact hbro_i) from cmt3_getElem_eq hbi1]
    have hct_hc : c_top = s0.scratch.scratch_buf[((s0.scratch.scratch_buf[(fidStepsCap c.scratch_cap
        + best_k.toNat) % 2 ^ 32]'(by rw [← hbi1]; exact hbro_i)).toNat + mi.toNat) % 2 ^ 32]'(by
          rw [← hbi2]; exact hbro_mi) := by dsimp only [c_top]; exact cmt3_getElem_eq hbi2
    refine wp_join_state (α := BitVec 64 × BitVec 64) (fun x => (x.1, x.2, ()))
      (fun _ m'' => m'' = m0)
      (fun _ (nar', nw') m'' hm'' => by
        rw [hm'']; c0_hfast
        exact ihb (nar', nw', mi + 1#32) m0 (by dsimp only; rw [hmi1]; omega)
          ⟨by rw [hmi1]; omega, rfl⟩)
      (fun Jbb hJbb => by
        c0_hfast_nogrp
        · have hbin : (c_top &&& 0x80000000#32) ≠ 0#32 := by rw [hct_hc]; exact hc
          unfold FidBvaRowEntryOk at hres_ok; rw [ite_eq_left hbin] at hres_ok
          have hq_wv : ((BitVec.setWidth 64 (c_top &&& 0x7FFFFFFF#32) <<< (1 : Nat)) +
              1#64).toNat < s0.core.wvec.length := by
            rw [hinv0.1.core_ok.wvec_len, BitVec.toNat_add, BitVec.toNat_shiftLeft, fid_bv64_32,
              show (1#64 : BitVec 64).toNat = 1 from rfl, Nat.shiftLeft_eq]
            have := hinv0.1.core_ok.cur_vars_le; have := hres_ok.1
            rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
          c0_hfast; exact hJbb (nar, _) m0 rfl
        · have hnb : (c_top &&& 0x80000000#32) = 0#32 := by rw [hct_hc]; exact hc
          unfold FidBvaRowEntryOk at hres_ok; rw [ite_eq_right (fun h => h hnb)] at hres_ok
          obtain ⟨hct_ref, hct_ng, _, _, _, _, _⟩ := hres_ok
          have hct_wf := hinv0.2.1.arena.refs_wf c_top.toNat hct_ref
          have hct2 : (BitVec.setWidth 64 c_top + 2#64).toNat < s0.core.arena.length := by
            rw [hinv0.1.core_ok.arena_len_arr]; have := hinv0.1.core_ok.arena_len_le; c0_bound
          have hbk_sb : (BitVec.setWidth 64 best_k).toNat < s0.scratch.scratch_buf.length := by
            rw [fid_bv64_32, hsb0_l]; omega
          c0_hfast_nogrp
          let csz := s0.core.arena[(BitVec.setWidth 64 c_top + 2#64).toNat]'hct2
          have hcsz_eq : csz.toNat = fullArenaClauseSize s0 c_top.toNat := by
            unfold fullArenaClauseSize fullArenaClauseSizeCore
            have h2 : (BitVec.setWidth 64 c_top + 2#64).toNat = c_top.toNat + 2 := by
              have := hinv0.1.core_ok.arena_len_le; c0_bound
            dsimp only [csz]; apply congrArg BitVec.toNat; apply Option.some.inj
            rw [← List.getElem?_eq_getElem hct2, h2,
              List.getElem?_eq_getElem (by rw [hinv0.1.core_ok.arena_len_arr]
                                           have := hinv0.1.core_ok.arena_len_le; omega),
              Option.getD_some]
          have hcsz_hi : (BitVec.setWidth 64 c_top + 2#64).toNat =
              ((s0.scratch.scratch_buf[((s0.scratch.scratch_buf[(fidStepsCap c.scratch_cap +
                best_k.toNat) % 2 ^ 32]'(by rw [← hbi1]; exact hbro_i)).toNat + mi.toNat) %
                2 ^ 32]'(by rw [← hbi2]; exact hbro_mi)).toNat + 2) % 2 ^ 64 := by
            rw [BitVec.toNat_add, fid_bv64_32, hct_hc]; c0_bound
          have hcsz_hc : csz = s0.core.arena[((s0.scratch.scratch_buf[((s0.scratch.scratch_buf[(
              fidStepsCap c.scratch_cap + best_k.toNat) % 2 ^ 32]'(by
                rw [← hbi1]; exact hbro_i)).toNat + mi.toNat) % 2 ^ 32]'(by
                rw [← hbi2]; exact hbro_mi)).toNat + 2) % 2 ^ 64]'(by
                rw [← hcsz_hi]; exact hct2) := by
            dsimp only [csz]; exact cmt3_getElem_eq hcsz_hi
          refine wp_while_state (α := BitVec 64 × BitVec 32) (fun x => (x.1, x.2, ()))
            (fun x => csz.toNat - x.2.toNat)
            (fun (_, j) m'' => j.toNat ≤ csz.toNat ∧ m'' = m0)
            (fun Jj hJj => by c0_hfast; exact hJj (nw_b, 0#32) m0 ⟨Nat.zero_le _, rfl⟩)
            (fun Jj (nw_j, j) m'' ⟨hj_le, hm''⟩ ihj => by
              rw [hm'']; c0_hfast_nogrp
              · have hj_lt : j.toNat < csz.toNat := by rw [hcsz_hc]; exact hc
                have hj_ar : (BitVec.setWidth 64 c_top + 3#64 + BitVec.setWidth 64 j).toNat <
                    s0.core.arena.length := by
                  rw [hinv0.1.core_ok.arena_len_arr]
                  have := hct_wf.1; have := hcsz_eq; unfold fullArenaClauseSize at *
                  have := hinv0.1.core_ok.arena_len_le; c0_bound
                have hl_lt : (s0.core.arena[(BitVec.setWidth 64 c_top + 3#64 +
                    BitVec.setWidth 64 j).toNat]'hj_ar).toNat < 2 * s0.core.cur_vars := by
                  have hi : (BitVec.setWidth 64 c_top + 3#64 + BitVec.setWidth 64 j).toNat =
                      c_top.toNat + 3 + j.toNat := by
                    have := hct_wf.1; have := hcsz_eq; unfold fullArenaClauseSize at *
                    have := hinv0.1.core_ok.arena_len_le; c0_bound
                  have h1 := fullArenaClauseLitsCore_getElem (k := s0.core) (r := c_top.toNat)
                    (j := j.toNat)
                    (by change j.toNat < fullArenaClauseSize s0 c_top.toNat
                        rw [← hcsz_eq]; exact hj_lt)
                    (by rw [← hi]; exact hj_ar)
                  have hmem : (s0.core.arena[(BitVec.setWidth 64 c_top + 3#64 +
                      BitVec.setWidth 64 j).toNat]'hj_ar).toNat ∈
                      fullArenaClauseLits s0 c_top.toNat := by
                    apply List.mem_of_getElem?
                    rw [show s0.core.arena[(BitVec.setWidth 64 c_top + 3#64 +
                        BitVec.setWidth 64 j).toNat]'hj_ar =
                      s0.core.arena[c_top.toNat + 3 + j.toNat]'(by rw [← hi]; exact hj_ar) from
                      cmt3_getElem_eq hi]
                    exact h1
                  exact hinv0.2.1.arena.lits_lt c_top.toNat hct_ref hct_ng _ hmem
                have hl_wv : ((BitVec.setWidth 64 (s0.core.arena[(BitVec.setWidth 64 c_top + 3#64 +
                    BitVec.setWidth 64 j).toNat]'hj_ar) <<< (1 : Nat)) + 1#64).toNat <
                    s0.core.wvec.length := by
                  rw [hinv0.1.core_ok.wvec_len, BitVec.toNat_add, BitVec.toNat_shiftLeft,
                    fid_bv64_32, show (1#64 : BitVec 64).toNat = 1 from rfl, Nat.shiftLeft_eq]
                  have := hinv0.1.core_ok.cur_vars_le
                  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
                have hj1 : (j + 1#32).toNat = j.toNat + 1 := by
                  have := hct_wf.1; have := hcsz_eq; unfold fullArenaClauseSize at *
                  have := hinv0.1.core_ok.arena_len_le; c0_bound
                c0_hfast_nogrp
                refine wp_join_state1 (t := i64) (α := BitVec 64) (fun x => x) (fun _ m3 => m3 = m0)
                  (fun _ nw' m3 hm3 => by
                    rw [hm3]; c0_hfast
                    exact ihj (nw', j + 1#32) m0 (by dsimp only; rw [hj1]; omega)
                      ⟨by rw [hj1]; omega, rfl⟩)
                  (fun Jnl hJnl => by
                    c0_hfast_nogrp
                    · exact hJnl _ m0 rfl
                    · exact hJnl nw_j m0 rfl)
              · c0_hfast; exact hJbb (_, nw_j) m0 rfl))
  -- Capacity guards
  c0_hfast_nogrp
  · c0_hfast; exact hfail s0 m0 hinv0 rfl rfl rfl rfl hm0
  · c0_hfast; exact hfail s0 m0 hinv0 rfl rfl rfl rfl hm0
  · c0_hfast; exact hfail s0 m0 hinv0 rfl rfl rfl rfl hm0
  have hcv_lt : s0.core.cur_vars < c.max_vars := by
    have h1 : ¬ ((BitVec.ofNat 64 c.max_vars).toNat ≤ (BitVec.ofNat 64 s0.core.cur_vars).toNat) :=
      by assumption
    have := hinv0.1.core_ok.cur_vars_le
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)] at h1
    omega
  -- Defrag guard (`group [[.bool]]`)
  refine wp_join_state1 (t := .bool) (α := Bool × FullState) (fun x => x.1)
    (fun (_, sd) md =>
      FullDenseInvW c F0 F_cur sd ∧
      sd.core.cur_vars = s0.core.cur_vars ∧
      sd.core.arena = s0.core.arena ∧ sd.core.arena_len = s0.core.arena_len ∧
      sd.core.fuel = s0.core.fuel ∧
      sd.scratch.scratch_buf = s0.scratch.scratch_buf ∧
      sd.scratch.res_sz = BitVec.ofNat 64 best_k.toNat ∧
      sd.scratch.tarjan_mark = s0.scratch.tarjan_mark ∧
      sd.scratch.tarjan_reach = s0.scratch.tarjan_reach ∧
      (FullMem c sd ⋆ R) md)
    (fun _ (dd0, sd) md ⟨hinv_d, hcv_d, har_d, hal_d, hfl_d, hsb_d, hrs_d, htm_d, htr_d, hmd⟩ => ?_)
    (fun Jdf hJdf => by
      refine wp_join0 (fun m' => m' = m0)
        (fun _ m' hm' => by
          rw [hm']
          refine wp_join_state1 (t := .bool) (α := Bool × FullState) (fun x => x.1)
            (fun (_, sd) md =>
              FullDenseInvW c F0 F_cur sd ∧
              sd.core.cur_vars = s0.core.cur_vars ∧
              sd.core.arena = s0.core.arena ∧ sd.core.arena_len = s0.core.arena_len ∧
              sd.core.fuel = s0.core.fuel ∧
              sd.scratch.scratch_buf = s0.scratch.scratch_buf ∧
              sd.scratch.res_sz = BitVec.ofNat 64 best_k.toNat ∧
              sd.scratch.tarjan_mark = s0.scratch.tarjan_mark ∧
              sd.scratch.tarjan_reach = s0.scratch.tarjan_reach ∧
              (FullMem c sd ⋆ R) md)
            (fun _ (dd_d, sd) md ⟨hi, hcv, har, hal, hfl, hsb, hrs, htm, htr, hmd⟩ => by
              refine wp_join0 (fun m'' => m'' = md)
                (fun _ m'' hm'' => by
                  rw [hm'']
                  refine wp_join0 (fun m3 => ∃ ws3,
                      let s3 := { sd with scratch := { sd.scratch with wsort := ws3 } }
                      FullDenseInvW c F0 F_cur s3 ∧ (FullMem c s3 ⋆ R) m3)
                    (fun _ m3 ⟨ws3, hi3, hm3⟩ => by
                      c0_hfast; exact hfail _ m3 hi3 hcv hfl htm htr hm3)
                    (fun Jfl hJfl => by
                      c0_hfast_nogrp
                      · fid_call hFill
                        refine cmt_fill_wsort_spec hi.1 hmd fun ws3 m3 hws3 hm3 => ?_
                        c0_hfast; exact hJfl m3 ⟨ws3, cmt_fullDenseInvW_set_wsort hi hws3, hm3⟩
                      · c0_hfast; exact hJfl md ⟨sd.scratch.wsort, hi, hmd⟩))
                (fun Jre hJre => by
                  c0_hfast_nogrp
                  · c0_hfast; exact hJre md rfl
                  · c0_hfast; exact hJre md rfl
                  · c0_hfast
                    exact hJdf (dd_d, sd) md ⟨hi, hcv, har, hal, hfl, hsb, hrs, htm, htr, hmd⟩))
            (fun Jdg hJdg => by
              c0_hfast_nogrp
              · fid_call hDefrag
                refine ⟨c, s0, R, rfl, hinv0.1, (m6_denseWatchesInv_of_w hinv0).layout, hm0,
                  fun wv' ws' wl' wso' md hlen' hlay' _ hpres hmd => ?_⟩
                c0_hfast
                exact hJdg (true, _) md
                  ⟨cmt_fullDenseInvW_defrag hinv0 hlen' hlay' hpres,
                   rfl, rfl, rfl, rfl, rfl, hres0, rfl, rfl, hmd⟩
              · c0_hfast
                exact hJdg (false, s0) m0
                  ⟨hinv0, rfl, rfl, rfl, rfl, rfl, hres0, rfl, rfl, hm0⟩))
        (fun Jck hJck => by
          c0_hfast_nogrp
          · c0_hfast; exact hJck m0 rfl
          · c0_hfast; exact hJck m0 rfl
          · c0_hfast
            exact hJdf (false, s0) m0 ⟨hinv0, rfl, rfl, rfl, rfl, rfl, hres0, rfl, rfl, hm0⟩))
  -- Fresh var init (`cur_vars += 1`, `full_init_fresh_var`, `cmt_ext_fresh_var`, zero `deg`/`cnt`)
  c0_hfast_nogrp
  have hcv_add : (BitVec.ofNat 64 sd.core.cur_vars + 1).toNat = sd.core.cur_vars + 1 := by
    c0_bound
  have hcv_inc_len : ({ sd with core := { sd.core with cur_vars := sd.core.cur_vars + 1 } } :
      FullState).LengthsOk c :=
    ⟨{ hinv_d.1.core_ok with
       cur_vars_ge := by dsimp only; have := hinv_d.1.core_ok.cur_vars_ge; omega
       cur_vars_le := by dsimp only; omega
       trail_end_le := by dsimp only; have := hinv_d.1.core_ok.trail_end_le; omega },
     hinv_d.1.scratch_ok⟩
  have hfv_nat : ((BitVec.ofNat 64 sd.core.cur_vars).setWidth 32).toNat = sd.core.cur_vars := by
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  rw [hcv_add] at hm
  fid_call hInitFresh
  refine ⟨c, { sd with core := { sd.core with cur_vars := sd.core.cur_vars + 1 } }, R, rfl,
    hcv_inc_len, by dsimp only [Arg.val]; rw [hfv_nat]; omega, hm,
    fun vals' mrk' fl' lvl' rsns' wv' unass' sc' m_fv hlen_fv hpres_fv hsb_fv hws_fv htm_fv
      htr_fv _ hrs_fv hv0 hv1 hv_oth hmrk0 hmrk_o _ hlvl_o _ hrsns_o hwv0 hwv_o hm_fv => ?_⟩
  let s_fv : FullState :=
    { sd with
      core :=
        { sd.core with
          cur_vars := sd.core.cur_vars + 1, vals := vals', mrk := mrk', flags := fl',
          lvl := lvl', rsns := rsns', wvec := wv', unassigned := unass' }
      scratch := sc' }
  have hmat_d : Step7BvaMatrixInv c F_cur sd (best_k.toNat + 1) bump :=
    cmt_matrix_of_eq hmat hcv_d har_d hal_d hsb_d
  dsimp only [Arg.val] at hv0 hv1 hv_oth hmrk0 hmrk_o hlvl_o hrsns_o hwv0 hwv_o
  rw [hfv_nat] at hv0 hv1 hv_oth hmrk0 hmrk_o hlvl_o hrsns_o hwv0 hwv_o
  obtain ⟨F_next, hinv_fv, hent_pos, hrow_res⟩ := cmt_ext_fresh_var hinv_d (by omega) hmat_d
    hlen_fv rfl hv0 hv1 hv_oth hmrk0 hmrk_o hlvl_o hrsns_o hwv0 hwv_o hpres_fv.1 hpres_fv.2
  rw [hcv_d, hsb_d] at hent_pos hrow_res
  rw [← hbro_eq, ← hmn_eq] at hrow_res
  have hfresh_nat : (((BitVec.ofNat 64 sd.core.cur_vars).setWidth 32) <<< (1 : BitVec 32)).toNat =
      2 * s0.core.cur_vars := by
    rw [hcv_d]
    change ((BitVec.ofNat 64 s0.core.cur_vars).setWidth 32 <<< (1 : Nat)).toNat = _
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  have hfresh1_or : ((((BitVec.ofNat 64 sd.core.cur_vars).setWidth 32) <<< (1 : BitVec 32)) |||
      1#32).toNat = 2 * s0.core.cur_vars + 1 := by
    have h1 := FullBvaFwdTactics.bv32_or1_of_even (x := ((BitVec.ofNat 64 sd.core.cur_vars).setWidth
      32) <<< (1 : BitVec 32)) (by rw [hfresh_nat]; omega)
    rw [h1, hfresh_nat]
  have hd0 : (BitVec.setWidth 64 (((BitVec.ofNat 64 sd.core.cur_vars).setWidth 32) <<<
      (1 : BitVec 32))).toNat < s_fv.core.repr.length := by
    rw [fid_bv64_32, hfresh_nat, hinv_fv.1.core_ok.repr_len]; omega
  have hd1 : (BitVec.setWidth 64 ((((BitVec.ofNat 64 sd.core.cur_vars).setWidth 32) <<<
      (1 : BitVec 32)) ||| 1#32)).toNat <
      (s_fv.core.repr.set (BitVec.setWidth 64 (((BitVec.ofNat 64 sd.core.cur_vars).setWidth 32) <<<
        (1 : BitVec 32))).toNat 0).length := by
    rw [List.length_set, fid_bv64_32, hfresh1_or, hinv_fv.1.core_ok.repr_len]; omega
  have hc0 : (BitVec.setWidth 64 (((BitVec.ofNat 64 sd.core.cur_vars).setWidth 32) <<<
      (1 : BitVec 32))).toNat < s_fv.scratch.wsort.length := by
    rw [fid_bv64_32, hfresh_nat, hinv_fv.1.scratch_ok.wsort_len]; omega
  have hc1 : (BitVec.setWidth 64 ((((BitVec.ofNat 64 sd.core.cur_vars).setWidth 32) <<<
      (1 : BitVec 32)) ||| 1#32)).toNat <
      (s_fv.scratch.wsort.set (BitVec.setWidth 64 (((BitVec.ofNat 64 sd.core.cur_vars).setWidth 32)
        <<< (1 : BitVec 32))).toNat 0).length := by
    rw [List.length_set, fid_bv64_32, hfresh1_or, hinv_fv.1.scratch_ok.wsort_len]; omega
  c0_hfast_nogrp
  have hrow_res0 : ∀ m < mn.toNat, ∃ res : List Nat,
      (∀ x ∈ res, x < 2 * s0.core.cur_vars) ∧ (res.map (· / 2)).Nodup ∧
      FidBvaRowEntryOk F_cur s0 (s0.scratch.scratch_buf[best_k.toNat]?.getD 0#32).toNat
        (s0.scratch.scratch_buf[brow_off.toNat + m]?.getD 0#32) res ∧
      (cnfOfClauses F_next).EntailsClause (cnfClause ((2 * s0.core.cur_vars + 1) :: res)) := by
    intro m hm_lt
    obtain ⟨res, h1, h2, h3, h4⟩ := hrow_res m hm_lt
    exact ⟨res, h1, h2, cmt_rowEntry_of_eq hcv_d.symm har_d.symm hal_d.symm h3, h4⟩
  obtain ⟨rp', ws', hrp', hws', hm_z⟩ : ∃ rp' ws',
      rp'.length = 2 * c.max_vars ∧ ws'.length = 2 * c.max_vars ∧
      (FullMem c { s_fv with core := { s_fv.core with repr := rp' },
                             scratch := { s_fv.scratch with wsort := ws' } } ⋆ R) m :=
    ⟨_, _, by simp [hinv_fv.1.core_ok.repr_len], by simp [hinv_fv.1.scratch_ok.wsort_len], hm⟩
  let s_z : FullState :=
    { s_fv with core := { s_fv.core with repr := rp' },
                scratch := { s_fv.scratch with wsort := ws' } }
  have hinv_z : FullDenseInvW c F0 F_next s_z :=
    cmt_fullDenseInvW_set_wsort (fullDenseInvW_set_repr hinv_fv hrp') hws'
  exact cmt_phases_wp (best_k := best_k) (sc := sc) (brow_off := brow_off) (mn := mn)
    (dd0 := dd0) (cv64 := BitVec.ofNat 64 sd.core.cur_vars)
    hFill hAddBin hAllocCl hWatchPush hUnwatch hDelBin hinv0.1 hinv0.2.1 hinv_z
    (by dsimp only [s_z, s_fv]; omega) (by rw [hcv_d]) hbk1 hbk_sc rfl hbro_eq hmn_eq hmat
    hent_pos hrow_res0 har_d hal_d (by dsimp only [s_z, s_fv]; rw [hsb_fv, hsb_d])
    (by dsimp only [s_z, s_fv]; rw [hrs_fv, hrs_d]) hfl_d
    (by dsimp only [s_z, s_fv]; rw [htm_fv, htm_d])
    (by dsimp only [s_z, s_fv]; rw [htr_fv, htr_d]) hm_z hQ

end

end LeanQbe.T.Examples.Kissat.Proof.Factor
