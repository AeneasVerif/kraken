/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep8
public import LeanQbe.T.Examples.Kissat.FullFidelityStep8ProofBva0
public import LeanQbe.T.Examples.Kissat.FullFidelityStep8ProofBva1
public import LeanQbe.T.Examples.Kissat.FullFidelityStep8ProofBva2
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
# Kissat Fidelity Step-8 BVA Commit WP Proof (`FullFidelityStep8ProofBva`)

Parametric `(Γ : Env)` WP proof (`0` `import all`, `public section`, `XPost`-polymorphic) of
`full_bva_commit_step8_wp`: Step-8 `FullFidelityStep8.full_bva_commit_body` satisfies
`FullFidelityStep7.step7BvaCommitSpec`, threading `defrag_dirty` to skip redundant `wsort` (`cnt`)
wipes when defrag could not run while preserving every state & matrix invariant.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep8

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

local elab "c0_hsteps_np" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { pruneJnz := false } 10000
local elab "c0_hstep_np" : tactic => LeanQbe.T.C0HeadStep.headSteps { pruneJnz := false } 1
local elab "c0_hsteps_nogrp_np" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { unrollGroup := false, pruneJnz := false } 10000

private theorem s8_prescan_mi_wp {Γ : Env} {Q : Post [.bool]} {X : XPost}
    (hDefrag : ∀ args m Q X, Full.fullWstackDefragSpec args m Q X →
      Γ "full_wstack_defrag" [i64] [] args m Q X)
    (hInitFresh : ∀ args m Q X, step7InitFreshVarSpec args m Q X →
      Γ "full_init_fresh_var" [i64, i32] [] args m Q X)
    (hAddBin : FidAddBinHyp Γ) (hAllocCl : FidAllocClHyp Γ) (hWPush : FidWPushHyp Γ)
    (hDelBin : FidDelBinHyp Γ) (hUnwatch : FidUnwatchHyp Γ)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {R : Mem 64 → Prop} {best_k sc brow_off mn_bv : Val i32} {need_w0 : Val i64}
    {m : Mem 64} {bump : Nat}
    (hinv : FullDenseInvW c F0 F_cur s)
    (hbk1 : 1 ≤ best_k.toNat) (hbk_sc : best_k.toNat < fidStepsCap c.scratch_cap)
    (hmat : FidBvaMatrixInv c F_cur s (best_k.toNat + 1) bump)
    (hlay : Step7BvaLayout c s (best_k.toNat + 1))
    (hres : s.scratch.res_sz = BitVec.ofNat 64 best_k.toNat)
    (hsc_nat : sc.toNat = fidStepsCap c.scratch_cap)
    (hdm_bv : (best_k + 1#32).toNat = best_k.toNat + 1)
    (hbo_getD :
      (s.scratch.scratch_buf[sc.toNat + best_k.toNat]?.getD 0#32).toNat = brow_off.toNat)
    (hmn_getD :
      (s.scratch.scratch_buf[2 * sc.toNat + best_k.toNat]?.getD 0#32).toNat = mn_bv.toNat)
    (hbk_entries : ∀ idx < mn_bv.toNat, ∃ res : List Nat,
      FidBvaRowEntryOk F_cur s (s.scratch.scratch_buf[best_k.toNat]?.getD 0#32).toNat
        (s.scratch.scratch_buf[brow_off.toNat + idx]?.getD 0#32) res)
    (hro_mn : brow_off.toNat + mn_bv.toNat ≤ bump)
    (hbump_le : bump ≤ c.scratch_cap)
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ ok s' m', FullDenseInv c F0 s' → s.core.cur_vars ≤ s'.core.cur_vars →
      (ok = true → s.core.cur_vars < s'.core.cur_vars) →
      (ok = true → Step7BvaCommittedOk c s' best_k.toNat) → s'.core.fuel = s.core.fuel →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach → (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    wp Γ Q X (s8PreMidExpr c.hdr c.pArena c.pScratchBuf c.pWsort c.pFlags c.pWvec best_k sc
      (best_k + 1#32) brow_off mn_bv |>
      sGrp64_32v (fun (_ : Tup Val [i64, i32]) (_ : Mem 64) => True) need_w0 |> sStep |> sElse)
      m := by
  have hmx := c.hmaxv; have hwcap := c.hwcap; have har_b := c.harena; have hscr_b := c.hscr
  unfold dimacsBound at hmx hwcap har_b hscr_b
  have hcl := hinv.1.core_ok; have hsc := hinv.1.scratch_ok
  have hcv_le := hcl.cur_vars_le; have hsb_len := hsc.scratch_buf_len; have hwv_len := hcl.wvec_len
  have hsc4 := fidStepsCap_mul4_le c.scratch_cap
  have heqpm : s8PreMidExpr c.hdr c.pArena c.pScratchBuf c.pWsort c.pFlags c.pWvec best_k sc
      (best_k + 1#32) brow_off mn_bv = s8PreMidExpr c.hdr c.pArena c.pScratchBuf c.pWsort
      c.pFlags c.pWvec best_k sc (best_k + 1#32) brow_off mn_bv := rfl
  conv at heqpm =>
    rhs
    unfold s8PreMidExpr s8HdrExpr
    delta FullFidelityStep8.full_bva_commit_body
    dsimp only [sSteps, sStep, sLet32, sLd64, sLd32, sCall32, sDummyTup, sDummyVal, i64, i32]
  refine (congrArg (fun e => wp Γ Q X
    (e |> sGrp64_32v (fun (_ : Tup Val [i64, i32]) (_ : Mem 64) => True) need_w0 |>
      sStep |> sElse) m) heqpm).mpr ?_
  dsimp only [sGrp64_32v, sStep, sElse, sDummyTup, sDummyVal, i64, i32]
  refine wp_loop_inv
    (fun (_need_ar, _need_w, mi, ()) mm => m = mm ∧ mi.toNat ≤ mn_bv.toNat)
    (fun (_, _, mi, _) _ => mn_bv.toNat - mi.toNat) (fun Jpre hJpre => by
      clear heqpm; c0_hsteps; exact hJpre (16#64, need_w0, 0#32, ()) m ⟨rfl, Nat.zero_le _⟩)
    (fun Jpre (need_ar, need_w, mi, ()) mm ⟨hmm, hmi_le⟩ ihpre => ?_)
  · rcases hmm with rfl; c0_hsplit
    · clear heqpm
      have hmi_lt : mi.toNat < mn_bv.toNat := by assumption
      have hmi1 : (mi + 1#32).toNat = mi.toNat + 1 := by c0_bound
      have hctop_idx : (brow_off + mi).toNat = brow_off.toNat + mi.toNat := by
        have h1 : (brow_off + mi).toNat = (brow_off + mi : BitVec 32).toNat := rfl
        rw [h1, BitVec.toNat_add]; apply Nat.mod_eq_of_lt; omega
      have hctop_sb : (BitVec.setWidth 64 (brow_off + mi)).toNat <
          s.scratch.scratch_buf.length := by rw [bv64_setWidth_32, hctop_idx, hsb_len]; omega
      let c_top := s.scratch.scratch_buf[brow_off.toNat + mi.toNat]'(by omega)
      have hctop_eq : s.scratch.scratch_buf[(BitVec.setWidth 64
          (brow_off + mi)).toNat]'hctop_sb = c_top := by
        dsimp only [c_top]; simp only [bv64_setWidth_32, hctop_idx]
      have hctop_mod_n : (brow_off.toNat + mi.toNat) % 2 ^ 32 =
          brow_off.toNat + mi.toNat := Nat.mod_eq_of_lt (by omega)
      have hctop_mod : s.scratch.scratch_buf[(brow_off.toNat + mi.toNat) % 2 ^ 32]'(by
          rw [hctop_mod_n, hsb_len]; omega) = c_top := by
        dsimp only [c_top]; simp only [hctop_mod_n]
      obtain ⟨_res_ct, hctop_ok⟩ := hbk_entries mi.toNat hmi_lt
      have hctop_getD : s.scratch.scratch_buf[brow_off.toNat + mi.toNat]?.getD 0#32 =
          c_top := by
        dsimp only [c_top]; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      rw [hctop_getD] at hctop_ok
      c0_hsteps_nogrp
      refine wp_join_state_pure (ts := [i64, i64]) (α := BitVec 64 × BitVec 64)
        (fun p => (p.1, p.2, ())) (fun _ => True) (fun _ ⟨na', nw'⟩ _ => ?_)
        (fun Jpn hJpn => ?_)
      · c0_hsteps; exact ihpre (na', nw', mi + 1#32, ()) m (by dsimp only; rw [hmi1]; omega)
          ⟨rfl, by rw [hmi1]; omega⟩
      c0_hsplit
      · have hbin_ct : (c_top &&& 0x80000000#32) ≠ 0#32 := by
          simpa only [← hctop_mod] using (by assumption : _)
        unfold FidBvaRowEntryOk at hctop_ok; rw [ite_eq_left hbin_ct] at hctop_ok
        have hq_lt : (c_top &&& 0x7FFFFFFF#32).toNat < 2 * s.core.cur_vars := hctop_ok.1
        have hq_wv : ((BitVec.setWidth 64 (s.scratch.scratch_buf[(BitVec.setWidth 64
            (brow_off + mi)).toNat]'hctop_sb &&& 0x7FFFFFFF#32) <<< (1 : Nat)) +
            1).toNat < s.core.wvec.length := by
          rw [hctop_eq, hwv_len]; simp only [bv_c0, show (1 : BitVec 64).toNat = 1 from rfl]
          omega
        c0_hfast; exact hJpn (need_ar, _) trivial
      · have hbin_ct : (c_top &&& 0x80000000#32) = 0#32 := by
          simpa only [← hctop_mod] using (by assumption : _)
        unfold FidBvaRowEntryOk at hctop_ok
        rw [ite_eq_right (fun h' => h' hbin_ct)] at hctop_ok
        obtain ⟨hct_ref0, hct_ng0, _, _, _, _, _⟩ := hctop_ok
        have hct_wf := hinv.2.1.arena.refs_wf c_top.toNat hct_ref0
        have hct2_n : (BitVec.setWidth 64 c_top + 2).toNat = c_top.toNat + 2 := by
          change (BitVec.setWidth 64 c_top + 2#64).toNat = _; c0_bound
        have hct2_ar : (BitVec.setWidth 64 (s.scratch.scratch_buf[(BitVec.setWidth 64
            (brow_off + mi)).toNat]'hctop_sb) + 2).toNat < s.core.arena.length := by
          rw [hctop_eq, hct2_n]; have := hcl.arena_len_le; have := hcl.arena_len_arr; omega
        let csz_bv := s.core.arena[c_top.toNat + 2]'(by
          have := hcl.arena_len_le; have := hcl.arena_len_arr; omega)
        have hcsz_eq : csz_bv.toNat = fullArenaClauseSizeCore s.core c_top.toNat := by
          dsimp only [csz_bv]; unfold fullArenaClauseSizeCore
          rw [List.getElem?_eq_getElem (by
            have := hcl.arena_len_le; have := hcl.arena_len_arr; omega), Option.getD_some]
        have hbk_sb : (BitVec.setWidth 64 best_k).toNat < s.scratch.scratch_buf.length := by
          rw [bv64_setWidth_32, hsb_len]; omega
        c0_hsteps_nogrp
        refine wp_loop_inv (fun (_nw, ji, ()) mji => m = mji ∧ ji.toNat ≤ csz_bv.toNat)
          (fun (_, ji, _) _ => csz_bv.toNat - ji.toNat)
          (fun Jj hJj => by c0_hsteps; exact hJj (need_w, 0#32, ()) m ⟨rfl, Nat.zero_le _⟩)
          (fun Jj (nwj, ji, ()) mji ⟨hmji, hji_le⟩ ihj => ?_)
        rcases hmji with rfl; c0_hsteps_nogrp
        · have hct2_mod : (c_top.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64 =
              c_top.toNat + 2 := by rw [show BitVec.toNat (2 : BitVec 64) = 2 from rfl]; omega
          have hji_lt : ji.toNat < csz_bv.toNat := by
            dsimp only [csz_bv]
            have h1 : ji.toNat < (s.core.arena[(c_top.toNat + BitVec.toNat (2 : BitVec 64)) %
                2 ^ 64]'(by rw [hct2_mod]; have := hcl.arena_len_le
                            have := hcl.arena_len_arr; omega)).toNat := by
              simpa only [← hctop_mod] using (by assumption : _)
            simpa only [hct2_mod] using h1
          have hji1 : (ji + 1#32).toNat = ji.toNat + 1 := by c0_bound
          have hctj_n : (BitVec.setWidth 64 c_top + 3 + BitVec.setWidth 64 ji).toNat =
              c_top.toNat + 3 + ji.toNat := by
            change (BitVec.setWidth 64 c_top + 3#64 + BitVec.setWidth 64 ji).toNat = _; c0_bound
          have hctj_ar : c_top.toNat + 3 + ji.toNat < s.core.arena.length := by
            have := hcl.arena_len_le; have := hcl.arena_len_arr; omega
          have hctj_ar_sb : (BitVec.setWidth 64 (s.scratch.scratch_buf[(BitVec.setWidth 64
              (brow_off + mi)).toNat]'hctop_sb) + 3 + BitVec.setWidth 64 ji).toNat <
              s.core.arena.length := by rw [hctop_eq, hctj_n]; exact hctj_ar
          have hlj_lt : (s.core.arena[c_top.toNat + 3 + ji.toNat]'hctj_ar).toNat <
              2 * s.core.cur_vars := by
            have h1 := FullBvaFwdHelpers.fullArenaClauseLitsCore_getElem (k := s.core)
              (r := c_top.toNat) (j := ji.toNat) (by rw [← hcsz_eq]; exact hji_lt) hctj_ar
            exact hinv.2.1.arena.lits_lt c_top.toNat hct_ref0 hct_ng0 _
              (List.mem_of_getElem? h1)
          c0_hsteps_nogrp; refine wp_join_state_pure (ts := [i64]) (α := BitVec 64)
            (fun x => (x, ())) (fun _ => True) (fun _ nw' _ => by
              c0_hsteps; exact ihj (nw', ji + 1#32, ()) m (by dsimp only; rw [hji1]; omega)
                ⟨rfl, by rw [hji1]; omega⟩)
            (fun Jlf hJlf => ?_)
          c0_hsplit
          · have hlj_wv : ((BitVec.setWidth 64 (s.core.arena[(BitVec.setWidth 64
                (s.scratch.scratch_buf[(BitVec.setWidth 64
                  (brow_off + mi)).toNat]'hctop_sb) +
                3 + BitVec.setWidth 64 ji).toNat]'hctj_ar_sb) <<< (1 : Nat)) + 1).toNat <
                s.core.wvec.length := by
              have hlj_eq : s.core.arena[(BitVec.setWidth 64
                  (s.scratch.scratch_buf[(BitVec.setWidth 64
                    (brow_off + mi)).toNat]'hctop_sb) + 3 +
                  BitVec.setWidth 64 ji).toNat]'hctj_ar_sb =
                  s.core.arena[c_top.toNat + 3 + ji.toNat]'hctj_ar := by
                simp only [hctop_eq, hctj_n]
              rw [hlj_eq, hwv_len]; simp only [bv_c0, show (1 : BitVec 64).toNat = 1 from rfl]
              omega
            c0_hsteps; exact hJlf _ trivial
          · c0_hsteps; exact hJlf nwj trivial
        · exact hJpn (_, nwj) trivial
    · c0_hsteps_nogrp_np
      · exact hQ false s m hinv.toDense (Nat.le_refl _) (fun h => absurd h (by decide))
          (fun h => absurd h (by decide)) rfl rfl rfl hm
      · exact hQ false s m hinv.toDense (Nat.le_refl _) (fun h => absurd h (by decide))
          (fun h => absurd h (by decide)) rfl rfl rfl hm
      · exact hQ false s m hinv.toDense (Nat.le_refl _) (fun h => absurd h (by decide))
          (fun h => absurd h (by decide)) rfl rfl rfl hm
      · have hcv_lt : s.core.cur_vars < c.max_vars := by clear heqpm; c0_bound
        have htail := s8_pre_exit_wp (Γ := Γ) (Q := Q) (X := X)
          hDefrag hInitFresh hAddBin hAllocCl hWPush hDelBin hUnwatch
          (sc := sc) (dm_bv := best_k + 1#32) (brow_off := brow_off) (mn_bv := mn_bv)
          (need_ar := need_ar) (need_w := need_w) (bump := bump)
          hinv hbk1 hbk_sc hmat hlay hres hsc_nat hdm_bv hbo_getD hmn_getD hm hcv_lt hQ
        unfold s8PreExitExpr at htail
        replace htail := (congrArg (fun e => wp Γ Q X
          (e |> sGrp64_32 (fun (_ : Tup Val [i64, i32]) (_ : Mem 64) => True) |> sStep |> sElse |>
            sGrp64_64_32v (fun (_ : Tup Val [i64, i64, i32]) (_ : Mem 64) => True) need_ar
              need_w |>
            sStep |> sElse |> sSteps 5 |> sElse |> sSteps 5 |> sElse |> sSteps 6 |> sElse)
          m) heqpm).mp htail
        dsimp only [sSteps, sStep, sGrp64_32, sGrp64_64_32v, sElse, sDummyTup, sDummyVal, i64,
          i32] at htail
        exact htail

/-- Step-8 `full_bva_commit` (skipping redundant `wsort` wipe when `full_wstack_defrag*` could not
execute) satisfies `FullFidelityStep7.step7BvaCommitSpec` parametrically in `Γ`. -/
theorem full_bva_commit_step8_wp (Γ : Env)
    (hStepsCap : ∀ args m Q X, fidBvaStepsCapSpec args m Q X →
      Γ "full_bva_steps_cap_fid" [i64] [i32] args m Q X)
    (hDefrag : ∀ args m Q X, Full.fullWstackDefragSpec args m Q X →
      Γ "full_wstack_defrag" [i64] [] args m Q X)
    (hInitFresh : ∀ args m Q X, step7InitFreshVarSpec args m Q X →
      Γ "full_init_fresh_var" [i64, i32] [] args m Q X)
    (hAddBin : ∀ args m Q X, Full.fullAddBinSpec args m Q X →
      Γ "full_add_bin" [i64, i32, i32] [i64] args m Q X)
    (hAllocCl : ∀ args m Q X, Full.fullAllocClSpec args m Q X →
      Γ "full_alloc_cl" [i64, i32, i32, .bool] [i64] args m Q X)
    (hWPush : ∀ args m Q X, Full.fullWatchPushSpec args m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] args m Q X)
    (hDelBin : ∀ args m Q X, Full.fullDeleteBinarySpec args m Q X →
      Γ "full_delete_binary" [i64, i32, i32] [] args m Q X)
    (hUnwatch : ∀ args m Q X, Full.fullUnwatchLargeSpec args m Q X →
      Γ "full_unwatch_large" [i64, i32, i32] [] args m Q X) :
    ∀ args m Q X, step7BvaCommitSpec args m Q X →
      Func.wp Γ FullFidelityStep8.full_bva_commit_body args m Q X := by
  rintro ⟨h, best_k, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, bump, rfl, hinv, hbk1, hbk_sc, ⟨hmat, hlay⟩, hres, hm, hQ⟩
  have hmx := c.hmaxv; have hwcap := c.hwcap; have har_b := c.harena; have hscr_b := c.hscr
  unfold dimacsBound at hmx hwcap har_b hscr_b
  have hcl := hinv.1.core_ok; have hsc := hinv.1.scratch_ok
  have hcv_le := hcl.cur_vars_le; have hsb_len := hsc.scratch_buf_len; have hwv_len := hcl.wvec_len
  have hsc_pos := hmat.1; have hsc_le256 := fidStepsCap_le_256 c.scratch_cap
  have hsc4 := fidStepsCap_mul4_le c.scratch_cap
  have hbump_ge := hmat.2.2.2.1; have hbump_le := hmat.2.2.2.2.1
  have hbk_row := hmat.2.2.2.2.2 best_k.toNat (by omega)
  obtain ⟨hfbk_lt, hro_ge, hmn_lo, hro_mn, _, hbk_entries⟩ := hbk_row
  c0_hsteps_nogrp
  · exact hQ false s m hinv.toDense (Nat.le_refl _) (fun h => absurd h (by decide))
          (fun h => absurd h (by decide)) rfl rfl rfl hm
  · apply wp_call_of_spec; apply hStepsCap; unfold fidBvaStepsCapSpec; dsimp only [vals, Arg.val]
    have hcap64 : (BitVec.ofNat 64 c.scratch_cap).toNat = c.scratch_cap := by c0_bound
    generalize hsc_def :
      BitVec.ofNat 32 (fidStepsCap (BitVec.ofNat 64 c.scratch_cap).toNat) = sc
    have hsc_nat : sc.toNat = fidStepsCap c.scratch_cap := by
      rw [← hsc_def, hcap64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hbk_sc_bv : best_k.toNat < sc.toNat := by omega
    have hsc_ne0 : sc ≠ 0#32 := by
      intro h; have := congrArg BitVec.toNat h
      rw [hsc_nat, show (0#32 : BitVec 32).toNat = 0 from rfl] at this; omega
    have hdm_bv : (best_k + 1#32).toNat = best_k.toNat + 1 := by simp only [bv_c0]; omega
    have hsc_bk : (sc + best_k).toNat = sc.toNat + best_k.toNat := by c0_bound
    have h2sc_bk : (2 * sc + best_k).toNat = 2 * sc.toNat + best_k.toNat := by
      have h2 : (2 * sc).toNat = 2 * sc.toNat := by
        change ((2#32 : BitVec 32) * sc).toNat = _; rw [BitVec.toNat_mul]
        have : (2#32 : BitVec 32).toNat = 2 := rfl; rw [this]; apply Nat.mod_eq_of_lt; omega
      change (2 * sc + best_k : BitVec 32).toNat = _; rw [BitVec.toNat_add, h2]
      apply Nat.mod_eq_of_lt; omega
    let brow_off := s.scratch.scratch_buf[sc.toNat + best_k.toNat]'(by omega)
    let mn_bv := s.scratch.scratch_buf[2 * sc.toNat + best_k.toNat]'(by omega)
    have hbo_getD :
        (s.scratch.scratch_buf[sc.toNat + best_k.toNat]?.getD 0#32).toNat = brow_off.toNat := by
      dsimp only [brow_off]; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    have hmn_getD :
        (s.scratch.scratch_buf[2 * sc.toNat + best_k.toNat]?.getD 0#32).toNat = mn_bv.toNat := by
      dsimp only [mn_bv]; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    rw [← hsc_nat] at hro_ge hmn_lo hro_mn hbk_entries
    rw [hbo_getD] at hro_ge hro_mn hbk_entries
    rw [hmn_getD] at hmn_lo hro_mn hbk_entries
    have hbo_eq : s.scratch.scratch_buf[(BitVec.setWidth 64 (sc + best_k)).toNat]'(by
        rw [bv64_setWidth_32, hsc_bk]; omega) = brow_off := by
      dsimp only [brow_off]; simp only [bv64_setWidth_32, hsc_bk]
    have hmn_eq : s.scratch.scratch_buf[(BitVec.setWidth 64 (2 * sc + best_k)).toNat]'(by
        rw [bv64_setWidth_32, h2sc_bk]; omega) = mn_bv := by
      dsimp only [mn_bv]; simp only [bv64_setWidth_32, h2sc_bk]
    have h2sc_bk_mod : (2 * sc.toNat + best_k.toNat) % 2 ^ 32 = 2 * sc.toNat + best_k.toNat := by
      omega
    let dm := best_k.toNat + 1
    c0_hsteps_nogrp
    · refine wp_loop_inv (fun (_need_w, si, ()) msi => m = msi ∧ si.toNat ≤ dm)
        (fun (_, si, _) _ => dm - si.toNat)
        (fun Jsi hJsi => by c0_hsteps; exact hJsi (_, 0#32, ()) m ⟨rfl, Nat.zero_le _⟩)
        (fun Jsi (need_w0, si, ()) msi ⟨hmsi, hsi_le⟩ ihsi => ?_)
      rcases hmsi with rfl; c0_hsteps_nogrp
      · have hsi_lt : si.toNat < dm := by
          have h1 : si.toNat < (best_k + 1#32).toNat := (by assumption); omega
        have hsi1 : (si + 1#32).toNat = si.toNat + 1 := by c0_bound
        have hfs_sb : (BitVec.setWidth 64 si).toNat < s.scratch.scratch_buf.length := by
          rw [bv64_setWidth_32, hsb_len]; omega
        have hfs_lt : (s.scratch.scratch_buf[si.toNat]'(by omega)).toNat < 2 * s.core.cur_vars := by
          have h1 := (hmat.2.2.2.2.2 si.toNat (by omega)).1
          simpa only [List.getElem?_eq_getElem (by omega : si.toNat < s.scratch.scratch_buf.length),
            Option.getD_some] using h1
        have hfs_wv : ((BitVec.setWidth 64
            (s.scratch.scratch_buf[(BitVec.setWidth 64 si).toNat]'hfs_sb) <<< (1 : Nat)) +
            1).toNat < s.core.wvec.length := by
          rw [hwv_len]; simp only [bv_c0, show (1 : BitVec 64).toNat = 1 from rfl]; omega
        c0_hsteps; exact ihsi (_, si + 1#32, ()) m (by dsimp only; rw [hsi1]; omega)
          ⟨rfl, by rw [hsi1]; omega⟩
      · have hmi := s8_prescan_mi_wp (Γ := Γ) (Q := Q) (X := X)
          hDefrag hInitFresh hAddBin hAllocCl hWPush hDelBin hUnwatch
          (sc := sc) (brow_off := brow_off) (mn_bv := mn_bv) (need_w0 := need_w0) (bump := bump)
          hinv hbk1 hbk_sc hmat hlay hres hsc_nat hdm_bv hbo_getD hmn_getD
          (fun idx hidx => let ⟨res, _, _, hok, _, _⟩ := hbk_entries idx hidx; ⟨res, hok⟩)
          hro_mn hbump_le hm hQ
        rw [← hbo_eq, ← hmn_eq] at hmi
        unfold s8PreMidExpr s8HdrExpr at hmi
        delta FullFidelityStep8.full_bva_commit_body at hmi
        dsimp only [sSteps, sStep, sLet32, sLd64, sLd32, sCall32, sGrp64_32v, sElse, sDummyTup,
          sDummyVal, i64, i32] at hmi
        exact hmi

end LeanQbe.T.Examples.Kissat.FullFidelityStep8

end
