module

public import LeanQbe.T.Examples.Kissat.FullM6BveFwdProof1
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullDenseWatchLemmas1
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Wave-2 `PR-W2D` (`RC-22`) Proofs — Part 2 (Cluster 2a: Forward Watch & Candidate Helpers)

M1-clean proof module (`public section`, `0` `@[expose]`, `0` `import all`, `private` helpers):
1. `full_fwd_flush_large_m6_wp`
2. `full_fwd_reconnect_irred_m6_wp`
3. `full_fwd_connect_subsumer_m6_wp`
4. `full_fwd_collect_sort_m6_wp`
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM6BveFwd

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullDenseWatchHelpers
open LeanQbe.T.Examples.Kissat.FullFastBveBudgets
open Kraken.Bedrock2.Test

open scoped FullArenaTactics

local macro "m6_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

private theorem m6_zero_mem_arenaRefs {c : FullCfg} {F_cur : List (List Nat)}
    {k : FullCoreState} (ha : FullArenaClausesInv c F_cur k) (hpos : 0 < k.arena_len) :
    0 ∈ fullArenaClauseRefsCore k := by
  rcases ha.len_ok with hz | h3
  · omega
  · unfold fullArenaClauseRefsCore
    cases hal : k.arena_len with
    | zero => omega
    | succ n =>
      rw [fullArenaScanRefs]
      have hle : 0 + 3 ≤ n + 1 := by omega
      simp [hle]

private theorem m6_sz_and_mask_eq {sz : BitVec 32} (hlt : sz.toNat < 2 ^ 31) :
    (sz &&& 0x7FFFFFFF#32) = sz := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (0x7FFFFFFF#32 : BitVec 32).toNat = 2 ^ 31 - 1 by decide]
  exact Nat.and_two_pow_sub_one_eq_mod sz.toNat 31 |>.trans (Nat.mod_eq_of_lt hlt)

private theorem m6_sz_and_mask_no_bin {sz : BitVec 32} :
    ((sz &&& 0x7FFFFFFF#32) &&& 0x80000000#32) = 0#32 := by
  ext i hi; simp only [BitVec.getElem_and, BitVec.getElem_zero]
  have h0 : ((0x7FFFFFFF#32 &&& 0x80000000#32) : BitVec 32)[i] = false := by
    have : (0x7FFFFFFF#32 &&& 0x80000000#32) = 0#32 := by decide
    rw [this]; simp
  simp only [BitVec.getElem_and] at h0
  rw [Bool.and_assoc, h0, Bool.and_false]

private theorem m6_bv32_ne_sent_of_lt {x : BitVec 32} (hlt : x.toNat < 2 ^ 31) :
    x ≠ 0xFFFFFFFF#32 := fun h => by
  have := congrArg BitVec.toNat h; simp at this; omega

private theorem m6_and_garb_zero_of_mask {hdr : BitVec 32}
    (h : (hdr &&& (0x00080000#32 ||| 0x00400000#32)) = 0#32) :
    (hdr &&& 0x00080000#32) = 0#32 := by
  have hmask : ((0x00080000#32 ||| 0x00400000#32) &&& 0x00080000#32) = 0x00080000#32 := by
    decide
  calc hdr &&& 0x00080000#32
      = hdr &&& ((0x00080000#32 ||| 0x00400000#32) &&& 0x00080000#32) := by rw [hmask]
    _ = (hdr &&& (0x00080000#32 ||| 0x00400000#32)) &&& 0x00080000#32 := by
      rw [BitVec.and_assoc]
    _ = 0#32 := by rw [h, BitVec.zero_and]

/-! ## 1. `full_fwd_flush_large_m6` -/

/-- Contract for `full_fwd_flush_large_m6`: removes all large-clause occurrence entries from dense
watch lists (keeping binary watches intact) and optionally defragments `watch_stk`. -/
def fullFwdFlushLargeM6Spec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ (FullMem c s ⋆ R) m ∧
    ∀ s' m',
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.arena = s.core.arena → s'.core.arena_len = s.core.arena_len →
      s'.core.fuel = s.core.fuel → s'.core.oom = s.core.oom →
      s'.core.inconsistent = s.core.inconsistent →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.red_refs = s.scratch.red_refs →
      s'.scratch.scratch_buf = s.scratch.scratch_buf →
      s'.scratch.work_stk1 = s.scratch.work_stk1 →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      s'.scratch.sim_sig = s.scratch.sim_sig →
      (FullMem c s' ⋆ R) m' → Q () m'

theorem fullFwdFlushLargeM6Spec_noExit :
    ∀ xs m Q X, fullFwdFlushLargeM6Spec xs m Q X →
      fullFwdFlushLargeM6Spec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem fullFwdFlushLargeM6Spec_intro {h : BitVec 64} {m : Mem 64}
    {Q : Post []} {X : XPost} {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {R : Mem 64 → Prop} (hh : h = c.hdr) (hdw : FullDenseInvW c F0 F_cur s)
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ s' m',
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.arena = s.core.arena → s'.core.arena_len = s.core.arena_len →
      s'.core.fuel = s.core.fuel → s'.core.oom = s.core.oom →
      s'.core.inconsistent = s.core.inconsistent →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.red_refs = s.scratch.red_refs →
      s'.scratch.scratch_buf = s.scratch.scratch_buf →
      s'.scratch.work_stk1 = s.scratch.work_stk1 →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      s'.scratch.sim_sig = s.scratch.sim_sig →
      (FullMem c s' ⋆ R) m' → Q () m') :
    fullFwdFlushLargeM6Spec (h, ()) m Q X :=
  ⟨c, F0, F_cur, s, R, hh, hdw, hm, hQ⟩

private def FlushStatePres (s s' : FullState) : Prop :=
  s'.core.cur_vars = s.core.cur_vars ∧
  s'.core.arena = s.core.arena ∧
  s'.core.arena_len = s.core.arena_len ∧
  s'.core.fuel = s.core.fuel ∧
  s'.core.oom = s.core.oom ∧
  s'.core.inconsistent = s.core.inconsistent ∧
  s'.scratch.tarjan_mark = s.scratch.tarjan_mark ∧
  s'.scratch.red_refs = s.scratch.red_refs ∧
  s'.scratch.scratch_buf = s.scratch.scratch_buf ∧
  s'.scratch.work_stk1 = s.scratch.work_stk1 ∧
  s'.scratch.work_stk2 = s.scratch.work_stk2 ∧
  s'.scratch.sim_sig = s.scratch.sim_sig

private theorem flushStatePres_refl (s : FullState) : FlushStatePres s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem flushStatePres_trans {s1 s2 s3 : FullState}
    (h12 : FlushStatePres s1 s2) (h23 : FlushStatePres s2 s3) : FlushStatePres s1 s3 :=
  ⟨h23.1.trans h12.1, h23.2.1.trans h12.2.1, h23.2.2.1.trans h12.2.2.1,
   h23.2.2.2.1.trans h12.2.2.2.1, h23.2.2.2.2.1.trans h12.2.2.2.2.1,
   h23.2.2.2.2.2.1.trans h12.2.2.2.2.2.1, h23.2.2.2.2.2.2.1.trans h12.2.2.2.2.2.2.1,
   h23.2.2.2.2.2.2.2.1.trans h12.2.2.2.2.2.2.2.1,
   h23.2.2.2.2.2.2.2.2.1.trans h12.2.2.2.2.2.2.2.2.1,
   h23.2.2.2.2.2.2.2.2.2.1.trans h12.2.2.2.2.2.2.2.2.2.1,
   h23.2.2.2.2.2.2.2.2.2.2.1.trans h12.2.2.2.2.2.2.2.2.2.2.1,
   h23.2.2.2.2.2.2.2.2.2.2.2.trans h12.2.2.2.2.2.2.2.2.2.2.2⟩

/-- Parametric `Func.wp` proof for `full_fwd_flush_large_m6`. -/
theorem full_fwd_flush_large_m6_wp (Γ : Env)
    (hDefrag : ∀ a m Q X, fullWstackDefragSpec a m Q X →
      Γ "full_wstack_defrag" [i64] [] a m Q X) :
    ∀ a m Q X, fullFwdFlushLargeM6Spec a m Q X →
      Func.wp Γ full_fwd_flush_large_m6_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m0 Q X ⟨c, F0, F_cur, s0, R, rfl, hdw0, hm0, hQ⟩
  have hmx := c.hmaxv; have hwc := c.hwcap
  unfold dimacsBound at hmx hwc
  have hcv_le := hdw0.1.core_ok.cur_vars_le
  have hnl_eq : (BitVec.ofNat 64 s0.core.cur_vars <<< (1 : Nat)).toNat = 2 * s0.core.cur_vars := by
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]; omega
  have hret : ∀ s1 m1, FullDenseInvW c F0 F_cur s1 → FlushStatePres s0 s1 →
      (FullMem c s1 ⋆ R) m1 → Q () m1 :=
    fun s1 m1 hdw1 hp hm1 => hQ s1 m1 hdw1 hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2.1
      hp.2.2.2.2.2.1 hp.2.2.2.2.2.2.1 hp.2.2.2.2.2.2.2.1 hp.2.2.2.2.2.2.2.2.1
      hp.2.2.2.2.2.2.2.2.2.1 hp.2.2.2.2.2.2.2.2.2.2.1 hp.2.2.2.2.2.2.2.2.2.2.2 hm1
  unfold Func.wp full_fwd_flush_large_m6_body
  c0_hsteps_nogrp
  refine wp_loop_group (ts := [i64])
    (fun rem (l, ()) ml => ∃ sl : FullState,
      l.toNat ≤ 2 * s0.core.cur_vars ∧ rem = 2 * s0.core.cur_vars - l.toNat ∧
      FullDenseInvW c F0 F_cur sl ∧ FlushStatePres s0 sl ∧ (FullMem c sl ⋆ R) ml)
    ?_ ?_
  · rintro L rem ⟨l, ⟨⟩⟩ ml hL ⟨sl, hl_le, rfl, hdwl, hpl, hml⟩
    have hl_nl_lt : ∀ h : l.toNat < (2 * (s0.core.cur_vars % 2 ^ 64)) % 2 ^ 64,
        l.toNat < 2 * sl.core.cur_vars := fun h => by
      rw [hpl.1]; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h; exact h
    c0_hsplit
    · have hl_lt : l.toNat < 2 * sl.core.cur_vars := hl_nl_lt hc
      have hdw_sl := m6_denseWatchesInv_of_w hdwl
      have hbd_l := hdw_sl.layout.bounds l.toNat hl_lt
      have hwlen_le := hdwl.1.core_ok.wlen_le
      have hlv0 : (l <<< (1 : Nat)).toNat < sl.core.wvec.length := by
        rw [hdwl.1.core_ok.wvec_len]; have := hdwl.1.core_ok.cur_vars_le; c0_bound
      have hlv1 : (l <<< (1 : Nat) + 1#64).toNat < sl.core.wvec.length := by
        rw [hdwl.1.core_ok.wvec_len]; have := hdwl.1.core_ok.cur_vars_le; c0_bound
      have hl1 : (l + 1#64).toNat = l.toNat + 1 := by c0_bound
      c0_hsteps_nogrp
      let off_l := (sl.core.wvec[(l <<< (1 : Nat)).toNat]'hlv0).setWidth 64
      let sz_l := (sl.core.wvec[(l <<< (1 : Nat) + 1#64).toNat]'hlv1).setWidth 64
      have hoff_eq : off_l.toNat = fullWatchOffCore sl.core l.toNat := by
        unfold off_l fullWatchOffCore
        rw [List.getElem?_eq_getElem (by rw [hdwl.1.core_ok.wvec_len]; omega), Option.getD_some,
          m6_zext32_toNat]
        exact congrArg BitVec.toNat (m6_getElem_congr (by c0_bound) _ _)
      have hsz_eq : sz_l.toNat = fullWatchSizeCore sl.core l.toNat := by
        unfold sz_l fullWatchSizeCore
        rw [List.getElem?_eq_getElem (by rw [hdwl.1.core_ok.wvec_len]; omega), Option.getD_some,
          m6_zext32_toNat]
        exact congrArg BitVec.toNat (m6_getElem_congr (by c0_bound) _ _)
      refine wp_join0 (P := fun mj => ∃ sj : FullState,
          FullDenseInvW c F0 F_cur sj ∧ FlushStatePres s0 sj ∧ (FullMem c sj ⋆ R) mj)
        (fun _ mj ⟨sj, hdwj, hpj, hmj⟩ => by
          c0_hsteps!
          exact hL (2 * s0.core.cur_vars - (l + 1#64).toNat) (l + 1#64, ()) mj (by omega)
            ⟨sj, by omega, rfl, hdwj, hpj, hmj⟩)
        (fun J hJ => by
          c0_hsplit
          · let end_l := off_l + sz_l
            have hend_eq : end_l.toNat = off_l.toNat + sz_l.toNat := by
              dsimp only [end_l]; rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
            have hsum_c0 :
                ((sl.core.wvec[2 * l.toNat % 2 ^ 64]'(by
                    rw [hdwl.1.core_ok.wvec_len]; omega)).toNat +
                  (sl.core.wvec[(2 * l.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
                    rw [hdwl.1.core_ok.wvec_len]; simp; omega)).toNat) % 2 ^ 64 = end_l.toNat := by
              have h1 : (sl.core.wvec[2 * l.toNat % 2 ^ 64]'(by
                  rw [hdwl.1.core_ok.wvec_len]; omega)).toNat = off_l.toNat := by
                rw [hoff_eq]; unfold fullWatchOffCore
                rw [List.getElem?_eq_getElem (by rw [hdwl.1.core_ok.wvec_len]; omega),
                  Option.getD_some]
                exact congrArg BitVec.toNat (m6_getElem_congr (by omega) _ _)
              have h2 : (sl.core.wvec[(2 * l.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
                  rw [hdwl.1.core_ok.wvec_len]; simp; omega)).toNat = sz_l.toNat := by
                rw [hsz_eq]; unfold fullWatchSizeCore
                rw [List.getElem?_eq_getElem (by rw [hdwl.1.core_ok.wvec_len]; omega),
                  Option.getD_some]
                exact congrArg BitVec.toNat (m6_getElem_congr (by simp; omega) _ _)
              rw [h1, h2, Nat.mod_eq_of_lt (by omega), hend_eq]
            c0_hsteps_nogrp
            -- Inner loop 1: compact binary watches into `[off_l ..< q)`
            refine wp_loop_group (ts := [i64, i64])
              (fun rem1 (p, q, ()) m1 => ∃ wstk1 : List (BitVec 32),
                let sp : FullState := { sl with core := { sl.core with wstk := wstk1 } }
                wstk1.length = c.wcap ∧
                off_l.toNat ≤ q.toNat ∧ q.toNat ≤ p.toNat ∧ p.toNat ≤ end_l.toNat ∧
                rem1 = end_l.toNat - p.toNat ∧
                (∀ idx, idx < off_l.toNat ∨ end_l.toNat ≤ idx →
                  wstk1[idx]? = sl.core.wstk[idx]?) ∧
                DenseWatchSliceOk F_cur sp.core l.toNat off_l.toNat (q.toNat - off_l.toNat) ∧
                DenseWatchSliceOk F_cur sp.core l.toNat p.toNat rem1 ∧
                (FullMem c sp ⋆ R) m1)
              ?_ ?_
            · rintro Lp rem1 ⟨p, q, ⟨⟩⟩ m1 hLp
                ⟨wstk1, hwl1, hq_ge, hq_le, hp_le, hrem1, hout1, hpref1, hsuf1, hm1⟩
              let sp : FullState := { sl with core := { sl.core with wstk := wstk1 } }
              c0_hsplit
              · have hp_lt : p.toNat < end_l.toNat := by rw [hsum_c0] at hc; exact hc
                have hpw : p.toNat < wstk1.length := by omega
                have hqw : q.toNat < wstk1.length := by omega
                have hp1_nat : (p + 1#64).toNat = p.toNat + 1 := by c0_bound
                have hq1_nat : (q + 1#64).toNat = q.toNat + 1 := by c0_bound
                cases hsuf1 with
                | empty => omega
                | @bin _ r1 w0 hwp hflag hne hot_lt hent_b hrest =>
                  have hw0_eq : wstk1[p.toNat]'hpw = w0 := by
                    rw [List.getElem?_eq_getElem hpw] at hwp; exact Option.some.inj hwp
                  c0_hsteps_nogrp
                  refine wp_join_state (ts := [i64, i64])
                    (α := BitVec 64 × BitVec 64 × List (BitVec 32))
                    (fun x => (x.1, x.2.1, ()))
                    (fun x mj =>
                      let sj : FullState := { sl with core := { sl.core with wstk := x.2.2 } }
                      x.2.2.length = c.wcap ∧ off_l.toNat ≤ x.2.1.toNat ∧
                      x.2.1.toNat ≤ x.1.toNat ∧ x.1.toNat ≤ end_l.toNat ∧
                      end_l.toNat - x.1.toNat < end_l.toNat - p.toNat ∧
                      (∀ idx, idx < off_l.toNat ∨ end_l.toNat ≤ idx →
                        x.2.2[idx]? = sl.core.wstk[idx]?) ∧
                      DenseWatchSliceOk F_cur sj.core l.toNat off_l.toNat
                        (x.2.1.toNat - off_l.toNat) ∧
                      DenseWatchSliceOk F_cur sj.core l.toNat x.1.toNat
                        (end_l.toNat - x.1.toNat) ∧
                      (FullMem c sj ⋆ R) mj)
                    (fun _ ⟨pj, qj, wj⟩ mj ⟨hwlj, hqgj, hqlj, hplj, hltj, houtj, hpj, hsj, hmj⟩ =>
                      by
                        c0_hsteps!
                        dsimp only at hltj
                        exact hLp (end_l.toNat - pj.toNat) (pj, qj, ()) mj (by omega)
                          ⟨wj, hwlj, hqgj, hqlj, hplj, rfl, houtj, hpj, hsj, hmj⟩)
                    (fun Jb hJb => by
                      c0_hsplit
                      · c0_hsteps!
                        let wstk2 := wstk1.set q.toNat (wstk1[p.toNat]'hpw)
                        let sp2 : FullState := { sl with core := { sl.core with wstk := wstk2 } }
                        have hpref2 : DenseWatchSliceOk F_cur sp2.core l.toNat off_l.toNat
                            ((q + 1#64).toNat - off_l.toNat) := by
                          rw [hq1_nat, show q.toNat + 1 - off_l.toNat =
                            (q.toNat - off_l.toNat) + 1 by omega]
                          exact m6_denseWatchSliceOk_append_bin (k := sp.core) (k' := sp2.core)
                            (Nat.le_refl _) (fun _ hr => hr)
                            (fun i hi => by
                              dsimp only [sp2, sp, wstk2]; exact List.getElem?_set_ne (by omega))
                            hpref1
                            (by
                              dsimp only [sp2, wstk2]
                              rw [show off_l.toNat + (q.toNat - off_l.toNat) = q.toNat by omega,
                                hw0_eq]
                              exact List.getElem?_set_self hqw)
                            hflag hne hot_lt hent_b
                        have hent_r : (cnfOfClauses F_cur).Entails (cnfOfClauses F_cur) := by
                          rw [CNF.entails_def]; exact fun _ hx => hx
                        have hsuf2 : DenseWatchSliceOk F_cur sp2.core l.toNat (p + 1#64).toNat
                            (end_l.toNat - (p + 1#64).toNat) := by
                          rw [show end_l.toNat - (p + 1#64).toNat = r1 by omega, hp1_nat]
                          exact hrest.mono (k := sp.core) (k' := sp2.core) hent_r (Nat.le_refl _)
                            (fun _ hr => hr) fun idx hi1 _ => by
                              dsimp only [sp2, sp, wstk2]; exact List.getElem?_set_ne (by omega)
                        exact hJb (p + 1#64, q + 1#64, wstk2) m
                          ⟨by simp [wstk2, hwl1], by dsimp only; omega, by dsimp only; omega,
                           by dsimp only; omega, by dsimp only; omega,
                           fun idx hidx => by
                             dsimp only [wstk2]; rw [List.getElem?_set_ne (by omega)]
                             exact hout1 idx hidx,
                           hpref2, hsuf2, hm⟩
                      · rw [hw0_eq] at hc; exact absurd hc hflag)
                | @occ _ r2 w0 cr hwp _ hflag _ _ _ hrest =>
                  have hw0_eq : wstk1[p.toNat]'hpw = w0 := by
                    rw [List.getElem?_eq_getElem hpw] at hwp; exact Option.some.inj hwp
                  have hp2_nat : (p + 1#64 + 1#64).toNat = p.toNat + 2 := by c0_bound
                  c0_hsteps_nogrp
                  refine wp_join_state (ts := [i64, i64])
                    (α := BitVec 64 × BitVec 64 × List (BitVec 32))
                    (fun x => (x.1, x.2.1, ()))
                    (fun x mj =>
                      let sj : FullState := { sl with core := { sl.core with wstk := x.2.2 } }
                      x.2.2.length = c.wcap ∧ off_l.toNat ≤ x.2.1.toNat ∧
                      x.2.1.toNat ≤ x.1.toNat ∧ x.1.toNat ≤ end_l.toNat ∧
                      end_l.toNat - x.1.toNat < end_l.toNat - p.toNat ∧
                      (∀ idx, idx < off_l.toNat ∨ end_l.toNat ≤ idx →
                        x.2.2[idx]? = sl.core.wstk[idx]?) ∧
                      DenseWatchSliceOk F_cur sj.core l.toNat off_l.toNat
                        (x.2.1.toNat - off_l.toNat) ∧
                      DenseWatchSliceOk F_cur sj.core l.toNat x.1.toNat
                        (end_l.toNat - x.1.toNat) ∧
                      (FullMem c sj ⋆ R) mj)
                    (fun _ ⟨pj, qj, wj⟩ mj ⟨hwlj, hqgj, hqlj, hplj, hltj, houtj, hpj, hsj, hmj⟩ =>
                      by
                        c0_hsteps!
                        dsimp only at hltj
                        exact hLp (end_l.toNat - pj.toNat) (pj, qj, ()) mj (by omega)
                          ⟨wj, hwlj, hqgj, hqlj, hplj, rfl, houtj, hpj, hsj, hmj⟩)
                    (fun Jb hJb => by
                      c0_hsplit
                      · rw [hw0_eq] at hc; exact absurd hflag hc
                      · c0_hsteps_nogrp
                        refine wp_join_state_pure (ts := [i64]) (α := BitVec 64) (fun x => (x, ()))
                          (fun x => x = p + 1#64 + 1#64)
                          (fun _ px hpx => by
                            subst hpx; c0_hsteps!
                            exact hJb (p + 1#64 + 1#64, q, wstk1) m1
                              ⟨hwl1, hq_ge, by dsimp only; omega, by dsimp only; omega,
                               by dsimp only; omega, hout1, hpref1,
                               by dsimp only
                                  rw [show end_l.toNat - (p + 1#64 + 1#64).toNat = r2 by omega,
                                   hp2_nat]; exact hrest, hm1⟩)
                          (fun Jp hJp => by
                            c0_hsplit
                            · c0_hsteps!; exact hJp (p + 1#64 + 1#64) rfl
                            · rw [hsum_c0] at hc; simp at hc; omega))
              · -- Inner loop 2: fill `[q ..< end_l)` with `0xFFFFFFFFu`
                c0_hsteps_nogrp
                refine wp_loop_group (ts := [i64])
                  (fun rem2 (cc, ()) m2 => ∃ wstk2 : List (BitVec 32),
                    let sc : FullState := { sl with core := { sl.core with wstk := wstk2 } }
                    wstk2.length = c.wcap ∧
                    q.toNat ≤ cc.toNat ∧ cc.toNat ≤ end_l.toNat ∧
                    rem2 = end_l.toNat - cc.toNat ∧
                    (∀ idx, idx < off_l.toNat ∨ end_l.toNat ≤ idx →
                      wstk2[idx]? = sl.core.wstk[idx]?) ∧
                    DenseWatchSliceOk F_cur sc.core l.toNat off_l.toNat (q.toNat - off_l.toNat) ∧
                    (FullMem c sc ⋆ R) m2)
                  ?_ ?_
                · rintro Lc rem2 ⟨cc, ⟨⟩⟩ m2 hLc
                    ⟨wstk2, hwl2, hc_ge, hc_le, hrem2, hout2, hpref2, hm2⟩
                  let sc : FullState := { sl with core := { sl.core with wstk := wstk2 } }
                  c0_hsplit
                  · have hc_lt : cc.toNat < end_l.toNat := by rw [hsum_c0] at hc; exact hc
                    have hcw : cc.toNat < wstk2.length := by omega
                    have hc1_nat : (cc + 1#64).toNat = cc.toNat + 1 := by c0_bound
                    c0_hsteps!
                    let wstk3 := wstk2.set cc.toNat 0xFFFFFFFF#32
                    let sc3 : FullState := { sl with core := { sl.core with wstk := wstk3 } }
                    have hent_r : (cnfOfClauses F_cur).Entails (cnfOfClauses F_cur) := by
                      rw [CNF.entails_def]; exact fun _ hx => hx
                    have hpref3 : DenseWatchSliceOk F_cur sc3.core l.toNat off_l.toNat
                        (q.toNat - off_l.toNat) :=
                      hpref2.mono (k := sc.core) (k' := sc3.core) hent_r (Nat.le_refl _)
                        (fun _ hr => hr) fun idx _ hi2 => by
                          dsimp only [sc3, sc, wstk3]; exact List.getElem?_set_ne (by omega)
                    exact hLc (end_l.toNat - (cc + 1#64).toNat) (cc + 1#64, ()) _ (by omega)
                      ⟨wstk3, by simp [wstk3, hwl2], by omega, by omega, rfl,
                       fun idx hidx => by
                         dsimp only [wstk3]; rw [List.getElem?_set_ne (by omega)]
                         exact hout2 idx hidx,
                       hpref3, hm⟩
                  · have hwv_idx : (l <<< (1 : Nat) + 1#64).toNat < sl.core.wvec.length := hlv1
                    have hwv_idx_eq : (l <<< (1 : Nat) + 1#64).toNat = 2 * l.toNat + 1 := by
                      c0_bound
                    c0_hsteps!
                    let nsz := q.toNat - off_l.toNat
                    have hq_sub : ((q - off_l).setWidth 32) = BitVec.ofNat 32 nsz := by
                      apply BitVec.eq_of_toNat_eq
                      rw [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat]
                      have hq_sub_eq : (2 ^ 64 - off_l.toNat + q.toNat) % 2 ^ 64 = nsz := by
                        dsimp only [nsz]; omega
                      rw [hq_sub_eq]
                    let wvec_f :=
                      sl.core.wvec.set (l <<< (1 : Nat) + 1#64).toNat ((q - off_l).setWidth 32)
                    let sf : FullState :=
                      { sc with
                        core := { sc.core with
                          wvec := wvec_f,
                          wusable := sc.core.wusable + (end_l - q) } }
                    have hsf_eq : sf =
                        { sl with
                          core := { sl.core with
                            wvec := sl.core.wvec.set (2 * l.toNat + 1) (BitVec.ofNat 32 nsz),
                            wstk := wstk2,
                            wusable := sl.core.wusable + (end_l - q) } } := by
                      dsimp only [sf, sc, wvec_f]
                      rw [hwv_idx_eq, hq_sub]
                    have hdwf : FullDenseInvW c F0 F_cur sf := by
                      rw [hsf_eq]
                      exact m6_denseInvW_of_shrink_watch hdwl hl_lt (nsz := nsz) (by omega) hwl2
                        (fun idx hidx => hout2 idx (by rw [hoff_eq, hsz_eq] at *; omega))
                        (by simpa only [hoff_eq, nsz] using hpref2)
                    exact hJ m ⟨sf, hdwf,
                      flushStatePres_trans hpl ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
                        rfl, rfl⟩, hm⟩
                · intro Lc hLc; c0_hsteps!
                  exact hLc (end_l.toNat - q.toNat) (q, ()) m1
                    ⟨wstk1, hwl1, Nat.le_refl _, by omega, rfl, hout1, hpref1, hm1⟩
            · intro Lp hLp; c0_hsteps!
              exact hLp sz_l.toNat (off_l, off_l, ()) ml
                ⟨sl.core.wstk, hdwl.1.core_ok.wstk_len_arr, Nat.le_refl _, Nat.le_refl _,
                 by omega, by omega, fun _ _ => rfl,
                 by rw [Nat.sub_self]; exact .empty,
                 by rw [hoff_eq, hsz_eq]; exact hdw_sl.slices l.toNat hl_lt, hml⟩
          · c0_hsteps!; exact hJ ml ⟨sl, hdwl, hpl, hml⟩)
    · -- Outer loop exit: check `wusable * 2 > wcap`
      c0_hsteps_nogrp
      refine wp_join0 (P := fun mf => ∃ sf : FullState,
        FullDenseInvW c F0 F_cur sf ∧ FlushStatePres s0 sf ∧ (FullMem c sf ⋆ R) mf)
        (fun _ mf ⟨sf, hdwf, hpf, hmf⟩ => by c0_hsteps!; exact hret sf mf hdwf hpf hmf)
        (fun Jd hJd => by
          c0_hsplit
          · c0_hsteps_nogrp
            m6_call hDefrag
            refine ⟨c, sl, R, rfl, hdwl.1, (m6_denseWatchesInv_of_w hdwl).layout, hml, ?_⟩
            intro wvec' wstk' wlen' wsort' m1 sd hlen_d hlay_d _ hslice_d hm1
            have hdw_d : FullDenseInvW c F0 F_cur sd :=
              m6_fullDenseInvW_of_wstackDefrag hdwl hlen_d hlay_d hslice_d
            c0_hsteps!
            exact hJd m1 ⟨sd, hdw_d,
              flushStatePres_trans hpl ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
                rfl, rfl⟩, hm1⟩
          · c0_hsteps!; exact hJd ml ⟨sl, hdwl, hpl, hml⟩)
  · intro L hL; c0_hsteps!
    exact hL (2 * s0.core.cur_vars) (0#64, ()) m0
      ⟨s0, Nat.zero_le _, by simp, hdw0, flushStatePres_refl s0, hm0⟩

/-! ## 2. `full_fwd_reconnect_irred_m6` -/

/-- Contract for `full_fwd_reconnect_irred_m6`: flushes large occurrences and reconnects all
unsatisfied irredundant large clauses into dense watch lists. -/
def fullFwdReconnectIrredM6Spec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ (FullMem c s ⋆ R) m ∧
    ∀ s' m',
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.arena_len = s.core.arena_len → s'.core.fuel = s.core.fuel →
      s'.core.inconsistent = s.core.inconsistent →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      (FullMem c s' ⋆ R) m' → Q () m'

theorem fullFwdReconnectIrredM6Spec_noExit :
    ∀ xs m Q X, fullFwdReconnectIrredM6Spec xs m Q X →
      fullFwdReconnectIrredM6Spec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem fullFwdReconnectIrredM6Spec_intro {h : BitVec 64} {m : Mem 64}
    {Q : Post []} {X : XPost} {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {R : Mem 64 → Prop} (hh : h = c.hdr) (hdw : FullDenseInvW c F0 F_cur s)
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ s' m',
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.arena_len = s.core.arena_len → s'.core.fuel = s.core.fuel →
      s'.core.inconsistent = s.core.inconsistent →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      (FullMem c s' ⋆ R) m' → Q () m') :
    fullFwdReconnectIrredM6Spec (h, ()) m Q X :=
  ⟨c, F0, F_cur, s, R, hh, hdw, hm, hQ⟩

/-- Parametric `Func.wp` proof for `full_fwd_reconnect_irred_m6`. -/
theorem full_fwd_reconnect_irred_m6_wp (Γ : Env)
    (hFlush : ∀ a m Q X, fullFwdFlushLargeM6Spec a m Q X →
      Γ "full_fwd_flush_large_m6" [i64] [] a m Q X)
    (hArenaNext : ∀ a m Q X, fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X)
    (hWatchPush : ∀ a m Q X, fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, fullFwdReconnectIrredM6Spec a m Q X →
      Func.wp Γ full_fwd_reconnect_irred_m6_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m0 Q X ⟨c, F0, F_cur, s0, R, rfl, hdw0, hm0, hQ⟩
  have hmx := c.hmaxv; have harc := c.harena; unfold dimacsBound at hmx harc
  unfold Func.wp full_fwd_reconnect_irred_m6_body
  c0_hsteps_nogrp
  m6_call hFlush
  refine fullFwdFlushLargeM6Spec_intro rfl hdw0 hm0 ?_
  intro s1 m1 hdw1 hcv1 _ hal1 hfl1 _ hinc1 htmk1 _ _ _ _ _ hm1
  c0_hsteps_nogrp
  refine wp_loop_group (ts := [i64])
    (fun rem (p, ()) mp => ∃ sp : FullState,
      p.toNat ≤ sp.core.arena_len ∧ rem = sp.core.arena_len - p.toNat ∧
      (p.toNat = sp.core.arena_len ∨ p.toNat ∈ fullArenaClauseRefs sp) ∧
      FullDenseInvW c F0 F_cur sp ∧ sp.core.cur_vars = s0.core.cur_vars ∧
      sp.core.arena_len = s0.core.arena_len ∧ sp.core.fuel = s0.core.fuel ∧
      sp.core.inconsistent = s0.core.inconsistent ∧
      sp.scratch.tarjan_mark = s0.scratch.tarjan_mark ∧
      (FullMem c sp ⋆ R) mp)
    ?_ ?_
  · rintro L rem ⟨p, ⟨⟩⟩ mp hL
      ⟨sp, hp_le, rfl, hp_mem, hdwp, hcvp, halp, hflp, hincp, htmkp, hmp⟩
    have hal_le := hdwp.1.core_ok.arena_len_le
    c0_hsplit
    · have hp_lt : p.toNat < sp.core.arena_len := by
        rw [Nat.mod_eq_of_lt (by omega)] at hc; exact hc
      c0_hsplit
      · have hp_ref : p.toNat ∈ fullArenaClauseRefs sp := hp_mem.resolve_left (by omega)
        have hwf_p := hdwp.2.1.arena.refs_wf p.toNat hp_ref
        have hp_ar : p.toNat < sp.core.arena.length := by
          rw [hdwp.1.core_ok.arena_len_arr]; omega
        have hp2_ar : (p + 2#64).toNat < sp.core.arena.length := by
          rw [hdwp.1.core_ok.arena_len_arr]; c0_bound
        have hp32 : (p.setWidth 32).toNat = p.toNat := by
          rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
        let hdr_p := sp.core.arena[p.toNat]'hp_ar
        let sz_p := sp.core.arena[(p + 2#64).toNat]'hp2_ar
        have hsz_eq : sz_p.toNat = fullArenaClauseSizeCore sp.core p.toNat := by
          unfold sz_p fullArenaClauseSizeCore
          rw [List.getElem?_eq_getElem (by rw [hdwp.1.core_ok.arena_len_arr]; omega),
            Option.getD_some]
          exact congrArg BitVec.toNat (m6_getElem_congr (by c0_bound) _ _)
        c0_hsteps_nogrp
        m6_call hArenaNext
        refine ⟨c, sp, R, rfl, hdwp.1, hmp, ?_⟩
        have hnb := fullArenaNextOff_bounds (ar := sp.core.arena) (alen := sp.core.arena_len)
          (cref := p.toNat) hwf_p.1
        have hnp_mem := fullArenaClauseRefs_next_mem hdwp.2.1.arena hp_ref
        let np := (BitVec.ofNat 32 (fullArenaNextOff sp.core.arena sp.core.arena_len
          (p.setWidth 32).toNat)).setWidth 64
        have hnp_toNat :
            np.toNat = fullArenaNextOff sp.core.arena sp.core.arena_len p.toNat := by
          dsimp only [np]; rw [hp32, m6_zext32_toNat, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (by omega)]
        c0_hsteps_nogrp
        refine wp_join0 (P := fun mj => ∃ sj : FullState,
            FullDenseInvW c F0 F_cur sj ∧ sj.core.cur_vars = s0.core.cur_vars ∧
            sj.core.arena_len = s0.core.arena_len ∧ sj.core.fuel = s0.core.fuel ∧
            sj.core.inconsistent = s0.core.inconsistent ∧
            sj.scratch.tarjan_mark = s0.scratch.tarjan_mark ∧
            fullArenaClauseRefs sj = fullArenaClauseRefs sp ∧
            (FullMem c sj ⋆ R) mj)
          (fun _ mj ⟨sj, hdwj, hcvj, halj, hflj, hincj, htmkj, hrefsj, hmj⟩ => by
            c0_hsteps!
            exact hL (sj.core.arena_len - np.toNat) (np, ()) mj (by omega)
              ⟨sj, by omega, rfl, by rw [hnp_toNat, halj, ← halp, hrefsj]; exact hnp_mem,
               hdwj, hcvj, halj, hflj, hincj, htmkj, hmj⟩)
          (fun Jp hJp => by
            c0_hsplit
            · have hng : fullArenaClauseGarb sp p.toNat = false := by
                unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
                rw [List.getElem?_eq_getElem hp_ar, Option.getD_some]
                rw [m6_and_garb_zero_of_mask hc]; rfl
              c0_hsplit
              · have hsz3 : 3 ≤ sz_p.toNat := hc
                c0_hsteps_nogrp
                refine wp_loop_break_group (brkTs := [.bool, i32]) (lpTs := [i32])
                  (fun (sat_b, _kb, ()) ms => ms = mp)
                  (fun rem_k (k, ()) mk => k.toNat ≤ sz_p.toNat ∧
                    rem_k = sz_p.toNat - k.toNat ∧ mk = mp)
                  ?_ ?_ ?_
                · rintro _ ⟨sat_b, _kb, ⟨⟩⟩ ms hm_s
                  subst ms
                  c0_hsteps_nogrp
                  refine wp_join_state (ts := [i32]) (α := BitVec 32 × FullState)
                    (fun x => (x.1, ()))
                    (fun x mj =>
                      FullDenseInvW c F0 F_cur x.2 ∧ x.2.core.cur_vars = s0.core.cur_vars ∧
                      x.2.core.arena_len = s0.core.arena_len ∧ x.2.core.fuel = s0.core.fuel ∧
                      x.2.core.inconsistent = s0.core.inconsistent ∧
                      x.2.scratch.tarjan_mark = s0.scratch.tarjan_mark ∧
                      fullArenaClauseRefs x.2 = fullArenaClauseRefs sp ∧ (FullMem c x.2 ⋆ R) mj)
                    (fun _ ⟨_, sj⟩ mj h => by c0_hsteps!; exact hJp mj ⟨sj, h⟩)
                    (fun J31 hJ31 => by
                      c0_hsplit
                      · have hhdr_eq : hdr_p = fullArenaHdr sp p.toNat := by
                          unfold hdr_p fullArenaHdr fullArenaHdrCore
                          rw [List.getElem?_eq_getElem hp_ar, Option.getD_some]
                        c0_hsteps!
                        let ag' := sp.core.arena_garbage + 3#64 + sz_p.setWidth 64
                        let ar' := sp.core.arena.set p.toNat (hdr_p ||| 0x00080000#32)
                        let smg : FullState :=
                          { sp with core := { sp.core with arena := ar', arena_garbage := ag' } }
                        have hmg := m6_fullDenseInvW_markGarb hdwp hp_ref (arena' := ar')
                          (ag' := ag') (by simp [ar', hdwp.1.core_ok.arena_len_arr])
                          (Or.inl (by
                            dsimp only [ar']; rw [hhdr_eq]; exact List.getElem?_set_self hp_ar))
                          (fun i hne _ => by dsimp only [ar']; exact List.getElem?_set_ne hne.symm)
                        exact hJ31 (_, smg) _ ⟨hmg.1, hcvp, halp, hflp, hincp, htmkp, hmg.2, hm⟩
                      · c0_hsteps_nogrp
                        refine wp_join_state (ts := [i32]) (α := BitVec 32 × FullState)
                          (fun x => (x.1, ()))
                          (fun x mw =>
                            FullDenseInvW c F0 F_cur x.2 ∧ x.2.core.cur_vars = s0.core.cur_vars ∧
                            x.2.core.arena_len = s0.core.arena_len ∧ x.2.core.fuel = s0.core.fuel ∧
                            x.2.core.inconsistent = s0.core.inconsistent ∧
                            x.2.scratch.tarjan_mark = s0.scratch.tarjan_mark ∧
                            fullArenaClauseRefs x.2 = fullArenaClauseRefs sp ∧
                            (FullMem c x.2 ⋆ R) mw)
                          (fun _ x mw h => by c0_hsteps!; exact hJ31 x mw h)
                          (fun J32 hJ32 => by
                            c0_hsteps_nogrp
                            refine wp_loop_group (ts := [i32])
                              (fun rem_w (k, ()) mw => ∃ sw : FullState,
                                k.toNat ≤ sz_p.toNat ∧ rem_w = sz_p.toNat - k.toNat ∧
                                FullDenseInvW c F0 F_cur sw ∧
                                sw.core.cur_vars = s0.core.cur_vars ∧
                                sw.core.arena = sp.core.arena ∧
                                sw.core.arena_len = s0.core.arena_len ∧
                                sw.core.fuel = s0.core.fuel ∧
                                sw.core.inconsistent = s0.core.inconsistent ∧
                                sw.scratch.tarjan_mark = s0.scratch.tarjan_mark ∧
                                (FullMem c sw ⋆ R) mw)
                              ?_ ?_
                            · rintro Lw rem_w ⟨k, ⟨⟩⟩ mw hLw
                                ⟨sw, hk_le, rfl, hdww, hcvw, harw, halw, hflw, hincw, htmkw, hmw⟩
                              have hrefsw : fullArenaClauseRefs sw = fullArenaClauseRefs sp := by
                                unfold fullArenaClauseRefs fullArenaClauseRefsCore
                                rw [harw, halw, halp]
                              c0_hsplit
                              · have hk_lt : k.toNat < sz_p.toNat := hc
                                have hpi_ar : (p + 3#64 + k.setWidth 64).toNat <
                                    sw.core.arena.length := by
                                  rw [hdww.1.core_ok.arena_len_arr]; c0_bound
                                have hsz_lt31 : sz_p.toNat < 2 ^ 31 := by omega
                                have hsz_mask : (sz_p &&& 0x7FFFFFFF#32) = sz_p :=
                                  m6_sz_and_mask_eq hsz_lt31
                                have hk1 : (k + 1#32).toNat = k.toNat + 1 := by c0_bound
                                c0_hsteps_nogrp
                                m6_call hWatchPush
                                refine ⟨c, sw, R, rfl, hdww.1,
                                  (m6_denseWatchesInv_of_w hdww).layout, fun h => by simp at h,
                                  fun _ => by
                                    dsimp only [Arg.val]
                                    refine ⟨?_, m6_bv32_ne_sent_of_lt (by rw [hp32]; omega)⟩
                                    rw [show (sp.core.arena[(p + 2).toNat]'hp2_ar &&&
                                        2147483647 : BitVec 32) = sz_p &&& 0x7FFFFFFF#32 from rfl,
                                      hsz_mask]
                                    exact m6_bv32_ne_sent_of_lt hsz_lt31,
                                  hmw, ?_⟩
                                intro ok wvec' wstk' wlen' wu' wsort' m2 s2 hlen2 hlay2 hoth2 hokt
                                  hokf hm2
                                have hdw2 : FullDenseInvW c F0 F_cur s2 :=
                                  m6_fullDenseInvW_of_watchPush_occ hdww hlen2 hlay2
                                    m6_sz_and_mask_no_bin (by rw [hsz_mask]; omega)
                                    (by rw [hp32]; omega) (by rw [hp32, hrefsw]; exact hp_ref)
                                    hoth2
                                    (fun ht => by
                                      obtain ⟨h1, _, h3, h4, h5, h6⟩ := hokt ht
                                      exact ⟨h1, h3, h4, h5, h6 rfl⟩)
                                    (fun hf => (hokf hf).1)
                                c0_hsplit
                                · c0_hsteps!
                                  exact hLw (sz_p.toNat - (k + 1#32).toNat) (k + 1#32, ()) m2
                                    (by omega) ⟨s2, by omega, rfl, hdw2, hcvw, harw, halw, hflw,
                                      hincw, htmkw, hm2⟩
                                · c0_hsteps!
                                  let soom : FullState :=
                                    { s2 with core := { s2.core with oom := 1#64 } }
                                  exact hJ32 (_, soom) _
                                    ⟨m6_fullDenseInvW_with_oom hdw2 1#64, hcvw, halw, hflw,
                                     hincw, htmkw, hrefsw, hm⟩
                              · c0_hsteps!
                                exact hJ32 (_, sw) mw
                                  ⟨hdww, hcvw, halw, hflw, hincw, htmkw, hrefsw, hmw⟩
                            · intro Lw hLw; c0_hsteps!
                              exact hLw sz_p.toNat (0#32, ()) mp
                                ⟨sp, Nat.zero_le _, by simp, hdwp, hcvp, rfl, halp, hflp, hincp,
                                 htmkp, hmp⟩))
                · rintro Bk Lk rem_k ⟨k, ⟨⟩⟩ mk hBk hLk ⟨hk_le, rfl, hmk_eq⟩
                  subst mk
                  c0_hsplit
                  · have hk_lt : k.toNat < sz_p.toNat := hc
                    have hpi_ar : (p + 3#64 + k.setWidth 64).toNat < sp.core.arena.length := by
                      rw [hdwp.1.core_ok.arena_len_arr]; c0_bound
                    have hcl_lt : (sp.core.arena[(p + 3#64 + k.setWidth 64).toNat]'
                        hpi_ar).toNat < 2 * sp.core.cur_vars := by
                      have hmem : (sp.core.arena[(p + 3#64 + k.setWidth 64).toNat]'
                          hpi_ar).toNat ∈ fullArenaClauseLitsCore sp.core p.toNat := by
                        rw [mem_fullArenaClauseLitsCore_iff (by
                          rw [hdwp.1.core_ok.arena_len_arr]; omega)]
                        exact ⟨k.toNat, by omega, congrArg BitVec.toNat
                          (m6_getElem_congr (by c0_bound) _ _)⟩
                      exact hdwp.2.1.arena.lits_lt p.toNat hp_ref hng _ hmem
                    have hcl_v : ((sp.core.arena[(p + 3#64 + k.setWidth 64).toNat]'
                        hpi_ar).setWidth 64).toNat < sp.core.vals.length := by
                      rw [hdwp.1.core_ok.vals_len]; have := hdwp.1.core_ok.cur_vars_le; c0_bound
                    c0_hsplit
                    · c0_hsteps!; exact hBk (true, k, ()) mp rfl
                    · c0_hsteps!
                      have hk1 : (k + 1#32).toNat = k.toNat + 1 := by c0_bound
                      exact hLk (sz_p.toNat - (k + 1#32).toNat) (k + 1#32, ()) mp (by omega)
                        ⟨by omega, rfl, rfl⟩
                  · c0_hsteps!; exact hBk (false, k, ()) mp rfl
                · intro _ Lk _ hLk; c0_hsteps!
                  exact hLk sz_p.toNat (0#32, ()) mp ⟨Nat.zero_le _, by simp, rfl⟩
              · c0_hsteps!
                exact hJp mp ⟨sp, hdwp, hcvp, halp, hflp, hincp, htmkp, rfl, hmp⟩
            · c0_hsteps!
              exact hJp mp ⟨sp, hdwp, hcvp, halp, hflp, hincp, htmkp, rfl, hmp⟩)
      · c0_hsteps!; exact hQ sp mp hdwp hcvp halp hflp hincp htmkp hmp
    · c0_hsteps!; exact hQ sp mp hdwp hcvp halp hflp hincp htmkp hmp
  · intro L hL; c0_hsteps!
    exact hL s1.core.arena_len (0#64, ()) m1
      ⟨s1, Nat.zero_le _, by simp, by
        by_cases hz : s1.core.arena_len = 0
        · exact Or.inl hz.symm
        · exact Or.inr (m6_zero_mem_arenaRefs hdw1.2.1.arena (Nat.pos_of_ne_zero hz)),
       hdw1, hcv1, hal1, hfl1, hinc1, htmk1, hm1⟩

/-! ## 3. `full_fwd_connect_subsumer_m6` -/

/-- Contract for `full_fwd_connect_subsumer_m6`: attaches at most one min-occ (`<= 1000`) watch
for live irredundant large clause `cref`. -/
def fullFwdConnectSubsumerM6Spec : Spec [i64, i32] [] := fun (h, cref, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ cref.toNat ∈ fullArenaClauseRefs s ∧
    (FullMem c s ⋆ R) m ∧
    ∀ s' m',
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.arena = s.core.arena → s'.core.arena_len = s.core.arena_len →
      s'.core.fuel = s.core.fuel → s'.core.inconsistent = s.core.inconsistent →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.red_refs = s.scratch.red_refs →
      (FullMem c s' ⋆ R) m' → Q () m'

theorem fullFwdConnectSubsumerM6Spec_noExit :
    ∀ xs m Q X, fullFwdConnectSubsumerM6Spec xs m Q X →
      fullFwdConnectSubsumerM6Spec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem fullFwdConnectSubsumerM6Spec_intro {h : BitVec 64} {cref : BitVec 32} {m : Mem 64}
    {Q : Post []} {X : XPost} {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {R : Mem 64 → Prop} (hh : h = c.hdr) (hdw : FullDenseInvW c F0 F_cur s)
    (href : cref.toNat ∈ fullArenaClauseRefs s) (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ s' m',
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.arena = s.core.arena → s'.core.arena_len = s.core.arena_len →
      s'.core.fuel = s.core.fuel → s'.core.inconsistent = s.core.inconsistent →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.red_refs = s.scratch.red_refs →
      (FullMem c s' ⋆ R) m' → Q () m') :
    fullFwdConnectSubsumerM6Spec (h, cref, ()) m Q X :=
  ⟨c, F0, F_cur, s, R, hh, hdw, href, hm, hQ⟩

/-- Parametric `Func.wp` proof for `full_fwd_connect_subsumer_m6`. -/
theorem full_fwd_connect_subsumer_m6_wp (Γ : Env)
    (hWatchPush : ∀ a m Q X, fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, fullFwdConnectSubsumerM6Spec a m Q X →
      Func.wp Γ full_fwd_connect_subsumer_m6_body a m Q X := by
  rintro ⟨h, cref, ⟨⟩⟩ m0 Q X ⟨c, F0, F_cur, s0, R, rfl, hdw0, href, hm0, hQ⟩
  have hmx := c.hmaxv; have harc := c.harena; unfold dimacsBound at hmx harc
  have hwf := hdw0.2.1.arena.refs_wf cref.toNat href
  have hal_le := hdw0.1.core_ok.arena_len_le
  have hcr_ar : (cref.setWidth 64).toNat < s0.core.arena.length := by
    rw [hdw0.1.core_ok.arena_len_arr, m6_zext32_toNat]; omega
  have hcr2_ar : (cref.setWidth 64 + 2#64).toNat < s0.core.arena.length := by
    rw [hdw0.1.core_ok.arena_len_arr]; c0_bound
  let hdr := s0.core.arena[(cref.setWidth 64).toNat]'hcr_ar
  let sz := s0.core.arena[(cref.setWidth 64 + 2#64).toNat]'hcr2_ar
  have hsz_eq : sz.toNat = fullArenaClauseSizeCore s0.core cref.toNat := by
    unfold sz fullArenaClauseSizeCore
    rw [List.getElem?_eq_getElem (by rw [hdw0.1.core_ok.arena_len_arr]; omega), Option.getD_some]
    exact congrArg BitVec.toNat (m6_getElem_congr (by c0_bound) _ _)
  unfold Func.wp full_fwd_connect_subsumer_m6_body
  c0_hsplit
  · c0_hsteps!; exact hQ s0 m0 hdw0 rfl rfl rfl rfl rfl rfl rfl hm0
  · have hng : fullArenaClauseGarb s0 cref.toNat = false := by
      unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
      rw [List.getElem?_eq_getElem (by rw [hdw0.1.core_ok.arena_len_arr]; omega), Option.getD_some]
      have hget : s0.core.arena[cref.toNat]'(by rw [hdw0.1.core_ok.arena_len_arr]; omega) = hdr :=
        m6_getElem_congr (m6_zext32_toNat cref).symm _ _
      rw [hget]
      rw [hget] at hc
      rw [m6_and_garb_zero_of_mask hc]; rfl
    c0_hsplit
    · c0_hsteps!; exact hQ s0 m0 hdw0 rfl rfl rfl rfl rfl rfl rfl hm0
    · have hsz3 : 3 ≤ sz.toNat := by omega
      have hcr3_ar : (cref.setWidth 64 + 3#64).toNat < s0.core.arena.length := by
        rw [hdw0.1.core_ok.arena_len_arr]; c0_bound
      have hl0_lt : (s0.core.arena[(cref.setWidth 64 + 3#64).toNat]'hcr3_ar).toNat <
          2 * s0.core.cur_vars := by
        have hmem : (s0.core.arena[(cref.setWidth 64 + 3#64).toNat]'hcr3_ar).toNat ∈
            fullArenaClauseLitsCore s0.core cref.toNat := by
          rw [mem_fullArenaClauseLitsCore_iff (by rw [hdw0.1.core_ok.arena_len_arr]; omega)]
          exact ⟨0, by omega, congrArg BitVec.toNat (m6_getElem_congr (by c0_bound) _ _)⟩
        exact hdw0.2.1.arena.lits_lt cref.toNat href hng _ hmem
      c0_hsteps_nogrp
      -- Loop 1: pick min-occ `FL_SUBSUME` lit
      refine wp_loop_group (ts := [i32, i32, i32])
        (fun rem1 (best_l, best_d, i, ()) m1 =>
          m1 = m0 ∧ i.toNat ≤ sz.toNat ∧ rem1 = sz.toNat - i.toNat ∧
          best_l.toNat < 2 * s0.core.cur_vars)
        ?_ ?_
      · rintro L1 rem1 ⟨best_l, best_d, i, ⟨⟩⟩ m1 hL1 ⟨rfl, hi_le, rfl, hbl_lt⟩
        c0_hsplit
        · have hi_lt : i.toNat < sz.toNat := hc
          have hcri : (cref.setWidth 64 + 3#64 + i.setWidth 64).toNat < s0.core.arena.length := by
            rw [hdw0.1.core_ok.arena_len_arr]; c0_bound
          have hl_lt : (s0.core.arena[(cref.setWidth 64 + 3#64 + i.setWidth 64).toNat]'hcri).toNat <
              2 * s0.core.cur_vars := by
            have hmem :
                (s0.core.arena[(cref.setWidth 64 + 3#64 + i.setWidth 64).toNat]'hcri).toNat ∈
                  fullArenaClauseLitsCore s0.core cref.toNat := by
              rw [mem_fullArenaClauseLitsCore_iff (by rw [hdw0.1.core_ok.arena_len_arr]; omega)]
              exact ⟨i.toNat, by omega, congrArg BitVec.toNat (m6_getElem_congr (by c0_bound) _ _)⟩
            exact hdw0.2.1.arena.lits_lt cref.toNat href hng _ hmem
          have hfl_idx : ((s0.core.arena[(cref.setWidth 64 + 3#64 + i.setWidth 64).toNat]'hcri >>>
              (1 : Nat)).setWidth 64).toNat < s0.core.flags.length := by
            rw [hdw0.1.core_ok.flags_len]; have := hdw0.1.core_ok.cur_vars_le; c0_bound
          have hi1 : (i + 1#32).toNat = i.toNat + 1 := by c0_bound
          c0_hsteps_nogrp
          refine wp_join_state_pure (ts := [i32, i32]) (α := BitVec 32 × BitVec 32)
            (fun p => (p.1, p.2, ())) (fun p => p.1.toNat < 2 * s0.core.cur_vars)
            (fun _ p hp => by
              c0_hsteps!
              exact hL1 (sz.toNat - (i + 1#32).toNat) (p.1, p.2, i + 1#32, ()) m1 (by omega)
                ⟨rfl, by omega, rfl, hp⟩)
            (fun J1 hJ1 => by
              c0_hsplit
              · have hwv_idx : ((s0.core.arena[(cref.setWidth 64 + 3#64 + i.setWidth 64).toNat]'
                    hcri).setWidth 64 <<< (1 : Nat) + 1#64).toNat < s0.core.wvec.length := by
                  rw [hdw0.1.core_ok.wvec_len]; have := hdw0.1.core_ok.cur_vars_le; c0_bound
                c0_hsteps_nogrp
                refine wp_join_state_pure (ts := [i32, i32]) (α := BitVec 32 × BitVec 32)
                  (fun p => (p.1, p.2, ())) (fun p => p.1.toNat < 2 * s0.core.cur_vars)
                  (fun _ p hp => by c0_hsteps!; exact hJ1 p hp)
                  (fun J1b hJ1b => by
                    c0_hsplit
                    · c0_hsteps!; exact hJ1b (_, _) hl_lt
                    · c0_hsteps!; exact hJ1b (best_l, best_d) hbl_lt)
              · c0_hsteps!
                exact hJ1 (best_l, best_d) hbl_lt)
        · -- Post-loop-1: optional fallback loop 2 + `if (best_d <= 1000u)` watch push
          c0_hsteps_nogrp
          refine wp_join_state_pure (ts := [i32, i32, i32])
            (α := BitVec 32 × BitVec 32 × BitVec 32) (fun p => (p.1, p.2.1, p.2.2, ()))
            (fun p => p.1.toNat < 2 * s0.core.cur_vars)
            ?_ ?_
          · rintro _ ⟨bl, bd, _⟩ hbl
            c0_hsteps_nogrp
            refine wp_join0 (P := fun mj => ∃ sj : FullState,
                FullDenseInvW c F0 F_cur sj ∧ sj.core.cur_vars = s0.core.cur_vars ∧
                sj.core.arena = s0.core.arena ∧ sj.core.arena_len = s0.core.arena_len ∧
                sj.core.fuel = s0.core.fuel ∧ sj.core.inconsistent = s0.core.inconsistent ∧
                sj.scratch.tarjan_mark = s0.scratch.tarjan_mark ∧
                sj.scratch.red_refs = s0.scratch.red_refs ∧ (FullMem c sj ⋆ R) mj)
              ?_ ?_
            · rintro _ mj ⟨sj, hdwj, hcvj, harj, halj, hflj, hincj, htmkj, hrrj, hmj⟩
              c0_hsteps!
              exact hQ sj mj hdwj hcvj harj halj hflj hincj htmkj hrrj hmj
            · intro J35 hJ35
              c0_hsplit
              · c0_hsteps_nogrp
                refine wp_join0 (P := fun mj => ∃ sj : FullState,
                    FullDenseInvW c F0 F_cur sj ∧ sj.core.cur_vars = s0.core.cur_vars ∧
                    sj.core.arena = s0.core.arena ∧ sj.core.arena_len = s0.core.arena_len ∧
                    sj.core.fuel = s0.core.fuel ∧
                    sj.core.inconsistent = s0.core.inconsistent ∧
                    sj.scratch.tarjan_mark = s0.scratch.tarjan_mark ∧
                    sj.scratch.red_refs = s0.scratch.red_refs ∧ (FullMem c sj ⋆ R) mj)
                  ?_ ?_
                · intro _ mj h; c0_hsteps!; exact hJ35 mj h
                · intro J37 hJ37
                  have hsz_lt31 : sz.toNat < 2 ^ 31 := by omega
                  have hsz_mask : (sz &&& 0x7FFFFFFF#32) = sz := m6_sz_and_mask_eq hsz_lt31
                  c0_hsteps_nogrp
                  m6_call hWatchPush
                  refine ⟨c, s0, R, rfl, hdw0.1, (m6_denseWatchesInv_of_w hdw0).layout,
                    fun h => by simp at h,
                    fun _ => by
                      dsimp only
                      have hcr_lt : cref.toNat < 2 ^ 31 := by have := hwf.1; omega
                      refine ⟨?_, m6_bv32_ne_sent_of_lt hcr_lt⟩
                      rw [show (s0.core.arena[(cref.setWidth 64 + 2).toNat]'hcr2_ar &&&
                          2147483647 : BitVec 32) = sz &&& 0x7FFFFFFF#32 from rfl, hsz_mask]
                      exact m6_bv32_ne_sent_of_lt hsz_lt31,
                    hm0, ?_⟩
                  intro ok wvec' wstk' wlen' wu' wsort' m2 s2 hlen2 hlay2 hoth2 hokt hokf hm2
                  have hdw2 : FullDenseInvW c F0 F_cur s2 :=
                    m6_fullDenseInvW_of_watchPush_occ hdw0 hlen2 hlay2 m6_sz_and_mask_no_bin
                      (by rw [hsz_mask]; omega) (by omega) href hoth2
                      (fun ht => by
                        obtain ⟨h1, _, h3, h4, h5, h6⟩ := hokt ht
                        exact ⟨h1, h3, h4, h5, h6 rfl⟩)
                      (fun hf => (hokf hf).1)
                  c0_hsplit
                  · c0_hsteps!
                    exact hJ37 m2 ⟨s2, hdw2, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hm2⟩
                  · c0_hsteps!
                    let soom : FullState := { s2 with core := { s2.core with oom := 1#64 } }
                    exact hJ37 m
                      ⟨soom, m6_fullDenseInvW_with_oom hdw2 1#64, rfl, rfl, rfl, rfl, rfl,
                       rfl, rfl, hm⟩
              · c0_hsteps!
                exact hJ35 m1 ⟨s0, hdw0, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hm0⟩
          · intro J2 hJ2
            c0_hsplit
            · have hbl_wv : (best_l.setWidth 64 <<< (1 : Nat) + 1#64).toNat <
                  s0.core.wvec.length := by
                rw [hdw0.1.core_ok.wvec_len]; have := hdw0.1.core_ok.cur_vars_le; c0_bound
              c0_hsteps_nogrp
              refine wp_loop_group (ts := [i32, i32, i32])
                (fun rem2 (bl2, bd2, i2, ()) m2 =>
                  m2 = m1 ∧ i2.toNat ≤ sz.toNat ∧ rem2 = sz.toNat - i2.toNat ∧
                  bl2.toNat < 2 * s0.core.cur_vars)
                ?_ ?_
              · rintro L2 rem2 ⟨bl2, bd2, i2, ⟨⟩⟩ m2 hL2 ⟨rfl, hi2_le, rfl, hbl2⟩
                c0_hsplit
                · have hi2_lt : i2.toNat < sz.toNat := hc
                  have hcri2 : (cref.setWidth 64 + 3#64 + i2.setWidth 64).toNat <
                      s0.core.arena.length := by
                    rw [hdw0.1.core_ok.arena_len_arr]; c0_bound
                  have hl2_lt : (s0.core.arena[(cref.setWidth 64 + 3#64 + i2.setWidth 64).toNat]'
                      hcri2).toNat < 2 * s0.core.cur_vars := by
                    have hmem : (s0.core.arena[(cref.setWidth 64 + 3#64 + i2.setWidth 64).toNat]'
                        hcri2).toNat ∈ fullArenaClauseLitsCore s0.core cref.toNat := by
                      rw [mem_fullArenaClauseLitsCore_iff (by
                        rw [hdw0.1.core_ok.arena_len_arr]; omega)]
                      exact ⟨i2.toNat, by omega, congrArg BitVec.toNat
                        (m6_getElem_congr (by c0_bound) _ _)⟩
                    exact hdw0.2.1.arena.lits_lt cref.toNat href hng _ hmem
                  have hwv2 : ((s0.core.arena[(cref.setWidth 64 + 3#64 + i2.setWidth 64).toNat]'
                      hcri2).setWidth 64 <<< (1 : Nat) + 1#64).toNat < s0.core.wvec.length := by
                    rw [hdw0.1.core_ok.wvec_len]; have := hdw0.1.core_ok.cur_vars_le; c0_bound
                  have hi21 : (i2 + 1#32).toNat = i2.toNat + 1 := by c0_bound
                  c0_hsteps_nogrp
                  refine wp_join_state_pure (ts := [i32, i32]) (α := BitVec 32 × BitVec 32)
                    (fun p => (p.1, p.2, ())) (fun p => p.1.toNat < 2 * s0.core.cur_vars)
                    (fun _ p hp => by
                      c0_hsteps!
                      exact hL2 (sz.toNat - (i2 + 1#32).toNat) (p.1, p.2, i2 + 1#32, ()) m2
                        (by omega) ⟨rfl, by omega, rfl, hp⟩)
                    (fun J2b hJ2b => by
                      c0_hsplit
                      · c0_hsteps!; exact hJ2b (_, _) hl2_lt
                      · c0_hsteps!; exact hJ2b (bl2, bd2) hbl2)
                · c0_hsteps!; exact hJ2 (bl2, bd2, i2) hbl2
              · intro L2 hL2; c0_hsteps!
                exact hL2 (sz.toNat - 1) (best_l, _, 1#32, ()) m1
                  ⟨rfl, by have : (1#32).toNat = 1 := rfl; omega, by simp, hbl_lt⟩
            · c0_hsteps!; exact hJ2 (best_l, best_d, i) hbl_lt
      · intro L1 hL1; c0_hsteps!
        exact hL1 sz.toNat (_, 0xFFFFFFFF#32, 0#32, ()) m0
          ⟨rfl, Nat.zero_le _, by simp, hl0_lt⟩

/-! ## 4. `full_fwd_collect_sort_m6` -/

/-- Contract for `full_fwd_collect_sort_m6`: clears `PH_SUBSUME`, collects candidate irredundant
large clauses (`3 <= sz <= 1000`, `>= 2` `FL_SUBSUME` lits) into `red_refs[0 ..< ncand)`, and
bucket-sorts ascending by length when `scratch_cap >= 1008`. -/
def fullFwdCollectSortM6Spec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ (FullMem c s ⋆ R) m ∧
    ∀ ncand s' m',
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.arena_len = s.core.arena_len → s'.core.fuel = s.core.fuel →
      s'.core.oom = s.core.oom → s'.core.inconsistent = s.core.inconsistent →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      ncand.toNat ≤ c.red_cap / 2 →
      (∀ i < ncand.toNat, (s'.scratch.red_refs[i]?.getD 0#32).toNat ∈ fullArenaClauseRefs s') →
      (FullMem c s' ⋆ R) m' → Q (ncand, ()) m'

theorem fullFwdCollectSortM6Spec_noExit :
    ∀ xs m Q X, fullFwdCollectSortM6Spec xs m Q X →
      fullFwdCollectSortM6Spec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem fullFwdCollectSortM6Spec_intro {h : BitVec 64} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {R : Mem 64 → Prop} (hh : h = c.hdr) (hdw : FullDenseInvW c F0 F_cur s)
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ ncand s' m',
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.arena_len = s.core.arena_len → s'.core.fuel = s.core.fuel →
      s'.core.oom = s.core.oom → s'.core.inconsistent = s.core.inconsistent →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      ncand.toNat ≤ c.red_cap / 2 →
      (∀ i < ncand.toNat, (s'.scratch.red_refs[i]?.getD 0#32).toNat ∈ fullArenaClauseRefs s') →
      (FullMem c s' ⋆ R) m' → Q (ncand, ()) m') :
    fullFwdCollectSortM6Spec (h, ()) m Q X :=
  ⟨c, F0, F_cur, s, R, hh, hdw, hm, hQ⟩

/-- Parametric `Func.wp` proof for `full_fwd_collect_sort_m6`. -/
theorem full_fwd_collect_sort_m6_wp (Γ : Env)
    (hArenaNext : ∀ a m Q X, fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X) :
    ∀ a m Q X, fullFwdCollectSortM6Spec a m Q X →
      Func.wp Γ full_fwd_collect_sort_m6_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m0 Q X ⟨c, F0, F_cur, s0, R, rfl, hdw0, hm0, hQ⟩
  have hmx := c.hmaxv; have harc := c.harena; have hrc := c.hred; have hsc := c.hscr
  unfold dimacsBound at hmx harc hrc hsc
  have hhalf_eq : (BitVec.ofNat 64 c.red_cap >>> (1 : Nat)).toNat = c.red_cap / 2 := by
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.shiftRight_eq_div_pow]
  unfold Func.wp full_fwd_collect_sort_m6_body
  c0_hsteps_nogrp
  -- Phase 1: scan arena, clear `PH_SUBSUME`, mark root-SAT `PH_GARB`, collect candidates
  refine wp_loop_group (ts := [i64, i64])
    (fun rem (ncand, p, ()) mp => ∃ sp : FullState,
      p.toNat ≤ sp.core.arena_len ∧ rem = sp.core.arena_len - p.toNat ∧
      (p.toNat = sp.core.arena_len ∨ p.toNat ∈ fullArenaClauseRefs sp) ∧
      FullDenseInvW c F0 F_cur sp ∧ sp.core.cur_vars = s0.core.cur_vars ∧
      sp.core.arena_len = s0.core.arena_len ∧ sp.core.fuel = s0.core.fuel ∧
      sp.core.oom = s0.core.oom ∧ sp.core.inconsistent = s0.core.inconsistent ∧
      sp.scratch.tarjan_mark = s0.scratch.tarjan_mark ∧
      ncand.toNat ≤ c.red_cap / 2 ∧
      (∀ i < ncand.toNat, (sp.scratch.red_refs[i]?.getD 0#32).toNat ∈ fullArenaClauseRefs sp) ∧
      (FullMem c sp ⋆ R) mp)
    ?_ ?_
  · rintro L rem ⟨ncand, p, ⟨⟩⟩ mp hL
      ⟨sp, hp_le, rfl, hp_mem, hdwp, hcvp, halp, hflp, hoomp, hincp, htmkp, hnc_le, hrr_ok, hmp⟩
    have hal_le := hdwp.1.core_ok.arena_len_le
    c0_hsplit
    · have hp_lt : p.toNat < sp.core.arena_len := by
        rw [Nat.mod_eq_of_lt (by omega)] at hc; exact hc
      have hp_ref : p.toNat ∈ fullArenaClauseRefs sp := hp_mem.resolve_left (by omega)
      have hwf_p := hdwp.2.1.arena.refs_wf p.toNat hp_ref
      have hp_ar : p.toNat < sp.core.arena.length := by
        rw [hdwp.1.core_ok.arena_len_arr]; omega
      have hp2_ar : (p + 2#64).toNat < sp.core.arena.length := by
        rw [hdwp.1.core_ok.arena_len_arr]; c0_bound
      have hp32 : (p.setWidth 32).toNat = p.toNat := by
        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
      let hdr_p := sp.core.arena[p.toNat]'hp_ar
      let sz_p := sp.core.arena[(p + 2#64).toNat]'hp2_ar
      have hsz_eq : sz_p.toNat = fullArenaClauseSizeCore sp.core p.toNat := by
        unfold sz_p fullArenaClauseSizeCore
        rw [List.getElem?_eq_getElem (by rw [hdwp.1.core_ok.arena_len_arr]; omega),
          Option.getD_some]
        exact congrArg BitVec.toNat (m6_getElem_congr (by c0_bound) _ _)
      c0_hsteps_nogrp
      m6_call hArenaNext
      refine ⟨c, sp, R, rfl, hdwp.1, hmp, ?_⟩
      have hnb := fullArenaNextOff_bounds (ar := sp.core.arena) (alen := sp.core.arena_len)
        (cref := p.toNat) hwf_p.1
      have hnp_mem := fullArenaClauseRefs_next_mem hdwp.2.1.arena hp_ref
      let np := (BitVec.ofNat 32 (fullArenaNextOff sp.core.arena sp.core.arena_len
        (p.setWidth 32).toNat)).setWidth 64
      have hnp_toNat : np.toNat = fullArenaNextOff sp.core.arena sp.core.arena_len p.toNat := by
        dsimp only [np]; rw [hp32, m6_zext32_toNat, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega)]
      c0_hsteps_nogrp
      refine wp_join_state (ts := [i64, i32]) (α := BitVec 64 × BitVec 32 × FullState)
        (fun x => (x.1, x.2.1, ()))
        (fun x mj =>
          FullDenseInvW c F0 F_cur x.2.2 ∧ x.2.2.core.cur_vars = s0.core.cur_vars ∧
          x.2.2.core.arena_len = s0.core.arena_len ∧ x.2.2.core.fuel = s0.core.fuel ∧
          x.2.2.core.oom = s0.core.oom ∧ x.2.2.core.inconsistent = s0.core.inconsistent ∧
          x.2.2.scratch.tarjan_mark = s0.scratch.tarjan_mark ∧
          fullArenaClauseRefs x.2.2 = fullArenaClauseRefs sp ∧
          x.1.toNat ≤ c.red_cap / 2 ∧
          (∀ i < x.1.toNat,
            (x.2.2.scratch.red_refs[i]?.getD 0#32).toNat ∈ fullArenaClauseRefs x.2.2) ∧
          (FullMem c x.2.2 ⋆ R) mj)
        (fun _ ⟨ncj, _hdj, sj⟩ mj ⟨hdwj, hcvj, halj, hflj, hoomj, hincj, htmkj, hrefsj, hncj,
            hrrj, hmj⟩ => by
          c0_hsteps!
          exact hL (sj.core.arena_len - np.toNat) (ncj, np, ()) mj
            (by rw [hnp_toNat, halj, ← halp]; omega)
            ⟨sj, by rw [hnp_toNat, halj, ← halp]; omega, rfl,
             by rw [hnp_toNat, halj, ← halp, hrefsj]; exact hnp_mem,
             hdwj, hcvj, halj, hflj, hoomj, hincj, htmkj, hncj, hrrj, hmj⟩)
        (fun Jp hJp => by
          c0_hsplit
          · have hng : fullArenaClauseGarb sp p.toNat = false := by
              unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
              rw [List.getElem?_eq_getElem hp_ar, Option.getD_some]
              rw [m6_and_garb_zero_of_mask hc]; rfl
            c0_hsplit
            · have hsz3 : 3 ≤ sz_p.toNat := hc
              -- Clear `PH_SUBSUME` bit if set
              c0_hsteps_nogrp
              refine wp_join_state (ts := [i32]) (α := BitVec 32 × FullState) (fun x => (x.1, ()))
                (fun x mc =>
                  FullDenseInvW c F0 F_cur x.2 ∧ x.2.core.cur_vars = s0.core.cur_vars ∧
                  x.2.core.arena_len = s0.core.arena_len ∧ x.2.core.fuel = s0.core.fuel ∧
                  x.2.core.oom = s0.core.oom ∧ x.2.core.inconsistent = s0.core.inconsistent ∧
                  x.2.scratch.tarjan_mark = s0.scratch.tarjan_mark ∧
                  x.2.scratch.red_refs = sp.scratch.red_refs ∧
                  fullArenaClauseRefs x.2 = fullArenaClauseRefs sp ∧
                  fullArenaClauseSize x.2 p.toNat = sz_p.toNat ∧
                  fullArenaClauseGarb x.2 p.toNat = false ∧
                  x.1 = fullArenaHdr x.2 p.toNat ∧
                  (FullMem c x.2 ⋆ R) mc)
                (fun _ ⟨hdr_c, sc⟩ mc ⟨hdwc, hcvc, halc, hflc, hoomc, hincc, htmkc, hrrc, hrefsc,
                    hszc, hngc, hhc, hmc⟩ => by
                  dsimp only at hrrc hszc hngc hhc
                  have hp_ref_c : p.toNat ∈ fullArenaClauseRefs sc := hrefsc.symm ▸ hp_ref
                  have hwf_c := hdwc.2.1.arena.refs_wf p.toNat hp_ref_c
                  have hp_arc : p.toNat < sc.core.arena.length := by
                    rw [hdwc.1.core_ok.arena_len_arr]; omega
                  c0_hsteps_nogrp
                  refine wp_loop_break_group (brkTs := [.bool, i32, i32]) (lpTs := [i32, i32])
                    (fun (sat_b, scnt_b, _kb, ()) ms => ms = mc)
                    (fun rem_k (scnt_k, k, ()) mk => k.toNat ≤ sz_p.toNat ∧
                      rem_k = sz_p.toNat - k.toNat ∧ mk = mc)
                    ?_ ?_ ?_
                  · rintro _ ⟨sat_b, scnt_b, _kb, ⟨⟩⟩ ms hms
                    subst ms
                    c0_hsteps_nogrp
                    refine wp_join_state (ts := [i64]) (α := BitVec 64 × FullState)
                      (fun x => (x.1, ()))
                      (fun x mj =>
                        FullDenseInvW c F0 F_cur x.2 ∧ x.2.core.cur_vars = s0.core.cur_vars ∧
                        x.2.core.arena_len = s0.core.arena_len ∧ x.2.core.fuel = s0.core.fuel ∧
                        x.2.core.oom = s0.core.oom ∧ x.2.core.inconsistent = s0.core.inconsistent ∧
                        x.2.scratch.tarjan_mark = s0.scratch.tarjan_mark ∧
                        fullArenaClauseRefs x.2 = fullArenaClauseRefs sp ∧
                        x.1.toNat ≤ c.red_cap / 2 ∧
                        (∀ i < x.1.toNat,
                          (x.2.scratch.red_refs[i]?.getD 0#32).toNat ∈
                            fullArenaClauseRefs x.2) ∧
                        (FullMem c x.2 ⋆ R) mj)
                      (fun _ ⟨nc', sr⟩ mr h => by
                        c0_hsteps!; exact hJp (nc', hdr_c, sr) mr h)
                      (fun J40 hJ40 => by
                        c0_hsplit
                        · c0_hsteps!
                          let ag' := sc.core.arena_garbage + 3#64 + sz_p.setWidth 64
                          let ar' := sc.core.arena.set p.toNat (hdr_c ||| 0x00080000#32)
                          let smg : FullState :=
                            { sc with core := { sc.core with arena := ar', arena_garbage := ag' } }
                          have hmg := m6_fullDenseInvW_markGarb hdwc hp_ref_c (arena' := ar')
                            (ag' := ag') (by simp [ar', hdwc.1.core_ok.arena_len_arr])
                            (Or.inl (by
                              dsimp only [ar']; rw [hhc]; exact List.getElem?_set_self hp_arc))
                            (fun i hne _ => by
                              dsimp only [ar']; exact List.getElem?_set_ne hne.symm)
                          exact hJ40 (ncand, smg) _ ⟨hmg.1, hcvc, halc, hflc, hoomc, hincc, htmkc,
                            hmg.2.trans hrefsc, hnc_le, fun i hi => by
                              dsimp only [smg]; rw [hrrc, hmg.2, hrefsc]; exact hrr_ok i hi, hm⟩
                        · c0_hsteps_nogrp
                          refine wp_join_state (ts := [i64]) (α := BitVec 64 × FullState)
                            (fun x => (x.1, ()))
                            (fun x mj =>
                              FullDenseInvW c F0 F_cur x.2 ∧ x.2.core.cur_vars = s0.core.cur_vars ∧
                              x.2.core.arena_len = s0.core.arena_len ∧
                              x.2.core.fuel = s0.core.fuel ∧
                              x.2.core.oom = s0.core.oom ∧
                              x.2.core.inconsistent = s0.core.inconsistent ∧
                              x.2.scratch.tarjan_mark = s0.scratch.tarjan_mark ∧
                              fullArenaClauseRefs x.2 = fullArenaClauseRefs sp ∧
                              x.1.toNat ≤ c.red_cap / 2 ∧
                              (∀ i < x.1.toNat,
                                (x.2.scratch.red_refs[i]?.getD 0#32).toNat ∈
                                  fullArenaClauseRefs x.2) ∧
                              (FullMem c x.2 ⋆ R) mj)
                            (fun _ ⟨nc', sr⟩ mr h => by c0_hsteps!; exact hJ40 (nc', sr) mr h)
                            (fun J41 hJ41 => by
                              c0_hsplit
                              · c0_hsplit
                                · c0_hsplit
                                  · have hnc_lt : ncand.toNat < c.red_cap / 2 := by
                                      rw [← hhalf_eq]; exact hc
                                    have hnc_rr : ncand.toNat < sc.scratch.red_refs.length := by
                                      rw [hdwc.1.scratch_ok.red_refs_len]; omega
                                    have hnc1 : (ncand + 1#64).toNat = ncand.toNat + 1 := by
                                      c0_bound
                                    c0_hsteps!
                                    let rr' := sc.scratch.red_refs.set ncand.toNat (p.setWidth 32)
                                    let sr : FullState :=
                                      { sc with scratch := { sc.scratch with red_refs := rr' } }
                                    have hdwr : FullDenseInvW c F0 F_cur sr :=
                                      m6_fullDenseInvW_with_scratch hdwc
                                        { hdwc.1.scratch_ok with
                                          red_refs_len := by
                                            simp [rr', hdwc.1.scratch_ok.red_refs_len] }
                                        rfl rfl
                                    exact hJ41 (ncand + 1#64, sr) _ ⟨hdwr, hcvc, halc, hflc, hoomc,
                                      hincc, htmkc, hrefsc, by dsimp only; omega, fun i hi => by
                                        dsimp only [sr, rr'] at hi ⊢
                                        rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp (hnc1 ▸ hi))
                                          with h | h
                                        · rw [List.getElem?_set_ne (by omega), hrrc]
                                          change _ ∈ fullArenaClauseRefs sc
                                          rw [hrefsc]; exact hrr_ok i h
                                        · subst h; rw [List.getElem?_set_self hnc_rr,
                                            Option.getD_some, hp32]; exact hp_ref_c, hm⟩
                                  · c0_hsteps!
                                    exact hJ41 (ncand, sc) mc ⟨hdwc, hcvc, halc, hflc, hoomc, hincc,
                                      htmkc, hrefsc, hnc_le, fun i hi => by
                                        rw [hrrc, hrefsc]; exact hrr_ok i hi, hmc⟩
                                · c0_hsteps!
                                  exact hJ41 (ncand, sc) mc ⟨hdwc, hcvc, halc, hflc, hoomc, hincc,
                                    htmkc, hrefsc, hnc_le, fun i hi => by
                                      rw [hrrc, hrefsc]; exact hrr_ok i hi, hmc⟩
                              · c0_hsteps!
                                exact hJ41 (ncand, sc) mc ⟨hdwc, hcvc, halc, hflc, hoomc, hincc,
                                  htmkc, hrefsc, hnc_le, fun i hi => by
                                    rw [hrrc, hrefsc]; exact hrr_ok i hi, hmc⟩))
                  · rintro Bk Lk rem_k ⟨scnt_k, k, ⟨⟩⟩ mk hBk hLk ⟨hk_le, rfl, hmk_eq⟩
                    subst hmk_eq
                    c0_hsplit
                    · have hk_lt : k.toNat < sz_p.toNat := hc
                      have hpi_ar : (p + 3#64 + k.setWidth 64).toNat < sc.core.arena.length := by
                        rw [hdwc.1.core_ok.arena_len_arr]; have := hdwc.1.core_ok.arena_len_le
                        c0_bound
                      have hcl_lt : (sc.core.arena[(p + 3#64 + k.setWidth 64).toNat]'hpi_ar).toNat <
                          2 * sc.core.cur_vars := by
                        have hmem : (sc.core.arena[(p + 3#64 + k.setWidth 64).toNat]'hpi_ar).toNat ∈
                            fullArenaClauseLitsCore sc.core p.toNat := by
                          rw [mem_fullArenaClauseLitsCore_iff (by
                            rw [hdwc.1.core_ok.arena_len_arr]
                            exact Nat.le_trans hwf_c.2.2.1
                              (Nat.le_trans hwf_c.2.2.2.1 hdwc.1.core_ok.arena_len_le))]
                          exact ⟨k.toNat, by
                              unfold fullArenaClauseSize at hszc; rw [hszc]; exact hk_lt,
                            congrArg BitVec.toNat (m6_getElem_congr (by c0_bound) _ _)⟩
                        exact hdwc.2.1.arena.lits_lt p.toNat hp_ref_c hngc _ hmem
                      have hcl_v : ((sc.core.arena[(p + 3#64 + k.setWidth 64).toNat]'
                          hpi_ar).setWidth 64).toNat < sc.core.vals.length := by
                        rw [hdwc.1.core_ok.vals_len]; have := hdwc.1.core_ok.cur_vars_le; c0_bound
                      have hk1 : (k + 1#32).toNat = k.toNat + 1 := by c0_bound
                      c0_hsplit
                      · c0_hsteps!; exact hBk (true, scnt_k, k, ()) mk rfl
                      · c0_hsteps_nogrp
                        refine wp_join_state_pure (ts := [i32]) (α := BitVec 32) (fun x => (x, ()))
                          (fun _ => True)
                          (fun _ sc' _ => by
                            c0_hsteps!
                            exact hLk (sz_p.toNat - (k + 1#32).toNat) (sc', k + 1#32, ()) mk
                              (by omega) ⟨by omega, rfl, rfl⟩)
                          (fun Js hJs => by
                            c0_hsplit
                            · have hfl_i : ((sc.core.arena[(p + 3#64 + k.setWidth 64).toNat]'
                                  hpi_ar >>> (1 : Nat)).setWidth 64).toNat <
                                  sc.core.flags.length := by
                                rw [hdwc.1.core_ok.flags_len]; have := hdwc.1.core_ok.cur_vars_le
                                c0_bound
                              c0_hsplit
                              · c0_hsteps!; exact hJs (scnt_k + 1#32) trivial
                              · c0_hsteps!; exact hJs scnt_k trivial
                            · c0_hsteps!; exact hJs scnt_k trivial)
                    · c0_hsteps!; exact hBk (false, scnt_k, k, ()) mk rfl
                  · intro _ Lk _ hLk; c0_hsteps!
                    exact hLk sz_p.toNat (0#32, 0#32, ()) mc ⟨Nat.zero_le _, by simp, rfl⟩)
                (fun Jc hJc => by
                  have hhdr_eq : hdr_p = fullArenaHdr sp p.toNat := by
                    unfold hdr_p fullArenaHdr fullArenaHdrCore
                    rw [List.getElem?_eq_getElem hp_ar, Option.getD_some]
                  c0_hsplit
                  · c0_hsteps!
                    let v' := hdr_p &&& ~~~0x01000000#32
                    let sc : FullState :=
                      { sp with core := { sp.core with arena := sp.core.arena.set p.toNat v' } }
                    have hcb := m6_bit24_clear_pres hdr_p
                    have hset := m6_fullDenseInvW_set_hdr_bit24 hdwp hp_ref (v' := v')
                      (by rw [← hhdr_eq]; exact hcb.1) (by rw [← hhdr_eq]; exact hcb.2)
                    have hper := hset.2.2 p.toNat hp_ref
                    have hhc : v' = fullArenaHdr sc p.toNat := by
                      unfold fullArenaHdr fullArenaHdrCore; dsimp only [sc]
                      rw [List.getElem?_set_self hp_ar, Option.getD_some]
                    exact hJc (v', sc) _ ⟨hset.1, hcvp, halp, hflp, hoomp, hincp, htmkp, rfl,
                      hset.2.1, hper.1.trans hsz_eq.symm, hper.2.1.trans hng, hhc, hm⟩
                  · c0_hsteps!
                    exact hJc (hdr_p, sp) mp ⟨hdwp, hcvp, halp, hflp, hoomp, hincp, htmkp, rfl,
                      rfl, hsz_eq.symm, hng, hhdr_eq, hmp⟩)
            · c0_hsteps!
              exact hJp (ncand, hdr_p, sp) mp ⟨hdwp, hcvp, halp, hflp, hoomp, hincp, htmkp, rfl,
                hnc_le, hrr_ok, hmp⟩
          · c0_hsteps!
            exact hJp (ncand, hdr_p, sp) mp ⟨hdwp, hcvp, halp, hflp, hoomp, hincp, htmkp, rfl,
              hnc_le, hrr_ok, hmp⟩)
    · -- Phase 2: ascending-length bucket sort if `ncand > 1 && scratch_cap >= 1008`
      c0_hsteps_nogrp
      refine wp_join_state (ts := []) (α := FullState) (fun _ => ())
        (fun sf mf => FullDenseInvW c F0 F_cur sf ∧ sf.core.cur_vars = s0.core.cur_vars ∧
          sf.core.arena_len = s0.core.arena_len ∧ sf.core.fuel = s0.core.fuel ∧
          sf.core.oom = s0.core.oom ∧ sf.core.inconsistent = s0.core.inconsistent ∧
          sf.scratch.tarjan_mark = s0.scratch.tarjan_mark ∧
          (∀ k < ncand.toNat, (sf.scratch.red_refs[k]?.getD 0#32).toNat ∈ fullArenaClauseRefs sf) ∧
          (FullMem c sf ⋆ R) mf)
        (fun _ sf mf ⟨hdwf, hcvf, half, hflf, hoomf, hincf, htmkf, hrrf, hmf⟩ => by
          c0_hsteps!
          exact hQ ncand sf mf hdwf hcvf half hflf hoomf hincf htmkf hnc_le hrrf hmf)
        (fun Jf hJf => by
          c0_hsplit
          · c0_hsplit
            · have hsc_ge : 1008 ≤ c.scratch_cap := by
                rw [Nat.mod_eq_of_lt (by omega)] at hc; exact hc
              c0_hsteps_nogrp
              -- Bucket zeroing loop: `b = 0 ..= 1000`
              refine wp_loop_group (ts := [i64])
                (fun rem1 (b, ()) m1 => ∃ scr1 : List (BitVec 32),
                  let s1 : FullState :=
                    { sp with scratch := { sp.scratch with scratch_buf := scr1 } }
                  scr1.length = c.scratch_cap ∧ b.toNat ≤ 1001 ∧ rem1 = 1001 - b.toNat ∧
                  (FullMem c s1 ⋆ R) m1)
                ?_ ?_
              · rintro L1 rem1 ⟨b, ⟨⟩⟩ m1 hL1 ⟨scr1, hsc1, hb_le, rfl, hm1⟩
                c0_hsplit
                · have hb_lt : b.toNat ≤ 1000 := hc
                  have hb_sc : b.toNat < scr1.length := by omega
                  have hb1 : (b + 1#64).toNat = b.toNat + 1 := by c0_bound
                  c0_hsteps!
                  exact hL1 (1001 - (b + 1#64).toNat) (b + 1#64, ()) _ (by omega)
                    ⟨scr1.set b.toNat 0#32, by simp [hsc1], by omega, rfl, hm⟩
                · -- Histogram loop: copy `rr[0..ncand)` to `rr[half..half+ncand)` & count sizes
                  c0_hsteps_nogrp
                  refine wp_loop_group (ts := [i64])
                    (fun rem2 (i, ()) m2 => ∃ (scr2 rr2 : List (BitVec 32)),
                      let s2 : FullState := { sp with scratch :=
                        { sp.scratch with scratch_buf := scr2, red_refs := rr2 } }
                      scr2.length = c.scratch_cap ∧ rr2.length = c.red_cap ∧
                      i.toNat ≤ ncand.toNat ∧ rem2 = ncand.toNat - i.toNat ∧
                      (∀ k < ncand.toNat, rr2[k]? = sp.scratch.red_refs[k]?) ∧
                      (∀ k < i.toNat,
                        (rr2[c.red_cap / 2 + k]?.getD 0#32).toNat ∈ fullArenaClauseRefs sp) ∧
                      (FullMem c s2 ⋆ R) m2)
                    ?_ ?_
                  · rintro L2 rem2 ⟨i, ⟨⟩⟩ m2 hL2
                      ⟨scr2, rr2, hsc2, hrr2, hi_le, rfl, hlo2, hhi2, hm2⟩
                    c0_hsplit
                    · have hi_lt : i.toNat < ncand.toNat := hc
                      have hi_rr : i.toNat < rr2.length := by omega
                      have hhi_idx : (BitVec.ofNat 64 c.red_cap >>> (1 : Nat) + i).toNat =
                          c.red_cap / 2 + i.toNat := by
                        rw [BitVec.toNat_add, hhalf_eq, Nat.mod_eq_of_lt (by omega)]
                      have hhi_rr : (BitVec.ofNat 64 c.red_cap >>> (1 : Nat) + i).toNat <
                          rr2.length := by omega
                      have hcr_ref : (rr2[i.toNat]'hi_rr).toNat ∈ fullArenaClauseRefs sp := by
                        have h0 := hrr_ok i.toNat hi_lt
                        rw [← hlo2 i.toNat hi_lt, List.getElem?_eq_getElem hi_rr,
                          Option.getD_some] at h0
                        exact h0
                      have hcr_wf := hdwp.2.1.arena.refs_wf _ hcr_ref
                      have hcr2_ar : ((rr2[i.toNat]'hi_rr).setWidth 64 + 2#64).toNat <
                          sp.core.arena.length := by
                        rw [hdwp.1.core_ok.arena_len_arr]; c0_bound
                      have hi1 : (i + 1#64).toNat = i.toNat + 1 := by c0_bound
                      let rr3 := rr2.set (BitVec.ofNat 64 c.red_cap >>> (1 : Nat) + i).toNat
                        (rr2[i.toNat]'hi_rr)
                      have hlo3 : ∀ k < ncand.toNat, rr3[k]? = sp.scratch.red_refs[k]? :=
                        fun k hk => by
                          dsimp only [rr3]; rw [List.getElem?_set_ne (by omega)]; exact hlo2 k hk
                      have hhi3 : ∀ k < (i + 1#64).toNat,
                          (rr3[c.red_cap / 2 + k]?.getD 0#32).toNat ∈ fullArenaClauseRefs sp :=
                        fun k hk => by
                          dsimp only [rr3]
                          rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp (hi1 ▸ hk)) with h | h
                          · rw [List.getElem?_set_ne (by omega)]; exact hhi2 k h
                          · subst h; rw [← hhi_idx, List.getElem?_set_self hhi_rr, Option.getD_some]
                            exact hcr_ref
                      c0_hsteps_nogrp
                      refine wp_join_state (ts := []) (α := List (BitVec 32)) (fun _ => ())
                        (fun scr2' m2' => scr2'.length = c.scratch_cap ∧
                          (FullMem c { sp with scratch :=
                            { sp.scratch with scratch_buf := scr2', red_refs := rr3 } } ⋆ R) m2')
                        (fun _ scr2' m2' ⟨hsc2', hm2'⟩ => by
                          c0_hsteps!
                          exact hL2 (ncand.toNat - (i + 1#64).toNat) (i + 1#64, ()) m2' (by omega)
                            ⟨scr2', rr3, hsc2', by simp [rr3, hrr2], by omega, rfl, hlo3, hhi3,
                             hm2'⟩)
                        (fun J2 hJ2 => by
                          c0_hsplit
                          · have hsz_val : sp.core.arena[((rr2[i.toNat]'hi_rr).setWidth 64 +
                                2#64).toNat]'hcr2_ar =
                                sp.core.arena[(rr2[i.toNat].toNat + 2) % 2 ^ 64]'(by
                                  rw [hdwp.1.core_ok.arena_len_arr]; simp; omega) :=
                              m6_getElem_congr (by c0_bound) _ _
                            have hsz_le1000 : (sp.core.arena[(rr2[i.toNat].toNat + 2) % 2 ^ 64]'(by
                                rw [hdwp.1.core_ok.arena_len_arr]; simp; omega)).toNat ≤ 1000 := by
                              simpa using hc
                            have hsz_sc : ((sp.core.arena[((rr2[i.toNat]'hi_rr).setWidth 64 +
                                2#64).toNat]'hcr2_ar).setWidth 64).toNat < scr2.length := by
                              rw [hsz_val, m6_zext32_toNat]; omega
                            c0_hsteps!
                            exact hJ2 _ _ ⟨by simp [hsc2], hm⟩
                          · c0_hsteps!; exact hJ2 scr2 _ ⟨hsc2, hm⟩)
                    · -- Prefix-sum loop: `b = 0 ..= 1000`
                      c0_hsteps_nogrp
                      refine wp_loop_group (ts := [i64, i32])
                        (fun rem3 (b, sum_b, ()) m3 => ∃ scr3 : List (BitVec 32),
                          let s3 : FullState := { sp with scratch :=
                            { sp.scratch with scratch_buf := scr3, red_refs := rr2 } }
                          scr3.length = c.scratch_cap ∧ b.toNat ≤ 1001 ∧ rem3 = 1001 - b.toNat ∧
                          (FullMem c s3 ⋆ R) m3)
                        ?_ ?_
                      · rintro L3 rem3 ⟨b, sum_b, ⟨⟩⟩ m3 hL3 ⟨scr3, hsc3, hb_le, rfl, hm3⟩
                        c0_hsplit
                        · have hb_lt : b.toNat ≤ 1000 := hc
                          have hb_sc : b.toNat < scr3.length := by omega
                          have hb1 : (b + 1#64).toNat = b.toNat + 1 := by c0_bound
                          c0_hsteps!
                          exact hL3 (1001 - (b + 1#64).toNat) (b + 1#64, _, ()) _ (by omega)
                            ⟨scr3.set b.toNat sum_b, by simp [hsc3], by omega, rfl, hm⟩
                        · -- Scatter loop: write `rr[half + pos] = cr`
                          c0_hsteps_nogrp
                          refine wp_loop_group (ts := [i64])
                            (fun rem4 (i, ()) m4 => ∃ (scr4 rr4 : List (BitVec 32)),
                              let s4 : FullState := { sp with scratch :=
                                { sp.scratch with scratch_buf := scr4, red_refs := rr4 } }
                              scr4.length = c.scratch_cap ∧ rr4.length = c.red_cap ∧
                              i.toNat ≤ ncand.toNat ∧ rem4 = ncand.toNat - i.toNat ∧
                              (∀ k < ncand.toNat, rr4[k]? = sp.scratch.red_refs[k]?) ∧
                              (∀ k < ncand.toNat,
                                (rr4[c.red_cap / 2 + k]?.getD 0#32).toNat ∈
                                  fullArenaClauseRefs sp) ∧
                              (FullMem c s4 ⋆ R) m4)
                            ?_ ?_
                          · rintro L4 rem4 ⟨i, ⟨⟩⟩ m4 hL4
                              ⟨scr4, rr4, hsc4, hrr4, hi_le, rfl, hlo4, hhi4, hm4⟩
                            c0_hsplit
                            · have hi_lt : i.toNat < ncand.toNat := hc
                              have hi_rr : i.toNat < rr4.length := by omega
                              have hcr_ref : (rr4[i.toNat]'hi_rr).toNat ∈
                                  fullArenaClauseRefs sp := by
                                have h0 := hrr_ok i.toNat hi_lt
                                rw [← hlo4 i.toNat hi_lt, List.getElem?_eq_getElem hi_rr,
                                  Option.getD_some] at h0
                                exact h0
                              have hcr_wf := hdwp.2.1.arena.refs_wf _ hcr_ref
                              have hcr2_ar : ((rr4[i.toNat]'hi_rr).setWidth 64 + 2#64).toNat <
                                  sp.core.arena.length := by
                                rw [hdwp.1.core_ok.arena_len_arr]; c0_bound
                              have hi1 : (i + 1#64).toNat = i.toNat + 1 := by c0_bound
                              c0_hsteps_nogrp
                              refine wp_join_state (ts := [])
                                (α := List (BitVec 32) × List (BitVec 32)) (fun _ => ())
                                (fun p4 m4' => p4.1.length = c.scratch_cap ∧
                                  p4.2.length = c.red_cap ∧
                                  (∀ k < ncand.toNat, p4.2[k]? = sp.scratch.red_refs[k]?) ∧
                                  (∀ k < ncand.toNat,
                                    (p4.2[c.red_cap / 2 + k]?.getD 0#32).toNat ∈
                                      fullArenaClauseRefs sp) ∧
                                  (FullMem c { sp with scratch :=
                                    { sp.scratch with scratch_buf := p4.1, red_refs := p4.2 } } ⋆
                                    R) m4')
                                (fun _ ⟨scr4', rr4'⟩ m4' ⟨hsc4', hrr4', hlo4', hhi4', hm4'⟩ => by
                                  c0_hsteps!
                                  exact hL4 (ncand.toNat - (i + 1#64).toNat) (i + 1#64, ()) m4'
                                    (by omega) ⟨scr4', rr4', hsc4', hrr4', by omega, rfl, hlo4',
                                      hhi4', hm4'⟩)
                                (fun J4 hJ4 => by
                                  c0_hsplit
                                  · have hsz_val : sp.core.arena[((rr4[i.toNat]'hi_rr).setWidth 64 +
                                        2#64).toNat]'hcr2_ar =
                                        sp.core.arena[(rr4[i.toNat].toNat + 2) % 2 ^ 64]'(by
                                          rw [hdwp.1.core_ok.arena_len_arr]; simp; omega) :=
                                      m6_getElem_congr (by c0_bound) _ _
                                    have hsz_le1000 :
                                        (sp.core.arena[(rr4[i.toNat].toNat + 2) % 2 ^ 64]'(by
                                          rw [hdwp.1.core_ok.arena_len_arr]; simp; omega)).toNat ≤
                                          1000 := by
                                      simpa using hc
                                    have hsz_sc : ((sp.core.arena[((rr4[i.toNat]'hi_rr).setWidth
                                        64 + 2#64).toNat]'hcr2_ar).setWidth 64).toNat <
                                        scr4.length := by
                                      rw [hsz_val, m6_zext32_toNat]; omega
                                    c0_hsteps_nogrp
                                    refine wp_join0 (P := fun mj =>
                                        ∃ scr4' rr4' : List (BitVec 32),
                                          scr4'.length = c.scratch_cap ∧ rr4'.length = c.red_cap ∧
                                          (∀ k < ncand.toNat,
                                            rr4'[k]? = sp.scratch.red_refs[k]?) ∧
                                          (∀ k < ncand.toNat,
                                            (rr4'[c.red_cap / 2 + k]?.getD 0#32).toNat ∈
                                              fullArenaClauseRefs sp) ∧
                                          (FullMem c { sp with
                                            scratch := { sp.scratch with
                                              scratch_buf := scr4', red_refs := rr4' } } ⋆ R) mj)
                                      (fun _ mj ⟨scr4', rr4', h1, h2, h3, h4, hm'⟩ => by
                                        c0_hsteps!
                                        exact hJ4 (scr4', rr4') mj ⟨h1, h2, h3, h4, hm'⟩)
                                      (fun J54 hJ54 => by
                                        c0_hsplit
                                        · have hpos_lt : (scr4[((sp.core.arena[((rr4[i.toNat]'
                                              hi_rr).setWidth 64 + 2#64).toNat]'hcr2_ar).setWidth
                                              64).toNat]'hsz_sc).toNat < ncand.toNat := by
                                            simpa only [hsz_val, m6_zext32_toNat,
                                              show (2 : BitVec 64).toNat = 2 from rfl] using hc
                                          have hpos_idx :
                                              (BitVec.ofNat 64 c.red_cap >>> (1 : Nat) +
                                                (scr4[((sp.core.arena[((rr4[i.toNat]'hi_rr).setWidth
                                                  64 + 2#64).toNat]'hcr2_ar).setWidth 64).toNat]'
                                                  hsz_sc).setWidth 64).toNat =
                                              c.red_cap / 2 +
                                                (scr4[((sp.core.arena[((rr4[i.toNat]'hi_rr).setWidth
                                                  64 + 2#64).toNat]'hcr2_ar).setWidth 64).toNat]'
                                                  hsz_sc).toNat := by
                                            rw [BitVec.toNat_add, hhalf_eq, m6_zext32_toNat,
                                              Nat.mod_eq_of_lt (by omega)]
                                          have hpos_rr :
                                              (BitVec.ofNat 64 c.red_cap >>> (1 : Nat) +
                                                (scr4[((sp.core.arena[((rr4[i.toNat]'hi_rr).setWidth
                                                  64 + 2#64).toNat]'hcr2_ar).setWidth 64).toNat]'
                                                  hsz_sc).setWidth 64).toNat < rr4.length := by
                                            omega
                                          have hpos_idx_c0 :
                                              ∀ (p1 : i.toNat < rr4.length)
                                                (p2 : ((rr4[i.toNat]'p1).setWidth 64 +
                                                  (2 : BitVec 64)).toNat < sp.core.arena.length)
                                                (p3 : ((sp.core.arena[((rr4[i.toNat]'p1).setWidth
                                                  64 + (2 : BitVec 64)).toNat]'p2).setWidth
                                                  64).toNat < scr4.length),
                                                (BitVec.ofNat 64 c.red_cap >>> (1 : Nat) +
                                                  (scr4[((sp.core.arena[((rr4[i.toNat]'p1).setWidth
                                                    64 + (2 : BitVec 64)).toNat]'p2).setWidth
                                                    64).toNat]'p3).setWidth 64).toNat =
                                                c.red_cap / 2 +
                                                  (scr4[((sp.core.arena[((rr4[i.toNat]'
                                                    hi_rr).setWidth 64 + 2#64).toNat]'
                                                    hcr2_ar).setWidth 64).toNat]'hsz_sc).toNat :=
                                            fun _ _ _ => hpos_idx
                                          c0_hsteps!
                                          dsimp only at hm
                                          refine hJ54 _ ⟨_, _, by simp [hsc4], by simp [hrr4],
                                            fun k hk => by
                                              rw [hpos_idx_c0, List.getElem?_set_ne (by omega)]
                                              exact hlo4 k hk,
                                            fun k hk => by
                                              rw [hpos_idx_c0]
                                              by_cases hke : c.red_cap / 2 + k =
                                                c.red_cap / 2 +
                                                  (scr4[((sp.core.arena[((rr4[i.toNat]'
                                                    hi_rr).setWidth 64 + 2#64).toNat]'
                                                    hcr2_ar).setWidth 64).toNat]'
                                                    hsz_sc).toNat
                                              · rw [hke, List.getElem?_set_self (by omega),
                                                  Option.getD_some]
                                                exact hcr_ref
                                              · rw [List.getElem?_set_ne (by omega)]
                                                exact hhi4 k hk,
                                            hm⟩
                                        · c0_hsteps!
                                          exact hJ54 m4 ⟨scr4, rr4, hsc4, hrr4, hlo4, hhi4, hm4⟩)
                                  · c0_hsteps!
                                    exact hJ4 (scr4, rr4) m4 ⟨hsc4, hrr4, hlo4, hhi4, hm4⟩)
                            · -- Final copyback loop: `rr[i] = rr[half + i]`
                              c0_hsteps_nogrp
                              refine wp_loop_group (ts := [i64])
                                (fun rem5 (i, ()) m5 => ∃ rr5 : List (BitVec 32),
                                  let s5 : FullState := { sp with scratch :=
                                    { sp.scratch with scratch_buf := scr4, red_refs := rr5 } }
                                  rr5.length = c.red_cap ∧ i.toNat ≤ ncand.toNat ∧
                                  rem5 = ncand.toNat - i.toNat ∧
                                  (∀ k < i.toNat,
                                    (rr5[k]?.getD 0#32).toNat ∈ fullArenaClauseRefs sp) ∧
                                  (∀ k < ncand.toNat,
                                    (rr5[c.red_cap / 2 + k]?.getD 0#32).toNat ∈
                                      fullArenaClauseRefs sp) ∧
                                  (FullMem c s5 ⋆ R) m5)
                                ?_ ?_
                              · rintro L5 rem5 ⟨i, ⟨⟩⟩ m5 hL5
                                  ⟨rr5, hrr5, hi_le, rfl, hlo5, hhi5, hm5⟩
                                c0_hsplit
                                · have hi_lt : i.toNat < ncand.toNat := hc
                                  have hi_rr : i.toNat < rr5.length := by omega
                                  have hhi_idx : (BitVec.ofNat 64 c.red_cap >>> (1 : Nat) +
                                      i).toNat = c.red_cap / 2 + i.toNat := by
                                    rw [BitVec.toNat_add, hhalf_eq, Nat.mod_eq_of_lt (by omega)]
                                  have hhi_rr : (BitVec.ofNat 64 c.red_cap >>> (1 : Nat) +
                                      i).toNat < rr5.length := by omega
                                  have hval_ref : (rr5[(BitVec.ofNat 64 c.red_cap >>> (1 : Nat) +
                                      i).toNat]'hhi_rr).toNat ∈ fullArenaClauseRefs sp := by
                                    have h0 := hhi5 i.toNat hi_lt
                                    rw [← hhi_idx, List.getElem?_eq_getElem hhi_rr,
                                      Option.getD_some] at h0
                                    exact h0
                                  have hi1 : (i + 1#64).toNat = i.toNat + 1 := by c0_bound
                                  c0_hsteps!
                                  refine hL5 (ncand.toNat - (i + 1#64).toNat) (i + 1#64, ()) _
                                    (by omega) ⟨_, by simp [hrr5], by omega, rfl,
                                      fun k hk => by
                                        rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp (hi1 ▸ hk))
                                          with h | h
                                        · rw [List.getElem?_set_ne (by omega)]; exact hlo5 k h
                                        · subst h; rw [List.getElem?_set_self hi_rr,
                                            Option.getD_some]
                                          exact hval_ref,
                                      fun k hk => by
                                        rw [List.getElem?_set_ne (by omega)]; exact hhi5 k hk, hm⟩
                                · have hi_eq : i.toNat = ncand.toNat := by omega
                                  c0_hsteps!
                                  let sfin : FullState := { sp with scratch :=
                                    { sp.scratch with scratch_buf := scr4, red_refs := rr5 } }
                                  have hdwf : FullDenseInvW c F0 F_cur sfin :=
                                    m6_fullDenseInvW_with_scratch hdwp
                                      { hdwp.1.scratch_ok with
                                        scratch_buf_len := hsc4, red_refs_len := hrr5 } rfl rfl
                                  exact hJf sfin m5 ⟨hdwf, hcvp, halp, hflp, hoomp, hincp, htmkp,
                                    fun k hk => hlo5 k (by omega), hm5⟩
                              · intro L5 hL5; c0_hsteps!
                                exact hL5 ncand.toNat (0#64, ()) m4
                                  ⟨rr4, hrr4, Nat.zero_le _, by simp, fun _ h => by simp at h,
                                   hhi4, hm4⟩
                          · intro L4 hL4; c0_hsteps!
                            exact hL4 ncand.toNat (0#64, ()) m3
                              ⟨scr3, rr2, hsc3, hrr2, Nat.zero_le _, by simp, hlo2,
                               fun k hk => hhi2 k (by omega), hm3⟩
                      · intro L3 hL3; c0_hsteps!
                        exact hL3 1001 (0#64, 0#32, ()) m2
                          ⟨scr2, hsc2, Nat.zero_le _, by simp, hm2⟩
                  · intro L2 hL2; c0_hsteps!
                    exact hL2 ncand.toNat (0#64, ()) m1
                      ⟨scr1, sp.scratch.red_refs, hsc1, hdwp.1.scratch_ok.red_refs_len,
                       Nat.zero_le _, by simp, fun _ _ => rfl, fun _ h => by simp at h, hm1⟩
              · intro L1 hL1; c0_hsteps!
                exact hL1 1001 (0#64, ()) mp
                  ⟨sp.scratch.scratch_buf, hdwp.1.scratch_ok.scratch_buf_len, Nat.zero_le _,
                   by simp, hmp⟩
            · c0_hsteps!
              exact hJf sp mp ⟨hdwp, hcvp, halp, hflp, hoomp, hincp, htmkp, hrr_ok, hmp⟩
          · c0_hsteps!
            exact hJf sp mp ⟨hdwp, hcvp, halp, hflp, hoomp, hincp, htmkp, hrr_ok, hmp⟩)
  · intro L hL; c0_hsteps!
    exact hL s0.core.arena_len (0#64, 0#64, ()) m0
      ⟨s0, Nat.zero_le _, by simp, by
        by_cases hz : s0.core.arena_len = 0
        · exact Or.inl hz.symm
        · exact Or.inr (m6_zero_mem_arenaRefs hdw0.2.1.arena (Nat.pos_of_ne_zero hz)),
       hdw0, rfl, rfl, rfl, rfl, rfl, rfl, Nat.zero_le _, fun _ h => by simp at h, hm0⟩

end LeanQbe.T.Examples.Kissat.FullM6BveFwd
