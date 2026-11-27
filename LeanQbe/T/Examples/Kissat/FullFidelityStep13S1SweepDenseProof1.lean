/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S1SweepDense
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S1Spec
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullDenseWatchLemmas1
import LeanQbe.T.Examples.Kissat.FullM6SweepProofCands
import LeanQbe.T.Examples.Kissat.FullM6CompactFlushProof2
import LeanQbe.T.Examples.Kissat.FullReduceLemmas1
import LeanQbe.T.Examples.Kissat.FullSpec1
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Fidelity Step 13 Shard S1-A Proofs — Part 1 (`dense_bin_roundtrip`,
`dense_bin_sort_roundtrip`, `full_m6_collect_cands`)

Parametric `(Γ : Env)` proofs (`public section`, `0` `@[expose]`, `0` `import all`,
`<= 100` cols, `< 1,400` LOC, every theorem `<= 420` lines):
1. `full_m6_collect_cands_s13_wp` (`step13CollectCandsSpec`)
2. `full_dense_bin_roundtrip_fid_s13_wp` (`step13DenseBinRoundtripSpec`)
3. `full_dense_bin_sort_roundtrip_fid_s13_wp` (`step13DenseBinSortRoundtripSpec`)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S1

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullDenseWatchHelpers
open LeanQbe.T.Examples.Kissat.FullM6Sweep
open Kraken.Bedrock2.Test

open scoped FullArenaTactics FullM6Sweep.CandsMemTactics

local macro "s13a1_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

/-! ## 1. `full_m6_collect_cands_s13_wp` (`step13CollectCandsSpec`) -/

private def S13CandsFrame (c : FullCfg) (s : FullState) : Mem 64 → Prop :=
  dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
  array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆ FullCoreArrays c s.core ⋆
  (FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆
    (array (t := i32) c.pWsort s.scratch.wsort ⋆
     array (t := i32) c.pWorkStk1 s.scratch.work_stk1 ⋆
     array (t := i32) c.pTarjanMark s.scratch.tarjan_mark) ⋆
    FullScrMetaArrs c s.scratch ⋆ FullScrDynArrs c s.scratch) ⋆
  c.pad

private theorem s13_candsFrame_irrel (c : FullCfg) (s : FullState)
    (trc' ws2' : List (BitVec 32)) :
    S13CandsFrame c
      { s with scratch := { s.scratch with tarjan_reach := trc', work_stk2 := ws2' } } =
      S13CandsFrame c s := rfl

private theorem s13_fullMem_eq_candsFrame (c : FullCfg) (s : FullState) :
    FullMem c s =
      (array (t := i32) c.pTarjanReach s.scratch.tarjan_reach ⋆
        array (t := i32) c.pWorkStk2 s.scratch.work_stk2 ⋆
        S13CandsFrame c s) := by
  unfold FullMem FullScratchArrays FullScrWksArrs S13CandsFrame; ac_rfl

private theorem s13_split_array {a : BitVec 64} {xs : List (BitVec 32)} {n : Nat}
    (hn : n ≤ xs.length) :
    array (t := i32) a xs =
      (array (t := i32) a (xs.take n) ⋆
        array (t := i32) (a + BitVec.ofNat 64 (4 * n)) (xs.drop n)) := by
  have htake : (xs.take n).length = n := List.length_take_of_le hn
  conv => lhs; rw [← List.take_append_drop n xs]
  rw [array_append, htake]; rfl

private theorem s13_join_array {a : BitVec 64} {pref suff : List (BitVec 32)}
    {n : Nat} (hp : pref.length = n) :
    (array (t := i32) a pref ⋆ array (t := i32) (a + BitVec.ofNat 64 (4 * n)) suff) =
      array (t := i32) a (pref ++ suff) := by
  rw [array_append, hp]; rfl

private theorem s13_lengthsOk_trc_ws2 {c : FullCfg} {s : FullState} (h : s.LengthsOk c)
    {trc' ws2' : List (BitVec 32)} (htrc : trc'.length = 2 * c.max_vars)
    (hws2 : ws2'.length = 2 * c.max_vars) :
    ({ s with scratch := { s.scratch with tarjan_reach := trc', work_stk2 := ws2' } } :
      FullState).LengthsOk c :=
  ⟨h.core_ok, { h.scratch_ok with tarjan_reach_len := htrc, work_stk2_len := hws2 }⟩

private theorem s13_list_set_swap_bound {xs : List (BitVec 32)} {r c n bound : Nat}
    (hr : r < n) (hc : c < n) (hn : n ≤ xs.length)
    (hbd : ∀ i < n, (xs[i]?.getD 0#32).toNat < bound) :
    ∀ i < n, (((xs.set r (xs[c]'(by omega))).set c
      (xs[r]'(by omega)))[i]?.getD 0#32).toNat < bound := by
  intro i hi
  by_cases hic : i = c
  · subst hic
    rw [List.getElem?_set_self (by simp; omega), Option.getD_some]
    have := hbd r hr
    rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at this
  · rw [List.getElem?_set_ne (Ne.symm hic)]
    by_cases hir : i = r
    · subst hir
      rw [List.getElem?_set_self (by omega), Option.getD_some]
      have := hbd c hc
      rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at this
    · rw [List.getElem?_set_ne (Ne.symm hir)]; exact hbd i hi

private theorem s13_call_cand_sift {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (hSift : M6EnvSpec Γ "full_m6_cand_sift" m6CandSiftSpec)
    {cands_ptr deg_ptr : BitVec 64} (start n : BitVec 32)
    {cands deg : List (BitVec 32)} {bound : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    {k : Tup Val [] → Expr Val Cont rs}
    (hsn : start.toNat < n.toNat) (hnc : n.toNat ≤ cands.length) (hn31 : n.toNat < 2 ^ 31)
    (hbd : bound ≤ deg.length) (hclt : ∀ i < n.toNat, (cands[i]?.getD 0#32).toNat < bound)
    (hm : (array (t := i32) cands_ptr cands ⋆ array (t := i32) deg_ptr deg ⋆ R) m)
    (hk : ∀ cands' m', cands'.length = cands.length →
      (∀ i < n.toNat, (cands'[i]?.getD 0#32).toNat < bound) →
      (array (t := i32) cands_ptr cands' ⋆ array (t := i32) deg_ptr deg ⋆ R) m' →
      wp Γ Q X (k ()) m') :
    wp Γ Q X
      (Expr.call (as := [i64, i64, i32, i32]) (bs := []) "full_m6_cand_sift"
        (Arg.var cands_ptr, Arg.var deg_ptr, Arg.var start, Arg.var n, ()) k) m :=
  wp_call_of_spec _ k
    (hSift (cands_ptr, deg_ptr, start, n, ()) m (fun r m' => wp Γ Q X (k r) m') X
      ⟨cands, deg, bound, R, hsn, hnc, hn31, hbd, hclt, hm, hk⟩)

private theorem s13_nat_two_mul_lor_one (n : Nat) : 2 * n ||| 1 = 2 * n + 1 := by
  apply Nat.eq_of_testBit_eq; intro k
  cases k with
  | zero => simp [Nat.testBit_zero]
  | succ k =>
    rw [Nat.testBit_or, Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ,
      show 1 / 2 = 0 from rfl, show (2 * n) / 2 = n from by omega,
      show (2 * n + 1) / 2 = n from by omega, Nat.zero_testBit, Bool.or_false]

/-- Step-13 `full_m6_collect_cands` uses `full_dense_occ_cnt_fid` and cyclic cursor. -/
theorem full_m6_collect_cands_s13_wp (Γ : Env)
    (hOcc : ∀ a m Q X, step13DenseOccCntSpec a m Q X →
      Γ "full_dense_occ_cnt_fid" [i64, i32, i64] [i64] a m Q X)
    (hSift : M6EnvSpec Γ "full_m6_cand_sift" m6CandSiftSpec) :
    ∀ a m Q X, step13CollectCandsSpec a m Q X →
      Func.wp Γ full_m6_collect_cands_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hlay, hm, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv_le := hlen.core_ok.cur_vars_le
  have hcv_lt64 : s.core.cur_vars < 2 ^ 64 := by omega
  have hcv_mod : (BitVec.ofNat 64 s.core.cur_vars).toNat = s.core.cur_vars := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcv_lt64]
  have hfl_len := hlen.core_ok.flags_len
  have hvals_len := hlen.core_ok.vals_len
  have hgu_len := hlen.scratch_ok.glue_used_len
  have htrc_len := hlen.scratch_ok.tarjan_reach_len
  have hws2_len := hlen.scratch_ok.work_stk2_len
  have h28_lt : 28 < s.scratch.glue_used.length := by omega
  have h30_lt : 30 < s.scratch.glue_used.length := by omega
  unfold Func.wp full_m6_collect_cands_body
  c0_hsteps_nogrp
  c0_hsplit
  · c0_hsteps_nogrp
    exact hQ 0#32 s.scratch.tarjan_reach s.scratch.work_stk2 m hlen (Nat.zero_le _)
      (fun _ hi => by simp at hi) hm
  have hcv_pos : 0 < s.core.cur_vars := by
    apply Nat.pos_of_ne_zero; intro hz
    exact hc (by rw [hz]; rfl)
  clear hc
  c0_hsteps_nogrp
  refine wp_join_state (ts := [i32]) (α := BitVec 32) (fun comp => (comp, ()))
    (fun _ mc => m = mc) ?_ (fun Jcomp hJcomp => by
      c0_hsplit
      · c0_hsteps_nogrp; exact hJcomp 5#32 m rfl
      · c0_hsteps_nogrp; exact hJcomp _ m rfl)
  rintro _ _ _ rfl
  c0_hsteps_nogrp
  refine wp_join_state (ts := [i64]) (α := BitVec 64) (fun cur => (cur, ()))
    (fun cur mc => m = mc ∧ cur.toNat < s.core.cur_vars)
    (fun _ cur mc ⟨hmc, hcur_lt⟩ => by
      cases hmc
      c0_hsteps_nogrp
      refine wp_while_state (ts := [i32, i64]) (α := BitVec 32 × BitVec 64)
        (fun st => (st.1, st.2, ())) (fun st => s.core.cur_vars - st.2.toNat)
        (fun st ml => st.1.toNat ≤ st.2.toNat ∧ st.2.toNat ≤ s.core.cur_vars ∧
          ∃ trc ws2, trc.length = 2 * c.max_vars ∧ ws2.length = 2 * c.max_vars ∧
          (∀ i < st.1.toNat, (trc[i]?.getD 0#32).toNat < s.core.cur_vars) ∧
          (FullMem c { s with scratch :=
            { s.scratch with tarjan_reach := trc, work_stk2 := ws2 } } ⋆ R) ml)
        (fun _ hJ => by
          c0_hsteps_nogrp
          exact hJ (0#32, 0#64) m ⟨Nat.zero_le _, Nat.zero_le _, s.scratch.tarjan_reach,
            s.scratch.work_stk2, htrc_len, hws2_len, fun _ hi => by simp at hi, hm⟩)
        (fun _ ⟨nc, step⟩ ml ⟨hnc_le, hstep_le, trc, ws2, htrcL, hws2L, hbdL, hmL⟩ hJ => by
          dsimp only at hnc_le hstep_le hbdL
          let sL : FullState :=
            { s with scratch := { s.scratch with tarjan_reach := trc, work_stk2 := ws2 } }
          have hlenL : sL.LengthsOk c := s13_lengthsOk_trc_ws2 hlen htrcL hws2L
          change (FullMem c sL ⋆ R) ml at hmL
          c0_hsplit
          · have hstep_lt : step.toNat < s.core.cur_vars := by rw [← hcv_mod]; exact hc
            have hstep1 : (step + 1#64).toNat = step.toNat + 1 := by bv_omega
            have hnc1 : (nc + 1#32).toNat = nc.toNat + 1 := by bv_omega
            c0_hsteps_nogrp
            refine wp_join_state (ts := [i64]) (α := BitVec 64) (fun v => (v, ()))
              (fun v mv => ml = mv ∧ v.toNat < s.core.cur_vars)
              (fun _ v mv ⟨rfl, hv_lt⟩ => by
                have hv_fl : v.toNat < sL.core.flags.length := by dsimp [sL]; omega
                have hv_2v : (v <<< (1 : Nat)).toNat = 2 * v.toNat := by bv_omega
                have hv_vals : (v <<< (1 : Nat)).toNat < sL.core.vals.length := by
                  rw [hv_2v]; dsimp [sL]; omega
                have hv_ws2 : v.toNat < sL.scratch.work_stk2.length := by dsimp [sL]; omega
                have hnc_trc : nc.toNat < sL.scratch.tarjan_reach.length := by dsimp [sL]; omega
                c0_hsteps_nogrp
                refine wp_join_state1 (fun nc' : BitVec 32 => nc')
                  (fun nc' mj => nc'.toNat ≤ step.toNat + 1 ∧
                    ∃ trc' ws2', trc'.length = 2 * c.max_vars ∧ ws2'.length = 2 * c.max_vars ∧
                    (∀ i < nc'.toNat, (trc'[i]?.getD 0#32).toNat < s.core.cur_vars) ∧
                    (FullMem c { s with scratch :=
                      { s.scratch with tarjan_reach := trc', work_stk2 := ws2' } } ⋆ R) mj)
                  (fun _ nc' mj ⟨h1, trc', ws2', htrc', hws2', hbd', hm'⟩ => by
                    dsimp only [Blocks.get]
                    c0_hsteps_nogrp
                    exact hJ (nc', step + 1#64) mj (by dsimp only; omega)
                      ⟨by dsimp only; omega, by dsimp only; omega, trc', ws2',
                       htrc', hws2', hbd', hm'⟩)
                  (fun _ hJin => by
                    c0_hsplit; rotate_left
                    · c0_hsteps_nogrp
                      exact hJin nc ml ⟨by omega, trc, ws2, htrcL, hws2L, hbdL, hmL⟩
                    c0_hsplit; rotate_left
                    · c0_hsteps_nogrp
                      exact hJin nc ml ⟨by omega, trc, ws2, htrcL, hws2L, hbdL, hmL⟩
                    have hl_pos : ((v <<< (1 : Nat)).setWidth 32).toNat <
                        2 * sL.core.cur_vars := by
                      rw [BitVec.toNat_setWidth, hv_2v,
                        Nat.mod_eq_of_lt (by dsimp [sL] at *; omega)]
                      dsimp [sL]; omega
                    c0_hsteps_nogrp; s13a1_call hOcc
                    refine ⟨c, sL, R, rfl, hlenL, hlay, hl_pos, hmL, fun dp => ?_⟩
                    have hl_neg : (((v <<< (1 : Nat)) ||| 1#64).setWidth 32).toNat <
                        2 * sL.core.cur_vars := by
                      rw [BitVec.toNat_setWidth, BitVec.toNat_or, hv_2v,
                        show (1#64 : BitVec 64).toNat = 1 from rfl, s13_nat_two_mul_lor_one,
                        Nat.mod_eq_of_lt (by dsimp [sL] at *; omega)]
                      dsimp [sL]; omega
                    c0_hsteps_nogrp; s13a1_call hOcc
                    refine ⟨c, sL, R, rfl, hlenL, hlay, hl_neg, hmL, fun dn => ?_⟩
                    c0_hsteps_nogrp
                    refine wp_join_state1 (fun nc' : BitVec 32 => nc')
                      (fun nc' mj => nc'.toNat ≤ step.toNat + 1 ∧
                        ∃ trc' ws2', trc'.length = 2 * c.max_vars ∧ ws2'.length = 2 * c.max_vars ∧
                        (∀ i < nc'.toNat, (trc'[i]?.getD 0#32).toNat < s.core.cur_vars) ∧
                        (FullMem c { s with scratch :=
                          { s.scratch with tarjan_reach := trc', work_stk2 := ws2' } } ⋆ R) mj)
                      (fun _ nc' mj h => hJin nc' mj h) (fun _ hJin2 => by
                    c0_hsplit; rotate_left
                    · c0_hsteps_nogrp
                      exact hJin2 nc ml ⟨by omega, trc, ws2, htrcL, hws2L, hbdL, hmL⟩
                    c0_hsplit; rotate_left
                    · c0_hsteps_nogrp
                      exact hJin2 nc ml ⟨by omega, trc, ws2, htrcL, hws2L, hbdL, hmL⟩
                    c0_hsplit; rotate_left
                    · c0_hsteps_nogrp
                      exact hJin2 nc ml ⟨by omega, trc, ws2, htrcL, hws2L, hbdL, hmL⟩
                    c0_hsplit; rotate_left
                    · c0_hsteps_nogrp
                      exact hJin2 nc ml ⟨by omega, trc, ws2, htrcL, hws2L, hbdL, hmL⟩
                    have hbd_new : ∀ i < (nc + 1#32).toNat,
                        ((trc.set nc.toNat (v.setWidth 32))[i]?.getD 0#32).toNat <
                          s.core.cur_vars := by
                      intro i hi
                      by_cases hinc : i = nc.toNat
                      · subst hinc
                        rw [List.getElem?_set_self (by dsimp [sL] at hnc_trc; omega),
                          Option.getD_some, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
                        exact hv_lt
                      · rw [List.getElem?_set_ne (Ne.symm hinc)]; exact hbdL i (by omega)
                    c0_hsteps_nogrp
                    refine wp_join_state1 (fun d32 : BitVec 32 => d32) (fun _ mj => ml = mj)
                      (fun _ d32 mj hmj => by
                        subst hmj; c0_hsteps_nogrp
                        refine wp_join_state1 (fun d32' : BitVec 32 => d32') (fun _ mk => ml = mk)
                          (fun _ d32' mk hmk => by
                            subst hmk; c0_hsteps_nogrp
                            refine hJin2 (nc + 1#32) _ ⟨by omega,
                              trc.set nc.toNat (v.setWidth 32),
                              ws2.set v.toNat d32',
                              by simp [htrcL], by simp [hws2L], hbd_new, ?_⟩
                            dsimp only [sL] at *; exact (by assumption))
                          (fun _ hJd => by
                            c0_hsplit
                            · c0_hsteps_nogrp
                              refine wp_join_state1 (fun df : BitVec 32 => df)
                                (fun _ mk => ml = mk)
                                (fun _ df mk hmk => by
                                  subst hmk; c0_hsteps_nogrp; exact hJd (d32 ||| df) ml rfl)
                                (fun _ hJf => by
                                  c0_hsplit
                                  · c0_hsteps_nogrp; exact hJf 0x40000000#32 ml rfl
                                  · c0_hsteps_nogrp; exact hJf 0x80000000#32 ml rfl)
                            · c0_hsteps_nogrp; exact hJd d32 ml rfl))
                      (fun _ hJd => by
                        c0_hsplit
                        · c0_hsteps_nogrp; exact hJd 0x3FFFFFFF#32 ml rfl
                        · c0_hsteps_nogrp; exact hJd ((dp + dn).setWidth 32) ml rfl))))
              (fun Jv hJv => by
                c0_hsplit
                · have hge : (BitVec.ofNat 64 s.core.cur_vars).toNat ≤ (cur + step).toNat := by
                    assumption
                  rw [hcv_mod] at hge
                  have hcur_step : (cur + step).toNat = cur.toNat + step.toNat := by
                    have : cur.toNat + step.toNat < 2 ^ 64 := by omega
                    bv_omega
                  have hsub_eq : (cur + step - BitVec.ofNat 64 s.core.cur_vars).toNat =
                      cur.toNat + step.toNat - s.core.cur_vars := by
                    rw [BitVec.toNat_sub, hcv_mod, hcur_step]; omega
                  c0_hsteps_nogrp
                  exact hJv (cur + step - BitVec.ofNat 64 s.core.cur_vars) ml
                    ⟨rfl, by rw [hsub_eq]; omega⟩
                · have hlt : ¬ (BitVec.ofNat 64 s.core.cur_vars).toNat ≤ (cur + step).toNat := by
                    assumption
                  rw [hcv_mod] at hlt
                  have hcur_step : (cur + step).toNat = cur.toNat + step.toNat := by
                    have : cur.toNat + step.toNat < 2 ^ 64 := by omega
                    bv_omega
                  c0_hsteps_nogrp
                  exact hJv (cur + step) ml ⟨rfl, by rw [hcur_step]; omega⟩)
          · have hstep_eq : step.toNat = s.core.cur_vars := by rw [← hcv_mod] at *; bv_omega
            have hnc_cur : nc.toNat ≤ s.core.cur_vars := by omega
            c0_hsplit
            · c0_hsteps_nogrp; exact hQ nc trc ws2 ml hlenL hnc_cur hbdL hmL
            have hnc_ge2 : 2 ≤ nc.toNat := by bv_omega
            c0_hsteps_nogrp
            refine wp_while_state1 (t := i32) (α := BitVec 32)
              (fun x => x) (fun x => x.toNat)
              (fun x ml1 => x.toNat ≤ nc.toNat ∧ ∃ trc1, trc1.length = 2 * c.max_vars ∧
                (∀ i < nc.toNat, (trc1[i]?.getD 0#32).toNat < s.core.cur_vars) ∧
                (FullMem c { s with scratch :=
                  { s.scratch with tarjan_reach := trc1, work_stk2 := ws2 } } ⋆ R) ml1)
              (fun _ hJs => by
                c0_hsteps_nogrp
                exact hJs (nc >>> 1#32) ml
                  ⟨by rw [show nc >>> 1#32 = nc >>> (1 : Nat) from rfl]; bv_omega,
                   trc, htrcL, hbdL, hmL⟩)
              (fun _ s_i ml1 ⟨hsi_le, trc1, htrc1L, hbd1L, hm1⟩ hJs => by
                c0_hsplit
                · have hsi_pos : 0 < s_i.toNat := by bv_omega
                  have hsi1 : (s_i - 1#32).toNat = s_i.toNat - 1 := by bv_omega
                  c0_hsteps_nogrp
                  have hm_focus : (array (t := i32) c.pTarjanReach trc1 ⋆
                      array (t := i32) c.pWorkStk2 ws2 ⋆
                      (S13CandsFrame c { s with scratch :=
                        { s.scratch with tarjan_reach := trc1, work_stk2 := ws2 } } ⋆ R)) ml1 := by
                    rw [s13_fullMem_eq_candsFrame] at hm1; exact sep_ac hm1
                  refine s13_call_cand_sift hSift (bound := s.core.cur_vars) (s_i - 1#32) nc
                    (by omega) (by omega) (by omega) (by omega) hbd1L hm_focus
                    fun trc2 m2 htrc2L hbd2L hm2 => ?_
                  have hm2_full : (FullMem c { s with scratch :=
                      { s.scratch with tarjan_reach := trc2, work_stk2 := ws2 } } ⋆ R) m2 := by
                    rw [s13_fullMem_eq_candsFrame, s13_candsFrame_irrel]; exact sep_ac hm2
                  c0_hsteps_nogrp
                  exact hJs (s_i - 1#32) m2 (by omega) ⟨by omega, trc2, by omega, hbd2L, hm2_full⟩
                · c0_hsteps_nogrp
                  refine wp_while_state1 (t := i32) (α := BitVec 32)
                    (fun x => x) (fun x => x.toNat)
                    (fun x ml2 => 1 ≤ x.toNat ∧ x.toNat ≤ nc.toNat ∧ ∃ trc2,
                      trc2.length = 2 * c.max_vars ∧
                      (∀ i < nc.toNat, (trc2[i]?.getD 0#32).toNat < s.core.cur_vars) ∧
                      (FullMem c { s with scratch :=
                        { s.scratch with tarjan_reach := trc2, work_stk2 := ws2 } } ⋆ R) ml2)
                    (fun _ hJe => by
                      c0_hsteps_nogrp
                      exact hJe nc ml1 ⟨by omega, Nat.le_refl _, trc1, htrc1L, hbd1L, hm1⟩)
                    (fun _ end_v ml2 ⟨hend1, hend_le, trc2, htrc2L, hbd2L, hm2⟩ hJe => by
                      c0_hsplit; rotate_left
                      · c0_hsteps_nogrp
                        exact hQ nc trc2 ws2 ml2 (s13_lengthsOk_trc_ws2 hlen htrc2L hws2L)
                          hnc_cur hbd2L hm2
                      have hend_gt1 : 1 < end_v.toNat := by bv_omega
                      let end' := end_v - 1#32
                      have hend'_eq : end'.toNat = end_v.toNat - 1 := by
                        dsimp only [end']; bv_omega
                      have h0_trc : 0 < trc2.length := by omega
                      have hend'_trc : end'.toNat < trc2.length := by omega
                      have hm2_arr : (array (t := i32) c.pTarjanReach trc2 ⋆
                          (array (t := i32) c.pWorkStk2 ws2 ⋆
                           (S13CandsFrame c { s with scratch :=
                             { s.scratch with tarjan_reach := trc2, work_stk2 := ws2 } } ⋆
                            R))) ml2 := by
                        rw [s13_fullMem_eq_candsFrame] at hm2; exact sep_ac hm2
                      c0_hsteps_nogrp
                      let trc3 := (trc2.set 0 (trc2[end'.toNat]'hend'_trc)).set end'.toNat
                        (trc2[0]'h0_trc)
                      have htrc3L : trc3.length = 2 * c.max_vars := by
                        dsimp only [trc3]; simp [htrc2L]
                      have hbd3L : ∀ i < nc.toNat,
                          (trc3[i]?.getD 0#32).toNat < s.core.cur_vars := by
                        simpa [trc3] using s13_list_set_swap_bound (n := nc.toNat) (by omega)
                          (by omega) (by omega) hbd2L
                      have hm3_split : (array (t := i32) c.pTarjanReach (trc3.take end'.toNat) ⋆
                          array (t := i32) c.pWorkStk2 ws2 ⋆
                          (array (t := i32) (c.pTarjanReach + BitVec.ofNat 64 (4 * end'.toNat))
                            (trc3.drop end'.toNat) ⋆
                           S13CandsFrame c { s with scratch :=
                             { s.scratch with tarjan_reach := trc2, work_stk2 := ws2 } } ⋆
                           R)) m := by
                        have hm_sw : (array (t := i32) c.pTarjanReach trc3 ⋆
                            (array (t := i32) c.pWorkStk2 ws2 ⋆
                             (S13CandsFrame c { s with scratch :=
                               { s.scratch with tarjan_reach := trc2, work_stk2 := ws2 } } ⋆
                              R))) m := by
                          have h1 := hm
                          simp only [bv_c0_zext32_64,
                            CandsMemTactics.bv_ofNat64_zero_toNat] at h1
                          have hlist : (trc2.set 0 trc2[(end_v - 1).toNat]).set (end_v - 1).toNat
                              trc2[0] = trc3 := by
                            dsimp only [trc3, end']; rfl
                          rwa [hlist] at h1
                        rw [s13_split_array (n := end'.toNat) (by omega)] at hm_sw
                        exact sep_ac hm_sw
                      refine s13_call_cand_sift hSift (bound := s.core.cur_vars) 0#32 end'
                        (by rw [show (0#32 : BitVec 32).toNat = 0 from rfl]; omega)
                        (by simp [htrc3L]; omega) (by omega) (by omega)
                        (fun i hi => by
                          rw [List.getElem?_take_of_lt hi]; exact hbd3L i (by omega))
                        hm3_split fun pref' m3 hprefL hbdP hm3' => ?_
                      have hprefL' : pref'.length = end'.toNat := by
                        rw [hprefL, List.length_take_of_le (by omega)]
                      let trc4 := pref' ++ trc3.drop end'.toNat
                      have htrc4L : trc4.length = 2 * c.max_vars := by
                        dsimp only [trc4]
                        rw [List.length_append, hprefL', List.length_drop, htrc3L]; omega
                      have hbd4L : ∀ i < nc.toNat,
                          (trc4[i]?.getD 0#32).toNat < s.core.cur_vars := by
                        intro i hi; by_cases hie : i < end'.toNat
                        · dsimp only [trc4]
                          rw [List.getElem?_append_left (by rw [hprefL']; exact hie)]
                          exact hbdP i hie
                        · dsimp only [trc4]
                          rw [List.getElem?_append_right (by rw [hprefL']; omega),
                            hprefL', List.getElem?_drop]
                          have heq : end'.toNat + (i - end'.toNat) = i := by omega
                          rw [heq]; exact hbd3L i hi
                      have hm4 : (FullMem c { s with scratch :=
                          { s.scratch with tarjan_reach := trc4, work_stk2 := ws2 } } ⋆ R) m3 := by
                        have hm3_arr : (array (t := i32) c.pTarjanReach trc4 ⋆
                            array (t := i32) c.pWorkStk2 ws2 ⋆
                            S13CandsFrame c { s with scratch :=
                              { s.scratch with tarjan_reach := trc2, work_stk2 := ws2 } } ⋆
                            R) m3 := by
                          have hm3a : ((array (t := i32) c.pTarjanReach pref' ⋆
                              array (t := i32) (c.pTarjanReach + BitVec.ofNat 64 (4 * end'.toNat))
                                (trc3.drop end'.toNat)) ⋆
                              array (t := i32) c.pWorkStk2 ws2 ⋆
                              S13CandsFrame c { s with scratch :=
                                { s.scratch with tarjan_reach := trc2, work_stk2 := ws2 } } ⋆
                              R) m3 := sep_ac hm3'
                          rwa [s13_join_array hprefL'] at hm3a
                        rw [s13_fullMem_eq_candsFrame, s13_candsFrame_irrel]
                        exact sep_ac hm3_arr
                      c0_hsteps_nogrp
                      exact hJe end' m3 (by omega)
                        ⟨by omega, by omega, trc4, htrc4L, hbd4L, hm4⟩))))
    (fun Jcur hJcur => by
      c0_hsplit
      · c0_hsteps_nogrp; exact hJcur 0#64 m ⟨rfl, hcv_pos⟩
      · have hlt : ¬ (BitVec.ofNat 64 s.core.cur_vars).toNat ≤
            ((s.scratch.glue_used[30]'(by omega)).setWidth 64).toNat := by assumption
        rw [hcv_mod] at hlt
        c0_hsteps_nogrp; exact hJcur _ m ⟨rfl, Nat.lt_of_not_le hlt⟩)

/-! ## 2. `full_dense_bin_roundtrip_fid` & `full_dense_bin_sort_roundtrip_fid` -/

@[expose] def S13ModeSliceOk (F_cur : List (List Nat)) (k : FullCoreState)
    (lit p rem : Nat) : Prop :=
  if k.dense_mode = 0#64 then WatchSliceOk F_cur k lit p rem
  else DenseWatchSliceOk F_cur k lit p rem

theorem s13_modeSlice_of_inv {F_cur : List (List Nat)} {k : FullCoreState}
    (hmw : ModeWatchesInv F_cur k) {l : Nat} (hl : l < 2 * k.cur_vars) :
    S13ModeSliceOk F_cur k l (fullWatchOffCore k l) (fullWatchSizeCore k l) := by
  unfold ModeWatchesInv at hmw; unfold S13ModeSliceOk
  by_cases hc : k.dense_mode = 0#64
  · simp only [hc, ↓reduceIte] at hmw ⊢
    exact hmw.slices l hl
  · simp only [hc, ↓reduceIte] at hmw ⊢
    exact hmw.slices l hl

theorem s13_modeSlice_step_bin {F_cur : List (List Nat)} {k : FullCoreState}
    {l p rem : Nat} {w0 : BitVec 32} (h : S13ModeSliceOk F_cur k l p rem)
    (hrem : 0 < rem) (hw0 : k.wstk[p]? = some w0)
    (hbin : (w0 &&& 0x80000000#32) ≠ 0#32) :
    w0 ≠ 0xFFFFFFFF#32 ∧ (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k.cur_vars ∧
    (cnfOfClauses F_cur).EntailsClause (cnfClause [l, (w0 &&& 0x7FFFFFFF#32).toNat]) ∧
    S13ModeSliceOk F_cur k l (p + 1) (rem - 1) := by
  unfold S13ModeSliceOk at h ⊢
  by_cases hc : k.dense_mode = 0#64
  · simp only [hc, ↓reduceIte] at h ⊢
    cases h with
    | empty => omega
    | bin hp hf hne hlt hent hnext =>
      rw [hw0] at hp; cases Option.some.inj hp
      exact ⟨hne, hlt, hent, hnext⟩
    | large hp _ hf _ _ _ =>
      rw [hw0] at hp; cases Option.some.inj hp; exact absurd hf hbin
  · simp only [hc, ↓reduceIte] at h ⊢
    cases h with
    | empty => omega
    | bin hp hf hne hlt hent hnext =>
      rw [hw0] at hp; cases Option.some.inj hp
      exact ⟨hne, hlt, hent, hnext⟩
    | occ hp _ hf _ _ _ _ =>
      rw [hw0] at hp; cases Option.some.inj hp; exact absurd hf hbin

private theorem s13_lt31_and_high {x : BitVec 32} (hx : x.toNat < 2 ^ 31) :
    (x &&& 0x80000000#32) = 0#32 := by
  have hand : (x &&& 0x7FFFFFFF#32) = x := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, show (0x7FFFFFFF#32 : BitVec 32).toNat = 2 ^ 31 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hx]
  rw [← hand, BitVec.and_assoc, show (0x7FFFFFFF#32 &&& 0x80000000#32) = 0#32 by decide,
    BitVec.and_zero]

theorem s13_modeSlice_step_nonbin {F_cur : List (List Nat)} {k : FullCoreState}
    {l p rem : Nat} {w0 : BitVec 32} (h : S13ModeSliceOk F_cur k l p rem)
    (hrem : 0 < rem) (hw0 : k.wstk[p]? = some w0)
    (hnb : (w0 &&& 0x80000000#32) = 0#32) :
    2 ≤ rem ∧ (∃ w1 : BitVec 32, k.wstk[p + 1]? = some w1 ∧
      (w1 &&& 0x80000000#32) = 0#32) ∧
    S13ModeSliceOk F_cur k l (p + 2) (rem - 2) := by
  unfold S13ModeSliceOk at h ⊢
  by_cases hc : k.dense_mode = 0#64
  · simp only [hc, ↓reduceIte] at h ⊢
    cases h with
    | empty => omega
    | bin hp hf _ _ _ _ =>
      rw [hw0] at hp; cases Option.some.inj hp; exact absurd hnb hf
    | @large _ _ _ cref hp hp1 _ hlt _ hnext =>
      rw [hw0] at hp; cases Option.some.inj hp
      exact ⟨by omega, ⟨cref, hp1, s13_lt31_and_high hlt⟩, hnext⟩
  · simp only [hc, ↓reduceIte] at h ⊢
    cases h with
    | empty => omega
    | bin hp hf _ _ _ _ =>
      rw [hw0] at hp; cases Option.some.inj hp; exact absurd hnb hf
    | @occ _ _ _ cref hp hp1 _ _ hlt _ hnext =>
      rw [hw0] at hp; cases Option.some.inj hp
      exact ⟨by omega, ⟨cref, hp1, s13_lt31_and_high hlt⟩, hnext⟩

private theorem s13_bin_word_props {x : BitVec 32} (hx : x.toNat < 2 ^ 30) :
    let w := (x &&& 0x7FFFFFFF#32) ||| 0x80000000#32
    (w &&& 0x80000000#32) ≠ 0#32 ∧ w ≠ 0xFFFFFFFF#32 ∧ (w &&& 0x7FFFFFFF#32) = x := by
  have hx_lt : x.toNat < 2 ^ 31 := by omega
  have hand : (x &&& 0x7FFFFFFF#32) = x := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, show (0x7FFFFFFF#32 : BitVec 32).toNat = 2 ^ 31 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hx_lt]
  have hbit : (x &&& 0x80000000#32) = 0#32 := by
    rw [← hand, BitVec.and_assoc, show (0x7FFFFFFF#32 &&& 0x80000000#32) = 0#32 by decide,
      BitVec.and_zero]
  have hf : (((x &&& 0x7FFFFFFF#32) ||| 0x80000000#32) &&& 0x80000000#32) ≠ 0#32 := by
    rw [hand]; intro heq
    have h31 := congrArg (·[31]) heq
    simp at h31
  have hne : ((x &&& 0x7FFFFFFF#32) ||| 0x80000000#32) ≠ 0xFFFFFFFF#32 := by
    rw [hand]; intro heq
    have : (x ||| 0x80000000#32) &&& 0x7FFFFFFF#32 = 0x7FFFFFFF#32 := by rw [heq]; decide
    have hdisj : (x ||| 0x80000000#32) &&& 0x7FFFFFFF#32 = x := by
      ext i hi; simp only [BitVec.getElem_and, BitVec.getElem_or]
      by_cases h31 : i = 31
      · subst h31; have hxb := congrArg (·[31]) hbit; simp at hxb; simp [hxb]
      · have h0 : (0x80000000#32 : BitVec 32)[i] = false := by revert i hi h31; decide
        have h1 : (0x7FFFFFFF#32 : BitVec 32)[i] = true := by revert i hi h31; decide
        simp [h0, h1]
    rw [hdisj] at this; rw [this] at hx; revert hx; decide
  have hmask : (((x &&& 0x7FFFFFFF#32) ||| 0x80000000#32) &&& 0x7FFFFFFF#32) = x := by
    rw [hand]; ext i hi; simp only [BitVec.getElem_and, BitVec.getElem_or]
    by_cases h31 : i = 31
    · subst h31; have hxb := congrArg (·[31]) hbit; simp at hxb; simp [hxb]
    · have h0 : (0x80000000#32 : BitVec 32)[i] = false := by revert i hi h31; decide
      have h1 : (0x7FFFFFFF#32 : BitVec 32)[i] = true := by revert i hi h31; decide
      simp [h0, h1]
  exact ⟨hf, hne, hmask⟩

@[expose] def BinPairsOk (c : FullCfg) (F_cur : List (List Nat)) (s : FullState)
    (nb : Nat) (scr : List (BitVec 32)) : Prop :=
  scr.length = c.scratch_cap ∧ 2 * nb ≤ c.scratch_cap ∧
  ∀ i < nb,
    let a := scr[2 * i]?.getD 0#32
    let b := scr[2 * i + 1]?.getD 0#32
    a.toNat < 2 * s.core.cur_vars ∧ b.toNat < 2 * s.core.cur_vars ∧
    (cnfOfClauses F_cur).EntailsClause (cnfClause [a.toNat, b.toNat])

theorem s13_binPairsOk_push {c : FullCfg} {F_cur : List (List Nat)} {s : FullState}
    {nb : Nat} {scr : List (BitVec 32)} (h : BinPairsOk c F_cur s nb scr)
    (hlt : 2 * nb + 1 < c.scratch_cap) {a b : BitVec 32}
    (ha : a.toNat < 2 * s.core.cur_vars) (hb : b.toNat < 2 * s.core.cur_vars)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [a.toNat, b.toNat])) :
    BinPairsOk c F_cur s (nb + 1) ((scr.set (2 * nb) a).set (2 * nb + 1) b) := by
  refine ⟨by simp [h.1], by omega, fun i hi => ?_⟩
  by_cases hin : i = nb
  · subst hin; dsimp only
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by rw [h.1]; omega),
      List.getElem?_set_self (by simp [h.1]; omega), Option.getD_some, Option.getD_some]
    exact ⟨ha, hb, hent⟩
  · dsimp only
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
    exact h.2.2 i (by omega)

theorem s13_binPairsOk_set {c : FullCfg} {F_cur : List (List Nat)} {s : FullState}
    {nb : Nat} {scr : List (BitVec 32)} (h : BinPairsOk c F_cur s nb scr)
    {dst : Nat} (hdst : dst < nb) {a b : BitVec 32}
    (ha : a.toNat < 2 * s.core.cur_vars) (hb : b.toNat < 2 * s.core.cur_vars)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [a.toNat, b.toNat])) :
    BinPairsOk c F_cur s nb ((scr.set (2 * dst) a).set (2 * dst + 1) b) := by
  refine ⟨by simp [h.1], h.2.1, fun i hi => ?_⟩
  by_cases hid : i = dst
  · subst hid; dsimp only
    have hsl := h.1; have h2nb := h.2.1
    have hs1 : (scr.set (2 * i) a).length = scr.length := List.length_set
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega),
      List.getElem?_set_self (by omega), Option.getD_some, Option.getD_some]
    exact ⟨ha, hb, hent⟩
  · dsimp only
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
    exact h.2.2 i hi

private theorem s13_empty_modeWatchesInv {c : FullCfg} {F_cur : List (List Nat)} {k : FullCoreState}
    (_hwvec : k.wvec.length = 4 * c.max_vars) (_hcv : k.cur_vars ≤ c.max_vars)
    (hwl : k.wlen = 1)
    (hz : ∀ l < 2 * k.cur_vars, k.wvec[2 * l]? = some 0#32 ∧ k.wvec[2 * l + 1]? = some 0#32) :
    ModeWatchesInv F_cur k := by
  have hlay : WatchStackLayout k :=
    ⟨fun l hl => by
       obtain ⟨h0, h1⟩ := hz l hl
       simp only [fullWatchOffCore, fullWatchSizeCore, h0, h1, Option.getD_some, hwl]
       decide,
     fun l hl hpos => by
       obtain ⟨_, h1⟩ := hz l hl
       simp only [fullWatchSizeCore, h1, Option.getD_some] at hpos
       exact absurd hpos (by decide),
     fun l1 _ hl1 _ _ hp1 _ => by
       obtain ⟨_, h1⟩ := hz l1 hl1
       simp only [fullWatchSizeCore, h1, Option.getD_some] at hp1
       exact absurd hp1 (by decide),
     fun l hl idx hidx => by
       obtain ⟨_, h1⟩ := hz l hl
       simp only [fullWatchSizeCore, h1, Option.getD_some] at hidx
       simp at hidx⟩
  unfold ModeWatchesInv
  by_cases hc : k.dense_mode = 0#64 <;> simp only [hc, ↓reduceIte]
  · refine ⟨hlay, fun l hl => ?_⟩
    obtain ⟨_, h1⟩ := hz l hl
    simp only [fullWatchSizeCore, h1, Option.getD_some]; exact .empty
  · refine ⟨hlay, fun l hl => ?_⟩
    obtain ⟨_, h1⟩ := hz l hl
    simp only [fullWatchSizeCore, h1, Option.getD_some]; exact .empty

private theorem s13_bin_roundtrip_call_push {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (hPush : ∀ a m Q X, Full.fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {a b : BitVec 32} {R : Mem 64 → Prop} {m : Mem 64}
    {cont : Tup Val [.bool] → Expr Val Cont rs}
    (hlen : s.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core)
    (_ha_lt : a.toNat < 2 * s.core.cur_vars) (hb_lt : b.toNat < 2 * s.core.cur_vars)
    (hb_bd : b.toNat < 2 ^ 30)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [a.toNat, b.toNat]))
    (hm : (FullMem c s ⋆ R) m)
    (hk : ∀ (ok : Bool) (s' : FullState) (m' : Mem 64),
      s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
      s'.core.cur_vars = s.core.cur_vars → s'.core.cur_level = s.core.cur_level →
      s'.core.dense_mode = s.core.dense_mode →
      s'.core.arena = s.core.arena → s'.core.arena_len = s.core.arena_len →
      s'.core.vals = s.core.vals → s'.core.lvl = s.core.lvl → s'.core.flags = s.core.flags →
      s'.core.fuel = s.core.fuel → s'.core.inconsistent = s.core.inconsistent →
      s'.core.d_cur = s.core.d_cur → s'.core.d_val = s.core.d_val →
      s'.core.frame_trail = s.core.frame_trail → s'.core.frame_dec = s.core.frame_dec →
      s'.core.trail_end = s.core.trail_end → s'.core.propagated = s.core.propagated →
      s'.core.probing = s.core.probing →
      s'.scratch.extend_len = s.scratch.extend_len →
      s'.scratch.walk_vals = s.scratch.walk_vals →
      s'.scratch.walk_best = s.scratch.walk_best →
      s'.scratch.last_learned = s.scratch.last_learned →
      s'.scratch.scratch_buf = s.scratch.scratch_buf →
      s'.core.lit_mark = s.core.lit_mark → s'.core.mrk = s.core.mrk →
      (FullMem c s' ⋆ R) m' → wp Γ Q X (cont (ok, ())) m') :
    wp Γ Q X (Expr.call (as := [i64, i32, i32, i32, i32]) (bs := [.bool])
      "full_watch_push"
      (Arg.var c.hdr, Arg.var a, Arg.var ((b &&& 0x7FFFFFFF#32) ||| 0x80000000#32),
        Arg.imm 0, Arg.imm 1, ()) cont) m := by
  have hwp := s13_bin_word_props hb_bd
  refine wp_call_of_spec _ cont
    (hPush (c.hdr, a, (b &&& 0x7FFFFFFF#32) ||| 0x80000000#32, 0#32, 1#32, ()) m
      (fun r m' => wp Γ Q X (cont r) m') X
      ⟨c, s, R, rfl, hlen, hw.watches.layout, fun _ => hwp.2.1,
        fun h => by exfalso; revert h; decide, hm, ?_⟩)
  intro ok wvec' wstk' wlen' wu' ws' m' _ hlen' hlay' hoth' hokT' hokF' hm'
  let s' : FullState :=
    { s with
      core := { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' }
      scratch := { s.scratch with wsort := ws' } }
  have hwat' : ModeWatchesInv F_cur s'.core :=
    fullWatchPush_preserves_modeWatchesInv hw.watches hlay' rfl rfl (fun _ hr => hr)
      (fun _ => ⟨hwp.1, hwp.2.1, by rw [hwp.2.2]; exact hb_lt,
        by rw [hwp.2.2]; exact hent⟩)
      (fun h2 => by exfalso; revert h2; decide)
      hoth' hokT' (fun hf ha => (hokF' hf).1 ha)
  have hw' : FullWitnessInv c F0 F_cur s'.core :=
    { hw with arena := { hw.arena with len_ok := hw.arena.len_ok }, watches := hwat' }
  exact hk ok s' m' hlen' hw' rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl rfl rfl hm'

theorem s13_bin_roundtrip_emit_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (hPush : ∀ a m Q X, Full.fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {nb : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64}
    {exitE : Expr Val Cont rs}
    (hlen : s.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core)
    (hlm : FullLitMarksClear c s) (hnd : FullArenaVarsNodup s) (hext : FullExtScratchOk c s)
    (hwcap : 0 < c.wcap) (hcv_bd : 2 * s.core.cur_vars < 2 ^ 30)
    (hbp : BinPairsOk c F_cur s nb.toNat s.scratch.scratch_buf) (hm : (FullMem c s ⋆ R) m)
    (hExit : ∀ (s' : FullState) (m' : Mem 64),
      s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
      FullLitMarksClear c s' → FullArenaVarsNodup s' → FullExtScratchOk c s' →
      s'.core.cur_vars = s.core.cur_vars → s'.core.cur_level = s.core.cur_level →
      s'.core.dense_mode = s.core.dense_mode →
      s'.core.arena = s.core.arena → s'.core.arena_len = s.core.arena_len →
      s'.core.vals = s.core.vals → s'.core.lvl = s.core.lvl → s'.core.flags = s.core.flags →
      s'.core.fuel = s.core.fuel → s'.core.inconsistent = s.core.inconsistent →
      s'.core.d_cur = s.core.d_cur → s'.core.d_val = s.core.d_val →
      s'.core.frame_trail = s.core.frame_trail → s'.core.frame_dec = s.core.frame_dec →
      s'.core.trail_end = s.core.trail_end → s'.core.propagated = s.core.propagated →
      s'.core.probing = s.core.probing →
      s'.scratch.extend_len = s.scratch.extend_len →
      s'.scratch.walk_vals = s.scratch.walk_vals →
      s'.scratch.walk_best = s.scratch.walk_best →
      s'.scratch.last_learned = s.scratch.last_learned →
      (FullMem c s' ⋆ R) m' → wp Γ Q X exitE m') :
    let nlits : BitVec 64 := BitVec.ofNat 64 s.core.cur_vars <<< 1#64
    let pwvec : Val i64 := c.pWvec
    let pwstk : Val i64 := c.pWstk
    let ppairs : Val i64 := c.pScratchBuf
    wp Γ Q X
      (Expr.group (sig := [[i64]]) (fun Js =>
        Blocks.cons (fun (l, ()) =>
          Expr.let_ (Op.mk (.cmp .ult i64 .bool rfl) (Arg.var l, Arg.var nlits, ()))
            (fun (bl, ()) =>
          Expr.jnz (Arg.var bl)
            (Expr.let_ (Op.mk (.sext 32 64) (Arg.imm 1, ())) (fun (c1, ()) =>
            Expr.let_ (Op.mk (.shl i64) (Arg.var l, Arg.var c1, ())) (fun (l2, ()) =>
            Expr.let_ (Op.mk (.mul i64) (Arg.var l2, Arg.imm 4, ())) (fun (o0, ()) =>
            Expr.let_ (Op.mk (.add i64) (Arg.var pwvec, Arg.var o0, ())) (fun (a0, ()) =>
            Expr.store (t := i32) (Arg.imm 0) (Arg.var a0)
              (Expr.let_ (Op.mk (.sext 32 64) (Arg.imm 1, ())) (fun (c1b, ()) =>
              Expr.let_ (Op.mk (.shl i64) (Arg.var l, Arg.var c1b, ())) (fun (l2b, ()) =>
              Expr.let_ (Op.mk (.add i64) (Arg.var l2b, Arg.imm 1, ())) (fun (l2p, ()) =>
              Expr.let_ (Op.mk (.mul i64) (Arg.var l2p, Arg.imm 4, ())) (fun (o1, ()) =>
              Expr.let_ (Op.mk (.add i64) (Arg.var pwvec, Arg.var o1, ())) (fun (a1, ()) =>
              Expr.store (t := i32) (Arg.imm 0) (Arg.var a1)
                (Expr.let_ (Op.mk (.add i64) (Arg.var l, Arg.imm 1, ())) (fun (ln, ()) =>
                Expr.jump Js.fst (Arg.var ln, ()))))))))))))))
            (Expr.let_ (Op.mk (.sext 32 64) (Arg.imm 0, ())) (fun (z0, ()) =>
            Expr.let_ (Op.mk (.mul i64) (Arg.var z0, Arg.imm 4, ())) (fun (oz, ()) =>
            Expr.let_ (Op.mk (.add i64) (Arg.var pwstk, Arg.var oz, ())) (fun (az, ()) =>
            Expr.store (t := i32) (Arg.imm 0) (Arg.var az)
              (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 56, ())) (fun (pwl, ()) =>
              Expr.store (t := i64) (Arg.imm 1) (Arg.var pwl)
                (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 464, ())) (fun (pwu, ()) =>
                Expr.store (t := i64) (Arg.imm 0) (Arg.var pwu)
                  (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 504, ()))
                    (fun (pnb, ()) =>
                  Expr.store (t := i64) (Arg.var nb) (Arg.var pnb)
                    (Expr.group (sig := [[i64]]) (fun Jk =>
                      Blocks.cons (fun (k, ()) =>
                        Expr.let_ (Op.mk (.cmp .ult i64 .bool rfl) (Arg.var k, Arg.var nb, ()))
                          (fun (bk, ()) =>
                        Expr.jnz (Arg.var bk)
                          (Expr.let_ (Op.mk (.sext 32 64) (Arg.imm 1, ())) (fun (c1, ()) =>
                          Expr.let_ (Op.mk (.shl i64) (Arg.var k, Arg.var c1, ()))
                            (fun (k2, ()) =>
                          Expr.let_ (Op.mk (.mul i64) (Arg.var k2, Arg.imm 4, ()))
                            (fun (ok0, ()) =>
                          Expr.let_ (Op.mk (.add i64) (Arg.var ppairs, Arg.var ok0, ()))
                            (fun (ak0, ()) =>
                          Expr.load i32 (Arg.var ak0) (fun a =>
                          Expr.let_ (Op.mk (.sext 32 64) (Arg.imm 1, ())) (fun (c1b, ()) =>
                          Expr.let_ (Op.mk (.shl i64) (Arg.var k, Arg.var c1b, ()))
                            (fun (k2b, ()) =>
                          Expr.let_ (Op.mk (.add i64) (Arg.var k2b, Arg.imm 1, ()))
                            (fun (k2p, ()) =>
                          Expr.let_ (Op.mk (.mul i64) (Arg.var k2p, Arg.imm 4, ()))
                            (fun (ok1, ()) =>
                          Expr.let_ (Op.mk (.add i64) (Arg.var ppairs, Arg.var ok1, ()))
                            (fun (ak1, ()) =>
                          Expr.load i32 (Arg.var ak1) (fun b =>
                          Expr.let_ (Op.mk (.and i32) (Arg.var b, Arg.imm 0x7FFFFFFF, ()))
                            (fun (bm, ()) =>
                          Expr.let_ (Op.mk (.or i32) (Arg.var bm, Arg.imm 0x80000000, ()))
                            (fun (wb, ()) =>
                          Expr.call (as := [i64, i32, i32, i32, i32]) (bs := [.bool])
                            "full_watch_push"
                            (Arg.var c.hdr, Arg.var a, Arg.var wb, Arg.imm 0, Arg.imm 1, ())
                            (fun (_, ()) =>
                          Expr.let_ (Op.mk (.and i32) (Arg.var a, Arg.imm 0x7FFFFFFF, ()))
                            (fun (am, ()) =>
                          Expr.let_ (Op.mk (.or i32) (Arg.var am, Arg.imm 0x80000000, ()))
                            (fun (wa, ()) =>
                          Expr.call (as := [i64, i32, i32, i32, i32]) (bs := [.bool])
                            "full_watch_push"
                            (Arg.var c.hdr, Arg.var b, Arg.var wa, Arg.imm 0, Arg.imm 1, ())
                            (fun (_, ()) =>
                          Expr.let_ (Op.mk (.add i64) (Arg.var k, Arg.imm 1, ()))
                            (fun (kn, ()) =>
                          Expr.jump Jk.fst (Arg.var kn, ()))))))))))))))))))))
                          exitE))
                      Blocks.nil) (fun Jk => Expr.jump Jk.fst (Arg.imm 0, ())))))))))))))))
        Blocks.nil) (fun Js => Expr.jump Js.fst (Arg.imm 0, ()))) m := by
  intro nlits pwvec pwstk ppairs
  have hcv_le := hlen.core_ok.cur_vars_le
  have hwv_len := hlen.core_ok.wvec_len
  have hws_len := hlen.core_ok.wstk_len_arr
  have hnlits : nlits.toNat = 2 * s.core.cur_vars := by
    dsimp only [nlits]
    have hmx := c.hmaxv; unfold dimacsBound at hmx
    rw [show BitVec.ofNat 64 s.core.cur_vars <<< 1#64 =
        BitVec.ofNat 64 s.core.cur_vars <<< (1 : Nat) from rfl,
      BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64),
      Nat.shiftLeft_eq, Nat.pow_one,
      Nat.mod_eq_of_lt (by omega : s.core.cur_vars * 2 < 2 ^ 64)]; omega
  refine wp_loop_inv (ts := [i64])
    (fun (l, ()) mL => l.toNat ≤ 2 * s.core.cur_vars ∧ ∃ wvecL : List (BitVec 32),
      wvecL.length = 4 * c.max_vars ∧
      (∀ i < l.toNat, wvecL[2 * i]? = some 0#32 ∧ wvecL[2 * i + 1]? = some 0#32) ∧
      (FullMem c { s with core := { s.core with wvec := wvecL } } ⋆ R) mL)
    (fun (l, ()) _ => 2 * s.core.cur_vars - l.toNat)
    (fun Js hLoopL => by
      c0_hsteps_nogrp
      exact hLoopL (0#64, ()) m ⟨Nat.zero_le _, s.core.wvec, hwv_len, fun _ h => by simp at h, hm⟩)
    (fun Js ⟨l, ⟨⟩⟩ mL ⟨hl_le, wvecL, hwvL, hzeroL, hmL⟩ hLoopL => ?_)
  c0_hsplit
  · have hl_lt : l.toNat < 2 * s.core.cur_vars := by rw [← hnlits]; exact hc
    have hidx0 : (l <<< 1#64).toNat = 2 * l.toNat := by
      have hmx := c.hmaxv; unfold dimacsBound at hmx
      rw [show l <<< 1#64 = l <<< (1 : Nat) from rfl, BitVec.toNat_shiftLeft,
        Nat.shiftLeft_eq, Nat.pow_one,
        Nat.mod_eq_of_lt (by omega : l.toNat * 2 < 2 ^ 64)]; omega
    have hidx1 : ((l <<< 1#64) + 1#64).toNat = 2 * l.toNat + 1 := by
      have hmx := c.hmaxv; unfold dimacsBound at hmx
      rw [BitVec.toNat_add, hidx0, show (1#64 : BitVec 64).toNat = 1 from rfl,
        Nat.mod_eq_of_lt (by omega)]
    have h0_lt : (l <<< 1#64).toNat <
        ({ s with core := { s.core with wvec := wvecL } }).core.wvec.length := by
      dsimp only; omega
    let w1 := wvecL.set (l <<< 1#64).toNat 0#32
    have h1_lt : ((l <<< 1#64) + 1#64).toNat <
        ({ s with core := { s.core with wvec := w1 } }).core.wvec.length := by
      dsimp only [w1]; rw [List.length_set]; omega
    have hl1 : (l + 1#64).toNat = l.toNat + 1 := by bv_omega
    c0_hsteps_nogrp
    have hmL' : (FullMem c { s with core := { s.core with
        wvec := (wvecL.set (2 * l.toNat) 0#32).set (2 * l.toNat + 1) 0#32 } } ⋆ R) m := by
      change (FullMem c { s with core := { s.core with
          wvec := (wvecL.set (l <<< 1#64).toNat 0#32).set
            ((l <<< 1#64 + 1#64).toNat) 0#32 } } ⋆ R) m at hm
      rw [hidx0, hidx1] at hm
      exact hm
    exact hLoopL (l + 1#64, ()) _ (by dsimp only; omega)
      ⟨by omega, _, by simp [hwvL], fun i hi => by
        by_cases hil : i = l.toNat
        · subst hil
          rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega),
            List.getElem?_set_self (by simp [hwvL]; omega)]; exact ⟨rfl, rfl⟩
        · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
            List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
          exact hzeroL i (by omega),
       hmL'⟩
  · have hl_eq : l.toNat = 2 * s.core.cur_vars := by
      have hlt : ¬ l.toNat < nlits.toNat := hc
      omega
    clear hLoopL Js
    have h0_ws : (BitVec.ofNat 64 (0#32 : BitVec 32).toNat).toNat <
        ({ s with core := { s.core with wvec := wvecL } }).core.wstk.length := by
      dsimp only; rw [hws_len]
      simp only [BitVec.toNat_ofNat, Nat.zero_mod]; exact hwcap
    have hmL_f : (FullMem c { s with core := { s.core with wvec := wvecL } } ⋆ R) mL := hmL
    c0_hsteps_nogrp
    let wstk0 := s.core.wstk.set 0 0#32
    let s0 : FullState :=
      { s with core := { s.core with wvec := wvecL, wstk := wstk0, wlen := 1,
                                     wusable := 0#64, num_binary := nb } }
    have hws_a : wstk0.length = c.wcap := by simp [wstk0, hws_len]
    have hwl_l : 1 ≤ c.wcap := hwcap
    have hlen0 : s0.LengthsOk c :=
      ⟨{ hlen.core_ok with wvec_len := hwvL, wstk_len_arr := hws_a, wlen_le := hwl_l },
       hlen.scratch_ok⟩
    have hwat0 : ModeWatchesInv F_cur s0.core :=
      s13_empty_modeWatchesInv hwvL hcv_le rfl fun i hi => by
        dsimp only [s0] at hi; exact hzeroL i (by omega)
    have hw0 : FullWitnessInv c F0 F_cur s0.core :=
      { hw with arena := { hw.arena with len_ok := hw.arena.len_ok }, watches := hwat0 }
    have hbp0 : BinPairsOk c F_cur s0 nb.toNat s0.scratch.scratch_buf :=
      ⟨hbp.1, hbp.2.1, fun i hi => hbp.2.2 i hi⟩
    refine wp_loop_inv (ts := [i64])
      (fun (k, ()) mK => k.toNat ≤ nb.toNat ∧ ∃ sK : FullState,
        sK.LengthsOk c ∧ FullWitnessInv c F0 F_cur sK.core ∧
        sK.core.cur_vars = s.core.cur_vars ∧ sK.core.cur_level = s.core.cur_level ∧
        sK.core.dense_mode = s.core.dense_mode ∧ sK.core.arena = s.core.arena ∧
        sK.core.arena_len = s.core.arena_len ∧ sK.core.vals = s.core.vals ∧
        sK.core.lvl = s.core.lvl ∧ sK.core.flags = s.core.flags ∧
        sK.core.fuel = s.core.fuel ∧ sK.core.inconsistent = s.core.inconsistent ∧
        sK.core.d_cur = s.core.d_cur ∧ sK.core.d_val = s.core.d_val ∧
        sK.core.frame_trail = s.core.frame_trail ∧ sK.core.frame_dec = s.core.frame_dec ∧
        sK.core.trail_end = s.core.trail_end ∧ sK.core.propagated = s.core.propagated ∧
        sK.core.probing = s.core.probing ∧
        sK.scratch.extend_len = s.scratch.extend_len ∧
        sK.scratch.walk_vals = s.scratch.walk_vals ∧
        sK.scratch.walk_best = s.scratch.walk_best ∧
        sK.scratch.last_learned = s.scratch.last_learned ∧
        sK.scratch.scratch_buf = s.scratch.scratch_buf ∧
        sK.core.lit_mark = s.core.lit_mark ∧ sK.core.mrk = s.core.mrk ∧
        (FullMem c sK ⋆ R) mK)
      (fun (k, ()) _ => nb.toNat - k.toNat)
      (fun Jk hLoopK => by
        c0_hsteps_nogrp
        refine hLoopK (0#64, ()) _ ⟨Nat.zero_le _, s0, hlen0, hw0, rfl, rfl, rfl, rfl, rfl,
          rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
          rfl, ?_⟩
        let wstk0_c0 := s.core.wstk.set (BitVec.setWidth 64 0#32).toNat 0#32
        let s0_c0 : FullState :=
          { s with core := { s.core with wvec := wvecL, wstk := wstk0_c0,
                                         wlen := (1#64).toNat, wusable := 0#64, num_binary := nb } }
        change (FullMem c s0_c0 ⋆ R) _ at *; exact (by assumption))
      (fun Jk ⟨k, ⟨⟩⟩ mK ⟨hk_le, sK, hlenK, hwK, hcvK, hclK, hdmK, harK, halK, hvalK, hlvlK,
          hflK, hfuK, hincK, hdcK, hdvK, hftK, hfdK, hteK, hprK, hprbK, helK, hwvK, hwbK, hllK,
          hsbK, hlmkK, hmrkK, hmK⟩ hLoopK => ?_)
    c0_hsplit
    · have hk_lt : k.toNat < nb.toNat := hc
      have hnb_bd : 2 * nb.toNat ≤ c.scratch_cap := hbp.2.1
      have hsc_cap := c.hscr; unfold dimacsBound at hsc_cap
      have hsc_len : sK.scratch.scratch_buf.length = c.scratch_cap :=
        hlenK.scratch_ok.scratch_buf_len
      have hk0 : (k <<< 1#64).toNat = 2 * k.toNat := by
        rw [show k <<< 1#64 = k <<< (1 : Nat) from rfl, BitVec.toNat_shiftLeft,
          Nat.shiftLeft_eq, Nat.pow_one, Nat.mod_eq_of_lt (by omega)]; omega
      have hk1 : ((k <<< 1#64) + 1#64).toNat = 2 * k.toNat + 1 := by
        rw [BitVec.toNat_add, hk0, show (1#64 : BitVec 64).toNat = 1 from rfl,
          Nat.mod_eq_of_lt (by omega)]
      have ha_lt : (k <<< 1#64).toNat < sK.scratch.scratch_buf.length := by omega
      have hb_lt : ((k <<< 1#64) + 1#64).toNat < sK.scratch.scratch_buf.length := by omega
      obtain ⟨hpa, hpb, hpent⟩ := hbp.2.2 k.toNat hk_lt
      have hk0_gen : (k <<< OfNat.ofNat 1).toNat = 2 * k.toNat := by
        rw [show (k <<< OfNat.ofNat 1) = k <<< 1#64 from rfl, hk0]
      have hk1_gen : (k <<< OfNat.ofNat 1 + (1 : BitVec 64)).toNat = 2 * k.toNat + 1 := by
        rw [show (k <<< OfNat.ofNat 1) = k <<< 1#64 from rfl,
          show (1 : BitVec 64) = 1#64 from rfl, hk1]
      have hsc_get : ∀ (sX : FullState) (hsX : sX.scratch.scratch_buf = s.scratch.scratch_buf)
          (idx mIdx : Nat) (hEq : idx = mIdx) (hBd : idx < sX.scratch.scratch_buf.length),
          sX.scratch.scratch_buf[idx]'hBd = s.scratch.scratch_buf[mIdx]?.getD 0#32 := by
        intro sX hsX idx mIdx hEq hBd
        have hBd' : mIdx < s.scratch.scratch_buf.length := by rw [← hsX, ← hEq]; exact hBd
        rw [List.getElem?_eq_getElem hBd', Option.getD_some]
        apply Option.some.inj
        rw [← List.getElem?_eq_getElem hBd, ← List.getElem?_eq_getElem hBd', hsX, hEq]
      have ha_k : ∀ (hBd : (k <<< OfNat.ofNat 1).toNat < sK.scratch.scratch_buf.length),
          sK.scratch.scratch_buf[(k <<< OfNat.ofNat 1).toNat]'hBd =
          s.scratch.scratch_buf[2 * k.toNat]?.getD 0#32 :=
        fun hBd => hsc_get sK hsbK _ _ hk0_gen hBd
      have hb_k : ∀ (hBd : (k <<< OfNat.ofNat 1 + (1 : BitVec 64)).toNat <
          sK.scratch.scratch_buf.length),
          sK.scratch.scratch_buf[(k <<< OfNat.ofNat 1 + (1 : BitVec 64)).toNat]'hBd =
          s.scratch.scratch_buf[2 * k.toNat + 1]?.getD 0#32 :=
        fun hBd => hsc_get sK hsbK _ _ hk1_gen hBd
      have hkn : (k + 1#64).toNat = k.toNat + 1 := by bv_omega
      have hpent_sw : (cnfOfClauses F_cur).EntailsClause (cnfClause
          [(s.scratch.scratch_buf[2 * k.toNat + 1]?.getD 0#32).toNat,
           (s.scratch.scratch_buf[2 * k.toNat]?.getD 0#32).toNat]) := by
        rw [CNF.entails_clause_def] at hpent ⊢
        intro α hα
        have h1 := (clauseEvalVal_iff α _).mpr (hpent α hα)
        refine (clauseEvalVal_iff α _).mp ?_
        simpa [clauseEvalVal, List.any_cons, Bool.or_comm] using h1
      c0_hsteps_nogrp
      refine s13_bin_roundtrip_call_push hPush hlenK hwK
        (by rw [ha_k, hcvK]; exact hpa)
        (by rw [hb_k, hcvK]; exact hpb)
        (by rw [hb_k]; omega)
        (by rw [ha_k, hb_k]; exact hpent) hmK ?_
      intro _ok1 sK1 mK1 hlenK1 hwK1 hcvK1 hclK1 hdmK1 harK1 halK1 hvalK1 hlvlK1 hflK1 hfuK1
        hincK1 hdcK1 hdvK1 hftK1 hfdK1 hteK1 hprK1 hprbK1 helK1 hwvK1 hwbK1 hllK1 hsbK1 hlmkK1
        hmrkK1 hmK1
      c0_hsteps_nogrp
      refine s13_bin_roundtrip_call_push hPush hlenK1 hwK1
        (by rw [hb_k, hcvK1, hcvK]; exact hpb)
        (by rw [ha_k, hcvK1, hcvK]; exact hpa)
        (by rw [ha_k]; omega)
        (by rw [ha_k, hb_k]; exact hpent_sw)
        hmK1 ?_
      intro _ok2 sK2 mK2 hlenK2 hwK2 hcvK2 hclK2 hdmK2 harK2 halK2 hvalK2 hlvlK2 hflK2 hfuK2
        hincK2 hdcK2 hdvK2 hftK2 hfdK2 hteK2 hprK2 hprbK2 helK2 hwvK2 hwbK2 hllK2 hsbK2 hlmkK2
        hmrkK2 hmK2
      c0_hsteps_nogrp
      exact hLoopK (k + 1#64, ()) mK2 (by dsimp only; omega)
        ⟨by omega, sK2, hlenK2, hwK2,
         hcvK2.trans (hcvK1.trans hcvK), hclK2.trans (hclK1.trans hclK),
         hdmK2.trans (hdmK1.trans hdmK), harK2.trans (harK1.trans harK),
         halK2.trans (halK1.trans halK), hvalK2.trans (hvalK1.trans hvalK),
         hlvlK2.trans (hlvlK1.trans hlvlK), hflK2.trans (hflK1.trans hflK),
         hfuK2.trans (hfuK1.trans hfuK), hincK2.trans (hincK1.trans hincK),
         hdcK2.trans (hdcK1.trans hdcK), hdvK2.trans (hdvK1.trans hdvK),
         hftK2.trans (hftK1.trans hftK), hfdK2.trans (hfdK1.trans hfdK),
         hteK2.trans (hteK1.trans hteK), hprK2.trans (hprK1.trans hprK),
         hprbK2.trans (hprbK1.trans hprbK), helK2.trans (helK1.trans helK),
         hwvK2.trans (hwvK1.trans hwvK), hwbK2.trans (hwbK1.trans hwbK),
         hllK2.trans (hllK1.trans hllK), hsbK2.trans (hsbK1.trans hsbK),
         hlmkK2.trans (hlmkK1.trans hlmkK), hmrkK2.trans (hmrkK1.trans hmrkK), hmK2⟩
    · c0_hsteps_nogrp
      have hlmK : FullLitMarksClear c sK :=
        ⟨by simpa only [FullMrkZero, hmrkK] using hlm.1,
          fun l hl => by rw [hlmkK]; exact hlm.2 l hl⟩
      have hndK : FullArenaVarsNodup sK := by
        simpa [FullArenaVarsNodup, fullArenaClauseRefs, fullArenaClauseRefsCore,
          fullArenaClauseGarb, fullArenaClauseGarbCore, fullArenaHdrCore, fullArenaClauseLits,
          fullArenaClauseLitsCore, fullArenaClauseSizeCore, harK, halK] using hnd
      have hextK : FullExtScratchOk c sK :=
        FullExtScratchOk.of_pres hext ⟨hllK, by omega⟩
          fun r hr => by
            simpa [fullArenaClauseRefs, fullArenaClauseRefsCore, harK, halK] using hr
      exact hExit sK mK hlenK hwK hlmK hndK hextK
        hcvK hclK hdmK harK halK hvalK hlvlK hflK hfuK hincK hdcK hdvK hftK hfdK hteK hprK hprbK
        helK hwvK hwbK hllK hmK

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S1
