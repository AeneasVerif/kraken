module

public import LeanQbe.T.Examples.Kissat.FullM6CompactFlushProof1
public import LeanQbe.T.Examples.Kissat.FullFastSchedLemmas
import LeanQbe.T.Examples.Kissat.FullReduceLemmas2
import LeanQbe.T.Examples.Kissat.FullDenseWatchLemmas
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb

/-!
# Kissat M6 Compact, Root Trail Flush & Binary Dedup Proofs — Part 2

Parametric `(Γ : Env)` `Func.wp` UNSAT-only proofs (`0` SAT/model proofs):
1. `full_sweep_bins_m6cf_wp` (`Full.fullSweepBinsSpec`): `wsort`-stamped `O(1)` binary clause
   deduplication + tautology drop + empty-offset zeroing + `prop_done` completeness.
2. `full_enter_dense_m6cf_wp` (`FullFastSched.schedEnterDenseSpec`): root backtrack + OOM guard
   + `full_flush_trail` + deduplicating `full_sweep_bins` + dense watch population.
3. `full_compact_mark_live_m6cf_wp` (`FullM4Compact.fullCompactMarkLiveSpec`): isolated-variable
   elimination (`map[v] = 0u` init; mark only unassigned vars occurring in non-tautological
   binary watches or unsatisfied large clauses with `ucnt >= 1`).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.FullM6CompactFlush

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullFastSched
open FullReduceHelpers FullDenseWatchHelpers
open Kraken.Bedrock2.Test
open scoped FullArenaTactics

private theorem bv32_ofNat_toNat_lt {n : Nat} (h : n < 2 ^ 32) :
    (BitVec.ofNat 32 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-! ## 1. `full_sweep_bins_m6cf_wp` (`Full.fullSweepBinsSpec`) -/

section SweepBinsProof

private theorem m6cf_zero_off_preserves {c : FullCfg} {F_cur : List (List Nat)}
    {kL : FullCoreState} {sc : FullScratch} {l : Nat}
    (hlenL : kL.LengthsOk c) (hscrL : sc.LengthsOk c) (hwatL : ModeWatchesInv F_cur kL)
    (hbinL : ∀ j < l, FullReduceSpecs.BinOnlyWatchSliceOk F_cur kL j (fullWatchOffCore kL j)
      (fullWatchSizeCore kL j))
    (hl_lt : l < 2 * kL.cur_vars) (hsz0 : fullWatchSizeCore kL l = 0) :
    let wvec' := kL.wvec.set (2 * l) 0#32
    let k' : FullCoreState := { kL with wvec := wvec' }
    FullState.LengthsOk c ⟨k', sc⟩ ∧ ModeWatchesInv F_cur k' ∧
    ∀ j < l + 1, FullReduceSpecs.BinOnlyWatchSliceOk F_cur k' j (fullWatchOffCore k' j)
      (fullWatchSizeCore k' j) := by
  intro wvec' k'
  have hcv := hlenL.cur_vars_le
  have hwv := hlenL.wvec_len
  have h2l_lt : 2 * l < kL.wvec.length := by omega
  have hoff_l : fullWatchOffCore k' l = 0 := by
    unfold fullWatchOffCore k' wvec'
    rw [List.getElem?_set_self h2l_lt, Option.getD_some]; rfl
  have hsz_l : fullWatchSizeCore k' l = 0 := by
    unfold fullWatchSizeCore k' wvec'
    rw [List.getElem?_set_ne (by omega)]; exact hsz0
  have hne_eq : ∀ j, j ≠ l →
      fullWatchOffCore k' j = fullWatchOffCore kL j ∧
      fullWatchSizeCore k' j = fullWatchSizeCore kL j := fun j hj => by
    unfold fullWatchOffCore fullWatchSizeCore k' wvec'
    constructor <;> rw [List.getElem?_set_ne (by omega)]
  have hlay' : WatchStackLayout k' :=
    ⟨fun j hj => by
       by_cases hjl : j = l
       · subst hjl; rw [hoff_l, hsz_l]; exact Nat.zero_le _
       · obtain ⟨ho, hs⟩ := hne_eq j hjl; rw [ho, hs]; exact hwatL.layout.bounds j hj,
     fun j hj hp => by
       by_cases hjl : j = l
       · subst hjl; rw [hsz_l] at hp; omega
       · obtain ⟨ho, hs⟩ := hne_eq j hjl; rw [ho]; rw [hs] at hp
         exact hwatL.layout.pos_off j hj hp,
     fun j1 j2 h1 h2 hne hp1 hp2 => by
       by_cases hj1 : j1 = l
       · subst hj1; rw [hsz_l] at hp1; omega
       · by_cases hj2 : j2 = l
         · subst hj2; rw [hsz_l] at hp2; omega
         · obtain ⟨ho1, hs1⟩ := hne_eq j1 hj1; obtain ⟨ho2, hs2⟩ := hne_eq j2 hj2
           rw [ho1, hs1, ho2, hs2]; rw [hs1] at hp1; rw [hs2] at hp2
           exact hwatL.layout.disjoint j1 j2 h1 h2 hne hp1 hp2,
     fun j hj idx hi => by
       by_cases hjl : j = l
       · subst hjl; rw [hsz_l] at hi; omega
       · obtain ⟨ho, hs⟩ := hne_eq j hjl; rw [ho]; rw [hs] at hi
         exact hwatL.layout.no_sentinel j hj idx hi⟩
  have hwat' : ModeWatchesInv F_cur k' := by
    unfold ModeWatchesInv
    by_cases hdm : kL.dense_mode = 0#64
    · rw [ite_eq_left hdm]
      have hwat0 : WatchesInv F_cur kL := by
        have h := hwatL; unfold ModeWatchesInv at h; rwa [ite_eq_left hdm] at h
      refine ⟨hlay', fun j hj => ?_⟩
      by_cases hjl : j = l
      · subst hjl; rw [hsz_l]; exact .empty
      · obtain ⟨ho, hs⟩ := hne_eq j hjl; rw [ho, hs]
        exact WatchSliceOk.mono (k := kL) (k' := k')
          (by rw [CNF.entails_def]; exact fun _ p => p)
          (Nat.le_refl _) (fun _ hr => hr) (fun _ _ _ => rfl) (hwat0.slices j hj)
    · rw [ite_eq_right hdm]
      have hwat0 : DenseWatchesInv F_cur kL := by
        have h := hwatL; unfold ModeWatchesInv at h; rwa [ite_eq_right hdm] at h
      refine ⟨hlay', fun j hj => ?_⟩
      by_cases hjl : j = l
      · subst hjl; rw [hsz_l]; exact .empty
      · obtain ⟨ho, hs⟩ := hne_eq j hjl; rw [ho, hs]
        exact DenseWatchSliceOk.mono (k := kL) (k' := k')
          (by rw [CNF.entails_def]; exact fun _ p => p)
          (Nat.le_refl _) (fun _ hr => hr) (fun _ _ _ => rfl) (hwat0.slices j hj)
  refine ⟨⟨{ hlenL with wvec_len := by dsimp only [k', wvec']; rw [List.length_set, hwv] },
    hscrL⟩, hwat', fun j hj => ?_⟩
  by_cases hjl : j = l
  · subst hjl; rw [hsz_l]; exact .empty
  · obtain ⟨ho, hs⟩ := hne_eq j hjl; rw [ho, hs]
    exact FullReduceSpecs.BinOnlyWatchSliceOk.relocate (k := kL) (k' := k')
      (p := fullWatchOffCore kL j) (p' := fullWatchOffCore kL j)
      (by rw [CNF.entails_def]; exact fun _ p => p) (Nat.le_refl _) (fun _ _ => rfl)
      (hbinL j (by omega))

public theorem full_sweep_bins_m6cf_wp (Γ : Env)
    (hdefrag : ∀ a m Q X, fullWstackDefragSpec a m Q X →
      Γ "full_wstack_defrag" [i64] [] a m Q X) :
    ∀ a m Q X, fullSweepBinsSpec a m Q X →
      Func.wp Γ full_sweep_bins_m6cf_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hm, hQ⟩
  have hcv_le := hlen.core_ok.cur_vars_le
  have hwl_le := hlen.core_ok.wlen_le
  have hv_len := hlen.core_ok.vals_len
  have hl_len := hlen.core_ok.lvl_len
  have hws_len := hlen.scratch_ok.wsort_len
  have hmax_lt : c.max_vars < 2 * 2 ^ 28 := c.hmaxv
  have hwcap_lt : c.wcap < 2 * 2 ^ 28 := c.hwcap
  let dense : Bool := decide (s.core.dense_mode ≠ 0#64)
  have hnlits_eq :
      ((BitVec.ofNat 64 s.core.cur_vars) <<< (1 : Nat)).toNat = 2 * s.core.cur_vars := by
    have h1 : (BitVec.ofNat 64 s.core.cur_vars).toNat = s.core.cur_vars := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [bv64_shl1_toNat (by omega), h1]
  unfold Func.wp full_sweep_bins_m6cf_body
  c0_hsteps_nogrp
  -- Loop 0: initialize `seen[si] = 0xFFFFFFFFu` (`wsort`) for `si < nlits`
  refine wp_loop_inv
    (fun (si, ()) m0 =>
      si.toNat ≤ 2 * s.core.cur_vars ∧
      ∃ wsort0 : List (BitVec 32), wsort0.length = 2 * c.max_vars ∧
        (FullMem c { s with scratch := { s.scratch with wsort := wsort0 } } ⋆ R) m0)
    (fun (si, ()) _ => 2 * s.core.cur_vars - si.toNat)
    (fun J0 hLoop0 => by
      c0_hsteps
      exact hLoop0 (0#64, ()) m ⟨Nat.zero_le _, s.scratch.wsort, hws_len, hm⟩)
    (fun J0 ⟨si, ⟨⟩⟩ m0 ⟨hsi_le, wsort0, hws0_len, hm0⟩ hLoop0 => ?_)
  c0_hsplit
  · have hsi_lt : si.toNat < 2 * s.core.cur_vars := by
      have : si.toNat < ((BitVec.ofNat 64 s.core.cur_vars) <<< (1 : Nat)).toNat := by c0_bound
      omega
    have hsi1_eq : (si + 1#64).toNat = si.toNat + 1 := bv64_add1 (by omega)
    have hsi_ws : si.toNat < wsort0.length := by omega
    c0_hsteps
    exact hLoop0 (si + 1#64, ()) _ (by dsimp only; rw [hsi1_eq]; omega)
      ⟨by rw [hsi1_eq]; omega, wsort0.set si.toNat 0xFFFFFFFF#32, by simp [hws0_len], hm⟩
  · -- Exit init loop; enter outer loop `l < nlits`
    clear hLoop0 J0
    have hlen0 : ({ s with scratch := { s.scratch with wsort := wsort0 } } : FullState).LengthsOk
        c := hlen.with_scratch { hlen.scratch_ok with wsort_len := hws0_len }
    c0_hsteps_nogrp
    refine wp_loop_inv
      (fun (l, ()) mL =>
        l.toNat ≤ 2 * s.core.cur_vars ∧
        ∃ wvecL wstkL wuL nbL wsortL,
          let sL : FullState :=
            { core := { s.core with wvec := wvecL, wstk := wstkL, wusable := wuL,
                                    num_binary := nbL }
              scratch := { s.scratch with wsort := wsortL } }
          sL.LengthsOk c ∧ ModeWatchesInv F_cur sL.core ∧
          (∀ j < l.toNat,
            FullReduceSpecs.BinOnlyWatchSliceOk F_cur sL.core j
              (fullWatchOff sL j) (fullWatchSize sL j)) ∧
          (FullMem c sL ⋆ R) mL)
      (fun (l, ()) _ => 2 * s.core.cur_vars - l.toNat)
      (fun JL hLoopL => by
        c0_hsteps
        exact hLoopL (0#64, ()) m0 ⟨Nat.zero_le _, s.core.wvec, s.core.wstk, s.core.wusable,
          s.core.num_binary, wsort0, hlen0, hw.watches,
          fun _ hj => absurd hj (Nat.not_lt_zero _), hm0⟩)
      (fun JL ⟨l, ⟨⟩⟩ mL ⟨hl_le, wvecL, wstkL, wuL, nbL, wsortL, hlenL, hwatL, hbinL, hmL⟩
          hLoopL => ?_)
    let sL : FullState :=
      { core := { s.core with wvec := wvecL, wstk := wstkL, wusable := wuL, num_binary := nbL }
        scratch := { s.scratch with wsort := wsortL } }
    have hwvL_len : wvecL.length = 4 * c.max_vars := hlenL.core_ok.wvec_len
    have hwsL_len : wsortL.length = 2 * c.max_vars := hlenL.scratch_ok.wsort_len
    c0_hsplit
    · have hl_lt : l.toNat < 2 * s.core.cur_vars := by
        have : l.toNat < ((BitVec.ofNat 64 s.core.cur_vars) <<< (1 : Nat)).toNat := by c0_bound
        omega
      have hl1_eq : (l + (1 : BitVec 64)).toNat = l.toNat + 1 := by bv_omega
      have h2l_eq : (l <<< (1 : Nat)).toNat = 2 * l.toNat := bv64_shl1_toNat (by omega)
      have h2l1_eq : ((l <<< (1 : Nat)) + (1 : BitVec 64)).toNat = 2 * l.toNat + 1 := by
        rw [bv64_add1 (by omega), h2l_eq]
      have h2l_lt : 2 * l.toNat < wvecL.length := by omega
      have h2l1_lt : 2 * l.toNat + 1 < wvecL.length := by omega
      have h1bv : (1 : BitVec 64).toNat = 1 := rfl
      have hmod0 : 2 * l.toNat % 2 ^ 64 = 2 * l.toNat := Nat.mod_eq_of_lt (by omega)
      have hmod1 : (2 * l.toNat + 1) % 2 ^ 64 = 2 * l.toNat + 1 := Nat.mod_eq_of_lt (by omega)
      let off0 : Nat := fullWatchOff sL l.toNat
      let sz0 : Nat := fullWatchSize sL l.toNat
      let offW : BitVec 32 := wvecL[(l <<< (1 : Nat)).toNat]'(by omega)
      let szW : BitVec 32 := wvecL[((l <<< (1 : Nat)) + (1 : BitVec 64)).toNat]'(by omega)
      have hoff_idx : (wvecL[2 * l.toNat]'h2l_lt).toNat = off0 := by
        unfold off0 fullWatchOff fullWatchOffCore sL
        rw [List.getElem?_eq_getElem h2l_lt, Option.getD_some]
      have hsz_idx : (wvecL[2 * l.toNat + 1]'h2l1_lt).toNat = sz0 := by
        unfold sz0 fullWatchSize fullWatchSizeCore sL
        rw [List.getElem?_eq_getElem h2l1_lt, Option.getD_some]
      have hoff_eq : offW.toNat = off0 := by unfold offW; simp only [h2l_eq]; exact hoff_idx
      have hsz_eq : szW.toNat = sz0 := by unfold szW; simp only [h2l1_eq]; exact hsz_idx
      have hbd_end : off0 + sz0 ≤ s.core.wlen := hwatL.bounds l.toNat hl_lt
      have hslice0 : FullReduceSpecs.ModeWatchSliceOk dense F_cur sL.core l.toNat off0 sz0 :=
        modeWatchesInv_slice_of_lt hwatL hl_lt
      clear hw hlen hdefrag hQ hlen0 hm0
      c0_hsplit
      · -- `sz == 0`: zero `wvec[l << 1] = 0u` and continue
        have hsz0 : sz0 = 0 := by
          have h1 := congrArg BitVec.toNat hc
          simp only [h1bv, hmod1] at h1
          rw [zext_toNat (wvecL[2 * l.toNat + 1]'h2l1_lt) (by decide), hsz_idx] at h1
          exact h1
        have h2l_w : (l <<< (1 : Nat)).toNat < wvecL.length := by rw [h2l_eq]; exact h2l_lt
        c0_hsteps
        obtain ⟨hlenZ, hwatZ, hbinZ⟩ :=
          m6cf_zero_off_preserves hlenL.core_ok hlenL.scratch_ok hwatL hbinL hl_lt hsz0
        let wvecZ := wvecL.set (2 * l.toNat) 0#32
        have hwvZ_eq : wvecL.set (l <<< (1 : Nat)).toNat 0 = wvecZ := by
          dsimp only [wvecZ]; rw [h2l_eq]; rfl
        refine hLoopL (l + (1 : BitVec 64), ()) _ (by dsimp only; rw [hl1_eq]; omega)
          ⟨by rw [hl1_eq]; omega, wvecZ, wstkL, wuL, nbL, wsortL, hlenZ, hwatZ,
           by rw [hl1_eq]; exact hbinZ, ?_⟩
        exact m6cf_fullMem_cast hm (by dsimp only [sL]; rw [hwvZ_eq])
      · have hlv_eq : (l >>> (1 : Nat)).toNat = l.toNat / 2 := bv64_shr1_toNat l
        have hlv_lt : (l >>> (1 : Nat)).toNat < s.core.lvl.length := by rw [hlv_eq]; omega
        have hl_v : l.toNat < s.core.vals.length := by omega
        let end0 : Nat := off0 + sz0
        c0_hsteps_nogrp
        -- Join after `lsat`
        refine wp_join_state_pure (ts := [.bool]) (α := Bool) (fun b => (b, ())) (fun _ => True)
          ?_ ?_
        · intro _ _ _
          c0_hsteps_nogrp
          -- Join after `lfix`
          refine wp_join_state_pure (ts := [.bool]) (α := Bool) (fun b => (b, ()))
            (fun _ => True) ?_ ?_
          · intro _ _ _
            c0_hsteps_nogrp
            -- Inner compaction & dedup loop `(p, q)`
            refine wp_loop_inv
              (fun (p, q, ()) m1 =>
                off0 ≤ q.toNat ∧ q.toNat ≤ p.toNat ∧ p.toNat ≤ end0 ∧
                ∃ wstk1 nb1 wsort1, wstk1.length = c.wcap ∧ wsort1.length = 2 * c.max_vars ∧
                  (∀ i, i < off0 ∨ p.toNat ≤ i → wstk1[i]? = wstkL[i]?) ∧
                  FullReduceSpecs.ModeWatchSliceOk dense F_cur sL.core l.toNat p.toNat
                    (end0 - p.toNat) ∧
                  FullReduceSpecs.BinOnlyWatchSliceOk F_cur
                    { s.core with wvec := wvecL, wstk := wstk1, wusable := wuL, num_binary := nbL }
                    l.toNat off0 (q.toNat - off0) ∧
                  (FullMem c
                    { core := { s.core with wvec := wvecL, wstk := wstk1, wusable := wuL,
                                            num_binary := nb1 }
                      scratch := { s.scratch with wsort := wsort1 } } ⋆ R) m1)
              (fun (p, _, ()) _ => end0 - p.toNat)
              (fun J1 hLoop1 => by
                c0_hsteps
                have hoff64 : (offW.setWidth 64).toNat = off0 := by
                  rw [zext_toNat offW (by decide), hoff_eq]
                refine hLoop1 _ mL ⟨by rw [hoff64]; exact Nat.le_refl _,
                  by rw [hoff64]; exact Nat.le_refl _, by rw [hoff64]; omega,
                  wstkL, nbL, wsortL, hlenL.core_ok.wstk_len_arr, hwsL_len, fun _ _ => rfl,
                  ?_, ?_, hmL⟩
                · rw [hoff64, show end0 - off0 = sz0 by omega]; exact hslice0
                · rw [hoff64, Nat.sub_self]; exact .empty)
              (fun J1 ⟨p, q, ⟨⟩⟩ m1
                  ⟨hoq, hqp, hpe, wstk1, nb1, wsort1, hlen1, hws1, hout1, hrem1, hpre1, hm1⟩
                  hLoop1 => ?_)
            have hend_bv : (offW.setWidth 64 + szW.setWidth 64).toNat = end0 := by
              rw [BitVec.toNat_add, zext_toNat offW (by decide), zext_toNat szW (by decide),
                hoff_eq, hsz_eq, Nat.mod_eq_of_lt (by omega)]
            c0_hsplit
            · have hp_lt : p.toNat < end0 := by
                simp only [h1bv, hmod0, hmod1, hoff_idx, hsz_idx] at hc; omega
              have hp_w : p.toNat < wstk1.length := by omega
              have hq_w : q.toNat < wstk1.length := by omega
              let w0 := wstk1[p.toNat]'hp_w
              have hw0_orig : sL.core.wstk[p.toNat]? = some w0 := by
                dsimp only [sL]
                rw [← hout1 p.toNat (Or.inr (Nat.le_refl _)), List.getElem?_eq_getElem hp_w]
              have hstep := hrem1.step (by omega) hw0_orig
              c0_hsteps_nogrp; c0_hstep; c0_hsplit
              · -- Binary watch
                have hbin : (w0 &&& 0x80000000#32) ≠ 0#32 := by
                  change ((wstk1[p.toNat]'hp_w) &&& 0x80000000#32) ≠ 0#32; assumption
                obtain ⟨hne, hlt_o, hent_o, hrem'⟩ := hstep.1 hbin
                have hp1_eq : (p + (1 : BitVec 64)).toNat = p.toNat + 1 := bv64_add1 (by omega)
                have hq1_eq : (q + (1 : BitVec 64)).toNat = q.toNat + 1 := bv64_add1 (by omega)
                have hot_lt : (w0 &&& 0x7FFFFFFF#32).toNat < 2 * s.core.cur_vars := hlt_o
                have hot_sh : ((w0 &&& 0x7FFFFFFF#32) >>> 1#32).toNat =
                    (w0 &&& 0x7FFFFFFF#32).toNat / 2 := bv32_shr1_toNat _
                have hot_lvl : (((w0 &&& 0x7FFFFFFF#32) >>> 1#32).setWidth 64).toNat <
                    s.core.lvl.length := by
                  rw [zext_toNat _ (by decide), hot_sh]; omega
                have hot_v : ((w0 &&& 0x7FFFFFFF#32).setWidth 64).toNat < s.core.vals.length := by
                  rw [zext_toNat _ (by decide)]; omega
                have hot_ws : ((w0 &&& 0x7FFFFFFF#32).setWidth 64).toNat < wsort1.length := by
                  rw [zext_toNat _ (by decide)]; omega
                c0_hsteps_nogrp
                -- Join after `osat`
                refine wp_join_state_pure (ts := [.bool]) (α := Bool) (fun b => (b, ()))
                  (fun _ => True) ?_ ?_
                · intro _ _ _
                  c0_hsteps_nogrp
                  -- Join after `ofix`
                  refine wp_join_state_pure (ts := [.bool]) (α := Bool) (fun b => (b, ()))
                    (fun _ => True) ?_ ?_
                  · intro _ _ _
                    c0_hsteps_nogrp
                    -- Join after `drop`
                    refine wp_join_state_pure (ts := [.bool]) (α := Bool) (fun b => (b, ()))
                      (fun _ => True) ?_ ?_
                    · intro _ _ _
                      c0_hsteps_nogrp
                      -- Join after `if (drop) ... else ...`
                      refine wp_join_group (fun (q', ()) mQ =>
                        off0 ≤ q'.toNat ∧ q'.toNat ≤ p.toNat + 1 ∧
                        ∃ wstk' nb' wsort',
                          wstk'.length = c.wcap ∧ wsort'.length = 2 * c.max_vars ∧
                          (∀ i, i < off0 ∨ p.toNat + 1 ≤ i → wstk'[i]? = wstkL[i]?) ∧
                          FullReduceSpecs.BinOnlyWatchSliceOk F_cur
                            { s.core with wvec := wvecL, wstk := wstk', wusable := wuL,
                                          num_binary := nbL }
                            l.toNat off0 (q'.toNat - off0) ∧
                          (FullMem c
                            { core := { s.core with wvec := wvecL, wstk := wstk', wusable := wuL,
                                                    num_binary := nb' }
                              scratch := { s.scratch with wsort := wsort' } } ⋆ R) mQ)
                        ?_ ?_
                      · rintro _ ⟨q', ⟨⟩⟩ mQ
                          ⟨hoq', hqp', wstk', nb', wsort', hlen', hws', hout', hpre', hmQ⟩
                        c0_hsteps
                        exact hLoop1 (p + (1 : BitVec 64), q', ()) mQ
                          (by dsimp only; rw [hp1_eq]; omega)
                          ⟨hoq', by rw [hp1_eq]; omega, by rw [hp1_eq]; omega,
                           wstk', nb', wsort', hlen', hws',
                           by rw [hp1_eq]; exact hout',
                           by rw [hp1_eq, show end0 - (p.toNat + 1) = end0 - p.toNat - 1 by omega]
                              exact hrem',
                           hpre', hmQ⟩
                      · intro Jq hJq
                        c0_hsplit
                        · -- `drop = true`
                          c0_hsteps
                          · exact hJq (q, ()) _ ⟨hoq, by omega, wstk1, nb1 - 1#64, wsort1,
                              hlen1, hws1, fun i hi => hout1 i (by omega), hpre1, hm⟩
                          · exact hJq (q, ()) m1 ⟨hoq, by omega, wstk1, nb1, wsort1,
                              hlen1, hws1, fun i hi => hout1 i (by omega), hpre1, hm1⟩
                          · exact hJq (q, ()) m1 ⟨hoq, by omega, wstk1, nb1, wsort1,
                              hlen1, hws1, fun i hi => hout1 i (by omega), hpre1, hm1⟩
                        · -- `drop = false`: stamp `seen[ot] = ltag` (if `ot < nlits`), keep `w0`
                          c0_hsteps_nogrp
                          refine wp_join_state0 (α := List (BitVec 32))
                            (fun wsort' mS =>
                              wsort'.length = 2 * c.max_vars ∧
                              (FullMem c
                                { core := { s.core with wvec := wvecL, wstk := wstk1,
                                                        wusable := wuL, num_binary := nb1 }
                                  scratch := { s.scratch with wsort := wsort' } } ⋆ R) mS)
                            ?_ ?_
                          · rintro _ wsort' mS ⟨hws', hmS⟩
                            c0_hsteps
                            refine hJq (q + (1 : BitVec 64), ()) _
                              ⟨by rw [hq1_eq]; omega, by rw [hq1_eq]; omega,
                               wstk1.set q.toNat w0, nb1, wsort',
                               List.length_set.trans hlen1, hws',
                               fun i hi => by
                                 rw [List.getElem?_set_ne (by omega)]; exact hout1 i (by omega),
                               ?_, hm⟩
                            rw [hq1_eq, show q.toNat + 1 - off0 = (q.toNat - off0) + 1 by omega]
                            exact FullReduceSpecs.BinOnlyWatchSliceOk.append_bin
                              (k := { s.core with wvec := wvecL, wstk := wstk1, wusable := wuL,
                                                  num_binary := nbL })
                              (k' := { s.core with wvec := wvecL, wstk := wstk1.set q.toNat w0,
                                                   wusable := wuL, num_binary := nbL })
                              (p := off0) (p' := off0) (Nat.le_refl _)
                              (fun j hj => List.getElem?_set_ne (by omega)) hpre1
                              (by rw [show off0 + (q.toNat - off0) = q.toNat by omega]
                                  exact List.getElem?_set_self hq_w)
                              hbin hne hlt_o hent_o
                          · intro Js hJs
                            c0_hsplit
                            · c0_hsteps; exact hJs _ _ ⟨by simp [hws1], hm⟩
                            · c0_hsteps; exact hJs wsort1 m1 ⟨hws1, hm1⟩
                    · intro Jd hJd
                      clear hLoopL JL hLoop1 hbinL hwatL hlenL hslice0 hrem1 hpre1 hout1 hstep
                      c0_hsplit
                      · c0_hsteps; exact hJd true trivial
                      · c0_hsplit
                        · c0_hsteps; exact hJd true trivial
                        · c0_hsplit
                          · c0_hsteps; exact hJd true trivial
                          · c0_hsplit
                            · c0_hsteps <;> exact hJd _ trivial
                            · c0_hsteps; exact hJd false trivial
                  · intro Jo hJo
                    clear hLoopL JL hLoop1 hbinL hwatL hlenL hslice0 hrem1 hpre1 hout1 hstep
                    c0_hsplit
                    · c0_hsteps; exact hJo true trivial
                    · c0_hsplit
                      · c0_hsplit
                        · c0_hsplit
                          · c0_hsteps <;> exact hJo _ trivial
                          · c0_hsteps; exact hJo false trivial
                        · c0_hsteps; exact hJo false trivial
                      · c0_hsteps; exact hJo false trivial
                · intro Jos hJos
                  clear hLoopL JL hLoop1 hbinL hwatL hlenL hslice0 hrem1 hpre1 hout1 hstep
                  c0_hsplit
                  · c0_hsplit
                    · c0_hsteps <;> exact hJos _ trivial
                    · c0_hsteps; exact hJos false trivial
                  · c0_hsteps; exact hJos false trivial
              · -- Non-binary watch: advance `p + 2`
                have hlg : (w0 &&& 0x80000000#32) = 0#32 := by
                  change ((wstk1[p.toNat]'hp_w) &&& 0x80000000#32) = 0#32; assumption
                obtain ⟨h2rem, _, _, _, _, _, hrem'⟩ := hstep.2 hlg
                have hp2_eq : (p + (2 : BitVec 64)).toNat = p.toNat + 2 := bv64_add2 (by omega)
                c0_hsteps
                exact hLoop1 (p + (2 : BitVec 64), q, ()) m1 (by dsimp only; rw [hp2_eq]; omega)
                  ⟨hoq, by rw [hp2_eq]; omega, by rw [hp2_eq]; omega,
                   wstk1, nb1, wsort1, hlen1, hws1,
                   fun i hi => by rw [hp2_eq] at hi; exact hout1 i (by omega),
                   by rw [hp2_eq, show end0 - (p.toNat + 2) = end0 - p.toNat - 2 by omega]
                      exact hrem',
                   hpre1, hm1⟩
            · -- Exit inner loop (`p = end0`): sentinel-fill `[q, end0)` with `0xFFFFFFFFu`
              have hp_end : p.toNat = end0 := by
                simp only [h1bv, hmod0, hmod1, hoff_idx, hsz_idx] at hc; omega
              clear hrem1 hslice0 hLoop1 J1
              c0_hsteps_nogrp
              refine wp_loop_inv
                (fun (k, ()) m2 =>
                  q.toNat ≤ k.toNat ∧ k.toNat ≤ end0 ∧
                  ∃ wstk2 : List (BitVec 32), wstk2.length = c.wcap ∧
                    (∀ i, i < q.toNat ∨ end0 ≤ i → wstk2[i]? = wstk1[i]?) ∧
                    (FullMem c
                      { core := { s.core with wvec := wvecL, wstk := wstk2, wusable := wuL,
                                              num_binary := nb1 }
                        scratch := { s.scratch with wsort := wsort1 } } ⋆ R) m2)
                (fun (k, ()) _ => end0 - k.toNat)
                (fun J2 hLoop2 => by
                  c0_hsteps; exact hLoop2 (q, ()) m1 ⟨Nat.le_refl _, by omega, wstk1, hlen1,
                    fun _ _ => rfl, hm1⟩)
                (fun J2 ⟨k, ⟨⟩⟩ m2 ⟨hqk, hke, wstk2, hlen2, hout2, hm2⟩ hLoop2 => ?_)
              c0_hsplit
              · have hk_lt : k.toNat < end0 := by
                  simp only [h1bv, hmod0, hmod1, hoff_idx, hsz_idx] at hc; omega
                have hk1_eq : (k + (1 : BitVec 64)).toNat = k.toNat + 1 := bv64_add1 (by omega)
                c0_hsteps
                exact hLoop2 (k + (1 : BitVec 64), ()) _ (by dsimp only; rw [hk1_eq]; omega)
                  ⟨by rw [hk1_eq]; omega, by rw [hk1_eq]; omega,
                   wstk2.set k.toNat 0xFFFFFFFF#32, List.length_set.trans hlen2,
                   fun i hi => by rw [List.getElem?_set_ne (by omega)]; exact hout2 i hi, hm⟩
              · -- Exit sentinel loop; join after `if (q == off) ... else ...`
                clear hLoop2 J2
                let wu' := wuL + ((offW.setWidth 64 + szW.setWidth 64) - q)
                have hqoff_bv : (q - offW.setWidth 64).setWidth 32
                    = BitVec.ofNat 32 (q.toNat - off0) := by
                  apply BitVec.eq_of_toNat_eq
                  rw [BitVec.toNat_setWidth, BitVec.toNat_sub, zext_toNat offW (by decide),
                    hoff_eq]
                  have hlt32 : q.toNat - off0 < 2 ^ 32 := by omega
                  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt32]
                  have : (2 ^ 64 - off0 + q.toNat) % 2 ^ 64 = q.toNat - off0 := by omega
                  rw [this, Nat.mod_eq_of_lt hlt32]
                c0_hsteps_nogrp
                refine wp_join_state0 (α := List (BitVec 32))
                  (fun wvec' mW =>
                    let sF : FullState :=
                      { core := { s.core with wvec := wvec', wstk := wstk2, wusable := wu',
                                              num_binary := nb1 }
                        scratch := { s.scratch with wsort := wsort1 } }
                    sF.LengthsOk c ∧ ModeWatchesInv F_cur sF.core ∧
                    (∀ j < l.toNat + 1,
                      FullReduceSpecs.BinOnlyWatchSliceOk F_cur sF.core j
                        (fullWatchOff sF j) (fullWatchSize sF j)) ∧
                    (FullMem c
                      { core := { s.core with wvec := wvec', wstk := wstk2, wusable := wuL,
                                              num_binary := nb1 }
                        scratch := { s.scratch with wsort := wsort1 } } ⋆ R) mW)
                  ?_ ?_
                · rintro _ wvec' mW ⟨hlenF, hwatF, hbinF, hmW⟩
                  c0_hsteps
                  exact hLoopL (l + (1 : BitVec 64), ()) _ (by dsimp only; rw [hl1_eq]; omega)
                    ⟨by rw [hl1_eq]; omega, wvec', wstk2, wu', nb1, wsort1, hlenF, hwatF,
                     by rw [hl1_eq]; exact hbinF, m6cf_fullMem_cast hm rfl⟩
                · intro Jw hJw
                  have hlenL1 : FullState.LengthsOk c
                      { core := sL.core, scratch := { s.scratch with wsort := wsort1 } } :=
                    hlenL.with_scratch { hlenL.scratch_ok with wsort_len := hws1 }
                  let wvec1 := wvecL.set (2 * l.toNat + 1) (BitVec.ofNat 32 (q.toNat - off0))
                  obtain ⟨hlen1', hwat1', hbin1'⟩ := full_sweep_bins_finish_lit
                    hlenL1.core_ok hlenL1.scratch_ok hwatL hbinL
                    hl_lt hlen2 hoq (show q.toNat ≤ end0 by omega)
                    (fun i hi => hout1 i (by change i < off0 ∨ end0 ≤ i at hi; omega))
                    hout2 hpre1
                    { s.core with wvec := wvec1, wstk := wstk2, wusable := wu', num_binary := nb1 }
                    rfl
                  c0_hsplit
                  · -- `q == off`: set `wvec[2*l] = 0u; wvec[2*l + 1] = 0u`
                    have hq_eq : q.toNat = off0 := by
                      have h1 := congrArg BitVec.toNat hc
                      simp only [hmod0] at h1
                      rw [zext_toNat _ (by decide), hoff_idx] at h1
                      exact h1
                    have hsz1_zero : fullWatchSizeCore
                        { s.core with wvec := wvec1, wstk := wstk2, wusable := wu',
                                      num_binary := nb1 } l.toNat = 0 := by
                      unfold fullWatchSizeCore
                      dsimp only [wvec1]
                      rw [List.getElem?_set_self h2l1_lt, Option.getD_some, hq_eq, Nat.sub_self]
                      rfl
                    obtain ⟨hlenZ, hwatZ, hbinZ⟩ := m6cf_zero_off_preserves
                      hlen1'.core_ok hlen1'.scratch_ok hwat1'
                      (fun j hj => hbin1' j (by omega)) hl_lt hsz1_zero
                    have h2l_w : (l <<< (1 : Nat)).toNat < wvecL.length := by
                      rw [h2l_eq]; exact h2l_lt
                    have h2l1_w : ((l <<< (1 : Nat)) + (1 : BitVec 64)).toNat <
                        (wvecL.set (l <<< (1 : Nat)).toNat 0#32).length := by
                      rw [List.length_set, h2l1_eq]; exact h2l1_lt
                    c0_hsteps
                    have hwv_comm :
                        (wvecL.set (l <<< (1 : Nat)).toNat 0).set
                          ((l <<< (1 : Nat)) + (1 : BitVec 64)).toNat 0 =
                        wvec1.set (2 * l.toNat) 0#32 := by
                      dsimp only [wvec1]
                      rw [h2l_eq, h2l1_eq, hq_eq, Nat.sub_self]
                      exact List.set_comm (0 : BitVec 32) (0 : BitVec 32) (by omega)
                    exact hJw (wvec1.set (2 * l.toNat) 0#32) _
                      ⟨hlenZ, hwatZ, hbinZ, m6cf_fullMem_cast hm (by dsimp only; rw [hwv_comm])⟩
                  · -- `q != off`: set `wvec[2*l + 1] = (u32)(q - off)`
                    have h2l1_w : ((l <<< (1 : Nat)) + (1 : BitVec 64)).toNat < wvecL.length := by
                      rw [h2l1_eq]; exact h2l1_lt
                    c0_hsteps
                    have hwv_eq :
                        wvecL.set ((l <<< (1 : Nat)) + (1 : BitVec 64)).toNat
                          ((q - offW.setWidth 64).setWidth 32) = wvec1 := by
                      dsimp only [wvec1]; rw [h2l1_eq, hqoff_bv]
                    exact hJw wvec1 _
                      ⟨hlen1', hwat1', hbin1', m6cf_fullMem_cast hm (by rw [hwv_eq])⟩
          · intro Jf hJf
            clear hLoopL JL hbinL hwatL hlenL hslice0 hbd_end
            c0_hsteps <;> exact hJf _ trivial
        · intro Js hJs
          clear hLoopL JL hbinL hwatL hlenL hslice0 hbd_end
          c0_hsteps <;> exact hJs _ trivial
    · -- Exit outer loop (`l = 2 * cur_vars`): call `full_wstack_defrag`
      have hl_end : l.toNat = 2 * s.core.cur_vars := by
        have : ((BitVec.ofNat 64 s.core.cur_vars) <<< (1 : Nat)).toNat ≤ l.toNat := by c0_bound
        omega
      have hbin_all : FullReduceSpecs.BinOnlyWatchesInv F_cur sL.core :=
        ⟨hwatL.layout, fun j hj => hbinL j (hl_end ▸ hj)⟩
      c0_hsteps; c0_call hdefrag
      refine ⟨c, sL, R, rfl, hlenL, hwatL.layout, hmL,
        fun wvec' wstk' wlen' wsort' m' hlen' hlay' _ hpres hm' => ?_⟩
      let sF : FullState :=
        { core := { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := 0#64,
                                num_binary := nbL }
          scratch := { s.scratch with wsort := wsort' } }
      have hbinF : FullReduceSpecs.BinOnlyWatchesInv F_cur sF.core :=
        fullWstackDefrag_preserves_binOnly hbin_all hlay' rfl hpres
      c0_hsteps
      exact hQ wvec' wstk' wlen' nbL wsort' m' hlen' hbinF.toFull hbinF.toDenseWatchesInv
        { hw with arena := { hw.arena with len_ok := hw.arena.len_ok },
                  watches := hbinF.toModeWatchesInv } hm'

end SweepBinsProof

/-! ## 2. `full_enter_dense_m6cf_wp` (`FullFastSched.schedEnterDenseSpec`) -/

section EnterDenseProof

private def M6EnterOk (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s st : FullState) : Prop :=
  st.LengthsOk c ∧ FullWitnessInv c F0 F_cur st.core ∧ FullLitMarksClear c st ∧
  FullArenaVarsNodup st ∧ FullExtScratchOk c st ∧
  st.core.cur_level = 0 ∧ st.core.fuel.toNat ≤ s.core.fuel.toNat

public theorem full_enter_dense_m6cf_wp (Γ : Env)
    (hBacktrack : ∀ a m Q X, fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hFlush : ∀ a m Q X, fullFlushTrailSpec a m Q X →
      Γ "full_flush_trail" [i64] [i64] a m Q X)
    (hSweepBins : ∀ a m Q X, fullSweepBinsSpec a m Q X →
      Γ "full_sweep_bins" [i64] [] a m Q X)
    (hWatchPush : ∀ a m Q X, fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X)
    (hSweep : ∀ a m Q X, fullArenaSweepSpec a m Q X →
      Γ "full_arena_sweep" [i64] [i64] a m Q X)
    (hArenaNext : ∀ a m Q X, fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X) :
    ∀ a m Q X, FullFastSched.schedEnterDenseSpec a m Q X →
      Func.wp Γ full_enter_dense_m6cf_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hsp0, hm, hQ⟩
  obtain ⟨F_cur, hspw0⟩ := hsp0.exists_witness
  have har_cap : c.arena_cap < 2 * 2 ^ 28 := c.harena
  have hmaxv : c.max_vars < 2 * 2 ^ 28 := c.hmaxv
  have hclv_lt : s.core.cur_level < 2 ^ 64 := by
    have := hspw0.2.1.cur_level_le; have := hspw0.1.core_ok.trail_end_le
    have := hspw0.1.core_ok.cur_vars_le; omega
  unfold Func.wp full_enter_dense_m6cf_body
  c0_hsteps_nogrp
  refine wp_join_state0 (α := FullState)
    (fun s1 m1 => M6EnterOk c F0 F_cur s s1 ∧ s1.core.dense_mode = 0#64 ∧
      (FullMem c s1 ⋆ R) m1) ?_ ?_
  · rintro _ s1 m1 ⟨hok1, hdm1, hm1⟩
    clear hm hsp0 hspw0
    have hspw1 : FullSparseInvW c F0 F_cur s1 :=
      ⟨hok1.1, hok1.2.1, hok1.2.2.1, hok1.2.2.2.1, hok1.2.2.2.2.1, hdm1⟩
    c0_hsplit
    · -- `h->oom != 0`: return `false` immediately
      c0_hsteps
      exact hQ false s1 m1 hok1.2.2.2.2.2.1 hok1.2.2.2.2.2.2 (by simp)
        (fun _ => hspw1.toSparse) hm1
    · c0_hsplit
      · exact absurd hdm1 hc
      · -- `dense_mode == 0`: call `full_flush_trail`
        c0_hsteps; c0_call hFlush
        refine ⟨c, F0, s1, R, rfl, hspw1.toSparse, hm1, ?_⟩
        intro fr s1p m1p hsp1p _ _ hfl1p hcl1p_fn _ _ _ hm1p
        have hcl1p : s1p.core.cur_level = 0 := hcl1p_fn hok1.2.2.2.2.2.1
        have hfl1p' : s1p.core.fuel.toNat ≤ s.core.fuel.toNat :=
          Nat.le_trans hfl1p hok1.2.2.2.2.2.2
        c0_hsplit
        · -- `fr != 1`: return `false`
          c0_hsteps
          exact hQ false s1p m1p hcl1p hfl1p' (by simp) (fun _ => hsp1p) hm1p
        · -- `fr == 1`: sweep bins and populate dense watches
          obtain ⟨F_cur1, hspw1p⟩ := hsp1p.exists_witness
          have hdm1p : s1p.core.dense_mode = 0#64 := hspw1p.2.2.2.2.2
          c0_hsteps; c0_call hSweepBins
          refine ⟨c, F0, F_cur1, s1p, R, rfl, hspw1p.1, hspw1p.2.1, hm1p,
            fun wvec2 wstk2 wlen2 nb2 wsort2 m2 hlen2 _ hd2 hw2 hm2 => ?_⟩
          let s2 : FullState :=
            { s1p with
              core := { s1p.core with
                wvec := wvec2, wstk := wstk2, wlen := wlen2, wusable := 0#64, num_binary := nb2 }
              scratch := { s1p.scratch with wsort := wsort2 } }
          have hok2 : M6EnterOk c F0 F_cur1 s s2 :=
            ⟨hlen2, hw2, hspw1p.2.2.1, hspw1p.2.2.2.1, hspw1p.2.2.2.2.1, hcl1p, hfl1p'⟩
          c0_hsteps_nogrp
          refine wp_loop_inv
            (fun (p, ()) mP =>
              p.toNat ≤ s2.core.arena_len ∧
              (p.toNat = s2.core.arena_len ∨ p.toNat ∈ fullArenaClauseRefs s2) ∧
              ∃ sP : FullState,
                M6EnterOk c F0 F_cur1 s sP ∧ DenseWatchesInv F_cur1 sP.core ∧
                sP.core.arena = s2.core.arena ∧ sP.core.arena_len = s2.core.arena_len ∧
                sP.core.dense_mode = 0#64 ∧ (FullMem c sP ⋆ R) mP)
            (fun (p, ()) _ => s2.core.arena_len - p.toNat)
            (fun JP hLoopP => by
              c0_hsteps
              refine hLoopP (0#64, ()) m2 ⟨Nat.zero_le _, ?_, s2, hok2, hd2, rfl, rfl, hdm1p, hm2⟩
              by_cases hz : s2.core.arena_len = 0
              · exact Or.inl hz.symm
              · exact Or.inr (FullDenseWatchHelpers.fullArenaClauseRefs_zero_mem hw2.arena
                  (Nat.pos_of_ne_zero hz)))
            (fun JP ⟨p, ⟨⟩⟩ mP ⟨hp_le, hp_mem, sP, hokP, hdP, harP, halenP, hdmP, hmP⟩
                hLoopP => ?_)
          have halP := hokP.1.core_ok.arena_len_le
          have haarP := hokP.1.core_ok.arena_len_arr
          have hrefsP : fullArenaClauseRefs sP = fullArenaClauseRefs s2 := by
            unfold fullArenaClauseRefs fullArenaClauseRefsCore; rw [harP, halenP]
          c0_hsplit
          · have hp_lt : p.toNat < sP.core.arena_len := by c0_bound
            have hp_in : p.toNat ∈ fullArenaClauseRefs sP := by
              rw [hrefsP]; exact hp_mem.resolve_left (by omega)
            have hp_wf := hokP.2.1.arena.refs_wf p.toNat hp_in
            have hp_lt32 : p.toNat < 2 ^ 32 := by omega
            have hp_trunc : (p.setWidth 32).toNat = p.toNat := by bv_omega
            have hnb := fullArenaNextOff_bounds (ar := sP.core.arena) (alen := sP.core.arena_len)
              (cref := p.toNat) hp_wf.1
            have hnxt_mem := fullArenaClauseRefs_next_mem hokP.2.1.arena hp_in
            c0_hsteps_nogrp
            refine wp_join_state0 (α := FullState)
              (fun sN mN => M6EnterOk c F0 F_cur1 s sN ∧ DenseWatchesInv F_cur1 sN.core ∧
                sN.core.arena = s2.core.arena ∧ sN.core.arena_len = s2.core.arena_len ∧
                sN.core.dense_mode = 0#64 ∧ (FullMem c sN ⋆ R) mN)
              (fun _ sN mN ⟨hokN, hdN, harN, halenN, hdmN, hmN⟩ => by
                c0_hsteps; c0_call hArenaNext
                refine ⟨c, sN, R, rfl, hokN.1, hmN, ?_⟩
                have hn_eq : ((BitVec.ofNat 32 (fullArenaNextOff sN.core.arena sN.core.arena_len
                    (p.setWidth 32).toNat)).setWidth 64).toNat =
                    fullArenaNextOff sP.core.arena sP.core.arena_len p.toNat := by
                  rw [harN, halenN, ← harP, ← halenP, hp_trunc, BitVec.toNat_setWidth,
                    bv32_ofNat_toNat_lt (by omega)]
                  exact Nat.mod_eq_of_lt (by omega)
                c0_hsteps
                exact hLoopP (_, ()) mN (by dsimp only; rw [hn_eq]; omega)
                  ⟨by rw [hn_eq]; omega,
                    by rw [hn_eq]
                       rcases hnxt_mem with hend | hmem
                       · exact Or.inl (hend.trans halenP)
                       · exact Or.inr (hrefsP ▸ hmem),
                    sN, hokN, hdN, harN, halenN, hdmN, hmN⟩)
              (fun JN hJN => ?_)
            c0_hsteps_nogrp
            · have hsz_eq : (sP.core.arena[(p + 2#64).toNat]'(by c0_bound)).toNat =
                  fullArenaClauseSizeCore sP.core p.toNat := by
                have hp2 : (p + 2#64).toNat = p.toNat + 2 := by c0_bound
                unfold fullArenaClauseSizeCore
                rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; simp only [hp2]
              have hsz_ge3 : 3 ≤ (sP.core.arena[(p + 2#64).toNat]'(by c0_bound)).toNat := by
                rw [hsz_eq]; exact hp_wf.2.1
              have hsz_lt31 : (sP.core.arena[(p + 2#64).toNat]'(by c0_bound)).toNat < 2 ^ 31 := by
                rw [hsz_eq]; have := hp_wf.2.2.1; have := hp_wf.2.2.2.1; omega
              have hmask := bv32_mask_7fffffff_props hsz_ge3 hsz_lt31
              have hp_lt31 : (p.setWidth 32).toNat < 0x80000000 := by rw [hp_trunc]; omega
              have hp_neff : p.setWidth 32 ≠ 0xFFFFFFFF#32 := fun heq => by
                rw [heq] at hp_lt31; revert hp_lt31; decide
              refine wp_loop_inv
                (fun (k, ()) mK =>
                  k.toNat ≤ (sP.core.arena[(p + 2#64).toNat]'(by c0_bound)).toNat ∧
                  ∃ sK : FullState,
                    M6EnterOk c F0 F_cur1 s sK ∧ DenseWatchesInv F_cur1 sK.core ∧
                    sK.core.arena = s2.core.arena ∧ sK.core.arena_len = s2.core.arena_len ∧
                    sK.core.dense_mode = 0#64 ∧ (FullMem c sK ⋆ R) mK)
                (fun (k, ()) _ => (sP.core.arena[(p + 2#64).toNat]'(by c0_bound)).toNat - k.toNat)
                (fun JK hLoopK => by
                  c0_hsteps
                  exact hLoopK (0#32, ()) mP
                    ⟨Nat.zero_le _, sP, hokP, hdP, harP, halenP, hdmP, hmP⟩)
                (fun JK ⟨k, ⟨⟩⟩ mK ⟨hk_le, sK, hokK, hdK, harK, halenK, hdmK, hmK⟩ hLoopK => ?_)
              have haarK := hokK.1.core_ok.arena_len_arr
              c0_hsplit
              · have hk_lt : k.toNat < (sP.core.arena[(p + 2#64).toNat]'(by c0_bound)).toNat := by
                  c0_bound
                have hidx_eq : (p + 3#64 + k.setWidth 64).toNat = p.toNat + 3 + k.toNat := by
                  have := hp_wf.2.2.1; have := hp_wf.2.2.2.1; bv_omega
                have hidx_lt : (p + 3#64 + k.setWidth 64).toNat < sK.core.arena.length := by
                  rw [hidx_eq]; rw [hsz_eq] at hk_lt
                  have := hp_wf.2.2.1; have := hp_wf.2.2.2.1
                  have := hokK.1.core_ok.arena_len_le; omega
                c0_hsteps; c0_call hWatchPush
                refine ⟨c, sK, R, rfl, hokK.1, hdK.layout, by simp,
                  fun _ => ⟨hmask.2.1, hp_neff⟩, hmK,
                  fun ok wvecK' wstkK' wlenK' wuK' wsortK' mK' hlenK' hlayK' hothK' hokT
                    hokF hmK' => ?_⟩
                let sK' : FullState :=
                  { sK with
                    core := { sK.core with wvec := wvecK', wstk := wstkK', wlen := wlenK',
                                           wusable := wuK' }
                    scratch := { sK.scratch with wsort := wsortK' } }
                have hp_inK : (p.setWidth 32).toNat ∈ fullArenaClauseRefsCore sK.core := by
                  rw [hp_trunc]; unfold fullArenaClauseRefsCore
                  rw [harK, halenK, ← harP, ← halenP]; exact hp_in
                have hdK' : DenseWatchesInv F_cur1 sK'.core :=
                  fullWatchPush_preserves_denseWatchesInv hdK hlayK' rfl (fun _ r => r)
                    hmask.1 hmask.2.2 hp_lt31 hp_inK hothK'
                    (fun ht => by
                      obtain ⟨hl, _, hsz', hpre', hw0', hw1'⟩ := hokT ht
                      exact ⟨hl, hsz', hpre', hw0', hw1' rfl⟩) (fun hf => (hokF hf).1)
                have hwK' : FullWitnessInv c F0 F_cur1 sK'.core :=
                  { hokK.2.1 with
                    arena := { hokK.2.1.arena with len_ok := hokK.2.1.arena.len_ok }
                    watches := by
                      rw [ModeWatchesInv, ite_eq_left hdmK]
                      exact denseWatchesInv_toWatchesInv hdK' }
                have hokK' : M6EnterOk c F0 F_cur1 s sK' :=
                  ⟨hlenK', hwK', hokK.2.2.1, hokK.2.2.2.1, hokK.2.2.2.2.1, hokK.2.2.2.2.2.1,
                    hokK.2.2.2.2.2.2⟩
                c0_hsplit
                · have hk1 : (k + 1#32).toNat = k.toNat + 1 := by c0_bound
                  c0_hsteps
                  exact hLoopK (k + 1#32, ()) mK' (by dsimp only; omega)
                    ⟨by omega, sK', hokK', hdK', harK, halenK, hdmK, hmK'⟩
                · c0_hsteps
                  let sOom : FullState := { sK' with core := { sK'.core with oom := 0#64 } }
                  have hlenOom : sOom.LengthsOk c :=
                    ⟨{ hlenK'.core_ok with vals_len := hlenK'.core_ok.vals_len },
                      hlenK'.scratch_ok⟩
                  have hwOom := fullWitnessInv_with_oom hwK' 0#64
                  c0_call hSweep
                  refine ⟨c, F0, F_cur1, sOom, R, rfl, hlenOom, hwOom, hokK'.2.2.2.1, hdmK,
                    fun hpos => by
                      change 0 < sK.core.cur_level at hpos; have := hokK.2.2.2.2.2.1; omega,
                    hm, ?_⟩
                  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ scS mS sS hlenS _ hextS _ hllS
                    hwS hndS _ _ _ _ _ hmS
                  have hspS : FullSparseInv c F0 sS :=
                    ⟨⟨hlenS, F_cur1, hwS⟩, hokK'.2.2.1, hndS, ⟨hllS, hextS ▸ hokK'.2.2.2.2.1.2⟩,
                      hdmK⟩
                  c0_hsteps
                  exact hQ false sS mS hokK'.2.2.2.2.2.1 hokK'.2.2.2.2.2.2
                    (by simp) (fun _ => hspS) hmS
              · c0_hsteps; exact hJN sK mK ⟨hokK, hdK, harK, halenK, hdmK, hmK⟩
            all_goals exact hJN sP mP ⟨hokP, hdP, harP, halenP, hdmP, hmP⟩
          · -- Outer loop exit: set `dense_mode = 1#64`, return `true`
            c0_hsteps
            let sFin : FullState := { sP with core := { sP.core with dense_mode := 1#64 } }
            have hlenFin : sFin.LengthsOk c :=
              ⟨{ hokP.1.core_ok with vals_len := hokP.1.core_ok.vals_len }, hokP.1.scratch_ok⟩
            have hwFin : FullWitnessInv c F0 F_cur1 sFin.core :=
              fullWitnessInv_with_dense_mode_nz hokP.2.1 hdP (by decide)
            have hdenFin : FullDenseInv c F0 sFin :=
              ⟨⟨hlenFin, F_cur1, hwFin⟩, hokP.2.2.1, hokP.2.2.2.1, hokP.2.2.2.2.1,
                hokP.2.2.2.2.2.1, show (1#64 : BitVec 64) ≠ 0#64 by decide⟩
            exact hQ true sFin _ hokP.2.2.2.2.2.1 hokP.2.2.2.2.2.2
              (fun _ => hdenFin) (by simp) hm
  · intro J1 hJ1; c0_hsplit
    · c0_hsteps; c0_call hBacktrack
      refine ⟨c, s, R, rfl, hspw0.1, hclv_lt, fun _ => by
        have := hspw0.2.1.cur_level_le; have := hspw0.1.core_ok.trail_end_le
        have := hspw0.1.core_ok.cur_vars_le; omega,
        hspw0.2.1.trail_lits_lt, hm, ?_⟩
      intro _ _ _ _ _ _ _ cl1 _ sc1 m1 s1 hlen1 _ _ hcl1 hprsc1 _ _ _ hw_le _ hm1
      have hw1 := hw_le F0 F_cur hspw0.2.1 (Nat.zero_le _)
      have hl01 : s1.core.cur_level = 0 := by dsimp only [s1]; rw [hcl1]; simp
      have hsp1 := m6cf_fullSparseInvW_after_bt0 hspw0 hlen1 hw1 hprsc1.1 rfl rfl rfl rfl rfl
      c0_hsteps
      exact hJ1 s1 m1 ⟨⟨hsp1.1, hsp1.2.1, hsp1.2.2.1, hsp1.2.2.2.1, hsp1.2.2.2.2.1, hl01,
        Nat.le_refl _⟩, hsp1.2.2.2.2.2, hm1⟩
    · have hl00 : s.core.cur_level = 0 := by
        have hnat := congrArg BitVec.toNat hc
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hclv_lt] at hnat; exact hnat
      c0_hsteps
      exact hJ1 s m ⟨⟨hspw0.1, hspw0.2.1, hspw0.2.2.1, hspw0.2.2.2.1, hspw0.2.2.2.2.1, hl00,
        Nat.le_refl _⟩, hspw0.2.2.2.2.2, hm⟩

end EnterDenseProof

/-! ## 3. `full_compact_mark_live_m6cf_wp` (`FullM4Compact.fullCompactMarkLiveSpec`) -/

section CompactMarkLiveProof

private theorem fullSparseInvW_with_work_stk1 {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hsp : FullSparseInvW c F0 F_cur s)
    {ws1 : List (BitVec 32)} (hlen1 : ws1.length = 2 * c.max_vars) :
    FullSparseInvW c F0 F_cur { s with scratch := { s.scratch with work_stk1 := ws1 } } :=
  ⟨hsp.1.with_scratch { hsp.1.scratch_ok with work_stk1_len := hlen1 },
    hsp.2.1, hsp.2.2.1, hsp.2.2.2.1, hsp.2.2.2.2.1, hsp.2.2.2.2.2⟩

public theorem full_compact_mark_live_m6cf_wp (Γ : Env)
    (hnext : ∀ a m Q X, fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X) :
    ∀ a m Q X, FullM4Compact.fullCompactMarkLiveSpec a m Q X →
      Func.wp Γ full_compact_mark_live_m6cf_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hsp, hm, hQ⟩
  have hlen := hsp.1
  have hw := hsp.2.1
  have hdm := hsp.2.2.2.2.2
  have hwat : WatchesInv F_cur s.core := by
    have hm' := hw.watches; unfold ModeWatchesInv at hm'; rwa [ite_eq_left hdm] at hm'
  have hcv_le := hlen.core_ok.cur_vars_le
  have hal_le := hlen.core_ok.arena_len_le
  have har_len := hlen.core_ok.arena_len_arr
  have hwl_le := hlen.core_ok.wlen_le
  have hws_len := hlen.core_ok.wstk_len_arr
  have hwv_len := hlen.core_ok.wvec_len
  have hv_len := hlen.core_ok.vals_len
  have hws1_len := hlen.scratch_ok.work_stk1_len
  have hmax_lt : c.max_vars < 2 * 2 ^ 28 := c.hmaxv
  have har_lt : c.arena_cap < 2 * 2 ^ 28 := c.harena
  have hcv_64 : (BitVec.ofNat 64 s.core.cur_vars).toNat = s.core.cur_vars := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hnlits_eq : ((BitVec.ofNat 64 s.core.cur_vars) <<< (1 : Nat)).toNat =
      2 * s.core.cur_vars := by
    rw [bv64_shl1_toNat (by rw [hcv_64]; omega), hcv_64]
  unfold Func.wp full_compact_mark_live_m6cf_body
  c0_hsteps_nogrp
  -- Loop 1: zero-initialize `map[v] = 0u` for all `v < cur_vars` (isolated vars stay 0)
  refine wp_loop_inv
    (fun (v, ()) m1 =>
      v.toNat ≤ s.core.cur_vars ∧
      ∃ ws1 : List (BitVec 32), ws1.length = 2 * c.max_vars ∧
        (FullMem c { s with scratch := { s.scratch with work_stk1 := ws1 } } ⋆ R) m1)
    (fun (v, ()) _ => s.core.cur_vars - v.toNat)
    (fun J1 hLoop1 => by
      c0_hsteps; exact hLoop1 (0#64, ()) m ⟨Nat.zero_le _, s.scratch.work_stk1, hws1_len, hm⟩)
    (fun J1 ⟨v, ⟨⟩⟩ m1 ⟨hv_le, ws1, hlen1, hm1⟩ hLoop1 => ?_)
  c0_hsplit
  · have hv_lt : v.toNat < s.core.cur_vars := by c0_bound
    have hv1_eq : (v + 1#64).toNat = v.toNat + 1 := bv64_add1 (by omega)
    have hv_ws : v.toNat < ws1.length := by omega
    c0_hsteps
    exact hLoop1 (v + 1#64, ()) _ (by dsimp only; rw [hv1_eq]; omega)
      ⟨by rw [hv1_eq]; omega, ws1.set v.toNat 0#32, by simp [hlen1], hm⟩
  · -- Loop 2: mark endpoints of non-tautological unassigned binary watches
    clear hLoop1 J1
    c0_hsteps_nogrp
    refine wp_loop_inv
      (fun (l, ()) m2 =>
        l.toNat ≤ 2 * s.core.cur_vars ∧
        ∃ ws2 : List (BitVec 32), ws2.length = 2 * c.max_vars ∧
          (FullMem c { s with scratch := { s.scratch with work_stk1 := ws2 } } ⋆ R) m2)
      (fun (l, ()) _ => 2 * s.core.cur_vars - l.toNat)
      (fun J2 hLoop2 => by
        c0_hsteps; exact hLoop2 (0#64, ()) m1 ⟨Nat.zero_le _, ws1, hlen1, hm1⟩)
      (fun J2 ⟨l, ⟨⟩⟩ m2 ⟨hl_le, ws2, hlen2, hm2⟩ hLoop2 => ?_)
    c0_hsplit
    · have hl_lt : l.toNat < 2 * s.core.cur_vars := by
        have : l.toNat < ((BitVec.ofNat 64 s.core.cur_vars) <<< (1 : Nat)).toNat := by c0_bound
        omega
      have hl1_eq : (l + 1#64).toNat = l.toNat + 1 := bv64_add1 (by omega)
      have h2l_eq : (l <<< (1 : Nat)).toNat = 2 * l.toNat := bv64_shl1_toNat (by omega)
      have h2l1_eq : ((l <<< (1 : Nat)) + (1 : BitVec 64)).toNat = 2 * l.toNat + 1 := by
        rw [bv64_add1 (by rw [h2l_eq]; omega), h2l_eq]
      have h2l_lt : 2 * l.toNat < s.core.wvec.length := by omega
      have h2l1_lt : 2 * l.toNat + 1 < s.core.wvec.length := by omega
      let off0 := fullWatchOffCore s.core l.toNat
      let sz0 := fullWatchSizeCore s.core l.toNat
      have hoff_eq : (s.core.wvec[2 * l.toNat]'h2l_lt).toNat = off0 := by
        unfold off0 fullWatchOffCore
        rw [List.getElem?_eq_getElem h2l_lt, Option.getD_some]
      have hsz_eq : (s.core.wvec[2 * l.toNat + 1]'h2l1_lt).toNat = sz0 := by
        unfold sz0 fullWatchSizeCore
        rw [List.getElem?_eq_getElem h2l1_lt, Option.getD_some]
      have hbd : off0 + sz0 ≤ s.core.wlen := hwat.layout.bounds l.toNat hl_lt
      have hslice0 : WatchSliceOk F_cur s.core l.toNat off0 sz0 := hwat.slices l.toNat hl_lt
      let end0 := off0 + sz0
      have hend_nat :
          ((s.core.wvec[(l <<< (1 : Nat)).toNat]'(by rw [h2l_eq]; omega)).setWidth 64 +
            (s.core.wvec[((l <<< (1 : Nat)) + (1 : BitVec 64)).toNat]'(by
              rw [h2l1_eq]; omega)).setWidth 64).toNat = end0 := by
        rw [BitVec.toNat_add, zext_toNat _ (by decide), zext_toNat _ (by decide)]
        simp only [h2l_eq, h2l1_eq, hoff_eq, hsz_eq]
        exact Nat.mod_eq_of_lt (by omega)
      c0_hsteps_nogrp
      refine wp_loop_inv
        (fun (p, ()) mP =>
          off0 ≤ p.toNat ∧ p.toNat ≤ end0 ∧
          WatchSliceOk F_cur s.core l.toNat p.toNat (end0 - p.toNat) ∧
          ∃ wsP : List (BitVec 32), wsP.length = 2 * c.max_vars ∧
            (FullMem c { s with scratch := { s.scratch with work_stk1 := wsP } } ⋆ R) mP)
        (fun (p, ()) _ => end0 - p.toNat)
        (fun Jp hLoopP => by
          c0_hsteps
          have hoff64 : ((s.core.wvec[2 * l.toNat]'h2l_lt).setWidth 64).toNat = off0 := by
            rw [zext_toNat _ (by decide)]; exact hoff_eq
          refine hLoopP _ m2 ⟨by simp only [h2l_eq, hoff64]; exact Nat.le_refl _,
            by simp only [h2l_eq, hoff64]; omega, ?_, ws2, hlen2, hm2⟩
          simpa only [h2l_eq, hoff64, show end0 - off0 = sz0 by omega] using hslice0)
        (fun Jp ⟨p, ⟨⟩⟩ mP ⟨hop, hpe, hrem, wsP, hlenP, hmP⟩ hLoopP => ?_)
      c0_hsplit
      · have hp_lt : p.toNat < end0 := by
          have h1 : p.toNat < ((s.core.wvec[(l <<< (1 : Nat)).toNat]'(by
              rw [h2l_eq]; omega)).setWidth 64 +
              (s.core.wvec[((l <<< (1 : Nat)) + (1 : BitVec 64)).toNat]'(by
                rw [h2l1_eq]; omega)).setWidth 64).toNat := by c0_bound
          omega
        have hp_wstk : p.toNat < s.core.wstk.length := by omega
        let w0 := s.core.wstk[p.toNat]'hp_wstk
        have hw0_some : s.core.wstk[p.toNat]? = some w0 := List.getElem?_eq_getElem hp_wstk
        have hstep := FullM4Compact.WatchSliceOk_step hrem (by omega) hw0_some
        c0_hsteps_nogrp; c0_hstep; c0_hsplit
        · -- Binary watch
          have hbin0 : (w0 &&& 0x80000000#32) ≠ 0#32 := by
            change ((s.core.wstk[p.toNat]'hp_wstk) &&& 0x80000000#32) ≠ 0#32; assumption
          obtain ⟨_, hot_lt, _, hrem'⟩ := hstep.1 hbin0
          have hp1_eq : (p + 1#64).toNat = p.toNat + 1 := bv64_add1 (by omega)
          have hlv_eq : (l >>> (1 : Nat)).toNat = l.toNat / 2 := bv64_shr1_toNat l
          have hrem_p1 : WatchSliceOk F_cur s.core l.toNat (p.toNat + 1)
              (end0 - (p.toNat + 1)) := by simpa [Nat.sub_sub] using hrem'
          have hl_v : l.toNat < s.core.vals.length := by omega
          have hot_v : ((w0 &&& 0x7FFFFFFF#32).setWidth 64).toNat < s.core.vals.length := by
            rw [zext_toNat _ (by decide)]; omega
          have hl_wsP : (l >>> (1 : Nat)).toNat < wsP.length := by rw [hlv_eq]; omega
          have hot_wsP : (((w0 &&& 0x7FFFFFFF#32) >>> 1#32).setWidth 64).toNat < wsP.length := by
            rw [zext_toNat _ (by decide), bv32_shr1_toNat]; omega
          c0_hsteps_nogrp
          refine wp_join_state0 (α := List (BitVec 32))
            (fun ws' m' => ws'.length = 2 * c.max_vars ∧
              (FullMem c { s with scratch := { s.scratch with work_stk1 := ws' } } ⋆ R) m')
            ?_ ?_
          · rintro _ ws' m' ⟨hlen', hm'⟩
            c0_hsteps
            exact hLoopP (p + 1#64, ()) m' (by dsimp only; rw [hp1_eq]; omega)
              ⟨by rw [hp1_eq]; omega, by rw [hp1_eq]; omega,
               by rw [hp1_eq]; exact hrem_p1, ws', hlen', hm'⟩
          · intro Jb hJb
            c0_hsteps <;>
              first
              | exact hJb _ _ ⟨by simp [hlenP], hm⟩
              | exact hJb wsP mP ⟨hlenP, hmP⟩
        · -- Large watch: skip 2 words
          have hlg0 : (w0 &&& 0x80000000#32) = 0#32 := by
            change ((s.core.wstk[p.toNat]'hp_wstk) &&& 0x80000000#32) = 0#32; assumption
          have ⟨hrem2, hrem'⟩ := hstep.2 hlg0
          have hp2_eq : (p + 2#64).toNat = p.toNat + 2 := bv64_add2 (by omega)
          have hrem_p2 : WatchSliceOk F_cur s.core l.toNat (p.toNat + 2)
              (end0 - (p.toNat + 2)) := by simpa [Nat.sub_sub] using hrem'
          c0_hsteps
          exact hLoopP (p + 2#64, ()) mP (by dsimp only; rw [hp2_eq]; omega)
            ⟨by rw [hp2_eq]; omega, by rw [hp2_eq]; omega, by rw [hp2_eq]; exact hrem_p2,
             wsP, hlenP, hmP⟩
      · c0_hsteps
        exact hLoop2 (l + 1#64, ()) mP (by dsimp only; rw [hl1_eq]; omega)
          ⟨by rw [hl1_eq]; omega, wsP, hlenP, hmP⟩
    · -- Loop 3: scan arena clauses (`!sat && ucnt >= 1u`)
      clear hLoop2 J2 hm1 hm ws1 hlen1 hw hdm hwat hwl_le hws_len hwv_len hcv_64
      have h2bv : (2 : BitVec 64).toNat = 2 := rfl
      have h3bv : (3 : BitVec 64).toNat = 3 := rfl
      have h2cv : 2 * (s.core.cur_vars % 2 ^ 64) % 2 ^ 64 = 2 * s.core.cur_vars := by omega
      c0_hsteps_nogrp
      -- Outer exit group `J3x : Cont [i64]` for both `break` (`pos + 3 > alen`) and `pos >= alen`
      refine wp_join_state1 (t := i64) (α := BitVec 64 × List (BitVec 32)) Prod.fst
        (fun ⟨_, wsE⟩ mE => wsE.length = 2 * c.max_vars ∧
          (FullMem c { s with scratch := { s.scratch with work_stk1 := wsE } } ⋆ R) mE)
        (fun _ ⟨_, wsE⟩ mE ⟨hlenE, hmE⟩ => by
          c0_hsteps; exact hQ wsE mE (fullSparseInvW_with_work_stk1 hsp hlenE) hmE)
        (fun J3x hJ3x => ?_)
      c0_hsteps_nogrp
      refine wp_loop_inv
        (fun (pos, ()) m3 =>
          pos.toNat ≤ s.core.arena_len ∧
          ∃ ws3 : List (BitVec 32), ws3.length = 2 * c.max_vars ∧
            (FullMem c { s with scratch := { s.scratch with work_stk1 := ws3 } } ⋆ R) m3)
        (fun (pos, ()) _ => s.core.arena_len - pos.toNat)
        (fun J3 hLoop3 => by
          c0_hsteps; exact hLoop3 (0#64, ()) m2 ⟨Nat.zero_le _, ws2, hlen2, hm2⟩)
        (fun J3 ⟨pos, ⟨⟩⟩ m3 ⟨hpos_le, ws3, hlen3, hm3⟩ hLoop3 => ?_)
      c0_hsplit
      · have hpos_lt : pos.toNat < s.core.arena_len := by c0_bound
        c0_hsplit
        · -- `pos + 3 > alen`: break
          c0_hsteps
          exact hJ3x (pos, ws3) m3 ⟨hlen3, hm3⟩
        · have hpos3_le : pos.toNat + 3 ≤ s.core.arena_len := by bv_omega
          have hpos2_eq : (pos + (2 : BitVec 64)).toNat = pos.toNat + 2 := bv64_add2 (by omega)
          have hpos2_mod : (pos.toNat + (2 : BitVec 64).toNat) % 2 ^ 64 = pos.toNat + 2 := by
            rw [h2bv, Nat.mod_eq_of_lt (by omega)]
          have hpos2_lt : (pos + (2 : BitVec 64)).toNat < s.core.arena.length := by
            rw [hpos2_eq]; omega
          let csz := s.core.arena[pos.toNat + 2]'(by omega)
          have hn_bounds := fullArenaNextOff_bounds (ar := s.core.arena)
            (alen := s.core.arena_len) (cref := pos.toNat) hpos3_le
          have hpos32_eq : (pos.setWidth 32).toNat = pos.toNat := by bv_omega
          c0_hsteps; c0_call hnext
          refine ⟨c, { s with scratch := { s.scratch with work_stk1 := ws3 } }, R, rfl,
            hlen.with_scratch { hlen.scratch_ok with work_stk1_len := hlen3 }, hm3, ?_⟩
          dsimp only
          simp only [hpos32_eq]
          let npos_nat := fullArenaNextOff s.core.arena s.core.arena_len pos.toNat
          have hnpos_to : ((BitVec.ofNat 32 npos_nat).setWidth 64).toNat = npos_nat := by
            rw [zext_toNat _ (by decide), bv32_ofNat_toNat_lt (by omega)]
          c0_hsteps_nogrp
          refine wp_join_state0 (α := List (BitVec 32))
            (fun ws4 m4 => ws4.length = 2 * c.max_vars ∧
              (FullMem c { s with scratch := { s.scratch with work_stk1 := ws4 } } ⋆ R) m4)
            (fun _ ws4 m4 ⟨hlen4, hm4⟩ => by
              c0_hsteps
              exact hLoop3 _ m4 (by dsimp only; rw [hnpos_to]; omega)
                ⟨by rw [hnpos_to]; omega, ws4, hlen4, hm4⟩)
            (fun J4 hJ4 => ?_)
          c0_hsplit
          · c0_hsplit
            · c0_hsplit
              · have hfit : pos.toNat + 3 + csz.toNat ≤ s.core.arena_len := by
                  have h1 := hc
                  have hal64 : s.core.arena_len % 2 ^ 64 = s.core.arena_len :=
                    Nat.mod_eq_of_lt (by omega)
                  have hcsz32 := csz.isLt
                  have hp3c : (pos.toNat + 3 + csz.toNat) % 2 ^ 64 = pos.toNat + 3 + csz.toNat :=
                    Nat.mod_eq_of_lt (by omega)
                  simp only [hpos2_mod, h3bv, hal64] at h1
                  change (pos.toNat + 3 + csz.toNat) % 2 ^ 64 ≤ s.core.arena_len at h1
                  rwa [hp3c] at h1
                c0_hsteps_nogrp
                -- Join block `Jex : Cont [.bool, i32, i32]` after pass 1 (`break` or exit)
                refine wp_join_group (fun (_, _, _, ()) mE => mE = m3) ?_ ?_
                · rintro _ ⟨sat, ucnt, i0, ⟨⟩⟩ mE hmE
                  rcases hmE.symm with rfl
                  c0_hsteps_nogrp
                  -- Join block `Jif : Cont [i32]` after `if (!sat && ucnt >= 1u) { i = 0; ... }`
                  refine wp_join_state1 (t := i32) (α := BitVec 32 × List (BitVec 32)) Prod.fst
                    (fun ⟨_, ws'⟩ m' => ws'.length = 2 * c.max_vars ∧
                      (FullMem c { s with scratch := { s.scratch with work_stk1 := ws' } } ⋆ R) m')
                    (fun _ ⟨_, ws'⟩ m' ⟨hlen', hm'⟩ => by
                      c0_hsteps; exact hJ4 ws' m' ⟨hlen', hm'⟩)
                    (fun Jif hJif => ?_)
                  c0_hsplit
                  · -- `sat = true`: skip pass 2
                    c0_hsteps; exact hJif (i0, ws3) m3 ⟨hlen3, hm3⟩
                  · -- `sat = false`: check `ucnt >= 1u`
                    c0_hsplit
                    · -- `ucnt >= 1u`: mark unassigned literals in clause (`map[lit >> 1] = 1u`)
                      c0_hsteps_nogrp
                      refine wp_loop_inv
                        (fun (i2, ()) mK =>
                          i2.toNat ≤ csz.toNat ∧
                          ∃ wsK : List (BitVec 32), wsK.length = 2 * c.max_vars ∧
                            (FullMem c { s with scratch := { s.scratch with work_stk1 := wsK } } ⋆
                              R) mK)
                        (fun (i2, ()) _ => csz.toNat - i2.toNat)
                        (fun Jk hLoopK => by
                          c0_hsteps; exact hLoopK (0#32, ()) m3 ⟨Nat.zero_le _, ws3, hlen3, hm3⟩)
                        (fun Jk ⟨i2, ⟨⟩⟩ mK ⟨hi2_le, wsK, hlenK, hmK⟩ hLoopK => ?_)
                      c0_hsplit
                      · have hi2_lt : i2.toNat < csz.toNat := by
                          have h1 := hc; simp only [hpos2_mod] at h1; exact h1
                        have hi2_1 : (i2 + 1#32).toNat = i2.toNat + 1 := bv32_add1 (by omega)
                        have hpi2_eq : (pos + 3#64 + i2.setWidth 64).toNat =
                            pos.toNat + 3 + i2.toNat := by bv_omega
                        have hpi2_mod : (pos.toNat + (3 : BitVec 64).toNat + i2.toNat) % 2 ^ 64 =
                            pos.toNat + 3 + i2.toNat := by rw [h3bv, Nat.mod_eq_of_lt (by omega)]
                        have hpi2_lt :
                            (pos + 3#64 + i2.setWidth 64).toNat < s.core.arena.length := by
                          rw [hpi2_eq]; omega
                        c0_hsteps_nogrp
                        refine wp_join_state0 (α := List (BitVec 32))
                          (fun ws' m' => ws'.length = 2 * c.max_vars ∧
                            (FullMem c { s with scratch := { s.scratch with work_stk1 := ws' } } ⋆
                              R) m')
                          (fun _ ws' m' ⟨hlen', hm'⟩ => by
                            c0_hsteps
                            exact hLoopK (i2 + 1#32, ()) m' (by dsimp only; rw [hi2_1]; omega)
                              ⟨by rw [hi2_1]; omega, ws', hlen', hm'⟩)
                          (fun Jm hJm => ?_)
                        c0_hsplit
                        · have hlit2_lt :
                              (s.core.arena[(pos + 3#64 + i2.setWidth 64).toNat]'hpi2_lt).toNat <
                              2 * s.core.cur_vars := by
                            have h1 := hc; simp only [hpi2_mod, h2cv] at h1
                            simp only [hpi2_eq]; exact h1
                          have hlit2_v :
                              ((s.core.arena[(pos + 3#64 + i2.setWidth 64).toNat]'hpi2_lt).setWidth
                                64).toNat < s.core.vals.length := by
                            rw [zext_toNat _ (by decide)]; omega
                          have hlit2_ws :
                              (((s.core.arena[(pos + 3#64 + i2.setWidth 64).toNat]'hpi2_lt) >>>
                                1#32).setWidth 64).toNat < wsK.length := by
                            rw [zext_toNat _ (by decide), bv32_shr1_toNat]; omega
                          c0_hsplit
                          · c0_hsteps; exact hJm _ _ ⟨by simp [hlenK], hm⟩
                          · c0_hsteps; exact hJm wsK mK ⟨hlenK, hmK⟩
                        · c0_hsteps; exact hJm wsK mK ⟨hlenK, hmK⟩
                      · c0_hsteps; exact hJif (i2, wsK) mK ⟨hlenK, hmK⟩
                    · -- `ucnt == 0`: skip pass 2
                      c0_hsteps; exact hJif (i0, ws3) m3 ⟨hlen3, hm3⟩
                · intro Jex hJex
                  c0_hsteps_nogrp
                  -- Inner pass 1: check `sat` and count `ucnt`
                  refine wp_loop_inv
                    (fun (_, i, ()) mI => i.toNat ≤ csz.toNat ∧ mI = m3)
                    (fun (_, i, ()) _ => csz.toNat - i.toNat)
                    (fun Ji hLoopI => by
                      c0_hsteps; exact hLoopI (0#32, 0#32, ()) m3 ⟨Nat.zero_le _, rfl⟩)
                    (fun Ji ⟨ucnt, i, ⟨⟩⟩ mI ⟨hi_le, hmI⟩ hLoopI => ?_)
                  rcases hmI.symm with rfl
                  c0_hsplit
                  · have hi_lt : i.toNat < csz.toNat := by
                      have h1 := hc; simp only [hpos2_mod] at h1; exact h1
                    have hi1_eq : (i + 1#32).toNat = i.toNat + 1 := bv32_add1 (by omega)
                    have hpi_eq : (pos + 3#64 + i.setWidth 64).toNat =
                        pos.toNat + 3 + i.toNat := by bv_omega
                    have hpi_mod : (pos.toNat + (3 : BitVec 64).toNat + i.toNat) % 2 ^ 64 =
                        pos.toNat + 3 + i.toNat := by rw [h3bv, Nat.mod_eq_of_lt (by omega)]
                    have hpi_lt : (pos + 3#64 + i.setWidth 64).toNat < s.core.arena.length := by
                      rw [hpi_eq]; omega
                    c0_hsteps_nogrp
                    refine wp_join_group (fun (_, _, ()) m' => m' = m3)
                      (fun _ ⟨_, u', ⟨⟩⟩ m' hm' => by
                        rcases hm'.symm with rfl
                        c0_hsteps
                        exact hLoopI (u', i + 1#32, ()) m3 (by dsimp only; rw [hi1_eq]; omega)
                          ⟨by rw [hi1_eq]; omega, rfl⟩)
                      (fun Ju hJu => ?_)
                    c0_hsplit
                    · have hlit_lt :
                          (s.core.arena[(pos + 3#64 + i.setWidth 64).toNat]'hpi_lt).toNat <
                          2 * s.core.cur_vars := by
                        have h1 := hc; simp only [hpi_mod, h2cv] at h1
                        simp only [hpi_eq]; exact h1
                      have hlit_v :
                          ((s.core.arena[(pos + 3#64 + i.setWidth 64).toNat]'hpi_lt).setWidth
                            64).toNat < s.core.vals.length := by
                        rw [zext_toNat _ (by decide)]; omega
                      c0_hsplit
                      · -- `lv > 0`: `sat = true; break`
                        c0_hsteps; exact hJex (true, ucnt, i, ()) m3 rfl
                      · c0_hsteps
                        · -- `lv == 0`: `ucnt + 1`
                          exact hJu (false, ucnt + 1#32, ()) m3 rfl
                        · -- `lv < 0`: continue
                          exact hJu (false, ucnt, ()) m3 rfl
                    · c0_hsteps; exact hJu (false, ucnt, ()) m3 rfl
                  · c0_hsteps
                    exact hJex (false, ucnt, i, ()) m3 rfl
              · c0_hsteps; exact hJ4 ws3 m3 ⟨hlen3, hm3⟩
            · c0_hsteps; exact hJ4 ws3 m3 ⟨hlen3, hm3⟩
          · c0_hsteps; exact hJ4 ws3 m3 ⟨hlen3, hm3⟩
      · -- Exit loop 3: `pos = alen`
        c0_hsteps
        exact hJ3x (pos, ws3) m3 ⟨hlen3, hm3⟩

end CompactMarkLiveProof

end LeanQbe.T.Examples.Kissat.FullM6CompactFlush
