/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityTumbleSpec
import LeanQbe.T.Examples.Kissat.FullLuckyLemmas1
import LeanQbe.T.Examples.Kissat.FullLuckyLemmas2
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Fidelity Step 11 PR 2 Lucky External-Order Proofs (`FullFidelityTumbleProofLucky`)

Proves:
1. `full_lucky_ord_fid_wp` against `fullLuckyOrdFidSpec` (`SafetySlice` over `fullSafetySlice`,
   mutating only `tarjan_reach` and `tarjan_mark` and returning `n ≤ cur_vars`).
2. `full_lucky_scan_tum_wp` against exact canonical `Full.fullLuckyScanSpec` (zero ripple into
   `full_lucky` or `full_lucky_late_m7`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityTumble

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullLuckyHelpers
open Kraken.Bedrock2.Test

/-! ## 1. `full_lucky_ord_fid` (`fullLuckyOrdFidSpec`, `SafetySlice`) -/

section LuckyOrdProof

open scoped FullArenaTactics

private theorem hlen_set_ord {c : FullCfg} {s : FullState} (hlen : s.LengthsOk c)
    (i : Nat) (v : BitVec 32) :
    ({ s with scratch := { s.scratch with tarjan_reach := s.scratch.tarjan_reach.set i v } } :
      FullState).LengthsOk c :=
  hlen.with_scratch { hlen.scratch_ok with
    tarjan_reach_len := by simp [hlen.scratch_ok.tarjan_reach_len] }

private theorem hlen_set_tmk {c : FullCfg} {s : FullState} (hlen : s.LengthsOk c)
    (i : Nat) (v : BitVec 32) :
    ({ s with scratch := { s.scratch with tarjan_mark := s.scratch.tarjan_mark.set i v } } :
      FullState).LengthsOk c :=
  hlen.with_scratch { hlen.scratch_ok with
    tarjan_mark_len := by simp [hlen.scratch_ok.tarjan_mark_len] }

private theorem extPres_set_ord {s s1 : FullState} (h : FullExtScratchPres s s1)
    (i : Nat) (v : BitVec 32) :
    FullExtScratchPres s
      { s1 with scratch := { s1.scratch with tarjan_reach := s1.scratch.tarjan_reach.set i v } } :=
  h

private theorem extPres_set_tmk {s s1 : FullState} (h : FullExtScratchPres s s1)
    (i : Nat) (v : BitVec 32) :
    FullExtScratchPres s
      { s1 with scratch := { s1.scratch with tarjan_mark := s1.scratch.tarjan_mark.set i v } } :=
  h

/-- `full_lucky_ord_fid` builds an external + post-compaction `factor` variable order in
`tarjan_reach[0..n)`, preserving `FullState.core` and `FullExtScratchPres`, with `n ≤ cur_vars`. -/
theorem full_lucky_ord_fid_wp (Γ : Env) :
    ∀ a m Q X, fullLuckyOrdFidSpec a m Q X → Func.wp Γ full_lucky_ord_fid_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice_mem, fullSafetySlice_coreProj, fullSafetySlice_safe] at hlen hm hQ
  have hmax : c.max_vars < 2 * dimacsBound := c.hmaxv
  have hext : c.extend_cap < dimacsBound := c.hext
  unfold dimacsBound at hmax hext
  have hcv_le : s.core.cur_vars ≤ c.max_vars := hlen.core_ok.cur_vars_le
  have hcv_mod : (BitVec.ofNat 64 s.core.cur_vars).toNat = s.core.cur_vars :=
    Nat.mod_eq_of_lt (by omega)
  have hmx_mod : (BitVec.ofNat 64 c.max_vars).toNat = c.max_vars :=
    Nat.mod_eq_of_lt (by omega)
  let len_bv : BitVec 64 := BitVec.ofNat 64 s.scratch.extend_len
  unfold Func.wp full_lucky_ord_fid_body
  c0_hsteps_nogrp
  -- Join after checking `has_perm` & `orig_mv`
  refine wp_join_group (ts := [.bool, i64])
    (fun (hp, omv, ()) m0 =>
      (FullMem c s ⋆ R) m0 ∧
      (hp = true →
        len_bv.toNat ≤ c.extend_cap ∧ omv.toNat ≤ c.max_vars ∧
        1 + omv.toNat ≤ len_bv.toNat))
    (fun Jp ⟨hp, omv, ⟨⟩⟩ m0 ⟨hm0, hpm⟩ => ?_)
    (fun Jp hJp => ?_)
  · c0_hsteps_nogrp
    · -- `has_perm = true`
      have hhp : hp = true := by assumption
      obtain ⟨helen_le, homv_le, h1omv_le⟩ := hpm hhp
      have hesl : s.scratch.extend_stk.length = c.extend_cap := hlen.scratch_ok.extend_stk_len
      -- Loop 1: copy `ord[e] = ext[1 + e]` for `e < orig_mv`
      refine wp_loop_safety_slice_pure (fullSafetySlice c) s R
        (fun s1 (e, ()) => e.toNat ≤ omv.toNat ∧ FullExtScratchPres s s1)
        (fun (e, ()) => omv.toNat - e.toNat)
        (fun J hL => by
          c0_hsteps
          exact hL s (0#64, ()) m0 hm0 rfl hlen ⟨Nat.zero_le _, ⟨rfl, rfl⟩⟩)
        (fun J s1 (e, ()) m1 hcore1 hlen1 ⟨hele, hpres1⟩ hm1 hL1 => ?_)
      rw [Blocks.get_here]; dsimp only [fullSafetySlice] at *
      c0_hsteps_nogrp
      · have he_lt : e.toNat < omv.toNat := by assumption
        have he1 : (e + 1#64).toNat = e.toNat + 1 := by simp only [bv_c0]; omega
        have h1e_lt : (1#64 + e).toNat < s1.scratch.extend_stk.length := by
          rw [hlen1.scratch_ok.extend_stk_len]; simp only [bv_c0]; omega
        have he_ord : e.toNat < s1.scratch.tarjan_reach.length := by
          rw [hlen1.scratch_ok.tarjan_reach_len]; omega
        c0_hsteps
        exact hL1 _ (e + 1#64, ()) m hm (by dsimp only; omega) rfl
          (hlen_set_ord hlen1 _ _) ⟨by dsimp only; omega, extPres_set_ord hpres1 _ _⟩
      · -- Loop 2: walk `p` from `1 + orig_mv` to `len` composing `EXT_COMPACT` blocks
        refine wp_loop_safety_slice_pure (fullSafetySlice c) s R
          (fun s2 (_, p, ()) => p.toNat ≤ len_bv.toNat ∧ FullExtScratchPres s s2)
          (fun (_, p, ()) => len_bv.toNat - p.toNat)
          (fun J2 hL2 => by
            c0_hsteps
            have h1omv : (1#64 + omv).toNat = 1 + omv.toNat := by simp only [bv_c0]; omega
            exact hL2 s1 (e, 1#64 + omv, ()) m1 hm1 hcore1 hlen1 ⟨by rw [h1omv]; omega, hpres1⟩)
          (fun J2 s2 (e_cur, p, ()) m2 hcore2 hlen2 ⟨hple, hpres2⟩ hm2 hL2 => ?_)
        rw [Blocks.get_here]; dsimp only [fullSafetySlice] at *
        c0_hsteps_nogrp
        · have hp_lt : p.toNat < len_bv.toNat := by
            have h1 : p.toNat < s.scratch.extend_len % 2 ^ 64 := by assumption
            simpa [len_bv, BitVec.toNat_ofNat] using h1
          have hp_ext : p.toNat < s2.scratch.extend_stk.length := by
            rw [hlen2.scratch_ok.extend_stk_len]; omega
          have hp1 : (p + 1#64).toNat = p.toNat + 1 := by simp only [bv_c0]; omega
          c0_hsteps_nogrp
          refine wp_join_group (ts := [i64, i64])
            (fun (_, p', ()) m3 =>
              p.toNat < p'.toNat ∧ p'.toNat ≤ len_bv.toNat ∧
              ∃ s3 : FullState,
                (FullMem c s3 ⋆ R) m3 ∧
                PreservesCoreSlice (fullSafetySlice c).coreProj s2 s3 ∧ s3.LengthsOk c ∧
                FullExtScratchPres s s3)
            (fun J3 ⟨e', p', ⟨⟩⟩ m3 ⟨hinc, hp'le, s3, hm3, hcore3, hlen3, hpres3⟩ => by
              c0_hsteps
              exact hL2 s3 (e', p', ()) m3 hm3 (by dsimp only; omega) hcore3 hlen3 ⟨hp'le, hpres3⟩)
            (fun J3 hJ3 => ?_)
          c0_hsteps_nogrp
          · -- `EXT_BLK_FLAG | EXT_COMPACT_FLAG` block: unroll `if (ncv <= mx && ...)` joins
            apply wp_unroll_group; intro J_if hJ_if; c0_hsteps_nogrp
            apply wp_unroll_group; intro J_else hJ_else; c0_hsteps_nogrp
            · -- `ncv ≤ mx`, `p + 1 + ncv ≤ len`
              let ncv_bv : BitVec 64 :=
                (s2.scratch.extend_stk[p.toNat]'hp_ext &&& 1073741823#32).setWidth 64
              have hncv_le : ncv_bv.toNat ≤ c.max_vars := by
                have h1 : (s2.scratch.extend_stk[p.toNat]'hp_ext &&& 1073741823#32).toNat ≤
                    c.max_vars % 2 ^ 64 := by assumption
                dsimp only [ncv_bv]; simp only [BitVec.toNat_setWidth]
                have := (s2.scratch.extend_stk[p.toNat]'hp_ext &&& 1073741823#32).isLt
                omega
              have hp1ncv_le : p.toNat + 1 + ncv_bv.toNat ≤ len_bv.toNat := by
                have h1 : (p.toNat + BitVec.toNat (1 : BitVec 64) +
                    (s2.scratch.extend_stk[p.toNat]'hp_ext &&& 1073741823#32).toNat) % 2 ^ 64 ≤
                    s.scratch.extend_len % 2 ^ 64 := by
                  assumption
                have h2 : ncv_bv.toNat =
                    (s2.scratch.extend_stk[p.toNat]'hp_ext &&& 1073741823#32).toNat := by
                  dsimp only [ncv_bv]; simp only [BitVec.toNat_setWidth]
                  have := (s2.scratch.extend_stk[p.toNat]'hp_ext &&& 1073741823#32).isLt
                  exact Nat.mod_eq_of_lt (by omega)
                have h3 : BitVec.toNat (1 : BitVec 64) = 1 := rfl
                rw [h3, ← h2] at h1
                have h4 : len_bv.toNat = s.scratch.extend_len % 2 ^ 64 := by
                  simp [len_bv, BitVec.toNat_ofNat]
                omega
              -- Inner loop 2a: `while (z < mx) tmk[z] = EXT_UNMAPPED`
              refine wp_loop_safety_slice_pure (fullSafetySlice c) s2 R
                (fun s3 (z, ()) => z.toNat ≤ c.max_vars ∧ FullExtScratchPres s s3)
                (fun (z, ()) => c.max_vars - z.toNat)
                (fun Jz hLz => by
                  c0_hsteps
                  exact hLz s2 (0#64, ()) m2 hm2 rfl hlen2 ⟨Nat.zero_le _, hpres2⟩)
                (fun Jz s3 (z, ()) m3 hcore3 hlen3 ⟨hzle, hpres3⟩ hm3 hLz => ?_)
              rw [Blocks.get_here]; dsimp only [fullSafetySlice] at *
              c0_hsteps_nogrp
              · have hz_lt : z.toNat < c.max_vars := by
                  have h1 : z.toNat < c.max_vars % 2 ^ 64 := by assumption
                  omega
                have hz1 : (z + 1#64).toNat = z.toNat + 1 := by simp only [bv_c0]; omega
                have hz_tmk : z.toNat < s3.scratch.tarjan_mark.length := by
                  rw [hlen3.scratch_ok.tarjan_mark_len]; omega
                c0_hsteps
                exact hLz _ (z + 1#64, ()) m hm (by dsimp only; omega) rfl
                  (hlen_set_tmk hlen3 _ _) ⟨by dsimp only; omega, extPres_set_tmk hpres3 _ _⟩
              · -- Inner loop 2b: `while (k < ncv)` populate `tmk[ov] = k`
                refine wp_loop_safety_slice_pure (fullSafetySlice c) s2 R
                  (fun s4 (k, ()) => k.toNat ≤ ncv_bv.toNat ∧ FullExtScratchPres s s4)
                  (fun (k, ()) => ncv_bv.toNat - k.toNat)
                  (fun Jk hLk => by
                    c0_hsteps
                    exact hLk s3 (0#64, ()) m3 hm3 hcore3 hlen3 ⟨Nat.zero_le _, hpres3⟩)
                  (fun Jk s4 (k, ()) m4 hcore4 hlen4 ⟨hkle, hpres4⟩ hm4 hLk => ?_)
                rw [Blocks.get_here]; dsimp only [fullSafetySlice] at *
                c0_hsteps_nogrp
                · have hk_lt : k.toNat < ncv_bv.toNat := by assumption
                  have hk1 : (k + 1#64).toNat = k.toNat + 1 := by simp only [bv_c0]; omega
                  have hpk_ext : (p + 1#64 + k).toNat < s4.scratch.extend_stk.length := by
                    rw [hlen4.scratch_ok.extend_stk_len]; simp only [bv_c0]; omega
                  c0_hsteps_nogrp
                  refine wp_join_state0 (α := FullState)
                    (fun s4' m4' =>
                      (FullMem c s4' ⋆ R) m4' ∧
                      PreservesCoreSlice (fullSafetySlice c).coreProj s4 s4' ∧
                      s4'.LengthsOk c ∧ FullExtScratchPres s s4')
                    (fun J4 s4' m4' ⟨hm4', hcore4', hlen4', hpres4'⟩ => by
                      c0_hsteps
                      exact hLk s4' (k + 1#64, ()) m4' hm4' (by dsimp only; omega)
                        hcore4' hlen4' ⟨by dsimp only; omega, hpres4'⟩)
                    (fun J4 hJ4 => by
                      c0_hsteps_nogrp
                      · have hidx_eq : (p + 1#64 + k).toNat =
                            (p.toNat + BitVec.toNat (1 : BitVec 64) + k.toNat) % 2 ^ 64 := by
                          simp only [bv_c0, show BitVec.toNat (1 : BitVec 64) = 1 from rfl]
                        let ov := s4.scratch.extend_stk[(p + 1#64 + k).toNat]'hpk_ext
                        have hov_lt : (ov.setWidth 64).toNat < s4.scratch.tarjan_mark.length := by
                          dsimp only [ov]
                          rw [hlen4.scratch_ok.tarjan_mark_len]
                          have h1 : (s4.scratch.extend_stk[(p.toNat + BitVec.toNat (1 : BitVec 64) +
                              k.toNat) % 2 ^ 64]'(hidx_eq ▸ hpk_ext)).toNat <
                              c.max_vars % 2 ^ 64 := by assumption
                          simp only [BitVec.toNat_setWidth]
                          have h2 : (s4.scratch.extend_stk[(p + 1#64 + k).toNat]'hpk_ext).toNat <
                              c.max_vars % 2 ^ 64 := by
                            simpa [hidx_eq] using h1
                          have := (s4.scratch.extend_stk[(p + 1#64 + k).toNat]'hpk_ext).isLt
                          omega
                        c0_hsteps
                        exact hJ4 _ m ⟨hm, rfl, hlen_set_tmk hlen4 _ _,
                          extPres_set_tmk hpres4 _ _⟩
                      · exact hJ4 s4 m4 ⟨hm4, rfl, hlen4, hpres4⟩)
                · -- Inner loop 2c: `while (e < orig_mv)` remap `ord[e]`
                  refine wp_loop_safety_slice_pure (fullSafetySlice c) s2 R
                    (fun s5 (e2, ()) => e2.toNat ≤ omv.toNat ∧ FullExtScratchPres s s5)
                    (fun (e2, ()) => omv.toNat - e2.toNat)
                    (fun Je hLe => by
                      c0_hsteps
                      exact hLe s4 (0#64, ()) m4 hm4 hcore4 hlen4 ⟨Nat.zero_le _, hpres4⟩)
                    (fun Je s5 (e2, ()) m5 hcore5 hlen5 ⟨he2le, hpres5⟩ hm5 hLe => ?_)
                  rw [Blocks.get_here]; dsimp only [fullSafetySlice] at *
                  c0_hsteps_nogrp
                  · have he2_lt : e2.toNat < omv.toNat := by assumption
                    have he2_1 : (e2 + 1#64).toNat = e2.toNat + 1 := by simp only [bv_c0]; omega
                    have he2_ord : e2.toNat < s5.scratch.tarjan_reach.length := by
                      rw [hlen5.scratch_ok.tarjan_reach_len]; omega
                    c0_hsteps_nogrp
                    refine wp_join_group (ts := [i32])
                      (fun _ m5' => (FullMem c s5 ⋆ R) m5')
                      (fun J5 ⟨nv, ⟨⟩⟩ m5' hm5' => by
                        c0_hsteps
                        exact hLe _ (e2 + 1#64, ()) m hm (by dsimp only; omega) rfl
                          (hlen_set_ord hlen5 _ _)
                          ⟨by dsimp only; omega, extPres_set_ord hpres5 _ _⟩)
                      (fun J5 hJ5 => by
                        c0_hsteps_nogrp
                        · let cur_v := s5.scratch.tarjan_reach[e2.toNat]'he2_ord
                          have hcur_tmk :
                              (cur_v.setWidth 64).toNat < s5.scratch.tarjan_mark.length := by
                            dsimp only [cur_v]
                            rw [hlen5.scratch_ok.tarjan_mark_len]
                            have h1 : (s5.scratch.tarjan_reach[e2.toNat]'he2_ord).toNat <
                                c.max_vars % 2 ^ 64 := by assumption
                            simp only [BitVec.toNat_setWidth]
                            have := (s5.scratch.tarjan_reach[e2.toNat]'he2_ord).isLt
                            omega
                          c0_hsteps; exact hJ5 (_, ()) m5 hm5
                        · exact hJ5 (_, ()) m5 hm5)
                  · have hp_adv : (p + 1#64 + ncv_bv).toNat = p.toNat + 1 + ncv_bv.toNat := by
                      simp only [bv_c0]; omega
                    exact hJ3 (e2, p + 1#64 + ncv_bv, ()) m5
                      ⟨by rw [hp_adv]; omega, by rw [hp_adv]; omega, s5, hm5, hcore5, hlen5, hpres5⟩
            · -- `ncv ≤ mx`, `¬ (p + 1 + ncv ≤ len)`
              exact hJ3 (e_cur, p + 1#64, ()) m2 ⟨by omega, by omega, s2, hm2, rfl, hlen2, hpres2⟩
            · -- `¬ (ncv ≤ mx)`
              exact hJ3 (e_cur, p + 1#64, ()) m2 ⟨by omega, by omega, s2, hm2, rfl, hlen2, hpres2⟩
          · -- Non-compact block: skip until next `EXT_BLK_FLAG` or `len`
            refine wp_loop_safety_slice_pure (fullSafetySlice c) s2 R
              (fun s3 (q, ()) => p.toNat < q.toNat ∧ q.toNat ≤ len_bv.toNat ∧
                FullExtScratchPres s s3)
              (fun (q, ()) => len_bv.toNat - q.toNat)
              (fun Jq hLq => by
                c0_hsteps
                exact hLq s2 (p + 1#64, ()) m2 hm2 rfl hlen2
                  ⟨by omega, by omega, hpres2⟩)
              (fun Jq s3 (q, ()) m3 hcore3 hlen3 ⟨hpq, hqle, hpres3⟩ hm3 hLq => ?_)
            rw [Blocks.get_here]; dsimp only [fullSafetySlice] at *
            c0_hsteps_nogrp
            · have hq_lt : q.toNat < len_bv.toNat := by
                have h1 : q.toNat < s.scratch.extend_len % 2 ^ 64 := by assumption
                simpa [len_bv, BitVec.toNat_ofNat] using h1
              have hq_ext : q.toNat < s3.scratch.extend_stk.length := by
                rw [hlen3.scratch_ok.extend_stk_len]; omega
              have hq1 : (q + 1#64).toNat = q.toNat + 1 := by simp only [bv_c0]; omega
              c0_hsteps_nogrp
              · exact hLq s3 (q + 1#64, ()) m3 hm3 (by dsimp only; rw [hq1]; omega) rfl hlen3
                  ⟨by dsimp only; rw [hq1]; omega, by dsimp only; rw [hq1]; omega, hpres3⟩
              · exact hJ3 (e_cur, q, ()) m3 ⟨hpq, hqle, s3, hm3, hcore3, hlen3, hpres3⟩
            · exact hJ3 (e_cur, q, ()) m3 ⟨hpq, hqle, s3, hm3, hcore3, hlen3, hpres3⟩
        · -- After Loop 2: Loop 3 (clear `tmk`), Loop 4 (compact `ord`), Loop 5 (append fresh)
          refine wp_loop_safety_slice_pure (fullSafetySlice c) s R
            (fun s3 (z, ()) => z.toNat ≤ s.core.cur_vars ∧ FullExtScratchPres s s3)
            (fun (z, ()) => s.core.cur_vars - z.toNat)
            (fun Jz hLz => by
              c0_hsteps; exact hLz s2 (0#64, ()) m2 hm2 hcore2 hlen2 ⟨Nat.zero_le _, hpres2⟩)
            (fun Jz s3 (z, ()) m3 hcore3 hlen3 ⟨hzle, hpres3⟩ hm3 hLz => ?_)
          rw [Blocks.get_here]; dsimp only [fullSafetySlice] at *
          c0_hsteps_nogrp
          · have hz_lt : z.toNat < s.core.cur_vars := by
              have h1 : z.toNat < s.core.cur_vars % 2 ^ 64 := by assumption
              omega
            have hz1 : (z + 1#64).toNat = z.toNat + 1 := by simp only [bv_c0]; omega
            have hz_tmk : z.toNat < s3.scratch.tarjan_mark.length := by
              rw [hlen3.scratch_ok.tarjan_mark_len]; omega
            c0_hsteps
            exact hLz _ (z + 1#64, ()) m hm (by dsimp only; omega) rfl
              (hlen_set_tmk hlen3 _ _) ⟨by dsimp only; omega, extPres_set_tmk hpres3 _ _⟩
          · -- Loop 4: compact valid `ord[0..orig_mv-1]` in-place (`(e2, n_v, ())`)
            refine wp_loop_safety_slice_pure (fullSafetySlice c) s R
              (fun s4 (e2, n_v, ()) =>
                n_v.toNat ≤ s.core.cur_vars ∧ e2.toNat ≤ omv.toNat ∧ FullExtScratchPres s s4)
              (fun (e2, _, ()) => omv.toNat - e2.toNat)
              (fun Je hLe => by
                c0_hsteps
                exact hLe s3 (0#64, 0#64, ()) m3 hm3 hcore3 hlen3
                  ⟨Nat.zero_le _, Nat.zero_le _, hpres3⟩)
              (fun Je s4 (e2, n_v, ()) m4 hcore4 hlen4 ⟨hnle, he2le, hpres4⟩ hm4 hLe => ?_)
            rw [Blocks.get_here]; dsimp only [fullSafetySlice] at *
            c0_hsteps_nogrp
            · have he2_lt : e2.toNat < omv.toNat := by assumption
              have he2_1 : (e2 + 1#64).toNat = e2.toNat + 1 := by simp only [bv_c0]; omega
              have he2_ord : e2.toNat < s4.scratch.tarjan_reach.length := by
                rw [hlen4.scratch_ok.tarjan_reach_len]; omega
              c0_hsteps_nogrp
              refine wp_join_group (ts := [i64])
                (fun (n', ()) m4' =>
                  n'.toNat ≤ s.core.cur_vars ∧
                  ∃ s4' : FullState,
                    (FullMem c s4' ⋆ R) m4' ∧
                    PreservesCoreSlice (fullSafetySlice c).coreProj s4 s4' ∧
                    s4'.LengthsOk c ∧ FullExtScratchPres s s4')
                (fun J4 ⟨n', ⟨⟩⟩ m4' ⟨hn'le, s4', hm4', hcore4', hlen4', hpres4'⟩ => by
                  c0_hsteps
                  exact hLe s4' (e2 + 1#64, n', ()) m4' hm4' (by dsimp only; omega)
                    hcore4' hlen4' ⟨hn'le, by dsimp only; omega, hpres4'⟩)
                (fun J4 hJ4 => by
                  c0_hsteps_nogrp
                  · have hiv_lt : ((s4.scratch.tarjan_reach[e2.toNat]'he2_ord).setWidth 64).toNat <
                        s.core.cur_vars := by
                      have h1 : (s4.scratch.tarjan_reach[e2.toNat]'he2_ord).toNat <
                          s.core.cur_vars % 2 ^ 64 := by assumption
                      simp only [BitVec.toNat_setWidth]
                      have := (s4.scratch.tarjan_reach[e2.toNat]'he2_ord).isLt
                      omega
                    have hiv_tmk : ((s4.scratch.tarjan_reach[e2.toNat]'he2_ord).setWidth 64).toNat <
                        s4.scratch.tarjan_mark.length := by
                      rw [hlen4.scratch_ok.tarjan_mark_len]; omega
                    c0_hsteps_nogrp
                    · have hn_lt : n_v.toNat < s.core.cur_vars := by
                        have h1 : n_v.toNat < s.core.cur_vars % 2 ^ 64 := by assumption
                        omega
                      have hn1 : (n_v + 1#64).toNat = n_v.toNat + 1 := by simp only [bv_c0]; omega
                      have hn_ord : n_v.toNat < s4.scratch.tarjan_reach.length := by
                        rw [hlen4.scratch_ok.tarjan_reach_len]; omega
                      c0_hsteps
                      exact hJ4 (n_v + 1#64, ()) m
                        ⟨by omega, _, hm, rfl, hlen_set_ord (hlen_set_tmk hlen4 _ _) _ _,
                         extPres_set_ord (extPres_set_tmk hpres4 _ _) _ _⟩
                    · exact hJ4 (n_v, ()) m4 ⟨hnle, s4, hm4, rfl, hlen4, hpres4⟩
                    · exact hJ4 (n_v, ()) m4 ⟨hnle, s4, hm4, rfl, hlen4, hpres4⟩
                  · exact hJ4 (n_v, ()) m4 ⟨hnle, s4, hm4, rfl, hlen4, hpres4⟩)
            · -- Loop 5: append remaining `v < cv` with `tmk[v] == 0u && n < cv`
              refine wp_loop_safety_slice_pure (fullSafetySlice c) s R
                (fun s5 (n_v2, v, ()) =>
                  n_v2.toNat ≤ s.core.cur_vars ∧ v.toNat ≤ s.core.cur_vars ∧
                  FullExtScratchPres s s5)
                (fun (_, v, ()) => s.core.cur_vars - v.toNat)
                (fun Jv hLv => by
                  c0_hsteps
                  exact hLv s4 (n_v, 0#64, ()) m4 hm4 hcore4 hlen4 ⟨hnle, Nat.zero_le _, hpres4⟩)
                (fun Jv s5 (n_v2, v, ()) m5 hcore5 hlen5 ⟨hn2le, hvle, hpres5⟩ hm5 hLv => ?_)
              rw [Blocks.get_here]; dsimp only [fullSafetySlice] at *
              c0_hsteps_nogrp
              · have hv_lt : v.toNat < s.core.cur_vars := by
                  have h1 : v.toNat < s.core.cur_vars % 2 ^ 64 := by assumption
                  omega
                have hv1 : (v + 1#64).toNat = v.toNat + 1 := by simp only [bv_c0]; omega
                have hv_tmk : v.toNat < s5.scratch.tarjan_mark.length := by
                  rw [hlen5.scratch_ok.tarjan_mark_len]; omega
                c0_hsteps_nogrp
                refine wp_join_group (ts := [i64])
                  (fun (n', ()) m5' =>
                    n'.toNat ≤ s.core.cur_vars ∧
                    ∃ s5' : FullState,
                      (FullMem c s5' ⋆ R) m5' ∧
                      PreservesCoreSlice (fullSafetySlice c).coreProj s5 s5' ∧
                      s5'.LengthsOk c ∧ FullExtScratchPres s s5')
                  (fun J5 ⟨n', ⟨⟩⟩ m5' ⟨hn'le, s5', hm5', hcore5', hlen5', hpres5'⟩ => by
                    c0_hsteps
                    exact hLv s5' (n', v + 1#64, ()) m5' hm5' (by dsimp only; omega)
                      hcore5' hlen5' ⟨hn'le, by dsimp only; omega, hpres5'⟩)
                  (fun J5 hJ5 => by
                    c0_hsteps_nogrp
                    · have hn2_lt : n_v2.toNat < s.core.cur_vars := by
                        have h1 : n_v2.toNat < s.core.cur_vars % 2 ^ 64 := by assumption
                        omega
                      have hn2_1 : (n_v2 + 1#64).toNat = n_v2.toNat + 1 := by
                        simp only [bv_c0]; omega
                      have hn2_ord : n_v2.toNat < s5.scratch.tarjan_reach.length := by
                        rw [hlen5.scratch_ok.tarjan_reach_len]; omega
                      c0_hsteps
                      exact hJ5 (n_v2 + 1#64, ()) m
                        ⟨by omega, _, hm, rfl, hlen_set_ord hlen5 _ _,
                         extPres_set_ord hpres5 _ _⟩
                    · exact hJ5 (n_v2, ()) m5 ⟨hn2le, s5, hm5, rfl, hlen5, hpres5⟩
                    · exact hJ5 (n_v2, ()) m5 ⟨hn2le, s5, hm5, rfl, hlen5, hpres5⟩)
              · exact hQ (n_v2, ()) s5 m5 hcore5 hlen5 ⟨hn2le, hpres5⟩ hm5
    · -- `!has_perm`: write identity `ord[v] = v` for `v < cv`, return `cv`
      refine wp_loop_safety_slice_pure (fullSafetySlice c) s R
        (fun s1 (v, ()) => v.toNat ≤ s.core.cur_vars ∧ FullExtScratchPres s s1)
        (fun (v, ()) => s.core.cur_vars - v.toNat)
        (fun J hL => by
          c0_hsteps
          exact hL s (0#64, ()) m0 hm0 rfl hlen ⟨Nat.zero_le _, ⟨rfl, rfl⟩⟩)
        (fun J s1 (v, ()) m1 hcore1 hlen1 ⟨hvle, hpres1⟩ hm1 hL1 => ?_)
      rw [Blocks.get_here]; dsimp only [fullSafetySlice] at *
      c0_hsteps_nogrp
      · have hv_lt : v.toNat < s.core.cur_vars := by
          have h1 : v.toNat < s.core.cur_vars % 2 ^ 64 := by assumption
          omega
        have hv1 : (v + 1#64).toNat = v.toNat + 1 := by simp only [bv_c0]; omega
        have hv_tr : v.toNat < s1.scratch.tarjan_reach.length := by
          rw [hlen1.scratch_ok.tarjan_reach_len]; omega
        c0_hsteps
        exact hL1 _ (v + 1#64, ()) m hm (by dsimp only; omega) rfl
          (hlen_set_ord hlen1 _ _) ⟨by dsimp only; omega, extPres_set_ord hpres1 _ _⟩
      · exact hQ (BitVec.ofNat 64 s.core.cur_vars, ()) s1 m1 hcore1 hlen1
          ⟨by rw [hcv_mod]; exact Nat.le_refl _, hpres1⟩ hm1
  · -- Compute `has_perm` and `orig_mv`
    c0_hsteps_nogrp
    · have hlen_pos : 0 < len_bv.toNat := by
        have h1 : BitVec.toNat (0 : BitVec 64) < s.scratch.extend_len % 2 ^ 64 := by assumption
        have h0 : BitVec.toNat (0 : BitVec 64) = 0 := rfl
        have h2 : len_bv.toNat = s.scratch.extend_len % 2 ^ 64 := by
          simp [len_bv, BitVec.toNat_ofNat]
        omega
      have hlen_le : len_bv.toNat ≤ c.extend_cap := by
        have h1 : s.scratch.extend_len % 2 ^ 64 ≤ c.extend_cap % 2 ^ 64 := by assumption
        have h2 : c.extend_cap % 2 ^ 64 = c.extend_cap := Nat.mod_eq_of_lt (by omega)
        have h3 : len_bv.toNat = s.scratch.extend_len % 2 ^ 64 := by
          simp [len_bv, BitVec.toNat_ofNat]
        omega
      have h0_ext : 0 < s.scratch.extend_stk.length := by
        rw [hlen.scratch_ok.extend_stk_len]; omega
      c0_hsteps
      · let omv_bv : BitVec 64 :=
          (s.scratch.extend_stk[0]'h0_ext &&& 536870911#32).setWidth 64
        have homv_le : omv_bv.toNat ≤ c.max_vars := by
          have h1 : (s.scratch.extend_stk[0]'h0_ext &&& 536870911#32).toNat ≤
              c.max_vars % 2 ^ 64 := by assumption
          dsimp only [omv_bv]; simp only [BitVec.toNat_setWidth]
          have := (s.scratch.extend_stk[0]'h0_ext &&& 536870911#32).isLt
          omega
        have h1omv_le : 1 + omv_bv.toNat ≤ len_bv.toNat := by
          have h1 : (BitVec.toNat (1 : BitVec 64) +
              (s.scratch.extend_stk[0]'h0_ext &&& 536870911#32).toNat) % 2 ^ 64 ≤
              s.scratch.extend_len % 2 ^ 64 := by
            assumption
          have h2 : omv_bv.toNat =
              (s.scratch.extend_stk[0]'h0_ext &&& 536870911#32).toNat := by
            dsimp only [omv_bv]; simp only [BitVec.toNat_setWidth]
            have := (s.scratch.extend_stk[0]'h0_ext &&& 536870911#32).isLt
            exact Nat.mod_eq_of_lt (by omega)
          have h3 : BitVec.toNat (1 : BitVec 64) = 1 := rfl
          rw [h3, ← h2] at h1
          have h4 : len_bv.toNat = s.scratch.extend_len % 2 ^ 64 := by
            simp [len_bv, BitVec.toNat_ofNat]
          omega
        exact hJp (true, omv_bv, ()) m ⟨hm, fun _ => ⟨hlen_le, homv_le, h1omv_le⟩⟩
      · exact hJp (false, _, ()) m ⟨hm, fun h => by cases h⟩
      · exact hJp (false, _, ()) m ⟨hm, fun h => by cases h⟩
      · exact hJp (false, 0#64, ()) m ⟨hm, fun h => by cases h⟩
    · exact hJp (false, 0#64, ()) m ⟨hm, fun h => by cases h⟩
    · exact hJp (false, 0#64, ()) m ⟨hm, fun h => by cases h⟩

end LuckyOrdProof

/-! ## 2. `full_lucky_scan_tum` (`Full.fullLuckyScanSpec`) -/

section LuckyScanTumProof

open scoped FullArenaTactics FullLuckyTactics

private theorem bv64_four : (4#64 : BitVec 64) = (4 : BitVec 64) := rfl
private theorem bv64_144 : (144#64 : BitVec 64) = (144 : BitVec 64) := rfl
private theorem bv64_160 : (160#64 : BitVec 64) = (160 : BitVec 64) := rfl
private theorem bv64_168 : (168#64 : BitVec 64) = (168 : BitVec 64) := rfl
private theorem bv64_768 : (768#64 : BitVec 64) = (768 : BitVec 64) := rfl

/-- `full_lucky_scan_tum` (walking `ord[0..n)` from `full_lucky_ord_fid` with dynamic `v < cv`
guard) satisfies exact canonical `Full.fullLuckyScanSpec`. -/
theorem full_lucky_scan_tum_wp (Γ : Env)
    (hOrd : ∀ args m Q X, fullLuckyOrdFidSpec args m Q X →
      Γ "full_lucky_ord_fid" [i64] [i64] args m Q X)
    (hAssign : ∀ args m Q X, fullAssignSpec args m Q X →
      Γ "full_assign" [i64, i32, i32] [] args m Q X)
    (hBt : ∀ args m Q X, fullBacktrackSpec args m Q X →
      Γ "full_backtrack" [i64, i64] [] args m Q X)
    (hProp : ∀ args m Q X, fullPropagateSpec args m Q X →
      Γ "full_propagate" [i64] [i64] args m Q X)
    (hAna : ∀ args m Q X, fullAnalyzeSpec args m Q X →
      Γ "full_analyze" [i64] [i64] args m Q X) :
    ∀ args m Q X, fullLuckyScanSpec args m Q X →
      Func.wp Γ full_lucky_scan_tum_body args m Q X := by
  rintro ⟨h, pol?, fwd?, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hsp, hcl0, hm, hQ⟩
  unfold Func.wp full_lucky_scan_tum_body
  flk_steps
  c0_call hOrd
  refine ⟨c, s, R, rfl, hsp.1.lengths, hm,
    fun ⟨n_bv, ⟨⟩⟩ s0 m0 hcore0 hlen0 ⟨hn_le, hpres0⟩ hm0 => ?_⟩
  dsimp only [fullSafetySlice_mem, fullSafetySlice_coreProj,
    fullSafetySlice_safe] at hcore0 hlen0 hm0
  have hceq0 : s0.core = s.core := hcore0
  have hsp0 : FullSparseInv c F0 s0 := by
    refine ⟨hsp.1.with_scratch hlen0 hcore0, ?_, ?_, ?_, ?_⟩
    · unfold FullLitMarksClear FullMrkZero; rw [hceq0]; exact hsp.2.1
    · unfold FullArenaVarsNodup fullArenaClauseRefs fullArenaClauseGarb fullArenaClauseLits
      rw [hceq0]; exact hsp.2.2.1
    · exact hsp.2.2.2.1.of_pres hpres0 (fun _ hr => by
        unfold fullArenaClauseRefs at hr ⊢; rw [hceq0]; exact hr)
    · rw [hceq0]; exact hsp.2.2.2.2
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  have hcv_le0 : s.core.cur_vars ≤ c.max_vars := hsp.1.lengths.core_ok.cur_vars_le
  have hn_le_mx : n_bv.toNat ≤ c.max_vars := Nat.le_trans hn_le hcv_le0
  dsimp only
  c0_hsteps_nogrp
  have hret_bt : ∀ r (s_b : FullState) mb,
      FullSparseInv c F0 s_b → s_b.core.fuel.toNat ≤ s.core.fuel.toNat →
      (FullMem c s_b ⋆ R) mb → (r = 0#64 ∨ r = 2#64) →
      wp Γ Q X (@Expr.call Val Cont [i64] "full_backtrack" [i64, i64] []
        (Arg.var c.hdr, Arg.imm (0 : BitVec 64), PUnit.unit)
        fun _ => Expr.ret (Arg.imm r, PUnit.unit)) mb := by
    intro r s_b mb hsb hfl_b hmb hr_or
    refine call_backtrack0_ret_wp hBt hsb hfl_b hmb fun s' m' hlen' hfl' hsp' hcl0' hm' => ?_
    exact hQ r s' m' hlen' (by rcases hr_or with rfl | rfl <;> simp) hfl'
      (fun h => by rcases hr_or with rfl | rfl <;> cases h) (fun _ => ⟨hsp', hcl0'⟩)
      (fun _ => hsp'.2.2.2.1.2) hm'
  have hret_otfs_bt : ∀ F_cur (s_b : FullState) mb,
      FullOtfsInvW c F0 F_cur s_b → s_b.core.fuel.toNat ≤ s.core.fuel.toNat →
      (FullMem c s_b ⋆ R) mb →
      wp Γ Q X (@Expr.call Val Cont [i64] "full_backtrack" [i64, i64] []
        (Arg.var c.hdr, Arg.imm (0 : BitVec 64), PUnit.unit)
        fun _ => Expr.ret (Arg.imm (2 : BitVec 64), PUnit.unit)) mb := by
    intro F_cur s_b mb hotfs hfl_b hmb
    refine call_backtrack0_otfs_ret2_wp hBt hotfs hfl_b hmb
      fun s' m' hlen' hfl' hsp' hcl0' hm' => ?_
    exact hQ 2#64 s' m' hlen' (Or.inr (Or.inl rfl)) hfl'
      (fun h => absurd h (by decide)) (fun _ => ⟨hsp', hcl0'⟩) (fun _ => hsp'.2.2.2.1.2) hm'
  refine wp_loop_group (ts := [i64])
    (fun rem (idx, _) ml => ∃ st : FullState,
      rem = n_bv.toNat - idx.toNat ∧ idx.toNat ≤ n_bv.toNat ∧
      st.core.cur_vars = s.core.cur_vars ∧ FullSparseInv c F0 st ∧
      st.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c st ⋆ R) ml) ?_ ?_
  · rintro Jloop rem ⟨idx, ⟨⟩⟩ ml ih ⟨st, rfl, hidx_le, hcv_eq, hst, hfl, hml⟩
    have hcv_le := hst.1.lengths.core_ok.cur_vars_le
    dsimp [Blocks.get]
    simp only [wp_let, Op.wp, OpCode.wp, vals, Arg.val, liftCmp, CmpOp.evalBits, Ty.hasFloat]
    rw [wp_jnz]; simp only [Bool.false_eq_true, ↓reduceIte]
    refine ⟨fun hult => ?_, fun _ => ?_⟩
    · have hidx_lt : idx.toNat < n_bv.toNat := by
        have h1 : BitVec.ult idx n_bv = true := hult
        rw [BitVec.ult, decide_eq_true_eq] at h1
        exact h1
      have hidx1_nat : (idx + 1#64).toNat = idx.toNat + 1 :=
        FullLuckyTactics.bv64_add1_toNat (by omega)
      refine wp_join_group (ts := [i64]) (fun (j_bv, _) mj =>
          mj = ml ∧ j_bv.toNat < n_bv.toNat) ?_ ?_
      · rintro Jj ⟨j_bv, ⟨⟩⟩ _ ⟨rfl, hj_lt⟩
        dsimp [Blocks.get]
        have hj_tr : j_bv.toNat < st.scratch.tarjan_reach.length := by
          rw [hst.1.lengths.scratch_ok.tarjan_reach_len]; omega
        c0_hsteps_nogrp
        refine wp_load_of (FullArenaTactics.c0_load_full_tarjan_reach hj_tr hml) ?_
        c0_hsteps_nogrp
        refine wp_join_group (ts := []) (fun _ mn =>
            ∃ st' : FullState, st'.core.cur_vars = s.core.cur_vars ∧
              FullSparseInv c F0 st' ∧ st'.core.fuel.toNat ≤ s.core.fuel.toNat ∧
              (FullMem c st' ⋆ R) mn) ?_ ?_
        · rintro Jnext ⟨⟩ mn ⟨st', hcv', hst', hfl', hmn⟩
          dsimp [Blocks.get]
          flk_steps
          exact ih (n_bv.toNat - (idx.toNat + 1)) (idx + 1#64, PUnit.unit) mn (by omega)
            ⟨st', by simp [hidx1_nat], by omega, hcv', hst', hfl', hmn⟩
        · intro Jnext hJnext
          c0_hsplit
          · -- `v < cv` branch
            let v : BitVec 64 := (st.scratch.tarjan_reach[j_bv.toNat]'hj_tr).setWidth 64
            have hv_lt : v.toNat < st.core.cur_vars := by
              have h1 : (st.scratch.tarjan_reach[j_bv.toNat]'hj_tr).toNat <
                  s.core.cur_vars % 2 ^ 64 := by assumption
              dsimp only [v]; simp only [BitVec.toNat_setWidth]
              have := (st.scratch.tarjan_reach[j_bv.toNat]'hj_tr).isLt
              rw [hcv_eq]; omega
            have hv_fl : v.toNat < st.core.flags.length := by
              have := hst.1.lengths.core_ok.flags_len; omega
            have hv2_vl : (v <<< 1#64).toNat < st.core.vals.length := by
              have := hst.1.lengths.core_ok.vals_len
              rw [FullLuckyTactics.bv64_shl1_toNat (by omega)]; omega
            flk_unmdata
            simp only [bv64_four, bv64_144, bv64_160, bv64_168, bv64_768]
            flk_to_group
            · exact hret_bt 2#64 st _ hst hfl hml (Or.inr rfl)
            · have hfl_ne : st.core.fuel ≠ 0#64 := by simpa using hc
              have hfl_sub : (st.core.fuel - 1#64).toNat = st.core.fuel.toNat - 1 :=
                FullLuckyTactics.bv64_sub1_toNat hfl_ne
              have hval0 : st.core.vals[2 * v.toNat]?.getD 0#8 = 0#8 := by
                have h2v : (v <<< 1#64).toNat = 2 * v.toNat :=
                  FullLuckyTactics.bv64_shl1_toNat (by omega)
                have h_eq : BitVec.signExtend 32 st.core.vals[2 * v.toNat % 2 ^ 64] = 0#32 := by
                  assumption
                have h_mod : 2 * v.toNat % 2 ^ 64 = 2 * v.toNat := by omega
                rw [FullLuckyTactics.bv8_sext32_eq0_iff] at h_eq
                have hv2_lt : 2 * v.toNat < st.core.vals.length := by
                  rw [← h2v]; exact hv2_vl
                have h_eq0 : st.core.vals[2 * v.toNat] = 0#8 := by simpa [h_mod] using h_eq
                simp [List.getElem?_eq_getElem hv2_lt, h_eq0]
              let st1 : FullState :=
                { st with core := { st.core with fuel := st.core.fuel - 1#64 } }
              have hst1 : FullSparseInv c F0 st1 :=
                FullSparseInv.with_fuel hst (st.core.fuel - 1#64)
              have hfl1 : st1.core.fuel.toNat ≤ s.core.fuel.toNat := by
                change (st.core.fuel - 1#64).toNat ≤ s.core.fuel.toNat; rw [hfl_sub]; omega
              refine wp_join_group (ts := [i32]) (fun (lit, _) mlit =>
                  (FullMem c st1 ⋆ R) mlit ∧ lit.toNat / 2 = v.toNat) ?_ ?_
              · rintro Jlit ⟨lit, ⟨⟩⟩ mlit ⟨hmlit, hlit_v⟩
                dsimp [Blocks.get]
                obtain ⟨hte_lt1, _, _, hnlvl_bv, hft_len, hfd_len, hnlvl_ne⟩ :=
                  decide_nlvl_ok hst1 hv_lt hval0
                have hte32_1 : st1.core.trail_end < 2 ^ 32 := by
                  have := hst1.1.lengths.core_ok.cur_vars_le; omega
                flk_unmdata
                simp only [bv64_four, bv64_144, bv64_160, bv64_768]
                c0_steps!
                rw [hnlvl_bv, FullLuckyTactics.bv64_trunc32_ofNat hte32_1] at *
                refine call_assign_prop_decide_wp (R := R) hAssign hProp hst1 hfl1 hv_lt hval0
                  hlit_v (by assumption) fun r1 F_cur1 s_asn1 s_p1 mp1 hlen1 hsp1 hw1 hcl1 hcv1
                    hfl_p1 hr1 hcf1 htr1 hte1 htrl1 hlvl1 hmp1 => ?_
                flk_unmdata
                flk_to_group
                · exact hret_bt 2#64 s_p1 mp1 hsp1 hfl_p1 hmp1 (Or.inr rfl)
                · refine wp_join_group (ts := [i64]) (fun (_, _) m_a =>
                      ∃ s_a : FullState, s_a.core.cur_vars = s.core.cur_vars ∧
                        FullSparseInv c F0 s_a ∧ s_a.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                        (FullMem c s_a ⋆ R) m_a) ?_ ?_
                  · rintro Jafter2 ⟨_, ⟨⟩⟩ m_a ⟨s_a, hcv_a, hsp_a, hfl_a, hm_a⟩
                    dsimp [Blocks.get]; flk_steps
                    exact hJnext PUnit.unit m_a ⟨s_a, hcv_a, hsp_a, hfl_a, hm_a⟩
                  · intro Jafter2 hJafter2
                    flk_unmdata; flk_to_group
                    · have hr1_eq : r1 = 1#64 := by assumption
                      refine wp_join_group (ts := [i64]) (fun (_, _) m_a =>
                          ∃ s_a : FullState, s_a.core.cur_vars = s.core.cur_vars ∧
                            FullSparseInv c F0 s_a ∧ s_a.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                            (FullMem c s_a ⋆ R) m_a) ?_ ?_
                      · rintro Jbt ⟨_, ⟨⟩⟩ m_a ⟨s_a, hcv_a, hsp_a, hfl_a, hm_a⟩
                        dsimp [Blocks.get]; flk_steps
                        exact hJafter2 _ m_a ⟨s_a, hcv_a, hsp_a, hfl_a, hm_a⟩
                      · intro Jbt hJbt
                        flk_unmdata
                        simp only [bv64_168]
                        flk_to_group
                        · have hcl_lt64 : s_p1.core.cur_level < 2 ^ 64 := by
                            have := hw1.cur_level_le
                            have := hlen1.core_ok.trail_end_le
                            have := hlen1.core_ok.cur_vars_le; omega
                          have hcl_mod : 1 < s_p1.core.cur_level % 2 ^ 64 := by simpa using hc
                          have hcl_gt1 : 1 < s_p1.core.cur_level := by omega
                          have hcl_bv : (BitVec.ofNat 64 s_p1.core.cur_level - 1#64).toNat =
                              st1.core.cur_level := by
                            rw [hcl1]; bv_omega
                          c0_call hBt
                          refine ⟨c, s_p1, R, rfl, hlen1, hcl_lt64,
                            fun _ => by
                              have := hlen1.core_ok.cur_vars_le
                              rw [hcl_bv, hcl1] at *; omega,
                            hw1.trail_lits_lt, hmp1, ?_⟩
                          dsimp only
                          intro vals_b lvl_b rsns_b trl_b tp_b te_b prop_b cl_b unass_b sc_b mb
                            hlen_b hte_b hprop_b hcl_b hps_b hsh_b htrl_b hbv_b hwt_b hot_b hmb
                          let s_b : FullState :=
                            { core := { s_p1.core with
                                vals := vals_b, lvl := lvl_b, rsns := rsns_b, trl := trl_b,
                                trail_pos := tp_b, trail_end := te_b, propagated := prop_b,
                                cur_level := cl_b, unassigned := unass_b }
                              scratch := sc_b }
                          have hsp_b : FullSparseInv c F0 s_b :=
                            fullSparseInv_of_fullBacktrack hsp1 hlen_b
                              (hwt_b F0 F_cur1 hw1 (by rw [hcl_bv, hcl1]; omega))
                              rfl rfl rfl rfl rfl hps_b.1.1 hps_b.1.2
                          have hv_lt_b : v.toNat < s_b.core.cur_vars := by
                            change v.toNat < s_p1.core.cur_vars
                            rw [hcv1]; exact hv_lt
                          have hval0_b : s_b.core.vals[2 * v.toNat]?.getD 0#8 = 0#8 := by
                            refine scan_backtrack_unassigned hlit_v hte1 htrl1 hlvl1 ?_ htr1
                              (by rw [hcv1]; exact Nat.mul_lt_mul_of_pos_left hv_lt (by decide)) ?_
                            · change st1.core.cur_level + 1 < 2 ^ 32; omega
                            · intro l hl
                              have := (hbv_b ⟨F0, F_cur1, Or.inl hw1⟩).1 l hl
                              simpa [hcl_bv] using this
                          flk_unmdata
                          c0_step; (repeat flk_strip); c0_step
                          · exact hret_bt 2#64 s_b mb hsp_b hfl_p1 hmb (Or.inr rfl)
                          · have hfl_ne_b : s_b.core.fuel ≠ 0#64 := hc
                            have hfl_sub_b : (s_b.core.fuel - 1#64).toNat =
                                s_b.core.fuel.toNat - 1 :=
                              FullLuckyTactics.bv64_sub1_toNat hfl_ne_b
                            let s_b1 : FullState :=
                              { s_b with core := { s_b.core with fuel := s_b.core.fuel - 1#64 } }
                            have hsb1 : FullSparseInv c F0 s_b1 :=
                              FullSparseInv.with_fuel hsp_b (s_b.core.fuel - 1#64)
                            have hfl_b1 : s_b1.core.fuel.toNat ≤ s.core.fuel.toNat := by
                              change (s_b.core.fuel - 1#64).toNat ≤ s.core.fuel.toNat
                              rw [hfl_sub_b]
                              have : s_b.core.fuel.toNat ≤ s.core.fuel.toNat := hfl_p1
                              omega
                            have hval0_b1 : s_b1.core.vals[2 * v.toNat]?.getD 0#8 = 0#8 := hval0_b
                            obtain ⟨_, _, _, hnlvl_b1, hft_b1, hfd_b1, hne_b1⟩ :=
                              decide_nlvl_ok hsb1 hv_lt_b hval0_b1
                            have hte32_b1 : s_b1.core.trail_end < 2 ^ 32 := by
                              have := hsb1.1.lengths.core_ok.cur_vars_le; omega
                            flk_unmdata
                            c0_steps!
                            rw [hnlvl_b1, FullLuckyTactics.bv64_trunc32_ofNat hte32_b1] at *
                            refine call_assign_prop_decide_wp (R := R) hAssign hProp hsb1 hfl_b1
                              hv_lt_b hval0_b1
                              ((FullLuckyHelpers.bv32_xor1_div2 lit).trans hlit_v)
                              (by assumption)
                              fun r2 F_cur2 s_asn2 s_p2 mp2 hlen2 hsp2 hw2 hcl2 hcv2 hfl_p2 hr2 hcf2
                                htr2 hte2 htrl2 hlvl2 hmp2 => ?_
                            flk_unmdata; flk_to_group
                            · exact hret_bt 2#64 s_p2 mp2 hsp2 hfl_p2 hmp2 (Or.inr rfl)
                            · exact hret_bt 0#64 s_p2 mp2 hsp2 hfl_p2 hmp2 (Or.inl rfl)
                            · flk_steps
                              exact hJbt _ mp2 ⟨s_p2, by
                                change s_p2.core.cur_vars = s.core.cur_vars
                                rw [hcv2]; change s_b.core.cur_vars = s.core.cur_vars
                                change s_p1.core.cur_vars = s.core.cur_vars
                                rw [hcv1]; exact hcv_eq, hsp2, hfl_p2, hmp2⟩
                        · have hcl_mod : s_p1.core.cur_level % 2 ^ 64 ≤ 1 := by simpa using hc
                          have hcl_lt64 : s_p1.core.cur_level < 2 ^ 64 := by
                            have := hw1.cur_level_le
                            have := hlen1.core_ok.trail_end_le
                            have := hlen1.core_ok.cur_vars_le; omega
                          have hcl_eq1 : s_p1.core.cur_level = 1 := by omega
                          refine scan_ana_branch_wp hProp hAna hsp1 hw1 hcl_eq1 (hcf1 hr1_eq)
                            hfl_p1 hmp1
                            (fun s_b mb hsb hfl_b hmb =>
                              hret_bt 2#64 s_b mb hsb hfl_b hmb (Or.inr rfl))
                            (fun s_b mb hotfs hfl_b hmb =>
                              hret_otfs_bt F_cur1 s_b mb hotfs hfl_b hmb)
                            (fun s_u mu hlen_u hfl_u huns hmu =>
                              hQ 20#64 s_u mu hlen_u (Or.inr (Or.inr (Or.inr rfl))) hfl_u
                                (fun _ => huns) (fun h => by rcases h with h | h <;> cases h)
                                (fun h => by cases h) hmu)
                            (fun s_o mo hcv_o hsp_o hfl_o hmo =>
                              hJbt _ mo ⟨s_o, by
                                change s_o.core.cur_vars = s.core.cur_vars
                                rw [hcv_o]; change s_p1.core.cur_vars = s.core.cur_vars
                                rw [hcv1]; exact hcv_eq, hsp_o, hfl_o, hmo⟩)
                    · flk_steps
                      exact hJafter2 _ mp1 ⟨s_p1, by
                        change s_p1.core.cur_vars = s.core.cur_vars
                        rw [hcv1]; exact hcv_eq, hsp1, hfl_p1, hmp1⟩
              · intro Jlit hJlit; flk_steps
                · have hl : (BitVec.setWidth 32 (v <<< 1)).toNat = 2 * v.toNat := by bv_omega
                  exact hJlit _ _ ⟨‹_›, by rw [hl]; omega⟩
                · have h_eq1 : (v <<< 1) = (v <<< 1#64) := rfl
                  have hl : (BitVec.setWidth 32 (v <<< 1) ||| 1#32).toNat = 2 * v.toNat + 1 := by
                    rw [h_eq1]; exact FullLuckyTactics.bv32_shl1_or1_trunc32_toNat (by omega)
                  exact hJlit _ _ ⟨‹_›, by rw [hl]; omega⟩
            · exact hJnext PUnit.unit _ ⟨st, hcv_eq, hst, hfl, hml⟩
            · exact hJnext PUnit.unit _ ⟨st, hcv_eq, hst, hfl, hml⟩
          · c0_hsteps; exact hJnext PUnit.unit _ ⟨st, hcv_eq, hst, hfl, hml⟩
      · intro Jj hJj
        flk_steps
        · exact hJj _ ml ⟨rfl, hidx_lt⟩
        · have hsub_nat : (n_bv - 1#64 - idx).toNat = n_bv.toNat - 1 - idx.toNat := by bv_omega
          exact hJj _ ml ⟨rfl, by rw [hsub_nat]; omega⟩
    · flk_steps
      exact hQ 10#64 st ml hst.1.lengths (Or.inr (Or.inr (Or.inl rfl))) hfl
        (fun h => absurd h (by decide)) (fun h => by rcases h with h | h <;> cases h)
        (fun _ => hst.2.2.2.1.2) hml
  · intro Jloop hJloop; flk_steps
    exact hJloop n_bv.toNat (0#64, PUnit.unit) m0
      ⟨s0, by simp, Nat.zero_le _, hceq0 ▸ rfl, hsp0, by rw [hceq0]; exact Nat.le_refl _, hm0⟩

end LuckyScanTumProof

end LeanQbe.T.Examples.Kissat.FullFidelityTumble

end
