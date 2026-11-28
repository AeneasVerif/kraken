/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Bump.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Bump.Helpers
public import LeanQbe.T.Examples.Kissat.Proof.Bump.WpBumpHelpers
import LeanQbe.T.Examples.Kissat.Proof.Lib.ContractLemmas
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Header
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts1
public import LeanQbe.T.Examples.Kissat.Proof.Tiers.Spec
public import LeanQbe.T.Examples.Kissat.Src.Bump
public import LeanQbe.T.Logic.CanonicalEnv
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
meta import LeanQbe.T.Logic.C0Step
meta import LeanQbe.T.Logic.C0HeadStep

/-!
# Canonical WP Proof for `full_bump_analyzed_mode_fid`

Proves `Func.wp Γ full_bump_analyzed_mode_fid_body` against `Spec.fullBumpAnalyzedModeSpec`
using `FullBumpInv`, `FullAnaMarksCov` push/pop/sort preservation, and `FullMem` + `m6ExtMem`
call wrappers (`0` legacy `Full*` imports, `0` SAT model proofs).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Bump

open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Bump
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Tiers.Spec
open LeanQbe.T.Examples.Kissat.Proof.Bump.Spec
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics

/-! ## 1. BitVec, Bounds, and Push-Update Helpers -/

private theorem bv_zext32_64_toNat (x : BitVec 32) :
    (BitVec.setWidth 64 x).toNat = x.toNat :=
  zext_toNat x (by decide)

private theorem bv_trunc8_one : BitVec.setWidth 8 (1#32 : BitVec 32) = 1#8 := rfl

private theorem bv64_mcl_p1_toNat {mcl : Nat} (h : mcl + 1 < 2 ^ 64) :
    (BitVec.ofNat 64 mcl + 1#64).toNat = mcl + 1 := by
  have hm : (BitVec.ofNat 64 mcl).toNat = mcl := bv64_ofNat_toNat (by omega)
  bv_omega

private theorem bv64_mcl_m1_toNat {mcl : Nat} (hgt : 0 < mcl) (h : mcl < 2 ^ 64) :
    (BitVec.ofNat 64 mcl - 1).toNat = mcl - 1 := by
  have hm : (BitVec.ofNat 64 mcl).toNat = mcl := bv64_ofNat_toNat h
  bv_omega

private theorem bv_ov_lt_of_c0 {ov : BitVec 32} {cv : Nat} (hcv : cv < 2 ^ 64)
    (hc : (BitVec.setWidth 64 ov).toNat < (BitVec.ofNat 64 cv).toNat) : ov.toNat < cv := by
  rwa [bv_zext32_64_toNat, bv64_ofNat_toNat hcv] at hc

private theorem bv_mcl_lt_of_c0 {mcl cv : Nat} (hmcl : mcl < 2 ^ 64) (hcv : cv < 2 ^ 64)
    (hc : (BitVec.ofNat 64 mcl).toNat < (BitVec.ofNat 64 cv).toNat) : mcl < cv := by
  rwa [bv64_ofNat_toNat hmcl, bv64_ofNat_toNat hcv] at hc

private theorem list_getElem_idx_eq {α : Type _} (xs : List α) {i j : Nat}
    (h : i = j) (hi : i < xs.length) (hj : j < xs.length) :
    xs[i]'hi = xs[j]'hj := by
  subst h; rfl

private theorem bv32_zext8_eq_zero {x : BitVec 8}
    (h : BitVec.setWidth 32 x = BitVec.ofNat 32 0) : x = 0#8 := by bv_omega

private theorem bv32_ushr1_toNat (x : BitVec 32) : (x >>> 1#32).toNat = x.toNat / 2 := by
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

private theorem mrk_getElem?_of_zext32 {mrk : List (BitVec 8)} {ov : BitVec 32} {idx : Nat}
    (hidx : ov.toNat = idx) (hlen : ov.toNat < mrk.length)
    (hc : ∀ h_d : idx < mrk.length,
      BitVec.setWidth 32 (mrk[idx]'h_d) = BitVec.ofNat 32 0) :
    mrk[ov.toNat]? = some 0#8 := by
  have hlen_d : idx < mrk.length := by rwa [← hidx]
  rw [List.getElem?_eq_getElem hlen]
  congr 1
  exact (list_getElem_idx_eq mrk hidx hlen hlen_d).trans (bv32_zext8_eq_zero (hc hlen_d))

private abbrev BumpPExt (c : FullCfg) (ext0 : List (BitVec 64)) (s0 : FullState)
    (R : Mem 64 → Prop) (allow : Bool) (ext : List (BitVec 64)) (s : FullState)
    (m1 : Mem 64) : Prop :=
  (FullMem c s ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R)) m1 ∧ FullBumpInv allow c ext0 s0 ext s

private abbrev BumpPJoin (c : FullCfg) (ext0 : List (BitVec 64)) (s0 : FullState)
    (R : Mem 64 → Prop) (allow : Bool) : Tup Val [] → Mem 64 → Prop :=
  fun _ m1 => ∃ ext1 s1, BumpPExt c ext0 s0 R allow ext1 s1 m1

private abbrev BumpPKInv (c : FullCfg) (ext0 : List (BitVec 64)) (s0 : FullState)
    (R : Mem 64 → Prop) (allow : Bool) (cnt : Nat) : Tup Val [i64] → Mem 64 → Prop :=
  fun (k, ()) m1 => ∃ ext1 s1, k.toNat ≤ s1.core.min_clr_len ∧
    BumpPExt c ext0 s0 R allow ext1 s1 m1 ∧ s1.core.min_clr_len = cnt

private abbrev BumpPKJoin (c : FullCfg) (ext0 : List (BitVec 64)) (s0 : FullState)
    (R : Mem 64 → Prop) (allow : Bool) (cnt : Nat) : Tup Val [] → Mem 64 → Prop :=
  fun _ m1 => ∃ ext1 s1, BumpPExt c ext0 s0 R allow ext1 s1 m1 ∧ s1.core.min_clr_len = cnt

private theorem fullBump_rollback_pop_false {ws : List (BitVec 32)} {mcl cv rv : Nat}
    (hgt : 0 < mcl) (hmcl : mcl < 2 ^ 64) (hcv : cv < 2 ^ 64) (hrv : rv < cv)
    (hna : mcl - 1 < ws.length) (hidx_eq : rv = (ws[mcl - 1]'hna).toNat)
    (hc : ∀ h_na : (2 ^ 64 - BitVec.toNat (1#64 : BitVec 64) + mcl) % 2 ^ 64 % 2 ^ 64 <
        ws.length,
      ¬ (ws[(2 ^ 64 - BitVec.toNat (1#64 : BitVec 64) + mcl) % 2 ^ 64 % 2 ^ 64]'h_na).toNat <
        cv % 2 ^ 64) : False := by
  have hm1 : (2 ^ 64 - BitVec.toNat (1#64 : BitVec 64) + mcl) % 2 ^ 64 % 2 ^ 64 = mcl - 1 := by
    have h1 : BitVec.toNat (1#64 : BitVec 64) = 1 := rfl
    omega
  have hna' : (2 ^ 64 - BitVec.toNat (1#64 : BitVec 64) + mcl) % 2 ^ 64 % 2 ^ 64 < ws.length := by
    rwa [hm1]
  have hc' := hc hna'
  have hget := congrArg BitVec.toNat (list_getElem_idx_eq ws hm1 hna' hna)
  rw [hget, Nat.mod_eq_of_lt hcv] at hc'
  exact hc' (by rw [← hidx_eq]; exact hrv)

private theorem fullBump_rsn2_lt {c : FullCfg} {s4 : FullState} {rsn : BitVec 32}
    (hlen4 : FullState.LengthsOk c s4) (hmaxa : c.arena_cap < 2 * 2 ^ 28)
    (h1 : (rsn.setWidth 64 + 3#64).toNat ≤ (BitVec.ofNat 64 s4.core.arena_len).toNat) :
    (rsn.setWidth 64 + 2#64).toNat < s4.core.arena.length := by
  have := hlen4.core_ok.arena_len_arr
  have := hlen4.core_ok.arena_len_le
  have := bv_zext32_64_toNat rsn; have := rsn.isLt
  rw [bv64_ofNat_toNat (by omega)] at h1; bv_omega

private theorem fullBump_sz_sum_le {c : FullCfg} {s4 : FullState} {rsn : BitVec 32}
    (hlen4 : FullState.LengthsOk c s4) (hmaxa : c.arena_cap < 2 * 2 ^ 28)
    (hrsn_2 : (rsn.setWidth 64 + 2#64).toNat < s4.core.arena.length)
    (h1 : (rsn.toNat + 3 + (s4.core.arena[(rsn.toNat + 2) % 2 ^ 64]'(by
      have := bv_zext32_64_toNat rsn; have := rsn.isLt
      have hidx : (rsn.setWidth 64 + 2#64).toNat = (rsn.toNat + 2) % 2 ^ 64 := by bv_omega
      rw [← hidx]; exact hrsn_2)).toNat) % 2 ^ 64 ≤ s4.core.arena_len % 2 ^ 64) :
    rsn.toNat + 3 + (s4.core.arena[(rsn.setWidth 64 + 2#64).toNat]'hrsn_2).toNat ≤
      s4.core.arena.length := by
  have hidx : (rsn.setWidth 64 + 2#64).toNat = (rsn.toNat + 2) % 2 ^ 64 := by
    have := bv_zext32_64_toNat rsn; have := rsn.isLt; bv_omega
  have hna : (rsn.toNat + 2) % 2 ^ 64 < s4.core.arena.length := by rw [← hidx]; exact hrsn_2
  have heq := list_getElem_idx_eq s4.core.arena hidx hrsn_2 hna
  rw [← heq] at h1
  have := hlen4.core_ok.arena_len_arr
  have := hlen4.core_ok.arena_len_le
  have := rsn.isLt
  have := (s4.core.arena[(rsn.setWidth 64 + 2#64).toNat]'hrsn_2).isLt
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h1
  omega

private theorem fullBump_har_j_lt {c : FullCfg} {s4 : FullState}
    (hlen4 : FullState.LengthsOk c s4) (_ : c.arena_cap < 2 * 2 ^ 28)
    {rsn j sz : BitVec 32} (hj_lt : j.toNat < sz.toNat)
    (hsum_le : rsn.toNat + 3 + sz.toNat ≤ s4.core.arena.length) :
    ((rsn.setWidth 64 + 3#64) + j.setWidth 64).toNat < s4.core.arena.length := by
  have := hlen4.core_ok.arena_len_arr; have := hlen4.core_ok.arena_len_le
  have := bv_zext32_64_toNat rsn; have := bv_zext32_64_toNat j
  have := rsn.isLt; have := j.isLt; bv_omega

private theorem fullBump_har_jn_lt {c : FullCfg} {s4 s5 : FullState}
    (hlen4 : FullState.LengthsOk c s4) (hmaxa : c.arena_cap < 2 * 2 ^ 28)
    (hare5 : s5.core.arena = s4.core.arena) {rsn j : BitVec 32}
    (har_j : ((rsn.setWidth 64 + 3#64) + j.setWidth 64).toNat < s5.core.arena.length) :
    (rsn.toNat + 3 + j.toNat) % 2 ^ 64 < s5.core.arena.length := by
  have := hlen4.core_ok.arena_len_arr; have := hlen4.core_ok.arena_len_le
  have := bv_zext32_64_toNat rsn; have := bv_zext32_64_toNat j
  have := rsn.isLt; have := j.isLt
  have h1 : ((rsn.setWidth 64 + 3#64) + j.setWidth 64).toNat =
      (rsn.toNat + 3 + j.toNat) % 2 ^ 64 := by rw [hare5] at har_j; bv_omega
  rwa [← h1]

private theorem fullBump_j_idx_eq {c : FullCfg} {s4 s5 : FullState}
    (hlen4 : FullState.LengthsOk c s4) (hmaxa : c.arena_cap < 2 * 2 ^ 28)
    (hare5 : s5.core.arena = s4.core.arena) {rsn j : BitVec 32}
    (har_j : ((rsn.setWidth 64 + 3#64) + j.setWidth 64).toNat < s5.core.arena.length)
    (har_jn : (rsn.toNat + 3 + j.toNat) % 2 ^ 64 < s5.core.arena.length) :
    ((s5.core.arena[((rsn.setWidth 64 + 3#64) + j.setWidth 64).toNat]'har_j) >>> 1#32).toNat =
      (s5.core.arena[(rsn.toNat + 3 + j.toNat) % 2 ^ 64]'har_jn).toNat / 2 := by
  have := hlen4.core_ok.arena_len_arr; have := hlen4.core_ok.arena_len_le
  have := bv_zext32_64_toNat rsn; have := bv_zext32_64_toNat j
  have := rsn.isLt; have := j.isLt
  have h1 : ((rsn.setWidth 64 + 3#64) + j.setWidth 64).toNat =
      (rsn.toNat + 3 + j.toNat) % 2 ^ 64 := by rw [hare5] at har_j; bv_omega
  rw [bv32_ushr1_toNat, list_getElem_idx_eq s5.core.arena h1 har_j har_jn]

private theorem fullBump_j_ov_lt {c : FullCfg} {s4 s5 : FullState}
    (hlen4 : FullState.LengthsOk c s4) (hmaxa : c.arena_cap < 2 * 2 ^ 28)
    (hare5 : s5.core.arena = s4.core.arena) (cv : Nat) (hcv : cv < 2 ^ 64)
    {rsn j : BitVec 32}
    (har_j : ((rsn.setWidth 64 + 3#64) + j.setWidth 64).toNat < s5.core.arena.length)
    (hc : ∀ h_n : (rsn.toNat + BitVec.toNat (3 : BitVec 64) + j.toNat) % 2 ^ 64 <
        s5.core.arena.length,
      (s5.core.arena[(rsn.toNat + BitVec.toNat (3 : BitVec 64) + j.toNat) %
        2 ^ 64]'h_n).toNat / 2 < cv % 2 ^ 64) :
    ((s5.core.arena[((rsn.setWidth 64 + 3#64) + j.setWidth 64).toNat]'har_j) >>> 1#32).toNat <
      cv := by
  have := hlen4.core_ok.arena_len_arr; have := hlen4.core_ok.arena_len_le
  have := bv_zext32_64_toNat rsn; have := bv_zext32_64_toNat j
  have := rsn.isLt; have := j.isLt
  have hidx : ((rsn.setWidth 64 + 3#64) + j.setWidth 64).toNat =
      (rsn.toNat + BitVec.toNat (3 : BitVec 64) + j.toNat) % 2 ^ 64 := by
    rw [hare5] at har_j; change _ = (rsn.toNat + 3 + j.toNat) % 2 ^ 64; bv_omega
  have hn : (rsn.toNat + BitVec.toNat (3 : BitVec 64) + j.toNat) % 2 ^ 64 <
      s5.core.arena.length := by rwa [← hidx]
  have hget := congrArg BitVec.toNat (list_getElem_idx_eq s5.core.arena hidx har_j hn)
  have hc' := hc hn
  rw [Nat.mod_eq_of_lt hcv] at hc'
  rw [bv32_ushr1_toNat, hget]
  exact hc'

private theorem fullBumpInv_push_mem_norm {c : FullCfg} {ext0 ext1 : List (BitVec 64)}
    {s0 s1 : FullState} (inv : FullBumpInv true c ext0 s0 ext1 s1) (hcov0 : FullAnaMarksCov c s0)
    (ov : BitVec 32) {R : Mem 64 → Prop} {m' : Mem 64}
    (hm' : (FullMem c
      { s1 with
        core := { s1.core with
          mrk := s1.core.mrk.set (BitVec.setWidth 64 ov).toNat (BitVec.setWidth 8 (1#32))
          min_clr_len := (BitVec.ofNat 64 s1.core.min_clr_len + 1#64).toNat }
        scratch := { s1.scratch with
          work_stk1 := s1.scratch.work_stk1.set
            (BitVec.ofNat 64 s1.core.min_clr_len).toNat ov } } ⋆
      (m6ExtMem (m6ExtAddr c.hdr) ext1 ⋆ R)) m')
    (hov_lt : ov.toNat < s0.core.cur_vars)
    (hmrk0 : s1.core.mrk[ov.toNat]? = some 0#8)
    (hmcl_lt : s1.core.min_clr_len < s0.core.cur_vars) :
    let s2 : FullState :=
      { s1 with
        core := { s1.core with
          mrk := s1.core.mrk.set ov.toNat 1#8
          min_clr_len := s1.core.min_clr_len + 1 }
        scratch := { s1.scratch with
          work_stk1 := s1.scratch.work_stk1.set s1.core.min_clr_len ov } }
    (FullMem c s2 ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext1 ⋆ R)) m' ∧
      FullBumpInv true c ext0 s0 ext1 s2 := by
  have hmaxv : c.max_vars < 2 * Ref.dimacsBound := c.hmaxv
  unfold Ref.dimacsBound at hmaxv
  have hcv_le := inv.len.core_ok.cur_vars_le
  have hcv_eq : s1.core.cur_vars = s0.core.cur_vars := by rw [inv.shape]
  have hm1 : (BitVec.ofNat 64 s1.core.min_clr_len).toNat = s1.core.min_clr_len :=
    bv64_ofNat_toNat (by omega)
  have hm2 : (BitVec.ofNat 64 s1.core.min_clr_len + 1#64).toNat = s1.core.min_clr_len + 1 :=
    bv64_mcl_p1_toNat (by omega)
  rw [bv_zext32_64_toNat, bv_trunc8_one, hm1, hm2] at hm'
  exact ⟨hm', fullBumpInv_push inv hcov0 hov_lt hmrk0 hmcl_lt⟩

/-! ## 2. Main `full_bump_analyzed_mode_fid_wp` Theorem -/

public section

theorem full_bump_analyzed_mode_fid_wp (Γ : Env)
    (hDelay : Γ.Has "m6_hdr_delaying" (m6HdrW2aSpec [i64] [.bool]))
    (hDrAllow : Γ.Has "m6_hdr_dr_allow" m6HdrDrAllowSpec)
    (hBumpDelay : Γ.Has "m6_hdr_bump_delay" (m6HdrW2aSpec [i64] []))
    (hReduceDelay : Γ.Has "m6_hdr_reduce_delay" (m6HdrW2aSpec [i64] []))
    (hSortAna : Γ.Has "full_sort_ana_qs_m6" sortAnaQsSpec)
    (hMtf : Γ.Has "full_queue_mtf" queueMtfSpec)
    (hBumpVar : Γ.Has "full_bump_var" bumpVarSpec)
    (hBumpDecay : Γ.Has "full_bump_decay" rescaleSpec) :
    ∀ a m Q X, bumpAnalyzedModeSpec a m Q X →
      Func.wp Γ full_bump_analyzed_mode_fid_body a m Q X := by
  rintro ⟨h, allow_reasons, ⟨⟩⟩ m Q X hs
  obtain ⟨c, ext0, s0, ⟨⟩, R, rfl, hcfg, hext0, hlen0, hpre0, hm0, hQ0⟩ := M6HdrContract.elim hs
  let hQ : ∀ mrk' mcl' repr' sc' ext' m',
      let s' : FullState :=
        { s0 with
          core := { s0.core with mrk := mrk', min_clr_len := mcl', repr := repr' }
          scratch := sc' }
      s'.LengthsOk c →
      (FullAnaMarksCov c s0 → FullAnaMarksCov c s') →
      (allow_reasons = false → mrk' = s0.core.mrk ∧ mcl' = s0.core.min_clr_len ∧ ext' = ext0) →
      (allow_reasons = false →
        ∀ k < mcl', (sc'.work_stk1[k]?.getD 0#32).toNat < s0.core.cur_vars) →
      FullExtScratchPres s0 s' → sc'.work_stk2 = s0.scratch.work_stk2 →
      M6HdrExtOk ext' → (M6HdrExtInitOk ext0 → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext0 ext') →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q () m' :=
    fun mrk' mcl' repr' sc' ext' m' hlen' hcov' hfp' hk' hpres' hws2' hext' hinit' hm' =>
      hQ0 () ext' _ m' hext' hinit' hlen'
        ⟨rfl, hcov', hfp', hk', hpres', hws2'⟩ hm'
  have hmaxv : c.max_vars < 2 * Ref.dimacsBound := c.hmaxv
  have harena : c.arena_cap < 2 * Ref.dimacsBound := c.harena
  unfold Ref.dimacsBound at hmaxv harena
  have hcv_le0 := hlen0.core_ok.cur_vars_le
  let PExt := BumpPExt c ext0 s0 R
  let PJoin := BumpPJoin c ext0 s0 R
  let PKInv := BumpPKInv c ext0 s0 R
  let PKJoin := BumpPKJoin c ext0 s0 R
  unfold Func.wp full_bump_analyzed_mode_fid_body
  dsimp only
  have hm0_f : (FullMem c s0 ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext0 ⋆ R)) m :=
    fullM6HdrMem_focus_full hm0
  c0_hsteps_nogrp
  · exact hQ s0.core.mrk s0.core.min_clr_len s0.core.repr s0.scratch ext0 m hlen0
      (fun h => h) (fun _ => ⟨rfl, rfl, rfl⟩)
      (fun hf k hk => by rw [hf] at hpre0; exact hpre0.2 k hk)
      ⟨rfl, rfl⟩ rfl hext0 (fun hi => ⟨hi, M6ExtW2bPres.refl ext0⟩) hm0
  · let inv0 := fullBumpInv_init hlen0 hext0 hpre0
    refine wp_join_group (ts := []) (PJoin allow_reasons) ?_ ?_
    · -- Phase 2 (`cnt = h->min_clr_len`; sort + MTF if `stable == 0`, else bump_var + decay)
      intro _ _ m_p ⟨ext_p, s_p, hm_p, inv_p⟩
      rw [Blocks.get_here]
      have hcv_p : s_p.core.cur_vars = s0.core.cur_vars := by rw [inv_p.shape]
      have hmcl_p := inv_p.mcl_le
      have hcnt_nat : (BitVec.ofNat 64 s_p.core.min_clr_len).toNat = s_p.core.min_clr_len :=
        bv64_ofNat_toNat (by omega)
      c0_hsteps_nogrp
      refine wp_join_group (ts := []) (PJoin allow_reasons) ?_ ?_
      · intro _ _ m_e ⟨ext_e, s_e, hm_e, inv_e⟩
        rw [Blocks.get_here]
        c0_hsteps_nogrp
        exact fullBumpInv_finish inv_e hm_e hQ
      · intro Jret hJret
        c0_hsteps_nogrp
        · -- `stable == 0`: sort + `full_queue_mtf` loop
          refine wp_join_group (ts := []) (PKJoin allow_reasons s_p.core.min_clr_len) ?_ ?_
          · intro _ _ m_st ⟨ext_s, s_s, ⟨hm_st, inv_s⟩, hmcl_eq⟩
            rw [Blocks.get_here]
            refine wp_loop_inv (ts := [i64]) (PKInv allow_reasons s_p.core.min_clr_len)
              (fun (k, ()) _ => s_p.core.min_clr_len - k.toNat)
              (fun Jk hJk => by
                c0_hsteps_nogrp
                exact hJk (0#64, ()) m_st ⟨ext_s, s_s, Nat.zero_le _, ⟨hm_st, inv_s⟩, hmcl_eq⟩)
              (fun Jk (k, ()) m_k ⟨ext_k, s_k, hk_le, ⟨hm_k, inv_k⟩, hk_mcl⟩ ihk => ?_)
            rw [Blocks.get_here]
            have hcv_k : s_k.core.cur_vars = s0.core.cur_vars := by rw [inv_k.shape]
            have hna_k := inv_k.len.scratch_ok.work_stk1_len
            have hmcl_k := inv_k.mcl_le
            c0_hsteps_nogrp
            · have hk_lt : k.toNat < s_p.core.min_clr_len := by
                have hc0 : k.toNat < (BitVec.ofNat 64 s_p.core.min_clr_len).toNat := by c0_bound
                rwa [hcnt_nat] at hc0
              have hk_na : k.toNat < s_k.scratch.work_stk1.length := by rw [hna_k]; omega
              have hkp1 : (k + 1#64).toNat = k.toNat + 1 := by bv_omega
              c0_hsteps_nogrp
              refine wp_join_group (ts := []) (PKJoin allow_reasons s_p.core.min_clr_len) ?_ ?_
              · intro _ _ m_k' ⟨ext_k', s_k', ⟨hm_k', inv_k'⟩, hmcl_k'⟩
                rw [Blocks.get_here]
                c0_hsteps_nogrp
                exact ihk (k + 1#64, ()) m_k' (by dsimp only; rw [hkp1]; omega)
                  ⟨ext_k', s_k', by rw [hkp1]; omega, ⟨hm_k', inv_k'⟩, hmcl_k'⟩
              · intro Jk1 hJk1
                have hfl_len := inv_k.len.core_ok.flags_len
                c0_hsteps_nogrp
                · refine bump_call_full_var rfl hMtf (by decide) (by decide) (by decide)
                    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
                    rfl inv_k.len hm_k
                    fun s_k' m_k' hc' hl' hp' hm_k' => ?_
                  c0_hsteps_nogrp
                  exact hJk1 () m_k' ⟨ext_k, s_k',
                    ⟨hm_k', fullBumpInv_of_safety inv_k hc' hl' hp'⟩, by rw [hc']; exact hk_mcl⟩
                · exact hJk1 () m_k ⟨ext_k, s_k, ⟨hm_k, inv_k⟩, hk_mcl⟩
                · exact hJk1 () m_k ⟨ext_k, s_k, ⟨hm_k, inv_k⟩, hk_mcl⟩
            · c0_hsteps_nogrp
              exact hJret () m_k ⟨ext_k, s_k, hm_k, inv_k⟩
          · intro Js_st hJs_st
            c0_hsteps_nogrp
            refine bump_call_sort_ana hSortAna (n := BitVec.ofNat 64 s_p.core.min_clr_len)
              rfl rfl inv_p.len (by rw [hcnt_nat, hcv_p]; exact hmcl_p)
              (fun k hk => by rw [hcnt_nat] at hk; rw [hcv_p]; exact inv_p.cov_k k hk) hm_p
              fun ws1' repr' wsort' sbuf' m_st hw1 hrp hws hsb hpm htl hcv' hm_st => ?_
            rw [hcnt_nat] at hpm
            have inv_st := fullBumpInv_sort inv_p hw1 hrp hws hsb hpm
              (by rw [hcnt_nat] at hcv'; exact hcv')
            c0_hsteps_nogrp
            exact hJs_st () m_st ⟨ext_p, _, ⟨hm_st, inv_st⟩, rfl⟩
        · -- `stable != 0`: `full_bump_var` loop + `full_bump_decay`
          refine wp_loop_inv (ts := [i64]) (PKInv allow_reasons s_p.core.min_clr_len)
            (fun (k, ()) _ => s_p.core.min_clr_len - k.toNat)
            (fun Jk hJk => by
              c0_hsteps_nogrp
              exact hJk (0#64, ()) m_p ⟨ext_p, s_p, Nat.zero_le _, ⟨hm_p, inv_p⟩, rfl⟩)
            (fun Jk (k, ()) m_k ⟨ext_k, s_k, hk_le, ⟨hm_k, inv_k⟩, hk_mcl⟩ ihk => ?_)
          rw [Blocks.get_here]
          have hcv_k : s_k.core.cur_vars = s0.core.cur_vars := by rw [inv_k.shape]
          have hna_k := inv_k.len.scratch_ok.work_stk1_len
          have hmcl_k := inv_k.mcl_le
          c0_hsteps_nogrp
          · have hk_lt : k.toNat < s_p.core.min_clr_len := by
              have hc0 : k.toNat < (BitVec.ofNat 64 s_p.core.min_clr_len).toNat := by c0_bound
              rwa [hcnt_nat] at hc0
            have hk_na : k.toNat < s_k.scratch.work_stk1.length := by rw [hna_k]; omega
            have hkp1 : (k + 1#64).toNat = k.toNat + 1 := by bv_omega
            c0_hsteps_nogrp
            refine wp_join_group (ts := []) (PKJoin allow_reasons s_p.core.min_clr_len) ?_ ?_
            · intro _ _ m_k' ⟨ext_k', s_k', ⟨hm_k', inv_k'⟩, hmcl_k'⟩
              rw [Blocks.get_here]
              c0_hsteps_nogrp
              exact ihk (k + 1#64, ()) m_k' (by dsimp only; rw [hkp1]; omega)
                ⟨ext_k', s_k', by rw [hkp1]; omega, ⟨hm_k', inv_k'⟩, hmcl_k'⟩
            · intro Jk1 hJk1
              have hfl_len := inv_k.len.core_ok.flags_len
              c0_hsteps_nogrp
              · refine bump_call_full_var rfl hBumpVar (by decide) (by decide) (by decide)
                  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
                  rfl inv_k.len hm_k
                  fun s_k' m_k' hc' hl' hp' hm_k' => ?_
                c0_hsteps_nogrp
                exact hJk1 () m_k' ⟨ext_k, s_k',
                  ⟨hm_k', fullBumpInv_of_safety inv_k hc' hl' hp'⟩, by rw [hc']; exact hk_mcl⟩
              · exact hJk1 () m_k ⟨ext_k, s_k, ⟨hm_k, inv_k⟩, hk_mcl⟩
              · exact hJk1 () m_k ⟨ext_k, s_k, ⟨hm_k, inv_k⟩, hk_mcl⟩
          · c0_hsteps_nogrp
            refine bump_call_full_void rfl hBumpDecay (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
              rfl inv_k.len hm_k
              fun s_k' m_k' hc' hl' hp' hm_k' => ?_
            c0_hsteps_nogrp
            exact hJret () m_k' ⟨ext_k, s_k', hm_k', fullBumpInv_of_safety inv_k hc' hl' hp'⟩
    · -- Phase 1 (`if (allow_reasons && !m6_hdr_delaying(h, 0) && m6_hdr_dr_allow(h))`)
      intro Jp2 hJp2
      c0_hsteps_nogrp
      · subst allow_reasons
        have hcov0 : FullAnaMarksCov c s0 := hpre0
        refine bump_call_w2a hDelay rfl hcfg hext0 hlen0 hm0_f
          fun ⟨del_r, ⟨⟩⟩ ext1 s1 m1 hc1 hl1 hp1 he1 hi1 hm1 => ?_
        have inv1 := fullBumpInv_of_m6h inv0 hc1 hl1 hp1 he1 hi1
        c0_hsteps_nogrp
        · exact hJp2 () m1 ⟨ext1, s1, hm1, inv1⟩
        · refine bump_call_dr_allow hDrAllow rfl hcfg he1 hl1 hm1
            fun dr_r ext2 m2 hi2 heq2 hm2 => ?_
          have inv2 : FullBumpInv true c ext0 s0 ext2 s1 :=
            ⟨inv1.len, inv1.shape, M6HdrExtInitOk.toOk hi2,
              fun h0 => let ⟨h1, hw1⟩ := inv1.init_pres h0; ⟨hi2, by rw [heq2 h1]; exact hw1⟩,
              inv1.ext_scr, inv1.ws2, inv1.cov_pres, inv1.mcl_le, inv1.cov_k,
              fun h => Bool.noConfusion h⟩
          c0_hsteps_nogrp
          · let saved := BitVec.ofNat 64 s1.core.min_clr_len
            let lim := saved * 10#64
            have hcv1 : s1.core.cur_vars = s0.core.cur_vars := by rw [inv2.shape]
            have htl1 : s1.core.tmp_len = s0.core.tmp_len := by rw [inv2.shape]
            have hsaved_nat : saved.toNat = s1.core.min_clr_len := by
              have := inv2.mcl_le; exact bv64_ofNat_toNat (by omega)
            have hlim_nat : lim.toNat = s1.core.min_clr_len * 10 := by
              have := inv2.mcl_le
              dsimp only [lim]
              rw [BitVec.toNat_mul, hsaved_nat,
                show (10#64 : BitVec 64).toNat = 10 from rfl, Nat.mod_eq_of_lt (by omega)]
            refine wp_join_group (ts := [i64])
              (fun (tlen, ()) m_tl => m_tl = m2 ∧
                tlen.toNat ≤ s0.core.cur_vars ∧ tlen.toNat ≤ s0.core.tmp_len)
              ?_ ?_
            · intro _ ⟨tlen, ⟨⟩⟩ m_tl ⟨hm_tl, ht_cv, ht_tl⟩
              rw [Blocks.get_here]
              subst m_tl
              refine wp_loop_inv (ts := [i64])
                (fun (i, ()) m3 => ∃ ext3 s3, i.toNat ≤ tlen.toNat ∧ PExt true ext3 s3 m3)
                (fun (i, ()) _ => tlen.toNat - i.toNat)
                (fun Ji hJi => by
                  c0_hsteps_nogrp
                  exact hJi (0#64, ()) m2 ⟨ext2, s1, Nat.zero_le _, hm2, inv2⟩)
                (fun Ji (i, ()) m3 ⟨ext3, s3, hi_le, hm3, inv3⟩ ihi => ?_)
              rw [Blocks.get_here]
              have hcv3 : s3.core.cur_vars = s0.core.cur_vars := by rw [inv3.shape]
              refine wp_join_group (ts := []) (PJoin true) ?_ ?_
              · -- Post-loop rollback (`mcl > lim`) + `bump_delay` / `reduce_delay`
                intro _ _ m4 ⟨ext4, s4, hm4, inv4⟩
                rw [Blocks.get_here]
                refine wp_join_group (ts := []) (PJoin true) ?_ ?_
                · intro _ _ m5 ⟨ext5, s5, hm5, inv5⟩
                  rw [Blocks.get_here]
                  c0_hsteps_nogrp
                  exact hJp2 () m5 ⟨ext5, s5, hm5, inv5⟩
                · intro Jpost hJpost
                  c0_hsteps_nogrp
                  · refine wp_while_state (ts := [])
                      (fun _ => PUnit.unit) (fun st => st.core.min_clr_len)
                      (PExt true ext4) ?_ ?_
                    · intro Jrb hJrb
                      c0_hsteps_nogrp
                      exact hJrb s4 m4 ⟨hm4, inv4⟩
                    · intro Jrb s5 m5 ⟨hm5, inv5⟩ ihrb
                      rw [Blocks.get_here]
                      have hcv5 : s5.core.cur_vars = s0.core.cur_vars := by rw [inv5.shape]
                      c0_hsteps_nogrp
                      · have hgt : 0 < s5.core.min_clr_len := by
                          have h2 :
                              s0.core.min_clr_len % 2 ^ 64 < s5.core.min_clr_len % 2 ^ 64 := by
                            assumption
                          have := inv5.mcl_le; omega
                        obtain ⟨hrv, inv5'⟩ := fullBumpInv_pop inv5 hcov0 hgt
                        have hmcl5 := inv5.mcl_le
                        have hna5 := inv5.len.scratch_ok.work_stk1_len
                        have hm5_m1 : (BitVec.ofNat 64 s5.core.min_clr_len - 1).toNat =
                            s5.core.min_clr_len - 1 := bv64_mcl_m1_toNat hgt (by omega)
                        have hm5_na : s5.core.min_clr_len - 1 < s5.scratch.work_stk1.length := by
                          rw [hna5]; omega
                        c0_hsteps_nogrp
                        refine wp_join_group (ts := [])
                          (fun _ m6 =>
                            (FullMem c
                              { s5 with
                                core := { s5.core with
                                  min_clr_len := s5.core.min_clr_len - 1
                                  mrk := s5.core.mrk.set
                                    (s5.scratch.work_stk1[s5.core.min_clr_len - 1]'hm5_na).toNat
                                    0#8 } } ⋆
                              (m6ExtMem (m6ExtAddr c.hdr) ext4 ⋆ R)) m6)
                          ?_ ?_
                        · intro _ _ m6 hm6
                          rw [Blocks.get_here]
                          c0_hsteps_nogrp
                          exact ihrb _ m6 (by dsimp only; omega) ⟨hm6, inv5'⟩
                        · intro Jrbi hJrbi
                          have hmrk5 := inv5.len.core_ok.mrk_len
                          have hm5_of : (BitVec.ofNat 64 (s5.core.min_clr_len - 1)).toNat =
                              s5.core.min_clr_len - 1 := bv64_ofNat_toNat (by omega)
                          c0_hsteps_nogrp
                          · have hm' : (FullMem c
                                { s5 with
                                  core := { s5.core with
                                    min_clr_len := s5.core.min_clr_len - 1
                                    mrk := s5.core.mrk.set
                                      (s5.scratch.work_stk1[s5.core.min_clr_len - 1]'hm5_na).toNat
                                      0#8 } } ⋆
                                (m6ExtMem (m6ExtAddr c.hdr) ext4 ⋆ R)) m := by
                              simpa only [hm5_m1, hm5_of, bv_zext32_64_toNat] using hm
                            exact hJrbi () _ hm'
                          · exact False.elim (fullBump_rollback_pop_false hgt (by omega) (by omega)
                              hrv hm5_na rfl (fun _ => by assumption))
                      · refine bump_call_w2a hBumpDelay rfl hcfg inv5.ext_ok inv5.len hm5
                          fun _ ext6 s6 m6 hc6 hl6 hp6 he6 hi6 hm6 => ?_
                        c0_hsteps_nogrp
                        exact hJpost () m6 ⟨ext6, s6, hm6,
                          fullBumpInv_of_m6h inv5 hc6 hl6 hp6 he6 hi6⟩
                  · refine bump_call_w2a hReduceDelay rfl hcfg inv4.ext_ok inv4.len hm4
                      fun _ ext5 s5 m5 hc5 hl5 hp5 he5 hi5 hm5 => ?_
                    c0_hsteps_nogrp
                    exact hJpost () m5 ⟨ext5, s5, hm5,
                      fullBumpInv_of_m6h inv4 hc5 hl5 hp5 he5 hi5⟩
              · -- Outer loop step (`i < tlen && mcl <= lim`)
                intro Jexit hJexit
                c0_hsteps_nogrp
                · have hi_lt : i.toNat < tlen.toNat := by c0_bound
                  have hip1 : (i + 1#64).toNat = i.toNat + 1 := by bv_omega
                  have hi_tmp : i.toNat < s3.core.tmp.length := by
                    rw [inv3.len.core_ok.tmp_len_arr]; omega
                  c0_hsteps_nogrp
                  · refine wp_join_group (ts := [i32]) (fun (rsn, ()) m4 => m4 = m3) ?_ ?_
                    · intro _ ⟨rsn, ⟨⟩⟩ m4 hm4
                      rw [Blocks.get_here]
                      subst m4
                      let PS3 : Tup Val [] → Mem 64 → Prop := fun _ m4 =>
                        ∃ s4, PExt true ext3 s4 m4
                      refine wp_join_group (ts := []) PS3 ?_ ?_
                      · intro _ _ m4 ⟨s4, hm4, inv4⟩
                        rw [Blocks.get_here]
                        c0_hsteps_nogrp
                        exact ihi (i + 1#64, ()) m4 (by dsimp only; rw [hip1]; omega)
                          ⟨ext3, s4, by rw [hip1]; omega, hm4, inv4⟩
                      · intro Jdone hJdone
                        refine wp_join_group (ts := []) PS3 ?_ ?_
                        · -- `L904` bodies (`Jbin_else`) = arena reason clause (`L910`)
                          intro _ _ m4 ⟨s4, hm4, inv4⟩
                          rw [Blocks.get_here]
                          refine wp_join_group (ts := []) PS3 ?_ ?_
                          · intro _ _ m5 ⟨s5, hm5, inv5⟩
                            rw [Blocks.get_here]
                            c0_hsteps_nogrp
                            exact hJdone () m5 ⟨s5, hm5, inv5⟩
                          · intro Jar_join hJar_join
                            c0_hsteps_nogrp
                            · have hrsn_2 := fullBump_rsn2_lt inv4.len harena (by c0_bound)
                              c0_hsteps_nogrp
                              let sz := s4.core.arena[(rsn.setWidth 64 + 2#64).toNat]'hrsn_2
                              refine wp_join_group (ts := []) PS3 ?_ ?_
                              · intro _ _ m5 ⟨s5, hm5, inv5⟩
                                rw [Blocks.get_here]
                                c0_hsteps_nogrp
                                exact hJar_join () m5 ⟨s5, hm5, inv5⟩
                              · intro Jloop_done hJloop_done
                                c0_hsteps_nogrp
                                · have hsum_le := fullBump_sz_sum_le inv4.len harena hrsn_2
                                    (by assumption)
                                  refine wp_loop_inv (ts := [i32])
                                    (fun (j, ()) m5 => ∃ s5, j.toNat ≤ sz.toNat ∧
                                      PExt true ext3 s5 m5)
                                    (fun (j, ()) _ => sz.toNat - j.toNat)
                                    (fun Jj hJj => by
                                      c0_hsteps_nogrp
                                      exact hJj (0#32, ()) _
                                        ⟨_, Nat.zero_le _, hm, fullBumpInv_inc_ticks inv4 _⟩)
                                    (fun Jj (j, ()) m5 ⟨s5, hj_le, hm5, inv5⟩ ihj => ?_)
                                  rw [Blocks.get_here]
                                  have hcv5 : s5.core.cur_vars = s0.core.cur_vars := by
                                    rw [inv5.shape]
                                  have hmcl5 := inv5.mcl_le
                                  c0_hsteps_nogrp
                                  · have hj_lt : j.toNat < sz.toNat := by c0_bound
                                    have hsz32 : sz.toNat < 2 ^ 32 := sz.isLt
                                    have hjp1 : (j + 1#32).toNat = j.toNat + 1 := by bv_omega
                                    have hare5 : s5.core.arena = s4.core.arena := by
                                      rw [inv5.shape, inv4.shape]
                                    have har_j : ((rsn.setWidth 64 + 3#64) + j.setWidth 64).toNat <
                                        s5.core.arena.length := by
                                      rw [hare5]
                                      exact fullBump_har_j_lt inv4.len harena hj_lt hsum_le
                                    c0_hsteps_nogrp
                                    refine wp_join_group (ts := []) PS3 ?_ ?_
                                    · intro _ _ m6 ⟨s6, hm6, inv6⟩
                                      rw [Blocks.get_here]
                                      c0_hsteps_nogrp
                                      exact ihj (j + 1#32, ()) m6 (by dsimp only; rw [hjp1]; omega)
                                        ⟨s6, by rw [hjp1]; omega, hm6, inv6⟩
                                    · intro Jj1 hJj1
                                      have hlvl5 := inv5.len.core_ok.lvl_len
                                      have hmrk5 := inv5.len.core_ok.mrk_len
                                      have hna5 := inv5.len.scratch_ok.work_stk1_len
                                      c0_hsteps_nogrp
                                      · have hov_lt := fullBump_j_ov_lt inv4.len harena hare5
                                          s0.core.cur_vars (by omega) har_j
                                          (fun _ => by assumption)
                                        have hmrk_lt :
                                            ((s5.core.arena[(rsn.setWidth 64 + 3#64 +
                                              j.setWidth 64).toNat]'har_j) >>> 1#32).toNat <
                                              s5.core.mrk.length := by
                                          rw [hmrk5]; omega
                                        have har_jn := fullBump_har_jn_lt inv4.len harena hare5
                                          har_j
                                        have hidx_eq := fullBump_j_idx_eq inv4.len harena hare5
                                          har_j har_jn
                                        c0_hsteps_nogrp
                                        · obtain ⟨hm6, inv6⟩ := fullBumpInv_push_mem_norm inv5 hcov0
                                            ((s5.core.arena[(rsn.setWidth 64 + 3#64 +
                                              j.setWidth 64).toNat]'har_j) >>> 1#32)
                                            hm hov_lt
                                            (mrk_getElem?_of_zext32 hidx_eq hmrk_lt
                                              (fun _ => by assumption))
                                            (bv_mcl_lt_of_c0 (by omega) (by omega) (by c0_bound))
                                          exact hJj1 () _ ⟨_, hm6, inv6⟩
                                        all_goals exact hJj1 () m5 ⟨s5, hm5, inv5⟩
                                      all_goals exact hJj1 () m5 ⟨s5, hm5, inv5⟩
                                  all_goals exact hJloop_done () m5 ⟨s5, hm5, inv5⟩
                                all_goals exact hJloop_done () m4 ⟨s4, hm4, inv4⟩
                            all_goals exact hJar_join () m4 ⟨s4, hm4, inv4⟩
                        · -- `L904` entry (`!= 0xFFFFFFFF && PW_BIN_FLAG`)
                          intro Jbin_else hJbin_else
                          c0_hsteps_nogrp
                          · refine wp_join_group (ts := []) PS3 ?_ ?_
                            · intro _ _ m4 ⟨s4, hm4, inv4⟩
                              rw [Blocks.get_here]
                              exact hJdone () m4 ⟨s4, hm4, inv4⟩
                            · intro Jbin hJbin
                              have hlvl3 := inv3.len.core_ok.lvl_len
                              have hmrk3 := inv3.len.core_ok.mrk_len
                              have hna3 := inv3.len.scratch_ok.work_stk1_len
                              have hmcl3 := inv3.mcl_le
                              c0_hsteps_nogrp
                              · have hov_lt := bv_ov_lt_of_c0
                                    (ov := (rsn &&& 2147483647#32) >>> 1#32)
                                    (by omega : s0.core.cur_vars < 2 ^ 64) (by c0_bound)
                                have hmrk_lt :
                                    ((rsn &&& 2147483647#32) >>> 1#32).toNat <
                                    s3.core.mrk.length := by
                                  rw [hmrk3]; omega
                                have hidx_eq : ((rsn &&& 2147483647#32) >>> 1#32).toNat =
                                    (rsn &&& (2147483647 : BitVec 32)).toNat / 2 :=
                                  bv32_ushr1_toNat _
                                obtain ⟨hm4, inv4⟩ := fullBumpInv_push_mem_norm inv3 hcov0
                                  ((rsn &&& 2147483647#32) >>> 1#32) hm hov_lt
                                  (mrk_getElem?_of_zext32 hidx_eq hmrk_lt
                                    (fun _ => by assumption))
                                  (bv_mcl_lt_of_c0 (by omega) (by omega) (by c0_bound))
                                exact hJbin () _ ⟨_, hm4, inv4⟩
                              all_goals exact hJbin () m3 ⟨s3, hm3, inv3⟩
                          all_goals exact hJbin_else () m3 ⟨s3, hm3, inv3⟩
                    · -- `rsn` ternary entry
                      intro Js hJs
                      have hrsns3 := inv3.len.core_ok.rsns_len
                      c0_hsteps_nogrp
                      · exact hJs _ m3 rfl
                      · exact hJs _ m3 rfl
                all_goals exact hJexit () m3 ⟨ext3, s3, hm3, inv3⟩
            · -- `tlen` entry
              intro Js hJs
              have hcv_tl : s1.core.cur_vars ≤ c.max_vars ∧ s1.core.tmp_len ≤ c.max_vars :=
                ⟨inv2.len.core_ok.cur_vars_le, inv2.len.core_ok.tmp_len_le⟩
              have hcv_tl0 : s0.core.cur_vars ≤ c.max_vars ∧ s0.core.tmp_len ≤ c.max_vars :=
                ⟨hlen0.core_ok.cur_vars_le, hlen0.core_ok.tmp_len_le⟩
              c0_hsteps_nogrp
              · exact hJs (BitVec.ofNat 64 s0.core.cur_vars, ()) m2
                  ⟨rfl, by rw [bv64_ofNat_toNat (by omega)]; exact Nat.le_refl _, by
                    have hc0 : (BitVec.ofNat 64 s0.core.cur_vars).toNat <
                        (BitVec.ofNat 64 s0.core.tmp_len).toNat := by c0_bound
                    rw [bv64_ofNat_toNat (by omega), bv64_ofNat_toNat (by omega)] at hc0
                    rw [bv64_ofNat_toNat (by omega)]; omega⟩
              · exact hJs (BitVec.ofNat 64 s1.core.tmp_len, ()) m2
                  ⟨rfl, by
                    have hc0 : ¬ (BitVec.ofNat 64 s0.core.cur_vars).toNat <
                        (BitVec.ofNat 64 s1.core.tmp_len).toNat := by c0_bound
                    rw [bv64_ofNat_toNat (by omega), bv64_ofNat_toNat (by omega), htl1] at hc0
                    rw [bv64_ofNat_toNat (by omega), htl1]; omega,
                    by rw [bv64_ofNat_toNat (by omega), htl1]; exact Nat.le_refl _⟩
          · exact hJp2 () m2 ⟨ext2, s1, hm2, inv2⟩
      · exact hJp2 () m ⟨ext0, s0, hm0_f, inv0⟩

end

end LeanQbe.T.Examples.Kissat.Proof.Bump
