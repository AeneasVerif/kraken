/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Watch.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Watch.Wp5a
public import LeanQbe.T.Examples.Kissat.Src.Watch

import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts
import LeanQbe.T.Examples.Kissat.Proof.Spec.MemBridges
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb

/-! # Watch WP Proofs Part 5: `full_watch_pop_c0`, `full_unwatch_large`, `full_has_bin`

Clean `CanonicalEnv` WP proofs for `Src.Watch` functions 8–10 (`pop`, `unwatch_large`, `has_bin`),
using `Wp5a`'s 64-bit `wstk` bridges, `watchStackLayout_shrink`, `WatchBoundary`, and
`watchSliceOk_erase` / `denseWatchSliceOk_erase`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Watch

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Watch
open LeanQbe.T.Examples.Kissat.Proof.Spec
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Proof.Watch.WatchMemTactics

local macro "c0_go" : tactic =>
  `(tactic| ((try (first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)); c0_steps))

local macro "c0_step1" : tactic =>
  `(tactic| ((try (first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)); c0_step))

private theorem pack64_lo (x y : BitVec 32) : (pack64 x y).setWidth 32 = x := by
  apply BitVec.eq_of_toNat_eq
  have hx := x.isLt
  simp [pack64_toNat, BitVec.toNat_setWidth]
  omega

private theorem pack64_hi (x y : BitVec 32) : (pack64 x y >>> 32).setWidth 32 = y := by
  apply BitVec.eq_of_toNat_eq
  have hx := x.isLt; have hy := y.isLt
  simp [pack64_toNat, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  omega

private theorem bv32_ushr31_of_bin {w0 : BitVec 32} (hb : w0 &&& 0x80000000#32 ≠ 0#32) :
    w0 >>> 31 = 1#32 := by
  have hlt : w0.toNat < 2 ^ 32 := w0.isLt
  have hge : 0x80000000 ≤ w0.toNat := by
    refine Classical.byContradiction fun hlt' => ?_
    have hz : w0 &&& 0x80000000#32 = 0#32 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_and, show (0x80000000#32).toNat = 2 ^ 31 from rfl]
      apply Nat.eq_of_testBit_eq; intro k
      rw [Nat.testBit_and, show (0#32 : BitVec 32).toNat = 0 from rfl, Nat.zero_testBit]
      by_cases hk : k = 31
      · subst hk
        have hw : w0.toNat.testBit 31 = false := by
          rw [Nat.testBit_eq_decide_div_mod_eq]
          simp [show w0.toNat / 2 ^ 31 = 0 by omega]
        rw [hw]; simp
      · have h2 : Nat.testBit (2 ^ 31) k = false := by
          rw [Nat.testBit_two_pow]; exact decide_eq_false (Ne.symm hk)
        rw [h2]; simp
    exact hb hz
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    show (1#32 : BitVec 32).toNat = 1 from rfl]
  omega

private theorem bv32_ushr31_of_lt {w0 : BitVec 32} (hlt : w0.toNat < 2147483648) :
    w0 >>> 31 = 0#32 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    show (0#32 : BitVec 32).toNat = 0 from rfl]
  omega

theorem watchSliceOk_at_boundary {F : List (List Nat)} {k : FullCoreState}
    {lit p rem q : Nat} (hs : WatchSliceOk F k lit p rem) (hbd : WatchBoundary k.wstk p rem q)
    (hq : q < p + rem) :
    (∃ w0, k.wstk[q]? = some w0 ∧ w0 &&& 0x80000000#32 ≠ 0#32 ∧
      (cnfOfClauses F).EntailsClause (cnfClause [lit, (w0 &&& 0x7FFFFFFF#32).toNat]) ∧
      WatchBoundary k.wstk p rem (q + 1)) ∨
    (∃ w0 cref, q + 2 ≤ p + rem ∧ k.wstk[q]? = some w0 ∧ k.wstk[q + 1]? = some cref ∧
      w0 &&& 0x80000000#32 = 0#32 ∧ cref.toNat < 2147483648 ∧
      WatchBoundary k.wstk p rem (q + 2)) := by
  induction hs with
  | empty => have := watchBoundary_le hbd; omega
  | @bin p rem' w0 hw hbin _ hlt hent hrest ih =>
    have hle := (watchBoundary_le hbd).1
    rcases Nat.eq_or_lt_of_le hle with rfl | hpq
    · left; refine ⟨w0, hw, hbin, hent, ?_⟩
      exact watchBoundary_append_bin hbd (by omega) hw hbin
    · have hbd' : WatchBoundary k.wstk (p + 1) rem' q := by
        cases hbd with
        | here => omega
        | @bin _ _ _ _ _ _ rest => exact rest
        | @large _ _ _ _ _ hw0' _ hlg' _ _ => rw [hw] at hw0'; cases hw0'; contradiction
      rcases ih hbd' (by omega) with
        ⟨w', hw', hbin', hent', hr'⟩ | ⟨w', c', hq2, hw0', hw1', hlg', hlt', hr'⟩
      · left; exact ⟨w', hw', hbin', hent', WatchBoundary.bin hw hbin hr'⟩
      · right; exact ⟨w', c', by omega, hw0', hw1', hlg', hlt', WatchBoundary.bin hw hbin hr'⟩
  | @large p rem' w0 cref hw0 hw1 hlg hlt _ hrest ih =>
    have hle := (watchBoundary_le hbd).1
    rcases Nat.eq_or_lt_of_le hle with rfl | hpq
    · right; refine ⟨w0, cref, by omega, hw0, hw1, hlg, hlt, ?_⟩
      exact watchBoundary_append_large hbd (by omega) hw0 hw1 hlg hlt
    · have hbd' : WatchBoundary k.wstk (p + 2) rem' q := by
        cases hbd with
        | here => omega
        | @bin _ _ _ _ hw' hbin' _ => rw [hw0] at hw'; cases hw'; contradiction
        | @large _ _ _ _ _ _ _ _ _ rest => exact rest
      have hq2 := (watchBoundary_le hbd').1
      rcases ih hbd' (by omega) with
        ⟨w', hw', hbin', hent', hr'⟩ | ⟨w', c', hq2', hw0', hw1', hlg', hlt', hr'⟩
      · left; exact ⟨w', hw', hbin', hent', WatchBoundary.large hw0 hw1 hlg hlt hr'⟩
      · right; exact ⟨w', c', by omega, hw0', hw1', hlg', hlt',
          WatchBoundary.large hw0 hw1 hlg hlt hr'⟩

private def UnwatchShiftInv (k0 k : FullCoreState) (off sz q src dst : Nat) : Prop :=
  off ≤ q ∧ q ≤ dst ∧ dst + 2 = src ∧ q + 2 ≤ src ∧ src ≤ off + sz ∧
  (∀ idx, idx < off → k.wstk[idx]? = k0.wstk[idx]?) ∧
  (∀ idx, off ≤ idx → idx < q → k.wstk[idx]? = k0.wstk[idx]?) ∧
  (∀ idx, q ≤ idx → idx < dst → k.wstk[idx]? = k0.wstk[idx + 2]?) ∧
  (∀ idx, src ≤ idx → idx < k0.wstk.length → k.wstk[idx]? = k0.wstk[idx]?) ∧
  k.wstk.length = k0.wstk.length

private theorem unwatchShiftInv_init (k0 : FullCoreState) {off sz q : Nat}
    (hq : off ≤ q) (hq2 : q + 2 ≤ off + sz) :
    UnwatchShiftInv k0 k0 off sz q (q + 2) q :=
  ⟨hq, Nat.le_refl _, rfl, Nat.le_refl _, hq2,
    fun _ _ => rfl, fun _ _ _ => rfl, fun _ h1 h2 => by omega,
    fun _ _ _ => rfl, rfl⟩

private theorem unwatchShiftInv_step1 {k0 k : FullCoreState} {off sz q src dst : Nat}
    (hinv : UnwatchShiftInv k0 k off sz q src dst) (hlt : src < off + sz)
    (hlen : off + sz ≤ k0.wstk.length) (w : BitVec 32)
    (hw : k.wstk[src]? = some w) :
    UnwatchShiftInv k0 { k with wstk := k.wstk.set dst w } off sz q (src + 1) (dst + 1) := by
  rcases hinv with ⟨h0, h1, h2, h3, h4, hlt_off, hpre, hsh, hpost, hwlen⟩
  have hw0 : k0.wstk[src]? = some w := by rw [← hpost src (Nat.le_refl _) (by omega), hw]
  refine ⟨h0, by omega, by omega, by omega, by omega, ?_, ?_, ?_, ?_, by simp [hwlen]⟩
  · intro idx hi; dsimp only; rw [List.getElem?_set_ne (by omega), hlt_off idx hi]
  · intro idx hi1 hi2; dsimp only; rw [List.getElem?_set_ne (by omega), hpre idx hi1 hi2]
  · intro idx hi1 hi2; dsimp only
    by_cases heq : idx = dst
    · subst heq; rw [List.getElem?_set_self (by omega), ← hw0, show idx + 2 = src by omega]
    · rw [List.getElem?_set_ne (Ne.symm heq), hsh idx hi1 (by omega)]
  · intro idx hi1 hi2; dsimp only; rw [List.getElem?_set_ne (by omega), hpost idx (by omega) hi2]

private theorem unwatchShiftInv_step2 {k0 k : FullCoreState} {off sz q src dst : Nat}
    (hinv : UnwatchShiftInv k0 k off sz q src dst) (hlt : src + 2 ≤ off + sz)
    (hlen : off + sz ≤ k0.wstk.length) (v : BitVec 64)
    (hlo : k.wstk[src]? = some (v.setWidth 32))
    (hhi : k.wstk[src + 1]? = some ((v >>> 32).setWidth 32)) :
    UnwatchShiftInv k0
      { k with wstk := (k.wstk.set dst (v.setWidth 32)).set (dst + 1) ((v >>> 32).setWidth 32) }
      off sz q (src + 2) (dst + 2) := by
  rcases hinv with ⟨h0, h1, h2, h3, h4, hlt_off, hpre, hsh, hpost, hwlen⟩
  have hlo0 : k0.wstk[src]? = some (v.setWidth 32) := by
    rw [← hpost src (Nat.le_refl _) (by omega), hlo]
  have hhi0 : k0.wstk[src + 1]? = some ((v >>> 32).setWidth 32) := by
    rw [← hpost (src + 1) (by omega) (by omega), hhi]
  refine ⟨h0, by omega, by omega, by omega, by omega, ?_, ?_, ?_, ?_, by simp [hwlen]⟩
  · intro idx hi; dsimp only
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega), hlt_off idx hi]
  · intro idx hi1 hi2; dsimp only
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega), hpre idx hi1 hi2]
  · intro idx hi1 hi2; dsimp only
    by_cases h_eq0 : idx = dst
    · subst h_eq0
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by simp [hwlen]; omega),
        ← hlo0, show idx + 2 = src by omega]
    · by_cases h_eq1 : idx = dst + 1
      · subst h_eq1
        rw [List.getElem?_set_self (by simp [hwlen]; omega), ← hhi0,
          show dst + 1 + 2 = src + 1 by omega]
      · rw [List.getElem?_set_ne (Ne.symm h_eq1), List.getElem?_set_ne (Ne.symm h_eq0),
          hsh idx hi1 (by omega)]
  · intro idx hi1 hi2; dsimp only
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      hpost idx (by omega) hi2]

private theorem unwatchShiftInv_step4 {k0 k : FullCoreState} {off sz q src dst : Nat}
    (hinv : UnwatchShiftInv k0 k off sz q src dst) (hlt : src + 4 ≤ off + sz)
    (hlen : off + sz ≤ k0.wstk.length) (v0 v1 : BitVec 64)
    (hv0_lo : k.wstk[src]? = some (v0.setWidth 32))
    (hv0_hi : k.wstk[src + 1]? = some ((v0 >>> 32).setWidth 32))
    (hv1_lo : k.wstk[src + 2]? = some (v1.setWidth 32))
    (hv1_hi : k.wstk[src + 3]? = some ((v1 >>> 32).setWidth 32)) :
    UnwatchShiftInv k0
      { k with wstk :=
        (((k.wstk.set dst (v0.setWidth 32)).set (dst + 1)
          ((v0 >>> 32).setWidth 32)).set (dst + 2)
          (v1.setWidth 32)).set (dst + 3) ((v1 >>> 32).setWidth 32) }
      off sz q (src + 4) (dst + 4) := by
  have hk1 := unwatchShiftInv_step2 hinv (by omega) hlen v0 hv0_lo hv0_hi
  have h2 := hinv.2.2.1
  let w1 := (k.wstk.set dst (v0.setWidth 32)).set (dst + 1) ((v0 >>> 32).setWidth 32)
  have h_s2 : ({ k with wstk := w1 } : FullCoreState).wstk[src + 2]? = some (v1.setWidth 32) := by
    dsimp only [w1]
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega), hv1_lo]
  have h_s3 : ({ k with wstk := w1 } : FullCoreState).wstk[src + 3]? =
      some ((v1 >>> 32).setWidth 32) := by
    dsimp only [w1]
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega), hv1_hi]
  have hk2 := unwatchShiftInv_step2 hk1 (by omega) hlen v1 h_s2 h_s3
  simpa [w1, Nat.add_assoc] using hk2

private theorem full_unwatch_tail_inv {c : FullCfg} {s : FullState}
    (hlen : s.LengthsOk c) (hlay : WatchStackLayout s.core)
    {lit q src dst : Nat} (hlit : lit < 2 * s.core.cur_vars)
    (hoffq : fullWatchOffCore s.core lit ≤ q)
    (hq2 : q + 2 ≤ fullWatchOffCore s.core lit + fullWatchSizeCore s.core lit)
    (hend : src = fullWatchOffCore s.core lit + fullWatchSizeCore s.core lit)
    {k_loop : FullCoreState}
    (hinv : UnwatchShiftInv s.core k_loop (fullWatchOffCore s.core lit)
      (fullWatchSizeCore s.core lit) q src dst)
    (hbd_impl : ∀ F_cur, ModeWatchesInv F_cur s.core →
      WatchBoundary s.core.wstk (fullWatchOffCore s.core lit) (fullWatchSizeCore s.core lit) q ∧
      ∃ w0 cref,
        s.core.wstk[q]? = some w0 ∧ s.core.wstk[q + 1]? = some cref ∧
        w0 &&& 0x80000000#32 = 0#32 ∧ cref.toNat < 2147483648) :
    let off := fullWatchOffCore s.core lit
    let sz := fullWatchSizeCore s.core lit
    let wstk' := (k_loop.wstk.set (off + sz - 2) 0xFFFFFFFF#32).set (off + sz - 1) 0xFFFFFFFF#32
    let wvec' := s.core.wvec.set (2 * lit + 1) (BitVec.ofNat 32 (sz - 2))
    let s' : FullState := { s with core := { s.core with
      wvec := wvec', wstk := wstk', wusable := s.core.wusable + 2#64 } }
    s'.LengthsOk c ∧ WatchStackLayout s'.core ∧
    (∀ F_cur, ModeWatchesInv F_cur s.core → ModeWatchesInv F_cur s'.core) := by
  intro off sz wstk' wvec' s'
  rcases hinv with ⟨_, hqd, h2, _, _, hlt_off, hpre, hsh, hpost, hwlen⟩
  have hdst_eq : dst = off + sz - 2 := by omega
  have hcv := hlen.core_ok.cur_vars_le; have hwv := hlen.core_ok.wvec_len
  have := c.hmaxv; unfold dimacsBound at *
  have hbounds := hlay.bounds lit hlit
  have hwlen_le := hlen.core_ok.wlen_le
  have hw_len : s.core.wstk.length = c.wcap := hlen.core_ok.wstk_len_arr
  have hwstk'_len : wstk'.length = c.wcap := by simp [wstk', hwlen, hw_len]
  have hwvec'_len : wvec'.length = 4 * c.max_vars := by simp [wvec', hwv]
  have hlen' : s'.LengthsOk c :=
    ⟨{ hlen.core_ok with wvec_len := hwvec'_len, wstk_len_arr := hwstk'_len }, hlen.scratch_ok⟩
  have hother : ∀ l < 2 * s.core.cur_vars, l ≠ lit → ∀ idx < fullWatchSizeCore s.core l,
      wstk'[fullWatchOffCore s.core l + idx]? = s.core.wstk[fullWatchOffCore s.core l + idx]? := by
    intro l hl hne idx hidx
    have hdisj := hlay.disjoint l lit hl hlit hne (Nat.lt_of_le_of_lt (Nat.zero_le _) hidx)
      (by omega)
    have hbd_l := hlay.bounds l hl
    have heq_loop : k_loop.wstk[fullWatchOffCore s.core l + idx]? =
        s.core.wstk[fullWatchOffCore s.core l + idx]? := by
      rcases hdisj with hle_l | hle_r
      · exact hlt_off _ (by omega)
      · exact hpost _ (by omega) (by omega)
    rw [show wstk'[fullWatchOffCore s.core l + idx]? =
        k_loop.wstk[fullWatchOffCore s.core l + idx]? by
      rcases hdisj with hle_l | hle_r <;>
        rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)], heq_loop]
  have hpre_lit : ∀ idx, off ≤ idx → idx < q → wstk'[idx]? = s.core.wstk[idx]? := by
    intro idx hi1 hi2
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega), hpre idx hi1 hi2]
  have hsh_lit : ∀ idx, q ≤ idx → idx < off + sz - 2 → wstk'[idx]? = s.core.wstk[idx + 2]? := by
    intro idx hi1 hi2
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      hsh idx hi1 (by omega)]
  have hnosent : ∀ idx < sz - 2,
      wstk'[off + idx]? ≠ some 0xFFFFFFFF#32 := by
    intro idx hidx
    by_cases hltq : off + idx < q
    · rw [hpre_lit (off + idx) (Nat.le_add_right off idx) hltq]
      exact hlay.no_sentinel lit hlit idx (by omega)
    · rw [hsh_lit (off + idx) (by omega) (by omega)]
      simpa [Nat.add_assoc] using hlay.no_sentinel lit hlit (idx + 2) (by omega)
  have hlay' : WatchStackLayout s'.core :=
    watchStackLayout_shrink hlay hlen.core_ok hlit (by omega) hother hnosent (Nat.le_refl _)
  refine ⟨hlen', hlay', fun F_cur hmode => ?_⟩
  obtain ⟨hbd_q, w0, cref, hw0_q, hcref_q, hlg_q, hcref_lt⟩ := hbd_impl F_cur hmode
  have hwv1 : 2 * lit + 1 < s.core.wvec.length := by omega
  have hsz_lt : sz - 2 < 2 ^ 32 := by
    have : sz < 2 ^ 32 := (s.core.wvec[2 * lit + 1]?.getD 0#32).isLt; omega
  have hoff_lit : fullWatchOffCore s'.core lit = off := by
    dsimp only [fullWatchOffCore, s', wvec']
    exact congrArg BitVec.toNat (wvec_set_size_off_self hwv1 _)
  have hsz_lit : fullWatchSizeCore s'.core lit = sz - 2 := by
    dsimp only [fullWatchSizeCore, s', wvec']
    rw [wvec_set_size_sz_self hwv1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsz_lt]
  have hoth_ws : ∀ l, l ≠ lit →
      fullWatchOffCore s'.core l = fullWatchOffCore s.core l ∧
      fullWatchSizeCore s'.core l = fullWatchSizeCore s.core l := by
    intro l hne
    have h := wvec_set_size_other (wvec := s.core.wvec) hne (BitVec.ofNat 32 (sz - 2))
    exact ⟨by dsimp only [fullWatchOffCore, s', wvec']; exact congrArg BitVec.toNat h.1,
      by dsimp only [fullWatchSizeCore, s', wvec']; exact congrArg BitVec.toNat h.2⟩
  by_cases hdm : s.core.dense_mode = 0#64
  · simp only [ModeWatchesInv, hdm, ↓reduceIte] at hmode
    have hdm' : s'.core.dense_mode = 0#64 := hdm
    simp only [ModeWatchesInv, hdm', ↓reduceIte]
    refine WatchesInv.of_slices hlay'.bounds hlay'.pos_off hlay'.disjoint fun l hl => ?_
    by_cases heq : l = lit
    · subst heq
      have hsl : WatchSliceOk F_cur s.core l off sz := hmode.slices l hl
      rw [hoff_lit, hsz_lit]
      exact watchSliceOk_erase (Nat.le_refl s.core.cur_vars) (fun r hr => hr) hsl hbd_q
        (by omega) (Or.inr ⟨rfl, w0, cref, hw0_q, hcref_q, hlg_q, hcref_lt⟩) hpre_lit hsh_lit
    · rw [(hoth_ws l heq).1, (hoth_ws l heq).2]
      dsimp only [s']
      refine (hmode.slices l hl).mono (Std.Sat.CNF.entails_refl (cnfOfClauses F_cur))
        (Nat.le_refl s.core.cur_vars) (fun r hr => hr) fun idx hi1 hi2 => ?_
      have h := hother l hl heq (idx - fullWatchOffCore s.core l) (by omega)
      rw [Nat.add_sub_cancel' hi1] at h
      exact h
  · simp only [ModeWatchesInv, hdm, ↓reduceIte] at hmode
    have hdm' : s'.core.dense_mode ≠ 0#64 := hdm
    simp only [ModeWatchesInv, hdm', ↓reduceIte]
    refine DenseWatchesInv.of_slices hlay'.bounds hlay'.pos_off hlay'.disjoint fun l hl => ?_
    by_cases heq : l = lit
    · subst heq
      have hsl : DenseWatchSliceOk F_cur s.core l off sz := hmode.slices l hl
      rw [hoff_lit, hsz_lit]
      exact denseWatchSliceOk_erase (Nat.le_refl s.core.cur_vars) (fun r hr => hr) hsl hbd_q
        (by omega) (Or.inr ⟨rfl, w0, cref, hw0_q, hcref_q, hlg_q, hcref_lt⟩) hpre_lit hsh_lit
    · rw [(hoth_ws l heq).1, (hoth_ws l heq).2]
      dsimp only [s']
      refine (hmode.slices l hl).mono (Std.Sat.CNF.entails_refl (cnfOfClauses F_cur))
        (Nat.le_refl s.core.cur_vars) (fun r hr => hr) fun idx hi1 hi2 => ?_
      have h := hother l hl heq (idx - fullWatchOffCore s.core l) (by omega)
      rw [Nat.add_sub_cancel' hi1] at h
      exact h

private theorem wp_jump64 {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {J : Cont [i64]} {args : Tup (Arg Val) [i64]} (n : Nat)
    (hx : vals args = (BitVec.ofNat 64 n, ()))
    (hJ : J (BitVec.ofNat 64 n, ()) m) : wp Γ Q X (Expr.jump J args) m :=
  wp_jump_state (proj := fun i : Nat => (BitVec.ofNat 64 i, ())) n hx hJ

private theorem has_bin_shl1 {c : FullCfg} {k : FullCoreState}
    (hl_k : FullCoreState.LengthsOk c k)
    {lit : Val i32} (_hlit : lit.toNat < 2 * k.cur_vars) :
    (BitVec.setWidth 64 lit <<< 1).toNat = 2 * lit.toNat ∧
    (BitVec.setWidth 64 lit <<< 1 + 1).toNat = 2 * lit.toNat + 1 := by
  have hcv := hl_k.cur_vars_le; have hmax : c.max_vars < 2 * 2 ^ 28 := c.hmaxv
  have hsh : (BitVec.setWidth 64 lit <<< 1).toNat = 2 * lit.toNat := by
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega),
      Nat.shiftLeft_eq]
    omega
  refine ⟨hsh, ?_⟩
  simp only [BitVec.toNat_add, hsh]
  rw [show (1 : BitVec 64).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]

private theorem has_bin_init_eq {c : FullCfg} {k : FullCoreState}
    (hl_k : FullCoreState.LengthsOk c k)
    {lit : Val i32} (hlit : lit.toNat < 2 * k.cur_vars)
    (h0 : (BitVec.setWidth 64 lit <<< 1).toNat < k.wvec.length) :
    BitVec.setWidth 64 k.wvec[(BitVec.setWidth 64 lit <<< 1).toNat] =
      BitVec.ofNat 64 (fullWatchOffCore k lit.toNat) := by
  apply BitVec.eq_of_toNat_eq
  have hsh := (has_bin_shl1 hl_k hlit).1
  have hwv0 : 2 * lit.toNat < k.wvec.length := by rw [← hsh]; exact h0
  have hlt0 := k.wvec[2 * lit.toNat].isLt
  have hget : k.wvec[(BitVec.setWidth 64 lit <<< 1).toNat] = k.wvec[2 * lit.toNat] := by
    congr 1
  rw [hget]
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow, fullWatchOffCore,
    List.getElem?_eq_getElem hwv0, Option.getD_some]

private theorem has_bin_end_eq {c : FullCfg} {k : FullCoreState}
    (hl_k : FullCoreState.LengthsOk c k)
    {lit : Val i32} (hlit : lit.toNat < 2 * k.cur_vars)
    (h0 : (BitVec.setWidth 64 lit <<< 1).toNat < k.wvec.length)
    (h1 : (BitVec.setWidth 64 lit <<< 1 + 1).toNat < k.wvec.length) :
    (BitVec.setWidth 64 k.wvec[(BitVec.setWidth 64 lit <<< 1).toNat] +
      BitVec.setWidth 64 k.wvec[(BitVec.setWidth 64 lit <<< 1 + 1).toNat]).toNat =
      fullWatchOffCore k lit.toNat + fullWatchSizeCore k lit.toNat := by
  have hsh := has_bin_shl1 hl_k hlit
  have hwv0 : 2 * lit.toNat < k.wvec.length := by rw [← hsh.1]; exact h0
  have hwv1 : 2 * lit.toNat + 1 < k.wvec.length := by rw [← hsh.2]; exact h1
  have hw0 := k.wvec[2 * lit.toNat].isLt
  have hw1 := k.wvec[2 * lit.toNat + 1].isLt
  have hg0 : k.wvec[(BitVec.setWidth 64 lit <<< 1).toNat] = k.wvec[2 * lit.toNat] := by
    congr 1; exact hsh.1
  have hg1 : k.wvec[(BitVec.setWidth 64 lit <<< 1 + 1).toNat] = k.wvec[2 * lit.toNat + 1] := by
    congr 1; exact hsh.2
  rw [hg0, hg1]
  simp only [BitVec.toNat_add, BitVec.toNat_setWidth, fullWatchOffCore, fullWatchSizeCore,
    List.getElem?_eq_getElem hwv0, List.getElem?_eq_getElem hwv1, Option.getD_some]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

public theorem full_watch_pop_c0_wp (Γ : Env) (_hΓ : Γ.Sat Spec.specs)
    (a : Tup Val [i64, i32, i32]) (m : Mem 64) (Q : Post []) (X : XPost) :
    Spec.fullWatchPopC0Spec a m Q X → Func.wp Γ full_watch_pop_c0_body a m Q X := by
  rcases a with ⟨h, lit, cnt, ⟨⟩⟩
  rintro ⟨c, s, R, rfl, hlen, hlay, hlit, hcnt0, hcnt_le, hm, hQ⟩
  have hcv := hlen.core_ok.cur_vars_le; have hwv := hlen.core_ok.wvec_len
  have hwl := hlen.core_ok.wstk_len_arr; have hbounds := hlay.bounds lit.toNat hlit
  have hwl_le := hlen.core_ok.wlen_le
  have hcmax : c.max_vars < 2 * 2 ^ 28 := c.hmaxv
  have hcwcap : c.wcap < 2 * 2 ^ 28 := c.hwcap
  have hmod_wv0 : (2 * lit.toNat) % 2 ^ 64 = 2 * lit.toNat := Nat.mod_eq_of_lt (by omega)
  have hmod_wv : (2 * lit.toNat + 1) % 2 ^ 64 = 2 * lit.toNat + 1 :=
    Nat.mod_eq_of_lt (by omega)
  have hwv0 : 2 * lit.toNat < s.core.wvec.length := by omega
  have hwv1 : 2 * lit.toNat + 1 < s.core.wvec.length := by omega
  have h1_64 : (1 : BitVec 64).toNat = 1 := rfl
  c0_go
  · exfalso
    simp only [h1_64, hmod_wv] at hc
    simp only [fullWatchSize, fullWatchSizeCore] at hcnt_le
    rw [List.getElem?_eq_getElem hwv1, Option.getD_some] at hcnt_le
    omega
  · exfalso
    have hw0 := s.core.wvec[2 * lit.toNat].isLt
    have hw1 := s.core.wvec[2 * lit.toNat + 1].isLt
    simp only [hmod_wv0, h1_64, hmod_wv] at hc
    rw [Nat.mod_eq_of_lt (show s.core.wlen < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (by omega)] at hc
    simp only [fullWatchOffCore, fullWatchSizeCore, List.getElem?_eq_getElem hwv0,
      List.getElem?_eq_getElem hwv1, Option.getD_some] at hbounds
    omega
  let off := fullWatchOffCore s.core lit.toNat
  let sz := fullWatchSizeCore s.core lit.toNat
  let Inv : Nat → Mem 64 → Prop := fun i m' =>
    sz - cnt.toNat ≤ i ∧ i ≤ sz ∧
    ∃ wstk' : List (BitVec 32),
      wstk'.length = s.core.wstk.length ∧
      (∀ idx, idx < off + (sz - cnt.toNat) → wstk'[idx]? = s.core.wstk[idx]?) ∧
      (∀ idx, off + i ≤ idx → idx < s.core.wstk.length → wstk'[idx]? = s.core.wstk[idx]?) ∧
      (FullMem c { s with core := { s.core with wstk := wstk' } } ⋆ R) m'
  apply wp_while_state1 (t := i64) (fun i : Nat => BitVec.ofNat 64 i) (fun i => sz - i) Inv
  · intro J hJ; c0_go
    have hsh1 := (has_bin_shl1 hlen.core_ok hlit).2
    have hw1_idx : (BitVec.setWidth 64 lit <<< 1 + 1).toNat < s.core.wvec.length := by
      rw [hsh1]; exact hwv1
    have hinit : BitVec.setWidth 64 (s.core.wvec[(BitVec.setWidth 64 lit <<< 1 + 1).toNat]) -
        BitVec.setWidth 64 cnt = BitVec.ofNat 64 (sz - BitVec.toNat cnt) := by
      apply BitVec.eq_of_toNat_eq
      have hget : s.core.wvec[(BitVec.setWidth 64 lit <<< 1 + 1).toNat] =
          s.core.wvec[2 * lit.toNat + 1] := by
        congr 1
      rw [hget]
      simp only [fullWatchSize, fullWatchSizeCore, List.getElem?_eq_getElem hwv1,
        Option.getD_some] at hcnt_le
      simp only [sz, fullWatchSizeCore, List.getElem?_eq_getElem hwv1, Option.getD_some,
        BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow]
      have hw1_lt := s.core.wvec[2 * lit.toNat + 1].isLt
      have hcnt_lt := cnt.isLt
      rw [Nat.mod_eq_of_lt (show cnt.toNat < 2 ^ 64 by omega),
        Nat.mod_eq_of_lt (show s.core.wvec[2 * lit.toNat + 1].toNat < 2 ^ 64 by omega),
        Nat.mod_eq_of_lt (show s.core.wvec[2 * lit.toNat + 1].toNat - cnt.toNat < 2 ^ 64 by omega)]
      omega
    rw [hinit]
    exact hJ _ m ⟨Nat.le_refl _, by omega, s.core.wstk, rfl, fun _ _ => rfl,
      fun _ _ _ => rfl, hm⟩
  · intro J i m' hInv ih
    rcases hInv with ⟨hi1, hi2, wstk', hwlen', hpre, hpost, hm'⟩
    c0_go
    · have hsz_lt : sz < 2 ^ 64 := by
        have := s.core.wvec[2 * lit.toNat + 1].isLt
        simp only [sz, fullWatchSizeCore, List.getElem?_eq_getElem hwv1, Option.getD_some]
        omega
      have hlt : i < sz := by
        simp only [h1_64, hmod_wv] at hc
        rw [Nat.mod_eq_of_lt (by omega)] at hc
        simp only [sz, fullWatchSizeCore, List.getElem?_eq_getElem hwv1, Option.getD_some]
        omega
      have hidx : off + i < wstk'.length := by omega
      c0_go
      · have hsh0 := (has_bin_shl1 hlen.core_ok hlit).1
        have h0_lt : (BitVec.setWidth 64 lit <<< 1).toNat < s.core.wvec.length := by
          rw [hsh0]; exact hwv0
        have hget0 : s.core.wvec[(BitVec.setWidth 64 lit <<< 1).toNat]'h0_lt =
            s.core.wvec[2 * lit.toNat] := by
          congr 1
        have hidx_eq : (BitVec.setWidth 64
              (s.core.wvec[(BitVec.setWidth 64 lit <<< 1).toNat]'h0_lt) +
            BitVec.ofNat 64 i).toNat = off + i := by
          rw [hget0]
          have hw0_lt := s.core.wvec[2 * lit.toNat].isLt
          simp only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
            Nat.reducePow, off, fullWatchOffCore, List.getElem?_eq_getElem hwv0,
            Option.getD_some]
          rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
            Nat.mod_eq_of_lt (by omega)]
        have hm_upd : (FullMem c { s with core := { s.core with
            wstk := wstk'.set (off + i) 0xFFFFFFFF#32 } } ⋆ R) m := by
          rw [hidx_eq] at hm; exact hm
        have hjump_i : BitVec.ofNat 64 i + 1 = BitVec.ofNat 64 (i + 1) := by
          apply BitVec.eq_of_toNat_eq
          simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, h1_64]
          rw [Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega),
            Nat.mod_eq_of_lt (show i + 1 < 2 ^ 64 by omega)]
        rw [hjump_i]
        exact ih (i + 1) _ (by omega) ⟨by omega, by omega, wstk'.set (off + i) 0xFFFFFFFF#32,
          by simp [hwlen'],
          fun idx hlt' => by rw [List.getElem?_set_ne (by omega), hpre idx hlt'],
          fun idx hle' hi_lt => by
            rw [List.getElem?_set_ne (by omega), hpost idx (by omega) hi_lt],
          hm_upd⟩
    · have hsz_lt : sz < 2 ^ 64 := by
        have := s.core.wvec[2 * lit.toNat + 1].isLt
        simp only [sz, fullWatchSizeCore, List.getElem?_eq_getElem hwv1, Option.getD_some]
        omega
      have hieq : i = sz := by
        simp only [h1_64, hmod_wv] at hc
        rw [Nat.mod_eq_of_lt (by omega)] at hc
        simp only [sz, fullWatchSizeCore, List.getElem?_eq_getElem hwv1, Option.getD_some] at hi2 ⊢
        omega
      subst hieq
      c0_go
      have hwv1 : 2 * lit.toNat + 1 < s.core.wvec.length := by omega
      c0_go
      have hsz_lt : sz - cnt.toNat < 2 ^ 32 := by
        have : sz < 2 ^ 32 := (s.core.wvec[2 * lit.toNat + 1]?.getD 0#32).isLt; omega
      have hother : ∀ l < 2 * s.core.cur_vars, l ≠ lit.toNat →
          ∀ idx < fullWatchSizeCore s.core l,
            wstk'[fullWatchOffCore s.core l + idx]? =
              s.core.wstk[fullWatchOffCore s.core l + idx]? := by
        intro l hl hne idx hidx
        have hdisj := hlay.disjoint l lit.toNat hl hlit hne
          (Nat.lt_of_le_of_lt (Nat.zero_le _) hidx) (by omega)
        rcases hdisj with hle_l | hle_r
        · exact hpre _ (by omega)
        · exact hpost _ (by omega) (by have := hlay.bounds l hl; omega)
      have hnosent : ∀ idx < sz - cnt.toNat,
          wstk'[off + idx]? ≠ some 0xFFFFFFFF#32 := by
        intro idx hidx; rw [hpre (off + idx) (by omega)]
        exact hlay.no_sentinel lit.toNat hlit idx (by omega)
      let wvec' := s.core.wvec.set (2 * lit.toNat + 1) (BitVec.ofNat 32 (sz - cnt.toNat))
      let k' : FullCoreState := { s.core with
        wvec := wvec', wstk := wstk',
        wusable := s.core.wusable + BitVec.zeroExtend 64 cnt }
      have hlay' : WatchStackLayout k' :=
        watchStackLayout_shrink hlay hlen.core_ok hlit hcnt_le hother hnosent (Nat.le_refl _)
      have hwv_len' : wvec'.length = 4 * c.max_vars := by simp [wvec', hwv]
      have hws_len' : wstk'.length = c.wcap := by rw [hwlen', hwl]
      have hlen_core' : k'.LengthsOk c :=
        { hlen.core_ok with wvec_len := hwv_len', wstk_len_arr := hws_len' }
      have hoff_lit : fullWatchOffCore k' lit.toNat = off := by
        dsimp only [fullWatchOffCore, k', wvec']
        exact congrArg BitVec.toNat (wvec_set_size_off_self hwv1 _)
      have hsz_lit : fullWatchSizeCore k' lit.toNat = sz - cnt.toNat := by
        dsimp only [fullWatchSizeCore, k', wvec']
        rw [wvec_set_size_sz_self hwv1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsz_lt]
      have hsh1 := (has_bin_shl1 hlen.core_ok hlit).2
      have hw1_idx : (BitVec.setWidth 64 lit <<< 1 + 1).toNat < s.core.wvec.length := by
        rw [hsh1]; exact hwv1
      have hsz_eq : fullWatchSize s lit.toNat = sz := rfl
      have hw1_toNat : (s.core.wvec[(BitVec.setWidth 64 lit <<< 1 + 1).toNat]'hw1_idx).toNat =
          sz := by
        have h_get : s.core.wvec[(BitVec.setWidth 64 lit <<< 1 + 1).toNat]'hw1_idx =
            s.core.wvec[2 * lit.toNat + 1]'hwv1 := by
          have h := hsh1
          generalize (BitVec.setWidth 64 lit <<< 1 + 1).toNat = j at hw1_idx h ⊢
          subst h; rfl
        rw [h_get, ← hsz_eq]
        dsimp only [fullWatchSize, fullWatchSizeCore]
        rw [List.getElem?_eq_getElem hwv1]
        rfl
      have hcnt_lt64 : cnt.toNat < 2 ^ 64 := by have := cnt.isLt; omega
      have hsz_lt64 : sz < 2 ^ 64 := by omega
      have hw1_val_eq : BitVec.setWidth 32
          (BitVec.setWidth 64 (s.core.wvec[(BitVec.setWidth 64 lit <<< 1 + 1).toNat]'hw1_idx) -
            BitVec.setWidth 64 cnt) = BitVec.ofNat 32 (sz - cnt.toNat) := by
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.reducePow,
          hw1_toNat, Nat.mod_eq_of_lt hsz_lt64, Nat.mod_eq_of_lt hcnt_lt64,
          Nat.mod_eq_of_lt hsz_lt]
        have hle : cnt.toNat ≤ sz := by omega
        omega
      rw [hw1_val_eq, hsh1] at hm
      apply hQ wvec' wstk' (s.core.wusable + BitVec.zeroExtend 64 cnt) _
        ⟨hlen_core', hlen.scratch_ok⟩ hlay'
      · intro l hl hne
        have hw' :=
          wvec_set_size_other (wvec := s.core.wvec) hne (BitVec.ofNat 32 (sz - cnt.toNat))
        have hoff_eq : fullWatchOff { s with core := k' } l = fullWatchOff s l := by
          dsimp only [fullWatchOff, fullWatchOffCore, k', wvec']
          exact congrArg BitVec.toNat hw'.1
        have hsz_eq' : fullWatchSize { s with core := k' } l = fullWatchSize s l := by
          dsimp only [fullWatchSize, fullWatchSizeCore, k', wvec']
          exact congrArg BitVec.toNat hw'.2
        exact ⟨hoff_eq, hsz_eq', fun idx hidx => by
          rw [hoff_eq]; exact hother l hl hne idx hidx⟩
      · exact hoff_lit
      · exact hsz_lit
      · intro idx hidx
        rw [show fullWatchOff { s with core := k' } lit.toNat = off from hoff_lit]
        have hidx' : idx < sz - cnt.toNat := by
          dsimp only [fullWatchSize] at hidx
          exact hidx
        exact hpre (off + idx) (by omega)
      · exact hm

@[local c0_load] private theorem c0_load_full_wstk64_add8_lit {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64} (hi : i.toNat + 3 < s.core.wstk.length)
    (hm : (FullMem c s ⋆ R) m) :
    loadVal m i64 (c.pWstk + i * 4 + 8#64) =
      some (pack64 s.core.wstk[i.toNat + 2] s.core.wstk[i.toNat + 3]) :=
  WatchMemTactics.c0_load_full_wstk64_add8 hi hm

@[local c0_store] private theorem c0_store_full_wstk64_add8_lit {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64} (v : BitVec 64)
    (hi : i.toNat + 3 < s.core.wstk.length) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i64 (c.pWstk + i * 4 + 8#64) ∧
      (FullMem c { s with core := { s.core with
        wstk := (s.core.wstk.set (i.toNat + 2) (v.setWidth 32)).set (i.toNat + 3)
          ((v >>> 32).setWidth 32) } } ⋆ R)
        (storeMem m i64 (c.pWstk + i * 4 + 8#64) v) :=
  WatchMemTactics.c0_store_full_wstk64_add8 v hi hm

@[local c0_store] private theorem c0_store_full_wstk64_add0 {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64} (v : BitVec 64)
    (hi : i.toNat + 1 < s.core.wstk.length) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i64 (c.pWstk + i * 4 + 0#64) ∧
      (FullMem c { s with core := { s.core with
        wstk := (s.core.wstk.set i.toNat (v.setWidth 32)).set (i.toNat + 1)
          ((v >>> 32).setWidth 32) } } ⋆ R)
        (storeMem m i64 (c.pWstk + i * 4 + 0#64) v) := by
  rw [show c.pWstk + i * 4 + 0#64 = c.pWstk + i * 4 from BitVec.add_zero _]
  exact WatchMemTactics.c0_store_full_wstk64 v hi hm

public theorem full_unwatch_large_wp (Γ : Env) (_hΓ : Γ.Sat Spec.specs)
    (a : Tup Val [i64, i32, i32]) (m : Mem 64) (Q : Post []) (X : XPost) :
    fullUnwatchLargeSpec a m Q X → Func.wp Γ full_unwatch_large_body a m Q X := by
  rcases a with ⟨h, lit, cref, ⟨⟩⟩
  rintro ⟨c, s, R, rfl, hlen, hlay, hm, hQ⟩
  have hcv := hlen.core_ok.cur_vars_le; have hwv := hlen.core_ok.wvec_len
  have hwl := hlen.core_ok.wstk_len_arr; have hwl_le := hlen.core_ok.wlen_le
  have hcmax : c.max_vars < 2 * 2 ^ 28 := c.hmaxv
  have hcwcap : c.wcap < 2 * 2 ^ 28 := c.hwcap
  c0_go
  · exact hQ s.core.wvec s.core.wstk s.core.wusable m hlen hlay (fun _ hm' => hm') hm
  · exact hQ s.core.wvec s.core.wstk s.core.wusable m hlen hlay (fun _ hm' => hm') hm
  · exact hQ s.core.wvec s.core.wstk s.core.wusable m hlen hlay (fun _ hm' => hm') hm
  · have hlit : lit.toNat < 2 * s.core.cur_vars := by omega
    have hcref_bin0 : cref &&& 0x80000000#32 = 0#32 := by assumption
    have hbounds := hlay.bounds lit.toNat hlit
    have hwv0 : 2 * lit.toNat < s.core.wvec.length := by omega
    have hwv1 : 2 * lit.toNat + 1 < s.core.wvec.length := by omega
    have hmod_wv0 : (2 * lit.toNat) % 2 ^ 64 = 2 * lit.toNat := Nat.mod_eq_of_lt (by omega)
    have hmod_wv1 : (2 * lit.toNat + 1) % 2 ^ 64 = 2 * lit.toNat + 1 := Nat.mod_eq_of_lt (by omega)
    let off := fullWatchOffCore s.core lit.toNat
    let sz := fullWatchSizeCore s.core lit.toNat
    have hsz2 : 2 ≤ sz := by
      have h1_64 : (1 : BitVec 64).toNat = 1 := rfl
      have h2_64 : (2 : BitVec 64).toNat = 2 := rfl
      simp only [h1_64, h2_64, hmod_wv1] at hc
      simp only [sz, fullWatchSizeCore, List.getElem?_eq_getElem hwv1, Option.getD_some]
      omega
    apply wp_while_state1 (fun p : Nat => BitVec.ofNat 64 p) (fun p => p - off)
      (fun p m' => m = m' ∧ off ≤ p ∧ p ≤ off + sz ∧
        (∀ F_cur, ModeWatchesInv F_cur s.core → WatchBoundary s.core.wstk off sz p))
    · intro J hJ; c0_go
      have hsh := has_bin_shl1 hlen.core_ok hlit
      have hj_eq : BitVec.setWidth 64 s.core.wvec[(BitVec.setWidth 64 lit <<< 1).toNat] +
          BitVec.setWidth 64 s.core.wvec[(BitVec.setWidth 64 lit <<< 1 + 1).toNat] =
          BitVec.ofNat 64 (off + sz) := by
        apply BitVec.eq_of_toNat_eq
        rw [has_bin_end_eq hlen.core_ok hlit (by rw [hsh.1]; omega) (by rw [hsh.2]; omega),
          BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      rw [hj_eq]
      exact hJ (off + sz) m ⟨rfl, by omega, Nat.le_refl _, fun F_cur hm' => by
        by_cases hdm : s.core.dense_mode = 0#64
        · simp only [ModeWatchesInv, hdm, ↓reduceIte] at hm'
          exact watchSliceOk_boundary_end (hm'.slices lit.toNat hlit)
        · simp only [ModeWatchesInv, hdm, ↓reduceIte] at hm'
          exact denseWatchSliceOk_boundary_end (hm'.slices lit.toNat hlit)⟩
    · intro J p m' hP ih
      rcases hP with ⟨rfl, hp_ge, hp_le, hbd_impl⟩
      c0_step1; c0_step1
      · have hp2 : off + 2 ≤ p := by
          have := s.core.wvec[2 * lit.toNat].isLt
          have h2_64 : (2 : BitVec 64).toNat = 2 := rfl
          simp only [hmod_wv0, h2_64] at hc
          rw [Nat.mod_eq_of_lt (by omega)] at hc
          simp only [off, fullWatchOffCore, List.getElem?_eq_getElem hwv0, Option.getD_some]
          omega
        have hwidx : p - 1 < s.core.wstk.length := by omega
        c0_step1; c0_step1
        · let q := p - 2
          have hq_ge : off ≤ q := by omega
          have hq2 : q + 2 ≤ off + sz := by omega
          have hw_eq : s.core.wstk[p - 1] = cref := by
            have h1_64 : (1 : BitVec 64).toNat = 1 := rfl
            have hp1 : (2 ^ 64 - 1 + p) % 2 ^ 64 = p - 1 := by omega
            simp only [h1_64, hp1] at hc
            exact hc
          have hbd_q_impl : ∀ F_cur, ModeWatchesInv F_cur s.core →
              WatchBoundary s.core.wstk off sz q ∧
              ∃ w0 cref', s.core.wstk[q]? = some w0 ∧ s.core.wstk[q + 1]? = some cref' ∧
                w0 &&& 0x80000000#32 = 0#32 ∧ cref'.toNat < 2147483648 := by
            intro F_cur hm'
            rcases watchBoundary_prev (hbd_impl F_cur hm') (by omega) with
              ⟨w0, hw0, hbin, _⟩ | ⟨w0, cref', _, hw0, hw1, hlg, hlt', hr'⟩
            · have hweq : w0 = cref := by
                have hsome := List.getElem?_eq_getElem hwidx
                rw [hw0] at hsome; cases hsome; exact hw_eq
              rw [hweq] at hbin; exact absurd hcref_bin0 hbin
            · refine ⟨hr', w0, cref', hw0, ?_, hlg, hlt'⟩
              simpa [q, show p - 2 + 1 = p - 1 by omega] using hw1
          have hqp : q + 2 = p := by omega
          have h1_64 : (1 : BitVec 64).toNat = 1 := rfl
          have h4_64 : (4 : BitVec 64).toNat = 4 := rfl
          have hw0_lt := s.core.wvec[2 * lit.toNat].isLt
          have hw1_lt := s.core.wvec[2 * lit.toNat + 1].isLt
          have hoff_sz_eq : off + sz = s.core.wvec[2 * lit.toNat].toNat +
              s.core.wvec[2 * lit.toNat + 1].toNat := by
            simp only [off, sz, fullWatchOffCore, fullWatchSizeCore,
              List.getElem?_eq_getElem hwv0, List.getElem?_eq_getElem hwv1, Option.getD_some]
          let SInv : Nat × Nat × List (BitVec 32) → Mem 64 → Prop := fun st m1 =>
            UnwatchShiftInv s.core { s.core with wstk := st.2.2 } off sz q st.1 st.2.1 ∧
            (FullMem c { s with core := { s.core with wstk := st.2.2 } } ⋆ R) m1
          let proj2 : Nat × Nat × List (BitVec 32) → Tup Val [i64, i64] :=
            fun st => (BitVec.ofNat 64 st.1, BitVec.ofNat 64 st.2.1, ())
          apply wp_join_state proj2 SInv
          · intro J610 ⟨src1, dst1, wstk1⟩ m1 ⟨hinv1, hm1⟩
            dsimp only [proj2] at hinv1 hm1 ⊢
            c0_step1
            apply wp_while_state proj2 (fun st => off + sz - st.1) SInv
            · intro J830 hJ830; c0_step1
              exact hJ830 (src1, dst1, wstk1) m1 ⟨hinv1, hm1⟩
            · intro J830 ⟨src2, dst2, wstk2⟩ m2 ⟨hinv2, hm2⟩ ih830
              dsimp only [proj2] at hinv2 hm2 ih830 ⊢
              let k2 : FullCoreState := { s.core with wstk := wstk2 }
              have hlt_src2 := hinv2.2.2.2.2.1
              have hwlen2 : k2.wstk.length = s.core.wstk.length := hinv2.2.2.2.2.2.2.2.2.2
              have hsrc2_bv : (BitVec.ofNat 64 src2).toNat = src2 := Nat.mod_eq_of_lt (by omega)
              have hdst2_src2 : dst2 + 2 = src2 := hinv2.2.2.1
              have hdst2_le : dst2 ≤ off + sz := by omega
              have hdst2_bv : (BitVec.ofNat 64 dst2).toNat = dst2 := Nat.mod_eq_of_lt (by omega)
              c0_step1; c0_step1
              · have h4 : src2 + 4 ≤ off + sz := by
                  simp only [hmod_wv0, h1_64, hmod_wv1, h4_64] at hc
                  try rw [hsrc2_bv] at hc
                  rw [Nat.mod_eq_of_lt (show src2 + 4 < 2 ^ 64 by omega), ← hoff_sz_eq,
                    Nat.mod_eq_of_lt (show off + sz < 2 ^ 64 by omega)] at hc
                  omega
                have hsrc2_p2 : (BitVec.ofNat 64 src2 + 2).toNat = src2 + 2 := by
                  simp [BitVec.toNat_add, hsrc2_bv,
                    Nat.mod_eq_of_lt (show src2 + 2 < 2 ^ 64 by omega)]
                have hdst2_p2 : (BitVec.ofNat 64 dst2 + 2).toNat = dst2 + 2 := by
                  simp [BitVec.toNat_add, hdst2_bv,
                    Nat.mod_eq_of_lt (show dst2 + 2 < 2 ^ 64 by omega)]
                simp only [BitVec.add_zero]
                have hwlen2' : wstk2.length = s.core.wstk.length := by
                  have h := hinv2.2.2.2.2.2.2.2.2.2
                  dsimp only at h; exact h
                have h_s2_0 : src2 + 1 < wstk2.length := by
                  have := hinv2.2.2.1; omega
                have h_d2_0 : dst2 + 1 < wstk2.length := by
                  have := hinv2.2.2.1; omega
                c0_go
                have h_s2 : src2 + 3 < k2.wstk.length := by omega
                have h_d2 : dst2 + 3 < k2.wstk.length := by omega
                dsimp only [k2] at h_s2 h_d2
                c0_go
                simp only [hsrc2_bv, hdst2_bv] at hm
                let v0 := pack64 k2.wstk[src2] k2.wstk[src2 + 1]
                let v1 := pack64 k2.wstk[src2 + 2] k2.wstk[src2 + 3]
                have h_l2 : ((k2.wstk.set dst2 (v0.setWidth 32)).set (dst2 + 1)
                    ((v0 >>> 32).setWidth 32))[src2 + 2]'(by simp [hwlen2]; omega) =
                    k2.wstk[src2 + 2] := by
                  rw [List.getElem_set_ne (by omega), List.getElem_set_ne (by omega)]
                have h_l3 : ((k2.wstk.set dst2 (v0.setWidth 32)).set (dst2 + 1)
                    ((v0 >>> 32).setWidth 32))[src2 + 3]'(by simp [hwlen2]; omega) =
                    k2.wstk[src2 + 3] := by
                  rw [List.getElem_set_ne (by omega), List.getElem_set_ne (by omega)]
                dsimp only [v0, k2] at h_l2 h_l3
                try simp only [h_l2, h_l3] at hm
                have hinv2' := unwatchShiftInv_step4 hinv2 h4 (by omega) v0 v1
                  (by rw [List.getElem?_eq_getElem (by dsimp only [k2]; omega), pack64_lo])
                  (by rw [List.getElem?_eq_getElem (by dsimp only [k2]; omega), pack64_hi])
                  (by rw [List.getElem?_eq_getElem (by dsimp only [k2]; omega), pack64_lo])
                  (by rw [List.getElem?_eq_getElem (by dsimp only [k2]; omega), pack64_hi])
                have hj4 : BitVec.ofNat 64 src2 + 4 = BitVec.ofNat 64 (src2 + 4) ∧
                    BitVec.ofNat 64 dst2 + 4 = BitVec.ofNat 64 (dst2 + 4) := by
                  have h4_bv : (4 : BitVec 64).toNat = 4 := rfl
                  constructor <;> apply BitVec.eq_of_toNat_eq <;>
                    (simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, h4_bv]
                     omega)
                rw [hj4.1, hj4.2]
                exact ih830 (src2 + 4, dst2 + 4, _) _ (by omega) ⟨hinv2', hm⟩
              · have hno4 : ¬ (src2 + 4 ≤ off + sz) := by
                  simp only [hmod_wv0, h1_64, hmod_wv1, h4_64] at hc
                  try rw [hsrc2_bv] at hc
                  rw [Nat.mod_eq_of_lt (show src2 + 4 < 2 ^ 64 by omega), ← hoff_sz_eq,
                    Nat.mod_eq_of_lt (show off + sz < 2 ^ 64 by omega)] at hc
                  omega
                let SInv1070 : Nat × Nat × List (BitVec 32) → Mem 64 → Prop := fun st m1 =>
                  SInv st m1 ∧ off + sz < st.1 + 2
                apply wp_join_state proj2 SInv1070
                · intro J1070 ⟨src3, dst3, wstk3⟩ m3 ⟨⟨hinv3, hm3⟩, hlt_tail⟩
                  dsimp only [proj2] at hinv3 hm3 hlt_tail ⊢
                  let k3 : FullCoreState := { s.core with wstk := wstk3 }
                  have hlt_src3 := hinv3.2.2.2.2.1
                  have hwlen3 : k3.wstk.length = s.core.wstk.length := hinv3.2.2.2.2.2.2.2.2.2
                  apply wp_join0 (fun m4 => ∃ wstk4,
                    UnwatchShiftInv s.core { s.core with wstk := wstk4 } off sz q
                      (off + sz) (off + sz - 2) ∧
                    (FullMem c { s with core := { s.core with wstk := wstk4 } } ⋆ R) m4)
                  · intro J1290 m4 ⟨wstk4, hinv4, hm4⟩
                    have hwlen4 := hinv4.2.2.2.2.2.2.2.2.2
                    dsimp only at hwlen4
                    have hsh := has_bin_shl1 hlen.core_ok hlit
                    have h0_lt : (BitVec.setWidth 64 lit <<< 1).toNat < s.core.wvec.length := by
                      rw [hsh.1]; exact hwv0
                    have h1_lt : (BitVec.setWidth 64 lit <<< 1 + 1).toNat < s.core.wvec.length := by
                      rw [hsh.2]; exact hwv1
                    have hm2_eq : (BitVec.setWidth 64 (s.core.wvec[
                          (BitVec.setWidth 64 lit <<< 1).toNat]'h0_lt) +
                        BitVec.setWidth 64 (s.core.wvec[
                          (BitVec.setWidth 64 lit <<< 1 + 1).toNat]'h1_lt) - 2).toNat =
                        off + sz - 2 := by
                      have hg0 : s.core.wvec[(BitVec.setWidth 64 lit <<< 1).toNat]'h0_lt =
                          s.core.wvec[2 * lit.toNat] := by congr 1; try exact hsh.1
                      have hg1 : s.core.wvec[(BitVec.setWidth 64 lit <<< 1 + 1).toNat]'h1_lt =
                          s.core.wvec[2 * lit.toNat + 1] := by congr 1; try exact hsh.2
                      rw [hg0, hg1]
                      have h2_64 : (2 : BitVec 64).toNat = 2 := rfl
                      simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_setWidth, h2_64,
                        Nat.mod_eq_of_lt (show s.core.wvec[2 * lit.toNat].toNat < 2 ^ 64 by omega),
                        Nat.mod_eq_of_lt
                          (show s.core.wvec[2 * lit.toNat + 1].toNat < 2 ^ 64 by omega)]
                      rw [← hoff_sz_eq, Nat.mod_eq_of_lt (show off + sz < 2 ^ 64 by omega)]
                      omega
                    have hm1_eq : (BitVec.setWidth 64 (s.core.wvec[
                          (BitVec.setWidth 64 lit <<< 1).toNat]'h0_lt) +
                        BitVec.setWidth 64 (s.core.wvec[
                          (BitVec.setWidth 64 lit <<< 1 + 1).toNat]'h1_lt) - 1).toNat =
                        off + sz - 1 := by
                      have hg0 : s.core.wvec[(BitVec.setWidth 64 lit <<< 1).toNat]'h0_lt =
                          s.core.wvec[2 * lit.toNat] := by congr 1; try exact hsh.1
                      have hg1 : s.core.wvec[(BitVec.setWidth 64 lit <<< 1 + 1).toNat]'h1_lt =
                          s.core.wvec[2 * lit.toNat + 1] := by congr 1; try exact hsh.2
                      rw [hg0, hg1]
                      simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_setWidth, h1_64,
                        Nat.mod_eq_of_lt (show s.core.wvec[2 * lit.toNat].toNat < 2 ^ 64 by omega),
                        Nat.mod_eq_of_lt
                          (show s.core.wvec[2 * lit.toNat + 1].toNat < 2 ^ 64 by omega)]
                      rw [← hoff_sz_eq, Nat.mod_eq_of_lt (show off + sz < 2 ^ 64 by omega)]
                      omega
                    have hw1_val : BitVec.setWidth 32 (BitVec.setWidth 64 (s.core.wvec[
                          (BitVec.setWidth 64 lit <<< 1 + 1).toNat]'h1_lt) - 2) =
                        BitVec.ofNat 32 (sz - 2) := by
                      have hg1 : s.core.wvec[(BitVec.setWidth 64 lit <<< 1 + 1).toNat]'h1_lt =
                          s.core.wvec[2 * lit.toNat + 1] := by congr 1; try exact hsh.2
                      rw [hg1]
                      apply BitVec.eq_of_toNat_eq
                      have h2_64 : (2 : BitVec 64).toNat = 2 := rfl
                      simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat,
                        Nat.reducePow, h2_64, sz, fullWatchSizeCore,
                        List.getElem?_eq_getElem hwv1, Option.getD_some,
                        Nat.mod_eq_of_lt
                          (show s.core.wvec[2 * lit.toNat + 1].toNat < 2 ^ 64 by omega)]
                      have hw1_ge2 : 2 ≤ s.core.wvec[2 * lit.toNat + 1].toNat := by
                        simpa [sz, fullWatchSizeCore, List.getElem?_eq_getElem hwv1,
                          Option.getD_some] using hsz2
                      have hsz_lt : s.core.wvec[2 * lit.toNat + 1].toNat - 2 < 2 ^ 32 := by omega
                      have hsub_eq : (2 ^ 64 - 2 + s.core.wvec[2 * lit.toNat + 1].toNat) % 2 ^ 64 =
                          s.core.wvec[2 * lit.toNat + 1].toNat - 2 := by omega
                      rw [hsub_eq, Nat.mod_eq_of_lt hsz_lt]
                      try rw [Nat.mod_eq_of_lt hsz_lt]
                    have hm2_lt : (BitVec.setWidth 64 (s.core.wvec[
                          (BitVec.setWidth 64 lit <<< 1).toNat]'h0_lt) +
                        BitVec.setWidth 64 (s.core.wvec[
                          (BitVec.setWidth 64 lit <<< 1 + 1).toNat]'h1_lt) - 2).toNat <
                        wstk4.length := by rw [hm2_eq]; omega
                    have hm1_lt : (BitVec.setWidth 64 (s.core.wvec[
                          (BitVec.setWidth 64 lit <<< 1).toNat]'h0_lt) +
                        BitVec.setWidth 64 (s.core.wvec[
                          (BitVec.setWidth 64 lit <<< 1 + 1).toNat]'h1_lt) - 1).toNat <
                        wstk4.length := by rw [hm1_eq]; omega
                    c0_go
                    rw [hm2_eq, hm1_eq, hw1_val] at hm
                    rw [hsh.2] at hm
                    have ht_fin := full_unwatch_tail_inv hlen hlay hlit hq_ge hq2 rfl hinv4
                      hbd_q_impl
                    exact hQ _ _ _ _ ht_fin.1 ht_fin.2.1 ht_fin.2.2 hm
                  · intro J1290 hJ1290
                    have hsrc3_bv : (BitVec.ofNat 64 src3).toNat = src3 :=
                      Nat.mod_eq_of_lt (by omega)
                    have hdst3_le : dst3 ≤ off + sz := by
                      have := hinv3.2.2.1; omega
                    have hdst3_bv : (BitVec.ofNat 64 dst3).toNat = dst3 :=
                      Nat.mod_eq_of_lt (by omega)
                    c0_step1; c0_step1
                    · have h1 : src3 < off + sz := by
                        simp only [hmod_wv0, h1_64, hmod_wv1] at hc
                        try rw [hsrc3_bv] at hc
                        rw [← hoff_sz_eq, Nat.mod_eq_of_lt (show off + sz < 2 ^ 64 by omega)] at hc
                        omega
                      have heq1 : src3 + 1 = off + sz := by omega
                      have hwlen3' : wstk3.length = s.core.wstk.length := by
                        have h := hinv3.2.2.2.2.2.2.2.2.2
                        dsimp only at h; exact h
                      have hs3_lt : src3 < wstk3.length := by
                        have := hinv3.2.2.1; omega
                      have hd3_lt : dst3 < wstk3.length := by
                        have := hinv3.2.2.1; omega
                      c0_go
                      try rw [hdst3_bv] at hm
                      simp only [hsrc3_bv] at hm
                      have hinv4 := unwatchShiftInv_step1 hinv3 h1 (by omega) wstk3[src3]
                        (List.getElem?_eq_getElem (by omega))
                      have hdst1 : dst3 + 1 = off + sz - 2 := by have := hinv3.2.2.1; omega
                      exact hJ1290 _ ⟨_, by simpa [heq1, hdst1] using hinv4, hm⟩
                    · have heq0 : src3 = off + sz := by
                        simp only [hmod_wv0, h1_64, hmod_wv1] at hc
                        try rw [hsrc3_bv] at hc
                        rw [← hoff_sz_eq, Nat.mod_eq_of_lt (show off + sz < 2 ^ 64 by omega)] at hc
                        omega
                      have hdst0 : dst3 = off + sz - 2 := by have := hinv3.2.2.1; omega
                      exact hJ1290 _ ⟨wstk3, by simpa [heq0, hdst0] using hinv3, hm3⟩
                · intro J1070 hJ1070
                  c0_step1; c0_step1
                  · have h2 : src2 + 2 ≤ off + sz := by
                      have h2_64 : (2 : BitVec 64).toNat = 2 := rfl
                      simp only [hmod_wv0, h1_64, hmod_wv1, h2_64] at hc
                      try rw [hsrc2_bv] at hc
                      rw [Nat.mod_eq_of_lt (show src2 + 2 < 2 ^ 64 by omega), ← hoff_sz_eq,
                        Nat.mod_eq_of_lt (show off + sz < 2 ^ 64 by omega)] at hc
                      omega
                    have hwlen2' : wstk2.length = s.core.wstk.length := by
                      have h := hinv2.2.2.2.2.2.2.2.2.2
                      dsimp only at h; exact h
                    have hs2_lt : src2 < wstk2.length := by
                      have := hinv2.2.2.1; omega
                    have hd2_lt : dst2 < wstk2.length := by
                      have := hinv2.2.2.1; omega
                    have h_s2 : src2 + 1 < k2.wstk.length := by omega
                    have h_d2 : dst2 + 1 < k2.wstk.length := by omega
                    dsimp only [k2] at h_s2 h_d2
                    simp only [BitVec.add_zero]
                    c0_go
                    simp only [hsrc2_bv, hdst2_bv] at hm
                    let v := pack64 k2.wstk[src2] k2.wstk[src2 + 1]
                    have hinv3 := unwatchShiftInv_step2 hinv2 h2 (by omega) v
                      (by rw [List.getElem?_eq_getElem (by omega), pack64_lo])
                      (by rw [List.getElem?_eq_getElem (by omega), pack64_hi])
                    have hj2 : BitVec.ofNat 64 src2 + 2 = BitVec.ofNat 64 (src2 + 2) ∧
                        BitVec.ofNat 64 dst2 + 2 = BitVec.ofNat 64 (dst2 + 2) := by
                      have h2_64 : (2 : BitVec 64).toNat = 2 := rfl
                      constructor <;> apply BitVec.eq_of_toNat_eq <;>
                        (simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, h2_64]
                         omega)
                    rw [hj2.1, hj2.2]
                    exact hJ1070 (src2 + 2, dst2 + 2, _) m ⟨⟨hinv3, hm⟩, by omega⟩
                  · have hno2 : off + sz < src2 + 2 := by
                      have h2_64 : (2 : BitVec 64).toNat = 2 := rfl
                      simp only [hmod_wv0, h1_64, hmod_wv1, h2_64] at hc
                      try rw [hsrc2_bv] at hc
                      rw [Nat.mod_eq_of_lt (show src2 + 2 < 2 ^ 64 by omega), ← hoff_sz_eq,
                        Nat.mod_eq_of_lt (show off + sz < 2 ^ 64 by omega)] at hc
                      omega
                    exact hJ1070 (src2, dst2, wstk2) m2 ⟨⟨hinv2, hm2⟩, hno2⟩
          · intro J610 hJ610
            have hinv0 : UnwatchShiftInv s.core s.core off sz q p q := by
              simpa [hqp] using unwatchShiftInv_init s.core hq_ge hq2
            have hq_bv : BitVec.ofNat 64 p - 2 = BitVec.ofNat 64 q := by
              have h2_64 : (2 : BitVec 64).toNat = 2 := rfl
              apply BitVec.eq_of_toNat_eq
              simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.reducePow, h2_64]
              rw [Nat.mod_eq_of_lt (show p < 2 ^ 64 by omega),
                Nat.mod_eq_of_lt (show q < 2 ^ 64 by omega)]
              omega
            have hp_bv : (BitVec.ofNat 64 p).toNat = p := Nat.mod_eq_of_lt (by omega)
            have hq_toNat : (BitVec.ofNat 64 q).toNat = q := Nat.mod_eq_of_lt (by omega)
            c0_step1; c0_step1
            · c0_step1
              · have hlt_p : p < off + sz := by
                  simp only [hmod_wv0, h1_64, hmod_wv1] at hc
                  try rw [hp_bv] at hc
                  rw [← hoff_sz_eq, Nat.mod_eq_of_lt (show off + sz < 2 ^ 64 by omega)] at hc
                  omega
                c0_go
                try rw [hq_bv] at hm
                try rw [hq_toNat] at hm
                simp only [hp_bv] at hm
                have hinv1 := unwatchShiftInv_step1 hinv0 hlt_p (by omega) s.core.wstk[p]
                  (List.getElem?_eq_getElem (by omega))
                have hj_pq : BitVec.ofNat 64 p + 1 = BitVec.ofNat 64 (p + 1) ∧
                    BitVec.ofNat 64 p - 2 + 1 = BitVec.ofNat 64 (q + 1) := by
                  rw [hq_bv]
                  have h1_64 : (1 : BitVec 64).toNat = 1 := rfl
                  constructor <;> apply BitVec.eq_of_toNat_eq <;>
                    (simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, h1_64]
                     omega)
                rw [hj_pq.1, hj_pq.2]
                exact hJ610 (p + 1, q + 1, _) m ⟨hinv1, by dsimp only; exact hm⟩
              · rw [hq_bv]; exact hJ610 (p, q, s.core.wstk) m ⟨hinv0, hm⟩
            · rw [hq_bv]; exact hJ610 (p, q, s.core.wstk) m ⟨hinv0, hm⟩
        · have hp64_sub1 : (BitVec.ofNat 64 p - 1).toNat = p - 1 := by
            simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.reducePow]
            rw [show (1 : BitVec 64).toNat = 1 from rfl,
              Nat.mod_eq_of_lt (show p < 2 ^ 64 by omega)]
            omega
          simp only [hp64_sub1]
          let w := s.core.wstk[p - 1]
          have hw_ne : w ≠ cref := by
            have h1_64 : (1 : BitVec 64).toNat = 1 := rfl
            have hp1 : (2 ^ 64 - 1 + p) % 2 ^ 64 = p - 1 := by omega
            simp only [h1_64, hp1] at hc
            exact hc
          have h31 : (w >>> 31).toNat ≤ 1 := by
            have := w.isLt
            simp [Nat.shiftRight_eq_div_pow]
            omega
          have hp2_bv : (BitVec.ofNat 64 p - (2 : BitVec 64)).toNat = p - 2 := by
            have h2_64 : (2 : BitVec 64).toNat = 2 := rfl
            rw [BitVec.toNat_sub, h2_64, BitVec.toNat_ofNat]
            simp only [Nat.reducePow]
            rw [Nat.mod_eq_of_lt (show p < 2 ^ 64 by omega)]
            omega
          have hw_sh : (BitVec.setWidth 64 (s.core.wstk[p - 1] >>> 31)).toNat =
              (w >>> 31).toNat := by
            have h_sh_lt : (w >>> 31).toNat < 2 ^ 64 := by omega
            change (BitVec.setWidth 64 (w >>> 31)).toNat = (w >>> 31).toNat
            rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt h_sh_lt]
          have hjump_eq :
              BitVec.ofNat 64 p - (2 : BitVec 64) +
                BitVec.setWidth 64 (s.core.wstk[p - 1] >>> 31) =
              BitVec.ofNat 64 (p - 2 + (w >>> 31).toNat) := by
            apply BitVec.eq_of_toNat_eq
            rw [BitVec.toNat_add, hp2_bv, hw_sh, BitVec.toNat_ofNat]
          rw [hjump_eq]
          exact ih _ m (by omega) ⟨rfl, by omega, by omega, fun F_cur hm' => by
            rcases watchBoundary_prev (hbd_impl F_cur hm') (by omega) with
              ⟨w0, hw0, hbin, hbd'⟩ | ⟨w0, cref', hle', hw0, hw1, hlg, hlt', hbd'⟩
            · have hweq : w0 = w := by
                have hs := List.getElem?_eq_getElem hwidx; rw [hw0] at hs; cases hs; rfl
              have h1_32 : (1#32 : BitVec 32).toNat = 1 := rfl
              rw [hweq] at hbin; rw [bv32_ushr31_of_bin hbin, h1_32]
              rw [show p - 2 + 1 = p - 1 by omega]; exact hbd'
            · have hweq : cref' = w := by
                have hs := List.getElem?_eq_getElem hwidx; rw [hw1] at hs; cases hs; rfl
              have h0_32 : (0#32 : BitVec 32).toNat = 0 := rfl
              rw [hweq] at hlt'; rw [bv32_ushr31_of_lt hlt', h0_32]
              rw [Nat.add_zero]; exact hbd'⟩
      · exact hQ s.core.wvec s.core.wstk s.core.wusable m hlen hlay (fun _ hm' => hm') hm

private theorem has_bin_slice_of_mode {F_cur : List (List Nat)} {k : FullCoreState} {l : Nat}
    (hw : ModeWatchesInv F_cur k) (hl : l < 2 * k.cur_vars) :
    WatchSliceOk F_cur k l (fullWatchOffCore k l) (fullWatchSizeCore k l) := by
  by_cases hdm : k.dense_mode = 0#64
  · simp only [ModeWatchesInv, hdm, ↓reduceIte] at hw; exact hw.slices l hl
  · simp only [ModeWatchesInv, hdm, ↓reduceIte] at hw; exact (hw.slices l hl).toWatchSliceOk

private theorem has_bin_hp_lt {c : FullCfg} {k : FullCoreState}
    (hl_k : FullCoreState.LengthsOk c k) {lit : Val i32} (_hlit : lit.toNat < 2 * k.cur_vars)
    {p : Nat} (hp : p ≤ fullWatchOffCore k lit.toNat + fullWatchSizeCore k lit.toNat)
    (hbounds : fullWatchOffCore k lit.toNat + fullWatchSizeCore k lit.toNat ≤ k.wlen)
    (h0 : 2 * lit.toNat % 2 ^ 64 < k.wvec.length)
    (h1 : (2 * lit.toNat + (1 : BitVec 64).toNat) % 2 ^ 64 < k.wvec.length)
    (hc : p % 2 ^ 64 < (k.wvec[2 * lit.toNat % 2 ^ 64].toNat +
      k.wvec[(2 * lit.toNat + (1 : BitVec 64).toNat) % 2 ^ 64].toNat) % 2 ^ 64) :
    p < fullWatchOffCore k lit.toNat + fullWatchSizeCore k lit.toNat := by
  have hcv := hl_k.cur_vars_le; have hwv := hl_k.wvec_len; have hwle := hl_k.wlen_le
  have hmax : c.max_vars < 2 * 2 ^ 28 := c.hmaxv
  have hwc : c.wcap < 2 * 2 ^ 28 := c.hwcap
  have h1_64 : (1 : BitVec 64).toNat = 1 := rfl
  have hmod0 : 2 * lit.toNat % 2 ^ 64 = 2 * lit.toNat := Nat.mod_eq_of_lt (by omega)
  have hmod1 : (2 * lit.toNat + 1) % 2 ^ 64 = 2 * lit.toNat + 1 := Nat.mod_eq_of_lt (by omega)
  have hw0 := k.wvec[2 * lit.toNat].isLt
  have hw1 := k.wvec[2 * lit.toNat + 1].isLt
  simp only [h1_64, hmod0, hmod1] at hc
  rw [Nat.mod_eq_of_lt (show p < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show k.wvec[2 * lit.toNat].toNat +
      k.wvec[2 * lit.toNat + 1].toNat < 2 ^ 64 by omega)] at hc
  simp only [fullWatchOffCore, fullWatchSizeCore,
    List.getElem?_eq_getElem (show 2 * lit.toNat < k.wvec.length by omega),
    List.getElem?_eq_getElem (show 2 * lit.toNat + 1 < k.wvec.length by omega), Option.getD_some]
  exact hc

private theorem has_bin_ret_true {F_cur : List (List Nat)} {n : Nat}
    {alit blit : Val i32} {m : Mem 64} {Q : Post [.bool]}
    (ha : alit.toNat < 2 * n) (hb : blit.toNat < 2 * n)
    (hne_eq : alit ≠ blit) (hne_neg : alit ≠ blit ^^^ 1#32)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [alit.toNat, blit.toNat]))
    (hQ : ∀ (ok : Bool), (ok = true →
      alit.toNat < 2 * n ∧ blit.toNat < 2 * n ∧ alit ≠ blit ∧ alit ≠ blit ^^^ 1#32 ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause [alit.toNat, blit.toNat])) → Q (ok, ()) m) :
    Q (true, ()) m :=
  hQ true (fun _ => ⟨ha, hb, hne_eq, hne_neg, hent⟩)

public theorem full_has_bin_wp (Γ : Env) (_hΓ : Γ.Sat Spec.specs)
    (a : Tup Val [i64, i32, i32]) (m : Mem 64) (Q : Post [.bool]) (X : XPost) :
    fullHasBinSpec a m Q X → Func.wp Γ full_has_bin_body a m Q X := by
  rcases a with ⟨h, alit, blit, ⟨⟩⟩
  rintro ⟨c, F0, F_cur, s, R, rfl, hlen, hf, hm, hQ⟩
  have hcv := hlen.core_ok.cur_vars_le; have hwv := hlen.core_ok.wvec_len
  have hwl := hlen.core_ok.wstk_len_arr; have hwl_le := hlen.core_ok.wlen_le
  have hcmax : c.max_vars < 2 * 2 ^ 28 := c.hmaxv
  have hcwcap : c.wcap < 2 * 2 ^ 28 := c.hwcap
  c0_go
  all_goals try exact hQ false (fun h => Bool.noConfusion h)
  · have ha : alit.toNat < 2 * s.core.cur_vars := by omega
    have hb : blit.toNat < 2 * s.core.cur_vars := by omega
    have hne_eq : alit ≠ blit := by assumption
    have hne_neg : alit ≠ blit ^^^ 1#32 := by assumption
    have hbounds := hf.watches.bounds alit.toNat ha
    have hslice := has_bin_slice_of_mode hf.watches ha
    let off := fullWatchOffCore s.core alit.toNat
    let sz := fullWatchSizeCore s.core alit.toNat
    apply wp_while_state1 (t := i64) (fun p : Nat => BitVec.ofNat 64 p) (fun p => off + sz - p)
      (fun p m' => m = m' ∧ off ≤ p ∧ p ≤ off + sz ∧ WatchBoundary s.core.wstk off sz p)
    · intro J920 hJ920; c0_go
      have hsh0 := (has_bin_shl1 hlen.core_ok ha).1
      rw [has_bin_init_eq hlen.core_ok ha (by rw [hsh0]; omega)]
      exact hJ920 off m ⟨rfl, Nat.le_refl _, by omega, WatchBoundary.here off sz⟩
    · intro J920 p m' hP ih
      rcases hP with ⟨rfl, hp_ge, hp_le, hbd⟩
      c0_go
      · have hp_lt : p < off + sz := has_bin_hp_lt hlen.core_ok ha hp_le hbounds _ _ hc
        rcases watchSliceOk_at_boundary hslice hbd hp_lt with
          ⟨w0, hw0, hbin, hent, hbd'⟩ | ⟨w0, _cref, _hq2, hw0, _hw1, hlg, _hlt, hbd'⟩
        · have hwidx : p < s.core.wstk.length := by omega
          have hweq : s.core.wstk[p] = w0 := by
            have hs := List.getElem?_eq_getElem hwidx; rw [hw0] at hs; cases hs; rfl
          c0_go
          · have hp64 : p % 2 ^ 64 = p := Nat.mod_eq_of_lt (by omega)
            simp only [hp64] at hc
            have hmatch : w0 &&& 0x7FFFFFFF#32 = blit := by rw [← hweq]; exact hc
            rw [show (w0 &&& 0x7FFFFFFF#32).toNat = blit.toNat from
              congrArg BitVec.toNat hmatch] at hent
            exact has_bin_ret_true ha hb hne_eq hne_neg hent hQ
          · rw [show BitVec.ofNat 64 p + 1 = BitVec.ofNat 64 (p + 1) by
              apply BitVec.eq_of_toNat_eq; simp]
            exact ih (p + 1) m (by omega) ⟨rfl, by omega, by omega, hbd'⟩
          · have hp64 : p % 2 ^ 64 = p := Nat.mod_eq_of_lt (by omega)
            simp only [hp64] at hc; rw [hweq] at hc; contradiction
        · have hwidx : p < s.core.wstk.length := by omega
          have hweq : s.core.wstk[p] = w0 := by
            have hs := List.getElem?_eq_getElem hwidx; rw [hw0] at hs; cases hs; rfl
          have hp64 : p % 2 ^ 64 = p := Nat.mod_eq_of_lt (by omega)
          have hlg_stk : s.core.wstk[p % 2 ^ 64] &&& 2147483648#32 = 0#32 := by
            simp only [hp64, hweq]; exact hlg
          c0_go
          all_goals first
          | (exfalso; contradiction)
          | (rw [show BitVec.ofNat 64 p + 2 = BitVec.ofNat 64 (p + 2) by
                apply BitVec.eq_of_toNat_eq; simp]
             exact ih (p + 2) m (by omega) ⟨rfl, by omega, by omega, hbd'⟩)
      · exact hQ false (fun h => Bool.noConfusion h)
  · have ha : alit.toNat < 2 * s.core.cur_vars := by omega
    have hb : blit.toNat < 2 * s.core.cur_vars := by omega
    have hne_eq : alit ≠ blit := by assumption
    have hne_neg : alit ≠ blit ^^^ 1#32 := by assumption
    have hbounds := hf.watches.bounds blit.toNat hb
    have hslice := has_bin_slice_of_mode hf.watches hb
    let off := fullWatchOffCore s.core blit.toNat
    let sz := fullWatchSizeCore s.core blit.toNat
    apply wp_while_state1 (t := i64) (fun p : Nat => BitVec.ofNat 64 p) (fun p => off + sz - p)
      (fun p m' => m = m' ∧ off ≤ p ∧ p ≤ off + sz ∧ WatchBoundary s.core.wstk off sz p)
    · intro J920 hJ920; c0_go
      have hsh0 := (has_bin_shl1 hlen.core_ok hb).1
      rw [has_bin_init_eq hlen.core_ok hb (by rw [hsh0]; omega)]
      exact hJ920 off m ⟨rfl, Nat.le_refl _, by omega, WatchBoundary.here off sz⟩
    · intro J920 p m' hP ih
      rcases hP with ⟨rfl, hp_ge, hp_le, hbd⟩
      c0_go
      · have hp_lt : p < off + sz := has_bin_hp_lt hlen.core_ok hb hp_le hbounds _ _ hc
        rcases watchSliceOk_at_boundary hslice hbd hp_lt with
          ⟨w0, hw0, hbin, hent, hbd'⟩ | ⟨w0, _cref, _hq2, hw0, _hw1, hlg, _hlt, hbd'⟩
        · have hwidx : p < s.core.wstk.length := by omega
          have hweq : s.core.wstk[p] = w0 := by
            have hs := List.getElem?_eq_getElem hwidx; rw [hw0] at hs; cases hs; rfl
          c0_go
          · have hp64 : p % 2 ^ 64 = p := Nat.mod_eq_of_lt (by omega)
            simp only [hp64] at hc
            have hmatch : w0 &&& 0x7FFFFFFF#32 = alit := by rw [← hweq]; exact hc
            rw [show (w0 &&& 0x7FFFFFFF#32).toNat = alit.toNat from
              congrArg BitVec.toNat hmatch] at hent
            exact has_bin_ret_true ha hb hne_eq hne_neg (entails_swap2 hent) hQ
          · rw [show BitVec.ofNat 64 p + 1 = BitVec.ofNat 64 (p + 1) by
              apply BitVec.eq_of_toNat_eq; simp]
            exact ih (p + 1) m (by omega) ⟨rfl, by omega, by omega, hbd'⟩
          · have hp64 : p % 2 ^ 64 = p := Nat.mod_eq_of_lt (by omega)
            simp only [hp64] at hc; rw [hweq] at hc; contradiction
        · have hwidx : p < s.core.wstk.length := by omega
          have hweq : s.core.wstk[p] = w0 := by
            have hs := List.getElem?_eq_getElem hwidx; rw [hw0] at hs; cases hs; rfl
          have hp64 : p % 2 ^ 64 = p := Nat.mod_eq_of_lt (by omega)
          have hlg_stk : s.core.wstk[p % 2 ^ 64] &&& 2147483648#32 = 0#32 := by
            simp only [hp64, hweq]; exact hlg
          c0_go
          all_goals first
          | (exfalso; contradiction)
          | (rw [show BitVec.ofNat 64 p + 2 = BitVec.ofNat 64 (p + 2) by
                apply BitVec.eq_of_toNat_eq; simp]
             exact ih (p + 2) m (by omega) ⟨rfl, by omega, by omega, hbd'⟩)
      · exact hQ false (fun h => Bool.noConfusion h)

end LeanQbe.T.Examples.Kissat.Proof.Watch
