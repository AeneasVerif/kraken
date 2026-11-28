/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Watch.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Watch.Helpers
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
using `Helpers` and `Wp5a` bridges. -/

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
  apply BitVec.eq_of_toNat_eq; have := x.isLt; simp [pack64_toNat]; omega

private theorem pack64_hi (x y : BitVec 32) : (pack64 x y >>> 32).setWidth 32 = y := by
  apply BitVec.eq_of_toNat_eq; have := x.isLt; have := y.isLt
  simp [pack64_toNat, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; omega

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
    rcases Nat.eq_or_lt_of_le (watchBoundary_le hbd).1 with rfl | hpq
    · exact Or.inl ⟨w0, hw, hbin, hent, watchBoundary_append_bin hbd (by omega) hw hbin⟩
    · have hbd' : WatchBoundary k.wstk (p + 1) rem' q := by
        cases hbd with
        | here => omega
        | bin _ _ rest => exact rest
        | large hw0' _ _ _ _ => rw [hw] at hw0'; cases hw0'; contradiction
      rcases ih hbd' (by omega) with
        ⟨w', hw', hbin', hent', hr'⟩ | ⟨w', c', hq2, hw0', hw1', hlg', hlt', hr'⟩
      · exact Or.inl ⟨w', hw', hbin', hent', WatchBoundary.bin hw hbin hr'⟩
      · exact Or.inr ⟨w', c', by omega, hw0', hw1', hlg', hlt', WatchBoundary.bin hw hbin hr'⟩
  | @large p rem' w0 cref hw0 hw1 hlg hlt _ hrest ih =>
    rcases Nat.eq_or_lt_of_le (watchBoundary_le hbd).1 with rfl | hpq
    · exact Or.inr ⟨w0, cref, by omega, hw0, hw1, hlg, hlt,
        watchBoundary_append_large hbd (by omega) hw0 hw1 hlg hlt⟩
    · have hbd' : WatchBoundary k.wstk (p + 2) rem' q := by
        cases hbd with
        | here => omega
        | bin hw' _ _ => rw [hw0] at hw'; cases hw'; contradiction
        | large _ _ _ _ rest => exact rest
      rcases ih hbd' (by omega) with
        ⟨w', hw', hbin', hent', hr'⟩ | ⟨w', c', hq2', hw0', hw1', hlg', hlt', hr'⟩
      · exact Or.inl ⟨w', hw', hbin', hent', WatchBoundary.large hw0 hw1 hlg hlt hr'⟩
      · exact Or.inr ⟨w', c', by omega, hw0', hw1', hlg', hlt',
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
  refine ⟨h0, by omega, by omega, by omega, by omega,
    fun idx hi => by rw [List.getElem?_set_ne (by omega), hlt_off idx hi],
    fun idx hi1 hi2 => by rw [List.getElem?_set_ne (by omega), hpre idx hi1 hi2],
    fun idx hi1 hi2 => by
      by_cases heq : idx = dst
      · subst heq; rw [List.getElem?_set_self (by omega), ← hw0, show idx + 2 = src by omega]
      · rw [List.getElem?_set_ne (Ne.symm heq), hsh idx hi1 (by omega)],
    fun idx hi1 hi2 => by rw [List.getElem?_set_ne (by omega), hpost idx (by omega) hi2],
    by simp [hwlen]⟩

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
  refine ⟨h0, by omega, by omega, by omega, by omega,
    fun idx hi => by
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega), hlt_off idx hi],
    fun idx hi1 hi2 => by
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega), hpre idx hi1 hi2],
    fun idx hi1 hi2 => by
      by_cases h_eq0 : idx = dst
      · subst h_eq0
        rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by simp [hwlen]; omega),
          ← hlo0, show idx + 2 = src by omega]
      · by_cases h_eq1 : idx = dst + 1
        · subst h_eq1
          rw [List.getElem?_set_self (by simp [hwlen]; omega), ← hhi0,
            show dst + 1 + 2 = src + 1 by omega]
        · rw [List.getElem?_set_ne (Ne.symm h_eq1), List.getElem?_set_ne (Ne.symm h_eq0),
            hsh idx hi1 (by omega)],
    fun idx hi1 hi2 => by
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
      exact hpost idx (by omega) hi2,
    by simp [hwlen]⟩

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
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega), hv1_lo]
  have h_s3 : ({ k with wstk := w1 } : FullCoreState).wstk[src + 3]? =
      some ((v1 >>> 32).setWidth 32) := by
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega), hv1_hi]
  simpa [w1, Nat.add_assoc] using unwatchShiftInv_step2 hk1 (by omega) hlen v1 h_s2 h_s3

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
  have hbounds := hlay.bounds lit hlit; have hwlen_le := hlen.core_ok.wlen_le
  have hw_len : s.core.wstk.length = c.wcap := hlen.core_ok.wstk_len_arr
  have hlen' : s'.LengthsOk c :=
    ⟨{ hlen.core_ok with
        wvec_len := by rw [List.length_set, hwv]
        wstk_len_arr := by rw [List.length_set, List.length_set, hwlen, hw_len] },
     hlen.scratch_ok⟩
  have hother : ∀ l < 2 * s.core.cur_vars, l ≠ lit → ∀ idx < fullWatchSizeCore s.core l,
      wstk'[fullWatchOffCore s.core l + idx]? =
        s.core.wstk[fullWatchOffCore s.core l + idx]? := by
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
  have hpre_lit : ∀ idx, off ≤ idx → idx < q → wstk'[idx]? = s.core.wstk[idx]? :=
    fun idx hi1 hi2 => by
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega), hpre idx hi1 hi2]
  have hsh_lit : ∀ idx, q ≤ idx → idx < off + sz - 2 → wstk'[idx]? = s.core.wstk[idx + 2]? :=
    fun idx hi1 hi2 => by
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega), hsh idx hi1 (by omega)]
  have hnosent : ∀ idx < sz - 2, wstk'[off + idx]? ≠ some 0xFFFFFFFF#32 := fun idx hidx => by
    by_cases hltq : off + idx < q
    · rw [hpre_lit (off + idx) (Nat.le_add_right off idx) hltq]
      exact hlay.no_sentinel lit hlit idx (by omega)
    · rw [hsh_lit (off + idx) (by omega) (by omega)]
      simpa [Nat.add_assoc] using hlay.no_sentinel lit hlit (idx + 2) (by omega)
  have hlay' := watchStackLayout_shrink hlay hlen.core_ok hlit (by omega) hother hnosent
    (wlen' := s.core.wlen) (wusable' := s.core.wusable + 2#64) (nb' := s.core.num_binary)
    (Nat.le_refl _)
  refine ⟨hlen', hlay', fun F_cur hmode => ?_⟩
  obtain ⟨hbd_q, w0, cref, hw0_q, hcref_q, hlg_q, hcref_lt⟩ := hbd_impl F_cur hmode
  have hwv1 : 2 * lit + 1 < s.core.wvec.length := by omega
  have hsz_lt : sz - 2 < 2 ^ 32 := by
    have : sz < 2 ^ 32 := (s.core.wvec[2 * lit + 1]?.getD 0#32).isLt; omega
  have hoff_lit : fullWatchOffCore s'.core lit = off :=
    congrArg BitVec.toNat (wvec_set_size_off_self hwv1 _)
  have hsz_lit : fullWatchSizeCore s'.core lit = sz - 2 := by
    dsimp only [fullWatchSizeCore, s', wvec']
    rw [wvec_set_size_sz_self hwv1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsz_lt]
  have hoth_ws : ∀ l, l ≠ lit →
      fullWatchOffCore s'.core l = fullWatchOffCore s.core l ∧
      fullWatchSizeCore s'.core l = fullWatchSizeCore s.core l := fun l hne => by
    have h := wvec_set_size_other (wvec := s.core.wvec) hne (BitVec.ofNat 32 (sz - 2))
    exact ⟨congrArg BitVec.toNat h.1, congrArg BitVec.toNat h.2⟩
  have hother_m : ∀ l, l < 2 * s.core.cur_vars → l ≠ lit → ∀ idx,
      fullWatchOffCore s.core l ≤ idx →
      idx < fullWatchOffCore s.core l + fullWatchSizeCore s.core l →
      s'.core.wstk[idx]? = s.core.wstk[idx]? := fun l hl heq idx hi1 hi2 => by
    have h := hother l hl heq (idx - fullWatchOffCore s.core l) (by omega)
    rw [Nat.add_sub_cancel' hi1] at h; exact h
  by_cases hdm : s.core.dense_mode = 0#64
  · rw [modeWatchesInv_eq_watches hdm] at hmode
    rw [modeWatchesInv_eq_watches (by simpa [s'] using hdm)]
    refine WatchesInv.of_slices hlay'.bounds hlay'.pos_off hlay'.disjoint fun l hl => ?_
    by_cases heq : l = lit
    · subst heq; rw [hoff_lit, hsz_lit]
      exact watchSliceOk_erase (k := s.core) (k' := s'.core) (Nat.le_refl _) (fun r hr => hr)
        (hmode.slices l hl) hbd_q (by omega)
        (Or.inr ⟨rfl, w0, cref, hw0_q, hcref_q, hlg_q, hcref_lt⟩) hpre_lit hsh_lit
    · rw [(hoth_ws l heq).1, (hoth_ws l heq).2]
      exact (hmode.slices l hl).mono (k := s.core) (k' := s'.core)
        (Std.Sat.CNF.entails_refl (cnfOfClauses F_cur)) (Nat.le_refl _) (fun r hr => hr)
        (hother_m l hl heq)
  · rw [modeWatchesInv_eq_dense hdm] at hmode
    rw [modeWatchesInv_eq_dense (by simpa [s'] using hdm)]
    refine DenseWatchesInv.of_slices hlay'.bounds hlay'.pos_off hlay'.disjoint fun l hl => ?_
    by_cases heq : l = lit
    · subst heq; rw [hoff_lit, hsz_lit]
      exact denseWatchSliceOk_erase (k := s.core) (k' := s'.core) (Nat.le_refl _) (fun r hr => hr)
        (hmode.slices l hl) hbd_q (by omega)
        (Or.inr ⟨rfl, w0, cref, hw0_q, hcref_q, hlg_q, hcref_lt⟩) hpre_lit hsh_lit
    · rw [(hoth_ws l heq).1, (hoth_ws l heq).2]
      exact (hmode.slices l hl).mono (k := s.core) (k' := s'.core)
        (Std.Sat.CNF.entails_refl (cnfOfClauses F_cur)) (Nat.le_refl _) (fun r hr => hr)
        (hother_m l hl heq)

public theorem full_watch_pop_c0_wp (Γ : Env) (_hΓ : Γ.Sat Spec.specs)
    (a : Tup Val [i64, i32, i32]) (m : Mem 64) (Q : Post []) (X : XPost) :
    Spec.fullWatchPopC0Spec a m Q X → Func.wp Γ full_watch_pop_c0_body a m Q X := by
  rcases a with ⟨h, lit, cnt, ⟨⟩⟩
  rintro ⟨c, s, R, rfl, hlen, hlay, hlit, hcnt0, hcnt_le, hm, hQ⟩
  have hcv := hlen.core_ok.cur_vars_le; have hwv := hlen.core_ok.wvec_len
  have hwl := hlen.core_ok.wstk_len_arr; have hbounds := hlay.bounds lit.toNat hlit
  have hwl_le := hlen.core_ok.wlen_le
  have hcmax := c.hmaxv; have hcwcap := c.hwcap; unfold dimacsBound at hcmax hcwcap
  obtain ⟨hwv0, hwv1, h0_lt, hw1_idx, hm0_, hm1_, hmod_wv0, hmod_wv⟩ :=
    wvec_shl1_lt hlen.core_ok hlit
  have hget0 : s.core.wvec[2 * lit.toNat % 2 ^ 64]'hm0_ = s.core.wvec[2 * lit.toNat]'hwv0 :=
    list_getElem_congr hm0_ hmod_wv0
  have hget1 : s.core.wvec[(2 * lit.toNat + 1) % 2 ^ 64]'hm1_ =
      s.core.wvec[2 * lit.toNat + 1]'hwv1 :=
    list_getElem_congr hm1_ hmod_wv
  have h1_64 : (1 : BitVec 64).toNat = 1 := rfl
  c0_go
  · exfalso; simp only [h1_64] at hc; rw [hget1] at hc
    simp only [fullWatchSize, fullWatchSizeCore, List.getElem?_eq_getElem hwv1,
      Option.getD_some] at hcnt_le
    omega
  · exfalso
    have hw0 := s.core.wvec[2 * lit.toNat].isLt
    have hw1 := s.core.wvec[2 * lit.toNat + 1].isLt
    simp only [h1_64] at hc; rw [hget0, hget1] at hc
    rw [Nat.mod_eq_of_lt (by omega : s.core.wlen < 2 ^ 64), Nat.mod_eq_of_lt (by omega)] at hc
    simp only [fullWatchOffCore, fullWatchSizeCore, List.getElem?_eq_getElem hwv0,
      List.getElem?_eq_getElem hwv1, Option.getD_some] at hbounds; omega
  let off := fullWatchOffCore s.core lit.toNat
  let sz := fullWatchSizeCore s.core lit.toNat
  let Inv : Nat → Mem 64 → Prop := fun i m' =>
    sz - cnt.toNat ≤ i ∧ i ≤ sz ∧
    ∃ wstk' : List (BitVec 32), wstk'.length = s.core.wstk.length ∧
      (∀ idx, idx < off + (sz - cnt.toNat) → wstk'[idx]? = s.core.wstk[idx]?) ∧
      (∀ idx, off + i ≤ idx → idx < s.core.wstk.length → wstk'[idx]? = s.core.wstk[idx]?) ∧
      (FullMem c { s with core := { s.core with wstk := wstk' } } ⋆ R) m'
  apply wp_while_state1 (t := i64) (fun i : Nat => BitVec.ofNat 64 i) (fun i => sz - i) Inv
  · intro J hJ; c0_go
    have hinit : BitVec.setWidth 64 (s.core.wvec[(BitVec.setWidth 64 lit <<< 1 + 1).toNat]) -
        BitVec.setWidth 64 cnt = BitVec.ofNat 64 (sz - BitVec.toNat cnt) := by
      have hg1 : s.core.wvec[(BitVec.setWidth 64 lit <<< 1 + 1).toNat] =
          s.core.wvec[2 * lit.toNat + 1] := list_getElem_congr hw1_idx (bv64_shl1_add1_lit lit)
      rw [hg1]; apply BitVec.eq_of_toNat_eq
      simp only [fullWatchSize, fullWatchSizeCore, List.getElem?_eq_getElem hwv1,
        Option.getD_some] at hcnt_le
      have := s.core.wvec[2 * lit.toNat + 1].isLt; have := cnt.isLt
      have hle_bv : BitVec.setWidth 64 cnt ≤
          BitVec.setWidth 64 s.core.wvec[2 * lit.toNat + 1] := by
        rw [BitVec.le_def, BitVec.toNat_setWidth, BitVec.toNat_setWidth,
          Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; exact hcnt_le
      rw [BitVec.toNat_sub_of_le hle_bv, BitVec.toNat_setWidth, BitVec.toNat_setWidth,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)]
      simp only [sz, fullWatchSizeCore, List.getElem?_eq_getElem hwv1, Option.getD_some]
    rw [hinit]
    exact hJ _ m ⟨Nat.le_refl _, by omega, s.core.wstk, rfl, fun _ _ => rfl, fun _ _ _ => rfl, hm⟩
  · intro J i m' ⟨hi1, hi2, wstk', hwlen', hpre, hpost, hm'⟩ ih
    have hsz_lt64 : sz < 2 ^ 64 := by
      have := s.core.wvec[2 * lit.toNat + 1].isLt
      simp only [sz, fullWatchSizeCore, List.getElem?_eq_getElem hwv1, Option.getD_some]; omega
    c0_go
    · have hlt : i < sz := by
        simp only [h1_64] at hc; rw [hget1] at hc; rw [Nat.mod_eq_of_lt (by omega)] at hc
        simp only [sz, fullWatchSizeCore, List.getElem?_eq_getElem hwv1, Option.getD_some]; omega
      have hidx : off + i < wstk'.length := by omega
      c0_go
      · have hget0' : s.core.wvec[(BitVec.setWidth 64 lit <<< 1).toNat]'h0_lt =
            s.core.wvec[2 * lit.toNat] := list_getElem_congr h0_lt (bv64_shl1_lit lit)
        have hidx_eq : (BitVec.setWidth 64
              (s.core.wvec[(BitVec.setWidth 64 lit <<< 1).toNat]'h0_lt) +
              BitVec.ofNat 64 i).toNat = off + i := by
          rw [hget0']; have := s.core.wvec[2 * lit.toNat].isLt
          simp only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow,
            off, fullWatchOffCore, List.getElem?_eq_getElem hwv0, Option.getD_some]
          rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
            Nat.mod_eq_of_lt (by omega)]
        rw [hidx_eq] at hm
        rw [bv64_ofNat_add1 (by omega)]
        exact ih (i + 1) _ (by omega) ⟨by omega, by omega, wstk'.set (off + i) 0xFFFFFFFF#32,
          by simp [hwlen'],
          fun idx hlt' => by rw [List.getElem?_set_ne (by omega), hpre idx hlt'],
          fun idx hle' hi_lt => by rw [List.getElem?_set_ne (by omega), hpost idx (by omega) hi_lt],
          hm⟩
    · have hieq : i = sz := by
        simp only [h1_64] at hc; rw [hget1] at hc; rw [Nat.mod_eq_of_lt (by omega)] at hc
        simp only [sz, fullWatchSizeCore, List.getElem?_eq_getElem hwv1,
          Option.getD_some] at hi2 ⊢; omega
      subst hieq; c0_go; c0_go
      have hsz_lt : sz - cnt.toNat < 2 ^ 32 := by
        have : sz < 2 ^ 32 := (s.core.wvec[2 * lit.toNat + 1]?.getD 0#32).isLt; omega
      have hw1_val_eq : BitVec.setWidth 32
          (BitVec.setWidth 64 (s.core.wvec[(BitVec.setWidth 64 lit <<< 1 + 1).toNat]'hw1_idx) -
            BitVec.setWidth 64 cnt) = BitVec.ofNat 32 (sz - cnt.toNat) := by
        have hg1 : s.core.wvec[(BitVec.setWidth 64 lit <<< 1 + 1).toNat]'hw1_idx =
            s.core.wvec[2 * lit.toNat + 1]'hwv1 :=
          list_getElem_congr hw1_idx (bv64_shl1_add1_lit lit)
        rw [hg1]; apply BitVec.eq_of_toNat_eq
        have hlt_c := cnt.isLt; have := s.core.wvec[2 * lit.toNat + 1].isLt
        simp only [fullWatchSize, fullWatchSizeCore, List.getElem?_eq_getElem hwv1,
          Option.getD_some] at hcnt_le
        have hle_bv : BitVec.setWidth 64 cnt ≤
            BitVec.setWidth 64 (s.core.wvec[2 * lit.toNat + 1]'hwv1) := by
          rw [BitVec.le_def, BitVec.toNat_setWidth, BitVec.toNat_setWidth,
            Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; exact hcnt_le
        rw [BitVec.toNat_setWidth, BitVec.toNat_sub_of_le hle_bv, BitVec.toNat_setWidth,
          BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
          Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        simp only [sz, fullWatchSizeCore, List.getElem?_eq_getElem hwv1, Option.getD_some]
        rw [Nat.mod_eq_of_lt (by omega)]
      rw [hw1_val_eq, bv64_shl1_add1_lit] at hm
      exact pop_tail_fin hlen hlay hlit hcnt_le hwlen' hpre hpost hwv1 hsz_lt hm hQ

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

private theorem bv64_ofNat_add_ofNat (x k : Nat) (h : x + k < 2 ^ 64) :
    BitVec.ofNat 64 x + OfNat.ofNat k = BitVec.ofNat 64 (x + k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  change (x % 2 ^ 64 + k % 2 ^ 64) % 2 ^ 64 = (x + k) % 2 ^ 64
  rw [Nat.mod_eq_of_lt (by omega : x < 2 ^ 64), Nat.mod_eq_of_lt (by omega : k < 2 ^ 64),
    Nat.mod_eq_of_lt h]

local macro "unwatch_src_le " hbv:term : tactic =>
  let h1 := Lean.mkIdent `h1_64; let h4 := Lean.mkIdent `h4_64; let h2 := Lean.mkIdent `h2_64
  let hg0 := Lean.mkIdent `hget0; let hg1 := Lean.mkIdent `hget1
  let ho := Lean.mkIdent `hoff_sz_eq; let hc := Lean.mkIdent `hc
  `(tactic| (
    simp only [$h1:ident, $h4:ident, $h2:ident] at $hc:ident
    rw [$hg0:ident, $hg1:ident] at $hc:ident
    try rw [$hbv:term] at $hc:ident
    rw [Nat.mod_eq_of_lt (by omega : _ < 2 ^ 64), ← $ho:ident,
      Nat.mod_eq_of_lt (by omega : _ < 2 ^ 64)] at $hc:ident
    omega))

public theorem full_unwatch_large_wp (Γ : Env) (_hΓ : Γ.Sat Spec.specs)
    (a : Tup Val [i64, i32, i32]) (m : Mem 64) (Q : Post []) (X : XPost) :
    fullUnwatchLargeSpec a m Q X → Func.wp Γ full_unwatch_large_body a m Q X := by
  rcases a with ⟨h, lit, cref, ⟨⟩⟩
  rintro ⟨c, s, R, rfl, hlen, hlay, hm, hQ⟩
  have hcv := hlen.core_ok.cur_vars_le; have hwv := hlen.core_ok.wvec_len
  have hwl := hlen.core_ok.wstk_len_arr; have hwl_le := hlen.core_ok.wlen_le
  have hcmax := c.hmaxv; have hcwcap := c.hwcap; unfold dimacsBound at hcmax hcwcap
  c0_go
  · exact hQ s.core.wvec s.core.wstk s.core.wusable m hlen hlay (fun _ hm' => hm') hm
  · exact hQ s.core.wvec s.core.wstk s.core.wusable m hlen hlay (fun _ hm' => hm') hm
  · exact hQ s.core.wvec s.core.wstk s.core.wusable m hlen hlay (fun _ hm' => hm') hm
  · have hlit : lit.toNat < 2 * s.core.cur_vars := by omega
    have hcref_bin0 : cref &&& 0x80000000#32 = 0#32 := by assumption
    have hbounds := hlay.bounds lit.toNat hlit
    obtain ⟨hwv0, hwv1, hwv0_bv, hwv1_bv, hj0, hj1, hmod_wv0, hmod_wv1⟩ :=
      wvec_shl1_lt hlen.core_ok hlit
    have hget0 : s.core.wvec[2 * lit.toNat % 2 ^ 64]'hj0 =
        s.core.wvec[2 * lit.toNat]'hwv0 := list_getElem_congr hj0 hmod_wv0
    have hget1 : s.core.wvec[(2 * lit.toNat + 1) % 2 ^ 64]'hj1 =
        s.core.wvec[2 * lit.toNat + 1]'hwv1 := list_getElem_congr hj1 hmod_wv1
    let off := fullWatchOffCore s.core lit.toNat
    let sz := fullWatchSizeCore s.core lit.toNat
    have hsz2 : 2 ≤ sz := by
      have h1_64 : (1 : BitVec 64).toNat = 1 := rfl
      have h2_64 : (2 : BitVec 64).toNat = 2 := rfl
      simp only [h1_64, h2_64] at hc; rw [hget1] at hc
      simp only [sz, fullWatchSizeCore, List.getElem?_eq_getElem hwv1, Option.getD_some]; omega
    apply wp_while_state1 (fun p : Nat => BitVec.ofNat 64 p) (fun p => p - off)
      (fun p m' => m = m' ∧ off ≤ p ∧ p ≤ off + sz ∧
        (∀ F_cur, ModeWatchesInv F_cur s.core → WatchBoundary s.core.wstk off sz p))
    · intro J hJ; c0_go
      have hj_eq : BitVec.setWidth 64 s.core.wvec[(BitVec.setWidth 64 lit <<< 1).toNat] +
          BitVec.setWidth 64 s.core.wvec[(BitVec.setWidth 64 lit <<< 1 + 1).toNat] =
          BitVec.ofNat 64 (off + sz) := by
        apply BitVec.eq_of_toNat_eq
        rw [wvec_end_add_eq hlen.core_ok hlit hwv0_bv hwv1_bv, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega)]
      rw [hj_eq]
      exact hJ (off + sz) m ⟨rfl, by omega, Nat.le_refl _, fun F_cur hm' => by
        by_cases hdm : s.core.dense_mode = 0#64
        · rw [modeWatchesInv_eq_watches hdm] at hm'
          exact watchSliceOk_boundary_end (hm'.slices lit.toNat hlit)
        · rw [modeWatchesInv_eq_dense hdm] at hm'
          exact denseWatchSliceOk_boundary_end (hm'.slices lit.toNat hlit)⟩
    · intro J p m' ⟨rfl, hp_ge, hp_le, hbd_impl⟩ ih
      have h1_64 : (1 : BitVec 64).toNat = 1 := rfl
      have h2_64 : (2 : BitVec 64).toNat = 2 := rfl
      have h4_64 : (4 : BitVec 64).toNat = 4 := rfl
      c0_step1; c0_step1
      · have hp2 : off + 2 ≤ p := by
          have := s.core.wvec[2 * lit.toNat].isLt
          simp only [hmod_wv0, h2_64] at hc; rw [Nat.mod_eq_of_lt (by omega)] at hc
          simp only [off, fullWatchOffCore, List.getElem?_eq_getElem hwv0,
            Option.getD_some] at ⊢; omega
        have hwidx : p - 1 < s.core.wstk.length := by omega
        c0_step1; c0_step1
        · let q := p - 2
          have hq_ge : off ≤ q := by omega
          have hq2 : q + 2 ≤ off + sz := by omega
          have hw_eq : s.core.wstk[p - 1] = cref := by
            have hp1 : (2 ^ 64 - 1 + p) % 2 ^ 64 = p - 1 := by omega
            simpa [h1_64, hp1] using hc
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
              exact absurd hcref_bin0 (hweq ▸ hbin)
            · exact ⟨hr', w0, cref', hw0,
                by simpa [q, show p - 2 + 1 = p - 1 by omega] using hw1, hlg, hlt'⟩
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
            c0_step1
            apply wp_while_state proj2 (fun st => off + sz - st.1) SInv
            · intro J830 hJ830; c0_step1; exact hJ830 _ m1 ⟨hinv1, hm1⟩
            · intro J830 ⟨src2, dst2, wstk2⟩ m2 ⟨hinv2, hm2⟩ ih830
              dsimp only [proj2] at hinv2 hm2 ih830 ⊢
              let k2 : FullCoreState := { s.core with wstk := wstk2 }
              have hlt_src2 := hinv2.2.2.2.2.1
              have hwlen2 : wstk2.length = s.core.wstk.length := hinv2.2.2.2.2.2.2.2.2.2
              have hsrc2_bv : (BitVec.ofNat 64 src2).toNat = src2 := Nat.mod_eq_of_lt (by omega)
              have hdst2_src2 : dst2 + 2 = src2 := hinv2.2.2.1
              have hdst2_bv : (BitVec.ofNat 64 dst2).toNat = dst2 := Nat.mod_eq_of_lt (by omega)
              c0_step1; c0_step1
              · have h4 : src2 + 4 ≤ off + sz := by unwatch_src_le hsrc2_bv
                have hsrc2_p2 : (BitVec.ofNat 64 src2 + 2).toNat = src2 + 2 := by
                  simp [BitVec.toNat_add, hsrc2_bv, Nat.mod_eq_of_lt (by omega : src2 + 2 < 2 ^ 64)]
                have hdst2_p2 : (BitVec.ofNat 64 dst2 + 2).toNat = dst2 + 2 := by
                  simp [BitVec.toNat_add, hdst2_bv, Nat.mod_eq_of_lt (by omega : dst2 + 2 < 2 ^ 64)]
                simp only [BitVec.add_zero]
                have h_s2_0 : src2 + 1 < wstk2.length := by omega
                have h_d2_0 : dst2 + 1 < wstk2.length := by omega
                c0_go
                have h_s2 : src2 + 3 < wstk2.length := by omega
                have h_d2 : dst2 + 3 < wstk2.length := by omega
                c0_go
                simp only [hsrc2_bv, hdst2_bv] at hm
                let v0 := pack64 k2.wstk[src2] k2.wstk[src2 + 1]
                let v1 := pack64 k2.wstk[src2 + 2] k2.wstk[src2 + 3]
                have h_l2 : ((wstk2.set dst2 (v0.setWidth 32)).set (dst2 + 1)
                    ((v0 >>> 32).setWidth 32))[src2 + 2]'(by simp [hwlen2]; omega) =
                    wstk2[src2 + 2] := by
                  rw [List.getElem_set_ne (by omega), List.getElem_set_ne (by omega)]
                have h_l3 : ((wstk2.set dst2 (v0.setWidth 32)).set (dst2 + 1)
                    ((v0 >>> 32).setWidth 32))[src2 + 3]'(by simp [hwlen2]; omega) =
                    wstk2[src2 + 3] := by
                  rw [List.getElem_set_ne (by omega), List.getElem_set_ne (by omega)]
                dsimp only [v0, k2] at h_l2 h_l3; try simp only [h_l2, h_l3] at hm
                have hinv2' := unwatchShiftInv_step4 hinv2 h4 (by omega) v0 v1
                  (by rw [List.getElem?_eq_getElem (by simp [hwlen2]; omega), pack64_lo])
                  (by rw [List.getElem?_eq_getElem (by simp [hwlen2]; omega), pack64_hi])
                  (by rw [List.getElem?_eq_getElem (by simp [hwlen2]; omega), pack64_lo])
                  (by rw [List.getElem?_eq_getElem (by simp [hwlen2]; omega), pack64_hi])
                rw [bv64_ofNat_add_ofNat src2 4 (by omega),
                  bv64_ofNat_add_ofNat dst2 4 (by omega)]
                exact ih830 (src2 + 4, dst2 + 4, _) _ (by omega) ⟨hinv2', hm⟩
              · have hno4 : ¬ (src2 + 4 ≤ off + sz) := by unwatch_src_le hsrc2_bv
                let SInv1070 : Nat × Nat × List (BitVec 32) → Mem 64 → Prop := fun st m1 =>
                  SInv st m1 ∧ off + sz < st.1 + 2
                apply wp_join_state proj2 SInv1070
                · intro J1070 ⟨src3, dst3, wstk3⟩ m3 ⟨⟨hinv3, hm3⟩, hlt_tail⟩
                  clear hm2
                  dsimp only [proj2] at hinv3 hm3 hlt_tail ⊢
                  have hlt_src3 := hinv3.2.2.2.2.1
                  have hwlen3 : wstk3.length = s.core.wstk.length := hinv3.2.2.2.2.2.2.2.2.2
                  apply wp_join0 (fun m4 => ∃ wstk4,
                    UnwatchShiftInv s.core { s.core with wstk := wstk4 } off sz q
                      (off + sz) (off + sz - 2) ∧
                    (FullMem c { s with core := { s.core with wstk := wstk4 } } ⋆ R) m4)
                  · intro J1290 m4 ⟨wstk4, hinv4, hm4⟩
                    have hwlen4 : wstk4.length = s.core.wstk.length := hinv4.2.2.2.2.2.2.2.2.2
                    obtain ⟨hm2_eq, hm1_eq, hw1_val, hm2_lt, hm1_lt⟩ :=
                      unwatch_tail_bv hlen.core_ok hlit hbounds hsz2 (wstk_len := wstk4.length)
                        (by rw [hwlen4, hwl]; omega)
                    c0_go
                    rw [hm2_eq, hm1_eq, hw1_val, bv64_shl1_add1_lit] at hm
                    have ht_fin :=
                      full_unwatch_tail_inv hlen hlay hlit hq_ge hq2 rfl hinv4 hbd_q_impl
                    exact hQ _ _ _ _ ht_fin.1 ht_fin.2.1 ht_fin.2.2 hm
                  · intro J1290 hJ1290
                    have hsrc3_bv : (BitVec.ofNat 64 src3).toNat = src3 :=
                      Nat.mod_eq_of_lt (by omega)
                    have hdst3_le : dst3 ≤ off + sz := by have := hinv3.2.2.1; omega
                    have hdst3_bv : (BitVec.ofNat 64 dst3).toNat = dst3 :=
                      Nat.mod_eq_of_lt (by omega)
                    c0_step1; c0_step1
                    · have h1 : src3 < off + sz := by unwatch_src_le hsrc3_bv
                      have heq1 : src3 + 1 = off + sz := by omega
                      have hs3_lt : src3 < wstk3.length := by have := hinv3.2.2.1; omega
                      have hd3_lt : dst3 < wstk3.length := by have := hinv3.2.2.1; omega
                      c0_go
                      try rw [hdst3_bv] at hm
                      simp only [hsrc3_bv] at hm
                      have hinv4 := unwatchShiftInv_step1 hinv3 h1 (by omega) wstk3[src3]
                        (List.getElem?_eq_getElem (by omega))
                      have hdst1 : dst3 + 1 = off + sz - 2 := by have := hinv3.2.2.1; omega
                      exact hJ1290 _ ⟨_, by simpa [heq1, hdst1] using hinv4, hm⟩
                    · have heq0 : src3 = off + sz := by unwatch_src_le hsrc3_bv
                      have hdst0 : dst3 = off + sz - 2 := by have := hinv3.2.2.1; omega
                      exact hJ1290 _ ⟨wstk3, by simpa [heq0, hdst0] using hinv3, hm3⟩
                · intro J1070 hJ1070; c0_step1; c0_step1
                  · have h2 : src2 + 2 ≤ off + sz := by unwatch_src_le hsrc2_bv
                    have hs2_lt : src2 < wstk2.length := by have := hinv2.2.2.1; omega
                    have hd2_lt : dst2 < wstk2.length := by have := hinv2.2.2.1; omega
                    have h_s2 : src2 + 1 < wstk2.length := by omega
                    have h_d2 : dst2 + 1 < wstk2.length := by omega
                    simp only [BitVec.add_zero]; c0_go
                    simp only [hsrc2_bv, hdst2_bv] at hm
                    let v := pack64 k2.wstk[src2] k2.wstk[src2 + 1]
                    have hinv3 := unwatchShiftInv_step2 hinv2 h2 (by omega) v
                      (by rw [List.getElem?_eq_getElem (by omega), pack64_lo])
                      (by rw [List.getElem?_eq_getElem (by omega), pack64_hi])
                    rw [bv64_ofNat_add_ofNat src2 2 (by omega),
                      bv64_ofNat_add_ofNat dst2 2 (by omega)]
                    exact hJ1070 (src2 + 2, dst2 + 2, _) m ⟨⟨hinv3, hm⟩, by omega⟩
                  · have hno2 : off + sz < src2 + 2 := by unwatch_src_le hsrc2_bv
                    exact hJ1070 (src2, dst2, wstk2) m2 ⟨⟨hinv2, hm2⟩, hno2⟩
          · intro J610 hJ610
            have hinv0 : UnwatchShiftInv s.core s.core off sz q p q := by
              simpa [show q + 2 = p by omega] using unwatchShiftInv_init s.core hq_ge hq2
            have hq_bv : BitVec.ofNat 64 p - 2 = BitVec.ofNat 64 q := by
              apply BitVec.eq_of_toNat_eq
              simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.reducePow, h2_64,
                Nat.mod_eq_of_lt (by omega : p < 2 ^ 64),
                Nat.mod_eq_of_lt (by omega : q < 2 ^ 64)]; omega
            have hp_bv : (BitVec.ofNat 64 p).toNat = p := Nat.mod_eq_of_lt (by omega)
            have hq_toNat : (BitVec.ofNat 64 q).toNat = q := Nat.mod_eq_of_lt (by omega)
            c0_step1; c0_step1
            · c0_step1
              · have hlt_p : p < off + sz := by unwatch_src_le hp_bv
                c0_go; try rw [hq_bv] at hm; try rw [hq_toNat] at hm; simp only [hp_bv] at hm
                have hinv1 := unwatchShiftInv_step1 hinv0 hlt_p (by omega) s.core.wstk[p]
                  (List.getElem?_eq_getElem (by omega))
                rw [bv64_ofNat_add1 (by omega), hq_bv, bv64_ofNat_add1 (by omega)]
                exact hJ610 (p + 1, q + 1, _) m ⟨hinv1, hm⟩
              · rw [hq_bv]; exact hJ610 (p, q, s.core.wstk) m ⟨hinv0, hm⟩
            · rw [hq_bv]; exact hJ610 (p, q, s.core.wstk) m ⟨hinv0, hm⟩
        · have hp64_sub1 : (BitVec.ofNat 64 p - 1).toNat = p - 1 := by
            simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.reducePow, h1_64,
              Nat.mod_eq_of_lt (by omega : p < 2 ^ 64)]; omega
          simp only [hp64_sub1]
          let w := s.core.wstk[p - 1]
          have hw_ne : w ≠ cref := by
            have hp1 : (2 ^ 64 - 1 + p) % 2 ^ 64 = p - 1 := by omega
            simpa [h1_64, hp1] using hc
          have h31 : (w >>> 31).toNat ≤ 1 := by
            have := w.isLt; simp [Nat.shiftRight_eq_div_pow]; omega
          have hp2_bv : (BitVec.ofNat 64 p - (2 : BitVec 64)).toNat = p - 2 := by
            rw [BitVec.toNat_sub, h2_64, BitVec.toNat_ofNat,
              Nat.mod_eq_of_lt (by omega : p < 2 ^ 64)]; omega
          have hw_sh : (BitVec.setWidth 64 (s.core.wstk[p - 1] >>> 31)).toNat =
              (w >>> 31).toNat := by
            change (BitVec.setWidth 64 (w >>> 31)).toNat = (w >>> 31).toNat
            rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
          have hjump_eq : BitVec.ofNat 64 p - (2 : BitVec 64) +
              BitVec.setWidth 64 (s.core.wstk[p - 1] >>> 31) =
              BitVec.ofNat 64 (p - 2 + (w >>> 31).toNat) := by
            apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add, hp2_bv, hw_sh, BitVec.toNat_ofNat]
          rw [hjump_eq]
          exact ih _ m (by omega) ⟨rfl, by omega, by omega, fun F_cur hm' => by
            rcases watchBoundary_prev (hbd_impl F_cur hm') (by omega) with
              ⟨w0, hw0, hbin, hbd'⟩ | ⟨w0, cref', _, hw0, hw1, _, hlt', hbd'⟩
            · have hweq : w0 = w := by
                have hs := List.getElem?_eq_getElem hwidx; rw [hw0] at hs; cases hs; rfl
              rw [bv32_ushr31_of_bin (hweq ▸ hbin), show (1#32 : BitVec 32).toNat = 1 from rfl,
                show p - 2 + 1 = p - 1 by omega]; exact hbd'
            · have hweq : cref' = w := by
                have hs := List.getElem?_eq_getElem hwidx; rw [hw1] at hs; cases hs; rfl
              rw [bv32_ushr31_of_lt (hweq ▸ hlt'), show (0#32 : BitVec 32).toNat = 0 from rfl,
                Nat.add_zero]; exact hbd'⟩
      · exact hQ s.core.wvec s.core.wstk s.core.wusable m hlen hlay (fun _ hm' => hm') hm

private theorem has_bin_hp_lt {c : FullCfg} {k : FullCoreState}
    (hl_k : FullCoreState.LengthsOk c k) {lit : Val i32}
    {p : Nat} (hp : p ≤ fullWatchOffCore k lit.toNat + fullWatchSizeCore k lit.toNat)
    (hbounds : fullWatchOffCore k lit.toNat + fullWatchSizeCore k lit.toNat ≤ k.wlen)
    (h0 : 2 * lit.toNat % 2 ^ 64 < k.wvec.length)
    (h1 : (2 * lit.toNat + (1 : BitVec 64).toNat) % 2 ^ 64 < k.wvec.length)
    (hc : p % 2 ^ 64 < (k.wvec[2 * lit.toNat % 2 ^ 64].toNat +
      k.wvec[(2 * lit.toNat + (1 : BitVec 64).toNat) % 2 ^ 64].toNat) % 2 ^ 64) :
    p < fullWatchOffCore k lit.toNat + fullWatchSizeCore k lit.toNat := by
  have hcv := hl_k.cur_vars_le; have hwv := hl_k.wvec_len; have hwle := hl_k.wlen_le
  have hmax := c.hmaxv; have hwc := c.hwcap; unfold dimacsBound at hmax hwc
  have hmod0 : 2 * lit.toNat % 2 ^ 64 = 2 * lit.toNat := Nat.mod_eq_of_lt (by omega)
  have hmod1 : (2 * lit.toNat + 1) % 2 ^ 64 = 2 * lit.toNat + 1 := Nat.mod_eq_of_lt (by omega)
  have hw0 := k.wvec[2 * lit.toNat].isLt; have hw1 := k.wvec[2 * lit.toNat + 1].isLt
  simp only [show (1 : BitVec 64).toNat = 1 from rfl, hmod0, hmod1] at hc
  rw [Nat.mod_eq_of_lt (by omega : p < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : k.wvec[2 * lit.toNat].toNat +
      k.wvec[2 * lit.toNat + 1].toNat < 2 ^ 64)] at hc
  simp only [fullWatchOffCore, fullWatchSizeCore,
    List.getElem?_eq_getElem (by omega : 2 * lit.toNat < k.wvec.length),
    List.getElem?_eq_getElem (by omega : 2 * lit.toNat + 1 < k.wvec.length), Option.getD_some]
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

local macro "solve_has_bin_loop " hf:term:max " , " hlen:term:max " , " ha:term:max " , "
    hb:term:max " , " hne_eq:term:max " , " hne_neg:term:max " , " hQ:term:max " , "
    s:term:max " , " m:term:max " , " src:term:max " , " tgt:term:max " , " hsrc:term:max
    " , " wrap:term : tactic => `(tactic| (
  have hbounds := ($hf).watches.bounds ($src).toNat $hsrc
  have hslice := modeWatchesInv_slice ($hf).watches $hsrc
  let off := fullWatchOffCore ($s).core ($src).toNat
  let sz := fullWatchSizeCore ($s).core ($src).toNat
  apply wp_while_state1 (t := i64) (fun p : Nat => BitVec.ofNat 64 p) (fun p => off + sz - p)
    (fun p m' => $m = m' ∧ off ≤ p ∧ p ≤ off + sz ∧ WatchBoundary ($s).core.wstk off sz p)
  · intro J920 hJ920; c0_go
    have hsh0 := (wvec_shl1_lt ($hlen).core_ok $hsrc).2.2.1
    rw [wvec_init_off_eq ($hlen).core_ok $hsrc hsh0]
    exact hJ920 off $m ⟨rfl, Nat.le_refl _, by omega, WatchBoundary.here off sz⟩
  · intro J920 p m' ⟨hm', hp_ge, hp_le, hbd⟩ ih; subst hm'; c0_go
    · have hp_lt : p < off + sz := has_bin_hp_lt ($hlen).core_ok hp_le hbounds _ _ (by assumption)
      rcases watchSliceOk_at_boundary hslice hbd hp_lt with
        ⟨w0, hw0, hbin, hent, hbd'⟩ | ⟨w0, _cref, _hq2, hw0, _hw1, hlg, _hlt, hbd'⟩
      · have hwidx : p < ($s).core.wstk.length := by omega
        have hweq : ($s).core.wstk[p] = w0 := by
          have hs := List.getElem?_eq_getElem hwidx; rw [hw0] at hs; cases hs; rfl
        have hp64 : p % 2 ^ 64 = p := Nat.mod_eq_of_lt (by omega)
        c0_go
        · simp only [hp64] at *
          have hmatch : w0 &&& 0x7FFFFFFF#32 = $tgt := by rw [← hweq]; exact ‹_›
          rw [congrArg BitVec.toNat hmatch] at hent
          exact has_bin_ret_true $ha $hb $hne_eq $hne_neg ($wrap hent) $hQ
        · rw [bv64_ofNat_add1 (by omega)]
          exact ih (p + 1) $m (by omega) ⟨rfl, by omega, by omega, hbd'⟩
        · simp only [hp64] at *; rw [hweq] at *; contradiction
      · have hwidx : p < ($s).core.wstk.length := by omega
        have hweq : ($s).core.wstk[p] = w0 := by
          have hs := List.getElem?_eq_getElem hwidx; rw [hw0] at hs; cases hs; rfl
        have hp64 : p % 2 ^ 64 = p := Nat.mod_eq_of_lt (by omega)
        have hlg_stk : ($s).core.wstk[p % 2 ^ 64] &&& 2147483648#32 = 0#32 := by
          simp only [hp64, hweq]; exact hlg
        c0_go
        all_goals first
        | (exfalso; contradiction)
        | (rw [bv64_ofNat_add_ofNat p 2 (by omega)]
           exact ih (p + 2) $m (by omega) ⟨rfl, by omega, by omega, hbd'⟩)
    · exact $hQ false (fun h => Bool.noConfusion h)))

public theorem full_has_bin_wp (Γ : Env) (_hΓ : Γ.Sat Spec.specs)
    (a : Tup Val [i64, i32, i32]) (m : Mem 64) (Q : Post [.bool]) (X : XPost) :
    fullHasBinSpec a m Q X → Func.wp Γ full_has_bin_body a m Q X := by
  rcases a with ⟨h, alit, blit, ⟨⟩⟩
  rintro ⟨c, F0, F_cur, s, R, rfl, hlen, hf, hm, hQ⟩
  have hcv := hlen.core_ok.cur_vars_le; have hwv := hlen.core_ok.wvec_len
  have hwl := hlen.core_ok.wstk_len_arr; have hwl_le := hlen.core_ok.wlen_le
  have hcmax := c.hmaxv; have hcwcap := c.hwcap; unfold dimacsBound at hcmax hcwcap
  c0_go
  all_goals try exact hQ false (fun h => Bool.noConfusion h)
  · have ha : alit.toNat < 2 * s.core.cur_vars := by omega
    have hb : blit.toNat < 2 * s.core.cur_vars := by omega
    have hne_eq : alit ≠ blit := by assumption
    have hne_neg : alit ≠ blit ^^^ 1#32 := by assumption
    solve_has_bin_loop hf, hlen, ha, hb, hne_eq, hne_neg, hQ, s, m, alit, blit, ha, id
  · have ha : alit.toNat < 2 * s.core.cur_vars := by omega
    have hb : blit.toNat < 2 * s.core.cur_vars := by omega
    have hne_eq : alit ≠ blit := by assumption
    have hne_neg : alit ≠ blit ^^^ 1#32 := by assumption
    solve_has_bin_loop hf, hlen, ha, hb, hne_eq, hne_neg, hQ, s, m, blit, alit, hb, entails_swap2

end LeanQbe.T.Examples.Kissat.Proof.Watch
