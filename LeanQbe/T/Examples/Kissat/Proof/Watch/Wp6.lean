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
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics1
import LeanQbe.T.Examples.Kissat.Proof.Spec.MemBridges
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.ControlComb

/-! # Watch WP Proofs Part 6: `full_delete_bin_side_wp` and `full_delete_binary_wp`

Proves `Func.wp` for `full_delete_bin_side` (`fullDeleteBinSideSpec`) and
`full_delete_binary` (`Watch.Spec.fullDeleteBinarySpec`) using `CanonicalEnv`
(`Γ.Sat Spec.specs`). -/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Watch

open Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.C0Step
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Watch
open LeanQbe.T.Examples.Kissat.Proof.Spec
open Kraken.Bedrock2.Test
open scoped FullArenaTactics

public section

private theorem watchBoundary_fwd {wstk : List (BitVec 32)} {p rem q e : Nat}
    (hq : WatchBoundary wstk p rem q) (he : WatchBoundary wstk p rem e) (hlt : q < e)
    {w0 : BitVec 32} (hw0 : wstk[q]? = some w0) (hlg : w0 &&& 0x80000000#32 = 0#32) :
    ∃ cref, q + 2 ≤ e ∧ wstk[q + 1]? = some cref ∧ cref.toNat < 2147483648 := by
  induction hq generalizing e with
  | here p rem =>
    cases he with
    | here => omega
    | bin hw' hbin' _ => rw [hw0] at hw'; cases hw'; exact absurd hlg hbin'
    | large hw0' hw1' _ hlt' rest' =>
      have := (watchBoundary_le rest').1
      exact ⟨_, by omega, hw1', hlt'⟩
  | bin hw hbin rest ih =>
    cases he with
    | here => have := (watchBoundary_le rest).1; omega
    | bin _ _ rest' => exact ih rest' (by omega) hw0
    | large hw0' _ hlg' _ _ => rw [hw0'] at hw; cases hw; exact absurd hlg' hbin
  | large hw0' hw1' hlg' _ rest ih =>
    cases he with
    | here => have := (watchBoundary_le rest).1; omega
    | bin hw' hbin' _ => rw [hw0'] at hw'; cases hw'; exact absurd hlg' hbin'
    | large _ _ _ _ rest' => exact ih rest' (by omega) hw0

private def DbsShiftInv (k0 : FullCoreState) (off sz q0 q : Nat)
    (wstk : List (BitVec 32)) : Prop :=
  off < q0 ∧ q0 ≤ q ∧ q ≤ off + sz ∧ wstk.length = k0.wstk.length ∧
  (∀ idx < q0 - 1, wstk[idx]? = k0.wstk[idx]?) ∧
  (∀ idx, q0 - 1 ≤ idx → idx + 1 < q → wstk[idx]? = k0.wstk[idx + 1]?) ∧
  (∀ idx, q ≤ idx → wstk[idx]? = k0.wstk[idx]?)

private theorem dbs_shift_init (k0 : FullCoreState) {off sz q0 : Nat}
    (hlo : off < q0) (hhi : q0 ≤ off + sz) : DbsShiftInv k0 off sz q0 q0 k0.wstk :=
  ⟨hlo, Nat.le_refl _, hhi, rfl, fun _ _ => rfl, fun _ h1 h2 => by omega, fun _ _ => rfl⟩

private theorem dbs_shift_step {k0 : FullCoreState} {off sz q0 q : Nat}
    {wstk : List (BitVec 32)} (h : DbsShiftInv k0 off sz q0 q wstk) (hlt : q < off + sz)
    (hq_lt : q < wstk.length) (hq1_lt : q - 1 < wstk.length) :
    DbsShiftInv k0 off sz q0 (q + 1) (wstk.set (q - 1) (wstk[q]'hq_lt)) := by
  rcases h with ⟨hlo, hqq0, hhi, hlen, hpre, hmid, hpost⟩
  refine ⟨hlo, by omega, by omega, by simp [hlen], ?_, ?_, ?_⟩
  · intro idx hidx; rw [List.getElem?_set_ne (by omega)]; exact hpre idx hidx
  · intro idx h1 h2
    by_cases hcur : idx = q - 1
    · subst hcur
      rw [List.getElem?_set_self hq1_lt]
      have hidx1 : (q - 1) + 1 = q := by omega
      rw [← List.getElem?_eq_getElem hq_lt, hidx1, hpost q (Nat.le_refl _)]
    · rw [List.getElem?_set_ne (Ne.symm hcur)]; exact hmid idx h1 (by omega)
  · intro idx hidx; rw [List.getElem?_set_ne (by omega)]; exact hpost idx (by omega)

private theorem dbs_other_mono {F_cur : List (List Nat)} {c : FullCfg} {k0 k' : FullCoreState}
    {lit off sz : Nat} (hlit : lit < 2 * k0.cur_vars) (hoff : fullWatchOffCore k0 lit = off)
    (hsz : fullWatchSizeCore k0 lit = sz) (hsz_pos : 0 < sz)
    (hcv_eq : k'.cur_vars = k0.cur_vars) (hdm_eq : k'.dense_mode = k0.dense_mode)
    (hare : fullArenaClauseRefsCore k' = fullArenaClauseRefsCore k0)
    (hlay_fn : WatchStackLayout k0 → WatchStackLayout k')
    (hoth_wv : ∀ l < 2 * k0.cur_vars, l ≠ lit →
      fullWatchOffCore k' l = fullWatchOffCore k0 l ∧
      fullWatchSizeCore k' l = fullWatchSizeCore k0 l)
    (hkeep : ∀ idx < c.wcap, (lit < 2 * k0.cur_vars → idx < off ∨ off + sz ≤ idx) →
      k'.wstk[idx]? = k0.wstk[idx]?)
    (hcap : WatchStackLayout k0 →
      ∀ l < 2 * k0.cur_vars, fullWatchOffCore k0 l + fullWatchSizeCore k0 l ≤ c.wcap)
    (hsl : WatchSliceOk F_cur k0 lit off sz → WatchSliceOk F_cur k' lit off (sz - 1))
    (hdsl : DenseWatchSliceOk F_cur k0 lit off sz →
      DenseWatchSliceOk F_cur k' lit off (sz - 1))
    (hoff' : fullWatchOffCore k' lit = off) (hsz' : fullWatchSizeCore k' lit = sz - 1)
    (hmode : ModeWatchesInv F_cur k0) : ModeWatchesInv F_cur k' := by
  have hmono : WatchStackLayout k0 → ∀ l < 2 * k0.cur_vars, l ≠ lit →
      ∀ idx, fullWatchOffCore k0 l ≤ idx →
        idx < fullWatchOffCore k0 l + fullWatchSizeCore k0 l → k'.wstk[idx]? = k0.wstk[idx]? :=
    fun hlay0 l hl hne idx hi1 hi2 => by
      have hbd := hcap hlay0 l hl
      rcases hlay0.disjoint l lit hl hlit hne (by omega)
          (by rw [hsz]; exact hsz_pos) with hd | hd <;>
        (simp only [hoff, hsz] at hd; exact hkeep idx (by omega) (fun _ => by omega))
  by_cases hdm : k0.dense_mode = 0#64
  · rw [modeWatchesInv_eq_watches hdm] at hmode
    rw [modeWatchesInv_eq_watches (hdm_eq.trans hdm)]
    refine ⟨hlay_fn hmode.layout, fun l hl => ?_⟩
    have hl0 : l < 2 * k0.cur_vars := hcv_eq ▸ hl
    by_cases hll : l = lit
    · subst hll; rw [hoff', hsz']; exact hsl (by rw [← hoff, ← hsz]; exact hmode.slices _ hl0)
    · obtain ⟨ho, hs⟩ := hoth_wv l hl0 hll; rw [ho, hs]
      exact WatchSliceOk.mono (k := k0) (k' := k') (Std.Sat.CNF.entails_refl (cnfOfClauses F_cur))
        (Nat.le_of_eq hcv_eq.symm) (fun _ r => hare ▸ r) (hmono hmode.layout l hl0 hll)
        (hmode.slices l hl0)
  · rw [modeWatchesInv_eq_dense hdm] at hmode
    rw [modeWatchesInv_eq_dense (hdm_eq.symm ▸ hdm)]
    refine ⟨hlay_fn hmode.layout, fun l hl => ?_⟩
    have hl0 : l < 2 * k0.cur_vars := hcv_eq ▸ hl
    by_cases hll : l = lit
    · subst hll; rw [hoff', hsz']; exact hdsl (by rw [← hoff, ← hsz]; exact hmode.slices _ hl0)
    · obtain ⟨ho, hs⟩ := hoth_wv l hl0 hll; rw [ho, hs]
      exact DenseWatchSliceOk.mono (k := k0) (k' := k')
        (Std.Sat.CNF.entails_refl (cnfOfClauses F_cur))
        (Nat.le_of_eq hcv_eq.symm) (fun _ r => hare ▸ r) (hmono hmode.layout l hl0 hll)
        (hmode.slices l hl0)

private theorem dbs_shift_post {c : FullCfg} {s : FullState} {lit : Val i32}
    {off sz q0 : Nat} {wstk1 : List (BitVec 32)} {w0 : BitVec 32} {R : Mem 64 → Prop}
    {m : Mem 64} {Q : Post []}
    (hlen : s.LengthsOk c) (hlit : lit.toNat < 2 * s.core.cur_vars)
    (hoff : off = fullWatchOff s lit.toNat) (hsz : sz = fullWatchSize s lit.toNat)
    (hbounds : off + sz ≤ s.core.wlen)
    (hw0_ex : s.core.wstk[q0 - 1]? = some w0 ∧ w0 &&& 0x80000000#32 ≠ 0#32)
    (hbd_slice : ∀ F_cur, WatchSliceOk F_cur s.core lit.toNat off sz →
      WatchBoundary s.core.wstk off sz (q0 - 1))
    (hbd_dense : ∀ F_cur, DenseWatchSliceOk F_cur s.core lit.toNat off sz →
      WatchBoundary s.core.wstk off sz (q0 - 1))
    (hinv : DbsShiftInv s.core off sz q0 (off + sz) wstk1)
    (hm : (FullMem c { s with core := { s.core with
      wvec := s.core.wvec.set (2 * lit.toNat + 1) (BitVec.ofNat 32 (sz - 1)),
      wstk := wstk1.set (off + sz - 1) 0xFFFFFFFF#32,
      wusable := s.core.wusable + 1#64 } } ⋆ R) m)
    (hQ : ∀ (wvec' wstk' : List (BitVec 32)) (wu' : BitVec 64) (m' : Mem 64),
      let s' : FullState := { s with core := { s.core with
        wvec := wvec', wstk := wstk', wusable := wu' } }
      s'.LengthsOk c →
      (lit.toNat < 2 * s.core.cur_vars →
        fullWatchOff s' lit.toNat = fullWatchOff s lit.toNat ∧
        fullWatchSize s' lit.toNat ≤ fullWatchSize s lit.toNat) →
      (∀ l < 2 * s.core.cur_vars, l ≠ lit.toNat →
        fullWatchOff s' l = fullWatchOff s l ∧ fullWatchSize s' l = fullWatchSize s l) →
      (∀ idx < c.wcap,
        (lit.toNat < 2 * s.core.cur_vars → idx < fullWatchOff s lit.toNat ∨
          fullWatchOff s lit.toNat + fullWatchSize s lit.toNat ≤ idx) →
        wstk'[idx]? = s.core.wstk[idx]?) →
      (∀ F_cur, WatchSliceOk F_cur s.core lit.toNat (fullWatchOff s lit.toNat)
        (fullWatchSize s lit.toNat) → WatchSliceOk F_cur s'.core lit.toNat
          (fullWatchOff s' lit.toNat) (fullWatchSize s' lit.toNat)) →
      (∀ F_cur, DenseWatchSliceOk F_cur s.core lit.toNat (fullWatchOff s lit.toNat)
        (fullWatchSize s lit.toNat) → DenseWatchSliceOk F_cur s'.core lit.toNat
          (fullWatchOff s' lit.toNat) (fullWatchSize s' lit.toNat)) →
      (WatchStackLayout s.core → WatchStackLayout s'.core) →
      (∀ F_cur, ModeWatchesInv F_cur s.core → ModeWatchesInv F_cur s'.core) →
      (FullMem c s' ⋆ R) m' → Q () m') : Q () m := by
  rcases hinv with ⟨hlo, hqq0, hhi, hlen1, hpre, hmid, hpost⟩
  have hwv := hlen.core_ok.wvec_len; have hwl := hlen.core_ok.wstk_len_arr
  have hcv := hlen.core_ok.cur_vars_le; have hwle := hlen.core_ok.wlen_le
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hwv1 : 2 * lit.toNat + 1 < s.core.wvec.length := by omega
  have hsz_lt : sz - 1 < 2 ^ 32 := by
    have hlt32 : fullWatchSize s lit.toNat < 2 ^ 32 :=
      (s.core.wvec[2 * lit.toNat + 1]?.getD 0#32).isLt
    rw [← hsz] at hlt32; omega
  let wvec' := s.core.wvec.set (2 * lit.toNat + 1) (BitVec.ofNat 32 (sz - 1))
  let wstk' := wstk1.set (off + sz - 1) 0xFFFFFFFF#32
  have hws_len' : wstk'.length = c.wcap := by simp [wstk', hlen1, hwl]
  have hwv_len' : wvec'.length = 4 * c.max_vars := by simp [wvec', hwv]
  have hlen' : FullState.LengthsOk c { s with core := { s.core with
      wvec := wvec', wstk := wstk', wusable := s.core.wusable + 1#64 } } :=
    ⟨{ hlen.core_ok with wvec_len := hwv_len', wstk_len_arr := hws_len' }, hlen.scratch_ok⟩
  have hoff_c0 : fullWatchOffCore s.core lit.toNat = off := hoff.symm
  have hsz_c0 : fullWatchSizeCore s.core lit.toNat = sz := hsz.symm
  have hoff_eq : fullWatchOffCore { s.core with
      wvec := wvec', wstk := wstk', wusable := s.core.wusable + 1#64 } lit.toNat = off := by
    dsimp only [fullWatchOffCore, wvec']
    rw [congrArg BitVec.toNat (wvec_set_size_off_self hwv1 _)]; exact hoff_c0
  have hsz_eq : fullWatchSizeCore { s.core with
      wvec := wvec', wstk := wstk', wusable := s.core.wusable + 1#64 } lit.toNat = sz - 1 := by
    dsimp only [fullWatchSizeCore, wvec']
    rw [wvec_set_size_sz_self hwv1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsz_lt]
  have hoth_wv : ∀ l < 2 * s.core.cur_vars, l ≠ lit.toNat →
      fullWatchOffCore { s.core with
        wvec := wvec', wstk := wstk', wusable := s.core.wusable + 1#64 } l =
        fullWatchOff s l ∧
      fullWatchSizeCore { s.core with
        wvec := wvec', wstk := wstk', wusable := s.core.wusable + 1#64 } l =
        fullWatchSize s l := by
    intro l _ hne
    have h := wvec_set_size_other (wvec := s.core.wvec) hne (BitVec.ofNat 32 (sz - 1))
    exact ⟨congrArg BitVec.toNat h.1, congrArg BitVec.toNat h.2⟩
  have hkeep : ∀ idx < c.wcap,
      (lit.toNat < 2 * s.core.cur_vars → idx < off ∨ off + sz ≤ idx) →
      wstk'[idx]? = s.core.wstk[idx]? := by
    intro idx _ hcond
    rcases hcond hlit with hlt_idx | hge_idx
    · rw [List.getElem?_set_ne (by omega)]; exact hpre idx (by omega)
    · rw [List.getElem?_set_ne (by omega)]; exact hpost idx (by omega)
  have hpre_slice : ∀ idx, off ≤ idx → idx < q0 - 1 → wstk'[idx]? = s.core.wstk[idx]? := by
    intro idx _ hi; rw [List.getElem?_set_ne (by omega)]; exact hpre idx hi
  have hmid_slice : ∀ idx, q0 - 1 ≤ idx → idx < off + sz - 1 →
      wstk'[idx]? = s.core.wstk[idx + 1]? := by
    intro idx h1 h2; rw [List.getElem?_set_ne (by omega)]; exact hmid idx h1 (by omega)
  have hsl_out : ∀ F_cur, WatchSliceOk F_cur s.core lit.toNat off sz →
      WatchSliceOk F_cur { s.core with
        wvec := wvec', wstk := wstk', wusable := s.core.wusable + 1#64 }
        lit.toNat off (sz - 1) := fun F_cur hs =>
    @watchSliceOk_erase F_cur s.core
      { s.core with wvec := wvec', wstk := wstk', wusable := s.core.wusable + 1#64 }
      lit.toNat off sz (q0 - 1) 1 (Nat.le_refl _) (fun _ r => r) hs (hbd_slice F_cur hs)
      (by omega) (Or.inl ⟨rfl, w0, hw0_ex.1, hw0_ex.2⟩) hpre_slice hmid_slice
  have hdsl_out : ∀ F_cur, DenseWatchSliceOk F_cur s.core lit.toNat off sz →
      DenseWatchSliceOk F_cur { s.core with
        wvec := wvec', wstk := wstk', wusable := s.core.wusable + 1#64 }
        lit.toNat off (sz - 1) := fun F_cur hs =>
    @denseWatchSliceOk_erase F_cur s.core
      { s.core with wvec := wvec', wstk := wstk', wusable := s.core.wusable + 1#64 }
      lit.toNat off sz (q0 - 1) 1 (Nat.le_refl _) (fun _ r => r) hs (hbd_dense F_cur hs)
      (by omega) (Or.inl ⟨rfl, w0, hw0_ex.1, hw0_ex.2⟩) hpre_slice hmid_slice
  have hlay_fn : WatchStackLayout s.core → WatchStackLayout { s.core with
      wvec := wvec', wstk := wstk', wusable := s.core.wusable + 1#64 } := fun hlay => by
    have hother : ∀ l < 2 * s.core.cur_vars, l ≠ lit.toNat →
        ∀ idx < fullWatchSizeCore s.core l,
          wstk'[fullWatchOffCore s.core l + idx]? =
            s.core.wstk[fullWatchOffCore s.core l + idx]? := by
      intro l hl hne idx hidx
      have hbd_l := hlay.bounds l hl
      have hd := hlay.disjoint l lit.toNat hl hlit hne (Nat.lt_of_le_of_lt (Nat.zero_le _) hidx)
        (by rw [hsz_c0]; omega)
      rw [hoff_c0, hsz_c0] at hd
      rcases hd with hd | hd
      · exact hkeep _ (by omega) (fun _ => Or.inl (by omega))
      · exact hkeep _ (by omega) (fun _ => Or.inr (by omega))
    have hnosent : ∀ idx < fullWatchSizeCore s.core lit.toNat - 1,
        wstk'[fullWatchOffCore s.core lit.toNat + idx]? ≠ some 0xFFFFFFFF#32 := by
      intro idx hidx
      rw [hsz_c0] at hidx
      rw [hoff_c0]
      by_cases hlt_q : off + idx < q0 - 1
      · rw [hpre_slice (off + idx) (Nat.le_add_right _ _) hlt_q, ← hoff_c0]
        exact hlay.no_sentinel lit.toNat hlit idx (by rw [hsz_c0]; omega)
      · rw [hmid_slice (off + idx) (by omega) (by omega)]
        rw [show off + idx + 1 = off + (idx + 1) by omega, ← hoff_c0]
        exact hlay.no_sentinel lit.toNat hlit (idx + 1) (by rw [hsz_c0]; omega)
    have hshr := watchStackLayout_shrink (cnt := 1) hlay hlen.core_ok hlit
      (by rw [hsz_c0]; omega) hother hnosent
      (nb' := s.core.num_binary) (wusable' := s.core.wusable + 1#64) (Nat.le_refl _)
    rw [hsz_c0] at hshr; exact hshr
  apply hQ wvec' wstk' (s.core.wusable + 1#64) m hlen'
    (fun _ => ⟨by simpa [fullWatchOff, hoff_c0] using hoff_eq,
      by dsimp only [fullWatchSize]; rw [hsz_eq, hsz_c0]; omega⟩)
    (fun l hl hne => hoth_wv l hl hne)
    (fun idx hi hc => by rw [← hoff_c0, ← hsz_c0] at hkeep; exact hkeep idx hi hc)
  · intro F_cur hs
    rw [show fullWatchOff s lit.toNat = off from hoff_c0,
      show fullWatchSize s lit.toNat = sz from hsz_c0] at hs
    rw [show fullWatchOff { s with core := _ } lit.toNat = off from hoff_eq,
      show fullWatchSize { s with core := _ } lit.toNat = sz - 1 from hsz_eq]
    exact hsl_out F_cur hs
  · intro F_cur hs
    rw [show fullWatchOff s lit.toNat = off from hoff_c0,
      show fullWatchSize s lit.toNat = sz from hsz_c0] at hs
    rw [show fullWatchOff { s with core := _ } lit.toNat = off from hoff_eq,
      show fullWatchSize { s with core := _ } lit.toNat = sz - 1 from hsz_eq]
    exact hdsl_out F_cur hs
  · exact hlay_fn
  · intro F_cur hmode
    exact dbs_other_mono (k' := { s.core with
      wvec := wvec', wstk := wstk', wusable := s.core.wusable + 1#64 })
      hlit hoff_c0 hsz_c0 (by omega) rfl rfl rfl hlay_fn
      hoth_wv hkeep (fun hlay l hl => Nat.le_trans (hlay.bounds l hl) hwle)
      (hsl_out F_cur) (hdsl_out F_cur) hoff_eq hsz_eq hmode
  · exact hm

theorem full_delete_bin_side_wp (Γ : Env) (_hΓ : Γ.Sat Spec.specs)
    (a : Tup Val [i64, i32, i32]) (m : Mem 64) (Q : Post []) (X : XPost) :
    fullDeleteBinSideSpec a m Q X → Func.wp Γ full_delete_bin_side_body a m Q X := by
  rcases a with ⟨h, lit, other, ⟨⟩⟩
  rintro ⟨c, s, R, rfl, hlen, hbd_fn, hm, hQ⟩
  have hcv := hlen.core_ok.cur_vars_le; have hwv := hlen.core_ok.wvec_len
  have hwl := hlen.core_ok.wstk_len_arr; have hwle := hlen.core_ok.wlen_le
  have hmx := c.hmaxv; have hwc := c.hwcap; unfold dimacsBound at hmx hwc
  unfold Func.wp full_delete_bin_side_body
  c0_hstraight
  c0_hsplit
  · have hge : 2 * s.core.cur_vars ≤ lit.toNat := by
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hc; omega
    exact hQ s.core.wvec s.core.wstk s.core.wusable m hlen (fun h => absurd h (by omega))
      (fun _ _ _ => ⟨rfl, rfl⟩) (fun _ _ _ => rfl) (fun _ h => h) (fun _ h => h)
      (fun h => h) (fun _ h => h) hm
  · have hlit : lit.toNat < 2 * s.core.cur_vars := by
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hc; omega
    have hbounds : fullWatchOffCore s.core lit.toNat + fullWatchSizeCore s.core lit.toNat ≤
        s.core.wlen := hbd_fn hlit
    have hwv0 : 2 * lit.toNat < s.core.wvec.length := by omega
    have hwv1 : 2 * lit.toNat + 1 < s.core.wvec.length := by omega
    have hsh : (BitVec.setWidth 64 lit <<< 1).toNat = 2 * lit.toNat ∧
        (BitVec.setWidth 64 lit <<< 1 + 1).toNat = 2 * lit.toNat + 1 :=
      ⟨bv64_shl1_lit lit, bv64_shl1_add1_lit lit⟩
    have hmod_wv0 : (BitVec.setWidth 64 lit <<< 1).toNat < s.core.wvec.length := by
      rw [hsh.1]; exact hwv0
    have hmod_wv1 : (BitVec.setWidth 64 lit <<< 1 + 1).toNat < s.core.wvec.length := by
      rw [hsh.2]; exact hwv1
    let off := fullWatchOffCore s.core lit.toNat
    let sz := fullWatchSizeCore s.core lit.toNat
    have hoff_eq : (BitVec.setWidth 64
        (s.core.wvec[(BitVec.setWidth 64 lit <<< 1).toNat]'hmod_wv0)).toNat = off := by
      have hget : s.core.wvec[(BitVec.setWidth 64 lit <<< 1).toNat]'hmod_wv0 =
          s.core.wvec[2 * lit.toNat]'hwv0 := by
        have h := hsh.1; generalize (BitVec.setWidth 64 lit <<< 1).toNat = j at hmod_wv0 h ⊢
        subst h; rfl
      rw [BitVec.toNat_setWidth, hget, Nat.mod_eq_of_lt (by omega)]
      unfold off fullWatchOffCore
      rw [List.getElem?_eq_getElem hwv0, Option.getD_some]
    have hsz_eq : (BitVec.setWidth 64
        (s.core.wvec[(BitVec.setWidth 64 lit <<< 1 + 1).toNat]'hmod_wv1)).toNat = sz := by
      have hget : s.core.wvec[(BitVec.setWidth 64 lit <<< 1 + 1).toNat]'hmod_wv1 =
          s.core.wvec[2 * lit.toNat + 1]'hwv1 := by
        have h := hsh.2; generalize (BitVec.setWidth 64 lit <<< 1 + 1).toNat = j at hmod_wv1 h ⊢
        subst h; rfl
      rw [BitVec.toNat_setWidth, hget, Nat.mod_eq_of_lt (by omega)]
      unfold sz fullWatchSizeCore
      rw [List.getElem?_eq_getElem hwv1, Option.getD_some]
    c0_hsteps_nogrp
    · exact hQ s.core.wvec s.core.wstk s.core.wusable m hlen (fun _ => ⟨rfl, Nat.le_refl _⟩)
        (fun _ _ _ => ⟨rfl, rfl⟩) (fun _ _ _ => rfl) (fun _ h => h) (fun _ h => h)
        (fun h => h) (fun _ h => h) hm
    · have hsz_wv : (s.core.wvec[2 * lit.toNat + 1]'hwv1).toNat = sz := by
        unfold sz fullWatchSizeCore
        rw [List.getElem?_eq_getElem hwv1, Option.getD_some]
      have hsz_pos : 0 < sz := by
        have hne_sz : sz ≠ 0 := fun hz => hc (BitVec.eq_of_toNat_eq (by
          have h1_64 : (1 : BitVec 64).toNat = 1 := rfl
          have hidx_eq : (2 * lit.toNat + (1 : BitVec 64).toNat) % 2 ^ 64 =
              2 * lit.toNat + 1 := by
            rw [h1_64, Nat.mod_eq_of_lt (by omega)]
          have hget := list_getElem_congr (by rw [hidx_eq]; exact hwv1) hidx_eq
          rw [BitVec.toNat_setWidth, hget, Nat.mod_eq_of_lt (by omega), hsz_wv, hz]; rfl))
        omega
      have h_end_eq :
          (BitVec.setWidth 64 (s.core.wvec[(BitVec.setWidth 64 lit <<< 1).toNat]'hmod_wv0) +
            BitVec.setWidth 64
              (s.core.wvec[(BitVec.setWidth 64 lit <<< 1 + 1).toNat]'hmod_wv1)).toNat =
            off + sz := by
        rw [BitVec.toNat_add, hoff_eq, hsz_eq, Nat.mod_eq_of_lt (by omega)]
      have h_end_sum :
          ((s.core.wvec[2 * lit.toNat]'hwv0).toNat +
            (s.core.wvec[2 * lit.toNat + 1]'hwv1).toNat) % 2 ^ 64 = off + sz := by
        have ho : (s.core.wvec[2 * lit.toNat]'hwv0).toNat = off := by
          unfold off fullWatchOffCore
          rw [List.getElem?_eq_getElem hwv0, Option.getD_some]
        rw [ho, hsz_wv, Nat.mod_eq_of_lt (by omega)]
      let InvOuter : Nat × Bool → Mem 64 → Prop := fun st m1 =>
        (FullMem c s ⋆ R) m1 ∧ off ≤ st.1 ∧ st.1 ≤ off + sz ∧
        (st.2 = true → off < st.1 ∧ ∃ w0 : BitVec 32,
          s.core.wstk[st.1 - 1]? = some w0 ∧ w0 &&& 0x80000000#32 ≠ 0#32 ∧
          (∀ F_cur, WatchSliceOk F_cur s.core lit.toNat off sz →
            WatchBoundary s.core.wstk off sz (st.1 - 1)) ∧
          (∀ F_cur, DenseWatchSliceOk F_cur s.core lit.toNat off sz →
            WatchBoundary s.core.wstk off sz (st.1 - 1)))
      apply wp_join_state (fun st : Nat × Bool => (BitVec.ofNat 64 st.1, st.2, ())) InvOuter
      · intro J_unused ⟨q0, found⟩ m1 ⟨hm1, hq_ge, hq_le, hfound⟩
        dsimp only at hfound ⊢
        c0_hsplit
        · rcases hfound hc with ⟨hq_lo, w0, hw0, hbin, hbd_s, hbd_d⟩
          let InvShift : Nat × List (BitVec 32) → Mem 64 → Prop := fun st m2 =>
            DbsShiftInv s.core off sz q0 st.1 st.2 ∧
            (FullMem c { s with core := { s.core with wstk := st.2 } } ⋆ R) m2
          apply wp_while_state (fun st => (BitVec.ofNat 64 st.1, ()))
            (fun st => off + sz - st.1) InvShift
          · intro Js hJs
            c0_hstraight
            exact hJs (q0, s.core.wstk) m1 ⟨dbs_shift_init s.core hq_lo hq_le, hm1⟩
          · intro Js ⟨q, wstk1⟩ m2 ⟨hinv1, hm2⟩ ih
            clear hm1
            dsimp only at hinv1 hm2 ih ⊢
            have hwlen1 : wstk1.length = s.core.wstk.length := hinv1.2.2.2.1
            have hq_le_cur : q ≤ off + sz := hinv1.2.2.1
            have hq_lo_cur : off < q := by have := hinv1.1; have := hinv1.2.1; omega
            have hq_bv : (BitVec.ofNat 64 q).toNat = q := Nat.mod_eq_of_lt (by omega)
            have h1_64 : (1 : BitVec 64).toNat = 1 := rfl
            c0_hsplit
            · have hlt_q : q < off + sz := by
                simp only [h1_64, Nat.mod_eq_of_lt (show q < 2 ^ 64 by omega),
                  Nat.mod_eq_of_lt (show 2 * lit.toNat < 2 ^ 64 by omega),
                  Nat.mod_eq_of_lt (show 2 * lit.toNat + 1 < 2 ^ 64 by omega),
                  h_end_sum] at hc
                exact hc
              have hq_sub1 : (BitVec.ofNat 64 q - (1 : BitVec 64)).toNat = q - 1 := by
                rw [BitVec.toNat_sub, h1_64, hq_bv]; omega
              have hq_lt : q < wstk1.length := by omega
              have hq1_lt : q - 1 < wstk1.length := by omega
              c0_hsteps
              have hjump : BitVec.ofNat 64 q + 1 = BitVec.ofNat 64 (q + 1) := by
                apply BitVec.eq_of_toNat_eq
                simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, h1_64]
                omega
              rw [hjump]
              have hm_next := ‹(FullMem c _ ⋆ R) _›
              simp only [hq_bv, hq_sub1] at hm_next
              exact ih (q + 1, wstk1.set (q - 1) (wstk1[q]'hq_lt)) _ (by omega)
                ⟨dbs_shift_step hinv1 hlt_q hq_lt hq1_lt, hm_next⟩
            · have heq_q : q = off + sz := by
                simp only [h1_64, Nat.mod_eq_of_lt (show q < 2 ^ 64 by omega),
                  Nat.mod_eq_of_lt (show 2 * lit.toNat < 2 ^ 64 by omega),
                  Nat.mod_eq_of_lt (show 2 * lit.toNat + 1 < 2 ^ 64 by omega),
                  h_end_sum] at hc
                omega
              subst heq_q
              have hwc := c.hwcap; unfold dimacsBound at hwc
              have hsz_wv : (s.core.wvec[2 * lit.toNat + 1]'hwv1).toNat = sz := by
                unfold sz fullWatchSizeCore
                rw [List.getElem?_eq_getElem hwv1, Option.getD_some]
              have hsz_lt32 : sz < 2 ^ 32 :=
                hsz_wv ▸ (s.core.wvec[2 * lit.toNat + 1]'hwv1).isLt
              have h_os_lt : off + sz < 2 ^ 32 := by
                have := hbounds; have := hlen.core_ok.wlen_le; omega
              have hsz64 :
                  (BitVec.setWidth 64 (s.core.wvec[2 * lit.toNat + 1]'hwv1)).toNat = sz := by
                rw [BitVec.toNat_setWidth, hsz_wv,
                  Nat.mod_eq_of_lt (Nat.lt_trans hsz_lt32 (by decide))]
              have hsum64 :
                  (BitVec.setWidth 64
                      (s.core.wvec[(BitVec.setWidth 64 lit <<< OfNat.ofNat 1).toNat]'hmod_wv0) +
                    BitVec.setWidth 64 (s.core.wvec[2 * lit.toNat + 1]'hwv1)).toNat =
                  off + sz := by
                rw [BitVec.toNat_add, hoff_eq, hsz64,
                  Nat.mod_eq_of_lt (Nat.lt_trans h_os_lt (by decide))]
              have hend_sub1 :
                  (BitVec.setWidth 64
                      (s.core.wvec[(BitVec.setWidth 64 lit <<< OfNat.ofNat 1).toNat]'hmod_wv0) +
                    BitVec.setWidth 64 (s.core.wvec[2 * lit.toNat + 1]'hwv1) - 1).toNat =
                  off + sz - 1 := by
                rw [bv64_sub1_nat (by rw [hsum64]; omega), hsum64]
              have hend_lt : off + sz - 1 < wstk1.length := by omega
              have hsh1 := hsh.2
              c0_hsteps
              have hsz_val :
                  BitVec.setWidth 32
                      (BitVec.setWidth 64 (s.core.wvec[2 * lit.toNat + 1]'hwv1) - 1) =
                    BitVec.ofNat 32 (sz - 1) := by
                apply BitVec.eq_of_toNat_eq
                rw [BitVec.toNat_setWidth, bv64_sub1_nat (by rw [hsz64]; exact hsz_pos),
                  hsz64, BitVec.toNat_ofNat,
                  Nat.mod_eq_of_lt (Nat.lt_trans (Nat.sub_lt hsz_pos (by decide)) hsz_lt32)]
              have hm_next := ‹(FullMem c _ ⋆ R) _›
              simp only [hsh1, hend_sub1, hsz_val] at hm_next
              exact dbs_shift_post hlen hlit rfl rfl hbounds ⟨hw0, hbin⟩ hbd_s hbd_d
                hinv1 hm_next hQ
        · c0_hsteps
          exact hQ s.core.wvec s.core.wstk s.core.wusable m1 hlen (fun _ => ⟨rfl, Nat.le_refl _⟩)
            (fun _ _ _ => ⟨rfl, rfl⟩) (fun _ _ _ => rfl) (fun _ h => h) (fun _ h => h)
            (fun h => h) (fun _ h => h) hm1
      · intro J_out hJ_out
        let InvScan : Nat → Mem 64 → Prop := fun q m1 =>
          (FullMem c s ⋆ R) m1 ∧ off ≤ q ∧ q ≤ off + sz ∧
          (∀ F_cur, WatchSliceOk F_cur s.core lit.toNat off sz →
            WatchBoundary s.core.wstk off sz q) ∧
          (∀ F_cur, DenseWatchSliceOk F_cur s.core lit.toNat off sz →
            WatchBoundary s.core.wstk off sz q)
        apply wp_while_state (fun q : Nat => (BitVec.ofNat 64 q, ()))
          (fun q => off + sz - q) InvScan
        · intro J hJ
          c0_hstraight
          have hoff_bv : BitVec.setWidth 64
              (s.core.wvec[(BitVec.setWidth 64 lit <<< 1).toNat]'hmod_wv0) =
              BitVec.ofNat 64 off := by
            apply BitVec.eq_of_toNat_eq
            rw [hoff_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          rw [hoff_bv]
          exact hJ off _ ⟨‹_›, Nat.le_refl _, by omega,
            fun _ _ => WatchBoundary.here off sz, fun _ _ => WatchBoundary.here off sz⟩
        · intro J q m1 ⟨hm1, hq_ge, hq_le, hbd_s, hbd_d⟩ ih
          dsimp only at hbd_s hbd_d ih ⊢
          have hq_bv : (BitVec.ofNat 64 q).toNat = q := Nat.mod_eq_of_lt (by omega)
          have h1_64 : (1 : BitVec 64).toNat = 1 := rfl
          c0_hsplit
          · have hlt_q : q < off + sz := by
              simp only [h1_64, Nat.mod_eq_of_lt (show q < 2 ^ 64 by omega),
                Nat.mod_eq_of_lt (show 2 * lit.toNat < 2 ^ 64 by omega),
                Nat.mod_eq_of_lt (show 2 * lit.toNat + 1 < 2 ^ 64 by omega),
                h_end_sum] at hc
              exact hc
            have hq_lt : q < s.core.wstk.length := by omega
            c0_hstraight
            let InvJoin2 : Nat × Bool → Mem 64 → Prop := fun st m2 =>
              (FullMem c s ⋆ R) m2 ∧ q < st.1 ∧ off < st.1 ∧ st.1 ≤ off + sz ∧ st.2 = false ∧
              (∀ F_cur, WatchSliceOk F_cur s.core lit.toNat off sz →
                WatchBoundary s.core.wstk off sz st.1) ∧
              (∀ F_cur, DenseWatchSliceOk F_cur s.core lit.toNat off sz →
                WatchBoundary s.core.wstk off sz st.1)
            apply wp_join_state (fun st : Nat × Bool => (BitVec.ofNat 64 st.1, st.2, ())) InvJoin2
            · intro J2 ⟨q', b'⟩ m2 ⟨hm2, hq_lt', hq'_lo, hq'_le, hb', hbd_s', hbd_d'⟩
              subst hb'
              c0_hstraight
              exact ih q' m2 (by omega) ⟨hm2, by omega, hq'_le, hbd_s', hbd_d'⟩
            · intro J2 hJ2
              have hq1_bv : BitVec.ofNat 64 q + 1 = BitVec.ofNat 64 (q + 1) := by
                apply BitVec.eq_of_toNat_eq
                simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, h1_64]
                omega
              c0_hsplit
              · have hw_eq : s.core.wstk[q]? = some (s.core.wstk[q]'hq_lt) :=
                  List.getElem?_eq_getElem hq_lt
                have hbin : (s.core.wstk[q]'hq_lt) &&& 0x80000000#32 ≠ 0#32 := by
                  simp only [Nat.mod_eq_of_lt (show q < 2 ^ 64 by omega)] at hc
                  exact hc
                c0_hsplit
                · c0_hsteps
                  rw [hq1_bv]
                  refine hJ_out (q + 1, true) m1 ⟨hm1, by omega, by omega, fun _ =>
                    ⟨by omega, s.core.wstk[q]'hq_lt, by simp [hw_eq], hbin, ?_, ?_⟩⟩
                  · intro F_cur hs; simpa using hbd_s F_cur hs
                  · intro F_cur hs; simpa using hbd_d F_cur hs
                · c0_hsteps
                  rw [hq1_bv]
                  exact hJ2 (q + 1, false) m1 ⟨hm1, by omega, by omega, by omega, rfl,
                    fun F_cur hs => watchBoundary_append_bin (hbd_s F_cur hs) (by omega) hw_eq hbin,
                    fun F_cur hs => watchBoundary_append_bin (hbd_d F_cur hs) (by omega) hw_eq hbin⟩
              · have hw_eq : s.core.wstk[q]? = some (s.core.wstk[q]'hq_lt) :=
                  List.getElem?_eq_getElem hq_lt
                have hlg : (s.core.wstk[q]'hq_lt) &&& 0x80000000#32 = 0#32 := by
                  simp only [Nat.mod_eq_of_lt (show q < 2 ^ 64 by omega)] at hc
                  exact hc
                let InvJoin3 : Nat → Mem 64 → Prop := fun q' m3 =>
                  (FullMem c s ⋆ R) m3 ∧ q < q' ∧ q' ≤ off + sz ∧
                  (∀ F_cur, WatchSliceOk F_cur s.core lit.toNat off sz →
                    WatchBoundary s.core.wstk off sz q') ∧
                  (∀ F_cur, DenseWatchSliceOk F_cur s.core lit.toNat off sz →
                    WatchBoundary s.core.wstk off sz q')
                apply wp_join_state (fun q' : Nat => (BitVec.ofNat 64 q', ())) InvJoin3
                · intro J3 q' m3 ⟨hm3, hq'_gt, hq'_le, hbd_s', hbd_d'⟩
                  c0_hstraight
                  exact hJ2 (q', false) m3 ⟨hm3, hq'_gt, by omega, hq'_le, rfl, hbd_s', hbd_d'⟩
                · intro J3 hJ3
                  c0_hsplit
                  · c0_hsteps
                    have hq1_lt_end : q + 1 < off + sz := by
                      simp only [h1_64, Nat.mod_eq_of_lt (show q + 1 < 2 ^ 64 by omega),
                        Nat.mod_eq_of_lt (show 2 * lit.toNat < 2 ^ 64 by omega),
                        Nat.mod_eq_of_lt (show 2 * lit.toNat + 1 < 2 ^ 64 by omega),
                        h_end_sum] at hc
                      exact hc
                    have hq2_bv : BitVec.ofNat 64 q + 1 + 1 = BitVec.ofNat 64 (q + 2) := by
                      apply BitVec.eq_of_toNat_eq
                      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, h1_64]
                      omega
                    rw [hq2_bv]
                    refine hJ3 (q + 2) m1 ⟨hm1, by omega, by omega, ?_, ?_⟩
                    · intro F_cur hs
                      have hbd := hbd_s F_cur hs
                      obtain ⟨cref, hq2, hw1, hcref⟩ :=
                        watchBoundary_fwd hbd (watchSliceOk_boundary_end hs) hlt_q hw_eq hlg
                      exact watchBoundary_append_large hbd hq2 hw_eq hw1 hlg hcref
                    · intro F_cur hs
                      have hbd := hbd_d F_cur hs
                      obtain ⟨cref, hq2, hw1, hcref⟩ :=
                        watchBoundary_fwd hbd (denseWatchSliceOk_boundary_end hs) hlt_q hw_eq hlg
                      exact watchBoundary_append_large hbd hq2 hw_eq hw1 hlg hcref
                  · c0_hsteps
                    have hq1_ge_end : off + sz ≤ q + 1 := by
                      simp only [h1_64, Nat.mod_eq_of_lt (show q + 1 < 2 ^ 64 by omega),
                        Nat.mod_eq_of_lt (show 2 * lit.toNat < 2 ^ 64 by omega),
                        Nat.mod_eq_of_lt (show 2 * lit.toNat + 1 < 2 ^ 64 by omega),
                        h_end_sum] at hc
                      omega
                    rw [hq1_bv]
                    refine hJ3 (q + 1) m1 ⟨hm1, by omega, by omega, ?_, ?_⟩
                    · intro F_cur hs
                      obtain ⟨_, hq2, _⟩ := watchBoundary_fwd (hbd_s F_cur hs)
                        (watchSliceOk_boundary_end hs) hlt_q hw_eq hlg
                      omega
                    · intro F_cur hs
                      obtain ⟨_, hq2, _⟩ := watchBoundary_fwd (hbd_d F_cur hs)
                        (denseWatchSliceOk_boundary_end hs) hlt_q hw_eq hlg
                      omega
          · c0_hsteps
            exact hJ_out (q, false) m1 ⟨hm1, hq_ge, hq_le, fun h => Bool.noConfusion h⟩

private theorem dbin_idx_lt {c : FullCfg} {k : FullCoreState} {x : BitVec 32}
    (hfl : k.flags.length = c.max_vars) (hx : x.toNat < 2 * c.max_vars) :
    (BitVec.setWidth 64 (x >>> 1)).toNat < k.flags.length := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.mod_eq_of_lt]
  · change x.toNat / 2 < k.flags.length; omega
  · have : x.toNat >>> 1 ≤ x.toNat := Nat.shiftRight_le _ _
    omega

theorem full_delete_binary_wp (Γ : Env) (hΓ : Γ.Sat Spec.specs)
    (a' : Tup Val [i64, i32, i32]) (m : Mem 64) (Q : Post []) (X : XPost) :
    Spec.fullDeleteBinarySpec a' m Q X → Func.wp Γ full_delete_binary_body a' m Q X := by
  rcases a' with ⟨h, a, b, ⟨⟩⟩
  rintro ⟨c, s, R, rfl, hlen, hlay, ha, hb, hm, hQ⟩
  unfold Func.wp full_delete_binary_body
  c0_hcall (Spec.has_full_delete_bin_side hΓ)
  · exact ⟨c, s, R, rfl, hlen, fun hlt => hlay.bounds a.toNat hlt, hm,
      fun wvec1 wstk1 wu1 m1 hlen1 _ _ _ _ _ hlay_fn1 hmode_fn1 hm1 => by
        let s1 : FullState := { s with core := { s.core with
          wvec := wvec1, wstk := wstk1, wusable := wu1 } }
        have hlay1 : WatchStackLayout s1.core := hlay_fn1 hlay
        c0_hcall (Spec.has_full_delete_bin_side hΓ)
        · exact ⟨c, s1, R, rfl, hlen1, fun hlt => hlay1.bounds b.toNat hlt, hm1,
            fun wvec2 wstk2 wu2 m2 hlen2 _ _ _ _ _ hlay_fn2 hmode_fn2 hm2 => by
              let s2 : FullState := { s1 with core := { s1.core with
                wvec := wvec2, wstk := wstk2, wusable := wu2 } }
              have hlay2 : WatchStackLayout s2.core := hlay_fn2 hlay1
              have hfl_len : s2.core.flags.length = c.max_vars := hlen2.core_ok.flags_len
              have ha_fl := dbin_idx_lt hfl_len ha
              have hb_fl := dbin_idx_lt hfl_len hb
              have hmx := c.hmaxv; unfold dimacsBound at hmx
              c0_hstraight
              let InvA : Val i32 → Mem 64 → Prop := fun _ ma => ma = m2
              apply wp_join_state (fun v : Val i32 => (v, ())) InvA
              · intro _ v ma hma
                dsimp only [InvA] at hma
                rw [hma]
                clear ma hma
                c0_hstraight
                let InvB : Val i32 → Mem 64 → Prop := fun _ mb =>
                  ∃ flags1 : List (BitVec 32), flags1.length = c.max_vars ∧
                    (FullMem c { s2 with core := { s2.core with flags := flags1 } } ⋆ R) mb
                apply wp_join_state (fun v' : Val i32 => (v', ())) InvB
                · intro _ v' mb ⟨flags1, hfl1, hmb⟩
                  have hb_fl1 : (BitVec.setWidth 64 (b >>> 1)).toNat < flags1.length := by
                    rw [hfl1, ← hfl_len]; exact hb_fl
                  c0_hstraight
                  apply wp_join0 (fun mr =>
                    ∃ (flags' : List (BitVec 32)) (nb' : BitVec 64), flags'.length = c.max_vars ∧
                      (FullMem c { s2 with core := { s2.core with
                        flags := flags', num_binary := nb' } } ⋆ R) mr)
                  · intro _ mr ⟨flags', nb', hfl', hmr⟩
                    c0_hsteps
                    have hs2_fin :
                        ({ s2 with core := { s2.core with
                          flags := flags', num_binary := nb' } } : FullState) =
                        ({ s with core := { s.core with
                          flags := flags', wvec := wvec2, wstk := wstk2,
                          wusable := wu2, num_binary := nb' } } : FullState) := rfl
                    rw [hs2_fin] at hmr
                    refine hQ flags' wvec2 wstk2 wu2 nb' mr ?_ ?_ ?_ hmr
                    · exact ⟨{ hlen2.core_ok with flags_len := hfl' }, hlen2.scratch_ok⟩
                    · exact ⟨hlay2.bounds, hlay2.pos_off, hlay2.disjoint, hlay2.no_sentinel⟩
                    · intro F_cur hmode
                      exact (hmode_fn2 F_cur (hmode_fn1 F_cur hmode)).with_wstk rfl rfl rfl rfl rfl
                        fun _ h => h
                  · intro J_ret hJ_ret
                    c0_hsplit <;> c0_hsteps
                    · have hm_new := ‹(FullMem c { s2 with core := { s2.core with
                          flags := flags1.set _ _, num_binary := _ } } ⋆ R) _›
                      exact hJ_ret _ ⟨_, _, by rw [List.length_set, hfl1], hm_new⟩
                    · have hm_old := ‹(FullMem c { s2 with core := { s2.core with
                          flags := flags1.set _ _ } } ⋆ R) _›
                      exact hJ_ret _ ⟨_, _, by rw [List.length_set, hfl1], hm_old⟩
                · intro J_b hJ_b
                  c0_hsplit <;> c0_hsteps <;>
                    (have hm_new := ‹(FullMem c { s2 with core := { s2.core with
                          flags := s2.core.flags.set _ _ } } ⋆ R) _›
                     exact hJ_b _ _ ⟨_, by rw [List.length_set, hfl_len], hm_new⟩)
              · intro J_a hJ_a
                c0_hsplit <;> c0_hsteps <;> exact hJ_a _ _ rfl⟩⟩

end

end LeanQbe.T.Examples.Kissat.Proof.Watch
