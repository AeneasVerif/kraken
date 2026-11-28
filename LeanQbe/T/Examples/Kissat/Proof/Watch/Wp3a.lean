/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Watch.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Watch.Helpers
public import LeanQbe.T.Examples.Kissat.Src.Watch

import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts1
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics1
import LeanQbe.T.Examples.Kissat.Proof.Spec.MemBridges
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.C0Grind
import LeanQbe.T.Logic.ProofKit

/-! # Watch WP Proofs Part 3a: Helpers & Invariants for `full_watch_push*`

Shared invariants, bounds/arithmetic lemmas, and case finalizers imported by
`Proof.Watch.Wp3` and `Proof.Watch.Wp4`. -/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Watch

open Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Grind
open LeanQbe.T.ProofKit
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Watch
open LeanQbe.T.Examples.Kissat.Proof.Spec
open Kraken.Bedrock2.Test
open scoped FullArenaTactics

public section

/-! ## 1. Watch Offset / Size, `WatchPresAll`, & `WPushPost` -/

@[expose] def wOff (wvec : List (BitVec 32)) (l : Nat) : Nat :=
  (wvec[2 * l]?.getD 0#32).toNat

@[expose] def wSz (wvec : List (BitVec 32)) (l : Nat) : Nat :=
  (wvec[2 * l + 1]?.getD 0#32).toNat

@[expose] def WatchPresAll (s s' : FullState) : Prop :=
  s'.core.cur_vars = s.core.cur_vars ∧
  ∀ l < 2 * s.core.cur_vars,
    wSz s'.core.wvec l = fullWatchSize s l ∧
    ∀ k < fullWatchSize s l, s'.core.wstk[wOff s'.core.wvec l + k]? =
      s.core.wstk[fullWatchOff s l + k]?

theorem watchPresAll_refl (s : FullState) : WatchPresAll s s :=
  ⟨rfl, fun _ _ => ⟨rfl, fun _ _ => rfl⟩⟩

theorem watchPresAll_trans {s1 s2 s3 : FullState}
    (h12 : WatchPresAll s1 s2) (h23 : WatchPresAll s2 s3) : WatchPresAll s1 s3 :=
  ⟨h23.1.trans h12.1, fun l hl => by
    have ⟨hs12, hst12⟩ := h12.2 l hl
    have ⟨hs23, hst23⟩ := h23.2 l (h12.1 ▸ hl)
    have hs12' : fullWatchSize s2 l = fullWatchSize s1 l := hs12
    have hs23' : fullWatchSize s3 l = fullWatchSize s2 l := hs23
    exact ⟨hs23'.trans hs12', fun k hk => (hst23 k (hs12' ▸ hk)).trans (hst12 k hk)⟩⟩

@[expose] def wpushSet (s : FullState) (wv ws wso : List (BitVec 32)) (wl : Nat) (wu : BitVec 64) :
    FullState :=
  { s with
    core := { s.core with wvec := wv, wstk := ws, wlen := wl, wusable := wu }
    scratch := { s.scratch with wsort := wso } }

@[expose] def WPushPost (c : FullCfg) (s : FullState) (R : Mem 64 → Prop)
    (lit w0 w1 cnt : BitVec 32) (Q : Post [Ty.bool]) : Prop :=
  ∀ (ok : Bool) wvec' wstk' wlen' wusable' wsort' m',
    let s' := wpushSet s wvec' wstk' wsort' wlen' wusable'
    s'.LengthsOk c → WatchStackLayout s'.core →
    (∀ l < 2 * s.core.cur_vars, l ≠ lit.toNat →
      fullWatchSize s' l = fullWatchSize s l ∧
      ∀ k < fullWatchSize s l,
        s'.core.wstk[fullWatchOff s' l + k]? = s.core.wstk[fullWatchOff s l + k]?) →
    (ok = true →
      lit.toNat < 2 * s.core.cur_vars ∧ (cnt.toNat = 1 ∨ cnt.toNat = 2) ∧
      fullWatchSize s' lit.toNat = fullWatchSize s lit.toNat + cnt.toNat ∧
      (∀ k < fullWatchSize s lit.toNat,
        s'.core.wstk[fullWatchOff s' lit.toNat + k]? =
          s.core.wstk[fullWatchOff s lit.toNat + k]?) ∧
      s'.core.wstk[fullWatchOff s' lit.toNat + fullWatchSize s lit.toNat]? = some w0 ∧
      (cnt.toNat = 2 →
        s'.core.wstk[fullWatchOff s' lit.toNat + fullWatchSize s lit.toNat + 1]? = some w1)) →
    (ok = false →
      (lit.toNat < 2 * s.core.cur_vars →
        fullWatchSize s' lit.toNat = fullWatchSize s lit.toNat ∧
        ∀ k < fullWatchSize s lit.toNat,
          s'.core.wstk[fullWatchOff s' lit.toNat + k]? =
            s.core.wstk[fullWatchOff s lit.toNat + k]?) ∧
      (2 * s.core.cur_vars ≤ lit.toNat ∨ (cnt.toNat ≠ 1 ∧ cnt.toNat ≠ 2) ∨ s' = s ∨
        wusable' = 0#64)) →
    (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

/-! ## 2. Layout & Push Finalizers -/

theorem wpush_sentinel_range_disjoint {k1 : FullCoreState} (hlay1 : WatchStackLayout k1)
    {dst len : Nat} (_hdst : 1 ≤ dst) (hlen : 0 < len)
    (hnil : ∀ off, dst ≤ off → off < dst + len → k1.wstk[off]? = some 0xFFFFFFFF#32) :
    ∀ j < 2 * k1.cur_vars, 0 < fullWatchSizeCore k1 j →
      fullWatchOffCore k1 j + fullWatchSizeCore k1 j ≤ dst ∨
      dst + len ≤ fullWatchOffCore k1 j := by
  intro j hj hpos
  by_cases h1 : fullWatchOffCore k1 j + fullWatchSizeCore k1 j ≤ dst
  · exact Or.inl h1
  · exact Or.inr (Nat.le_of_not_lt fun hlt => by
      by_cases h3 : dst ≤ fullWatchOffCore k1 j
      · exact hlay1.no_sentinel j hj 0 hpos (by
          simpa using hnil (fullWatchOffCore k1 j) h3 hlt)
      · have hlt2 : fullWatchOffCore k1 j < dst := Nat.lt_of_not_le h3
        have hns := hlay1.no_sentinel j hj (dst - fullWatchOffCore k1 j) (by omega)
        rw [show fullWatchOffCore k1 j + (dst - fullWatchOffCore k1 j) = dst by omega] at hns
        exact hns (hnil dst (Nat.le_refl dst) (by omega)))

theorem wpush_ok_post {c : FullCfg} {s s2 : FullState} {R : Mem 64 → Prop}
    {lit w0 w1 cnt : BitVec 32} {Q : Post [Ty.bool]} (hQ : WPushPost c s R lit w0 w1 cnt Q)
    (hlay2 : WatchStackLayout s2.core) (hpres : WatchPresAll s s2)
    (hlit : lit.toNat < 2 * s.core.cur_vars) (hc12 : cnt.toNat = 1 ∨ cnt.toNat = 2)
    (hw0 : cnt.toNat = 1 → w0 ≠ 0xFFFFFFFF#32)
    (hw1 : cnt.toNat = 2 → w0 ≠ 0xFFFFFFFF#32 ∧ w1 ≠ 0xFFFFFFFF#32)
    {dst wlen' : Nat} {wvec' wstk' wsort' : List (BitVec 32)} (wusable' : BitVec 64) {m' : Mem 64}
    (hlen' : (wpushSet s wvec' wstk' wsort' wlen' wusable').LengthsOk c)
    (hwlen_le : s2.core.wlen ≤ wlen') (hdst1 : 1 ≤ dst)
    (hdst_le : dst + (wSz s2.core.wvec lit.toNat + cnt.toNat) ≤ wlen')
    (hother_wv : ∀ j < 2 * s.core.cur_vars, j ≠ lit.toNat →
      wOff wvec' j = wOff s2.core.wvec j ∧ wSz wvec' j = wSz s2.core.wvec j)
    (hlit_off : wOff wvec' lit.toNat = dst)
    (hlit_sz : wSz wvec' lit.toNat = wSz s2.core.wvec lit.toNat + cnt.toNat)
    (hdisj : ∀ j < 2 * s.core.cur_vars, j ≠ lit.toNat → 0 < wSz s2.core.wvec j →
      wOff s2.core.wvec j + wSz s2.core.wvec j ≤ dst ∨
      dst + (wSz s2.core.wvec lit.toNat + cnt.toNat) ≤ wOff s2.core.wvec j)
    (hother_st : ∀ j < 2 * s.core.cur_vars, j ≠ lit.toNat → ∀ k < wSz s2.core.wvec j,
      wstk'[wOff s2.core.wvec j + k]? = s2.core.wstk[wOff s2.core.wvec j + k]?)
    (hcopy : ∀ k < wSz s2.core.wvec lit.toNat,
      wstk'[dst + k]? = s2.core.wstk[wOff s2.core.wvec lit.toNat + k]?)
    (hat0 : wstk'[dst + wSz s2.core.wvec lit.toNat]? = some w0)
    (hat1 : cnt.toNat = 2 → wstk'[dst + wSz s2.core.wvec lit.toNat + 1]? = some w1)
    (hm' : (FullMem c (wpushSet s wvec' wstk' wsort' wlen' wusable') ⋆ R) m') :
    Q (true, ()) m' := by
  have hcv2 := hpres.1; have hlit2 : lit.toNat < 2 * s2.core.cur_vars := hcv2 ▸ hlit
  have hsz2 : wSz s2.core.wvec lit.toNat = fullWatchSizeCore s.core lit.toNat :=
    (hpres.2 lit.toNat hlit).1
  have hne0 : w0 ≠ 0xFFFFFFFF#32 := by
    rcases hc12 with h | h; exact hw0 h; exact (hw1 h).1
  let s' := wpushSet s wvec' wstk' wsort' wlen' wusable'
  have hoff_l : fullWatchOffCore s'.core lit.toNat = dst := hlit_off
  have hsz_l : fullWatchSizeCore s'.core lit.toNat = wSz s2.core.wvec lit.toNat + cnt.toNat :=
    hlit_sz
  have hoff_o (j) (hj : j < 2 * s.core.cur_vars) (hne : j ≠ lit.toNat) :
      fullWatchOffCore s'.core j = fullWatchOffCore s2.core j := (hother_wv j hj hne).1
  have hsz_o (j) (hj : j < 2 * s.core.cur_vars) (hne : j ≠ lit.toNat) :
      fullWatchSizeCore s'.core j = fullWatchSizeCore s2.core j := (hother_wv j hj hne).2
  have hlay' : WatchStackLayout s'.core := by
    refine ⟨fun l hl => ?_, fun l hl hp => ?_, fun l1 l2 h1 h2 hne hp1 hp2 => ?_,
      fun l hl k hk => ?_⟩
    · by_cases hll : l = lit.toNat
      · subst hll; rw [hoff_l, hsz_l]; exact hdst_le
      · rw [hoff_o l hl hll, hsz_o l hl hll]
        exact Nat.le_trans (hlay2.bounds l (hcv2 ▸ hl)) hwlen_le
    · by_cases hll : l = lit.toNat
      · subst hll; rw [hoff_l]; exact hdst1
      · rw [hsz_o l hl hll] at hp; rw [hoff_o l hl hll]; exact hlay2.pos_off l (hcv2 ▸ hl) hp
    · by_cases hl1 : l1 = lit.toNat
      · subst hl1; rw [hsz_o l2 h2 hne.symm] at hp2
        rw [hoff_l, hsz_l, hoff_o l2 h2 hne.symm, hsz_o l2 h2 hne.symm]
        exact (hdisj l2 h2 hne.symm hp2).symm
      · by_cases hl2 : l2 = lit.toNat
        · subst hl2; rw [hsz_o l1 h1 hl1] at hp1
          rw [hoff_o l1 h1 hl1, hsz_o l1 h1 hl1, hoff_l, hsz_l]; exact hdisj l1 h1 hl1 hp1
        · rw [hsz_o l1 h1 hl1] at hp1; rw [hsz_o l2 h2 hl2] at hp2
          rw [hoff_o l1 h1 hl1, hsz_o l1 h1 hl1, hoff_o l2 h2 hl2, hsz_o l2 h2 hl2]
          exact hlay2.disjoint l1 l2 (hcv2 ▸ h1) (hcv2 ▸ h2) hne hp1 hp2
    · by_cases hll : l = lit.toNat
      · subst hll; rw [hsz_l] at hk
        change wstk'[fullWatchOffCore s'.core lit.toNat + k]? ≠ _; rw [hoff_l]
        by_cases hks : k < wSz s2.core.wvec lit.toNat
        · rw [hcopy k hks]; exact hlay2.no_sentinel lit.toNat hlit2 k hks
        · by_cases hk0 : k = wSz s2.core.wvec lit.toNat
          · subst hk0; rw [hat0]; exact fun heq => hne0 (Option.some.inj heq)
          · have hc2 : cnt.toNat = 2 := by omega
            have hk1 : k = wSz s2.core.wvec lit.toNat + 1 := by omega
            subst hk1; rw [← Nat.add_assoc, hat1 hc2]
            exact fun heq => (hw1 hc2).2 (Option.some.inj heq)
      · rw [hsz_o l hl hll] at hk; rw [hoff_o l hl hll]
        change wstk'[wOff s2.core.wvec l + k]? ≠ _
        rw [hother_st l hl hll k hk]; exact hlay2.no_sentinel l (hcv2 ▸ hl) k hk
  refine hQ true wvec' wstk' wlen' wusable' wsort' m' hlen' hlay' (fun l hl hne => ?_)
    (fun _ => ⟨hlit, hc12, (by change wSz wvec' lit.toNat = _; rw [hlit_sz, hsz2]),
      (fun k hk => by change wstk'[wOff wvec' lit.toNat + k]? = _
                      rw [hlit_off]
                      exact (hcopy k (hsz2 ▸ hk)).trans ((hpres.2 lit.toNat hlit).2 k hk)),
      (by change wstk'[wOff wvec' lit.toNat + fullWatchSizeCore s.core lit.toNat]? = _
          rw [hlit_off, ← hsz2]; exact hat0),
      (fun hc2 => by
        change wstk'[wOff wvec' lit.toNat + fullWatchSizeCore s.core lit.toNat + 1]? = _
        rw [hlit_off, ← hsz2]; exact hat1 hc2)⟩)
    (fun h => absurd h (by decide)) hm'
  have ⟨hp1, hp2⟩ := hpres.2 l hl
  refine ⟨(hsz_o l hl hne).trans hp1, fun k hk => ?_⟩
  change wstk'[fullWatchOffCore s'.core l + k]? = _
  rw [hoff_o l hl hne]; exact (hother_st l hl hne k (hp1 ▸ hk)).trans (hp2 k hk)

theorem wpush_lengthsOk {c : FullCfg} {s : FullState}
    (hlen : s.LengthsOk c) {wvec' wstk' wsort' : List (BitVec 32)} {wlen' : Nat}
    {wusable' : BitVec 64}
    (hwv : wvec'.length = 4 * c.max_vars) (hws : wstk'.length = c.wcap)
    (hwl : wlen' ≤ c.wcap) (hwso : wsort'.length = 2 * c.max_vars) :
    (wpushSet s wvec' wstk' wsort' wlen' wusable').LengthsOk c :=
  ⟨{ hlen.core_ok with wvec_len := hwv, wstk_len_arr := hws, wlen_le := hwl },
    { hlen.scratch_ok with wsort_len := hwso }⟩

theorem wpush_wcap_lt32 (c : FullCfg) : c.wcap < 2 ^ 32 :=
  Nat.lt_of_lt_of_le c.hwcap (by decide)

theorem wpush_init_wlen0 {c : FullCfg} {s : FullState}
    (hlen : s.LengthsOk c) (hlay : WatchStackLayout s.core)
    (hw0 : s.core.wlen = 0) (hcap : 1 ≤ c.wcap) :
    let s1 : FullState :=
      { s with core := { s.core with wstk := s.core.wstk.set 0 0#32, wlen := 1 } }
    s1.LengthsOk c ∧ WatchStackLayout s1.core ∧ WatchPresAll s s1 := by
  intro s1
  have hsz0 : ∀ l < 2 * s.core.cur_vars, fullWatchSizeCore s.core l = 0 := fun l hl => by
    have hb := hlay.bounds l hl; rw [hw0] at hb; omega
  have hlen1 : s1.LengthsOk c :=
    ⟨{ hlen.core_ok with wstk_len_arr := by simp [s1, hlen.core_ok.wstk_len_arr], wlen_le := hcap },
      hlen.scratch_ok⟩
  have hlay1 : WatchStackLayout s1.core := ⟨
    fun l hl => by
      have hb := hlay.bounds l hl
      change fullWatchOffCore s.core l + fullWatchSizeCore s.core l ≤ 1; omega,
    fun l hl hp => absurd hp (by change ¬0 < fullWatchSizeCore s.core l; rw [hsz0 l hl]; omega),
    fun l1 _ h1 _ _ hp1 _ =>
      absurd hp1 (by change ¬0 < fullWatchSizeCore s.core l1; rw [hsz0 l1 h1]; omega),
    fun l hl _ hidx =>
      absurd hidx (by change ¬_ < fullWatchSizeCore s.core l; rw [hsz0 l hl]; omega)⟩
  refine ⟨hlen1, hlay1, ⟨rfl, fun l hl => ⟨rfl, fun k hk => ?_⟩⟩⟩
  exact absurd hk (by change ¬k < fullWatchSizeCore s.core l; rw [hsz0 l hl]; omega)

theorem wpush_fail_post {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {lit w0 w1 cnt : BitVec 32} {Q : Post [Ty.bool]} (hQ : WPushPost c s R lit w0 w1 cnt Q)
    (wvec' wstk' wsort' : List (BitVec 32)) (wlen' : Nat) (wusable' : BitVec 64)
    {m' : Mem 64}
    (hlen' : (wpushSet s wvec' wstk' wsort' wlen' wusable').LengthsOk c)
    (hlay' : WatchStackLayout (wpushSet s wvec' wstk' wsort' wlen' wusable').core)
    (hpres : WatchPresAll s (wpushSet s wvec' wstk' wsort' wlen' wusable'))
    (hwhy : 2 * s.core.cur_vars ≤ lit.toNat ∨ (cnt.toNat ≠ 1 ∧ cnt.toNat ≠ 2) ∨
      wpushSet s wvec' wstk' wsort' wlen' wusable' = s ∨ wusable' = 0#64)
    (hm' : (FullMem c (wpushSet s wvec' wstk' wsort' wlen' wusable') ⋆ R) m') :
    Q (false, ()) m' :=
  hQ false wvec' wstk' wlen' wusable' wsort' m' hlen' hlay'
    (fun l hl _ => hpres.2 l hl) (fun h => absurd h (by decide))
    (fun _ => ⟨fun hlt => hpres.2 lit.toNat hlt, hwhy⟩) hm'

private theorem wpush_wvec_set_sz {wv : List (BitVec 32)} {lit : Nat} (sz' : BitVec 32)
    (hwv2 : 2 * lit + 1 < wv.length) :
    let wv' := wv.set (2 * lit + 1) sz'
    wv'.length = wv.length ∧
    (∀ j, j ≠ lit → wOff wv' j = wOff wv j ∧ wSz wv' j = wSz wv j) ∧
    wOff wv' lit = wOff wv lit ∧ wSz wv' lit = sz'.toNat := by
  refine ⟨List.length_set, fun j hne => ⟨congrArg BitVec.toNat (wvec_set_size_other hne sz').1,
    congrArg BitVec.toNat (wvec_set_size_other hne sz').2⟩,
    congrArg BitVec.toNat (wvec_set_size_off_self hwv2 sz'),
    congrArg BitVec.toNat (wvec_set_size_sz_self hwv2 sz')⟩

private theorem wpush_wvec_set_off_sz {wv : List (BitVec 32)} {lit : Nat}
    (off' sz' : BitVec 32) (hwv1 : 2 * lit < wv.length) (hwv2 : 2 * lit + 1 < wv.length) :
    let wv' := (wv.set (2 * lit) off').set (2 * lit + 1) sz'
    wv'.length = wv.length ∧
    (∀ j, j ≠ lit → wOff wv' j = wOff wv j ∧ wSz wv' j = wSz wv j) ∧
    wOff wv' lit = off'.toNat ∧ wSz wv' lit = sz'.toNat := by
  have h1 := wvec_set_even_eq (wvec := wv) (l := lit) (v := off') hwv1
  have h2 := wvec_set_odd_eq (wvec := wv.set (2 * lit) off') (l := lit) (v := sz')
    (by simp [hwv2])
  exact ⟨by simp, fun j hne => ⟨by simp [wOff, (h2 j).1, (h1 j).2.1 hne],
    by simp [wSz, (h2 j).2.1 hne, (h1 j).1]⟩,
    by simp [wOff, (h2 lit).1, (h1 lit).2.2], by simp [wSz, (h2 lit).2.2]⟩

private theorem wpush_wvec_lt2 {c : FullCfg} {k : FullCoreState} {lit : Nat}
    (hk : k.LengthsOk c) (hlit : lit < 2 * k.cur_vars) :
    2 * lit < k.wvec.length ∧ 2 * lit + 1 < k.wvec.length ∧ k.wlen < 2 ^ 32 := by
  have := hk.cur_vars_le; have := hk.wvec_len; have := hk.wlen_le
  have := wpush_wcap_lt32 c; omega

theorem wpush_caseA_fin {c : FullCfg} {s s2 : FullState} {R : Mem 64 → Prop}
    {lit w0 w1 cnt : BitVec 32} {Q : Post [Ty.bool]}
    (hQ : WPushPost c s R lit w0 w1 cnt Q) (hlen : s.LengthsOk c) (hlen2 : s2.LengthsOk c)
    (hlay2 : WatchStackLayout s2.core) (hpres : WatchPresAll s s2)
    (hlit : lit.toNat < 2 * s.core.cur_vars) (hc12 : cnt.toNat = 1 ∨ cnt.toNat = 2)
    (hw0 : cnt.toNat = 1 → w0 ≠ 0xFFFFFFFF#32)
    (hw1 : cnt.toNat = 2 → w0 ≠ 0xFFFFFFFF#32 ∧ w1 ≠ 0xFFFFFFFF#32)
    (hs2_so : wOff s2.core.wvec lit.toNat = 0 ∨ wSz s2.core.wvec lit.toNat = 0)
    (hwlen1 : 1 ≤ s2.core.wlen) (hfit : s2.core.wlen + cnt.toNat ≤ c.wcap)
    {wstk' wsort' : List (BitVec 32)} (wusable' : BitVec 64) {m' : Mem 64}
    (hws_len : wstk'.length = c.wcap) (hwso_len : wsort'.length = 2 * c.max_vars)
    (hws_lt : ∀ i < s2.core.wlen, wstk'[i]? = s2.core.wstk[i]?)
    (hat0 : wstk'[s2.core.wlen]? = some w0)
    (hat1 : cnt.toNat = 2 → wstk'[s2.core.wlen + 1]? = some w1)
    (wvec' : List (BitVec 32))
    (hwvec'_eq : wvec' = (s2.core.wvec.set (2 * lit.toNat) (BitVec.ofNat 32 s2.core.wlen)).set
      (2 * lit.toNat + 1) cnt)
    (hm' : (FullMem c (wpushSet s wvec' wstk' wsort' (s2.core.wlen + cnt.toNat) wusable') ⋆ R) m') :
    Q (true, ()) m' := by
  have hcv2 := hpres.1; have hlit2 : lit.toNat < 2 * s2.core.cur_vars := hcv2 ▸ hlit
  have hsz0 : wSz s2.core.wvec lit.toNat = 0 := by
    rcases hs2_so with h0 | h0
    · by_cases hne : wSz s2.core.wvec lit.toNat = 0; exact hne
      have hp := hlay2.pos_off lit.toNat hlit2 (Nat.pos_of_ne_zero hne)
      change wOff s2.core.wvec lit.toNat ≥ 1 at hp; omega
    · exact h0
  obtain ⟨hwv1, hwv2, hwlen32⟩ := wpush_wvec_lt2 hlen2.core_ok hlit2
  obtain ⟨hwv'_len, hoth_w, hoff_w, hsz_w⟩ :=
    wpush_wvec_set_off_sz (BitVec.ofNat 32 s2.core.wlen) cnt hwv1 hwv2
  subst hwvec'_eq
  have hlen' := wpush_lengthsOk (wlen' := s2.core.wlen + cnt.toNat) (wusable' := wusable')
    hlen (hwv'_len.trans hlen2.core_ok.wvec_len) hws_len hfit hwso_len
  refine wpush_ok_post hQ hlay2 hpres hlit hc12 hw0 hw1 wusable' hlen' (Nat.le_add_right _ _)
    hwlen1 (by rw [hsz0]; omega) (fun j _ hne => hoth_w j hne)
    (by rw [hoff_w, bv32_eq_nat _ hwlen32 rfl]) (by rw [hsz_w, hsz0, Nat.zero_add])
    (fun j hj _ _ => Or.inl (hlay2.bounds j (hcv2 ▸ hj)))
    (fun j hj _ k hk => hws_lt _
      (Nat.lt_of_lt_of_le (Nat.add_lt_add_left hk _) (hlay2.bounds j (hcv2 ▸ hj))))
    (fun k hk => absurd hk (by omega)) (by rwa [hsz0, Nat.add_zero])
    (fun hc2 => by rw [hsz0, Nat.add_zero]; exact hat1 hc2) hm'

theorem wpush_caseB_fin {c : FullCfg} {s s2 : FullState} {R : Mem 64 → Prop}
    {lit w0 w1 cnt : BitVec 32} {Q : Post [Ty.bool]}
    (hQ : WPushPost c s R lit w0 w1 cnt Q) (hlen : s.LengthsOk c) (hlen2 : s2.LengthsOk c)
    (hlay2 : WatchStackLayout s2.core) (hpres : WatchPresAll s s2)
    (hlit : lit.toNat < 2 * s.core.cur_vars) (hc12 : cnt.toNat = 1 ∨ cnt.toNat = 2)
    (hw0 : cnt.toNat = 1 → w0 ≠ 0xFFFFFFFF#32)
    (hw1 : cnt.toNat = 2 → w0 ≠ 0xFFFFFFFF#32 ∧ w1 ≠ 0xFFFFFFFF#32)
    (hoff1 : 1 ≤ wOff s2.core.wvec lit.toNat)
    (hend : wOff s2.core.wvec lit.toNat + wSz s2.core.wvec lit.toNat = s2.core.wlen)
    (hfit : s2.core.wlen + cnt.toNat ≤ c.wcap)
    {wstk' wsort' : List (BitVec 32)} (wusable' : BitVec 64) {m' : Mem 64}
    (hws_len : wstk'.length = c.wcap) (hwso_len : wsort'.length = 2 * c.max_vars)
    (hws_lt : ∀ i < s2.core.wlen, wstk'[i]? = s2.core.wstk[i]?)
    (hat0 : wstk'[s2.core.wlen]? = some w0)
    (hat1 : cnt.toNat = 2 → wstk'[s2.core.wlen + 1]? = some w1)
    (wvec' : List (BitVec 32))
    (hwvec'_eq : wvec' = s2.core.wvec.set (2 * lit.toNat + 1)
      (BitVec.ofNat 32 (wSz s2.core.wvec lit.toNat + cnt.toNat)))
    (hm' : (FullMem c (wpushSet s wvec' wstk' wsort' (s2.core.wlen + cnt.toNat) wusable') ⋆ R) m') :
    Q (true, ()) m' := by
  have hcv2 := hpres.1; have hlit2 : lit.toNat < 2 * s2.core.cur_vars := hcv2 ▸ hlit
  obtain ⟨_, hwv2, _⟩ := wpush_wvec_lt2 hlen2.core_ok hlit2
  have hsz32 : wSz s2.core.wvec lit.toNat + cnt.toNat < 2 ^ 32 :=
    Nat.lt_of_le_of_lt (by omega) (wpush_wcap_lt32 c)
  obtain ⟨hwv'_len, hoth_w, hoff_w, hsz_w⟩ :=
    wpush_wvec_set_sz (BitVec.ofNat 32 (wSz s2.core.wvec lit.toNat + cnt.toNat)) hwv2
  subst hwvec'_eq
  have hlen' := wpush_lengthsOk (wlen' := s2.core.wlen + cnt.toNat) (wusable' := wusable')
    hlen (hwv'_len.trans hlen2.core_ok.wvec_len) hws_len hfit hwso_len
  refine wpush_ok_post hQ hlay2 hpres hlit hc12 hw0 hw1 wusable' hlen' (Nat.le_add_right _ _)
    hoff1 (by omega) (fun j _ hne => hoth_w j hne) hoff_w
    (by rw [hsz_w, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsz32]) ?_
    (fun j hj _ k hk => hws_lt _
      (Nat.lt_of_lt_of_le (Nat.add_lt_add_left hk _) (hlay2.bounds j (hcv2 ▸ hj))))
    (fun k hk => hws_lt _ (by omega)) (by rw [hend]; exact hat0)
    (fun hc2 => by rw [hend]; exact hat1 hc2) hm'
  · intro j hj hne hpj; have hb := hlay2.bounds j (hcv2 ▸ hj)
    change wOff s2.core.wvec j + wSz s2.core.wvec j ≤ s2.core.wlen at hb
    by_cases hszp : 0 < wSz s2.core.wvec lit.toNat
    · rcases hlay2.disjoint j lit.toNat (hcv2 ▸ hj) hlit2 hne hpj hszp with h | h
      · exact Or.inl h
      · change wOff s2.core.wvec lit.toNat + wSz s2.core.wvec lit.toNat ≤ wOff s2.core.wvec j
          at h; omega
    · exact Or.inl (by omega)

theorem wpush_caseC_fin {c : FullCfg} {s s2 : FullState} {R : Mem 64 → Prop}
    {lit w0 w1 cnt : BitVec 32} {Q : Post [Ty.bool]}
    (hQ : WPushPost c s R lit w0 w1 cnt Q) (hlen : s.LengthsOk c) (hlen2 : s2.LengthsOk c)
    (hlay2 : WatchStackLayout s2.core) (hpres : WatchPresAll s s2)
    (hlit : lit.toNat < 2 * s.core.cur_vars) (hc12 : cnt.toNat = 1 ∨ cnt.toNat = 2)
    (hw0 : cnt.toNat = 1 → w0 ≠ 0xFFFFFFFF#32)
    (hw1 : cnt.toNat = 2 → w0 ≠ 0xFFFFFFFF#32 ∧ w1 ≠ 0xFFFFFFFF#32)
    (hoff1 : 1 ≤ wOff s2.core.wvec lit.toNat)
    (hend_le : wOff s2.core.wvec lit.toNat + wSz s2.core.wvec lit.toNat + cnt.toNat ≤ s2.core.wlen)
    (hsent : ∀ k < cnt.toNat,
      s2.core.wstk[wOff s2.core.wvec lit.toNat + wSz s2.core.wvec lit.toNat + k]? =
        some 0xFFFFFFFF#32)
    {wstk' wsort' : List (BitVec 32)} (wusable' : BitVec 64) {m' : Mem 64}
    (hws_len : wstk'.length = c.wcap) (hwso_len : wsort'.length = 2 * c.max_vars)
    (hws_out : ∀ i, i < wOff s2.core.wvec lit.toNat + wSz s2.core.wvec lit.toNat ∨
      wOff s2.core.wvec lit.toNat + wSz s2.core.wvec lit.toNat + cnt.toNat ≤ i →
      wstk'[i]? = s2.core.wstk[i]?)
    (hat0 : wstk'[wOff s2.core.wvec lit.toNat + wSz s2.core.wvec lit.toNat]? = some w0)
    (hat1 : cnt.toNat = 2 →
      wstk'[wOff s2.core.wvec lit.toNat + wSz s2.core.wvec lit.toNat + 1]? = some w1)
    (wvec' : List (BitVec 32))
    (hwvec'_eq : wvec' = s2.core.wvec.set (2 * lit.toNat + 1)
      (BitVec.ofNat 32 (wSz s2.core.wvec lit.toNat + cnt.toNat)))
    (hm' : (FullMem c (wpushSet s wvec' wstk' wsort' s2.core.wlen wusable') ⋆ R) m') :
    Q (true, ()) m' := by
  have hcv2 := hpres.1; have hlit2 : lit.toNat < 2 * s2.core.cur_vars := hcv2 ▸ hlit
  obtain ⟨_, hwv2, _⟩ := wpush_wvec_lt2 hlen2.core_ok hlit2
  have hsz32 : wSz s2.core.wvec lit.toNat + cnt.toNat < 2 ^ 32 :=
    Nat.lt_of_le_of_lt (Nat.le_trans (by omega) hlen2.core_ok.wlen_le) (wpush_wcap_lt32 c)
  obtain ⟨hwv'_len, hoth_w, hoff_w, hsz_w⟩ :=
    wpush_wvec_set_sz (BitVec.ofNat 32 (wSz s2.core.wvec lit.toNat + cnt.toNat)) hwv2
  subst hwvec'_eq
  have hdisj_sent := wpush_sentinel_range_disjoint hlay2
    (dst := wOff s2.core.wvec lit.toNat + wSz s2.core.wvec lit.toNat) (len := cnt.toNat)
    (by omega) (by omega) (fun off hlo hhi => by
      have := hsent (off - (wOff s2.core.wvec lit.toNat + wSz s2.core.wvec lit.toNat)) (by omega)
      rwa [show wOff s2.core.wvec lit.toNat + wSz s2.core.wvec lit.toNat +
        (off - (wOff s2.core.wvec lit.toNat + wSz s2.core.wvec lit.toNat)) = off by omega] at this)
  have hdisj : ∀ j < 2 * s.core.cur_vars, j ≠ lit.toNat → 0 < wSz s2.core.wvec j →
      wOff s2.core.wvec j + wSz s2.core.wvec j ≤ wOff s2.core.wvec lit.toNat ∨
      wOff s2.core.wvec lit.toNat + (wSz s2.core.wvec lit.toNat + cnt.toNat) ≤
        wOff s2.core.wvec j := by
    intro j hj hne hpj
    rcases hdisj_sent j (hcv2 ▸ hj) hpj with hs1 | hs2
    · by_cases hszp : 0 < wSz s2.core.wvec lit.toNat
      · rcases hlay2.disjoint j lit.toNat (hcv2 ▸ hj) hlit2 hne hpj hszp with h1 | h2
        · exact Or.inl h1
        · change wOff s2.core.wvec lit.toNat + wSz s2.core.wvec lit.toNat ≤ wOff s2.core.wvec j
            at h2
          change wOff s2.core.wvec j + wSz s2.core.wvec j ≤
            wOff s2.core.wvec lit.toNat + wSz s2.core.wvec lit.toNat at hs1
          change 0 < wSz s2.core.wvec j at hpj; omega
      · have hsz0 : wSz s2.core.wvec lit.toNat = 0 := Nat.eq_zero_of_not_pos hszp
        exact Or.inl (by
          change wOff s2.core.wvec j + wSz s2.core.wvec j ≤
            wOff s2.core.wvec lit.toNat + wSz s2.core.wvec lit.toNat at hs1; omega)
    · exact Or.inr (by
        change wOff s2.core.wvec lit.toNat + wSz s2.core.wvec lit.toNat + cnt.toNat ≤
          wOff s2.core.wvec j at hs2; omega)
  have hlen' := wpush_lengthsOk (wlen' := s2.core.wlen) (wusable' := wusable')
    hlen (hwv'_len.trans hlen2.core_ok.wvec_len) hws_len hlen2.core_ok.wlen_le hwso_len
  refine wpush_ok_post hQ hlay2 hpres hlit hc12 hw0 hw1 wusable' hlen' (Nat.le_refl _)
    hoff1 (by omega) (fun j _ hne => hoth_w j hne) hoff_w
    (by rw [hsz_w, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsz32]) hdisj
    (fun j hj hne k hk => by
      by_cases hpj : 0 < wSz s2.core.wvec j
      · rcases hdisj j hj hne hpj with h1 | h2 <;> exact hws_out _ (by omega)
      · exact absurd hk (by omega))
    (fun k hk => hws_out _ (Or.inl (by omega))) hat0 hat1 hm'

/-! ## 3. Relocation Copy & Fill Invariants -/

def RelocCopyInv (s2 : FullState) (lit k : Nat) (wstk : List (BitVec 32)) : Prop :=
  let off := wOff s2.core.wvec lit
  let sz := wSz s2.core.wvec lit
  let dst := s2.core.wlen
  wstk.length = s2.core.wstk.length ∧
  (∀ j < 2 * s2.core.cur_vars, j ≠ lit → ∀ i < wSz s2.core.wvec j,
    wstk[wOff s2.core.wvec j + i]? = s2.core.wstk[wOff s2.core.wvec j + i]?) ∧
  (∀ i < k, wstk[dst + i]? = s2.core.wstk[off + i]?) ∧
  (∀ i, k ≤ i → i < sz → wstk[off + i]? = s2.core.wstk[off + i]?) ∧
  (∀ i < k, wstk[off + i]? = some 0xFFFFFFFF#32)

theorem wpush_reloc_init (s2 : FullState) (lit : Nat) :
    RelocCopyInv s2 lit 0 s2.core.wstk :=
  ⟨rfl, fun _ _ _ _ _ => rfl, fun _ h => absurd h (Nat.not_lt_zero _),
    fun _ _ _ => rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩

theorem wpush_reloc_step_c0 {s2 : FullState} {lit k : Nat} {wstk : List (BitVec 32)}
    (hlay2 : WatchStackLayout s2.core) (hwlen_le : s2.core.wlen ≤ s2.core.wstk.length)
    (hlit : lit < 2 * s2.core.cur_vars)
    (hk : k < wSz s2.core.wvec lit) (hinv : RelocCopyInv s2 lit k wstk)
    (hfit : s2.core.wlen + k < wstk.length) :
    let off := wOff s2.core.wvec lit
    let dst := s2.core.wlen
    let v := (wstk[off + k]?).getD 0#32
    let wstk' := (wstk.set (dst + k) v).set (off + k) 0xFFFFFFFF#32
    RelocCopyInv s2 lit (k + 1) wstk' := by
  intro off dst v wstk'
  obtain ⟨hlen, hoth, hcp, hrem, hclr⟩ := hinv
  have hb_lit : wOff s2.core.wvec lit + wSz s2.core.wvec lit ≤ s2.core.wlen := hlay2.bounds lit hlit
  have hoff_lt : off + k < wstk.length := by change wOff s2.core.wvec lit + k < wstk.length; omega
  have hne_idx : dst + k ≠ off + k := by
    change s2.core.wlen + k ≠ wOff s2.core.wvec lit + k; omega
  have hv_eq : some v = s2.core.wstk[off + k]? := by
    have hget := hrem k (Nat.le_refl k) hk
    change wstk[off + k]? = s2.core.wstk[off + k]? at hget
    simp [v, hget, List.getElem?_eq_getElem (hlen ▸ hoff_lt)]
  have hcomm : wstk' = (wstk.set (off + k) 0xFFFFFFFF#32).set (dst + k) v := by
    rw [List.set_comm]; omega
  rw [hcomm]
  have hlen1 : (wstk.set (off + k) 0xFFFFFFFF#32).length = wstk.length := List.length_set
  refine ⟨by simp [hlen], ?_, ?_, ?_, ?_⟩
  · intro j hj hne i hi
    have hb_j : wOff s2.core.wvec j + wSz s2.core.wvec j ≤ s2.core.wlen := hlay2.bounds j hj
    have hd : wOff s2.core.wvec j + wSz s2.core.wvec j ≤ wOff s2.core.wvec lit ∨
        wOff s2.core.wvec lit + wSz s2.core.wvec lit ≤ wOff s2.core.wvec j :=
      hlay2.disjoint j lit hj hlit hne
        (by change 0 < wSz s2.core.wvec j; omega)
        (by change 0 < wSz s2.core.wvec lit; omega)
    have hne1 : wOff s2.core.wvec j + i ≠ dst + k := by
      change wOff s2.core.wvec j + i ≠ s2.core.wlen + k; omega
    have hne2 : wOff s2.core.wvec j + i ≠ off + k := by
      change wOff s2.core.wvec j + i ≠ wOff s2.core.wvec lit + k; rcases hd with h | h <;> omega
    rw [List.getElem?_set_ne (Ne.symm hne1), List.getElem?_set_ne (Ne.symm hne2)]
    exact hoth j hj hne i hi
  · intro i hi; by_cases hik : i = k
    · subst hik; rw [List.getElem?_set_self (by rw [hlen1]; exact hfit), ← hv_eq]
    · have hne1 : dst + i ≠ dst + k := by omega
      have hne2 : dst + i ≠ off + k := by
        change s2.core.wlen + i ≠ wOff s2.core.wvec lit + k; omega
      rw [List.getElem?_set_ne (Ne.symm hne1), List.getElem?_set_ne (Ne.symm hne2)]
      exact hcp i (by omega)
  · intro i hlo hhi
    have hne1 : off + i ≠ dst + k := by change wOff s2.core.wvec lit + i ≠ s2.core.wlen + k; omega
    have hne2 : off + i ≠ off + k := by
      change wOff s2.core.wvec lit + i ≠ wOff s2.core.wvec lit + k; omega
    rw [List.getElem?_set_ne (Ne.symm hne1), List.getElem?_set_ne (Ne.symm hne2)]
    exact hrem i (by omega) hhi
  · intro i hi; by_cases hik : i = k
    · subst hik; rw [List.getElem?_set_ne hne_idx, List.getElem?_set_self hoff_lt]
    · have hne1 : off + i ≠ dst + k := by
        change wOff s2.core.wvec lit + i ≠ s2.core.wlen + k; omega
      have hne2 : off + i ≠ off + k := by
        change wOff s2.core.wvec lit + i ≠ wOff s2.core.wvec lit + k; omega
      rw [List.getElem?_set_ne (Ne.symm hne1), List.getElem?_set_ne (Ne.symm hne2)]
      exact hclr i (by omega)

theorem wpush_reloc_fin {c : FullCfg} {s s2 : FullState} {R : Mem 64 → Prop}
    {lit w0 w1 cnt : BitVec 32} {Q : Post [Ty.bool]} (hQ : WPushPost c s R lit w0 w1 cnt Q)
    (hlen : s.LengthsOk c) (hlen2 : s2.LengthsOk c)
    (hlay2 : WatchStackLayout s2.core) (hpres : WatchPresAll s s2)
    (hlit : lit.toNat < 2 * s.core.cur_vars) (hc12 : cnt.toNat = 1 ∨ cnt.toNat = 2)
    (hw0 : cnt.toNat = 1 → w0 ≠ 0xFFFFFFFF#32)
    (hw1 : cnt.toNat = 2 → w0 ≠ 0xFFFFFFFF#32 ∧ w1 ≠ 0xFFFFFFFF#32)
    (hwlen1 : 1 ≤ s2.core.wlen) {ncap : Nat}
    (hsz_cnt : wSz s2.core.wvec lit.toNat + cnt.toNat ≤ ncap)
    (hfit : s2.core.wlen + ncap ≤ c.wcap)
    {wstk_cp wstk' wsort' : List (BitVec 32)} (wusable' : BitVec 64) {m' : Mem 64}
    (hinv : RelocCopyInv s2 lit.toNat (wSz s2.core.wvec lit.toNat) wstk_cp)
    (hws_len : wstk'.length = c.wcap) (hwso_len : wsort'.length = 2 * c.max_vars)
    (hws_lt : ∀ i < s2.core.wlen + wSz s2.core.wvec lit.toNat, wstk'[i]? = wstk_cp[i]?)
    (hat0 : wstk'[s2.core.wlen + wSz s2.core.wvec lit.toNat]? = some w0)
    (hat1 : cnt.toNat = 2 → wstk'[s2.core.wlen + wSz s2.core.wvec lit.toNat + 1]? = some w1)
    (wvec' : List (BitVec 32))
    (hwvec'_eq : wvec' = (s2.core.wvec.set (2 * lit.toNat) (BitVec.ofNat 32 s2.core.wlen)).set
      (2 * lit.toNat + 1) (BitVec.ofNat 32 (wSz s2.core.wvec lit.toNat + cnt.toNat)))
    (hm' : (FullMem c (wpushSet s wvec' wstk' wsort' (s2.core.wlen + ncap) wusable') ⋆ R) m') :
    Q (true, ()) m' := by
  have hcv2 := hpres.1; obtain ⟨_, hoth_cp, hcp_cp, _, _⟩ := hinv
  obtain ⟨hwv1, hwv2, hwlen32⟩ := wpush_wvec_lt2 hlen2.core_ok (hcv2 ▸ hlit)
  have hsz32 : wSz s2.core.wvec lit.toNat + cnt.toNat < 2 ^ 32 :=
    Nat.lt_of_le_of_lt (Nat.le_trans (by omega) hfit) (wpush_wcap_lt32 c)
  obtain ⟨hwv'_len, hoth_w, hoff_w, hsz_w⟩ :=
    wpush_wvec_set_off_sz (BitVec.ofNat 32 s2.core.wlen)
      (BitVec.ofNat 32 (wSz s2.core.wvec lit.toNat + cnt.toNat)) hwv1 hwv2
  subst hwvec'_eq
  have hlen' := wpush_lengthsOk (wlen' := s2.core.wlen + ncap) (wusable' := wusable')
    hlen (hwv'_len.trans hlen2.core_ok.wvec_len) hws_len hfit hwso_len
  refine wpush_ok_post hQ hlay2 hpres hlit hc12 hw0 hw1 wusable' hlen' (Nat.le_add_right _ _)
    hwlen1 (by omega) (fun j _ hne => hoth_w j hne)
    (by rw [hoff_w, bv32_eq_nat _ hwlen32 rfl])
    (by rw [hsz_w, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsz32])
    (fun j hj _ _ => Or.inl (hlay2.bounds j (hcv2 ▸ hj)))
    (fun j hj hne k hk =>
      (hws_lt _ (by have hb := hlay2.bounds j (hcv2 ▸ hj)
                    change wOff s2.core.wvec j + wSz s2.core.wvec j ≤ s2.core.wlen at hb
                    omega)).trans
        (hoth_cp j (hcv2 ▸ hj) hne k hk))
    (fun k hk => (hws_lt _ (Nat.add_lt_add_left hk _)).trans (hcp_cp k hk)) hat0 hat1 hm'

/-! ## 4. Branch Arithmetic, State Updates, & Loop Invariants -/

private theorem wvec_pair_rw {wvec : List (BitVec 32)} {lit : Val i32}
    (hwv1 : 2 * lit.toNat + 1 < wvec.length) :
    2 * lit.toNat % 2 ^ 64 = 2 * lit.toNat ∧
    (2 * lit.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 = 2 * lit.toNat + 1 ∧
    wOff wvec lit.toNat = (wvec[2 * lit.toNat]'(by omega)).toNat ∧
    wSz wvec lit.toNat = (wvec[2 * lit.toNat + 1]'hwv1).toNat := by
  have := lit.isLt
  refine ⟨Nat.mod_eq_of_lt (by omega),
    by rw [show BitVec.toNat (1 : BitVec 64) = 1 from rfl]; exact Nat.mod_eq_of_lt (by omega),
    by simp [wOff, List.getElem?_eq_getElem (by omega : 2 * lit.toNat < wvec.length)],
    by simp [wSz, List.getElem?_eq_getElem hwv1]⟩

theorem wpush_bv_off_sz_add {wvec : List (BitVec 32)} {lit : BitVec 32}
    (h0 : 2 * lit.toNat < wvec.length) (h1 : 2 * lit.toNat + 1 < wvec.length)
    (_hl : 2 * lit.toNat + 1 < 2 ^ 64) :
    (BitVec.setWidth 64 (wvec[2 * lit.toNat]'h0) +
      BitVec.setWidth 64 (wvec[2 * lit.toNat + 1]'h1)).toNat =
      wOff wvec lit.toNat + wSz wvec lit.toNat := by
  have := (wvec[2 * lit.toNat]'h0).isLt; have := (wvec[2 * lit.toNat + 1]'h1).isLt
  simp only [wOff, wSz, List.getElem?_eq_getElem h0, List.getElem?_eq_getElem h1,
    Option.getD_some]; c0_bv_omega

theorem wpush_bv_sz_add_cnt {wvec : List (BitVec 32)} {lit cnt : BitVec 32}
    (h1 : 2 * lit.toNat + 1 < wvec.length) (_hcnt : cnt.toNat ≤ 2)
    (hsz : wSz wvec lit.toNat + cnt.toNat < 2 ^ 32) :
    (BitVec.setWidth 64 (wvec[2 * lit.toNat + 1]'h1) + BitVec.setWidth 64 cnt).setWidth 32 =
      BitVec.ofNat 32 (wSz wvec lit.toNat + cnt.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [wSz, List.getElem?_eq_getElem h1, Option.getD_some] at hsz ⊢; c0_bv_omega

theorem wpush_bv_sz_add_cnt32 {wvec : List (BitVec 32)} {lit cnt : BitVec 32}
    (h1 : 2 * lit.toNat + 1 < wvec.length) :
    BitVec.setWidth 32 (BitVec.setWidth 64 wvec[2 * lit.toNat + 1]) +
      BitVec.setWidth 32 (BitVec.setWidth 64 cnt) =
      BitVec.ofNat 32 (wSz wvec lit.toNat + cnt.toNat) :=
  BitVec.eq_of_toNat_eq (by simp [wSz, List.getElem?_eq_getElem h1])

theorem wpush_bv64_add3_eq {wvec : List (BitVec 32)} {lit cnt : BitVec 32} {sum : Nat}
    (h0 : 2 * lit.toNat < wvec.length) (h1 : 2 * lit.toNat + 1 < wvec.length)
    (hl : 2 * lit.toNat + 1 < 2 ^ 64) (hoff : wOff wvec lit.toNat + wSz wvec lit.toNat = sum)
    (hsum : sum + cnt.toNat < 2 ^ 64) :
    (BitVec.setWidth 64 (wvec[2 * lit.toNat]'h0) +
      BitVec.setWidth 64 (wvec[2 * lit.toNat + 1]'h1) + BitVec.setWidth 64 cnt).toNat =
      sum + cnt.toNat := by
  have := cnt.isLt; rw [BitVec.toNat_add, wpush_bv_off_sz_add h0 h1 hl, hoff]; c0_bv_omega

theorem wpush_bv64_add_off_sz_1 {p : Nat} {a b : Val i64}
    (hp : (a + b).toNat = p) (hlt : p + 1 < 2 ^ 64) :
    (a + b + (1 : BitVec 64)).toNat = p + 1 := by rw [BitVec.toNat_add, hp]; c0_bv_omega

theorem wpush_state_upd {s s2 : FullState}
    {wv2 ws2 wso2 wvec' wstk' : List (BitVec 32)} {wl2 wlen' : Nat} {wu2 wu' : BitVec 64}
    (hs2 : s2 = wpushSet s wv2 ws2 wso2 wl2 wu2) :
    ({ s2 with
      core := { s2.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' } } :
        FullState) = wpushSet s wvec' wstk' wso2 wlen' wu' := by subst hs2; rfl

@[expose] def WPushInvState (c : FullCfg) (s : FullState) (R : Mem 64 → Prop)
    (s2 : FullState) (m2 : Mem 64) : Prop :=
  s2.LengthsOk c ∧ WatchStackLayout s2.core ∧ WatchPresAll s s2 ∧ 1 ≤ s2.core.wlen ∧
  (∃ wvec2 wstk2 wsort2 wlen2 wusable2, s2 = wpushSet s wvec2 wstk2 wsort2 wlen2 wusable2) ∧
  (FullMem c s2 ⋆ R) m2

theorem wpush_inv_state_self {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hlen : s.LengthsOk c) (hlay : WatchStackLayout s.core) (hw1 : 1 ≤ s.core.wlen)
    (hm : (FullMem c s ⋆ R) m) : WPushInvState c s R s m :=
  ⟨hlen, hlay, watchPresAll_refl s, hw1,
    ⟨s.core.wvec, s.core.wstk, s.scratch.wsort, s.core.wlen, s.core.wusable, rfl⟩, hm⟩

theorem wpush_inv_state_defrag {c : FullCfg} {s s2 : FullState} {R : Mem 64 → Prop}
    {wvec' wstk' wsort' : List (BitVec 32)} {wlen' : Nat} {m2 m' : Mem 64}
    (hinv2 : WPushInvState c s R s2 m2)
    (hlen' : (wpushSet s2 wvec' wstk' wsort' wlen' 0#64).LengthsOk c)
    (hlay' : WatchStackLayout (wpushSet s2 wvec' wstk' wsort' wlen' 0#64).core)
    (hw1' : 1 ≤ s2.core.wlen → 1 ≤ wlen')
    (hpres' : ∀ l < 2 * s2.core.cur_vars,
      wSz wvec' l = fullWatchSize s2 l ∧
      ∀ k < fullWatchSize s2 l, wstk'[wOff wvec' l + k]? = s2.core.wstk[fullWatchOff s2 l + k]?)
    (hm' : (FullMem c (wpushSet s2 wvec' wstk' wsort' wlen' 0#64) ⋆ R) m') :
    WPushInvState c s R (wpushSet s wvec' wstk' wsort' wlen' 0#64) m' := by
  obtain ⟨_, _, hpres2, hw12, ⟨_, _, _, _, _, hs2_eq⟩, _⟩ := hinv2; subst hs2_eq
  exact ⟨hlen', hlay', watchPresAll_trans hpres2 ⟨rfl, hpres'⟩, hw1' hw12,
    ⟨wvec', wstk', wsort', wlen', 0#64, rfl⟩, hm'⟩

theorem wpush_inv_core_eq {c : FullCfg} {s s2 : FullState} {R : Mem 64 → Prop}
    {m2 : Mem 64} (hinv2 : WPushInvState c s R s2 m2) :
    s2.core.cur_vars = s.core.cur_vars ∧ s2.core.wlen < 2 ^ 32 ∧ c.wcap < 2 ^ 32 := by
  obtain ⟨hlen2, _, hpres2, _, _, _⟩ := hinv2
  exact ⟨hpres2.1, Nat.lt_of_le_of_lt hlen2.core_ok.wlen_le (wpush_wcap_lt32 c), wpush_wcap_lt32 c⟩

theorem full_state_update_wpush_no_wu {s s3 : FullState}
    {wv3 ws3 wso3 : List (BitVec 32)} {wl3 : Nat} {wu3 : BitVec 64}
    (hs3 : s3 = wpushSet s wv3 ws3 wso3 wl3 wu3) (wv4 ws4 : List (BitVec 32)) (wl4 : Nat) :
    { s3 with core := { s3.core with wvec := wv4, wstk := ws4, wlen := wl4 } } =
      wpushSet s wv4 ws4 wso3 wl4 wu3 := by subst hs3; rfl

@[expose] def WPushAppendInv (c : FullCfg) (s : FullState) (R : Mem 64 → Prop)
    (p : Nat) (w0 w1 cnt : Val i32) (wstk0 wstk' : List (BitVec 32)) (mw : Mem 64) : Prop :=
  wstk'.length = c.wcap ∧
  (∀ i, i < p ∨ p + cnt.toNat ≤ i → wstk'[i]? = wstk0[i]?) ∧
  wstk'[p]? = some w0 ∧
  (cnt.toNat = 2 → wstk'[p + 1]? = some w1) ∧
  (FullMem c { s with core := { s.core with wstk := wstk' } } ⋆ R) mw

theorem wpush_append_set2 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {p : Nat} {w0 w1 cnt : Val i32} {wstk0 : List (BitVec 32)} {mw : Mem 64}
    (hlen0 : wstk0.length = c.wcap) (hp2 : p + 2 ≤ c.wcap) (_hc2 : cnt.toNat = 2)
    (hmw : (FullMem c { s with core := { s.core with
      wstk := (wstk0.set p w0).set (p + 1) w1 } } ⋆ R) mw) :
    ∃ wstk', WPushAppendInv c s R p w0 w1 cnt wstk0 wstk' mw := by
  refine ⟨_, by simp [hlen0], fun i _ => ?_, ?_, fun _ => ?_, hmw⟩
  · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
  · rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega)]
  · rw [List.getElem?_set_self (by rw [List.length_set, hlen0]; omega)]

theorem wpush_append_set1 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {p : Nat} {w0 w1 cnt : Val i32} {wstk0 : List (BitVec 32)} {mw : Mem 64}
    (hlen0 : wstk0.length = c.wcap) (hp1 : p + 1 ≤ c.wcap) (hc1 : cnt.toNat = 1)
    (hmw : (FullMem c { s with core := { s.core with wstk := wstk0.set p w0 } } ⋆ R) mw) :
    ∃ wstk', WPushAppendInv c s R p w0 w1 cnt wstk0 wstk' mw := by
  refine ⟨_, by simp [hlen0], fun i hi => ?_, ?_, fun h => absurd h (by omega), hmw⟩
  · rcases hi with hi1 | hi2 <;> rw [List.getElem?_set_ne (by omega)]
  · rw [List.getElem?_set_self (by omega)]

theorem wpush_caseA_wlen_bv {c : FullCfg} {s3 : FullState} (hfit : s3.core.wlen < c.wcap) :
    (BitVec.ofNat 64 s3.core.wlen).toNat = s3.core.wlen ∧
    (BitVec.ofNat 64 s3.core.wlen + (1 : BitVec 64)).toNat = s3.core.wlen + 1 := by
  have hwcap32 := wpush_wcap_lt32 c; exact ⟨by c0_bv_omega, by c0_bv_omega⟩

theorem wpush_caseA_fin_setup {c : FullCfg} {s s3 : FullState}
    {wv3 ws3 wso3 : List (BitVec 32)} {wl3 : Nat} {wu3 : BitVec 64}
    {lit cnt : Val i32}
    (hs3 : s3 = { s with
      core := { s.core with wvec := wv3, wstk := ws3, wlen := wl3, wusable := wu3 }
      scratch := { s.scratch with wsort := wso3 } })
    (hlen3 : s3.LengthsOk c) (hlit3 : lit.toNat < 2 * s3.core.cur_vars)
    (_hc12 : cnt.toNat = 1 ∨ cnt.toNat = 2) (hfit3 : s3.core.wlen + cnt.toNat ≤ c.wcap) :
    2 * lit.toNat < s3.core.wvec.length ∧
    2 * lit.toNat + 1 <
      (s3.core.wvec.set (2 * lit.toNat) (BitVec.ofNat 32 s3.core.wlen)).length ∧
    (BitVec.ofNat 64 s3.core.wlen + BitVec.setWidth 64 cnt).toNat = s3.core.wlen + cnt.toNat ∧
    (BitVec.ofNat 64 s3.core.wlen).setWidth 32 = BitVec.ofNat 32 s3.core.wlen ∧
    wso3.length = 2 * c.max_vars := by
  have hwcap32 := wpush_wcap_lt32 c
  have hcv := hlen3.core_ok.cur_vars_le; have hwv := hlen3.core_ok.wvec_len
  have hcnt := cnt.isLt
  exact ⟨by omega, by simp [hwv]; omega, by c0_bv_omega, bv32_ofNat_64 _,
    (hs3 ▸ hlen3).scratch_ok.wsort_len⟩

theorem wpush_case_pos1_lt {c : FullCfg} {s2 : FullState} {lit : Val i32} {p : Nat}
    (hlen2 : s2.LengthsOk c) (hwv0 : 2 * lit.toNat < s2.core.wvec.length)
    (hwv1 : 2 * lit.toNat + 1 < s2.core.wvec.length)
    (_hwv0_bv : (lit.setWidth 64 <<< 1).toNat < s2.core.wvec.length)
    (_hwv1_bv : (lit.setWidth 64 <<< 1 + 1).toNat < s2.core.wvec.length)
    (_hj0 : 2 * lit.toNat % 2 ^ 64 < s2.core.wvec.length)
    (_hj1 : (2 * lit.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 < s2.core.wvec.length)
    (hpos_eq :
      (BitVec.setWidth 64 s2.core.wvec[(lit.setWidth 64 <<< 1).toNat] +
        BitVec.setWidth 64 s2.core.wvec[(lit.setWidth 64 <<< 1 + 1).toNat]).toNat = p)
    (hp2 : p + 2 ≤ c.wcap) (w0 : Val i32) :
    ((BitVec.setWidth 64 s2.core.wvec[(lit.setWidth 64 <<< 1).toNat] +
      BitVec.setWidth 64 s2.core.wvec[(lit.setWidth 64 <<< 1 + 1).toNat]) + (1 : BitVec 64)).toNat =
      p + 1 ∧
    ((BitVec.setWidth 64 s2.core.wvec[(lit.setWidth 64 <<< 1).toNat] +
      BitVec.setWidth 64 s2.core.wvec[(lit.setWidth 64 <<< 1 + 1).toNat]) + (1 : BitVec 64)).toNat <
      s2.core.wstk.length ∧
    ((BitVec.setWidth 64 s2.core.wvec[(lit.setWidth 64 <<< 1).toNat] +
      BitVec.setWidth 64 s2.core.wvec[(lit.setWidth 64 <<< 1 + 1).toNat]) + (1 : BitVec 64)).toNat <
      (s2.core.wstk.set (BitVec.setWidth 64 s2.core.wvec[(lit.setWidth 64 <<< 1).toNat] +
        BitVec.setWidth 64 s2.core.wvec[(lit.setWidth 64 <<< 1 + 1).toNat]).toNat w0).length ∧
    (s2.core.wvec[2 * lit.toNat % 2 ^ 64].toNat +
      s2.core.wvec[(2 * lit.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64].toNat +
      BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 < s2.core.wstk.length := by
  have hwcap32 := wpush_wcap_lt32 c; have := lit.isLt
  obtain ⟨hm0, hm1, ho_w, hs_w⟩ := wvec_pair_rw hwv1
  have hp1 := wpush_bv64_add_off_sz_1 hpos_eq (by omega)
  simp only [bv64_shl1_lit, bv64_shl1_add1_lit] at hpos_eq
  have hp_eq' := (wpush_bv_off_sz_add hwv0 hwv1 (by omega)).symm.trans hpos_eq
  have hlt_m : (s2.core.wvec[2 * lit.toNat % 2 ^ 64].toNat +
      s2.core.wvec[(2 * lit.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64].toNat +
      BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 = p + 1 := by
    simp only [hm0, hm1]; change (s2.core.wvec[2 * lit.toNat].toNat +
      s2.core.wvec[2 * lit.toNat + 1].toNat + 1) % 2 ^ 64 = p + 1
    rw [← ho_w, ← hs_w, hp_eq', Nat.mod_eq_of_lt (by omega : p + 1 < 2 ^ 64)]
  exact ⟨hp1, by rw [hlen2.core_ok.wstk_len_arr, hp1]; omega,
    by rw [List.length_set, hlen2.core_ok.wstk_len_arr, hp1]; omega,
    by rw [hlt_m, hlen2.core_ok.wstk_len_arr]; omega⟩

theorem wpush_caseB_bounds {c : FullCfg} {s2 : FullState} {lit cnt : Val i32}
    (hlen2 : s2.LengthsOk c) (hwv0 : 2 * lit.toNat < s2.core.wvec.length)
    (hwv1 : 2 * lit.toNat + 1 < s2.core.wvec.length)
    (_hwv0_bv : (lit.setWidth 64 <<< 1).toNat < s2.core.wvec.length)
    (_hwv1_bv : (lit.setWidth 64 <<< 1 + 1).toNat < s2.core.wvec.length)
    (_hj0 : 2 * lit.toNat % 2 ^ 64 < s2.core.wvec.length)
    (_hj1 : (2 * lit.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 < s2.core.wvec.length)
    (hbc_eq :
      BitVec.setWidth 64 s2.core.wvec[2 * lit.toNat % 2 ^ 64] +
        BitVec.setWidth 64 s2.core.wvec[(2 * lit.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64] =
        BitVec.ofNat 64 s2.core.wlen)
    (hfit_bv : cnt.toNat ≤ (2 ^ 64 - s2.core.wlen % 2 ^ 64 + c.wcap) % 2 ^ 64)
    (hc12 : cnt.toNat = 1 ∨ cnt.toNat = 2) :
    wOff s2.core.wvec lit.toNat + wSz s2.core.wvec lit.toNat = s2.core.wlen ∧
    s2.core.wlen + cnt.toNat ≤ c.wcap ∧
    (BitVec.setWidth 64 s2.core.wvec[(lit.setWidth 64 <<< 1).toNat] +
      BitVec.setWidth 64 s2.core.wvec[(lit.setWidth 64 <<< 1 + 1).toNat]).toNat =
      s2.core.wlen ∧
    (BitVec.setWidth 64 s2.core.wvec[(lit.setWidth 64 <<< 1).toNat] +
      BitVec.setWidth 64 s2.core.wvec[(lit.setWidth 64 <<< 1 + 1).toNat]).toNat <
      s2.core.wstk.length := by
  have hwcap32 := wpush_wcap_lt32 c; have hle := hlen2.core_ok.wlen_le; have := lit.isLt
  obtain ⟨hm0, hm1, _, _⟩ := wvec_pair_rw hwv1
  have hoff_eq : wOff s2.core.wvec lit.toNat + wSz s2.core.wvec lit.toNat = s2.core.wlen := by
    have h := congrArg BitVec.toNat hbc_eq; simp only [hm0, hm1] at h
    rw [wpush_bv_off_sz_add hwv0 hwv1 (by omega), BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : s2.core.wlen < 2 ^ 64)] at h; exact h
  have hfitB : s2.core.wlen + cnt.toNat ≤ c.wcap := by
    rw [Nat.mod_eq_of_lt (by omega : s2.core.wlen < 2 ^ 64),
      show 2 ^ 64 - s2.core.wlen + c.wcap = 2 ^ 64 + (c.wcap - s2.core.wlen) by omega,
      Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)] at hfit_bv; omega
  have hpos_eq : (BitVec.setWidth 64 s2.core.wvec[(lit.setWidth 64 <<< 1).toNat] +
      BitVec.setWidth 64 s2.core.wvec[(lit.setWidth 64 <<< 1 + 1).toNat]).toNat = s2.core.wlen := by
    simp only [bv64_shl1_lit, bv64_shl1_add1_lit]
    rw [wpush_bv_off_sz_add hwv0 hwv1 (by omega), hoff_eq]
  exact ⟨hoff_eq, hfitB, hpos_eq, by rw [hlen2.core_ok.wstk_len_arr, hpos_eq]; omega⟩

theorem wpush_caseB_mem_rw {c : FullCfg} {s2 : FullState} {lit cnt : Val i32}
    (hlen2 : s2.LengthsOk c) (hlay2 : WatchStackLayout s2.core)
    (hlit2 : lit.toNat < 2 * s2.core.cur_vars)
    (hwv0 : 2 * lit.toNat < s2.core.wvec.length) (hwv1 : 2 * lit.toNat + 1 < s2.core.wvec.length)
    (hoff_eq : wOff s2.core.wvec lit.toNat + wSz s2.core.wvec lit.toNat = s2.core.wlen)
    (hfitB : s2.core.wlen + cnt.toNat ≤ c.wcap) (hc12 : cnt.toNat = 1 ∨ cnt.toNat = 2) :
    ((s2.core.wvec[2 * lit.toNat + 1].setWidth 64 + cnt.setWidth 64).setWidth 32 =
      BitVec.ofNat 32 (wSz s2.core.wvec lit.toNat + cnt.toNat)) ∧
    ((s2.core.wvec[2 * lit.toNat].setWidth 64 +
      s2.core.wvec[2 * lit.toNat + 1].setWidth 64 +
      cnt.setWidth 64).toNat = s2.core.wlen + cnt.toNat) := by
  have hwcap32 := wpush_wcap_lt32 c; have hle := hlen2.core_ok.wlen_le
  have hbd := hlay2.bounds lit.toNat hlit2
  exact ⟨wpush_bv_sz_add_cnt hwv1 (by omega) (by omega),
    wpush_bv64_add3_eq hwv0 hwv1 (by have := lit.isLt; omega) hoff_eq (by omega)⟩

theorem wpush_caseC_bounds {c : FullCfg} {s2 : FullState} {lit cnt : Val i32}
    (hlen2 : s2.LengthsOk c) (hlay2 : WatchStackLayout s2.core)
    (hlit2 : lit.toNat < 2 * s2.core.cur_vars)
    (hwv0 : 2 * lit.toNat < s2.core.wvec.length) (hwv1 : 2 * lit.toNat + 1 < s2.core.wvec.length)
    (_hwv0_bv : (lit.setWidth 64 <<< 1).toNat < s2.core.wvec.length)
    (_hwv1_bv : (lit.setWidth 64 <<< 1 + 1).toNat < s2.core.wvec.length)
    (_hj0 : 2 * lit.toNat % 2 ^ 64 < s2.core.wvec.length)
    (_hj1 : (2 * lit.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 < s2.core.wvec.length)
    (hleC_bv :
      (s2.core.wvec[2 * lit.toNat % 2 ^ 64].toNat +
        s2.core.wvec[(2 * lit.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64].toNat +
        cnt.toNat) % 2 ^ 64 ≤ s2.core.wlen % 2 ^ 64)
    (hc12 : cnt.toNat = 1 ∨ cnt.toNat = 2) :
    (BitVec.setWidth 64 s2.core.wvec[(lit.setWidth 64 <<< 1).toNat] +
      BitVec.setWidth 64 s2.core.wvec[(lit.setWidth 64 <<< 1 + 1).toNat]).toNat =
      wOff s2.core.wvec lit.toNat + wSz s2.core.wvec lit.toNat ∧
    wOff s2.core.wvec lit.toNat + wSz s2.core.wvec lit.toNat + cnt.toNat ≤ s2.core.wlen ∧
    (BitVec.setWidth 64 s2.core.wvec[(lit.setWidth 64 <<< 1).toNat] +
      BitVec.setWidth 64 s2.core.wvec[(lit.setWidth 64 <<< 1 + 1).toNat]).toNat <
      s2.core.wstk.length ∧
    (s2.core.wvec[2 * lit.toNat % 2 ^ 64].toNat +
      s2.core.wvec[(2 * lit.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64].toNat) % 2 ^ 64 <
      s2.core.wstk.length := by
  have hwcap32 := wpush_wcap_lt32 c; have hwl := hlen2.core_ok.wlen_le
  have hbd := hlay2.bounds lit.toNat hlit2; have := lit.isLt
  have h64 : 2 * lit.toNat + 1 < 2 ^ 64 := by omega
  obtain ⟨hm0, hm1, ho_w, hs_w⟩ := wvec_pair_rw hwv1
  have hpos_eq : (BitVec.setWidth 64 s2.core.wvec[(lit.setWidth 64 <<< 1).toNat] +
      BitVec.setWidth 64 s2.core.wvec[(lit.setWidth 64 <<< 1 + 1).toNat]).toNat =
      wOff s2.core.wvec lit.toNat + wSz s2.core.wvec lit.toNat := by
    simp only [bv64_shl1_lit, bv64_shl1_add1_lit]; exact wpush_bv_off_sz_add hwv0 hwv1 h64
  simp only [hm0, hm1, ← ho_w, ← hs_w] at hleC_bv
  have hleC :
      wOff s2.core.wvec lit.toNat + wSz s2.core.wvec lit.toNat + cnt.toNat ≤ s2.core.wlen := by
    rw [Nat.mod_eq_of_lt (by omega : _ < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : s2.core.wlen < 2 ^ 64)] at hleC_bv; exact hleC_bv
  have hsum_mod : (s2.core.wvec[2 * lit.toNat % 2 ^ 64].toNat +
      s2.core.wvec[(2 * lit.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64].toNat) % 2 ^ 64 =
      wOff s2.core.wvec lit.toNat + wSz s2.core.wvec lit.toNat := by
    simp only [hm0, hm1, ← ho_w, ← hs_w]; exact Nat.mod_eq_of_lt (by omega)
  exact ⟨hpos_eq, hleC, by rw [hlen2.core_ok.wstk_len_arr, hpos_eq]; omega,
    by rw [hsum_mod, hlen2.core_ok.wstk_len_arr]; omega⟩

theorem wpush_caseC_sent0 {s2 : FullState} {lit : Val i32}
    (hwv1 : 2 * lit.toNat + 1 < s2.core.wvec.length)
    (_hj0 : 2 * lit.toNat % 2 ^ 64 < s2.core.wvec.length)
    (_hj1 : (2 * lit.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 < s2.core.wvec.length)
    (hpos_lt :
      (s2.core.wvec[2 * lit.toNat % 2 ^ 64].toNat +
        s2.core.wvec[(2 * lit.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64].toNat) % 2 ^ 64 <
        s2.core.wstk.length)
    (hsent0 :
      s2.core.wstk[(s2.core.wvec[2 * lit.toNat % 2 ^ 64].toNat +
        s2.core.wvec[(2 * lit.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64].toNat) % 2 ^ 64] =
        0xFFFFFFFF#32) :
    s2.core.wstk[wOff s2.core.wvec lit.toNat + wSz s2.core.wvec lit.toNat]? =
      some 0xFFFFFFFF#32 := by
  have := lit.isLt; obtain ⟨hm0, hm1, ho_w, hs_w⟩ := wvec_pair_rw hwv1
  have hlt0 := (s2.core.wvec[2 * lit.toNat]'(by omega)).isLt
  have hlt1 := (s2.core.wvec[2 * lit.toNat + 1]'hwv1).isLt
  have hm_eq : (s2.core.wvec[2 * lit.toNat % 2 ^ 64].toNat +
      s2.core.wvec[(2 * lit.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64].toNat) % 2 ^ 64 =
      wOff s2.core.wvec lit.toNat + wSz s2.core.wvec lit.toNat := by
    simp only [hm0, hm1, ← ho_w, ← hs_w]; exact Nat.mod_eq_of_lt (by omega)
  have hget := List.getElem?_eq_getElem hpos_lt; rw [hsent0, hm_eq] at hget; exact hget

theorem wpush_caseC_sent1 {s2 : FullState} {lit cnt : Val i32}
    (hwv1 : 2 * lit.toNat + 1 < s2.core.wvec.length)
    (_hj0 : 2 * lit.toNat % 2 ^ 64 < s2.core.wvec.length)
    (_hj1 : (2 * lit.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 < s2.core.wvec.length)
    (hcnt2 : cnt.toNat = 2)
    (hpos1_lt :
      (s2.core.wvec[2 * lit.toNat % 2 ^ 64].toNat +
        s2.core.wvec[(2 * lit.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64].toNat +
        BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 < s2.core.wstk.length)
    (hsent0' : s2.core.wstk[wOff s2.core.wvec lit.toNat + wSz s2.core.wvec lit.toNat]? =
      some 0xFFFFFFFF#32)
    (hsent1 :
      s2.core.wstk[(s2.core.wvec[2 * lit.toNat % 2 ^ 64].toNat +
        s2.core.wvec[(2 * lit.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64].toNat +
        BitVec.toNat (1 : BitVec 64)) % 2 ^ 64] = 0xFFFFFFFF#32) :
    ∀ k < cnt.toNat, s2.core.wstk[wOff s2.core.wvec lit.toNat +
      wSz s2.core.wvec lit.toNat + k]? = some 0xFFFFFFFF#32 := by
  have := lit.isLt; obtain ⟨hm0, hm1, ho_w, hs_w⟩ := wvec_pair_rw hwv1
  have hlt0 := (s2.core.wvec[2 * lit.toNat]'(by omega)).isLt
  have hlt1 := (s2.core.wvec[2 * lit.toNat + 1]'hwv1).isLt
  have hs1_eq : (s2.core.wvec[2 * lit.toNat % 2 ^ 64].toNat +
      s2.core.wvec[(2 * lit.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64].toNat +
      BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 =
      wOff s2.core.wvec lit.toNat + wSz s2.core.wvec lit.toNat + 1 := by
    simp only [hm0, hm1]
    change (s2.core.wvec[2 * lit.toNat].toNat +
      s2.core.wvec[2 * lit.toNat + 1].toNat + 1) % 2 ^ 64 =
      wOff s2.core.wvec lit.toNat + wSz s2.core.wvec lit.toNat + 1
    rw [← ho_w, ← hs_w]; exact Nat.mod_eq_of_lt (by omega)
  intro k hk
  rcases Nat.lt_succ_iff_lt_or_eq.mp (by omega : k < 1 + 1) with hk0 | rfl
  · have : k = 0 := by omega
    subst this; simpa using hsent0'
  · have hget := List.getElem?_eq_getElem hpos1_lt; rw [hsent1, hs1_eq] at hget; exact hget

theorem wpush_nc1_nz {s2 : FullState} {lit : Val i32}
    (hwv1 : 2 * lit.toNat + 1 < s2.core.wvec.length)
    (_hwv1_bv : (lit.setWidth 64 <<< 1 + 1).toNat < s2.core.wvec.length)
    (_hj1 : (2 * lit.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 < s2.core.wvec.length)
    (hsz_nz :
      ¬ BitVec.setWidth 64 s2.core.wvec[(2 * lit.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64] =
        0) :
    (s2.core.wvec[(lit.setWidth 64 <<< 1 + 1).toNat].setWidth 64 <<< 1).toNat =
      if wSz s2.core.wvec lit.toNat = 0 then 2 else 2 * wSz s2.core.wvec lit.toNat := by
  have := lit.isLt; obtain ⟨_, hm1, _, hs_w⟩ := wvec_pair_rw hwv1
  simp only [hm1] at hsz_nz; simp only [bv64_shl1_add1_lit]
  have hnz : wSz s2.core.wvec lit.toNat ≠ 0 :=
    Nat.ne_of_gt (list_zext64_pos hwv1 hwv1 rfl hsz_nz)
  have hlt1 := (s2.core.wvec[2 * lit.toNat + 1]'hwv1).isLt
  rw [ite_eq_right hnz]; c0_bv_omega

theorem wpush_nc2_cmp {s2 : FullState} {lit cnt : Val i32}
    (hwv1 : 2 * lit.toNat + 1 < s2.core.wvec.length)
    (_hwv1_bv : (lit.setWidth 64 <<< 1 + 1).toNat < s2.core.wvec.length)
    (_hj1 : (2 * lit.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 < s2.core.wvec.length)
    (_hc12 : cnt.toNat = 1 ∨ cnt.toNat = 2) {nc1 : Val i64} {bound : Nat}
    (hnc1 : nc1.toNat =
      if wSz s2.core.wvec lit.toNat = 0 then 2 else 2 * wSz s2.core.wvec lit.toNat)
    (hsz_le : wSz s2.core.wvec lit.toNat ≤ bound) :
    (nc1.toNat <
        (s2.core.wvec[(2 * lit.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64].toNat +
          cnt.toNat) % 2 ^ 64 →
      wSz s2.core.wvec lit.toNat + cnt.toNat ≤
        (s2.core.wvec[(lit.setWidth 64 <<< 1 + 1).toNat].setWidth 64 + cnt.setWidth 64).toNat ∧
      (s2.core.wvec[(lit.setWidth 64 <<< 1 + 1).toNat].setWidth 64 + cnt.setWidth 64).toNat ≤
        max 2 (2 * bound) + 2) ∧
    (¬ nc1.toNat <
        (s2.core.wvec[(2 * lit.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64].toNat +
          cnt.toNat) % 2 ^ 64 →
      wSz s2.core.wvec lit.toNat + cnt.toNat ≤ nc1.toNat ∧ nc1.toNat ≤ max 2 (2 * bound) + 2) := by
  have := lit.isLt; obtain ⟨_, hm1, _, hs_w⟩ := wvec_pair_rw hwv1
  have hlt1 := (s2.core.wvec[2 * lit.toNat + 1]'hwv1).isLt
  simp only [bv64_shl1_add1_lit]
  have hadd : (s2.core.wvec[2 * lit.toNat + 1].setWidth 64 + cnt.setWidth 64).toNat =
      wSz s2.core.wvec lit.toNat + cnt.toNat := by have := cnt.isLt; c0_bv_omega
  refine ⟨fun _ => by rw [hadd]; omega, fun hge => by
    simp only [hm1] at hge
    rw [← hs_w, Nat.mod_eq_of_lt (by omega : _ < 2 ^ 64)] at hge
    split at hnc1 <;> omega⟩

theorem wpush_fit_of_cmp {c : FullCfg} {s3 : FullState} {v : Nat}
    (hle3 : s3.core.wlen ≤ c.wcap)
    (hfit : ¬ (2 ^ 64 - s3.core.wlen % 2 ^ 64 + c.wcap) % 2 ^ 64 < v) :
    s3.core.wlen + v ≤ c.wcap := by
  have hwcap32 := wpush_wcap_lt32 c
  rw [Nat.mod_eq_of_lt (by omega : s3.core.wlen < 2 ^ 64),
    show 2 ^ 64 - s3.core.wlen + c.wcap = 2 ^ 64 + (c.wcap - s3.core.wlen) by omega,
    Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)] at hfit
  omega

theorem wpush_fit_lt_of_cmp {c : FullCfg} {s3 : FullState} {v : Nat}
    (hle3 : s3.core.wlen ≤ c.wcap)
    (hfit : (2 ^ 64 - s3.core.wlen % 2 ^ 64 + c.wcap) % 2 ^ 64 < v) :
    c.wcap - s3.core.wlen < v := by
  have hwcap32 := wpush_wcap_lt32 c
  rw [Nat.mod_eq_of_lt (by omega : s3.core.wlen < 2 ^ 64),
    show 2 ^ 64 - s3.core.wlen + c.wcap = 2 ^ 64 + (c.wcap - s3.core.wlen) by omega,
    Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)] at hfit
  exact hfit

theorem wpush_defrag_call {c : FullCfg} {s s2 : FullState} {R : Mem 64 → Prop} {m2 : Mem 64}
    (hinv2 : WPushInvState c s R s2 m2) {Q' : Post []} {X : XPost}
    (hk : ∀ wv' ws' wl' wso' m',
      WPushInvState c s R (wpushSet s wv' ws' wso' wl' 0#64) m' → Q' () m') :
    Proof.Spec.fullWstackDefragSpec (c.hdr, ()) m2 Q' X :=
  ⟨c, s2, R, rfl, hinv2.1, hinv2.2.1, hinv2.2.2.2.2.2,
    fun wv' ws' wl' wso' m' hlen' hlay' hw1' hpres' hm' =>
      hk wv' ws' wl' wso' m' (wpush_inv_state_defrag hinv2 hlen' hlay' hw1' hpres' hm')⟩

theorem wpush_jd3_fit {c : FullCfg} {s3 : FullState} {lit cnt : Val i32} {sz3 : Val i64}
    (hsz3 : sz3.toNat = wSz s3.core.wvec lit.toNat) (hc12 : cnt.toNat = 1 ∨ cnt.toNat = 2)
    (hsz3_le : sz3.toNat ≤ c.wcap) :
    wSz s3.core.wvec lit.toNat + cnt.toNat ≤ (sz3 + BitVec.setWidth 64 cnt).toNat ∧
    (sz3 + BitVec.setWidth 64 cnt).toNat ≤ max 2 (2 * c.wcap) + 2 := by
  have hwcap32 := wpush_wcap_lt32 c; have := cnt.isLt; c0_bv_omega

@[expose] def WPushRelocCopyInv (c : FullCfg) (s3 : FullState) (R : Mem 64 → Prop)
    (lit : Val i32) (sz3 : Val i64) (n : Nat) (xs : Tup Val [i64]) (mw : Mem 64) : Prop :=
  ∃ wstk_cp : List (BitVec 32), xs.fst.toNat ≤ sz3.toNat ∧
    n = sz3.toNat - xs.fst.toNat ∧ wstk_cp.length = c.wcap ∧
    RelocCopyInv s3 lit.toNat xs.fst.toNat wstk_cp ∧
    (FullMem c { s3 with core := { s3.core with wstk := wstk_cp } } ⋆ R) mw

@[expose] def WPushRelocFillInv (c : FullCfg) (s3 : FullState) (R : Mem 64 → Prop)
    (sz3 ncap3 : Val i64) (w0 w1 cnt : Val i32) (wstk_cp : List (BitVec 32))
    (n : Nat) (xs : Tup Val [i64]) (mw : Mem 64) : Prop :=
  ∃ wstk_f : List (BitVec 32), sz3.toNat + cnt.toNat ≤ xs.fst.toNat ∧
    xs.fst.toNat ≤ ncap3.toNat ∧ n = ncap3.toNat - xs.fst.toNat ∧
    wstk_f.length = c.wcap ∧
    (∀ i < s3.core.wlen + sz3.toNat, wstk_f[i]? = wstk_cp[i]?) ∧
    wstk_f[s3.core.wlen + sz3.toNat]? = some w0 ∧
    (cnt.toNat = 2 → wstk_f[s3.core.wlen + sz3.toNat + 1]? = some w1) ∧
    (FullMem c { s3 with core := { s3.core with wstk := wstk_f } } ⋆ R) mw

theorem wpush_reloc_copy_init {c : FullCfg} {s3 : FullState} {R : Mem 64 → Prop}
    {lit : Val i32} {sz3 : Val i64} {m5 : Mem 64}
    (hlen3 : s3.LengthsOk c) (hm3 : (FullMem c s3 ⋆ R) m5) :
    WPushRelocCopyInv c s3 R lit sz3 sz3.toNat (0#64, ()) m5 :=
  ⟨s3.core.wstk, Nat.zero_le _, by simp, hlen3.core_ok.wstk_len_arr,
    wpush_reloc_init s3 lit.toNat, hm3⟩

theorem wpush_reloc_step_bounds {c : FullCfg} {s3 : FullState}
    {off3 sz3 k_bv : Val i64} {wstk_cp : List (BitVec 32)}
    (hlen3 : s3.LengthsOk c) (hcp_len : wstk_cp.length = c.wcap)
    (hoff3_bd : off3.toNat + sz3.toNat ≤ s3.core.wlen)
    (hfit3 : s3.core.wlen + sz3.toNat ≤ c.wcap) (hk_lt : k_bv.toNat < sz3.toNat) :
    (off3 + k_bv).toNat = off3.toNat + k_bv.toNat ∧
    (BitVec.ofNat 64 s3.core.wlen + k_bv).toNat = s3.core.wlen + k_bv.toNat ∧
    (BitVec.ofNat 64 s3.core.wlen + k_bv).toNat < wstk_cp.length ∧
    ∀ v : BitVec 32, (off3 + k_bv).toNat <
      (wstk_cp.set (BitVec.ofNat 64 s3.core.wlen + k_bv).toNat v).length := by
  have hwcap32 := wpush_wcap_lt32 c; have hwl := hlen3.core_ok.wlen_le
  have hk_off : (off3 + k_bv).toNat = off3.toNat + k_bv.toNat := by c0_bv_omega
  have hk_dst : (BitVec.ofNat 64 s3.core.wlen + k_bv).toNat = s3.core.wlen + k_bv.toNat := by
    c0_bv_omega
  exact ⟨hk_off, hk_dst, by rw [hk_dst, hcp_len]; omega,
    fun _ => by rw [List.length_set, hk_off, hcp_len]; omega⟩

theorem wpush_reloc_copy_next {c : FullCfg} {s3 : FullState} {R : Mem 64 → Prop}
    {lit : Val i32} {off3 sz3 k_bv : Val i64} {wstk_cp : List (BitVec 32)} {mw : Mem 64}
    (hlen3 : s3.LengthsOk c) (hlay3 : WatchStackLayout s3.core)
    (hlit3 : lit.toNat < 2 * s3.core.cur_vars)
    (hoff3 : off3.toNat = wOff s3.core.wvec lit.toNat)
    (hsz3 : sz3.toNat = wSz s3.core.wvec lit.toNat)
    (hcp_len : wstk_cp.length = c.wcap) (hcp_inv : RelocCopyInv s3 lit.toNat k_bv.toNat wstk_cp)
    (hfit3 : s3.core.wlen + sz3.toNat ≤ c.wcap) (hk_lt : k_bv.toNat < sz3.toNat)
    (hoff_lt : off3.toNat + k_bv.toNat < wstk_cp.length)
    (hrm : (FullMem c { s3 with
      core := { s3.core with wstk := (wstk_cp.set (s3.core.wlen + k_bv.toNat)
        wstk_cp[off3.toNat + k_bv.toNat]).set (off3.toNat + k_bv.toNat) 0xFFFFFFFF#32 } } ⋆ R)
      mw) :
    sz3.toNat - (k_bv.toNat + 1) < sz3.toNat - k_bv.toNat ∧
    WPushRelocCopyInv c s3 R lit sz3 (sz3.toNat - (k_bv.toNat + 1)) (k_bv + 1#64, ()) mw := by
  have hwcap32 := wpush_wcap_lt32 c; have hwl := hlen3.core_ok.wlen_le
  have hreloc := wpush_reloc_step_c0 hlay3 (by rw [hlen3.core_ok.wstk_len_arr]; exact hwl)
    hlit3 (by rw [← hsz3]; exact hk_lt) hcp_inv (by rw [hcp_len]; omega)
  rw [← hoff3] at hreloc; dsimp only at hreloc
  rw [← (by rw [List.getElem?_eq_getElem hoff_lt]; rfl :
    wstk_cp[off3.toNat + k_bv.toNat] = wstk_cp[off3.toNat + k_bv.toNat]?.getD 0#32)] at hreloc
  have hk1 : (k_bv + 1#64).toNat = k_bv.toNat + 1 := by c0_bv_omega
  exact ⟨by omega, _, by dsimp only; rw [hk1]; omega, by dsimp only; rw [hk1],
    by simp [hcp_len], by dsimp only; rw [hk1]; exact hreloc, hrm⟩

theorem wpush_reloc_p0_bounds {c : FullCfg} {s3 : FullState}
    {sz3 k_bv : Val i64} {wstk_cp : List (BitVec 32)}
    (hcp_len : wstk_cp.length = c.wcap) (hk_eq : k_bv.toNat = sz3.toNat)
    (hfit3 : s3.core.wlen + sz3.toNat + 1 ≤ c.wcap) :
    (BitVec.ofNat 64 s3.core.wlen + sz3).toNat = s3.core.wlen + sz3.toNat ∧
    (BitVec.ofNat 64 s3.core.wlen + k_bv).toNat < wstk_cp.length := by
  have hwcap32 := wpush_wcap_lt32 c
  have hp0 : (BitVec.ofNat 64 s3.core.wlen + sz3).toNat = s3.core.wlen + sz3.toNat := by c0_bv_omega
  exact ⟨hp0, by rw [BitVec.eq_of_toNat_eq hk_eq, hp0, hcp_len]; omega⟩

theorem wpush_reloc_fill_init {c : FullCfg} {s3 : FullState} {R : Mem 64 → Prop}
    {sz3 ncap3 : Val i64} {w0 w1 cnt : Val i32} {wstk_cp wstk_w : List (BitVec 32)}
    {mw2 : Mem 64}
    (hlen3 : s3.LengthsOk c) (hsz3_lo : sz3.toNat + cnt.toNat ≤ ncap3.toNat)
    (_hlo_fit : cnt.toNat ≤ 2) (hwl_w : wstk_w.length = c.wcap)
    (hpr_w : ∀ i < s3.core.wlen + sz3.toNat, wstk_w[i]? = wstk_cp[i]?)
    (h0_w : wstk_w[s3.core.wlen + sz3.toNat]? = some w0)
    (h1_w : cnt.toNat = 2 → wstk_w[s3.core.wlen + sz3.toNat + 1]? = some w1)
    (hmw2 : (FullMem c { s3 with core := { s3.core with wstk := wstk_w } } ⋆ R) mw2) :
    WPushRelocFillInv c s3 R sz3 ncap3 w0 w1 cnt wstk_cp
      (ncap3.toNat - (sz3.toNat + cnt.toNat)) (sz3 + BitVec.setWidth 64 cnt, ()) mw2 := by
  have hle_wl := hlen3.core_ok.wlen_le; have := cnt.isLt
  have hj0 : (sz3 + BitVec.setWidth 64 cnt).toNat = sz3.toNat + cnt.toNat := by c0_bv_omega
  exact ⟨wstk_w, by dsimp only; rw [hj0]; omega, by dsimp only; rw [hj0]; omega,
    by dsimp only; rw [hj0], hwl_w, hpr_w, h0_w, h1_w, hmw2⟩

theorem wpush_reloc_fill_next_bounds {c : FullCfg} {s3 : FullState}
    {ncap3 j_bv : Val i64} {wstk_f : List (BitVec 32)}
    (hfl_len : wstk_f.length = c.wcap) (hj_lt : j_bv.toNat < ncap3.toNat)
    (hfit3 : s3.core.wlen + ncap3.toNat ≤ c.wcap) :
    (BitVec.ofNat 64 s3.core.wlen + j_bv).toNat = s3.core.wlen + j_bv.toNat ∧
    (BitVec.ofNat 64 s3.core.wlen + j_bv).toNat < wstk_f.length := by
  have hwcap32 := wpush_wcap_lt32 c
  have hj_eq : (BitVec.ofNat 64 s3.core.wlen + j_bv).toNat = s3.core.wlen + j_bv.toNat := by
    c0_bv_omega
  exact ⟨hj_eq, by rw [hj_eq, hfl_len]; omega⟩

theorem wpush_reloc_fill_next {c : FullCfg} {s3 : FullState} {R : Mem 64 → Prop}
    {sz3 ncap3 j_bv : Val i64} {w0 w1 cnt : Val i32} {wstk_cp wstk_f : List (BitVec 32)}
    {mw3 : Mem 64}
    (hfl_len : wstk_f.length = c.wcap) (hj_lo : sz3.toNat + cnt.toNat ≤ j_bv.toNat)
    (hj_lt : j_bv.toNat < ncap3.toNat)
    (hpr_f : ∀ i < s3.core.wlen + sz3.toNat, wstk_f[i]? = wstk_cp[i]?)
    (h0_f : wstk_f[s3.core.wlen + sz3.toNat]? = some w0)
    (h1_f : cnt.toNat = 2 → wstk_f[s3.core.wlen + sz3.toNat + 1]? = some w1)
    (hc12 : cnt.toNat = 1 ∨ cnt.toNat = 2)
    (hrmf : (FullMem c { s3 with core := { s3.core with
      wstk := wstk_f.set (s3.core.wlen + j_bv.toNat) 0xFFFFFFFF#32 } } ⋆ R) mw3) :
    ncap3.toNat - (j_bv.toNat + 1) < ncap3.toNat - j_bv.toNat ∧
    WPushRelocFillInv c s3 R sz3 ncap3 w0 w1 cnt wstk_cp
      (ncap3.toNat - (j_bv.toNat + 1)) (j_bv + 1#64, ()) mw3 := by
  have hwcap32 := wpush_wcap_lt32 c
  have hj1 : (j_bv + 1#64).toNat = j_bv.toNat + 1 := by c0_bv_omega
  exact ⟨by omega, _, by dsimp only; rw [hj1]; omega, by dsimp only; rw [hj1]; omega,
    by dsimp only; rw [hj1], by simp [hfl_len],
    fun i hi => by rw [List.getElem?_set_ne (by omega)]; exact hpr_f i hi,
    by rw [List.getElem?_set_ne (by omega)]; exact h0_f,
    fun hc2 => by rw [List.getElem?_set_ne (by omega)]; exact h1_f hc2, hrmf⟩

end

end LeanQbe.T.Examples.Kissat.Proof.Watch
