/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Watch.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Watch.Wp3a

import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics1
import LeanQbe.T.Examples.Kissat.Proof.Spec.MemBridges

/-! # Watch WP Proofs Part 3b: Helper Lemmas for `full_watch_push_slow_m6_wp`

Pure state, layout, arithmetic, and `FullMem` helpers extracted from
`full_watch_push_slow_m6_wp` to keep `Wp3.lean` concise (`<= 450` LOC/decl). -/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Watch

open Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open Kraken.Bedrock2.Test
open scoped FullArenaTactics

public section

@[expose] def WPushInvState (c : FullCfg) (s : FullState) (R : Mem 64 → Prop)
    (s2 : FullState) (m2 : Mem 64) : Prop :=
  s2.LengthsOk c ∧
  WatchStackLayout s2.core ∧
  WatchPresAll s s2 ∧
  1 ≤ s2.core.wlen ∧
  (∃ wvec2 wstk2 wsort2 wlen2 wusable2,
    s2 = { s with
      core := { s.core with
        wvec := wvec2, wstk := wstk2, wlen := wlen2, wusable := wusable2 }
      scratch := { s.scratch with wsort := wsort2 } }) ∧
  (FullMem c s2 ⋆ R) m2

theorem wpush_inv_state_self {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hlen : s.LengthsOk c) (hlay : WatchStackLayout s.core) (hw1 : 1 ≤ s.core.wlen)
    (hm : (FullMem c s ⋆ R) m) :
    WPushInvState c s R s m :=
  ⟨hlen, hlay, watchPresAll_refl s, hw1,
    ⟨s.core.wvec, s.core.wstk, s.scratch.wsort, s.core.wlen, s.core.wusable, rfl⟩, hm⟩

theorem wpush_inv_state_defrag {c : FullCfg} {s s2 : FullState} {R : Mem 64 → Prop}
    {wvec' wstk' wsort' : List (BitVec 32)} {wlen' : Nat} {m2 m' : Mem 64}
    (hinv2 : WPushInvState c s R s2 m2)
    (hlen' : ({ s2 with
      core := { s2.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := 0#64 }
      scratch := { s2.scratch with wsort := wsort' } } : FullState).LengthsOk c)
    (hlay' : WatchStackLayout
      ({ s2.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := 0#64 }))
    (hw1' : 1 ≤ s2.core.wlen → 1 ≤ wlen')
    (hpres' : ∀ l < 2 * s2.core.cur_vars,
      wSz wvec' l = fullWatchSize s2 l ∧
      ∀ k < fullWatchSize s2 l, wstk'[wOff wvec' l + k]? = s2.core.wstk[fullWatchOff s2 l + k]?)
    (hm' : (FullMem c
      { s2 with
        core := { s2.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := 0#64 }
        scratch := { s2.scratch with wsort := wsort' } } ⋆ R) m') :
    let s3 : FullState :=
      { s with
        core := { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := 0#64 }
        scratch := { s.scratch with wsort := wsort' } }
    WPushInvState c s R s3 m' := by
  obtain ⟨_, _, hpres2, hw12, ⟨_, _, _, _, _, hs2_eq⟩, _⟩ := hinv2
  subst hs2_eq
  have hpres3 : WatchPresAll s
      { s with
        core := { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := 0#64 }
        scratch := { s.scratch with wsort := wsort' } } :=
    watchPresAll_trans hpres2 ⟨rfl, hpres'⟩
  exact ⟨hlen', hlay', hpres3, hw1' hw12, ⟨wvec', wstk', wsort', wlen', 0#64, rfl⟩, hm'⟩

theorem wpush_inv_core_eq {c : FullCfg} {s s2 : FullState} {R : Mem 64 → Prop}
    {m2 : Mem 64} (hinv2 : WPushInvState c s R s2 m2) :
    s2.core.cur_vars = s.core.cur_vars ∧
    s2.core.wlen < 2 ^ 32 ∧
    c.wcap < 2 ^ 32 := by
  obtain ⟨hlen2, _, hpres2, _, _, _⟩ := hinv2
  exact ⟨hpres2.1, Nat.lt_of_le_of_lt hlen2.core_ok.wlen_le (wpush_wcap_lt32 c),
    wpush_wcap_lt32 c⟩

theorem full_state_update_wpush_no_wu {s s3 : FullState}
    {wv3 ws3 wso3 : List (BitVec 32)} {wl3 : Nat} {wu3 : BitVec 64}
    (hs3 : s3 = { s with
      core := { s.core with wvec := wv3, wstk := ws3, wlen := wl3, wusable := wu3 }
      scratch := { s.scratch with wsort := wso3 } })
    (wv4 ws4 : List (BitVec 32)) (wl4 : Nat) :
    { s3 with core := { s3.core with wvec := wv4, wstk := ws4, wlen := wl4 } } =
    { s with
      core := { s.core with wvec := wv4, wstk := ws4, wlen := wl4, wusable := wu3 }
      scratch := { s.scratch with wsort := wso3 } } := by
  subst hs3; rfl

theorem wpush_wvec_lt {c : FullCfg} {s2 : FullState} {lit : Val i32}
    (hlen2 : s2.LengthsOk c) (hlit2 : lit.toNat < 2 * s2.core.cur_vars) :
    2 * lit.toNat < s2.core.wvec.length ∧
    2 * lit.toNat + 1 < s2.core.wvec.length ∧
    (lit.setWidth 64 <<< 1).toNat < s2.core.wvec.length ∧
    (lit.setWidth 64 <<< 1 + 1).toNat < s2.core.wvec.length ∧
    2 * lit.toNat % 2 ^ 64 < s2.core.wvec.length ∧
    (2 * lit.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 < s2.core.wvec.length ∧
    2 * lit.toNat % 2 ^ 64 = 2 * lit.toNat ∧
    (2 * lit.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 = 2 * lit.toNat + 1 := by
  have hcv := hlen2.core_ok.cur_vars_le
  have hwv := hlen2.core_ok.wvec_len
  have h0 : 2 * lit.toNat < s2.core.wvec.length := by rw [hwv]; omega
  have h1 : 2 * lit.toNat + 1 < s2.core.wvec.length := by rw [hwv]; omega
  have hm0 : 2 * lit.toNat % 2 ^ 64 = 2 * lit.toNat := Nat.mod_eq_of_lt (by omega)
  have h1bv : BitVec.toNat (1 : BitVec 64) = 1 := rfl
  have hm1 : (2 * lit.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 = 2 * lit.toNat + 1 := by
    rw [h1bv]; exact Nat.mod_eq_of_lt (by omega)
  exact ⟨h0, h1, by rw [wpush_lit2]; exact h0, by rw [wpush_lit2p1]; exact h1,
    by rw [hm0]; exact h0, by rw [hm1]; exact h1, hm0, hm1⟩

@[expose] def WPushAppendInv (c : FullCfg) (s : FullState) (R : Mem 64 → Prop)
    (p : Nat) (w0 w1 cnt : Val i32) (wstk0 wstk' : List (BitVec 32)) (mw : Mem 64) : Prop :=
  wstk'.length = c.wcap ∧
  (∀ i, i < p ∨ p + cnt.toNat ≤ i → wstk'[i]? = wstk0[i]?) ∧
  wstk'[p]? = some w0 ∧
  (cnt.toNat = 2 → wstk'[p + 1]? = some w1) ∧
  (FullMem c { s with core := { s.core with wstk := wstk' } } ⋆ R) mw

theorem wpush_append_set2 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {p : Nat} {w0 w1 cnt : Val i32} {wstk0 : List (BitVec 32)} {mw : Mem 64}
    (hlen0 : wstk0.length = c.wcap) (hp2 : p + 2 ≤ c.wcap) (hc2 : cnt.toNat = 2)
    (hmw : (FullMem c { s with core := { s.core with
      wstk := (wstk0.set p w0).set (p + 1) w1 } } ⋆ R) mw) :
    ∃ wstk', WPushAppendInv c s R p w0 w1 cnt wstk0 wstk' mw := by
  have ⟨hwl, hpr, h0, h1⟩ := wpush_wstk_set2_ok (p := p) (w0 := w0) (w1 := w1) (cnt := cnt)
    hlen0 hp2 hc2
  exact ⟨_, hwl, hpr, h0, h1, hmw⟩

theorem wpush_append_set1 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {p : Nat} {w0 w1 cnt : Val i32} {wstk0 : List (BitVec 32)} {mw : Mem 64}
    (hlen0 : wstk0.length = c.wcap) (hp1 : p + 1 ≤ c.wcap) (hc1 : cnt.toNat = 1)
    (hmw : (FullMem c { s with core := { s.core with wstk := wstk0.set p w0 } } ⋆ R) mw) :
    ∃ wstk', WPushAppendInv c s R p w0 w1 cnt wstk0 wstk' mw := by
  have ⟨hwl, hpr, h0, h1⟩ := wpush_wstk_set1_ok (p := p) (w0 := w0) (w1 := w1) (cnt := cnt)
    hlen0 (by omega) (by omega) (by omega)
  exact ⟨_, hwl, hpr, h0, h1, hmw⟩

theorem wpush_caseA_wlen_bv {c : FullCfg} {s3 : FullState} (hfit : s3.core.wlen < c.wcap) :
    (BitVec.ofNat 64 s3.core.wlen).toNat = s3.core.wlen ∧
    (BitVec.ofNat 64 s3.core.wlen + (1 : BitVec 64)).toNat = s3.core.wlen + 1 := by
  have hwcap32 := wpush_wcap_lt32 c
  have h0 : (BitVec.ofNat 64 s3.core.wlen).toNat = s3.core.wlen := Nat.mod_eq_of_lt (by omega)
  refine ⟨h0, ?_⟩
  rw [BitVec.toNat_add, h0, show (1 : BitVec 64).toNat = 1 from rfl]
  exact Nat.mod_eq_of_lt (by omega)

theorem wpush_caseA_fin_setup {c : FullCfg} {s s3 : FullState}
    {wv3 ws3 wso3 : List (BitVec 32)} {wl3 : Nat} {wu3 : BitVec 64}
    {lit cnt : Val i32}
    (hs3 : s3 = { s with
      core := { s.core with wvec := wv3, wstk := ws3, wlen := wl3, wusable := wu3 }
      scratch := { s.scratch with wsort := wso3 } })
    (hlen3 : s3.LengthsOk c) (hlit3 : lit.toNat < 2 * s3.core.cur_vars)
    (hc12 : cnt.toNat = 1 ∨ cnt.toNat = 2) (hfit3 : s3.core.wlen + cnt.toNat ≤ c.wcap) :
    2 * lit.toNat < s3.core.wvec.length ∧
    2 * lit.toNat + 1 <
      (s3.core.wvec.set (2 * lit.toNat) (BitVec.ofNat 32 s3.core.wlen)).length ∧
    (BitVec.ofNat 64 s3.core.wlen + BitVec.setWidth 64 cnt).toNat = s3.core.wlen + cnt.toNat ∧
    (BitVec.ofNat 64 s3.core.wlen).setWidth 32 = BitVec.ofNat 32 s3.core.wlen ∧
    wso3.length = 2 * c.max_vars := by
  have hwcap32 := wpush_wcap_lt32 c
  have h0 : 2 * lit.toNat < s3.core.wvec.length := by
    rw [hlen3.core_ok.wvec_len]; have := hlen3.core_ok.cur_vars_le; omega
  have h1 : 2 * lit.toNat + 1 <
      (s3.core.wvec.set (2 * lit.toNat) (BitVec.ofNat 32 s3.core.wlen)).length := by
    simp [hlen3.core_ok.wvec_len]; have := hlen3.core_ok.cur_vars_le; omega
  have hadd : (BitVec.ofNat 64 s3.core.wlen + BitVec.setWidth 64 cnt).toNat =
      s3.core.wlen + cnt.toNat := by
    have hc_lt : cnt.toNat ≤ 2 := by omega
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth,
      Nat.mod_eq_of_lt (by omega : s3.core.wlen < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : cnt.toNat < 2 ^ 64)]
    exact Nat.mod_eq_of_lt (by omega)
  have h32 : (BitVec.ofNat 64 s3.core.wlen).setWidth 32 = BitVec.ofNat 32 s3.core.wlen := by
    apply BitVec.eq_of_toNat_eq; simp
  exact ⟨h0, h1, hadd, h32, (hs3 ▸ hlen3).scratch_ok.wsort_len⟩

theorem wpush_bv64_add_off_sz_1 {p : Nat} {a b : Val i64}
    (hp : (a + b).toNat = p) (hlt : p + 1 < 2 ^ 64) :
    (a + b + (1 : BitVec 64)).toNat = p + 1 := by
  rw [BitVec.toNat_add, hp, show (1 : BitVec 64).toNat = 1 from rfl]
  exact Nat.mod_eq_of_lt hlt

theorem wpush_case_pos1_lt {c : FullCfg} {s2 : FullState} {lit : Val i32} {p : Nat}
    (hlen2 : s2.LengthsOk c)
    (hwv_lt0 : 2 * lit.toNat < s2.core.wvec.length)
    (hwv_lt1 : 2 * lit.toNat + 1 < s2.core.wvec.length)
    (_hwv_lt0_bv : (lit.setWidth 64 <<< 1).toNat < s2.core.wvec.length)
    (hwv_lt1_bv : (lit.setWidth 64 <<< 1 + 1).toNat < s2.core.wvec.length)
    (hj0 : 2 * lit.toNat % 2 ^ 64 < s2.core.wvec.length)
    (hj1 : (2 * lit.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 < s2.core.wvec.length)
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
  have hwcap32 := wpush_wcap_lt32 c
  have hp1 := wpush_bv64_add_off_sz_1 hpos_eq (by omega)
  have hm0 : 2 * lit.toNat % 2 ^ 64 = 2 * lit.toNat := Nat.mod_eq_of_lt (by omega)
  have hm1 : (2 * lit.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 = 2 * lit.toNat + 1 := by
    rw [show BitVec.toNat (1 : BitVec 64) = 1 from rfl]; exact Nat.mod_eq_of_lt (by omega)
  have hlt_m : (s2.core.wvec[2 * lit.toNat % 2 ^ 64].toNat +
      s2.core.wvec[(2 * lit.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64].toNat +
      BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 = p + 1 := by
    simp only [hm0, hm1]
    simp only [wpush_lit2, wpush_lit2p1] at hpos_eq
    have hlt0 : (s2.core.wvec[2 * lit.toNat]'hwv_lt0).toNat < 2 ^ 32 := BitVec.isLt _
    have hlt1 : (s2.core.wvec[2 * lit.toNat + 1]'hwv_lt1).toNat < 2 ^ 32 := BitVec.isLt _
    rw [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_setWidth,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)] at hpos_eq
    simp only [show BitVec.toNat (1 : BitVec 64) = 1 from rfl, hpos_eq]
    exact Nat.mod_eq_of_lt (by omega)
  refine ⟨hp1, by rw [hlen2.core_ok.wstk_len_arr, hp1]; omega,
    by rw [List.length_set, hlen2.core_ok.wstk_len_arr, hp1]; omega,
    by rw [hlt_m, hlen2.core_ok.wstk_len_arr]; omega⟩

theorem wpush_caseB_bounds {c : FullCfg} {s2 : FullState} {lit cnt : Val i32}
    (hlen2 : s2.LengthsOk c) (hlay2 : WatchStackLayout s2.core)
    (hlit2 : lit.toNat < 2 * s2.core.cur_vars)
    (hwv_lt0 : 2 * lit.toNat < s2.core.wvec.length)
    (hwv_lt1 : 2 * lit.toNat + 1 < s2.core.wvec.length)
    (_hwv_lt0_bv : (lit.setWidth 64 <<< 1).toNat < s2.core.wvec.length)
    (hwv_lt1_bv : (lit.setWidth 64 <<< 1 + 1).toNat < s2.core.wvec.length)
    (hj0 : 2 * lit.toNat % 2 ^ 64 < s2.core.wvec.length)
    (hj1 : (2 * lit.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 < s2.core.wvec.length)
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
  have hwcap32 := wpush_wcap_lt32 c
  have hle := hlen2.core_ok.wlen_le
  have hbd := hlay2.bounds lit.toNat hlit2
  have hoff_eq : wOff s2.core.wvec lit.toNat + wSz s2.core.wvec lit.toNat = s2.core.wlen := by
    have h := congrArg BitVec.toNat hbc_eq
    simp only [show BitVec.toNat (1 : BitVec 64) = 1 from rfl,
      Nat.mod_eq_of_lt (by omega : 2 * lit.toNat < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : 2 * lit.toNat + 1 < 2 ^ 64),
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : s2.core.wlen < 2 ^ 64)] at h
    rw [wpush_bv_off_sz_add hwv_lt0 hwv_lt1 (by omega)] at h
    exact h
  have hfitB : s2.core.wlen + cnt.toNat ≤ c.wcap := by
    rw [Nat.mod_eq_of_lt (by omega : s2.core.wlen < 2 ^ 64),
      show 2 ^ 64 - s2.core.wlen + c.wcap = 2 ^ 64 + (c.wcap - s2.core.wlen) by omega,
      Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)] at hfit_bv
    omega
  have hpos_eq :
      (BitVec.setWidth 64 s2.core.wvec[(lit.setWidth 64 <<< 1).toNat] +
        BitVec.setWidth 64 s2.core.wvec[(lit.setWidth 64 <<< 1 + 1).toNat]).toNat =
        s2.core.wlen := by
    simp only [wpush_lit2, wpush_lit2p1]
    rw [wpush_bv_off_sz_add hwv_lt0 hwv_lt1 (by omega), hoff_eq]
  have hpos_lt :
      (BitVec.setWidth 64 s2.core.wvec[(lit.setWidth 64 <<< 1).toNat] +
        BitVec.setWidth 64 s2.core.wvec[(lit.setWidth 64 <<< 1 + 1).toNat]).toNat <
        s2.core.wstk.length := by
    rw [hlen2.core_ok.wstk_len_arr, hpos_eq]; omega
  exact ⟨hoff_eq, hfitB, hpos_eq, hpos_lt⟩

theorem wpush_caseB_mem_rw {c : FullCfg} {s2 : FullState} {lit cnt : Val i32}
    (hlen2 : s2.LengthsOk c) (hlay2 : WatchStackLayout s2.core)
    (hlit2 : lit.toNat < 2 * s2.core.cur_vars)
    (hwv_lt0 : 2 * lit.toNat < s2.core.wvec.length)
    (hwv_lt1 : 2 * lit.toNat + 1 < s2.core.wvec.length)
    (_hwv_lt0_bv : (lit.setWidth 64 <<< 1).toNat < s2.core.wvec.length)
    (_hwv_lt1_bv : (lit.setWidth 64 <<< 1 + 1).toNat < s2.core.wvec.length)
    (hoff_eq : wOff s2.core.wvec lit.toNat + wSz s2.core.wvec lit.toNat = s2.core.wlen)
    (hfitB : s2.core.wlen + cnt.toNat ≤ c.wcap)
    (hc12 : cnt.toNat = 1 ∨ cnt.toNat = 2) :
    ((s2.core.wvec[2 * lit.toNat + 1].setWidth 64 + cnt.setWidth 64).setWidth 32 =
      BitVec.ofNat 32 (wSz s2.core.wvec lit.toNat + cnt.toNat)) ∧
    ((s2.core.wvec[2 * lit.toNat].setWidth 64 +
      s2.core.wvec[2 * lit.toNat + 1].setWidth 64 +
      cnt.setWidth 64).toNat = s2.core.wlen + cnt.toNat) := by
  have hwcap32 := wpush_wcap_lt32 c
  have hle := hlen2.core_ok.wlen_le
  have hbd := hlay2.bounds lit.toNat hlit2
  refine ⟨wpush_bv_sz_add_cnt hwv_lt1 (by omega) (by omega),
    wpush_bv64_add3_eq hwv_lt0 hwv_lt1 (by omega) hoff_eq (by omega)⟩

theorem wpush_caseC_bounds {c : FullCfg} {s2 : FullState} {lit cnt : Val i32}
    (hlen2 : s2.LengthsOk c) (hlay2 : WatchStackLayout s2.core)
    (hlit2 : lit.toNat < 2 * s2.core.cur_vars)
    (hwv_lt0 : 2 * lit.toNat < s2.core.wvec.length)
    (hwv_lt1 : 2 * lit.toNat + 1 < s2.core.wvec.length)
    (_hwv_lt0_bv : (lit.setWidth 64 <<< 1).toNat < s2.core.wvec.length)
    (hwv_lt1_bv : (lit.setWidth 64 <<< 1 + 1).toNat < s2.core.wvec.length)
    (hj0 : 2 * lit.toNat % 2 ^ 64 < s2.core.wvec.length)
    (hj1 : (2 * lit.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 < s2.core.wvec.length)
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
  have hwcap32 := wpush_wcap_lt32 c
  have hwl := hlen2.core_ok.wlen_le
  have hbd := hlay2.bounds lit.toNat hlit2
  have hpos_eq :
      (BitVec.setWidth 64 s2.core.wvec[(lit.setWidth 64 <<< 1).toNat] +
        BitVec.setWidth 64 s2.core.wvec[(lit.setWidth 64 <<< 1 + 1).toNat]).toNat =
        wOff s2.core.wvec lit.toNat + wSz s2.core.wvec lit.toNat := by
    simp only [wpush_lit2, wpush_lit2p1]
    exact wpush_bv_off_sz_add hwv_lt0 hwv_lt1 (by omega)
  have hlt0 : (s2.core.wvec[2 * lit.toNat]'hwv_lt0).toNat < 2 ^ 32 := BitVec.isLt _
  have hlt1 : (s2.core.wvec[2 * lit.toNat + 1]'hwv_lt1).toNat < 2 ^ 32 := BitVec.isLt _
  simp only [show BitVec.toNat (1 : BitVec 64) = 1 from rfl,
    Nat.mod_eq_of_lt (by omega : 2 * lit.toNat < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : 2 * lit.toNat + 1 < 2 ^ 64)] at hleC_bv
  have hleC : wOff s2.core.wvec lit.toNat + wSz s2.core.wvec lit.toNat + cnt.toNat ≤
      s2.core.wlen := by
    have hwl_64 : s2.core.wlen < 2 ^ 64 := by omega
    simp only [wOff, wSz, List.getElem?_eq_getElem hwv_lt0, List.getElem?_eq_getElem hwv_lt1,
      Option.getD_some] at *
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hwl_64] at hleC_bv
    exact hleC_bv
  have hm0 : (s2.core.wvec[2 * lit.toNat % 2 ^ 64].toNat +
      s2.core.wvec[(2 * lit.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64].toNat) % 2 ^ 64 =
      wOff s2.core.wvec lit.toNat + wSz s2.core.wvec lit.toNat := by
    simp only [show BitVec.toNat (1 : BitVec 64) = 1 from rfl,
      Nat.mod_eq_of_lt (by omega : 2 * lit.toNat < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : 2 * lit.toNat + 1 < 2 ^ 64),
      wOff, wSz, List.getElem?_eq_getElem hwv_lt0, List.getElem?_eq_getElem hwv_lt1,
      Option.getD_some]
    exact Nat.mod_eq_of_lt (by omega)
  refine ⟨hpos_eq, hleC, by rw [hlen2.core_ok.wstk_len_arr, hpos_eq]; omega,
    by rw [hm0, hlen2.core_ok.wstk_len_arr]; omega⟩

theorem wpush_caseC_sent0 {s2 : FullState} {lit : Val i32}
    (hwv_lt0 : 2 * lit.toNat < s2.core.wvec.length)
    (hwv_lt1 : 2 * lit.toNat + 1 < s2.core.wvec.length)
    (hj0 : 2 * lit.toNat % 2 ^ 64 < s2.core.wvec.length)
    (hj1 : (2 * lit.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 < s2.core.wvec.length)
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
  have hm_eq :
      (s2.core.wvec[2 * lit.toNat % 2 ^ 64].toNat +
        s2.core.wvec[(2 * lit.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64].toNat) % 2 ^ 64 =
        wOff s2.core.wvec lit.toNat + wSz s2.core.wvec lit.toNat := by
    have hlt0 : (s2.core.wvec[2 * lit.toNat]'hwv_lt0).toNat < 2 ^ 32 := BitVec.isLt _
    have hlt1 : (s2.core.wvec[2 * lit.toNat + 1]'hwv_lt1).toNat < 2 ^ 32 := BitVec.isLt _
    simp only [show BitVec.toNat (1 : BitVec 64) = 1 from rfl,
      Nat.mod_eq_of_lt (by omega : 2 * lit.toNat < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : 2 * lit.toNat + 1 < 2 ^ 64),
      wOff, wSz, List.getElem?_eq_getElem hwv_lt0, List.getElem?_eq_getElem hwv_lt1,
      Option.getD_some]
    exact Nat.mod_eq_of_lt (by omega)
  have hget := List.getElem?_eq_getElem hpos_lt
  rw [hsent0] at hget
  rw [hm_eq] at hget
  exact hget

theorem wpush_caseC_sent1 {s2 : FullState} {lit cnt : Val i32}
    (hwv_lt0 : 2 * lit.toNat < s2.core.wvec.length)
    (hwv_lt1 : 2 * lit.toNat + 1 < s2.core.wvec.length)
    (hj0 : 2 * lit.toNat % 2 ^ 64 < s2.core.wvec.length)
    (hj1 : (2 * lit.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 < s2.core.wvec.length)
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
  have hs1_eq :
      (s2.core.wvec[2 * lit.toNat % 2 ^ 64].toNat +
        s2.core.wvec[(2 * lit.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64].toNat +
        BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 =
        wOff s2.core.wvec lit.toNat + wSz s2.core.wvec lit.toNat + 1 := by
    have hlt0 : (s2.core.wvec[2 * lit.toNat]'hwv_lt0).toNat < 2 ^ 32 := BitVec.isLt _
    have hlt1 : (s2.core.wvec[2 * lit.toNat + 1]'hwv_lt1).toNat < 2 ^ 32 := BitVec.isLt _
    simp only [show BitVec.toNat (1 : BitVec 64) = 1 from rfl,
      Nat.mod_eq_of_lt (by omega : 2 * lit.toNat < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : 2 * lit.toNat + 1 < 2 ^ 64),
      wOff, wSz, List.getElem?_eq_getElem hwv_lt0, List.getElem?_eq_getElem hwv_lt1,
      Option.getD_some]
    exact Nat.mod_eq_of_lt (by omega)
  intro k hk
  rcases Nat.lt_succ_iff_lt_or_eq.mp (by omega : k < 1 + 1) with hk0 | hk1
  · have : k = 0 := by omega
    subst this; simpa using hsent0'
  · subst hk1
    have hget := List.getElem?_eq_getElem hpos1_lt
    rw [hsent1] at hget
    rw [hs1_eq] at hget
    exact hget

theorem wpush_nc1_nz {s2 : FullState} {lit : Val i32}
    (hwv_lt1 : 2 * lit.toNat + 1 < s2.core.wvec.length)
    (hj1 : (2 * lit.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 < s2.core.wvec.length)
    (hwv_lt1_bv : (lit.setWidth 64 <<< 1 + 1).toNat < s2.core.wvec.length)
    (hsz_nz :
      ¬ BitVec.setWidth 64 s2.core.wvec[(2 * lit.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64] =
        0) :
    (s2.core.wvec[(lit.setWidth 64 <<< 1 + 1).toNat].setWidth 64 <<< 1).toNat =
      if wSz s2.core.wvec lit.toNat = 0 then 2 else 2 * wSz s2.core.wvec lit.toNat := by
  simp only [show BitVec.toNat (1 : BitVec 64) = 1 from rfl,
    Nat.mod_eq_of_lt (by omega : 2 * lit.toNat + 1 < 2 ^ 64)] at hsz_nz
  simp only [wpush_lit2p1]
  have hsz_pos : 0 < wSz s2.core.wvec lit.toNat :=
    wpush_list_zext64_pos hwv_lt1 hwv_lt1 rfl hsz_nz
  have hnz : wSz s2.core.wvec lit.toNat ≠ 0 := Nat.ne_of_gt hsz_pos
  have hlt1 : (s2.core.wvec[2 * lit.toNat + 1]'hwv_lt1).toNat < 2 ^ 32 := BitVec.isLt _
  simp only [wSz, List.getElem?_eq_getElem hwv_lt1, Option.getD_some] at hnz ⊢
  split <;> rename_i hc_eq
  · exact absurd hc_eq hnz
  · rw [BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, Nat.shiftLeft_eq, Nat.pow_one,
      Nat.mod_eq_of_lt (by omega : _ < 2 ^ 64), Nat.mod_eq_of_lt (by omega), Nat.mul_comm]

theorem wpush_nc2_cmp {s2 : FullState} {lit cnt : Val i32}
    (hwv_lt1 : 2 * lit.toNat + 1 < s2.core.wvec.length)
    (hj1 : (2 * lit.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 < s2.core.wvec.length)
    (hwv_lt1_bv : (lit.setWidth 64 <<< 1 + 1).toNat < s2.core.wvec.length)
    (hc12 : cnt.toNat = 1 ∨ cnt.toNat = 2)
    {nc1 : Val i64} {bound : Nat}
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
  have hlt1 : (s2.core.wvec[2 * lit.toNat + 1]'hwv_lt1).toNat < 2 ^ 32 := BitVec.isLt _
  have hm1 : (2 * lit.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 = 2 * lit.toNat + 1 := by
    rw [show BitVec.toNat (1 : BitVec 64) = 1 from rfl]; exact Nat.mod_eq_of_lt (by omega)
  simp only [wpush_lit2p1]
  have hadd : (s2.core.wvec[2 * lit.toNat + 1].setWidth 64 + cnt.setWidth 64).toNat =
      wSz s2.core.wvec lit.toNat + cnt.toNat := by
    simp only [wSz, List.getElem?_eq_getElem hwv_lt1, Option.getD_some,
      BitVec.toNat_add, BitVec.toNat_setWidth]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  refine ⟨fun _ => by rw [hadd]; omega, fun hge => by
    simp only [hm1] at hge
    have hsz_e : wSz s2.core.wvec lit.toNat = (s2.core.wvec[2 * lit.toNat + 1]'hwv_lt1).toNat := by
      simp [wSz, List.getElem?_eq_getElem hwv_lt1]
    rw [← hsz_e, Nat.mod_eq_of_lt (by omega)] at hge
    split at hnc1 <;> omega⟩

theorem wpush_fit_of_cmp {c : FullCfg} {s3 : FullState} {v : Val i64}
    (hle3 : s3.core.wlen ≤ c.wcap)
    (hfit : ¬ (2 ^ 64 - s3.core.wlen % 2 ^ 64 + c.wcap) % 2 ^ 64 < v.toNat) :
    s3.core.wlen + v.toNat ≤ c.wcap := by
  have hwcap32 := wpush_wcap_lt32 c
  rw [Nat.mod_eq_of_lt (by omega : s3.core.wlen < 2 ^ 64),
    show 2 ^ 64 - s3.core.wlen + c.wcap = 2 ^ 64 + (c.wcap - s3.core.wlen) by omega,
    Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)] at hfit
  omega

theorem wpush_jd3_fit {c : FullCfg} {s3 : FullState} {lit cnt : Val i32} {sz3 : Val i64}
    (hsz3 : sz3.toNat = wSz s3.core.wvec lit.toNat) (hc12 : cnt.toNat = 1 ∨ cnt.toNat = 2)
    (hsz3_le : sz3.toNat ≤ c.wcap) :
    wSz s3.core.wvec lit.toNat + cnt.toNat ≤ (sz3 + BitVec.setWidth 64 cnt).toNat ∧
    (sz3 + BitVec.setWidth 64 cnt).toNat ≤ max 2 (2 * c.wcap) + 2 := by
  have hwcap32 := wpush_wcap_lt32 c
  rw [BitVec.toNat_add, BitVec.toNat_setWidth, hsz3,
    Nat.mod_eq_of_lt (by omega : cnt.toNat < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]
  omega

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
    WPushRelocCopyInv c s3 R lit sz3 sz3.toNat (0#64, ()) m5 := by
  have hmem3 : (FullMem c { s3 with core := { s3.core with wstk := s3.core.wstk } } ⋆ R) m5 := by
    rcases s3 with ⟨c3, sc3⟩; rcases c3; exact hm3
  exact ⟨s3.core.wstk, Nat.zero_le _, by simp, hlen3.core_ok.wstk_len_arr,
    wpush_reloc_init s3 lit.toNat, hmem3⟩

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
  have hwcap32 := wpush_wcap_lt32 c
  have hwl := hlen3.core_ok.wlen_le
  have hk_off : (off3 + k_bv).toNat = off3.toNat + k_bv.toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
  have hk_dst : (BitVec.ofNat 64 s3.core.wlen + k_bv).toNat = s3.core.wlen + k_bv.toNat := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : s3.core.wlen < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]
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
  have hwcap32 := wpush_wcap_lt32 c
  have hwl := hlen3.core_ok.wlen_le
  have hreloc := wpush_reloc_step_c0 hlay3
    (by rw [hlen3.core_ok.wstk_len_arr]; exact hwl)
    hlit3 (by rw [← hsz3]; exact hk_lt) hcp_inv (by rw [hcp_len]; omega)
  rw [← hoff3] at hreloc
  dsimp only at hreloc
  rw [← (by rw [List.getElem?_eq_getElem hoff_lt]; rfl :
    wstk_cp[off3.toNat + k_bv.toNat] = wstk_cp[off3.toNat + k_bv.toNat]?.getD 0#32)] at hreloc
  have hk1 : (k_bv + 1#64).toNat = k_bv.toNat + 1 := by
    rw [BitVec.toNat_add, show (1#64 : BitVec 64).toNat = 1 from rfl,
      Nat.mod_eq_of_lt (by omega)]
  exact ⟨by omega, _, by dsimp only; rw [hk1]; omega, by dsimp only; rw [hk1],
    by simp [hcp_len], by dsimp only; rw [hk1]; exact hreloc, hrm⟩

theorem wpush_reloc_p0_bounds {c : FullCfg} {s3 : FullState}
    {sz3 k_bv : Val i64} {wstk_cp : List (BitVec 32)}
    (hcp_len : wstk_cp.length = c.wcap) (hk_eq : k_bv.toNat = sz3.toNat)
    (hfit3 : s3.core.wlen + sz3.toNat + 1 ≤ c.wcap) :
    (BitVec.ofNat 64 s3.core.wlen + sz3).toNat = s3.core.wlen + sz3.toNat ∧
    (BitVec.ofNat 64 s3.core.wlen + k_bv).toNat < wstk_cp.length := by
  have hwcap32 := wpush_wcap_lt32 c
  have hp0 : (BitVec.ofNat 64 s3.core.wlen + sz3).toNat = s3.core.wlen + sz3.toNat := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : s3.core.wlen < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]
  have hbv := BitVec.eq_of_toNat_eq hk_eq
  exact ⟨hp0, by rw [hbv, hp0, hcp_len]; omega⟩

theorem wpush_reloc_fill_init {c : FullCfg} {s3 : FullState} {R : Mem 64 → Prop}
    {sz3 ncap3 : Val i64} {w0 w1 cnt : Val i32} {wstk_cp wstk_w : List (BitVec 32)}
    {mw2 : Mem 64}
    (hlen3 : s3.LengthsOk c) (hsz3_lo : sz3.toNat + cnt.toNat ≤ ncap3.toNat)
    (hlo_fit : cnt.toNat ≤ 2) (hwl_w : wstk_w.length = c.wcap)
    (hpr_w : ∀ i < s3.core.wlen + sz3.toNat, wstk_w[i]? = wstk_cp[i]?)
    (h0_w : wstk_w[s3.core.wlen + sz3.toNat]? = some w0)
    (h1_w : cnt.toNat = 2 → wstk_w[s3.core.wlen + sz3.toNat + 1]? = some w1)
    (hmw2 : (FullMem c { s3 with core := { s3.core with wstk := wstk_w } } ⋆ R) mw2) :
    WPushRelocFillInv c s3 R sz3 ncap3 w0 w1 cnt wstk_cp
      (ncap3.toNat - (sz3.toNat + cnt.toNat)) (sz3 + BitVec.setWidth 64 cnt, ()) mw2 := by
  have hle_wl := hlen3.core_ok.wlen_le
  have hj0 : (sz3 + BitVec.setWidth 64 cnt).toNat = sz3.toNat + cnt.toNat := by
    rw [BitVec.toNat_add, BitVec.toNat_setWidth,
      Nat.mod_eq_of_lt (by omega : cnt.toNat < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]
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
    rw [BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : s3.core.wlen < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]
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
  have hj1 : (j_bv + 1#64).toNat = j_bv.toNat + 1 := by
    rw [BitVec.toNat_add, show (1#64 : BitVec 64).toNat = 1 from rfl,
      Nat.mod_eq_of_lt (by omega)]
  exact ⟨by omega, _, by dsimp only; rw [hj1]; omega, by dsimp only; rw [hj1]; omega,
    by dsimp only; rw [hj1], by simp [hfl_len],
    fun i hi => by rw [List.getElem?_set_ne (by omega)]; exact hpr_f i hi,
    by rw [List.getElem?_set_ne (by omega)]; exact h0_f,
    fun hc2 => by rw [List.getElem?_set_ne (by omega)]; exact h1_f hc2,
    hrmf⟩

theorem wpush_reloc_s3_post {c : FullCfg} {s s3 : FullState} {R : Mem 64 → Prop}
    {lit w0 w1 cnt : Val i32} {Q : Post [Ty.bool]}
    {wv3 ws3 wso3 : List (BitVec 32)} {wl3 : Nat} {wu3 wu' : BitVec 64}
    {sz3 ncap3 : Val i64} {wstk_cp wstk_f : List (BitVec 32)} {mw3 : Mem 64}
    (hQ : WPushPost c s R lit w0 w1 cnt Q)
    (hlen : s.LengthsOk c) (hlen3 : s3.LengthsOk c) (hlay3 : WatchStackLayout s3.core)
    (hpres3 : WatchPresAll s s3)
    (hs3 : s3 = { s with
      core := { s.core with wvec := wv3, wstk := ws3, wlen := wl3, wusable := wu3 }
      scratch := { s.scratch with wsort := wso3 } })
    (hlit : lit.toNat < 2 * s.core.cur_vars) (hc12 : cnt.toNat = 1 ∨ cnt.toNat = 2)
    (hw0 : cnt.toNat = 1 → w0 ≠ 0xFFFFFFFF#32)
    (hw1 : cnt.toNat = 2 → w0 ≠ 0xFFFFFFFF#32 ∧ w1 ≠ 0xFFFFFFFF#32)
    (hwlen3 : 1 ≤ s3.core.wlen) (hsz3 : sz3.toNat = wSz s3.core.wvec lit.toNat)
    (hlo3 : wSz s3.core.wvec lit.toNat + cnt.toNat ≤ ncap3.toNat)
    (hfit3 : s3.core.wlen + ncap3.toNat ≤ c.wcap)
    (hcp_inv : RelocCopyInv s3 lit.toNat sz3.toNat wstk_cp)
    (hfl_len : wstk_f.length = c.wcap)
    (hpr_f : ∀ i < s3.core.wlen + sz3.toNat, wstk_f[i]? = wstk_cp[i]?)
    (h0_f : wstk_f[s3.core.wlen + sz3.toNat]? = some w0)
    (h1_f : cnt.toNat = 2 → wstk_f[s3.core.wlen + sz3.toNat + 1]? = some w1)
    (hrmf : (FullMem c { s3 with core := { s3.core with
      wvec := (s3.core.wvec.set (2 * lit.toNat)
        ((BitVec.ofNat 64 s3.core.wlen).setWidth 32)).set (2 * lit.toNat + 1)
          ((sz3 + cnt.setWidth 64).setWidth 32)
      wstk := wstk_f
      wlen := (BitVec.ofNat 64 s3.core.wlen + ncap3).toNat
      wusable := wu' } } ⋆ R) mw3) :
    Q (true, ()) mw3 := by
  have hwcap32 := wpush_wcap_lt32 c
  have hle_wl := hlen3.core_ok.wlen_le
  have hsz_add_lt : wSz s3.core.wvec lit.toNat + cnt.toNat < 2 ^ 32 := by omega
  have hw2 : (sz3 + cnt.setWidth 64).setWidth 32 =
      BitVec.ofNat 32 (wSz s3.core.wvec lit.toNat + cnt.toNat) := by
    apply BitVec.eq_of_toNat_eq
    simp [hsz3, BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
  have hw3 : (BitVec.ofNat 64 s3.core.wlen + ncap3).toNat = s3.core.wlen + ncap3.toNat := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : s3.core.wlen < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]
  have hlt3_cp := hlit; rw [← hpres3.1] at hlt3_cp
  rw [wpush_bv32_ofNat_64, hw2, hw3] at hrmf
  exact wpush_reloc_s3 hQ hlen hlen3 hlay3 hpres3 hs3 hlit hc12 hw0 hw1 hwlen3 hlo3 hfit3
    (by rw [← hsz3]; exact hcp_inv) hfl_len
    (fun i hi => hpr_f i (by rw [← hsz3] at hi; exact hi))
    (by rw [hsz3] at h0_f; exact h0_f) (fun h => by rw [hsz3] at h1_f; exact h1_f h) hrmf

end

end LeanQbe.T.Examples.Kissat.Proof.Watch
