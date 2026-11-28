/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Watch.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Watch.Wp2a
public import LeanQbe.T.Examples.Kissat.Src.Watch

import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts1
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
import LeanQbe.T.Examples.Kissat.Proof.Spec.MemBridges
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
import LeanQbe.T.Logic.C0HeadStep

/-! # Watch WP Proofs Part 3a: Helpers & Postconditions for `full_watch_push*`

Self-contained helpers imported by `Proof.Watch.Wp3` and `Proof.Watch.Wp4`:
- BitVec arithmetic bridges (`wpush_lit2`, `wpush_lit2p1`, `bv32_trunc_add`, ...)
- Watch-array offset/size projections (`wOff`, `wSz`, `WatchPresAll`, `wpush_finalize`, ...)
- Canonical `WPushPost` alias matching `Proof.Spec.fullWatchPushSpec`. -/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Watch

open Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Watch
open LeanQbe.T.Examples.Kissat.Proof.Spec
open Kraken.Bedrock2.Test

public section

/-! ## 1. BitVec & `wvec` Update Helpers -/

theorem wpush_lit2 (lit : BitVec 32) :
    (lit.setWidth 64 <<< (1 : Nat)).toNat = 2 * lit.toNat := by
  have hl := lit.isLt
  rw [BitVec.toNat_shiftLeft, zext_toNat lit (by decide), Nat.shiftLeft_eq, Nat.pow_one,
    Nat.mul_comm, Nat.mod_eq_of_lt (by omega)]

theorem wpush_lit2p1 (lit : BitVec 32) :
    ((lit.setWidth 64 <<< (1 : Nat)) + (1 : BitVec 64)).toNat = 2 * lit.toNat + 1 := by
  have hl := lit.isLt
  have h1 : (1 : BitVec 64).toNat = 1 := rfl
  rw [BitVec.toNat_add, wpush_lit2, h1, Nat.mod_eq_of_lt (by omega)]

theorem wpush_bv32_trunc_add {a : BitVec 64} {b : BitVec 32} (h : a.toNat + b.toNat < 2 ^ 32) :
    ((a + b.setWidth 64).setWidth 32).toNat = a.toNat + b.toNat := by
  have hadd : (a + b.setWidth 64).toNat = a.toNat + b.toNat := by
    rw [BitVec.toNat_add, zext_toNat b (by decide), Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.toNat_setWidth, hadd, Nat.mod_eq_of_lt h]

theorem wpush_getElem_toNat {xs : List (BitVec 32)} {i j : Nat}
    (hi : i < xs.length) (hij : i = j) : (xs[i]'hi).toNat = (xs[j]?.getD 0#32).toNat := by
  subst hij; rw [List.getElem?_eq_getElem hi, Option.getD_some]

theorem wpush_bv64_eq_zero_of_not_pos {x : BitVec 64} (h : ¬ 0 < x.toNat) : x = 0#64 :=
  BitVec.eq_of_toNat_eq (by simp only [BitVec.toNat_ofNat]; omega)

theorem wpush_bv32_eq_nat (n : Nat) (hn : n < 2 ^ 32) {x : BitVec 32}
    (h : x = BitVec.ofNat 32 n) : x.toNat = n := by
  rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

theorem wpush_bv32_ne_nat (n : Nat) (hn : n < 2 ^ 32) {x : BitVec 32}
    (h : x ≠ BitVec.ofNat 32 n) : x.toNat ≠ n := fun heq =>
  h (BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]; exact heq))

/-! ## 2. Watch Offset / Size, `WatchPresAll`, & `wpush_finalize` -/

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
    refine ⟨hs23'.trans hs12', fun k hk => ?_⟩
    exact (hst23 k (hs12' ▸ hk)).trans (hst12 k hk)⟩

theorem wvec_set_even_u {wvec : List (BitVec 32)} {l : Nat} {v : BitVec 32}
    (hl : 2 * l < wvec.length) :
    ∀ j,
      (wvec.set (2 * l) v)[2 * j + 1]? = wvec[2 * j + 1]? ∧
      (j ≠ l → (wvec.set (2 * l) v)[2 * j]? = wvec[2 * j]?) ∧
      (wvec.set (2 * l) v)[2 * l]? = some v := fun j =>
  ⟨List.getElem?_set_ne (by omega), fun hj => List.getElem?_set_ne (by omega),
    List.getElem?_set_self hl⟩

theorem wvec_set_odd_u {wvec : List (BitVec 32)} {l : Nat} {v : BitVec 32}
    (hl : 2 * l + 1 < wvec.length) :
    ∀ j,
      (wvec.set (2 * l + 1) v)[2 * j]? = wvec[2 * j]? ∧
      (j ≠ l → (wvec.set (2 * l + 1) v)[2 * j + 1]? = wvec[2 * j + 1]?) ∧
      (wvec.set (2 * l + 1) v)[2 * l + 1]? = some v := fun j =>
  ⟨List.getElem?_set_ne (by omega), fun hj => List.getElem?_set_ne (by omega),
    List.getElem?_set_self hl⟩

@[expose] def WPushPost (c : FullCfg) (s : FullState) (R : Mem 64 → Prop)
    (lit w0 w1 cnt : BitVec 32) (Q : Post [Ty.bool]) : Prop :=
  ∀ (ok : Bool) wvec' wstk' wlen' wusable' wsort' m',
    let s' : FullState :=
      { s with
        core := { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wusable' }
        scratch := { s.scratch with wsort := wsort' } }
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

theorem wpush_sentinel_disjoint {k1 : FullCoreState} (_hlay1 : WatchStackLayout k1)
    {lit dst sz needed : Nat} (_hlit : lit < 2 * k1.cur_vars)
    (_hsz : sz = fullWatchSizeCore k1 lit) (_hdst : 1 ≤ dst)
    (hbad1 : ∀ l < 2 * k1.cur_vars, l ≠ lit → 0 < fullWatchSizeCore k1 l →
      fullWatchOffCore k1 l ≤ dst + sz + needed →
      fullWatchOffCore k1 l + fullWatchSizeCore k1 l ≤ dst)
    (_hbad2 : fullWatchOffCore k1 lit < dst + sz + needed →
      fullWatchOffCore k1 lit + sz ≤ dst) :
    ∀ j < 2 * k1.cur_vars, j ≠ lit → 0 < fullWatchSizeCore k1 j →
      fullWatchOffCore k1 j + fullWatchSizeCore k1 j ≤ dst ∨
      dst + sz + needed ≤ fullWatchOffCore k1 j := by
  intro j hj hne hpos
  by_cases hlt : fullWatchOffCore k1 j < dst + sz + needed
  · exact Or.inl (hbad1 j hj hne hpos (Nat.le_of_lt hlt))
  · exact Or.inr (Nat.le_of_not_lt hlt)

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
        have hk : dst - fullWatchOffCore k1 j < fullWatchSizeCore k1 j := by omega
        have hns := hlay1.no_sentinel j hj (dst - fullWatchOffCore k1 j) hk
        rw [show fullWatchOffCore k1 j + (dst - fullWatchOffCore k1 j) = dst by omega] at hns
        exact hns (hnil dst (Nat.le_refl dst) (by omega)))

theorem wpush_finalize {s s2 : FullState} {lit cnt dst wlen' : Nat}
    {w0 w1 : BitVec 32} {wvec' wstk' wsort' : List (BitVec 32)}
    (hlay2 : WatchStackLayout s2.core) (hpres : WatchPresAll s s2)
    (hlit : lit < 2 * s.core.cur_vars) (hc12 : cnt = 1 ∨ cnt = 2)
    (hw0 : cnt = 1 → w0 ≠ 0xFFFFFFFF#32)
    (hw1 : cnt = 2 → w0 ≠ 0xFFFFFFFF#32 ∧ w1 ≠ 0xFFFFFFFF#32)
    (hwlen_le : s2.core.wlen ≤ wlen') (hdst1 : 1 ≤ dst)
    (hdst_le : dst + (wSz s2.core.wvec lit + cnt) ≤ wlen')
    (hother_wv : ∀ j < 2 * s.core.cur_vars, j ≠ lit →
      wOff wvec' j = wOff s2.core.wvec j ∧ wSz wvec' j = wSz s2.core.wvec j)
    (hlit_off : wOff wvec' lit = dst) (hlit_sz : wSz wvec' lit = wSz s2.core.wvec lit + cnt)
    (hdisj : ∀ j < 2 * s.core.cur_vars, j ≠ lit → 0 < wSz s2.core.wvec j →
      wOff s2.core.wvec j + wSz s2.core.wvec j ≤ dst ∨
      dst + (wSz s2.core.wvec lit + cnt) ≤ wOff s2.core.wvec j)
    (hother_st : ∀ j < 2 * s.core.cur_vars, j ≠ lit → ∀ k < wSz s2.core.wvec j,
      wstk'[wOff s2.core.wvec j + k]? = s2.core.wstk[wOff s2.core.wvec j + k]?)
    (hcopy : ∀ k < wSz s2.core.wvec lit,
      wstk'[dst + k]? = s2.core.wstk[wOff s2.core.wvec lit + k]?)
    (hat0 : wstk'[dst + wSz s2.core.wvec lit]? = some w0)
    (hat1 : cnt = 2 → wstk'[dst + wSz s2.core.wvec lit + 1]? = some w1)
    (wusable' : BitVec 64) :
    let s' : FullState :=
      { s with
        core := { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wusable' }
        scratch := { s.scratch with wsort := wsort' } }
    WatchStackLayout s'.core ∧
    (∀ l < 2 * s.core.cur_vars, l ≠ lit → fullWatchSize s' l = fullWatchSize s l ∧
      ∀ k < fullWatchSize s l,
        s'.core.wstk[fullWatchOff s' l + k]? = s.core.wstk[fullWatchOff s l + k]?) ∧
    fullWatchSize s' lit = fullWatchSize s lit + cnt ∧
    (∀ k < fullWatchSize s lit,
      s'.core.wstk[fullWatchOff s' lit + k]? = s.core.wstk[fullWatchOff s lit + k]?) ∧
    s'.core.wstk[fullWatchOff s' lit + fullWatchSize s lit]? = some w0 ∧
    (cnt = 2 → s'.core.wstk[fullWatchOff s' lit + fullWatchSize s lit + 1]? = some w1) := by
  intro s'
  have hcv2 : s2.core.cur_vars = s.core.cur_vars := hpres.1
  have hlit2 : lit < 2 * s2.core.cur_vars := hcv2 ▸ hlit
  have hoff_l : fullWatchOffCore s'.core lit = dst := hlit_off
  have hsz_l : fullWatchSizeCore s'.core lit = wSz s2.core.wvec lit + cnt := hlit_sz
  have hoff_o : ∀ j < 2 * s.core.cur_vars, j ≠ lit →
      fullWatchOffCore s'.core j = fullWatchOffCore s2.core j :=
    fun j hj hne => (hother_wv j hj hne).1
  have hsz_o : ∀ j < 2 * s.core.cur_vars, j ≠ lit →
      fullWatchSizeCore s'.core j = fullWatchSizeCore s2.core j :=
    fun j hj hne => (hother_wv j hj hne).2
  have hsz_lit2 : wSz s2.core.wvec lit = fullWatchSizeCore s.core lit := (hpres.2 lit hlit).1
  have hne0 : w0 ≠ 0xFFFFFFFF#32 := by rcases hc12 with rfl | rfl; exact hw0 rfl; exact (hw1 rfl).1
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_,
    by change fullWatchSizeCore s'.core lit = fullWatchSizeCore s.core lit + cnt
       rw [hsz_l, hsz_lit2], ?_, ?_, ?_⟩
  · intro l hl; by_cases hll : l = lit
    · rcases hll.symm with rfl; rw [hoff_l, hsz_l]; exact hdst_le
    · rw [hoff_o l hl hll, hsz_o l hl hll]
      exact Nat.le_trans (hlay2.bounds l (hcv2 ▸ hl)) hwlen_le
  · intro l hl hpos; by_cases hll : l = lit
    · rcases hll.symm with rfl; rw [hoff_l]; exact hdst1
    · rw [hsz_o l hl hll] at hpos; rw [hoff_o l hl hll]
      exact hlay2.pos_off l (hcv2 ▸ hl) hpos
  · intro l1 l2 h1 h2 hne hp1 hp2; by_cases hl1 : l1 = lit
    · rcases hl1.symm with rfl; have hl2 : l2 ≠ lit := hne.symm
      rw [hsz_o l2 h2 hl2] at hp2
      rw [hoff_l, hsz_l, hoff_o l2 h2 hl2, hsz_o l2 h2 hl2]; exact (hdisj l2 h2 hl2 hp2).symm
    · by_cases hl2 : l2 = lit
      · rcases hl2.symm with rfl; rw [hsz_o l1 h1 hl1] at hp1
        rw [hoff_o l1 h1 hl1, hsz_o l1 h1 hl1, hoff_l, hsz_l]; exact hdisj l1 h1 hl1 hp1
      · rw [hsz_o l1 h1 hl1] at hp1; rw [hsz_o l2 h2 hl2] at hp2
        rw [hoff_o l1 h1 hl1, hsz_o l1 h1 hl1, hoff_o l2 h2 hl2, hsz_o l2 h2 hl2]
        exact hlay2.disjoint l1 l2 (hcv2 ▸ h1) (hcv2 ▸ h2) hne hp1 hp2
  · intro l hl k hk; by_cases hll : l = lit
    · rcases hll.symm with rfl; rw [hsz_l] at hk; rw [hoff_l]
      by_cases hks : k < wSz s2.core.wvec lit
      · change wstk'[dst + k]? ≠ _; rw [hcopy k hks]; exact hlay2.no_sentinel lit hlit2 k hks
      · by_cases hk0 : k = wSz s2.core.wvec lit
        · subst hk0; change wstk'[dst + wSz s2.core.wvec lit]? ≠ _; rw [hat0]
          exact fun heq => hne0 (Option.some.inj heq)
        · have hc2 : cnt = 2 := by omega
          have hk1 : k = wSz s2.core.wvec lit + 1 := by omega
          subst hk1; change wstk'[dst + (wSz s2.core.wvec lit + 1)]? ≠ _
          rw [← Nat.add_assoc, hat1 hc2]; exact fun heq => (hw1 hc2).2 (Option.some.inj heq)
    · rw [hsz_o l hl hll] at hk; rw [hoff_o l hl hll]
      change wstk'[wOff s2.core.wvec l + k]? ≠ _
      rw [hother_st l hl hll k hk]; exact hlay2.no_sentinel l (hcv2 ▸ hl) k hk
  · intro l hl hne; have ⟨hp1, hp2⟩ := hpres.2 l hl
    have hp1' : wSz s2.core.wvec l = fullWatchSize s l := hp1
    refine ⟨(hsz_o l hl hne).trans hp1, fun k hk => ?_⟩
    change wstk'[fullWatchOffCore s'.core l + k]? = _
    rw [hoff_o l hl hne]; exact (hother_st l hl hne k (hp1' ▸ hk)).trans (hp2 k hk)
  · intro k hk; change wstk'[fullWatchOffCore s'.core lit + k]? = _
    rw [hoff_l]; exact (hcopy k (hsz_lit2 ▸ hk)).trans ((hpres.2 lit hlit).2 k hk)
  · change wstk'[fullWatchOffCore s'.core lit + fullWatchSizeCore s.core lit]? = _
    rw [hoff_l, ← hsz_lit2]; exact hat0
  · intro hc2
    change wstk'[fullWatchOffCore s'.core lit + fullWatchSizeCore s.core lit + 1]? = _
    rw [hoff_l, ← hsz_lit2]; exact hat1 hc2

theorem wpush_lengthsOk {c : FullCfg} {s : FullState}
    (hlen : s.LengthsOk c) {wvec' wstk' wsort' : List (BitVec 32)} {wlen' : Nat}
    {wusable' : BitVec 64}
    (hwv : wvec'.length = 4 * c.max_vars) (hws : wstk'.length = c.wcap)
    (hwl : wlen' ≤ c.wcap) (hwso : wsort'.length = 2 * c.max_vars) :
    FullState.LengthsOk c
      { s with
        core := { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wusable' }
        scratch := { s.scratch with wsort := wsort' } } :=
  ⟨{ hlen.core_ok with wvec_len := hwv, wstk_len_arr := hws, wlen_le := hwl },
    { hlen.scratch_ok with wsort_len := hwso }⟩

theorem wpush_wcap_lt32 (c : FullCfg) : c.wcap < 2 ^ 32 := by
  exact Nat.lt_of_lt_of_le c.hwcap (by decide)

theorem wpush_init_wlen0 {c : FullCfg} {s : FullState}
    (hlen : s.LengthsOk c) (hlay : WatchStackLayout s.core)
    (hw0 : s.core.wlen = 0) (hcap : 1 ≤ c.wcap) :
    let s1 : FullState :=
      { s with core := { s.core with wstk := s.core.wstk.set 0 0#32, wlen := 1 } }
    s1.LengthsOk c ∧ WatchStackLayout s1.core ∧ WatchPresAll s s1 := by
  intro s1
  have hlen1 : s1.LengthsOk c :=
    ⟨{ hlen.core_ok with wstk_len_arr := by simp [s1, hlen.core_ok.wstk_len_arr], wlen_le := hcap },
      hlen.scratch_ok⟩
  have hsz0 : ∀ l < 2 * s.core.cur_vars, fullWatchSizeCore s.core l = 0 := by
    intro l hl; have hb := hlay.bounds l hl; rw [hw0] at hb; omega
  have hlay1 : WatchStackLayout s1.core := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro l hl; have hb := hlay.bounds l hl
      change fullWatchOffCore s.core l + fullWatchSizeCore s.core l ≤ 1; omega
    · intro l hl hpos; exact absurd hpos (by
        change ¬0 < fullWatchSizeCore s.core l; rw [hsz0 l hl]; omega)
    · intro l1 l2 h1 _ _ hp1 _; exact absurd hp1 (by
        change ¬0 < fullWatchSizeCore s.core l1; rw [hsz0 l1 h1]; omega)
    · intro l hl idx hidx; exact absurd hidx (by
        change ¬idx < fullWatchSizeCore s.core l; rw [hsz0 l hl]; omega)
  refine ⟨hlen1, hlay1, ⟨rfl, fun l hl => ⟨rfl, fun k hk => ?_⟩⟩⟩
  exact absurd hk (by change ¬k < fullWatchSizeCore s.core l; rw [hsz0 l hl]; omega)

theorem wpush_fail_post {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {lit w0 w1 cnt : BitVec 32} {Q : Post [Ty.bool]}
    (hQ : WPushPost c s R lit w0 w1 cnt Q)
    (wvec' wstk' wsort' : List (BitVec 32)) (wlen' : Nat) (wusable' : BitVec 64)
    {m' : Mem 64}
    (hlen' :
      ({ s with
          core := { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wusable' }
          scratch := { s.scratch with wsort := wsort' } } : FullState).LengthsOk c)
    (hlay' :
      WatchStackLayout
        ({ s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wusable' }))
    (hpres :
      WatchPresAll s
        { s with
          core := { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wusable' }
          scratch := { s.scratch with wsort := wsort' } })
    (hwhy : 2 * s.core.cur_vars ≤ lit.toNat ∨ (cnt.toNat ≠ 1 ∧ cnt.toNat ≠ 2) ∨
      ({ s with
          core := { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wusable' }
          scratch := { s.scratch with wsort := wsort' } } : FullState) = s ∨
        wusable' = 0#64)
    (hm' :
      (FullMem c
        { s with
          core := { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wusable' }
          scratch := { s.scratch with wsort := wsort' } } ⋆ R) m') :
    Q (false, ()) m' := by
  let s' : FullState :=
    { s with
      core := { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wusable' }
      scratch := { s.scratch with wsort := wsort' } }
  refine hQ false wvec' wstk' wlen' wusable' wsort' m' hlen' hlay' ?_
    (fun h => absurd h (by decide)) ?_ hm'
  · intro l hl _
    have ⟨hs, hst⟩ := hpres.2 l hl
    exact ⟨hs, hst⟩
  · intro _
    refine ⟨fun hlt => ?_, hwhy⟩
    have ⟨hs, hst⟩ := hpres.2 lit.toNat hlt
    exact ⟨hs, hst⟩

theorem wpush_ok_post {c : FullCfg} {s s2 : FullState} {R : Mem 64 → Prop}
    {lit w0 w1 cnt : BitVec 32} {Q : Post [Ty.bool]}
    (hQ : WPushPost c s R lit w0 w1 cnt Q)
    (hlay2 : WatchStackLayout s2.core) (hpres : WatchPresAll s s2)
    (hlit : lit.toNat < 2 * s.core.cur_vars) (hc12 : cnt.toNat = 1 ∨ cnt.toNat = 2)
    (hw0 : cnt.toNat = 1 → w0 ≠ 0xFFFFFFFF#32)
    (hw1 : cnt.toNat = 2 → w0 ≠ 0xFFFFFFFF#32 ∧ w1 ≠ 0xFFFFFFFF#32)
    {dst wlen' : Nat} {wvec' wstk' wsort' : List (BitVec 32)} (wusable' : BitVec 64) {m' : Mem 64}
    (hlen' :
      ({ s with
          core := { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wusable' }
          scratch := { s.scratch with wsort := wsort' } } : FullState).LengthsOk c)
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
    (hm' :
      (FullMem c
        { s with
          core := { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wusable' }
          scratch := { s.scratch with wsort := wsort' } } ⋆ R) m') :
    Q (true, ()) m' := by
  obtain ⟨hlay', hoth, hsz', hcp', ha0, ha1⟩ :=
    wpush_finalize hlay2 hpres hlit hc12 hw0 hw1 hwlen_le hdst1 hdst_le hother_wv hlit_off hlit_sz
      hdisj hother_st hcopy hat0 hat1 wusable'
  exact hQ true wvec' wstk' wlen' wusable' wsort' m' hlen' hlay' hoth
    (fun _ => ⟨hlit, hc12, hsz', hcp', ha0, ha1⟩) (fun h => absurd h (by decide)) hm'

theorem wpush_caseA_fin {c : FullCfg} {s s2 : FullState} {R : Mem 64 → Prop}
    {lit w0 w1 cnt : BitVec 32} {Q : Post [Ty.bool]}
    (hQ : WPushPost c s R lit w0 w1 cnt Q)
    (hlen : s.LengthsOk c) (hlen2 : s2.LengthsOk c)
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
    (hm' :
      (FullMem c
        { s with
          core := { s.core with
            wvec := wvec', wstk := wstk', wlen := s2.core.wlen + cnt.toNat, wusable := wusable' }
          scratch := { s.scratch with wsort := wsort' } } ⋆ R) m') :
    Q (true, ()) m' := by
  have hcv2 := hpres.1
  have hlit2 : lit.toNat < 2 * s2.core.cur_vars := hcv2 ▸ hlit
  have hsz0 : wSz s2.core.wvec lit.toNat = 0 := by
    rcases hs2_so with h0 | h0
    · by_cases hne : wSz s2.core.wvec lit.toNat = 0
      · exact hne
      · exfalso
        have hp := hlay2.pos_off lit.toNat hlit2 (Nat.pos_of_ne_zero hne)
        change wOff s2.core.wvec lit.toNat ≥ 1 at hp; omega
    · exact h0
  have hwv2 : 2 * lit.toNat + 1 < s2.core.wvec.length := by
    rw [hlen2.core_ok.wvec_len]; have := hlen2.core_ok.cur_vars_le; omega
  have hwv'_len : wvec'.length = 4 * c.max_vars := by
    subst hwvec'_eq; simp [hlen2.core_ok.wvec_len]
  have hwlen32 : s2.core.wlen < 2 ^ 32 :=
    Nat.lt_of_le_of_lt hlen2.core_ok.wlen_le (wpush_wcap_lt32 c)
  have hlen' := wpush_lengthsOk (wlen' := s2.core.wlen + cnt.toNat) (wusable' := wusable')
    hlen hwv'_len hws_len hfit hwso_len
  refine wpush_ok_post hQ hlay2 hpres hlit hc12 hw0 hw1 wusable' hlen' (Nat.le_add_right _ _)
    hwlen1 (by rw [hsz0]; omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hm'
  · intro j hj hne
    have h1 := wvec_set_even_u (wvec := s2.core.wvec) (l := lit.toNat)
      (v := BitVec.ofNat 32 s2.core.wlen) (by omega)
    have h2 := wvec_set_odd_u (wvec := s2.core.wvec.set (2 * lit.toNat)
      (BitVec.ofNat 32 s2.core.wlen)) (l := lit.toNat) (v := cnt) (by simp; omega)
    subst hwvec'_eq
    exact ⟨by simp [wOff, (h2 j).1, (h1 j).2.1 hne],
      by simp [wSz, (h2 j).2.1 hne, (h1 j).1]⟩
  · subst hwvec'_eq
    have h1 := wvec_set_even_u (wvec := s2.core.wvec) (l := lit.toNat)
      (v := BitVec.ofNat 32 s2.core.wlen) (by omega)
    have h2 := wvec_set_odd_u (wvec := s2.core.wvec.set (2 * lit.toNat)
      (BitVec.ofNat 32 s2.core.wlen)) (l := lit.toNat) (v := cnt) (by simp; omega)
    simp [wOff, (h2 lit.toNat).1, (h1 lit.toNat).2.2, wpush_bv32_eq_nat _ hwlen32 rfl]
  · subst hwvec'_eq
    have h2 := wvec_set_odd_u (wvec := s2.core.wvec.set (2 * lit.toNat)
      (BitVec.ofNat 32 s2.core.wlen)) (l := lit.toNat) (v := cnt) (by simp; omega)
    simp only [wSz]; rw [(h2 lit.toNat).2.2]
    change cnt.toNat = wSz s2.core.wvec lit.toNat + cnt.toNat; omega
  · intro j hj _ _; exact Or.inl (hlay2.bounds j (hcv2 ▸ hj))
  · intro j hj _ k hk
    have hb : wOff s2.core.wvec j + k < s2.core.wlen :=
      Nat.lt_of_lt_of_le (Nat.add_lt_add_left hk _) (hlay2.bounds j (hcv2 ▸ hj))
    exact hws_lt _ hb
  · intro k hk; exact absurd hk (by omega)
  · rw [hsz0, Nat.add_zero]; exact hat0
  · intro hc2; rw [hsz0, Nat.add_zero]; exact hat1 hc2

theorem wpush_caseB_fin {c : FullCfg} {s s2 : FullState} {R : Mem 64 → Prop}
    {lit w0 w1 cnt : BitVec 32} {Q : Post [Ty.bool]}
    (hQ : WPushPost c s R lit w0 w1 cnt Q)
    (hlen : s.LengthsOk c) (hlen2 : s2.LengthsOk c)
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
    (hm' :
      (FullMem c
        { s with
          core := { s.core with
            wvec := wvec', wstk := wstk', wlen := s2.core.wlen + cnt.toNat, wusable := wusable' }
          scratch := { s.scratch with wsort := wsort' } } ⋆ R) m') :
    Q (true, ()) m' := by
  have hcv2 := hpres.1
  have hlit2 : lit.toNat < 2 * s2.core.cur_vars := hcv2 ▸ hlit
  have hdst1 : 1 ≤ wOff s2.core.wvec lit.toNat := hoff1
  have hwv'_len : wvec'.length = 4 * c.max_vars := by
    subst hwvec'_eq; simp [hlen2.core_ok.wvec_len]
  have hsz32 : wSz s2.core.wvec lit.toNat + cnt.toNat < 2 ^ 32 := by
    have : wSz s2.core.wvec lit.toNat + cnt.toNat ≤ s2.core.wlen + cnt.toNat := by omega
    exact Nat.lt_of_le_of_lt (Nat.le_trans this hfit) (wpush_wcap_lt32 c)
  have hwv2 : 2 * lit.toNat + 1 < s2.core.wvec.length := by
    rw [hlen2.core_ok.wvec_len]; have := hlen2.core_ok.cur_vars_le; omega
  have hlen' := wpush_lengthsOk (wlen' := s2.core.wlen + cnt.toNat) (wusable' := wusable')
    hlen hwv'_len hws_len hfit hwso_len
  refine wpush_ok_post hQ hlay2 hpres hlit hc12 hw0 hw1 wusable' hlen' (Nat.le_add_right _ _)
    hdst1 (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hm'
  · intro j hj hne
    subst hwvec'_eq
    exact ⟨by simp only [wOff]; rw [List.getElem?_set_ne (by omega)],
      by simp only [wSz]; rw [List.getElem?_set_ne (by omega)]⟩
  · subst hwvec'_eq
    simp only [wOff]; rw [List.getElem?_set_ne (by omega)]
  · subst hwvec'_eq
    simp only [wSz]; rw [List.getElem?_set_self hwv2]
    simp; exact hsz32
  · intro j hj hne hpj
    have hb := hlay2.bounds j (hcv2 ▸ hj)
    change wOff s2.core.wvec j + wSz s2.core.wvec j ≤ s2.core.wlen at hb
    by_cases hszp : 0 < wSz s2.core.wvec lit.toNat
    · rcases hlay2.disjoint j lit.toNat (hcv2 ▸ hj) hlit2 hne hpj hszp with h | h
      · exact Or.inl h
      · exfalso
        change wOff s2.core.wvec lit.toNat + wSz s2.core.wvec lit.toNat ≤
          wOff s2.core.wvec j at h
        omega
    · exact Or.inl (by omega)
  · intro j hj _ k hk
    exact hws_lt _ (Nat.lt_of_lt_of_le (Nat.add_lt_add_left hk _) (hlay2.bounds j (hcv2 ▸ hj)))
  · intro k hk; exact hws_lt _ (by omega)
  · rw [hend]; exact hat0
  · intro hc2; rw [hend]; exact hat1 hc2

theorem wpush_caseC_fin {c : FullCfg} {s s2 : FullState} {R : Mem 64 → Prop}
    {lit w0 w1 cnt : BitVec 32} {Q : Post [Ty.bool]}
    (hQ : WPushPost c s R lit w0 w1 cnt Q)
    (hlen : s.LengthsOk c) (hlen2 : s2.LengthsOk c)
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
    (hm' :
      (FullMem c
        { s with
          core := { s.core with
            wvec := wvec', wstk := wstk', wlen := s2.core.wlen, wusable := wusable' }
          scratch := { s.scratch with wsort := wsort' } } ⋆ R) m') :
    Q (true, ()) m' := by
  have hcv2 := hpres.1
  have hlit2 : lit.toNat < 2 * s2.core.cur_vars := hcv2 ▸ hlit
  have hdst1 : 1 ≤ wOff s2.core.wvec lit.toNat := hoff1
  have hwv'_len : wvec'.length = 4 * c.max_vars := by
    subst hwvec'_eq; simp [hlen2.core_ok.wvec_len]
  have hsz32 : wSz s2.core.wvec lit.toNat + cnt.toNat < 2 ^ 32 := by
    have hle1 : wSz s2.core.wvec lit.toNat + cnt.toNat ≤ s2.core.wlen := by omega
    exact Nat.lt_of_le_of_lt (Nat.le_trans hle1 hlen2.core_ok.wlen_le) (wpush_wcap_lt32 c)
  have hwv2 : 2 * lit.toNat + 1 < s2.core.wvec.length := by
    rw [hlen2.core_ok.wvec_len]; have := hlen2.core_ok.cur_vars_le; omega
  have hcnt_pos : 0 < cnt.toNat := by omega
  have hdisj_sent := wpush_sentinel_range_disjoint hlay2
    (dst := wOff s2.core.wvec lit.toNat + wSz s2.core.wvec lit.toNat) (len := cnt.toNat)
    (by omega) hcnt_pos (fun off hlo hhi => by
      have := hsent (off - (wOff s2.core.wvec lit.toNat + wSz s2.core.wvec lit.toNat)) (by omega)
      rwa [show wOff s2.core.wvec lit.toNat + wSz s2.core.wvec lit.toNat +
        (off - (wOff s2.core.wvec lit.toNat + wSz s2.core.wvec lit.toNat)) = off by omega] at this)
  have hdisj : ∀ j < 2 * s.core.cur_vars, j ≠ lit.toNat → 0 < wSz s2.core.wvec j →
      wOff s2.core.wvec j + wSz s2.core.wvec j ≤ wOff s2.core.wvec lit.toNat ∨
      wOff s2.core.wvec lit.toNat + (wSz s2.core.wvec lit.toNat + cnt.toNat) ≤
        wOff s2.core.wvec j := by
    intro j hj hne hpj
    by_cases hszp : 0 < wSz s2.core.wvec lit.toNat
    · rcases hlay2.disjoint j lit.toNat (hcv2 ▸ hj) hlit2 hne hpj hszp with h1 | h2
      · exact Or.inl h1
      · rcases hdisj_sent j (hcv2 ▸ hj) hpj with hs1 | hs2
        · exfalso
          change wOff s2.core.wvec lit.toNat + wSz s2.core.wvec lit.toNat ≤
            wOff s2.core.wvec j at h2
          change wOff s2.core.wvec j + wSz s2.core.wvec j ≤
            wOff s2.core.wvec lit.toNat + wSz s2.core.wvec lit.toNat at hs1
          change 0 < wSz s2.core.wvec j at hpj
          omega
        · exact Or.inr (by
            change wOff s2.core.wvec lit.toNat + wSz s2.core.wvec lit.toNat + cnt.toNat ≤
              wOff s2.core.wvec j at hs2
            omega)
    · have hsz0 : wSz s2.core.wvec lit.toNat = 0 := Nat.eq_zero_of_not_pos hszp
      rcases hdisj_sent j (hcv2 ▸ hj) hpj with hs1 | hs2
      · exact Or.inl (by
          change wOff s2.core.wvec j + wSz s2.core.wvec j ≤
            wOff s2.core.wvec lit.toNat + wSz s2.core.wvec lit.toNat at hs1
          omega)
      · exact Or.inr (by
          change wOff s2.core.wvec lit.toNat + wSz s2.core.wvec lit.toNat + cnt.toNat ≤
            wOff s2.core.wvec j at hs2
          omega)
  have hlen' := wpush_lengthsOk (wlen' := s2.core.wlen) (wusable' := wusable')
    hlen hwv'_len hws_len hlen2.core_ok.wlen_le hwso_len
  refine wpush_ok_post hQ hlay2 hpres hlit hc12 hw0 hw1 wusable' hlen' (Nat.le_refl _)
    hdst1 (by omega) ?_ ?_ ?_ hdisj ?_ ?_ hat0 hat1 hm'
  · intro j hj hne
    subst hwvec'_eq
    exact ⟨by simp only [wOff]; rw [List.getElem?_set_ne (by omega)],
      by simp only [wSz]; rw [List.getElem?_set_ne (by omega)]⟩
  · subst hwvec'_eq
    simp only [wOff]; rw [List.getElem?_set_ne (by omega)]
  · subst hwvec'_eq
    simp only [wSz]; rw [List.getElem?_set_self hwv2]
    simp; exact hsz32
  · intro j hj hne k hk
    by_cases hpj : 0 < wSz s2.core.wvec j
    · rcases hdisj j hj hne hpj with h1 | h2
      · exact hws_out _ (Or.inl (by omega))
      · exact hws_out _ (Or.inr (by omega))
    · exact absurd hk (by omega)
  · intro k hk; exact hws_out _ (Or.inl (by omega))

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

theorem wpush_reloc_step {s2 : FullState} {lit k : Nat} {wstk : List (BitVec 32)}
    (hlay2 : WatchStackLayout s2.core) (hwlen_le : s2.core.wlen ≤ s2.core.wstk.length)
    (hlit : lit < 2 * s2.core.cur_vars)
    (hk : k < wSz s2.core.wvec lit) (hinv : RelocCopyInv s2 lit k wstk)
    (hfit : s2.core.wlen + k < wstk.length) :
    let off := wOff s2.core.wvec lit
    let dst := s2.core.wlen
    let v := (wstk[off + k]?).getD 0#32
    let wstk' := (wstk.set (off + k) 0xFFFFFFFF#32).set (dst + k) v
    RelocCopyInv s2 lit (k + 1) wstk' := by
  intro off dst v wstk'
  obtain ⟨hlen, hoth, hcp, hrem, hclr⟩ := hinv
  have hb_lit : wOff s2.core.wvec lit + wSz s2.core.wvec lit ≤ s2.core.wlen :=
    hlay2.bounds lit hlit
  have hoff_lt : off + k < wstk.length := by change wOff s2.core.wvec lit + k < wstk.length; omega
  have hlen1 : (wstk.set (off + k) 0xFFFFFFFF#32).length = wstk.length := List.length_set
  have hne_idx : dst + k ≠ off + k := by change s2.core.wlen + k ≠ wOff s2.core.wvec lit + k; omega
  have hv_eq : some v = s2.core.wstk[off + k]? := by
    have hget := hrem k (Nat.le_refl k) hk
    change wstk[off + k]? = s2.core.wstk[off + k]? at hget
    have hlt_s2 : off + k < s2.core.wstk.length := hlen ▸ hoff_lt
    simp [v, hget, List.getElem?_eq_getElem hlt_s2]
  refine ⟨by simp [wstk', hlen], ?_, ?_, ?_, ?_⟩
  · intro j hj hne i hi
    have hb_j : wOff s2.core.wvec j + wSz s2.core.wvec j ≤ s2.core.wlen := hlay2.bounds j hj
    have hpj : 0 < wSz s2.core.wvec j := by omega
    have hpk : 0 < wSz s2.core.wvec lit := by omega
    have hd : wOff s2.core.wvec j + wSz s2.core.wvec j ≤ wOff s2.core.wvec lit ∨
        wOff s2.core.wvec lit + wSz s2.core.wvec lit ≤ wOff s2.core.wvec j :=
      hlay2.disjoint j lit hj hlit hne hpj hpk
    have hne1 : wOff s2.core.wvec j + i ≠ dst + k := by
      change wOff s2.core.wvec j + i ≠ s2.core.wlen + k; omega
    have hne2 : wOff s2.core.wvec j + i ≠ off + k := by
      change wOff s2.core.wvec j + i ≠ wOff s2.core.wvec lit + k
      rcases hd with h | h <;> omega
    simp only [wstk']
    rw [List.getElem?_set_ne (Ne.symm hne1), List.getElem?_set_ne (Ne.symm hne2)]
    exact hoth j hj hne i hi
  · intro i hi
    by_cases hik : i = k
    · subst hik; simp only [wstk']
      rw [List.getElem?_set_self (by rw [hlen1]; exact hfit), ← hv_eq]
    · have hne1 : dst + i ≠ dst + k := by omega
      have hne2 : dst + i ≠ off + k := by
        change s2.core.wlen + i ≠ wOff s2.core.wvec lit + k; omega
      simp only [wstk']
      rw [List.getElem?_set_ne (Ne.symm hne1), List.getElem?_set_ne (Ne.symm hne2)]
      exact hcp i (by omega)
  · intro i hlo hhi
    have hne1 : off + i ≠ dst + k := by
      change wOff s2.core.wvec lit + i ≠ s2.core.wlen + k; omega
    have hne2 : off + i ≠ off + k := by
      change wOff s2.core.wvec lit + i ≠ wOff s2.core.wvec lit + k; omega
    simp only [wstk']
    rw [List.getElem?_set_ne (Ne.symm hne1), List.getElem?_set_ne (Ne.symm hne2)]
    exact hrem i (by omega) hhi
  · intro i hi
    by_cases hik : i = k
    · subst hik; simp only [wstk']
      rw [List.getElem?_set_ne (Ne.symm (Ne.symm hne_idx)), List.getElem?_set_self hoff_lt]
    · have hne1 : off + i ≠ dst + k := by
        change wOff s2.core.wvec lit + i ≠ s2.core.wlen + k; omega
      have hne2 : off + i ≠ off + k := by
        change wOff s2.core.wvec lit + i ≠ wOff s2.core.wvec lit + k; omega
      simp only [wstk']
      rw [List.getElem?_set_ne (Ne.symm hne1), List.getElem?_set_ne (Ne.symm hne2)]
      exact hclr i (by omega)

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
  have hb_lit : wOff s2.core.wvec lit + wSz s2.core.wvec lit ≤ s2.core.wlen :=
    hlay2.bounds lit hlit
  have hstep := wpush_reloc_step hlay2 hwlen_le hlit hk hinv hfit
  dsimp only at hstep ⊢
  rw [List.set_comm]
  · exact hstep
  · omega

theorem wpush_reloc_fin {c : FullCfg} {s s2 : FullState} {R : Mem 64 → Prop}
    {lit w0 w1 cnt : BitVec 32} {Q : Post [Ty.bool]}
    (hQ : WPushPost c s R lit w0 w1 cnt Q)
    (hlen : s.LengthsOk c) (hlen2 : s2.LengthsOk c)
    (hlay2 : WatchStackLayout s2.core) (hpres : WatchPresAll s s2)
    (hlit : lit.toNat < 2 * s.core.cur_vars) (hc12 : cnt.toNat = 1 ∨ cnt.toNat = 2)
    (hw0 : cnt.toNat = 1 → w0 ≠ 0xFFFFFFFF#32)
    (hw1 : cnt.toNat = 2 → w0 ≠ 0xFFFFFFFF#32 ∧ w1 ≠ 0xFFFFFFFF#32)
    (hwlen1 : 1 ≤ s2.core.wlen)
    {ncap : Nat} (hsz_cnt : wSz s2.core.wvec lit.toNat + cnt.toNat ≤ ncap)
    (hfit : s2.core.wlen + ncap ≤ c.wcap)
    {wstk_cp wstk' wsort' : List (BitVec 32)} (wusable' : BitVec 64) {m' : Mem 64}
    (hinv : RelocCopyInv s2 lit.toNat (wSz s2.core.wvec lit.toNat) wstk_cp)
    (hws_len : wstk'.length = c.wcap) (hwso_len : wsort'.length = 2 * c.max_vars)
    (hws_lt : ∀ i < s2.core.wlen + wSz s2.core.wvec lit.toNat, wstk'[i]? = wstk_cp[i]?)
    (hat0 : wstk'[s2.core.wlen + wSz s2.core.wvec lit.toNat]? = some w0)
    (hat1 : cnt.toNat = 2 →
      wstk'[s2.core.wlen + wSz s2.core.wvec lit.toNat + 1]? = some w1)
    (wvec' : List (BitVec 32))
    (hwvec'_eq : wvec' = (s2.core.wvec.set (2 * lit.toNat) (BitVec.ofNat 32 s2.core.wlen)).set
      (2 * lit.toNat + 1) (BitVec.ofNat 32 (wSz s2.core.wvec lit.toNat + cnt.toNat)))
    (hm' :
      (FullMem c
        { s with
          core := { s.core with
            wvec := wvec', wstk := wstk', wlen := s2.core.wlen + ncap, wusable := wusable' }
          scratch := { s.scratch with wsort := wsort' } } ⋆ R) m') :
    Q (true, ()) m' := by
  have hcv2 := hpres.1
  have hlit2 : lit.toNat < 2 * s2.core.cur_vars := hcv2 ▸ hlit
  obtain ⟨_, hoth_cp, hcp_cp, _, hclr_cp⟩ := hinv
  have hwv1 : 2 * lit.toNat < s2.core.wvec.length := by
    rw [hlen2.core_ok.wvec_len]; have := hlen2.core_ok.cur_vars_le; omega
  have hwv2 : 2 * lit.toNat + 1 < s2.core.wvec.length := by
    rw [hlen2.core_ok.wvec_len]; have := hlen2.core_ok.cur_vars_le; omega
  have hwv'_len : wvec'.length = 4 * c.max_vars := by
    subst hwvec'_eq; simp [hlen2.core_ok.wvec_len]
  have hwlen32 : s2.core.wlen < 2 ^ 32 :=
    Nat.lt_of_le_of_lt hlen2.core_ok.wlen_le (wpush_wcap_lt32 c)
  have hsz32 : wSz s2.core.wvec lit.toNat + cnt.toNat < 2 ^ 32 := by
    have : wSz s2.core.wvec lit.toNat + cnt.toNat ≤ s2.core.wlen + ncap := by omega
    exact Nat.lt_of_le_of_lt (Nat.le_trans this hfit) (wpush_wcap_lt32 c)
  have hlen' := wpush_lengthsOk (wlen' := s2.core.wlen + ncap) (wusable' := wusable')
    hlen hwv'_len hws_len hfit hwso_len
  refine wpush_ok_post hQ hlay2 hpres hlit hc12 hw0 hw1 wusable' hlen' (Nat.le_add_right _ _)
    hwlen1 (by omega) ?_ ?_ ?_ ?_ ?_ ?_ hat0 hat1 hm'
  · intro j hj hne
    subst hwvec'_eq
    exact ⟨by
      simp only [wOff]; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)],
      by simp only [wSz]; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]⟩
  · subst hwvec'_eq
    simp only [wOff]
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_self hwv1]
    simp [wpush_bv32_eq_nat _ hwlen32 rfl]
  · subst hwvec'_eq
    simp only [wSz]
    rw [List.getElem?_set_self (by simp; exact hwv2)]
    simp; exact hsz32
  · intro j hj _ _; exact Or.inl (hlay2.bounds j (hcv2 ▸ hj))
  · intro j hj hne k hk
    have hb : wOff s2.core.wvec j + wSz s2.core.wvec j ≤ s2.core.wlen := hlay2.bounds j (hcv2 ▸ hj)
    have hlt_w : wOff s2.core.wvec j + k < s2.core.wlen := by omega
    have h1 := hws_lt _ (Nat.lt_of_lt_of_le hlt_w (Nat.le_add_right _ _))
    exact h1.trans (hoth_cp j (hcv2 ▸ hj) hne k hk)
  · intro k hk
    exact (hws_lt _ (Nat.add_lt_add_left hk _)).trans (hcp_cp k hk)

theorem wpush_reloc_fill_step {wstk : List (BitVec 32)} {base idx : Nat}
    (hidx : base ≤ idx) :
    ∀ {wstk0 : List (BitVec 32)},
      (∀ i < base, wstk[i]? = wstk0[i]?) →
      (∀ i < base, (wstk.set idx 0xFFFFFFFF#32)[i]? = wstk0[i]?) := by
  intro wstk0 h i hi
  rw [List.getElem?_set_ne (by omega)]
  exact h i hi

theorem wpush_zext64_eq_zero {x : BitVec 32} (h : x.setWidth 64 = 0#64) : x.toNat = 0 := by
  have hx := x.isLt
  have h0 := congrArg BitVec.toNat h
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat] at h0
  omega

theorem wpush_zext64_pos {x : BitVec 32} (h : x.setWidth 64 ≠ 0#64) : 0 < x.toNat :=
  Nat.pos_of_ne_zero fun h0 => h (by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, h0])

theorem wpush_list_zext64_eq_zero {xs : List (BitVec 32)} {i j : Nat}
    (hi : i < xs.length) (hj : j < xs.length) (heq : j = i)
    (h : (xs[j]'hj).setWidth 64 = 0#64) : (xs[i]?.getD 0#32).toNat = 0 := by
  subst heq
  rw [List.getElem?_eq_getElem hi]
  exact wpush_zext64_eq_zero h

theorem wpush_list_zext64_pos {xs : List (BitVec 32)} {i j : Nat}
    (hi : i < xs.length) (hj : j < xs.length) (heq : j = i)
    (h : (xs[j]'hj).setWidth 64 ≠ 0#64) : 0 < (xs[i]?.getD 0#32).toNat := by
  subst heq
  rw [List.getElem?_eq_getElem hi]
  exact wpush_zext64_pos h

theorem wpush_bv64_add_ofNat (a b : Nat) (h : a + b < 2 ^ 64) :
    (BitVec.ofNat 64 a + BitVec.ofNat 64 b).toNat = a + b := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : a < 2 ^ 64), Nat.mod_eq_of_lt (by omega : b < 2 ^ 64)]
  exact Nat.mod_eq_of_lt h

theorem wpush_bv64_add_setWidth (a : Nat) (b : BitVec 32) (h : a + b.toNat < 2 ^ 64) :
    (BitVec.ofNat 64 a + BitVec.setWidth 64 b).toNat = a + b.toNat := by
  have hb : b.toNat < 2 ^ 64 := Nat.lt_trans b.isLt (by decide)
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (by omega : a < 2 ^ 64), Nat.mod_eq_of_lt hb]
  exact Nat.mod_eq_of_lt h

theorem wpush_bv32_ofNat_64 (a : Nat) :
    (BitVec.ofNat 64 a).setWidth 32 = BitVec.ofNat 32 a := by
  apply BitVec.eq_of_toNat_eq; simp

theorem wpush_bv_off_sz_add {wvec : List (BitVec 32)} {lit : BitVec 32}
    (h0 : 2 * lit.toNat < wvec.length) (h1 : 2 * lit.toNat + 1 < wvec.length)
    (hl : 2 * lit.toNat + 1 < 2 ^ 64) :
    (BitVec.setWidth 64 (wvec[2 * lit.toNat]'h0) +
      BitVec.setWidth 64 (wvec[2 * lit.toNat + 1]'h1)).toNat =
      wOff wvec lit.toNat + wSz wvec lit.toNat := by
  have _ := hl
  have hlt0 : (wvec[2 * lit.toNat]'h0).toNat < 2 ^ 32 := BitVec.isLt _
  have hlt1 : (wvec[2 * lit.toNat + 1]'h1).toNat < 2 ^ 32 := BitVec.isLt _
  simp only [wOff, wSz, List.getElem?_eq_getElem h0, List.getElem?_eq_getElem h1,
    Option.getD_some, BitVec.toNat_add, BitVec.toNat_setWidth]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

theorem wpush_bv_fit_sub {a cap : Nat} {cnt : BitVec 32}
    (hle : a ≤ cap) (hcap : cap < 2 ^ 64)
    (h : (BitVec.setWidth 64 cnt).ule (BitVec.ofNat 64 cap - BitVec.ofNat 64 a) = true) :
    a + cnt.toNat ≤ cap := by
  have hcnt : cnt.toNat < 2 ^ 64 := Nat.lt_trans cnt.isLt (by decide)
  have h1 : cnt.toNat ≤ (BitVec.ofNat 64 cap - BitVec.ofNat 64 a).toNat := by
    simpa [BitVec.ule, BitVec.toNat_setWidth, Nat.mod_eq_of_lt hcnt] using h
  have hsub : (BitVec.ofNat 64 cap - BitVec.ofNat 64 a).toNat = cap - a := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hcap, Nat.mod_eq_of_lt (by omega : a < 2 ^ 64)]
    omega
  omega

theorem wpush_bv_sz_add_cnt {wvec : List (BitVec 32)} {lit cnt : BitVec 32}
    (h1 : 2 * lit.toNat + 1 < wvec.length) (hcnt : cnt.toNat ≤ 2)
    (hsz : wSz wvec lit.toNat + cnt.toNat < 2 ^ 32) :
    (BitVec.setWidth 64 (wvec[2 * lit.toNat + 1]'h1) + BitVec.setWidth 64 cnt).setWidth 32 =
      BitVec.ofNat 32 (wSz wvec lit.toNat + cnt.toNat) := by
  have hlt1 : (wvec[2 * lit.toNat + 1]'h1).toNat + cnt.toNat < 2 ^ 32 := by
    simpa [wSz, List.getElem?_eq_getElem h1] using hsz
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, wSz,
    List.getElem?_eq_getElem h1, Option.getD_some, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

theorem wpush_bv64_add3_eq {wvec : List (BitVec 32)} {lit cnt : BitVec 32} {sum : Nat}
    (h0 : 2 * lit.toNat < wvec.length) (h1 : 2 * lit.toNat + 1 < wvec.length)
    (hl : 2 * lit.toNat + 1 < 2 ^ 64) (hoff : wOff wvec lit.toNat + wSz wvec lit.toNat = sum)
    (hsum : sum + cnt.toNat < 2 ^ 64) :
    (BitVec.setWidth 64 (wvec[2 * lit.toNat]'h0) +
      BitVec.setWidth 64 (wvec[2 * lit.toNat + 1]'h1) + BitVec.setWidth 64 cnt).toNat =
      sum + cnt.toNat := by
  have hcnt : cnt.toNat < 2 ^ 64 := Nat.lt_trans cnt.isLt (by decide)
  rw [BitVec.toNat_add, wpush_bv_off_sz_add h0 h1 hl, hoff, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt hcnt]
  exact Nat.mod_eq_of_lt hsum

theorem wpush_state_upd {s s2 : FullState}
    {wv2 ws2 wso2 wvec' wstk' : List (BitVec 32)} {wl2 wlen' : Nat} {wu2 wu' : BitVec 64}
    (hs2 : s2 = { s with
      core := { s.core with wvec := wv2, wstk := ws2, wlen := wl2, wusable := wu2 }
      scratch := { s.scratch with wsort := wso2 } }) :
    ({ s2 with
      core := { s2.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' } } :
        FullState) =
      { core := { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' }
        scratch := { s.scratch with wsort := wso2 } } := by
  subst hs2; rfl

theorem wpush_caseB_s3 {c : FullCfg} {s s2 : FullState} {R : Mem 64 → Prop}
    {lit w0 w1 cnt : BitVec 32} {Q : Post [Ty.bool]}
    {wv2 ws2 wso2 wstk' : List (BitVec 32)} {wl2 : Nat} {wu2 : BitVec 64} {m' : Mem 64}
    (hQ : WPushPost c s R lit w0 w1 cnt Q)
    (hlen : s.LengthsOk c) (hlen2 : s2.LengthsOk c)
    (hlay2 : WatchStackLayout s2.core) (hpres2 : WatchPresAll s s2)
    (hs2 : s2 = { s with
      core := { s.core with wvec := wv2, wstk := ws2, wlen := wl2, wusable := wu2 }
      scratch := { s.scratch with wsort := wso2 } })
    (hlit : lit.toNat < 2 * s.core.cur_vars) (hc12 : cnt.toNat = 1 ∨ cnt.toNat = 2)
    (hw0 : cnt.toNat = 1 → w0 ≠ 0xFFFFFFFF#32)
    (hw1 : cnt.toNat = 2 → w0 ≠ 0xFFFFFFFF#32 ∧ w1 ≠ 0xFFFFFFFF#32)
    (hoff1 : 1 ≤ wOff s2.core.wvec lit.toNat)
    (heq : wOff s2.core.wvec lit.toNat + wSz s2.core.wvec lit.toNat = s2.core.wlen)
    (hfit : s2.core.wlen + cnt.toNat ≤ c.wcap)
    (hwlen : wstk'.length = c.wcap)
    (hpres_stk : ∀ i, i < s2.core.wlen → wstk'[i]? = s2.core.wstk[i]?)
    (hat0 : wstk'[s2.core.wlen]? = some w0)
    (hat1 : cnt.toNat = 2 → wstk'[s2.core.wlen + 1]? = some w1)
    (hm' : (FullMem c { s2 with
      core := { s2.core with
        wvec := s2.core.wvec.set (2 * lit.toNat + 1)
          (BitVec.ofNat 32 (wSz s2.core.wvec lit.toNat + cnt.toNat))
        wstk := wstk', wlen := s2.core.wlen + cnt.toNat } } ⋆ R) m') :
    Q (true, ()) m' := by
  dsimp only at hm'
  have hm'' : (FullMem c { s2 with
      core := { s2.core with
        wvec := s2.core.wvec.set (2 * lit.toNat + 1)
          (BitVec.ofNat 32 (wSz s2.core.wvec lit.toNat + cnt.toNat))
        wstk := wstk', wlen := s2.core.wlen + cnt.toNat, wusable := s2.core.wusable } } ⋆ R) m' :=
    hm'
  rw [wpush_state_upd hs2] at hm''
  exact wpush_caseB_fin hQ hlen hlen2 hlay2 hpres2 hlit hc12 hw0 hw1 hoff1 heq hfit
    s2.core.wusable (wsort' := wso2) hwlen (hs2 ▸ hlen2).scratch_ok.wsort_len
    hpres_stk hat0 hat1 _ rfl hm''

theorem wpush_caseC_s3 {c : FullCfg} {s s2 : FullState} {R : Mem 64 → Prop}
    {lit w0 w1 cnt : BitVec 32} {Q : Post [Ty.bool]}
    {wv2 ws2 wso2 wstk' : List (BitVec 32)} {wl2 : Nat} {wu2 wu' : BitVec 64} {m' : Mem 64}
    (hQ : WPushPost c s R lit w0 w1 cnt Q)
    (hlen : s.LengthsOk c) (hlen2 : s2.LengthsOk c)
    (hlay2 : WatchStackLayout s2.core) (hpres2 : WatchPresAll s s2)
    (hs2 : s2 = { s with
      core := { s.core with wvec := wv2, wstk := ws2, wlen := wl2, wusable := wu2 }
      scratch := { s.scratch with wsort := wso2 } })
    (hlit : lit.toNat < 2 * s.core.cur_vars) (hc12 : cnt.toNat = 1 ∨ cnt.toNat = 2)
    (hw0 : cnt.toNat = 1 → w0 ≠ 0xFFFFFFFF#32)
    (hw1 : cnt.toNat = 2 → w0 ≠ 0xFFFFFFFF#32 ∧ w1 ≠ 0xFFFFFFFF#32)
    (hoff1 : 1 ≤ wOff s2.core.wvec lit.toNat)
    (hle : wOff s2.core.wvec lit.toNat + wSz s2.core.wvec lit.toNat + cnt.toNat ≤ s2.core.wlen)
    (hsent : ∀ k < cnt.toNat,
      s2.core.wstk[wOff s2.core.wvec lit.toNat + wSz s2.core.wvec lit.toNat + k]? =
        some 0xFFFFFFFF#32)
    (hwlen : wstk'.length = c.wcap)
    (hpres_stk : ∀ i,
      i < wOff s2.core.wvec lit.toNat + wSz s2.core.wvec lit.toNat ∨
        wOff s2.core.wvec lit.toNat + wSz s2.core.wvec lit.toNat + cnt.toNat ≤ i →
      wstk'[i]? = s2.core.wstk[i]?)
    (hat0 : wstk'[wOff s2.core.wvec lit.toNat + wSz s2.core.wvec lit.toNat]? = some w0)
    (hat1 : cnt.toNat = 2 →
      wstk'[wOff s2.core.wvec lit.toNat + wSz s2.core.wvec lit.toNat + 1]? = some w1)
    (hm' : (FullMem c { s2 with
      core := { s2.core with
        wvec := s2.core.wvec.set (2 * lit.toNat + 1)
          (BitVec.ofNat 32 (wSz s2.core.wvec lit.toNat + cnt.toNat))
        wstk := wstk', wusable := wu' } } ⋆ R) m') :
    Q (true, ()) m' := by
  dsimp only at hm'
  have hm'' : (FullMem c { s2 with
      core := { s2.core with
        wvec := s2.core.wvec.set (2 * lit.toNat + 1)
          (BitVec.ofNat 32 (wSz s2.core.wvec lit.toNat + cnt.toNat))
        wstk := wstk', wlen := s2.core.wlen, wusable := wu' } } ⋆ R) m' :=
    hm'
  rw [wpush_state_upd (wlen' := s2.core.wlen) hs2] at hm''
  exact wpush_caseC_fin hQ hlen hlen2 hlay2 hpres2 hlit hc12 hw0 hw1 hoff1 hle hsent
    wu' (wsort' := wso2) hwlen (hs2 ▸ hlen2).scratch_ok.wsort_len
    hpres_stk hat0 hat1 _ rfl hm''

theorem wpush_reloc_s3 {c : FullCfg} {s s2 : FullState} {R : Mem 64 → Prop}
    {lit w0 w1 cnt : BitVec 32} {Q : Post [Ty.bool]}
    {wv2 ws2 wso2 wstk_cp wstk' : List (BitVec 32)} {wl2 ncap : Nat}
    {wu2 wu' : BitVec 64} {m' : Mem 64}
    (hQ : WPushPost c s R lit w0 w1 cnt Q)
    (hlen : s.LengthsOk c) (hlen2 : s2.LengthsOk c)
    (hlay2 : WatchStackLayout s2.core) (hpres2 : WatchPresAll s s2)
    (hs2 : s2 = { s with
      core := { s.core with wvec := wv2, wstk := ws2, wlen := wl2, wusable := wu2 }
      scratch := { s.scratch with wsort := wso2 } })
    (hlit : lit.toNat < 2 * s.core.cur_vars) (hc12 : cnt.toNat = 1 ∨ cnt.toNat = 2)
    (hw0 : cnt.toNat = 1 → w0 ≠ 0xFFFFFFFF#32)
    (hw1 : cnt.toNat = 2 → w0 ≠ 0xFFFFFFFF#32 ∧ w1 ≠ 0xFFFFFFFF#32)
    (hw1_2 : 1 ≤ s2.core.wlen)
    (hncap : wSz s2.core.wvec lit.toNat + cnt.toNat ≤ ncap)
    (hfit : s2.core.wlen + ncap ≤ c.wcap)
    (hcp : RelocCopyInv s2 lit.toNat (wSz s2.core.wvec lit.toNat) wstk_cp)
    (hwlen : wstk'.length = c.wcap)
    (hpres_stk : ∀ i < s2.core.wlen + wSz s2.core.wvec lit.toNat, wstk'[i]? = wstk_cp[i]?)
    (hat0 : wstk'[s2.core.wlen + wSz s2.core.wvec lit.toNat]? = some w0)
    (hat1 : cnt.toNat = 2 →
      wstk'[s2.core.wlen + wSz s2.core.wvec lit.toNat + 1]? = some w1)
    (hm' : (FullMem c { s2 with
      core := { s2.core with
        wvec := (s2.core.wvec.set (2 * lit.toNat) (BitVec.ofNat 32 s2.core.wlen)).set
          (2 * lit.toNat + 1) (BitVec.ofNat 32 (wSz s2.core.wvec lit.toNat + cnt.toNat))
        wstk := wstk', wlen := s2.core.wlen + ncap, wusable := wu' } } ⋆ R) m') :
    Q (true, ()) m' := by
  dsimp only at hm'
  rw [wpush_state_upd hs2] at hm'
  exact wpush_reloc_fin hQ hlen hlen2 hlay2 hpres2 hlit hc12 hw0 hw1 hw1_2 hncap hfit
    wu' (wsort' := wso2) hcp hwlen (hs2 ▸ hlen2).scratch_ok.wsort_len
    hpres_stk hat0 hat1 _ rfl hm'

theorem wpush_wstk_set2_ok {wstk : List (BitVec 32)} {wcap p : Nat} {w0 w1 cnt : BitVec 32}
    (hlen : wstk.length = wcap) (hp1 : p + 1 < wcap) (hc2 : cnt.toNat = 2) :
    let wstk' := (wstk.set p w0).set (p + 1) w1
    wstk'.length = wcap ∧
      (∀ i, i < p ∨ p + cnt.toNat ≤ i → wstk'[i]? = wstk[i]?) ∧
      wstk'[p]? = some w0 ∧
      (cnt.toNat = 2 → wstk'[p + 1]? = some w1) := by
  refine ⟨by simp [hlen], fun i hi => ?_, ?_, fun _ => ?_⟩
  · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
  · rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega)]
  · rw [List.getElem?_set_self (by rw [List.length_set, hlen]; exact hp1)]

theorem wpush_wstk_set1_ok {wstk : List (BitVec 32)} {wcap p : Nat} {w0 w1 cnt : BitVec 32}
    (hlen : wstk.length = wcap) (hp : p < wcap) (hcnt : 1 ≤ cnt.toNat) (hc1 : cnt.toNat ≠ 2) :
    let wstk' := wstk.set p w0
    wstk'.length = wcap ∧
      (∀ i, i < p ∨ p + cnt.toNat ≤ i → wstk'[i]? = wstk[i]?) ∧
      wstk'[p]? = some w0 ∧
      (cnt.toNat = 2 → wstk'[p + 1]? = some w1) := by
  refine ⟨by simp [hlen], fun i hi => ?_, ?_, fun h => absurd h hc1⟩
  · have _ := hcnt
    rcases hi with hi1 | hi2 <;> rw [List.getElem?_set_ne (by omega)]
  · rw [List.getElem?_set_self (by omega)]

end

end LeanQbe.T.Examples.Kissat.Proof.Watch
