/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.PropSearch.BcpWatchHelpers
import LeanQbe.T.Logic.C0Step
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat BCP Split-Watch & Delayed-Flush Layout Helpers (`Proof.PropSearch.BcpFlushHelpers`)

Canonical non-legacy helper layer for `SplitWatchesInv`, `DelayedWatchesOk`, and watch-stack
append/flush layout lemmas (`0` legacy imports, `0` `@[expose]` on theorems/lemmas):
1. `SplitWatchesInv.*` compaction, write, push, and framing lemmas.
2. `DelayedWatchesOk` congruence & push lemmas.
3. Delayed-watch flush layout lemmas (`fidFlushDisk`, `fid_repl_empty_layout`,
   `m7_repl_empty_layout`, `s15_append_{end,sentinel}_layout`, `s15_flush_step_*`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.PropSearch

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.PropSearch.Spec

/-! ## 1. `SplitWatchesInv` Compaction, Write & Push Lemmas -/

theorem SplitWatchesInv.end_lt_wcap {c : FullCfg} {F_cur : List (List Nat)}
    {k : FullCoreState} {not_lit off q p end_v : Nat}
    (hlen : k.LengthsOk c) (h : SplitWatchesInv F_cur k not_lit off q p end_v)
    (hn : not_lit < 2 * k.cur_vars) :
    end_v ≤ k.wlen ∧ k.wlen ≤ c.wcap := by
  have hb := h.layout.bounds not_lit hn
  rw [h.off_eq, h.sz_eq] at hb; exact ⟨by omega, hlen.wlen_le⟩

theorem SplitWatchesInv.rem_ne_sentinel {F_cur : List (List Nat)} {k : FullCoreState}
    {not_lit off q p end_v : Nat} (h : SplitWatchesInv F_cur k not_lit off q p end_v)
    (hp : p < end_v) : k.wstk[p]? ≠ some 0xFFFFFFFF#32 := by
  simpa using h.rem_slice.ne_sentinel 0 (by omega)

theorem SplitWatchesInv.advance_rem {F_cur : List (List Nat)} {k : FullCoreState}
    {not_lit off q p p' end_v : Nat} (h : SplitWatchesInv F_cur k not_lit off q p end_v)
    (hp : p ≤ p') (hp' : p' ≤ end_v)
    (hrem : WatchSliceOk F_cur k not_lit p' (end_v - p')) :
    SplitWatchesInv F_cur k not_lit off q p' end_v :=
  ⟨h.layout, h.off_eq, h.sz_eq, h.sz_pos, h.q_ge, Nat.le_trans h.q_le_p hp, hp',
    h.other_slices, h.kept_slice, hrem⟩

theorem SplitWatchesInv.write_bin {c : FullCfg} {F_cur : List (List Nat)}
    {k : FullCoreState} {not_lit off q p end_v : Nat} {w0 : BitVec 32}
    (h : SplitWatchesInv F_cur k not_lit off q p end_v)
    (hcv : k.cur_vars ≤ c.max_vars) (hnot : not_lit < 2 * k.cur_vars)
    (hq_le : q + 1 ≤ p) (hq_lt : q < k.wstk.length)
    (hflag : (w0 &&& 0x80000000#32) ≠ 0#32)
    (hlt : (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k.cur_vars)
    (hent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause [not_lit, (w0 &&& 0x7FFFFFFF#32).toNat])) :
    SplitWatchesInv F_cur { k with wstk := k.wstk.set q w0 } not_lit off (q + 1) p end_v := by
  have hb := h.layout.bounds not_lit hnot; rw [h.off_eq, h.sz_eq] at hb
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  have hq_ge := h.q_ge; have hp_le := h.p_le_end
  have hne : w0 ≠ 0xFFFFFFFF#32 := binWatchWord_ne_sentinel (by omega)
  let k' : FullCoreState := { k with wstk := k.wstk.set q w0 }
  have hdisj : ∀ l < 2 * k.cur_vars, l ≠ not_lit → ∀ idx < fullWatchSizeCore k l,
      fullWatchOffCore k l + idx ≠ q := fun l hl hne_l idx hidx => by
    have hpos : 0 < fullWatchSizeCore k l := by omega
    rcases h.layout.disjoint l not_lit hl hnot hne_l hpos (by rw [h.sz_eq]; exact h.sz_pos) with
      h1 | h2
    · rw [h.off_eq] at h1; omega
    · rw [h.off_eq, h.sz_eq] at h2; omega
  have hother' : ∀ l < 2 * k'.cur_vars, l ≠ not_lit →
      WatchSliceOk F_cur k' l (fullWatchOffCore k' l) (fullWatchSizeCore k' l) := fun l hl hne_l =>
    WatchSliceOk.mono (k := k) (by rw [CNF.entails_def]; exact fun _ p => p) (Nat.le_refl _)
      (fun _ hr => hr) (fun idx hlo hhi => by
        change fullWatchOffCore k l ≤ idx at hlo
        change idx < fullWatchOffCore k l + fullWatchSizeCore k l at hhi
        have hd := hdisj l hl hne_l (idx - fullWatchOffCore k l) (by omega)
        rw [show fullWatchOffCore k l + (idx - fullWatchOffCore k l) = idx by omega] at hd
        exact List.getElem?_set_ne (Ne.symm hd))
      (h.other_slices l hl hne_l)
  have hkept' : WatchSliceOk F_cur k' not_lit off (q + 1 - off) := by
    rw [show q + 1 - off = (q - off) + 1 by omega]
    exact watchSlice_append_bin (k := k) (p := off) (Nat.le_refl _) (fun _ hr => hr)
      (fun idx hi => List.getElem?_set_ne (by omega))
      h.kept_slice
      (by have : off + (q - off) = q := by omega
          rw [this]; exact List.getElem?_set_self hq_lt)
      hflag hne hlt hent
  have hrem' : WatchSliceOk F_cur k' not_lit p (end_v - p) :=
    WatchSliceOk.mono (k := k) (by rw [CNF.entails_def]; exact fun _ p => p) (Nat.le_refl _)
      (fun _ hr => hr) (fun idx hlo _ => List.getElem?_set_ne (by omega)) h.rem_slice
  have hns' : ∀ l < 2 * k'.cur_vars, ∀ idx < fullWatchSizeCore k' l,
      k'.wstk[fullWatchOffCore k' l + idx]? ≠ some 0xFFFFFFFF#32 := by
    intro l hl idx hidx; by_cases hl_eq : l = not_lit
    · subst hl_eq
      change (k.wstk.set q w0)[fullWatchOffCore k l + idx]? ≠ some 0xFFFFFFFF#32
      rw [h.off_eq]; by_cases hij : off + idx = q
      · rw [hij, List.getElem?_set_self hq_lt]; exact fun heq => hne (Option.some.inj heq)
      · rw [List.getElem?_set_ne (Ne.symm hij), ← h.off_eq]
        exact h.layout.no_sentinel l hl idx hidx
    · exact (hother' l hl hl_eq).ne_sentinel idx hidx
  exact ⟨⟨fun l hl => h.layout.bounds l hl, fun l hl hp => h.layout.pos_off l hl hp,
    fun l1 l2 h1 h2 hne' hp1 hp2 => h.layout.disjoint l1 l2 h1 h2 hne' hp1 hp2, hns'⟩,
    h.off_eq, h.sz_eq, h.sz_pos, by omega, hq_le, hp_le, hother', hkept', hrem'⟩

theorem SplitWatchesInv.write_large {F_cur : List (List Nat)} {k : FullCoreState}
    {not_lit off q p end_v : Nat} {w0 cref : BitVec 32}
    (h : SplitWatchesInv F_cur k not_lit off q p end_v)
    (hnot : not_lit < 2 * k.cur_vars) (hq_le : q + 2 ≤ p) (hq_lt : q + 1 < k.wstk.length)
    (hflag : (w0 &&& 0x80000000#32) = 0#32) (hlt : cref.toNat < 0x80000000)
    (href : cref.toNat ∈ fullArenaClauseRefsCore k) :
    SplitWatchesInv F_cur { k with wstk := (k.wstk.set q w0).set (q + 1) cref }
      not_lit off (q + 2) p end_v := by
  have hb := h.layout.bounds not_lit hnot; rw [h.off_eq, h.sz_eq] at hb
  have hq_ge := h.q_ge; have hp_le := h.p_le_end
  let k' : FullCoreState := { k with wstk := (k.wstk.set q w0).set (q + 1) cref }
  have hdisj : ∀ l < 2 * k.cur_vars, l ≠ not_lit → ∀ idx < fullWatchSizeCore k l,
      fullWatchOffCore k l + idx ≠ q ∧ fullWatchOffCore k l + idx ≠ q + 1 :=
    fun l hl hne idx hidx => by
    have hpos : 0 < fullWatchSizeCore k l := by omega
    rcases h.layout.disjoint l not_lit hl hnot hne hpos (by rw [h.sz_eq]; exact h.sz_pos) with
      h1 | h2
    · rw [h.off_eq] at h1; omega
    · rw [h.off_eq, h.sz_eq] at h2; omega
  have hother' : ∀ l < 2 * k'.cur_vars, l ≠ not_lit →
      WatchSliceOk F_cur k' l (fullWatchOffCore k' l) (fullWatchSizeCore k' l) := fun l hl hne =>
    WatchSliceOk.mono (k := k) (by rw [CNF.entails_def]; exact fun _ p => p) (Nat.le_refl _)
      (fun _ hr => hr) (fun idx hlo hhi => by
        change fullWatchOffCore k l ≤ idx at hlo
        change idx < fullWatchOffCore k l + fullWatchSizeCore k l at hhi
        obtain ⟨hn0, hn1⟩ := hdisj l hl hne (idx - fullWatchOffCore k l) (by omega)
        rw [show fullWatchOffCore k l + (idx - fullWatchOffCore k l) = idx by omega] at hn0 hn1
        change k'.wstk[idx]? = k.wstk[idx]?
        rw [List.getElem?_set_ne (Ne.symm hn1), List.getElem?_set_ne (Ne.symm hn0)])
      (h.other_slices l hl hne)
  have hkept' : WatchSliceOk F_cur k' not_lit off (q + 2 - off) := by
    rw [show q + 2 - off = (q - off) + 2 by omega]
    exact watchSlice_append_large (k := k) (p := off) (Nat.le_refl _) (fun _ hr => hr)
      (fun idx hi => by
        rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)])
      h.kept_slice
      (by have h0 : off + (q - off) = q := by omega
          rw [h0, List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega)])
      (by have h1 : off + (q - off) + 1 = q + 1 := by omega
          rw [h1, List.getElem?_set_self (by rw [List.length_set]; exact hq_lt)])
      hflag hlt href
  have hrem' : WatchSliceOk F_cur k' not_lit p (end_v - p) :=
    WatchSliceOk.mono (k := k) (by rw [CNF.entails_def]; exact fun _ p => p) (Nat.le_refl _)
      (fun _ hr => hr) (fun idx hlo _ => by
        rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)])
      h.rem_slice
  have hw0_ne : w0 ≠ 0xFFFFFFFF#32 := fun heq => by subst heq; revert hflag; decide
  have hcr_ne : cref ≠ 0xFFFFFFFF#32 := fun heq => by subst heq; revert hlt; decide
  have hns' : ∀ l < 2 * k'.cur_vars, ∀ idx < fullWatchSizeCore k' l,
      k'.wstk[fullWatchOffCore k' l + idx]? ≠ some 0xFFFFFFFF#32 := by
    intro l hl idx hidx; by_cases hl_eq : l = not_lit
    · subst hl_eq
      change ((k.wstk.set q w0).set (q + 1) cref)[fullWatchOffCore k l + idx]? ≠
        some 0xFFFFFFFF#32
      rw [h.off_eq]; by_cases hij1 : off + idx = q + 1
      · rw [hij1, List.getElem?_set_self (by rw [List.length_set]; exact hq_lt)]
        exact fun heq => hcr_ne (Option.some.inj heq)
      · rw [List.getElem?_set_ne (Ne.symm hij1)]; by_cases hij0 : off + idx = q
        · rw [hij0, List.getElem?_set_self (by omega)]
          exact fun heq => hw0_ne (Option.some.inj heq)
        · rw [List.getElem?_set_ne (Ne.symm hij0), ← h.off_eq]
          exact h.layout.no_sentinel l hl idx hidx
    · exact (hother' l hl hl_eq).ne_sentinel idx hidx
  exact ⟨⟨fun l hl => h.layout.bounds l hl, fun l hl hp => h.layout.pos_off l hl hp,
    fun l1 l2 h1 h2 hne' hp1 hp2 => h.layout.disjoint l1 l2 h1 h2 hne' hp1 hp2, hns'⟩,
    h.off_eq, h.sz_eq, h.sz_pos, by omega, hq_le, hp_le, hother', hkept', hrem'⟩

theorem SplitWatchesInv.push_nonskip {F_cur : List (List Nat)} {k k' : FullCoreState}
    {not_lit off q p end_v lit w0 cref : Nat} (hcv : k'.cur_vars = k.cur_vars)
    (hareq : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k')
    (hlit : lit < 2 * k.cur_vars) (hlit_ne : lit ≠ not_lit)
    (h : SplitWatchesInv F_cur k not_lit off q p end_v) (hnot : not_lit < 2 * k.cur_vars)
    (hlay' : WatchStackLayout k')
    (hother : ∀ l < 2 * k.cur_vars, l ≠ lit →
      fullWatchSizeCore k' l = fullWatchSizeCore k l ∧
      ∀ idx < fullWatchSizeCore k l,
        k'.wstk[fullWatchOffCore k' l + idx]? = k.wstk[fullWatchOffCore k l + idx]?)
    (hlit_ok : fullWatchSizeCore k' lit = fullWatchSizeCore k lit + 2 ∧
      (∀ idx < fullWatchSizeCore k lit,
        k'.wstk[fullWatchOffCore k' lit + idx]? = k.wstk[fullWatchOffCore k lit + idx]?) ∧
      k'.wstk[fullWatchOffCore k' lit + fullWatchSizeCore k lit]? = some (BitVec.ofNat 32 w0) ∧
      k'.wstk[fullWatchOffCore k' lit + fullWatchSizeCore k lit + 1]? = some (BitVec.ofNat 32 cref))
    (hw0_flag : (BitVec.ofNat 32 w0 &&& 0x80000000#32) = 0#32)
    (hcr_lt : cref < 0x80000000) (hcr_ref : cref ∈ fullArenaClauseRefsCore k') :
    let off' := fullWatchOffCore k' not_lit
    SplitWatchesInv F_cur k' not_lit off' (off' + (q - off)) (off' + (p - off))
      (off' + (end_v - off)) := by
  intro off'
  have ⟨hsz_not, hnot_copy⟩ := hother not_lit hnot hlit_ne.symm
  have hcr_32 : cref < 2 ^ 32 := Nat.lt_trans hcr_lt (by decide)
  have hq_ge := h.q_ge; have hq_le := h.q_le_p; have hp_le := h.p_le_end
  have hnot_copy' : ∀ idx < end_v - off, k'.wstk[off' + idx]? = k.wstk[off + idx]? :=
    fun idx hi => by
    have := hnot_copy idx (by rw [h.sz_eq]; exact hi); rwa [h.off_eq] at this
  refine ⟨hlay', rfl, ?_, by simpa [Nat.add_sub_cancel_left] using h.sz_pos, by omega, by omega,
    by omega, ?_, ?_, ?_⟩
  · rw [hsz_not, h.sz_eq]; omega
  · intro l hl' hne_l; have hl : l < 2 * k.cur_vars := hcv ▸ hl'
    by_cases hll : l = lit
    · subst hll
      have ho_lit := h.other_slices l hl hlit_ne
      rw [hlit_ok.1]
      refine watchSlice_append_large (hcv ▸ Nat.le_refl _) hareq hlit_ok.2.1 ho_lit
        hlit_ok.2.2.1 hlit_ok.2.2.2 hw0_flag (by rwa [bv32_ofNat_toNat_lt hcr_32])
        (by rwa [bv32_ofNat_toNat_lt hcr_32])
    · have ⟨hsz_l, hcp_l⟩ := hother l hl hll
      rw [hsz_l]
      exact watchSlice_relocate (by rw [CNF.entails_def]; exact fun _ p => p)
        (hcv ▸ Nat.le_refl _) hareq (fun idx hidx => hcp_l idx hidx) (h.other_slices l hl hne_l)
  · rw [Nat.add_sub_cancel_left]
    exact watchSlice_relocate (by rw [CNF.entails_def]; exact fun _ p => p)
      (hcv ▸ Nat.le_refl _) hareq (fun idx hi => hnot_copy' idx (by omega)) h.kept_slice
  · rw [show off' + (end_v - off) - (off' + (p - off)) = end_v - p by omega]
    exact watchSlice_relocate (by rw [CNF.entails_def]; exact fun _ p => p)
      (hcv ▸ Nat.le_refl _) hareq
      (fun idx hi => by
        simpa [Nat.add_assoc, show p - off + idx = idx + (p - off) by omega,
          show p + idx = off + (idx + (p - off)) by omega] using
          hnot_copy' (idx + (p - off)) (by omega))
      h.rem_slice

theorem SplitWatchesInv.of_init {F_cur : List (List Nat)} {k : FullCoreState}
    {not_lit : Nat} (hw : WatchesInv F_cur k) (hnot : not_lit < 2 * k.cur_vars)
    (hpos : 0 < fullWatchSizeCore k not_lit) :
    let off := fullWatchOffCore k not_lit
    let end_v := off + fullWatchSizeCore k not_lit
    SplitWatchesInv F_cur k not_lit off off off end_v :=
  ⟨hw.layout, rfl, by simp, by simpa using hpos, le_refl _, le_refl _, by omega,
   fun l hl _ => hw.slices l hl, by simp; exact .empty, by simp; exact hw.slices not_lit hnot⟩

theorem SplitWatchesInv.finish_compact {c : FullCfg} {F_cur : List (List Nat)}
    {k : FullCoreState} {not_lit off q end_v : Nat}
    (h : SplitWatchesInv F_cur k not_lit off q end_v end_v) (hc : c.wcap < 2 ^ 32)
    (hlen : k.LengthsOk c) (hnot : not_lit < 2 * k.cur_vars) :
    WatchesInv F_cur
      { k with wvec := k.wvec.set (2 * not_lit + 1) (BitVec.ofNat 32 (q - off)) } := by
  have hb := h.layout.bounds not_lit hnot
  have hwlen := hlen.wlen_le
  have hcv := hlen.cur_vars_le
  have hq_le := h.q_le_p; have hq_ge := h.q_ge; have hsz := h.sz_eq
  rw [h.off_eq, hsz] at hb
  have hq32 : q - off < 2 ^ 32 := by omega
  have hwlen_vec : k.wvec.length = 4 * c.max_vars := hlen.wvec_len
  let k' : FullCoreState :=
    { k with wvec := k.wvec.set (2 * not_lit + 1) (BitVec.ofNat 32 (q - off)) }
  have hoff_k' : ∀ l, fullWatchOffCore k' l = fullWatchOffCore k l := fun l => by
    unfold fullWatchOffCore; dsimp only [k']; rw [List.getElem?_set_ne (by omega)]
  have hsz_not' : fullWatchSizeCore k' not_lit = q - off := by
    unfold fullWatchSizeCore; dsimp only [k']
    rw [List.getElem?_set_self (by rw [hwlen_vec]; omega), Option.getD_some,
      bv32_ofNat_toNat_lt hq32]
  have hsz_other' : ∀ l, l ≠ not_lit → fullWatchSizeCore k' l = fullWatchSizeCore k l :=
    fun l hn => by
    unfold fullWatchSizeCore; dsimp only [k']; rw [List.getElem?_set_ne (by omega)]
  refine WatchesInv.of_slices (fun l hl => ?_) (fun l hl hp => ?_)
    (fun l1 l2 h1 h2 hne hp1 hp2 => ?_) (fun l hl => ?_)
  · dsimp only at hl
    change fullWatchOffCore k' l + fullWatchSizeCore k' l ≤ k'.wlen
    rw [hoff_k' l]; by_cases hln : l = not_lit
    · subst hln; rw [hsz_not', h.off_eq]; change off + (q - off) ≤ k.wlen; omega
    · rw [hsz_other' l hln]; exact h.layout.bounds l hl
  · dsimp only at hl
    change 0 < fullWatchSizeCore k' l at hp
    change 1 ≤ fullWatchOffCore k' l
    rw [hoff_k' l]; by_cases hln : l = not_lit
    · subst hln; exact h.layout.pos_off l hl (by rw [hsz]; exact h.sz_pos)
    · rw [hsz_other' l hln] at hp; exact h.layout.pos_off l hl hp
  · dsimp only at h1 h2
    change 0 < fullWatchSizeCore k' l1 at hp1; change 0 < fullWatchSizeCore k' l2 at hp2
    change fullWatchOffCore k' l1 + fullWatchSizeCore k' l1 ≤ fullWatchOffCore k' l2 ∨
      fullWatchOffCore k' l2 + fullWatchSizeCore k' l2 ≤ fullWatchOffCore k' l1
    rw [hoff_k' l1, hoff_k' l2]
    by_cases hn1 : l1 = not_lit
    · subst hn1; rw [h.off_eq, hsz_not']; rw [hsz_other' l2 hne.symm] at hp2 ⊢
      rcases h.layout.disjoint l1 l2 h1 h2 hne (by rw [hsz]; exact h.sz_pos) hp2 with ha | hb'
      · left; rw [h.off_eq, hsz] at ha; omega
      · right; rw [h.off_eq] at hb'; exact hb'
    · by_cases hn2 : l2 = not_lit
      · subst hn2; rw [h.off_eq, hsz_not']; rw [hsz_other' l1 hn1] at hp1 ⊢
        rcases h.layout.disjoint l1 l2 h1 h2 hne hp1 (by rw [hsz]; exact h.sz_pos) with ha | hb'
        · left; rw [h.off_eq] at ha; exact ha
        · right; rw [h.off_eq, hsz] at hb'; omega
      · rw [hsz_other' l1 hn1] at hp1 ⊢; rw [hsz_other' l2 hn2] at hp2 ⊢
        exact h.layout.disjoint l1 l2 h1 h2 hne hp1 hp2
  · dsimp only at hl
    change WatchSliceOk F_cur k' l (fullWatchOffCore k' l) (fullWatchSizeCore k' l)
    rw [hoff_k' l]; by_cases hln : l = not_lit
    · subst hln; rw [hsz_not', h.off_eq]
      exact WatchSliceOk.mono (k := k) (by rw [CNF.entails_def]; exact fun _ p => p)
        (Nat.le_refl _) (fun _ r => r) (fun _ _ _ => rfl) h.kept_slice
    · rw [hsz_other' l hln]
      exact WatchSliceOk.mono (k := k) (by rw [CNF.entails_def]; exact fun _ p => p)
        (Nat.le_refl _) (fun _ r => r) (fun _ _ _ => rfl) (h.other_slices l hl hln)

theorem SplitWatchesInv.with_nonwatch {F_cur : List (List Nat)} {k k' : FullCoreState}
    {not_lit off q p end_v : Nat} (h : SplitWatchesInv F_cur k not_lit off q p end_v)
    (hcv : k'.cur_vars = k.cur_vars) (hw : k'.wvec = k.wvec) (hs : k'.wstk = k.wstk)
    (hl : k'.wlen = k.wlen)
    (ha : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k') :
    SplitWatchesInv F_cur k' not_lit off q p end_v :=
  ⟨h.layout.with_wstk hcv hw hs hl,
   by unfold fullWatchOffCore; rw [hw]; exact h.off_eq,
   by unfold fullWatchSizeCore; rw [hw]; exact h.sz_eq,
   h.sz_pos, h.q_ge, h.q_le_p, h.p_le_end,
   fun l hl' hne => by
     simpa [fullWatchOffCore, fullWatchSizeCore, hw] using
       (h.other_slices l (hcv ▸ hl') hne).mono (by rw [CNF.entails_def]; exact fun _ p => p)
         (by omega) ha fun _ _ _ => by simp [hs],
   h.kept_slice.mono (by rw [CNF.entails_def]; exact fun _ p => p) (by omega) ha
     fun _ _ _ => by simp [hs],
   h.rem_slice.mono (by rw [CNF.entails_def]; exact fun _ p => p) (by omega) ha
     fun _ _ _ => by simp [hs]⟩

/-! ## 2. `DelayedWatchesOk` & Delayed-Flush Layout Helpers -/

theorem delayedWatchesOk_congr {k k' : FullCoreState} {del : List (BitVec 32)} {dlen skip_lit : Nat}
    (h : DelayedWatchesOk k del dlen skip_lit) (hcv : k'.cur_vars = k.cur_vars)
    (haref : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k') :
    DelayedWatchesOk k' del dlen skip_lit := fun j hj => by
  obtain ⟨hr, hne, hf, hc, hmem⟩ := h j hj
  exact ⟨hcv ▸ hr, hne, hf, hc, haref _ hmem⟩

theorem delayedWatchesOk_push {k : FullCoreState} {del : List (BitVec 32)}
    {dlen skip_lit : Nat} {repl w0 cref : BitVec 32}
    (h : DelayedWatchesOk k del dlen skip_lit) (hdl : 3 * dlen + 2 < del.length)
    (hrepl : repl.toNat < 2 * k.cur_vars) (hne : repl.toNat ≠ skip_lit)
    (hflag : (w0 &&& 0x80000000#32) = 0#32) (hcr : cref.toNat < 0x80000000)
    (href : cref.toNat ∈ fullArenaClauseRefsCore k) :
    DelayedWatchesOk k
      (((del.set (3 * dlen) repl).set (3 * dlen + 1) w0).set (3 * dlen + 2) cref)
      (dlen + 1) skip_lit := by
  intro j hj
  by_cases heq : j = dlen
  · subst heq
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_self (by omega), Option.getD_some,
      List.getElem?_set_ne (by omega), List.getElem?_set_self (by rw [List.length_set]; omega),
      Option.getD_some, List.getElem?_set_self (by simp; omega), Option.getD_some]
    exact ⟨hrepl, hne, hflag, hcr, href⟩
  · have hlt : j < dlen := by omega
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega)]
    exact h j hlt

theorem fid_watches_congr {F_cur : List (List Nat)} {k k' : FullCoreState}
    (h : WatchesInv F_cur k) (hcv : k'.cur_vars = k.cur_vars)
    (hwv : k'.wvec = k.wvec) (hws : k'.wstk = k.wstk) (hwl : k'.wlen = k.wlen)
    (ha : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k') :
    WatchesInv F_cur k' :=
  watchesInv_with_wstk h hcv hwv hws hwl ha

@[expose] def fidFlushDisk (wl_d : Nat) (wu_d : BitVec 64) (st : FullState) : FullState :=
  { st with core := { st.core with wlen := wl_d, wusable := wu_d } }

theorem fid_repl_empty_layout {c : FullCfg} {k : FullCoreState}
    (hlay : WatchStackLayout k) (hlen : k.LengthsOk c) {lit w0 cref : BitVec 32}
    (hlit : lit.toNat < 2 * k.cur_vars) (hw_pos : 1 ≤ k.wlen)
    (hrsz0 : fullWatchSizeCore k lit.toNat = 0) (hfit2 : k.wlen + 2 ≤ c.wcap)
    (hw0_f : (w0 &&& 0x80000000#32) = 0#32) (hcr_lt : cref.toNat < 0x80000000) :
    let wend := k.wlen
    let k' : FullCoreState :=
      { k with
        wstk := (k.wstk.set wend w0).set (wend + 1) cref
        wvec := (k.wvec.set (2 * lit.toNat) (BitVec.ofNat 32 wend)).set
          (2 * lit.toNat + 1) 2#32
        wlen := wend + 2 }
    k'.LengthsOk c ∧ WatchStackLayout k' ∧
    (∀ l, l ≠ lit.toNat → fullWatchOffCore k' l = fullWatchOffCore k l) ∧
    (∀ l < 2 * k.cur_vars, l ≠ lit.toNat →
      fullWatchSizeCore k' l = fullWatchSizeCore k l ∧
      ∀ j < fullWatchSizeCore k l,
        k'.wstk[fullWatchOffCore k' l + j]? = k.wstk[fullWatchOffCore k l + j]?) ∧
    fullWatchSizeCore k' lit.toNat = fullWatchSizeCore k lit.toNat + 2 ∧
    (∀ j < fullWatchSizeCore k lit.toNat,
      k'.wstk[fullWatchOffCore k' lit.toNat + j]? =
        k.wstk[fullWatchOffCore k lit.toNat + j]?) ∧
    k'.wstk[fullWatchOffCore k' lit.toNat + fullWatchSizeCore k lit.toNat]? = some w0 ∧
    k'.wstk[fullWatchOffCore k' lit.toNat + fullWatchSizeCore k lit.toNat + 1]? = some cref := by
  intro wend k'
  have hwc := c.hwcap; have hmaxv := c.hmaxv; unfold dimacsBound at hwc hmaxv
  have hcv := hlen.cur_vars_le; have hwv := hlen.wvec_len; have hws := hlen.wstk_len_arr
  have hwend_32 : wend < 2 ^ 32 := by dsimp [wend]; omega
  have h2l_lt : 2 * lit.toNat < k.wvec.length := by rw [hwv]; omega
  have h2l1_lt : 2 * lit.toNat + 1 < k.wvec.length := by rw [hwv]; omega
  have hw0_lt : wend < k.wstk.length := by rw [hws]; dsimp [wend]; omega
  have hw1_lt : wend + 1 < k.wstk.length := by rw [hws]; dsimp [wend]; omega
  have hoff_lit : fullWatchOffCore k' lit.toNat = wend := by
    unfold fullWatchOffCore; dsimp [k']
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_self h2l_lt, Option.getD_some,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt hwend_32]
  have hsz_lit : fullWatchSizeCore k' lit.toNat = 2 := by
    unfold fullWatchSizeCore; dsimp [k']
    rw [List.getElem?_set_self (by rw [List.length_set]; exact h2l1_lt), Option.getD_some]; rfl
  have hoff_ne : ∀ l, l ≠ lit.toNat → fullWatchOffCore k' l = fullWatchOffCore k l := by
    intro l hne; unfold fullWatchOffCore; dsimp [k']
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
  have hsz_ne : ∀ l, l ≠ lit.toNat → fullWatchSizeCore k' l = fullWatchSizeCore k l := by
    intro l hne; unfold fullWatchSizeCore; dsimp [k']
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
  have hwstk_ne : ∀ j < wend, k'.wstk[j]? = k.wstk[j]? := by
    intro j hj; dsimp [k']
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
  have hlen' : k'.LengthsOk c :=
    { hlen with wstk_len_arr := by simp [k', hws], wvec_len := by simp [k', hwv], wlen_le := hfit2 }
  have hlay' : WatchStackLayout k' := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro l hl; by_cases hll : l = lit.toNat
      · subst hll; rw [hoff_lit, hsz_lit]; dsimp [k']; omega
      · rw [hoff_ne l hll, hsz_ne l hll]
        exact Nat.le_trans (hlay.bounds l hl) (by dsimp [k']; omega)
    · intro l hl hpos; by_cases hll : l = lit.toNat
      · subst hll; rw [hoff_lit]; exact hw_pos
      · rw [hoff_ne l hll]; rw [hsz_ne l hll] at hpos; exact hlay.pos_off l hl hpos
    · intro l1 l2 h1 h2 hne hp1 hp2
      by_cases hl1 : l1 = lit.toNat
      · subst hl1; rw [hsz_ne l2 hne.symm] at hp2 ⊢; rw [hoff_lit, hoff_ne l2 hne.symm]
        exact Or.inr (hlay.bounds l2 h2)
      · by_cases hl2 : l2 = lit.toNat
        · subst hl2; rw [hsz_ne l1 hl1] at hp1 ⊢; rw [hoff_ne l1 hl1, hoff_lit]
          exact Or.inl (hlay.bounds l1 h1)
        · rw [hsz_ne l1 hl1] at hp1 ⊢; rw [hsz_ne l2 hl2] at hp2 ⊢
          rw [hoff_ne l1 hl1, hoff_ne l2 hl2]; exact hlay.disjoint l1 l2 h1 h2 hne hp1 hp2
    · intro l hl idx hidx; by_cases hll : l = lit.toNat
      · subst hll; rw [hsz_lit] at hidx; rw [hoff_lit]
        rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_of_lt_of_eq hidx rfl) with h0 | rfl
        · have hi0 : idx = 0 := by omega
          subst hi0; dsimp [k']
          rw [List.getElem?_set_ne (by omega), List.getElem?_set_self hw0_lt]
          intro heq; rw [Option.some.inj heq] at hw0_f; exact absurd hw0_f (by decide)
        · dsimp [k']; rw [List.getElem?_set_self (by rw [List.length_set]; exact hw1_lt)]
          intro heq; have h := Option.some.inj heq; rw [h] at hcr_lt; revert hcr_lt; decide
      · rw [hsz_ne l hll] at hidx; rw [hoff_ne l hll]
        have hb := hlay.bounds l hl
        rw [hwstk_ne (fullWatchOffCore k l + idx) (by omega)]; exact hlay.no_sentinel l hl idx hidx
  refine ⟨hlen', hlay', hoff_ne, fun l hl hne => ⟨hsz_ne l hne, fun j hj => ?_⟩,
    by rw [hsz_lit, hrsz0], fun j hj => by omega, ?_, ?_⟩
  · have hb := hlay.bounds l hl; rw [hoff_ne l hne]; exact hwstk_ne _ (by omega)
  · rw [hrsz0, hoff_lit, Nat.add_zero]; dsimp [k']
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_self hw0_lt]
  · rw [hrsz0, hoff_lit, Nat.add_zero]; dsimp [k']
    rw [List.getElem?_set_self (by rw [List.length_set]; exact hw1_lt)]

theorem m7_repl_empty_layout {c : FullCfg} {k : FullCoreState}
    (hlay : WatchStackLayout k) (hlen : k.LengthsOk c) {not_lit : Nat} {lit w0 cref : BitVec 32}
    (hlit : lit.toNat < 2 * k.cur_vars) (hnot : not_lit < 2 * k.cur_vars)
    (hnot_sz : 0 < fullWatchSizeCore k not_lit) (hrsz0 : fullWatchSizeCore k lit.toNat = 0)
    (hfit2 : k.wlen + 2 ≤ c.wcap)
    (hw0_f : (w0 &&& 0x80000000#32) = 0#32) (hcr_lt : cref.toNat < 0x80000000) :
    let wend := k.wlen
    let k' : FullCoreState :=
      { k with
        wstk := (k.wstk.set wend w0).set (wend + 1) cref
        wvec := (k.wvec.set (2 * lit.toNat) (BitVec.ofNat 32 wend)).set
          (2 * lit.toNat + 1) 2#32
        wlen := wend + 2 }
    k'.LengthsOk c ∧ WatchStackLayout k' ∧
    (∀ l, l ≠ lit.toNat → fullWatchOffCore k' l = fullWatchOffCore k l) ∧
    (∀ l < 2 * k.cur_vars, l ≠ lit.toNat →
      fullWatchSizeCore k' l = fullWatchSizeCore k l ∧
      ∀ j < fullWatchSizeCore k l,
        k'.wstk[fullWatchOffCore k' l + j]? = k.wstk[fullWatchOffCore k l + j]?) ∧
    fullWatchSizeCore k' lit.toNat = fullWatchSizeCore k lit.toNat + 2 ∧
    (∀ j < fullWatchSizeCore k lit.toNat,
      k'.wstk[fullWatchOffCore k' lit.toNat + j]? =
        k.wstk[fullWatchOffCore k lit.toNat + j]?) ∧
    k'.wstk[fullWatchOffCore k' lit.toNat + fullWatchSizeCore k lit.toNat]? = some w0 ∧
    k'.wstk[fullWatchOffCore k' lit.toNat + fullWatchSizeCore k lit.toNat + 1]? = some cref :=
  fid_repl_empty_layout hlay hlen hlit
    (by have := hlay.pos_off not_lit hnot hnot_sz; have := hlay.bounds not_lit hnot; omega)
    hrsz0 hfit2 hw0_f hcr_lt

theorem s15_append_end_layout {c : FullCfg} {k : FullCoreState}
    (hlay : WatchStackLayout k) (hlen : k.LengthsOk c) {lit w0 cref : BitVec 32}
    (hlit : lit.toNat < 2 * k.cur_vars) (hrsz_pos : 0 < fullWatchSizeCore k lit.toNat)
    (heq_end : fullWatchOffCore k lit.toNat + fullWatchSizeCore k lit.toNat = k.wlen)
    (hfit2 : k.wlen + 2 ≤ c.wcap)
    (hw0_f : (w0 &&& 0x80000000#32) = 0#32) (hcr_lt : cref.toNat < 0x80000000) :
    let wend := k.wlen
    let k' : FullCoreState :=
      { k with
        wstk := (k.wstk.set wend w0).set (wend + 1) cref
        wvec := k.wvec.set (2 * lit.toNat + 1) (BitVec.ofNat 32 (fullWatchSizeCore k lit.toNat + 2))
        wlen := wend + 2 }
    k'.LengthsOk c ∧ WatchStackLayout k' ∧
    (∀ l, l ≠ lit.toNat → fullWatchOffCore k' l = fullWatchOffCore k l) ∧
    (∀ l < 2 * k.cur_vars, l ≠ lit.toNat →
      fullWatchSizeCore k' l = fullWatchSizeCore k l ∧
      ∀ j < fullWatchSizeCore k l,
        k'.wstk[fullWatchOffCore k' l + j]? = k.wstk[fullWatchOffCore k l + j]?) ∧
    fullWatchSizeCore k' lit.toNat = fullWatchSizeCore k lit.toNat + 2 ∧
    (∀ j < fullWatchSizeCore k lit.toNat,
      k'.wstk[fullWatchOffCore k' lit.toNat + j]? =
        k.wstk[fullWatchOffCore k lit.toNat + j]?) ∧
    k'.wstk[fullWatchOffCore k' lit.toNat + fullWatchSizeCore k lit.toNat]? = some w0 ∧
    k'.wstk[fullWatchOffCore k' lit.toNat + fullWatchSizeCore k lit.toNat + 1]? = some cref := by
  intro wend k'
  have hwc := c.hwcap; have hmaxv := c.hmaxv; unfold dimacsBound at hwc hmaxv
  have hcv := hlen.cur_vars_le; have hwv := hlen.wvec_len; have hws := hlen.wstk_len_arr
  have hsz2_32 : fullWatchSizeCore k lit.toNat + 2 < 2 ^ 32 := by omega
  have h2l1_lt : 2 * lit.toNat + 1 < k.wvec.length := by rw [hwv]; omega
  have hw0_lt : wend < k.wstk.length := by rw [hws]; dsimp [wend]; omega
  have hw1_lt : wend + 1 < k.wstk.length := by rw [hws]; dsimp [wend]; omega
  have hoff_all : ∀ l, fullWatchOffCore k' l = fullWatchOffCore k l := fun l => by
    unfold fullWatchOffCore; dsimp [k']; rw [List.getElem?_set_ne (by omega)]
  have hsz_lit : fullWatchSizeCore k' lit.toNat = fullWatchSizeCore k lit.toNat + 2 := by
    unfold fullWatchSizeCore; dsimp [k']
    rw [List.getElem?_set_self h2l1_lt, Option.getD_some, bv32_ofNat_toNat_lt hsz2_32]; rfl
  have hsz_ne : ∀ l, l ≠ lit.toNat → fullWatchSizeCore k' l = fullWatchSizeCore k l := by
    intro l hne; unfold fullWatchSizeCore; dsimp [k']; rw [List.getElem?_set_ne (by omega)]
  have hwstk_ne : ∀ j < wend, k'.wstk[j]? = k.wstk[j]? := fun j hj => by
    dsimp [k']; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
  have hlen' : k'.LengthsOk c :=
    { hlen with wstk_len_arr := by simp [k', hws], wvec_len := by simp [k', hwv], wlen_le := hfit2 }
  have hlay' : WatchStackLayout k' := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro l hl; rw [hoff_all l]; by_cases hll : l = lit.toNat
      · subst hll; rw [hsz_lit]; dsimp [k']; omega
      · rw [hsz_ne l hll]; exact Nat.le_trans (hlay.bounds l hl) (by dsimp [k']; omega)
    · intro l hl hpos; rw [hoff_all l]; by_cases hll : l = lit.toNat
      · subst hll; exact hlay.pos_off lit.toNat hl hrsz_pos
      · rw [hsz_ne l hll] at hpos; exact hlay.pos_off l hl hpos
    · intro l1 l2 h1 h2 hne hp1 hp2
      rw [hoff_all l1, hoff_all l2]
      by_cases hl1 : l1 = lit.toNat
      · subst hl1; rw [hsz_lit]; rw [hsz_ne l2 hne.symm] at hp2 ⊢
        rcases hlay.disjoint lit.toNat l2 h1 h2 hne hrsz_pos hp2 with h | h
        · have hb2 := hlay.bounds l2 h2; rw [heq_end] at h; exfalso; omega
        · right; exact h
      · by_cases hl2 : l2 = lit.toNat
        · subst hl2; rw [hsz_lit]; rw [hsz_ne l1 hl1] at hp1 ⊢
          rcases hlay.disjoint l1 lit.toNat h1 h2 hne hp1 hrsz_pos with h | h
          · left; exact h
          · have hb1 := hlay.bounds l1 h1; rw [heq_end] at h; exfalso; omega
        · rw [hsz_ne l1 hl1] at hp1 ⊢; rw [hsz_ne l2 hl2] at hp2 ⊢
          exact hlay.disjoint l1 l2 h1 h2 hne hp1 hp2
    · intro l hl idx hidx; rw [hoff_all l]; by_cases hll : l = lit.toNat
      · subst hll; rw [hsz_lit] at hidx
        by_cases hlt : idx < fullWatchSizeCore k lit.toNat
        · rw [hwstk_ne _ (by omega)]; exact hlay.no_sentinel lit.toNat hl idx hlt
        · have hidx_eq : idx = fullWatchSizeCore k lit.toNat ∨
              idx = fullWatchSizeCore k lit.toNat + 1 := by omega
          rcases hidx_eq with rfl | rfl
          · have : fullWatchOffCore k lit.toNat + fullWatchSizeCore k lit.toNat = wend := heq_end
            rw [this]; dsimp [k']
            rw [List.getElem?_set_ne (by omega), List.getElem?_set_self hw0_lt]
            intro heq; rw [Option.some.inj heq] at hw0_f; exact absurd hw0_f (by decide)
          · have : fullWatchOffCore k lit.toNat + (fullWatchSizeCore k lit.toNat + 1) =
                wend + 1 := by omega
            rw [this]; dsimp [k']
            rw [List.getElem?_set_self (by rw [List.length_set]; exact hw1_lt)]
            intro heq; have h := Option.some.inj heq; rw [h] at hcr_lt; revert hcr_lt; decide
      · rw [hsz_ne l hll] at hidx; have hb := hlay.bounds l hl
        rw [hwstk_ne _ (by omega)]; exact hlay.no_sentinel l hl idx hidx
  refine ⟨hlen', hlay', fun l _ => hoff_all l,
    fun l hl hne => ⟨hsz_ne l hne, fun j hj => by
      have hb := hlay.bounds l hl; rw [hoff_all l]; exact hwstk_ne _ (by omega)⟩,
    hsz_lit, fun j hj => by rw [hoff_all lit.toNat]; exact hwstk_ne _ (by omega), ?_, ?_⟩
  · rw [hoff_all lit.toNat, heq_end]; dsimp [k']
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_self hw0_lt]
  · rw [hoff_all lit.toNat, show fullWatchOffCore k lit.toNat + fullWatchSizeCore k lit.toNat + 1 =
      wend + 1 by omega]
    dsimp [k']; rw [List.getElem?_set_self (by rw [List.length_set]; exact hw1_lt)]

theorem s15_append_sentinel_layout {c : FullCfg} {k : FullCoreState}
    (hlay : WatchStackLayout k) (hlen : k.LengthsOk c) {lit w0 cref : BitVec 32}
    (hlit : lit.toNat < 2 * k.cur_vars) (hrsz_pos : 0 < fullWatchSizeCore k lit.toNat)
    (hsent : k.wstk[fullWatchOffCore k lit.toNat + fullWatchSizeCore k lit.toNat]? =
      some 0xFFFFFFFF#32)
    (hnext : k.wstk[fullWatchOffCore k lit.toNat + fullWatchSizeCore k lit.toNat + 1]? =
      some 0xFFFFFFFF#32)
    (hnext_lt : fullWatchOffCore k lit.toNat + fullWatchSizeCore k lit.toNat + 1 < k.wlen)
    (hw0_f : (w0 &&& 0x80000000#32) = 0#32) (hcr_lt : cref.toNat < 0x80000000) :
    let roff := fullWatchOffCore k lit.toNat
    let rsz := fullWatchSizeCore k lit.toNat
    let k' : FullCoreState :=
      { k with
        wstk := (k.wstk.set (roff + rsz) w0).set (roff + rsz + 1) cref
        wvec := k.wvec.set (2 * lit.toNat + 1) (BitVec.ofNat 32 (rsz + 2)) }
    k'.LengthsOk c ∧ WatchStackLayout k' ∧
    (∀ l, l ≠ lit.toNat → fullWatchOffCore k' l = fullWatchOffCore k l) ∧
    (∀ l < 2 * k.cur_vars, l ≠ lit.toNat →
      fullWatchSizeCore k' l = fullWatchSizeCore k l ∧
      ∀ j < fullWatchSizeCore k l,
        k'.wstk[fullWatchOffCore k' l + j]? = k.wstk[fullWatchOffCore k l + j]?) ∧
    fullWatchSizeCore k' lit.toNat = fullWatchSizeCore k lit.toNat + 2 ∧
    (∀ j < fullWatchSizeCore k lit.toNat,
      k'.wstk[fullWatchOffCore k' lit.toNat + j]? =
        k.wstk[fullWatchOffCore k lit.toNat + j]?) ∧
    k'.wstk[fullWatchOffCore k' lit.toNat + fullWatchSizeCore k lit.toNat]? = some w0 ∧
    k'.wstk[fullWatchOffCore k' lit.toNat + fullWatchSizeCore k lit.toNat + 1]? = some cref := by
  intro roff rsz k'
  have hwc := c.hwcap; have hmaxv := c.hmaxv; unfold dimacsBound at hwc hmaxv
  have hcv := hlen.cur_vars_le; have hwv := hlen.wvec_len; have hws := hlen.wstk_len_arr
  have hwlen_le := hlen.wlen_le
  have hsz2_32 : rsz + 2 < 2 ^ 32 := by omega
  have h2l1_lt : 2 * lit.toNat + 1 < k.wvec.length := by rw [hwv]; omega
  have hw0_lt : roff + rsz < k.wstk.length := by rw [hws]; omega
  have hw1_lt : roff + rsz + 1 < k.wstk.length := by rw [hws]; omega
  have hoff_all : ∀ l, fullWatchOffCore k' l = fullWatchOffCore k l := fun l => by
    unfold fullWatchOffCore; dsimp [k']; rw [List.getElem?_set_ne (by omega)]
  have hsz_lit : fullWatchSizeCore k' lit.toNat = rsz + 2 := by
    unfold fullWatchSizeCore; dsimp [k']
    rw [List.getElem?_set_self h2l1_lt, Option.getD_some, bv32_ofNat_toNat_lt hsz2_32]
  have hsz_ne : ∀ l, l ≠ lit.toNat → fullWatchSizeCore k' l = fullWatchSizeCore k l := by
    intro l hne; unfold fullWatchSizeCore; dsimp [k']; rw [List.getElem?_set_ne (by omega)]
  have hdisj_other : ∀ l < 2 * k.cur_vars, l ≠ lit.toNat → ∀ idx < fullWatchSizeCore k l,
      fullWatchOffCore k l + idx ≠ roff + rsz ∧ fullWatchOffCore k l + idx ≠ roff + rsz + 1 := by
    intro l hl hne idx hidx
    rcases Nat.eq_zero_or_pos (fullWatchSizeCore k l) with hz | hpos
    · omega
    · rcases hlay.disjoint l lit.toNat hl hlit hne hpos hrsz_pos with h1 | h2
      · constructor <;> omega
      · have hns0 := hlay.no_sentinel l hl idx hidx
        have hlt1 : fullWatchOffCore k l + idx ≠ roff + rsz := fun heq => by
          rw [heq] at hns0; exact hns0 hsent
        have hlt2 : fullWatchOffCore k l + idx ≠ roff + rsz + 1 := fun heq => by
          rw [heq] at hns0; exact hns0 hnext
        exact ⟨hlt1, hlt2⟩
  have hother_ub : ∀ l < 2 * k.cur_vars, l ≠ lit.toNat → 0 < fullWatchSizeCore k l →
      roff + (rsz + 2) ≤ fullWatchOffCore k l ∨
        fullWatchOffCore k l + fullWatchSizeCore k l ≤ roff := by
    intro l hl hne hpos
    rcases hlay.disjoint lit.toNat l hlit hl hne.symm hrsz_pos hpos with h1 | h2
    · by_cases hlt : roff + (rsz + 2) ≤ fullWatchOffCore k l
      · exact Or.inl hlt
      · exfalso; have hlt' : fullWatchOffCore k l < roff + rsz + 2 := Nat.lt_of_not_le hlt
        have hidx_eq : fullWatchOffCore k l = roff + rsz ∨
            fullWatchOffCore k l = roff + rsz + 1 := by omega
        have hns0 := hlay.no_sentinel l hl 0 hpos
        rcases hidx_eq with heq | heq <;> rw [Nat.add_zero, heq] at hns0
        · exact hns0 hsent
        · exact hns0 hnext
    · right; exact h2
  have hwstk_other : ∀ l < 2 * k.cur_vars, l ≠ lit.toNat → ∀ j < fullWatchSizeCore k l,
      k'.wstk[fullWatchOffCore k' l + j]? = k.wstk[fullWatchOffCore k l + j]? := by
    intro l hl hne j hj; obtain ⟨hn0, hn1⟩ := hdisj_other l hl hne j hj
    rw [hoff_all l]; dsimp [k']
    rw [List.getElem?_set_ne (Ne.symm hn1), List.getElem?_set_ne (Ne.symm hn0)]
  have hwstk_lit_old : ∀ j < rsz, k'.wstk[roff + j]? = k.wstk[roff + j]? := fun j hj => by
    dsimp [k']; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
  have hlen' : k'.LengthsOk c :=
    { hlen with wstk_len_arr := by simp [k', hws], wvec_len := by simp [k', hwv] }
  have hlay' : WatchStackLayout k' := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro l hl; rw [hoff_all l]; by_cases hll : l = lit.toNat
      · subst hll; rw [hsz_lit]; dsimp [k']; omega
      · rw [hsz_ne l hll]; exact hlay.bounds l hl
    · intro l hl hpos; rw [hoff_all l]; by_cases hll : l = lit.toNat
      · subst hll; exact hlay.pos_off lit.toNat hl hrsz_pos
      · rw [hsz_ne l hll] at hpos; exact hlay.pos_off l hl hpos
    · intro l1 l2 h1 h2 hne hp1 hp2; rw [hoff_all l1, hoff_all l2]
      by_cases hl1 : l1 = lit.toNat
      · subst hl1; rw [hsz_lit]; rw [hsz_ne l2 hne.symm] at hp2 ⊢
        exact hother_ub l2 h2 hne.symm hp2
      · by_cases hl2 : l2 = lit.toNat
        · subst hl2; rw [hsz_lit]; rw [hsz_ne l1 hl1] at hp1 ⊢
          exact (hother_ub l1 h1 hl1 hp1).symm
        · rw [hsz_ne l1 hl1] at hp1 ⊢; rw [hsz_ne l2 hl2] at hp2 ⊢
          exact hlay.disjoint l1 l2 h1 h2 hne hp1 hp2
    · intro l hl idx hidx; by_cases hll : l = lit.toNat
      · subst hll; rw [hoff_all lit.toNat]; rw [hsz_lit] at hidx
        by_cases hlt : idx < rsz
        · rw [hwstk_lit_old idx hlt]; exact hlay.no_sentinel lit.toNat hl idx hlt
        · have hidx_eq : idx = rsz ∨ idx = rsz + 1 := by omega
          rcases hidx_eq with rfl | rfl
          · dsimp [k']; rw [List.getElem?_set_ne (by omega), List.getElem?_set_self hw0_lt]
            intro heq; rw [Option.some.inj heq] at hw0_f; exact absurd hw0_f (by decide)
          · dsimp [k']
            rw [show fullWatchOffCore k lit.toNat + (rsz + 1) = roff + rsz + 1 by
                dsimp [roff]; omega,
              List.getElem?_set_self (by rw [List.length_set]; exact hw1_lt)]
            intro heq; have h := Option.some.inj heq; rw [h] at hcr_lt; revert hcr_lt; decide
      · rw [hsz_ne l hll] at hidx; rw [hwstk_other l hl hll idx hidx]
        exact hlay.no_sentinel l hl idx hidx
  refine ⟨hlen', hlay', fun l _ => hoff_all l,
    fun l hl hne => ⟨hsz_ne l hne, hwstk_other l hl hne⟩, hsz_lit,
    fun j hj => by rw [hoff_all lit.toNat]; exact hwstk_lit_old j hj, ?_, ?_⟩
  · rw [hoff_all lit.toNat]; dsimp [k']
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_self hw0_lt]
  · rw [hoff_all lit.toNat]; dsimp [k']
    rw [List.getElem?_set_self (by rw [List.length_set]; exact hw1_lt)]

theorem s15_flush_step_preserves {_c : FullCfg} {F_cur : List (List Nat)}
    {k k' : FullCoreState} {skip_lit : Nat} {w0 cref : BitVec 32} {lit : Nat}
    (hcv : k'.cur_vars = k.cur_vars)
    (haref : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k')
    (hlit : lit < 2 * k.cur_vars) (hlit_ne : lit ≠ skip_lit)
    (hw0_flag : (w0 &&& 0x80000000#32) = 0#32) (hcr_lt : cref.toNat < 0x80000000)
    (hcr_ref : cref.toNat ∈ fullArenaClauseRefsCore k')
    (hoff_ne : ∀ l, l ≠ lit → fullWatchOffCore k' l = fullWatchOffCore k l)
    (hother : ∀ l < 2 * k.cur_vars, l ≠ lit →
      fullWatchSizeCore k' l = fullWatchSizeCore k l ∧
      ∀ idx < fullWatchSizeCore k l,
        k'.wstk[fullWatchOffCore k' l + idx]? = k.wstk[fullWatchOffCore k l + idx]?)
    (hlit_ok : fullWatchSizeCore k' lit = fullWatchSizeCore k lit + 2 ∧
      (∀ idx < fullWatchSizeCore k lit,
        k'.wstk[fullWatchOffCore k' lit + idx]? = k.wstk[fullWatchOffCore k lit + idx]?) ∧
      k'.wstk[fullWatchOffCore k' lit + fullWatchSizeCore k lit]? = some w0 ∧
      k'.wstk[fullWatchOffCore k' lit + fullWatchSizeCore k lit + 1]? = some cref)
    (hlay' : WatchStackLayout k') :
    (WatchesInv F_cur k → WatchesInv F_cur k') ∧
    (skip_lit < 2 * k.cur_vars → ∀ off q p end_v, SplitWatchesInv F_cur k skip_lit off q p end_v →
      let off' := fullWatchOffCore k' skip_lit
      SplitWatchesInv F_cur k' skip_lit off'
        (off' + (q - off)) (off' + (p - off)) (off' + (end_v - off))) := by
  constructor
  · intro hw; refine ⟨hlay', fun l hl' => ?_⟩; have hl : l < 2 * k.cur_vars := hcv ▸ hl'
    by_cases hll : l = lit
    · rw [hll, hlit_ok.1]
      exact watchSlice_append_large (k := k) (p := fullWatchOffCore k lit)
        (hcv ▸ Nat.le_refl _) haref hlit_ok.2.1 (hll ▸ hw.slices l hl)
        hlit_ok.2.2.1 hlit_ok.2.2.2 hw0_flag hcr_lt hcr_ref
    · have ⟨hsz, hcp⟩ := hother l hl hll; rw [hoff_ne l hll, hsz]
      exact WatchSliceOk.mono (k := k) (by rw [CNF.entails_def]; exact fun _ p => p)
        (hcv ▸ Nat.le_refl _) haref (fun idx hlo hhi => by
          change fullWatchOffCore k l ≤ idx at hlo
          change idx < fullWatchOffCore k l + fullWatchSizeCore k l at hhi
          have := hcp (idx - fullWatchOffCore k l) (by omega)
          rwa [hoff_ne l hll,
            show fullWatchOffCore k l + (idx - fullWatchOffCore k l) = idx by omega] at this)
        (hw.slices l hl)
  · intro hskip off q p end_v hsw
    have hoff_eq : fullWatchOffCore k' skip_lit = off := by
      rw [hoff_ne skip_lit hlit_ne.symm, hsw.off_eq]
    have hsw' := SplitWatchesInv.push_nonskip (w0 := w0.toNat) (cref := cref.toNat)
      hcv haref hlit hlit_ne hsw hskip hlay' hother
      ⟨hlit_ok.1, hlit_ok.2.1,
        by simpa [bv32_ofNat_toNat_lt w0.isLt] using hlit_ok.2.2.1,
        by simpa [bv32_ofNat_toNat_lt cref.isLt] using hlit_ok.2.2.2⟩
      (by simpa [bv32_ofNat_toNat_lt w0.isLt] using hw0_flag)
      hcr_lt hcr_ref
    simpa only [hoff_eq] using hsw'

theorem s15_flush_step_false_preserves {c : FullCfg} {F_cur : List (List Nat)}
    {k : FullCoreState} {skip_lit : Nat}
    (hlen : k.LengthsOk c) (hlay : WatchStackLayout k) (_hs_len : k.wstk.length = c.wcap)
    {repl : BitVec 32} (_hrepl : repl.toNat < 2 * k.cur_vars)
    {w0 cref : BitVec 32} (hwstk' : List (BitVec 32))
    (hws_len' : hwstk'.length = c.wcap)
    (hhold : ∀ l < 2 * k.cur_vars, l ≠ repl.toNat → ∀ idx < fullWatchSizeCore k l,
      hwstk'[fullWatchOffCore k l + idx]? = k.wstk[fullWatchOffCore k l + idx]?)
    (hhold_r : ∀ idx < fullWatchSizeCore k repl.toNat,
      hwstk'[fullWatchOffCore k repl.toNat + idx]? = k.wstk[fullWatchOffCore k repl.toNat + idx]?)
    (_hset0 : hwstk'[fullWatchOffCore k repl.toNat + fullWatchSizeCore k repl.toNat]? = some w0)
    (_hset1 : hwstk'[fullWatchOffCore k repl.toNat + fullWatchSizeCore k repl.toNat + 1]? =
      some cref) :
    let k' : FullCoreState := { k with wstk := hwstk' }
    k'.LengthsOk c ∧ WatchStackLayout k' ∧
    (WatchesInv F_cur k → WatchesInv F_cur k') ∧
    (skip_lit < 2 * k.cur_vars → ∀ off q p end_v, SplitWatchesInv F_cur k skip_lit off q p end_v →
      let off' := fullWatchOffCore k' skip_lit
      SplitWatchesInv F_cur k' skip_lit off'
        (off' + (q - off)) (off' + (p - off)) (off' + (end_v - off))) := by
  intro k'
  have hlen' : k'.LengthsOk c := { hlen with wstk_len_arr := hws_len' }
  have hns : ∀ l < 2 * k.cur_vars, ∀ idx < fullWatchSizeCore k l,
      hwstk'[fullWatchOffCore k l + idx]? ≠ some 0xFFFFFFFF#32 := fun l hl idx hidx => by
    by_cases hlr : l = repl.toNat
    · subst hlr; rw [hhold_r idx hidx]; exact hlay.no_sentinel repl.toNat hl idx hidx
    · rw [hhold l hl hlr idx hidx]; exact hlay.no_sentinel l hl idx hidx
  have hlay' : WatchStackLayout k' :=
    ⟨hlay.bounds, hlay.pos_off, hlay.disjoint, hns⟩
  have hw_mem : ∀ l < 2 * k.cur_vars, ∀ idx,
      fullWatchOffCore k l ≤ idx → idx < fullWatchOffCore k l + fullWatchSizeCore k l →
      hwstk'[idx]? = k.wstk[idx]? := fun l hl idx hlo hhi => by
    have heq : fullWatchOffCore k l + (idx - fullWatchOffCore k l) = idx := by omega
    by_cases hlr : l = repl.toNat
    · subst hlr
      have := hhold_r (idx - fullWatchOffCore k repl.toNat) (by omega); rwa [heq] at this
    · have := hhold l hl hlr (idx - fullWatchOffCore k l) (by omega); rwa [heq] at this
  refine ⟨hlen', hlay', ?_, ?_⟩
  · intro hw; refine ⟨hlay', fun l hl => WatchSliceOk.mono (k := k)
      (by rw [CNF.entails_def]; exact fun _ p => p) (Nat.le_refl _) (fun _ r => r)
      (fun idx hlo hhi => hw_mem l hl idx hlo hhi) (hw.slices l hl)⟩
  · intro hskip off q p end_v hsw
    have hoff_eq : fullWatchOffCore k' skip_lit = off := hsw.off_eq
    have hq_ge := hsw.q_ge; have hq_le := hsw.q_le_p; have hp_le := hsw.p_le_end
    simpa only [hoff_eq, Nat.sub_self, Nat.add_sub_cancel' hq_ge,
      Nat.add_sub_cancel' (Nat.le_trans hq_ge hq_le),
      Nat.add_sub_cancel' (Nat.le_trans hq_ge (Nat.le_trans hq_le hp_le))] using
      SplitWatchesInv.mk hlay' hsw.off_eq hsw.sz_eq hsw.sz_pos hq_ge hq_le hp_le
        (fun l hl hne => WatchSliceOk.mono (k := k)
          (by rw [CNF.entails_def]; exact fun _ p => p) (Nat.le_refl _) (fun _ r => r)
          (fun idx hlo hhi => hw_mem l hl idx hlo hhi) (hsw.other_slices l hl hne))
        (WatchSliceOk.mono (k := k) (by rw [CNF.entails_def]; exact fun _ p => p) (Nat.le_refl _)
          (fun _ r => r) (fun idx hlo hhi =>
          hw_mem skip_lit hskip idx (by rw [hsw.off_eq]; exact hlo)
            (by rw [hsw.off_eq, hsw.sz_eq]; omega)) hsw.kept_slice)
        (WatchSliceOk.mono (k := k) (by rw [CNF.entails_def]; exact fun _ p => p) (Nat.le_refl _)
          (fun _ r => r) (fun idx hlo hhi =>
          hw_mem skip_lit hskip idx (by rw [hsw.off_eq]; omega)
            (by rw [hsw.off_eq, hsw.sz_eq]; omega)) hsw.rem_slice)

end LeanQbe.T.Examples.Kissat.Proof.PropSearch
