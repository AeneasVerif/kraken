/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM5Otfs
public import LeanQbe.T.Examples.Kissat.FullSpec
public import LeanQbe.T.Examples.Kissat.FullReduceLemmas1
public import LeanQbe.T.Examples.Kissat.FullAnalyzeLemmas5
public import LeanQbe.T.Logic.C0HeadStep
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat M5 `Func.wp` Proofs — Part 1 (`full_unwatch_large`, Watch-Blocker Loop & `full_otfs_large`)

Zero `import all LeanQbe.*`. Proves canonical `FullSpec2` contracts (`XPost := False`, UNSAT-only)
for:
1. `full_unwatch_large_wp` (`Full.fullUnwatchLargeSpec`): backward suffix-free watch deletion.
2. Shared `m5_loop4_sz_wp`: backward watch-slice blocker replacement (used by both
   `full_otfs_large_wp` and `full_prop_lit_chrono_wp` in `FullM5OtfsLemmas2`).
3. `full_otfs_large_wp` (`Full.fullOtfsLargeSpec`): early `cnt >= 3` exit, read-only `nl1_pre`
   scan, headroom pre-check + `full_wstack_defrag` + `full_watch_push` *before* arena swap and
   `full_unwatch_large(uip)`, fused compaction + `hp`, header/`PH_SHRK`, `hp` swap, and `l0`
   blocker update.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM5Otfs

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0HeadStep LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test
open LeanQbe.T.Examples.Kissat.Full hiding
  full_otfs_large_wp full_otfs_large_wp_weak
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics

/-! ## 1. Shared Watch-Slice, BitVec & Local Canonical Adapters -/

section SharedHelpers

theorem m5_fullMem_of_eq {c : FullCfg} {s1 s2 : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} (hm : (FullMem c s1 ⋆ R) m) (hc : s1.core = s2.core)
    (hs : s1.scratch = s2.scratch) : (FullMem c s2 ⋆ R) m := by
  cases s1; cases s2; cases hc; cases hs; exact hm

theorem m5_otfs_opaque_state {c : FullCfg} {s_old : FullState} (k_new : FullCoreState)
    (sc_new : FullScratch) {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem c s_old ⋆ R) m) (hc : s_old.core = k_new) (hs : s_old.scratch = sc_new) :
    ∃ s_new : FullState,
      s_new.core = k_new ∧ s_new.scratch = sc_new ∧ (FullMem c s_new ⋆ R) m :=
  ⟨{ core := k_new, scratch := sc_new }, rfl, rfl, m5_fullMem_of_eq hm hc hs⟩

theorem m5_unwatch_fin_mem {c : FullCfg} {sL s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} {ws0 ws1 ws2 ws3 wv1 wv2 : List (BitVec 32)} {wu1 wu2 : BitVec 64}
    (hm : (FullMem c
      { { { { sL with core := { sL.core with wstk := ws1 } } with
          core := { { sL with core := { sL.core with wstk := ws1 } }.core with wstk := ws2 } } with
          core := { { { sL with core := { sL.core with wstk := ws1 } } with
            core := { { sL with core := { sL.core with wstk := ws1 } }.core with
              wstk := ws2 } }.core with wvec := wv1 } } with
          core := { { { { sL with core := { sL.core with wstk := ws1 } } with
            core := { { sL with core := { sL.core with wstk := ws1 } }.core with
              wstk := ws2 } } with
            core := { { { sL with core := { sL.core with wstk := ws1 } } with
              core := { { sL with core := { sL.core with wstk := ws1 } }.core with
                wstk := ws2 } }.core with wvec := wv1 } }.core with wusable := wu1 } } ⋆ R) m)
    (hk : sL.core = { s.core with wstk := ws0 }) (hsc : sL.scratch = s.scratch)
    (hws : ws2 = ws3) (hwv : wv1 = wv2) (hwu : wu1 = wu2) :
    (FullMem c { s with core := { s.core with wvec := wv2, wstk := ws3, wusable := wu2 } } ⋆ R) m :=
  m5_fullMem_of_eq hm (by
    cases sL with
    | mk cL scL => dsimp only at hk hsc ⊢; subst hk hws hwv hwu; rfl) hsc

theorem m5_bv32_lt_highbit_iff (r : BitVec 32) :
    r.toNat < 0x80000000 ↔ (r &&& 0x80000000#32) = 0#32 :=
  Full.FullReduceHelpers.bv32_lt_highbit_iff r

theorem m5_bv64_shl1_nat (x : BitVec 64) (h : 2 * x.toNat < 2 ^ 64) :
    (x <<< (1 : Nat)).toNat = 2 * x.toNat := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; simp only [Nat.pow_one]; omega

theorem m5_bv64_add1_nat (x : BitVec 64) (h : x.toNat + 1 < 2 ^ 64) :
    (x + (1 : BitVec 64)).toNat = x.toNat + 1 := by
  rw [BitVec.toNat_add, show (1 : BitVec 64).toNat = 1 from rfl]
  exact Nat.mod_eq_of_lt h

theorem m5_bv32_ofNat_add1 (n : Nat) :
    BitVec.ofNat 32 n + (1 : BitVec 32) = BitVec.ofNat 32 (n + 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    show (1 : BitVec 32).toNat = 1 from rfl, Nat.mod_add_mod]

theorem m5_list_getElem_of_idx {α : Type _} {xs : List α} {i j : Nat}
    {hi : i < xs.length} {hj : j < xs.length} (h : i = j) :
    xs[i]'hi = xs[j]'hj := by
  subst h; rfl

theorem m5_list_getElem_of_list_idx {α : Type} {xs ys : List α} {i j : Nat}
    {hi : i < xs.length} {hj : j < ys.length} (hl : xs = ys) (hij : i = j) :
    xs[i]'hi = ys[j]'hj := by
  subst hl; subst hij; rfl

theorem m5_bv32_lshr31_cases (w : BitVec 32) :
    ((w &&& 0x80000000#32) = 0#32 → (w >>> 31#32).toNat = 0) ∧
    ((w &&& 0x80000000#32) ≠ 0#32 → (w >>> 31#32).toNat = 1) ∧
    (w >>> 31#32).toNat ≤ 1 := by
  have hw := w.isLt
  have hsh : (w >>> 31#32).toNat = w.toNat / 2 ^ 31 := by
    simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hiff := m5_bv32_lt_highbit_iff w
  refine ⟨fun h0 => ?_, fun hne => ?_, ?_⟩
  · have hlt := hiff.mpr h0; rw [hsh]; omega
  · have hge : ¬ w.toNat < 0x80000000 := fun hlt => hne (hiff.mp hlt)
    rw [hsh]; omega
  · rw [hsh]; omega

theorem m5_bv32_lshr31_nat_cases (w : BitVec 32) :
    ((w &&& 0x80000000#32) = 0#32 → (w >>> (31 : Nat)).toNat = 0) ∧
    ((w &&& 0x80000000#32) ≠ 0#32 → (w >>> (31 : Nat)).toNat = 1) ∧
    (w >>> (31 : Nat)).toNat ≤ 1 := by
  simpa [BitVec.ushiftRight_eq'] using m5_bv32_lshr31_cases w

theorem m5_watchSlice_split_last {F_cur : List (List Nat)} {k : FullCoreState}
    {lit p len : Nat} (h : WatchSliceOk F_cur k lit p len) (hlen : 0 < len) :
    (∃ w0, k.wstk[p + len - 1]? = some w0 ∧ (w0 &&& 0x80000000#32) ≠ 0#32 ∧
      w0 ≠ 0xFFFFFFFF#32 ∧ (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k.cur_vars ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause [lit, (w0 &&& 0x7FFFFFFF#32).toNat]) ∧
      WatchSliceOk F_cur k lit p (len - 1)) ∨
    (2 ≤ len ∧ ∃ w0 cr, k.wstk[p + len - 2]? = some w0 ∧ k.wstk[p + len - 1]? = some cr ∧
      (w0 &&& 0x80000000#32) = 0#32 ∧ cr.toNat < 0x80000000 ∧
      cr.toNat ∈ fullArenaClauseRefsCore k ∧ WatchSliceOk F_cur k lit p (len - 2)) := by
  induction h with
  | empty => omega
  | @bin p rem w0 hp hflag hne hlt hent hrest ih =>
    cases rem with
    | zero => exact Or.inl ⟨w0, by simpa using hp, hflag, hne, hlt, hent, .empty⟩
    | succ r =>
      rcases ih (Nat.succ_pos r) with
        ⟨w', hw', hf', hne', hlt', hent', hpre⟩ |
        ⟨h2, w', cr', hw', hcr', hf', hlt', href', hpre⟩
      · refine Or.inl ⟨w', by simpa [show p + 1 + (r + 1) - 1 = p + (r + 1 + 1) - 1 by omega]
            using hw', hf', hne', hlt', hent', ?_⟩
        rw [show r + 1 + 1 - 1 = r + 1 by omega]
        exact .bin hp hflag hne hlt hent (by simpa using hpre)
      · refine Or.inr ⟨by omega, w', cr',
          by simpa [show p + 1 + (r + 1) - 2 = p + (r + 1 + 1) - 2 by omega] using hw',
          by simpa [show p + 1 + (r + 1) - 1 = p + (r + 1 + 1) - 1 by omega] using hcr',
          hf', hlt', href', ?_⟩
        rw [show r + 1 + 1 - 2 = (r - 1) + 1 by omega]
        exact .bin hp hflag hne hlt hent (by simpa [show r + 1 - 2 = r - 1 by omega] using hpre)
  | @large p rem w0 cr hp hp1 hflag hlt href hrest ih =>
    cases rem with
    | zero =>
      exact Or.inr ⟨Nat.le_refl 2, w0, cr, by simpa using hp, by simpa using hp1,
        hflag, hlt, href, .empty⟩
    | succ r =>
      rcases ih (Nat.succ_pos r) with
        ⟨w', hw', hf', hne', hlt', hent', hpre⟩ |
        ⟨h2, w', cr', hw', hcr', hf', hlt', href', hpre⟩
      · refine Or.inl ⟨w', by simpa [show p + 2 + (r + 1) - 1 = p + (r + 1 + 2) - 1 by omega]
            using hw', hf', hne', hlt', hent', ?_⟩
        rw [show r + 1 + 2 - 1 = r + 2 by omega]
        exact .large hp hp1 hflag hlt href (by simpa using hpre)
      · refine Or.inr ⟨by omega, w', cr',
          by simpa [show p + 2 + (r + 1) - 2 = p + (r + 1 + 2) - 2 by omega] using hw',
          by simpa [show p + 2 + (r + 1) - 1 = p + (r + 1 + 2) - 1 by omega] using hcr',
          hf', hlt', href', ?_⟩
        rw [show r + 1 + 2 - 2 = (r - 1) + 2 by omega]
        exact .large hp hp1 hflag hlt href (by simpa [show r + 1 - 2 = r - 1 by omega] using hpre)

theorem m5_denseWatchSlice_split_last {F_cur : List (List Nat)} {k : FullCoreState}
    {lit p len : Nat} (h : DenseWatchSliceOk F_cur k lit p len) (hlen : 0 < len) :
    (∃ w0, k.wstk[p + len - 1]? = some w0 ∧ (w0 &&& 0x80000000#32) ≠ 0#32 ∧
      w0 ≠ 0xFFFFFFFF#32 ∧ (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k.cur_vars ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause [lit, (w0 &&& 0x7FFFFFFF#32).toNat]) ∧
      DenseWatchSliceOk F_cur k lit p (len - 1)) ∨
    (2 ≤ len ∧ ∃ w0 cr, k.wstk[p + len - 2]? = some w0 ∧ k.wstk[p + len - 1]? = some cr ∧
      (w0 &&& 0x80000000#32) = 0#32 ∧ 3 ≤ w0.toNat ∧ cr.toNat < 0x80000000 ∧
      cr.toNat ∈ fullArenaClauseRefsCore k ∧ DenseWatchSliceOk F_cur k lit p (len - 2)) := by
  induction h with
  | empty => omega
  | @bin p rem w0 hp hflag hne hlt hent hrest ih =>
    cases rem with
    | zero => exact Or.inl ⟨w0, by simpa using hp, hflag, hne, hlt, hent, .empty⟩
    | succ r =>
      rcases ih (Nat.succ_pos r) with
        ⟨w', hw', hf', hne', hlt', hent', hpre⟩ |
        ⟨h2, w', cr', hw', hcr', hf', hsz', hlt', href', hpre⟩
      · refine Or.inl ⟨w', by simpa [show p + 1 + (r + 1) - 1 = p + (r + 1 + 1) - 1 by omega]
            using hw', hf', hne', hlt', hent', ?_⟩
        rw [show r + 1 + 1 - 1 = r + 1 by omega]
        exact .bin hp hflag hne hlt hent (by simpa using hpre)
      · refine Or.inr ⟨by omega, w', cr',
          by simpa [show p + 1 + (r + 1) - 2 = p + (r + 1 + 1) - 2 by omega] using hw',
          by simpa [show p + 1 + (r + 1) - 1 = p + (r + 1 + 1) - 1 by omega] using hcr',
          hf', hsz', hlt', href', ?_⟩
        rw [show r + 1 + 1 - 2 = (r - 1) + 1 by omega]
        exact .bin hp hflag hne hlt hent (by simpa [show r + 1 - 2 = r - 1 by omega] using hpre)
  | @occ p rem w0 cr hp hp1 hflag hsz hlt href hrest ih =>
    cases rem with
    | zero =>
      exact Or.inr ⟨Nat.le_refl 2, w0, cr, by simpa using hp, by simpa using hp1,
        hflag, hsz, hlt, href, .empty⟩
    | succ r =>
      rcases ih (Nat.succ_pos r) with
        ⟨w', hw', hf', hne', hlt', hent', hpre⟩ |
        ⟨h2, w', cr', hw', hcr', hf', hsz', hlt', href', hpre⟩
      · refine Or.inl ⟨w', by simpa [show p + 2 + (r + 1) - 1 = p + (r + 1 + 2) - 1 by omega]
            using hw', hf', hne', hlt', hent', ?_⟩
        rw [show r + 1 + 2 - 1 = r + 2 by omega]
        exact .occ hp hp1 hflag hsz hlt href (by simpa using hpre)
      · refine Or.inr ⟨by omega, w', cr',
          by simpa [show p + 2 + (r + 1) - 2 = p + (r + 1 + 2) - 2 by omega] using hw',
          by simpa [show p + 2 + (r + 1) - 1 = p + (r + 1 + 2) - 1 by omega] using hcr',
          hf', hsz', hlt', href', ?_⟩
        rw [show r + 1 + 2 - 2 = (r - 1) + 2 by omega]
        exact .occ hp hp1 hflag hsz hlt href
          (by simpa [show r + 1 - 2 = r - 1 by omega] using hpre)

theorem m5_modeWatchSlice_split_last {dense : Bool} {F_cur : List (List Nat)}
    {k : FullCoreState} {lit p len : Nat}
    (h : Full.FullReduceSpecs.ModeWatchSliceOk dense F_cur k lit p len) (hlen : 0 < len) :
    (∃ w0, k.wstk[p + len - 1]? = some w0 ∧ (w0 &&& 0x80000000#32) ≠ 0#32 ∧
      w0 ≠ 0xFFFFFFFF#32 ∧ (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k.cur_vars ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause [lit, (w0 &&& 0x7FFFFFFF#32).toNat]) ∧
      Full.FullReduceSpecs.ModeWatchSliceOk dense F_cur k lit p (len - 1)) ∨
    (2 ≤ len ∧ ∃ w0 cr, k.wstk[p + len - 2]? = some w0 ∧ k.wstk[p + len - 1]? = some cr ∧
      (w0 &&& 0x80000000#32) = 0#32 ∧ (dense = true → 3 ≤ w0.toNat) ∧
      cr.toNat < 0x80000000 ∧ cr.toNat ∈ fullArenaClauseRefsCore k ∧
      Full.FullReduceSpecs.ModeWatchSliceOk dense F_cur k lit p (len - 2)) := by
  cases dense <;>
    simp only [Full.FullReduceSpecs.ModeWatchSliceOk, Bool.false_eq_true, ↓reduceIte] at h ⊢
  · rcases m5_watchSlice_split_last h hlen with hbin | ⟨h2, w0, cr, hw0, hcr, hf, hlt, href, hpre⟩
    · exact Or.inl hbin
    · exact Or.inr ⟨h2, w0, cr, hw0, hcr, hf, fun hc => False.elim hc, hlt, href, hpre⟩
  · rcases m5_denseWatchSlice_split_last h hlen with
      hbin | ⟨h2, w0, cr, hw0, hcr, hf, hsz, hlt, href, hpre⟩
    · exact Or.inl hbin
    · exact Or.inr ⟨h2, w0, cr, hw0, hcr, hf, fun _ => hsz, hlt, href, hpre⟩

theorem m5_watchSlice_append {F_cur : List (List Nat)} {k : FullCoreState}
    {lit p len1 len2 : Nat}
    (h1 : WatchSliceOk F_cur k lit p len1) (h2 : WatchSliceOk F_cur k lit (p + len1) len2) :
    WatchSliceOk F_cur k lit p (len1 + len2) := by
  induction h1 with
  | empty => simpa using h2
  | @bin p rem w0 hp hflag hne hlt hent _ ih =>
    rw [show rem + 1 + len2 = (rem + len2) + 1 by omega]
    exact .bin hp hflag hne hlt hent (ih (by simpa [show p + 1 + rem = p + (rem + 1) by omega]
      using h2))
  | @large p rem w0 cr hp hp1 hflag hlt href _ ih =>
    rw [show rem + 2 + len2 = (rem + len2) + 2 by omega]
    exact .large hp hp1 hflag hlt href (ih (by simpa [show p + 2 + rem = p + (rem + 2) by omega]
      using h2))

theorem m5_denseWatchSlice_append {F_cur : List (List Nat)} {k : FullCoreState}
    {lit p len1 len2 : Nat}
    (h1 : DenseWatchSliceOk F_cur k lit p len1)
    (h2 : DenseWatchSliceOk F_cur k lit (p + len1) len2) :
    DenseWatchSliceOk F_cur k lit p (len1 + len2) := by
  induction h1 with
  | empty => simpa using h2
  | @bin p rem w0 hp hflag hne hlt hent _ ih =>
    rw [show rem + 1 + len2 = (rem + len2) + 1 by omega]
    exact .bin hp hflag hne hlt hent (ih (by simpa [show p + 1 + rem = p + (rem + 1) by omega]
      using h2))
  | @occ p rem w0 cr hp hp1 hflag hsz hlt href _ ih =>
    rw [show rem + 2 + len2 = (rem + len2) + 2 by omega]
    exact .occ hp hp1 hflag hsz hlt href (ih (by simpa [show p + 2 + rem = p + (rem + 2) by omega]
      using h2))

theorem m5_modeWatchSlice_append {dense : Bool} {F_cur : List (List Nat)}
    {k : FullCoreState} {lit p len1 len2 : Nat}
    (h1 : Full.FullReduceSpecs.ModeWatchSliceOk dense F_cur k lit p len1)
    (h2 : Full.FullReduceSpecs.ModeWatchSliceOk dense F_cur k lit (p + len1) len2) :
    Full.FullReduceSpecs.ModeWatchSliceOk dense F_cur k lit p (len1 + len2) := by
  cases dense <;>
    simp only [Full.FullReduceSpecs.ModeWatchSliceOk, Bool.false_eq_true, ↓reduceIte] at h1 h2 ⊢
  · exact m5_watchSlice_append h1 h2
  · exact m5_denseWatchSlice_append h1 h2

theorem m5_modeWatchSlice_cons_bin {dense : Bool} {F_cur : List (List Nat)}
    {k : FullCoreState} {lit p rem : Nat} {w0 : BitVec 32}
    (hp : k.wstk[p]? = some w0) (hflag : (w0 &&& 0x80000000#32) ≠ 0#32) (hne : w0 ≠ 0xFFFFFFFF#32)
    (hlt : (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k.cur_vars)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [lit, (w0 &&& 0x7FFFFFFF#32).toNat]))
    (hrest : Full.FullReduceSpecs.ModeWatchSliceOk dense F_cur k lit (p + 1) rem) :
    Full.FullReduceSpecs.ModeWatchSliceOk dense F_cur k lit p (rem + 1) := by
  cases dense <;>
    simp only [Full.FullReduceSpecs.ModeWatchSliceOk, Bool.false_eq_true, ↓reduceIte] at hrest ⊢
  · exact .bin hp hflag hne hlt hent hrest
  · exact .bin hp hflag hne hlt hent hrest

theorem m5_modeWatchSlice_cons_pair {dense : Bool} {F_cur : List (List Nat)}
    {k : FullCoreState} {lit p rem : Nat} {w0 cr : BitVec 32}
    (hp : k.wstk[p]? = some w0) (hp1 : k.wstk[p + 1]? = some cr)
    (hflag : (w0 &&& 0x80000000#32) = 0#32) (hsz : dense = true → 3 ≤ w0.toNat)
    (hlt : cr.toNat < 0x80000000) (href : cr.toNat ∈ fullArenaClauseRefsCore k)
    (hrest : Full.FullReduceSpecs.ModeWatchSliceOk dense F_cur k lit (p + 2) rem) :
    Full.FullReduceSpecs.ModeWatchSliceOk dense F_cur k lit p (rem + 2) := by
  cases dense <;>
    simp only [Full.FullReduceSpecs.ModeWatchSliceOk, Bool.false_eq_true, ↓reduceIte] at hrest ⊢
  · exact .large hp hp1 hflag hlt href hrest
  · exact .occ hp hp1 hflag (hsz rfl) hlt href hrest

theorem m5_otfsActCnt_mono {k : FullCoreState} {cref : Nat} :
    ∀ {i j : Nat}, 2 ≤ i → i ≤ j → Full.otfsActCnt k cref i ≤ Full.otfsActCnt k cref j := by
  intro i j hi hij
  induction hij with
  | refl => exact Nat.le_refl _
  | @step m hm ih =>
    rw [Full.otfsActCnt_succ (Nat.le_trans hi hm)]
    omega

theorem m5_otfs_bv_idx3_64 (cref : BitVec 32) (k : Nat) (hbd : cref.toNat + 3 + k < 2 ^ 32)
    (hk : k < 2 ^ 32) :
    (cref.setWidth 64 + 3#64 + (BitVec.ofNat 32 k).setWidth 64).toNat = cref.toNat + 3 + k := by
  have hz1 : (cref.setWidth 64).toNat = cref.toNat := zext_toNat cref (by decide)
  have hz2 : ((BitVec.ofNat 32 k).setWidth 64).toNat = k := by
    rw [zext_toNat _ (by decide), bv32_ofNat_toNat hk]
  bv_omega

theorem m5_canonCut_to_anaCut {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {k : FullCoreState} (h : FullWitnessCutInv c F0 F_cur cut k) :
    Full.FullAnalyzeSpecs.FullWitnessCutInv c F0 F_cur cut k :=
  ⟨h.ext_sound, h.inconsistent_sound, h.arena, h.watches, h.cur_level_le, h.trail_lits_lt,
    h.trail_vars_nodup, h.vals_domain, h.vals_true_iff, h.vals_false_iff, h.lvl_le, h.dec_earliest,
    h.levels_inhabited, h.level0_sound, h.trail_pos_inv, h.level0_rsn_none, h.frame_trail_lt,
    h.frame_trail_mono, h.frame_trail_before_lt, h.frame_dec_lt,
    fun idx hi hcond hne =>
      hcond.elim (fun hc => h.reason_inv_cut idx hc hne)
        (fun hlt => h.reason_inv_below idx hi hlt hne),
    fun idx hi hcond hne hlg =>
      hcond.elim (fun hc => h.reason_lit_mem_cut idx hc hne hlg)
        (fun hlt => h.reason_lit_mem_below idx hi hlt hne hlg)⟩

theorem m5_anaCut_to_canonCut {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {k : FullCoreState} (h : Full.FullAnalyzeSpecs.FullWitnessCutInv c F0 F_cur cut k)
    (hcut : cut ≤ k.trail_end) : FullWitnessCutInv c F0 F_cur cut k :=
  ⟨⟨h.ext_sound, h.inconsistent_sound, h.arena, h.watches, h.cur_level_le, h.trail_lits_lt,
    h.trail_vars_nodup, h.vals_domain, h.vals_true_iff, h.vals_false_iff, h.lvl_le, h.dec_earliest,
    h.levels_inhabited, h.level0_sound, h.trail_pos_inv, h.level0_rsn_none, h.frame_trail_lt,
    h.frame_trail_mono, h.frame_trail_before_lt, h.frame_dec_lt,
    fun idx hi hlt hne => h.reason_inv idx hi (Or.inr hlt) hne,
    fun idx hi hlt hne hlg => h.reason_lit_mem idx hi (Or.inr hlt) hne hlg⟩,
    hcut,
    fun idx hc hne => h.reason_inv idx (Nat.lt_of_lt_of_le hc hcut) (Or.inl hc) hne,
    fun idx hc hne hlg => h.reason_lit_mem idx (Nat.lt_of_lt_of_le hc hcut) (Or.inl hc) hne hlg⟩

theorem m5_anaWatchPush_adapter {Γ : Env}
    (hPush : ∀ a m Q X, Full.fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, Full.FullAnalyzeSpecs.fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X := by
  rintro ⟨h, lit, w0, w1, cnt, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hlay, hc1, hc2, hm, hQ⟩
  refine hPush _ m Q X ⟨c, s, R, rfl, hlen, hlay, hc1, hc2, hm,
    fun ok wv ws wl wu wso m' hlen' hlay' hoth hT hF hm' => ?_⟩
  refine hQ ok wv ws wl wu wso m' hlen' hlay' hoth hT (fun hf => ?_) hm'
  obtain ⟨hpres, hwhy⟩ := hF hf
  refine ⟨hpres, ?_⟩
  rcases hwhy with hlt | hcnt | hsame | hw0
  · exact Or.inl (by omega)
  · exact Or.inr (Or.inl hcnt)
  · exact Or.inr (Or.inr (Or.inl (congrArg FullState.core hsame)))
  · exact Or.inr (Or.inr (Or.inr hw0))

theorem m5_canonCut_shrink_cut {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut cut' : Nat} {k : FullCoreState} (h : FullWitnessCutInv c F0 F_cur cut k)
    (hle : cut' ≤ cut) : FullWitnessCutInv c F0 F_cur cut' k :=
  m5_anaCut_to_canonCut ((m5_canonCut_to_anaCut h).shrink_cut hle) (Nat.le_trans hle h.cut_le)

theorem m5_canonCut_with_watches {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {k : FullCoreState} (h : FullWitnessCutInv c F0 F_cur cut k)
    {wvec' wstk' : List (BitVec 32)} {wlen' : Nat} {wu' : BitVec 64}
    (hw : ModeWatchesInv F_cur
      { k with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' }) :
    FullWitnessCutInv c F0 F_cur cut
      { k with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' } :=
  m5_anaCut_to_canonCut ((m5_canonCut_to_anaCut h).with_watches hw) h.cut_le

theorem m5_canonCut_with_oom {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {k : FullCoreState} (h : FullWitnessCutInv c F0 F_cur cut k)
    (oom' : BitVec 64) : FullWitnessCutInv c F0 F_cur cut { k with oom := oom' } :=
  m5_anaCut_to_canonCut ((m5_canonCut_to_anaCut h).with_oom oom') h.cut_le

end SharedHelpers

/-! ## 2. `full_unwatch_large_wp` (`Full.fullUnwatchLargeSpec`) -/

section UnwatchLargeProof

open Full.FullReduceSpecs Full.FullReduceHelpers
open scoped Full.FullReduceTactics

private theorem m5_unwatch_step_ok {dense : Bool} {k : FullCoreState} {lit off0 end0 : Nat}
    {p : BitVec 64} {w : BitVec 32}
    (hp_ge2 : off0 + 2 ≤ p.toNat) (hpe : p.toNat ≤ end0) (_hend : end0 < 2 ^ 64)
    (hw_some : k.wstk[p.toNat - 1]? = some w)
    (hinv : ∀ F_cur, ModeWatchesInv F_cur k →
      ModeWatchSliceOk dense F_cur k lit off0 (p.toNat - off0) ∧
      ModeWatchSliceOk dense F_cur k lit p.toNat (end0 - p.toNat)) :
    let p' := p - 2#64 + (w >>> (31 : Nat)).setWidth 64
    p'.toNat - off0 < p.toNat - off0 ∧ off0 ≤ p'.toNat ∧ p'.toNat ≤ end0 ∧
    ∀ F_cur, ModeWatchesInv F_cur k →
      ModeWatchSliceOk dense F_cur k lit off0 (p'.toNat - off0) ∧
      ModeWatchSliceOk dense F_cur k lit p'.toNat (end0 - p'.toNat) := by
  intro p'
  have hp2_toNat : (p - 2#64).toNat = p.toNat - 2 := by bv_omega
  have hsh_le := (m5_bv32_lshr31_nat_cases w).2.2
  have hp'_toNat : p'.toNat = p.toNat - 2 + (w >>> (31 : Nat)).toNat := by
    dsimp only [p']; rw [BitVec.toNat_add, hp2_toNat, zext_toNat _ (by decide)]
    exact Nat.mod_eq_of_lt (by omega)
  refine ⟨by omega, by omega, by omega, fun F_cur hmw => ?_⟩
  obtain ⟨hpre, hsuf⟩ := hinv F_cur hmw
  rcases m5_modeWatchSlice_split_last hpre (by omega) with
    ⟨w0, hw0, hfl0, hne0, hlt0, hent0, hpre1⟩ |
    ⟨_, w0, cr, hw0, hcr, hfl0, hsz0, hlt0, href0, hpre2⟩
  · rw [show off0 + (p.toNat - off0) - 1 = p.toNat - 1 by omega, hw_some] at hw0
    cases hw0
    have hsh1 := (m5_bv32_lshr31_nat_cases w).2.1 hfl0
    have hp'_eq : p'.toNat = p.toNat - 1 := by rw [hp'_toNat, hsh1]; omega
    rw [hp'_eq, show p.toNat - 1 - off0 = p.toNat - off0 - 1 by omega,
      show end0 - (p.toNat - 1) = (end0 - p.toNat) + 1 by omega]
    exact ⟨hpre1, m5_modeWatchSlice_cons_bin hw_some hfl0 hne0 hlt0 hent0
      (by simpa only [show p.toNat - 1 + 1 = p.toNat by omega] using hsuf)⟩
  · rw [show off0 + (p.toNat - off0) - 1 = p.toNat - 1 by omega, hw_some] at hcr
    cases hcr
    have hcr_msb0 : (w &&& 0x80000000#32) = 0#32 := (m5_bv32_lt_highbit_iff w).mp hlt0
    have hsh0 := (m5_bv32_lshr31_nat_cases w).1 hcr_msb0
    have hp'_eq : p'.toNat = p.toNat - 2 := by rw [hp'_toNat, hsh0]; omega
    rw [hp'_eq, show p.toNat - 2 - off0 = p.toNat - off0 - 2 by omega,
      show end0 - (p.toNat - 2) = (end0 - p.toNat) + 2 by omega]
    rw [show off0 + (p.toNat - off0) - 2 = p.toNat - 2 by omega] at hw0
    exact ⟨hpre2, m5_modeWatchSlice_cons_pair hw0
      (by simpa only [show p.toNat - 2 + 1 = p.toNat - 1 by omega] using hw_some)
      hfl0 hsz0 hlt0 href0 (by simpa only [show p.toNat - 2 + 2 = p.toNat by omega] using hsuf)⟩

private theorem m5_unwatch_fin_inv {dense : Bool} {c : FullCfg} {k : FullCoreState}
    {wstk1 : List (BitVec 32)} {lit p_nat : Nat}
    (hdense : dense = decide (k.dense_mode ≠ 0#64))
    (hlen : k.LengthsOk c) (hlay : WatchStackLayout k) (hlit : lit < 2 * k.cur_vars)
    (hsz2 : 2 ≤ fullWatchSizeCore k lit)
    (hp_ge2 : fullWatchOffCore k lit + 2 ≤ p_nat)
    (hpe : p_nat ≤ fullWatchOffCore k lit + fullWatchSizeCore k lit)
    (hout1 : ∀ i, i < p_nat - 2 ∨ fullWatchOffCore k lit + fullWatchSizeCore k lit - 2 ≤ i →
      wstk1[i]? = k.wstk[i]?)
    (hsh1 : ∀ j, j < fullWatchOffCore k lit + fullWatchSizeCore k lit - p_nat →
      wstk1[(p_nat - 2) + j]? = k.wstk[p_nat + j]?)
    (hinv_found : ∀ F_cur, ModeWatchesInv F_cur k →
      ModeWatchSliceOk dense F_cur k lit (fullWatchOffCore k lit)
        (p_nat - 2 - fullWatchOffCore k lit) ∧
      ModeWatchSliceOk dense F_cur k lit p_nat
        (fullWatchOffCore k lit + fullWatchSizeCore k lit - p_nat)) :
    let off0 := fullWatchOffCore k lit
    let sz0 := fullWatchSizeCore k lit
    let end0 := off0 + sz0
    let wstk2 := (wstk1.set (end0 - 2) 0xFFFFFFFF#32).set (end0 - 1) 0xFFFFFFFF#32
    let wvec' := k.wvec.set (2 * lit + 1) (BitVec.ofNat 32 (sz0 - 2))
    let wu' := k.wusable + 2#64
    WatchStackLayout { k with wvec := wvec', wstk := wstk2, wusable := wu' } ∧
    ∀ F_cur, ModeWatchesInv F_cur k →
      ModeWatchesInv F_cur { k with wvec := wvec', wstk := wstk2, wusable := wu' } := by
  intro off0 sz0 end0 wstk2 wvec' wu'
  have hout_fin : ∀ i, i < off0 ∨ off0 + sz0 ≤ i → wstk2[i]? = k.wstk[i]? := fun i hi => by
    dsimp only [wstk2]
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
    exact hout1 i (by omega)
  have hpre_fin : ∀ j < p_nat - 2 - off0, wstk2[off0 + j]? = k.wstk[off0 + j]? := fun j hj => by
    dsimp only [wstk2]
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
    exact hout1 (off0 + j) (Or.inl (by omega))
  have hsuf_fin : ∀ j < end0 - p_nat, wstk2[(p_nat - 2) + j]? = k.wstk[p_nat + j]? := fun j hj => by
    dsimp only [wstk2]
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
    exact hsh1 j (by omega)
  have hns_fin : ∀ j < sz0 - 2, wstk2[off0 + j]? ≠ some 0xFFFFFFFF#32 := by
    intro j hj
    by_cases hjp : j < p_nat - 2 - off0
    · rw [hpre_fin j hjp]; exact hlay.no_sentinel lit hlit j (by omega)
    · have hj' : j - (p_nat - 2 - off0) < end0 - p_nat := by omega
      have heq := hsuf_fin (j - (p_nat - 2 - off0)) hj'
      rw [show p_nat - 2 + (j - (p_nat - 2 - off0)) = off0 + j by omega,
        show p_nat + (j - (p_nat - 2 - off0)) = off0 + (j + 2) by omega] at heq
      rw [heq]; exact hlay.no_sentinel lit hlit (j + 2) (by omega)
  refine ⟨(watchStackLayout_shrink_slice hlay hlen hlit (new_sz := sz0 - 2) (by omega) hout_fin
      hns_fin wu' k.num_binary).1, fun F_cur hmw => ?_⟩
  obtain ⟨hpre_ok, hsuf_ok⟩ := hinv_found F_cur hmw
  have hF_refl : (cnfOfClauses F_cur).Entails (cnfOfClauses F_cur) := by
    rw [CNF.entails_def]; exact fun _ hx => hx
  have hpre_w2 : ModeWatchSliceOk dense F_cur { k with wstk := wstk2 } lit off0
      (p_nat - 2 - off0) :=
    ModeWatchSliceOk.relocate (k := k) (k' := { k with wstk := wstk2 }) (p := off0) (p' := off0)
      hF_refl (Nat.le_refl _) (fun _ hr => hr) hpre_fin hpre_ok
  have hsuf_w2 : ModeWatchSliceOk dense F_cur { k with wstk := wstk2 } lit
      (off0 + (p_nat - 2 - off0)) (end0 - p_nat) :=
    ModeWatchSliceOk.relocate (k := k) (k' := { k with wstk := wstk2 }) (p := p_nat)
      (p' := off0 + (p_nat - 2 - off0)) hF_refl (Nat.le_refl _) (fun _ hr => hr)
      (fun j hj => by
        rw [show off0 + (p_nat - 2 - off0) + j = (p_nat - 2) + j by omega]
        exact hsuf_fin j hj) hsuf_ok
  have hslice_w2 : ModeWatchSliceOk dense F_cur { k with wstk := wstk2 } lit off0 (sz0 - 2) := by
    have happ := m5_modeWatchSlice_append hpre_w2 hsuf_w2
    rwa [show p_nat - 2 - off0 + (end0 - p_nat) = sz0 - 2 by omega] at happ
  subst hdense
  exact modeWatchesInv_shrink_slice hmw hlen hlit (new_sz := sz0 - 2) (by omega) hout_fin wu'
    k.num_binary hslice_w2

theorem full_unwatch_large_wp (Γ : Env) :
    ∀ a m Q X, Full.fullUnwatchLargeSpec a m Q X →
      Func.wp Γ full_unwatch_large_body a m Q X := by
  rintro ⟨h, lit, cref, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hlay, hm, hQ⟩
  have hcv_le := hlen.core_ok.cur_vars_le
  have hwv_len := hlen.core_ok.wvec_len
  have hws_len := hlen.core_ok.wstk_len_arr
  have hwl_le := hlen.core_ok.wlen_le
  have hmax_lt : c.max_vars < 2 * 2 ^ 28 := c.hmaxv
  have hwcap_lt : c.wcap < 2 * 2 ^ 28 := c.hwcap
  have hret_same : Q () m :=
    hQ s.core.wvec s.core.wstk s.core.wusable m hlen hlay (fun _ h => h) hm
  let dense : Bool := decide (s.core.dense_mode ≠ 0#64)
  have hnlits_eq :
      ((BitVec.ofNat 64 s.core.cur_vars) <<< (1 : Nat)).toNat = 2 * s.core.cur_vars := by
    have h1 : (BitVec.ofNat 64 s.core.cur_vars).toNat = s.core.cur_vars := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [m5_bv64_shl1_nat _ (by omega), h1]
  unfold Func.wp full_unwatch_large_body
  c0_hsteps_nogrp
  · exact hret_same
  · exact hret_same
  · exact hret_same
  · have hlit_lt : lit.toNat < 2 * s.core.cur_vars := by
      have h1 : ¬ ((BitVec.ofNat 64 s.core.cur_vars) <<< (1 : Nat)).toNat ≤
          (lit.setWidth 64).toNat := by c0_bound
      rw [hnlits_eq, zext_toNat lit (by decide)] at h1; omega
    have hcr_msb : (cref &&& 0x80000000#32) = 0#32 := by assumption
    have h2l_eq : ((lit.setWidth 64) <<< (1 : Nat)).toNat = 2 * lit.toNat := by
      have h1 : (lit.setWidth 64).toNat = lit.toNat := zext_toNat lit (by decide)
      rw [m5_bv64_shl1_nat _ (by omega), h1]
    have h2l1_eq : (((lit.setWidth 64) <<< (1 : Nat)) + (1 : BitVec 64)).toNat =
        2 * lit.toNat + 1 := by
      rw [m5_bv64_add1_nat _ (by omega), h2l_eq]
    have h2l_lt : 2 * lit.toNat < s.core.wvec.length := by omega
    have h2l1_lt : 2 * lit.toNat + 1 < s.core.wvec.length := by omega
    let off0 : Nat := fullWatchOff s lit.toNat
    let sz0 : Nat := fullWatchSize s lit.toNat
    have hoff_idx : (s.core.wvec[2 * lit.toNat]'h2l_lt).toNat = off0 := by
      unfold off0 fullWatchOff fullWatchOffCore
      rw [List.getElem?_eq_getElem h2l_lt, Option.getD_some]
    have hsz_idx : (s.core.wvec[2 * lit.toNat + 1]'h2l1_lt).toNat = sz0 := by
      unfold sz0 fullWatchSize fullWatchSizeCore
      rw [List.getElem?_eq_getElem h2l1_lt, Option.getD_some]
    have hbd_end : off0 + sz0 ≤ s.core.wlen := hlay.bounds lit.toNat hlit_lt
    have hbd0_w : (lit.setWidth 64 <<< (1 : Nat)).toNat < s.core.wvec.length := by
      rw [h2l_eq]; exact h2l_lt
    have hbd1_w : ((lit.setWidth 64 <<< (1 : Nat)) + (1 : BitVec 64)).toNat <
        s.core.wvec.length := by rw [h2l1_eq]; exact h2l1_lt
    have hoff_w : (s.core.wvec[(lit.setWidth 64 <<< (1 : Nat)).toNat]'hbd0_w).toNat = off0 := by
      simpa only [h2l_eq] using hoff_idx
    have hsz_w :
        (s.core.wvec[((lit.setWidth 64 <<< (1 : Nat)) + (1 : BitVec 64)).toNat]'hbd1_w).toNat =
        sz0 := by simpa only [h2l1_eq] using hsz_idx
    have hsz2 : 2 ≤ sz0 := by
      have h1 : ¬ (s.core.wvec[((lit.setWidth 64 <<< (1 : Nat)) +
          (1 : BitVec 64)).toNat]'hbd1_w).toNat < 2 := by
        have hc' : ¬ (BitVec.setWidth 64
            (s.core.wvec[((lit.setWidth 64 <<< (1 : Nat)) +
              (1 : BitVec 64)).toNat]'hbd1_w)).toNat < (2#64).toNat := by
          c0_bound
        rwa [zext_toNat _ (by decide)] at hc'
      rw [hsz_w] at h1; omega
    let end0 : Nat := off0 + sz0
    have hoff64 : (BitVec.setWidth 64
        (s.core.wvec[(lit.setWidth 64 <<< (1 : Nat)).toNat]'hbd0_w)).toNat = off0 := by
      rw [zext_toNat _ (by decide), hoff_w]
    have hsz64 : (BitVec.setWidth 64
        (s.core.wvec[((lit.setWidth 64 <<< (1 : Nat)) +
          (1 : BitVec 64)).toNat]'hbd1_w)).toNat = sz0 := by
      rw [zext_toNat _ (by decide), hsz_w]
    have hend64 : (BitVec.setWidth 64
          (s.core.wvec[(lit.setWidth 64 <<< (1 : Nat)).toNat]'hbd0_w) +
        BitVec.setWidth 64
          (s.core.wvec[((lit.setWidth 64 <<< (1 : Nat)) +
            (1 : BitVec 64)).toNat]'hbd1_w)).toNat = end0 := by
      rw [BitVec.toNat_add, hoff64, hsz64]; exact Nat.mod_eq_of_lt (by omega)
    have hoff2_64 : (BitVec.setWidth 64
          (s.core.wvec[(lit.setWidth 64 <<< (1 : Nat)).toNat]'hbd0_w) + 2#64).toNat =
        off0 + 2 := by
      rw [BitVec.toNat_add, hoff64, show (2#64).toNat = 2 from rfl]
      exact Nat.mod_eq_of_lt (by omega)
    refine wp_loop_inv (ts := [i64])
      (fun (p, ()) m1 =>
        m1 = m ∧ off0 ≤ p.toNat ∧ p.toNat ≤ end0 ∧
        ∀ F_cur, ModeWatchesInv F_cur s.core →
          ModeWatchSliceOk dense F_cur s.core lit.toNat off0 (p.toNat - off0) ∧
          ModeWatchSliceOk dense F_cur s.core lit.toNat p.toNat (end0 - p.toNat))
      (fun (p, ()) _ => p.toNat - off0)
      (fun J1 hLoop1 => ?_) ?_
    · c0_hsteps
      refine hLoop1 _ m ⟨rfl, by rw [hend64]; omega, by rw [hend64]; exact Nat.le_refl _,
        fun F_cur hmw => ?_⟩
      rw [hend64, show end0 - off0 = sz0 by omega, Nat.sub_self]
      exact ⟨modeWatchesInv_slice_of_lt hmw hlit_lt, by
        cases dense <;> simp only [ModeWatchSliceOk, Bool.false_eq_true, ↓reduceIte]
        · exact .empty
        · exact .empty⟩
    · rintro J1 ⟨p, ⟨⟩⟩ m1 ⟨rfl, hop, hpe, hinv⟩ hLoop1
      c0_hsplit
      · have hp_ge2 : off0 + 2 ≤ p.toNat := by
          have hc' : (BitVec.setWidth 64
              (s.core.wvec[(lit.setWidth 64 <<< (1 : Nat)).toNat]'hbd0_w) + 2#64).toNat ≤
              p.toNat := by c0_bound
          rwa [hoff2_64] at hc'
        have hp1_toNat : (p - 1#64).toNat = p.toNat - 1 := by bv_omega
        have hp2_toNat : (p - 2#64).toNat = p.toNat - 2 := by bv_omega
        have hp1_lt : (p - 1#64).toNat < s.core.wstk.length := by rw [hp1_toNat]; omega
        let w : BitVec 32 := s.core.wstk[(p - 1#64).toNat]'hp1_lt
        have hw_some : s.core.wstk[p.toNat - 1]? = some w := by
          rw [List.getElem?_eq_getElem (by omega : p.toNat - 1 < s.core.wstk.length)]
          exact congrArg some (by dsimp only [w]; exact (m5_list_getElem_of_idx hp1_toNat).symm)
        c0_hsplit
        · have hw_eq : w = cref := by assumption
          have hinv_found : ∀ F_cur, ModeWatchesInv F_cur s.core →
              ModeWatchSliceOk dense F_cur s.core lit.toNat off0 (p.toNat - 2 - off0) ∧
              ModeWatchSliceOk dense F_cur s.core lit.toNat p.toNat (end0 - p.toNat) := by
            intro F_cur hmw
            obtain ⟨hpre, hsuf⟩ := hinv F_cur hmw
            rcases m5_modeWatchSlice_split_last hpre (by omega) with
              ⟨w0, hw0, hfl0, _⟩ | ⟨_, _, _, _, _, _, _, _, _, hpre2⟩
            · rw [show off0 + (p.toNat - off0) - 1 = p.toNat - 1 by omega, hw_some] at hw0
              cases hw0; rw [hw_eq] at hfl0; exact absurd hcr_msb hfl0
            · exact ⟨by simpa only [show p.toNat - off0 - 2 = p.toNat - 2 - off0 by omega]
                using hpre2, hsuf⟩
          c0_hsteps_nogrp
          refine wp_loop_inv (ts := [i64, i64])
            (fun (pc, qc, ()) m2 =>
              p.toNat ≤ pc.toNat ∧ pc.toNat ≤ end0 ∧ qc.toNat = pc.toNat - 2 ∧
              ∃ wstk1 : List (BitVec 32), wstk1.length = c.wcap ∧
                (∀ i, i < p.toNat - 2 ∨ pc.toNat - 2 ≤ i → wstk1[i]? = s.core.wstk[i]?) ∧
                (∀ j, j < pc.toNat - p.toNat →
                  wstk1[(p.toNat - 2) + j]? = s.core.wstk[p.toNat + j]?) ∧
                (FullMem c { s with core := { s.core with wstk := wstk1 } } ⋆ R) m2)
            (fun (pc, _, ()) _ => end0 - pc.toNat)
            (fun J2 hLoop2 => ?_) ?_
          · c0_hsteps
            exact hLoop2 (p, p - 2#64, ()) m1
              ⟨Nat.le_refl _, hpe, hp2_toNat, s.core.wstk, hws_len,
               fun _ _ => rfl, fun _ hj => by omega, hm⟩
          · rintro J2 ⟨pc, qc, ⟨⟩⟩ m2 ⟨hpc_lo, hpc_hi, hqc_eq, wstk1, hlen1, hout1, hsh1, hm2⟩
              hLoop2
            obtain ⟨sL, hsL_eq, hmL⟩ : ∃ sL : FullState,
                sL = { s with core := { s.core with wstk := wstk1 } } ∧ (FullMem c sL ⋆ R) m2 :=
              ⟨_, rfl, hm2⟩
            clear hm2
            have hsL_c : sL.core = { s.core with wstk := wstk1 } := congrArg FullState.core hsL_eq
            have hsL_sc : sL.scratch = s.scratch := by rw [hsL_eq]
            have hsL_ws : sL.core.wstk = wstk1 := by rw [hsL_c]
            have hsL_wv : sL.core.wvec = s.core.wvec := by rw [hsL_c]
            have hsL_wu : sL.core.wusable = s.core.wusable := by rw [hsL_c]
            clear hsL_eq
            c0_hsplit
            · have hpc_lt : pc.toNat < end0 := by
                have hc' : pc.toNat < (BitVec.setWidth 64
                    (s.core.wvec[(lit.setWidth 64 <<< (1 : Nat)).toNat]'hbd0_w) +
                  BitVec.setWidth 64
                    (s.core.wvec[((lit.setWidth 64 <<< (1 : Nat)) +
                      (1 : BitVec 64)).toNat]'hbd1_w)).toNat := by c0_bound
                rwa [hend64] at hc'
              have hpc_w : pc.toNat < wstk1.length := by omega
              have hqc_w : qc.toNat < wstk1.length := by omega
              have hpc_sL : pc.toNat < sL.core.wstk.length := by rw [hsL_ws]; exact hpc_w
              have hqc_sL : qc.toNat < sL.core.wstk.length := by rw [hsL_ws]; exact hqc_w
              have hpc1 : (pc + 1#64).toNat = pc.toNat + 1 := m5_bv64_add1_nat _ (by omega)
              have hqc1 : (qc + 1#64).toNat = qc.toNat + 1 := m5_bv64_add1_nat _ (by omega)
              c0_hsteps
              let wstk1' := wstk1.set qc.toNat (wstk1[pc.toNat]'hpc_w)
              have hws_step : sL.core.wstk.set qc.toNat (sL.core.wstk[pc.toNat]'hpc_sL) =
                  wstk1' := by
                dsimp only [wstk1']
                rw [m5_list_getElem_of_list_idx (hj := hpc_w) hsL_ws rfl, hsL_ws]
              have hm_next : (FullMem c { s with core := { s.core with wstk := wstk1' } } ⋆ R) _ :=
                m5_fullMem_of_eq (s1 := { sL with core := { sL.core with
                    wstk := sL.core.wstk.set qc.toNat (sL.core.wstk[pc.toNat]'hpc_sL) } })
                  (by assumption) (by dsimp only; rw [hws_step, hsL_c]) hsL_sc
              refine hLoop2 (pc + 1#64, qc + 1#64, ()) _ (by dsimp only; rw [hpc1]; omega)
                ⟨by rw [hpc1]; omega, by rw [hpc1]; omega, by rw [hpc1, hqc1]; omega,
                 wstk1', by simp [wstk1', hlen1],
                 fun i hi => by
                   rw [hpc1] at hi; dsimp only [wstk1']
                   rw [List.getElem?_set_ne (by omega)]
                   exact hout1 i (by omega),
                 fun j hj => by
                   rw [hpc1] at hj; dsimp only [wstk1']
                   by_cases hjeq : j = pc.toNat - p.toNat
                   · subst hjeq
                     have hq_idx : p.toNat - 2 + (pc.toNat - p.toNat) = qc.toNat := by omega
                     have hp_idx : p.toNat + (pc.toNat - p.toNat) = pc.toNat := by omega
                     rw [hq_idx, List.getElem?_set_self hqc_w, hp_idx,
                       ← hout1 pc.toNat (Or.inr (by omega)), List.getElem?_eq_getElem hpc_w]
                   · rw [List.getElem?_set_ne (by omega)]
                     exact hsh1 j (by omega),
                 hm_next⟩
            · have hpc_eq : pc.toNat = end0 := by
                have hc' : ¬ pc.toNat < (BitVec.setWidth 64
                    (s.core.wvec[(lit.setWidth 64 <<< (1 : Nat)).toNat]'hbd0_w) +
                  BitVec.setWidth 64
                    (s.core.wvec[((lit.setWidth 64 <<< (1 : Nat)) +
                      (1 : BitVec 64)).toNat]'hbd1_w)).toNat := by c0_bound
                rw [hend64] at hc'; omega
              clear hLoop1 hLoop2 hinv hw_some hw_eq hp1_toNat hp2_toNat hpc_lo hpc_hi
                hqc_eq hret_same hcr_msb
              have he2_toNat : ((BitVec.setWidth 64
                    (s.core.wvec[(lit.setWidth 64 <<< (1 : Nat)).toNat]'hbd0_w) +
                  BitVec.setWidth 64
                    (s.core.wvec[((lit.setWidth 64 <<< (1 : Nat)) +
                      (1 : BitVec 64)).toNat]'hbd1_w)) - 2#64).toNat = end0 - 2 := by
                rw [BitVec.toNat_sub_of_le (by
                  rw [BitVec.le_def, hend64, show (2#64).toNat = 2 from rfl]; omega),
                  hend64, show (2#64).toNat = 2 from rfl]
              have he1_toNat : ((BitVec.setWidth 64
                    (s.core.wvec[(lit.setWidth 64 <<< (1 : Nat)).toNat]'hbd0_w) +
                  BitVec.setWidth 64
                    (s.core.wvec[((lit.setWidth 64 <<< (1 : Nat)) +
                      (1 : BitVec 64)).toNat]'hbd1_w)) - 1#64).toNat = end0 - 1 := by
                rw [BitVec.toNat_sub_of_le (by
                  rw [BitVec.le_def, hend64, show (1#64).toNat = 1 from rfl]; omega),
                  hend64, show (1#64).toNat = 1 from rfl]
              have hsz_sub2 : (BitVec.setWidth 64
                    (s.core.wvec[((lit.setWidth 64 <<< (1 : Nat)) +
                      (1 : BitVec 64)).toNat]'hbd1_w) - 2#64).setWidth 32 =
                  BitVec.ofNat 32 (sz0 - 2) := by
                apply BitVec.eq_of_toNat_eq
                rw [BitVec.toNat_setWidth, BitVec.toNat_sub_of_le (by
                  rw [BitVec.le_def, hsz64, show (2#64).toNat = 2 from rfl]; omega),
                  hsz64, show (2#64).toNat = 2 from rfl, BitVec.toNat_ofNat,
                  Nat.mod_eq_of_lt (by omega)]
              have he2_sL : ((BitVec.setWidth 64
                    (s.core.wvec[(lit.setWidth 64 <<< (1 : Nat)).toNat]'hbd0_w) +
                  BitVec.setWidth 64
                    (s.core.wvec[((lit.setWidth 64 <<< (1 : Nat)) +
                      (1 : BitVec 64)).toNat]'hbd1_w)) - 2#64).toNat < sL.core.wstk.length := by
                rw [he2_toNat, hsL_ws, hlen1]; omega
              have he1_sL : ((BitVec.setWidth 64
                    (s.core.wvec[(lit.setWidth 64 <<< (1 : Nat)).toNat]'hbd0_w) +
                  BitVec.setWidth 64
                    (s.core.wvec[((lit.setWidth 64 <<< (1 : Nat)) +
                      (1 : BitVec 64)).toNat]'hbd1_w)) - 1#64).toNat <
                  (sL.core.wstk.set ((BitVec.setWidth 64
                    (s.core.wvec[(lit.setWidth 64 <<< (1 : Nat)).toNat]'hbd0_w) +
                  BitVec.setWidth 64
                    (s.core.wvec[((lit.setWidth 64 <<< (1 : Nat)) +
                      (1 : BitVec 64)).toNat]'hbd1_w)) - 2#64).toNat 0xFFFFFFFF#32).length := by
                rw [List.length_set, he1_toNat, hsL_ws, hlen1]; omega
              have hwv_sL : ((lit.setWidth 64 <<< (1 : Nat)) + (1 : BitVec 64)).toNat <
                  sL.core.wvec.length := by rw [hsL_wv]; exact hbd1_w
              c0_hsteps
              let wstk2 := (wstk1.set (end0 - 2) 0xFFFFFFFF#32).set (end0 - 1) 0xFFFFFFFF#32
              let wvec' := s.core.wvec.set (2 * lit.toNat + 1) (BitVec.ofNat 32 (sz0 - 2))
              let wu' := s.core.wusable + 2#64
              obtain ⟨hlay', hmw_pres⟩ := m5_unwatch_fin_inv rfl hlen.core_ok hlay hlit_lt hsz2
                hp_ge2 hpe (by simpa only [hpc_eq] using hout1) (by simpa only [hpc_eq] using hsh1)
                hinv_found
              have hws_eq :
                  (sL.core.wstk.set ((BitVec.setWidth 64
                      (s.core.wvec[(lit.setWidth 64 <<< (1 : Nat)).toNat]'hbd0_w) +
                    BitVec.setWidth 64
                      (s.core.wvec[((lit.setWidth 64 <<< (1 : Nat)) +
                        (1 : BitVec 64)).toNat]'hbd1_w)) - 2#64).toNat 0xFFFFFFFF#32).set
                  ((BitVec.setWidth 64
                      (s.core.wvec[(lit.setWidth 64 <<< (1 : Nat)).toNat]'hbd0_w) +
                    BitVec.setWidth 64
                      (s.core.wvec[((lit.setWidth 64 <<< (1 : Nat)) +
                        (1 : BitVec 64)).toNat]'hbd1_w)) - 1#64).toNat 0xFFFFFFFF#32 =
                  wstk2 := by dsimp only [wstk2]; rw [hsL_ws, he2_toNat, he1_toNat]
              have hwv_eq : sL.core.wvec.set
                  ((lit.setWidth 64 <<< (1 : Nat)) + (1 : BitVec 64)).toNat
                  ((BitVec.setWidth 64
                    (s.core.wvec[((lit.setWidth 64 <<< (1 : Nat)) +
                      (1 : BitVec 64)).toNat]'hbd1_w) - 2#64).setWidth 32) = wvec' := by
                dsimp only [wvec']; rw [hsL_wv, hsz_sub2, h2l1_eq]
              have hm_fin : (FullMem c { s with core :=
                  { s.core with wvec := wvec', wstk := wstk2, wusable := wu' } } ⋆ R) _ :=
                m5_unwatch_fin_mem (by assumption) hsL_c hsL_sc hws_eq hwv_eq
                  (congrArg (· + 2#64) hsL_wu)
              exact hQ wvec' wstk2 wu' _
                ⟨{ hlen.core_ok with wvec_len := by simp [wvec', hwv_len],
                                     wstk_len_arr := by simp [wstk2, hlen1] },
                 hlen.scratch_ok⟩ hlay' hmw_pres hm_fin
        · c0_hsteps
          obtain ⟨hdec, hlo', hle', hinv'⟩ :=
            m5_unwatch_step_ok hp_ge2 hpe (by omega) hw_some hinv
          exact hLoop1 (p - 2#64 + (w >>> (31 : Nat)).setWidth 64, ()) m1 hdec
            ⟨rfl, hlo', hle', hinv'⟩
      · c0_hsteps; exact hret_same

end UnwatchLargeProof

/-! ## 3. Shared Suffix-Free Backward Watch-Blocker Update Loop (`m5_loop4_sz_wp`) -/

section Loop4Blocker

open Full.FullAnalyzeTactics Full.FullAnalyzeSpecs Full.FullAnalyzeHelpers
open scoped Full.FullAnalyzeTactics

private theorem m5_loop4_hit_ok {c : FullCfg} {F_cur : List (List Nat)}
    {k : FullCoreState} {l0 cref nl1 : BitVec 32} {p_nat : Nat}
    (hdm : k.dense_mode = 0#64) (hmw : ModeWatchesInv F_cur k)
    (hl0 : l0.toNat < 2 * k.cur_vars) (hnl1 : nl1.toNat < 2 * k.cur_vars)
    (h2cv : 2 * k.cur_vars < 2 ^ 31 - 1) (hcr_lt : cref.toNat < 0x80000000)
    (hcref : cref.toNat ∈ fullArenaClauseRefsCore k) (hcr_msb : (cref &&& 0x80000000#32) = 0#32)
    (hlen : k.wstk.length = c.wcap) (hwle : k.wlen ≤ c.wcap)
    (hbnd : fullWatchOffCore k l0.toNat + fullWatchSizeCore k l0.toNat ≤ k.wlen)
    (hp_ge2 : fullWatchOffCore k l0.toNat + 2 ≤ p_nat)
    (hle : p_nat ≤ fullWatchOffCore k l0.toNat + fullWatchSizeCore k l0.toNat)
    (hw_some : k.wstk[p_nat - 1]? = some cref)
    (hpre : WatchSliceOk F_cur k l0.toNat (fullWatchOffCore k l0.toNat)
      (p_nat - fullWatchOffCore k l0.toNat))
    (hsuf : WatchSliceOk F_cur k l0.toNat p_nat
      (fullWatchOffCore k l0.toNat + fullWatchSizeCore k l0.toNat - p_nat)) :
    ModeWatchesInv F_cur
      { k with wstk := k.wstk.set (p_nat - 2) (nl1 &&& 0x7FFFFFFF#32) } := by
  let off_n := fullWatchOffCore k l0.toNat
  let sz_n := fullWatchSizeCore k l0.toNat
  let end_n := off_n + sz_n
  rcases m5_watchSlice_split_last hpre (by omega) with
    ⟨w0, hw0, hfl0, _⟩ | ⟨_, w0, cr, hw0, hcr, _, _, _, hpre2⟩
  · rw [show off_n + (p_nat - off_n) - 1 = p_nat - 1 by omega, hw_some] at hw0
    cases hw0; exact absurd hcr_msb hfl0
  · rw [show off_n + (p_nat - off_n) - 1 = p_nat - 1 by omega, hw_some] at hcr
    cases hcr
    let b' := nl1 &&& 0x7FFFFFFF#32
    let ws_f := k.wstk.set (p_nat - 2) b'
    let k' : FullCoreState := { k with wstk := ws_f }
    have hnl1_p := bv32_lit_lo31_props (l := nl1) (by omega)
    have hb'_ne : b' ≠ 0xFFFFFFFF#32 := by
      dsimp only [b']; rw [hnl1_p.1]; exact bv32_lit_neq_ff (by omega)
    have hF_refl : (cnfOfClauses F_cur).Entails (cnfOfClauses F_cur) := by
      rw [CNF.entails_def]; exact fun _ hx => hx
    have hpre2' : WatchSliceOk F_cur k' l0.toNat off_n (p_nat - 2 - off_n) :=
      fa_watchSlice_relocate (k := k) (k' := k') hF_refl (Nat.le_refl _) (fun _ hr => hr)
        (fun idx _ => by dsimp only [k', ws_f]; rw [List.getElem?_set_ne (by omega)])
        (by dsimp only [off_n] at *; simpa only [show p_nat - fullWatchOffCore k l0.toNat - 2 =
          p_nat - 2 - fullWatchOffCore k l0.toNat by omega] using hpre2)
    have hsuf' : WatchSliceOk F_cur k' l0.toNat p_nat (end_n - p_nat) :=
      fa_watchSlice_relocate (k := k) (k' := k') hF_refl (Nat.le_refl _) (fun _ hr => hr)
        (fun idx _ => by dsimp only [k', ws_f]; rw [List.getElem?_set_ne (by omega)]) hsuf
    have hmid_suf : WatchSliceOk F_cur k' l0.toNat (p_nat - 2) (end_n - p_nat + 2) :=
      .large (by dsimp only [k', ws_f]; exact List.getElem?_set_self (by omega))
        (by dsimp only [k', ws_f]; rw [List.getElem?_set_ne (by omega),
              show p_nat - 2 + 1 = p_nat - 1 by omega]; exact hw_some)
        hnl1_p.2.1 hcr_lt hcref
        (by simpa only [show p_nat - 2 + 2 = p_nat by omega] using hsuf')
    have hslice_all : WatchSliceOk F_cur k' l0.toNat off_n sz_n := by
      have happ := m5_watchSlice_append hpre2'
        (by simpa only [show off_n + (p_nat - 2 - off_n) = p_nat - 2 by omega] using hmid_suf)
      simpa only [show p_nat - 2 - off_n + (end_n - p_nat + 2) = sz_n by omega] using happ
    exact fa_modeWatches_set_in_slice hdm hmw hl0 (by omega) (by omega) (by omega) hb'_ne
      hslice_all

private theorem m5_loop4_step_ok {F_cur : List (List Nat)} {k : FullCoreState}
    {lit off_n end_n : Nat} {p : BitVec 64} {w : BitVec 32}
    (hp_ge2 : off_n + 2 ≤ p.toNat) (hle : p.toNat ≤ end_n) (_hend : end_n < 2 ^ 64)
    (hw_some : k.wstk[p.toNat - 1]? = some w)
    (hpre : WatchSliceOk F_cur k lit off_n (p.toNat - off_n))
    (hsuf : WatchSliceOk F_cur k lit p.toNat (end_n - p.toNat)) :
    let p' := p - 2#64 + (w >>> (31 : Nat)).setWidth 64
    p'.toNat - off_n < p.toNat - off_n ∧ off_n ≤ p'.toNat ∧ p'.toNat ≤ end_n ∧
    WatchSliceOk F_cur k lit off_n (p'.toNat - off_n) ∧
    WatchSliceOk F_cur k lit p'.toNat (end_n - p'.toNat) := by
  intro p'
  have hp2_toNat : (p - 2#64).toNat = p.toNat - 2 := by bv_omega
  have hsh_le := (m5_bv32_lshr31_nat_cases w).2.2
  have hp'_toNat : p'.toNat = p.toNat - 2 + (w >>> (31 : Nat)).toNat := by
    dsimp only [p']; rw [BitVec.toNat_add, hp2_toNat, zext_toNat _ (by decide)]
    exact Nat.mod_eq_of_lt (by omega)
  rcases m5_watchSlice_split_last hpre (by omega) with
    ⟨w0, hw0, hfl0, hne0, hlt0, hent0, hpre1⟩ |
    ⟨_, w0, cr, hw0, hcr, hfl0, hlt0, href0, hpre2⟩
  · rw [show off_n + (p.toNat - off_n) - 1 = p.toNat - 1 by omega, hw_some] at hw0
    cases hw0
    have hsh1 := (m5_bv32_lshr31_nat_cases w).2.1 hfl0
    have hp'_eq : p'.toNat = p.toNat - 1 := by rw [hp'_toNat, hsh1]; omega
    refine ⟨by omega, by omega, by omega,
      by rw [hp'_eq, show p.toNat - 1 - off_n = p.toNat - off_n - 1 by omega]; exact hpre1,
      by rw [hp'_eq, show end_n - (p.toNat - 1) = (end_n - p.toNat) + 1 by omega]
         exact .bin hw_some hfl0 hne0 hlt0 hent0
           (by simpa only [show p.toNat - 1 + 1 = p.toNat by omega] using hsuf)⟩
  · rw [show off_n + (p.toNat - off_n) - 1 = p.toNat - 1 by omega, hw_some] at hcr
    cases hcr
    have hcr_msb0 : (w &&& 0x80000000#32) = 0#32 := (m5_bv32_lt_highbit_iff w).mp hlt0
    have hsh0 := (m5_bv32_lshr31_nat_cases w).1 hcr_msb0
    have hp'_eq : p'.toNat = p.toNat - 2 := by rw [hp'_toNat, hsh0]; omega
    rw [show off_n + (p.toNat - off_n) - 2 = p.toNat - 2 by omega] at hw0
    refine ⟨by omega, by omega, by omega,
      by rw [hp'_eq, show p.toNat - 2 - off_n = p.toNat - off_n - 2 by omega]; exact hpre2,
      by rw [hp'_eq, show end_n - (p.toNat - 2) = (end_n - p.toNat) + 2 by omega]
         exact .large hw0
           (by simpa only [show p.toNat - 2 + 1 = p.toNat - 1 by omega] using hw_some)
           hfl0 hlt0 href0 (by simpa only [show p.toNat - 2 + 2 = p.toNat by omega] using hsuf)⟩

/-- Shared suffix-free backward watch-blocker replacement WP for `if (sz >= 2ULL) { ... }`
(parameterized only by `ModeWatchesInv`, usable by both `full_otfs_large` and
`full_prop_lit_chrono`). -/
theorem m5_loop4_sz_wp {Γ : Env} {ts : List Ty} {Q : Post ts} {X : XPost}
    {c : FullCfg} {F_cur : List (List Nat)}
    {s5 : FullState} {ws5 : List (BitVec 32)} {cref l0 nl1 : BitVec 32}
    {offV szV : BitVec 64} {R : Mem 64 → Prop} {m5 : Mem 64} {J_out : Cont []}
    (hdm5 : s5.core.dense_mode = 0#64) (hmw5 : ModeWatchesInv F_cur s5.core)
    (hlen5 : s5.LengthsOk c) (h2cv : 2 * s5.core.cur_vars < 2 ^ 31 - 1)
    (hl0_lt5 : l0.toNat < 2 * s5.core.cur_vars) (hnl1_lt5 : nl1.toNat < 2 * s5.core.cur_vars)
    (hws5_c : s5.core.wstk = ws5) (hcr_lt5 : cref.toNat < 0x80000000)
    (hcref5 : cref.toNat ∈ fullArenaClauseRefsCore s5.core)
    (hoffV : offV.toNat = fullWatchOffCore s5.core l0.toNat)
    (hszV : szV.toNat = fullWatchSizeCore s5.core l0.toNat)
    (hm5 : (FullMem c s5 ⋆ R) m5)
    (hJ_out : ∀ xs ml,
      (∃ ws_f : List (BitVec 32),
        (FullMem c { s5 with core := { s5.core with wstk := ws_f } } ⋆ R) ml ∧
        ws_f.length = c.wcap ∧ ModeWatchesInv F_cur { s5.core with wstk := ws_f }) →
      J_out xs ml) :
    wp Γ Q X
      (Expr.group (fun (_ : Tup Cont [[]]) =>
          Blocks.cons (fun (_ : Tup Val []) => Expr.jump J_out ()) Blocks.nil)
        fun Js =>
        Expr.let_ (Op.mk (.cmp .uge (.bits 64) .bool rfl) (Arg.var szV, Arg.imm 2, ())) fun p_60 =>
        Expr.jnz (Arg.var p_60.fst)
          (Expr.let_ (Op.mk (.add (.bits 64)) (Arg.var offV, Arg.var szV, ())) fun p_61 =>
           Expr.let_ (Op.mk (.add (.bits 64)) (Arg.var offV, Arg.imm 2, ())) fun p_62 =>
           Expr.group (fun (_ : Tup Cont [[i64]]) =>
             Blocks.cons (fun (_ : Tup Val [i64]) => Expr.jump Js.fst ()) Blocks.nil) fun Js_b =>
           Expr.group (fun (Js_1 : Tup Cont [[i64]]) =>
             Blocks.cons (fun (p_63 : Tup Val [i64]) =>
               Expr.let_ (Op.mk (.cmp .uge (.bits 64) .bool rfl)
                 (Arg.var p_63.fst, Arg.var p_62.fst, ())) fun p_64 =>
               Expr.jnz (Arg.var p_64.fst)
                 (Expr.let_ (Op.mk (.sub (.bits 64)) (Arg.var p_63.fst, Arg.imm 1, ())) fun p_65 =>
                  Expr.let_ (Op.mk (.mul (.bits 64)) (Arg.var p_65.fst, Arg.imm 4, ())) fun p_66 =>
                  Expr.let_ (Op.mk (.add (.bits 64))
                    (Arg.var c.pWstk, Arg.var p_66.fst, ())) fun p_67 =>
                  Expr.load i32 (Arg.var p_67.fst) fun ld_10 =>
                  Expr.let_ (Op.mk (.cmp .eq (.bits 32) .bool rfl)
                    (Arg.var ld_10, Arg.var cref, ())) fun p =>
                  Expr.jnz (Arg.var p.fst)
                    (Expr.let_ (Op.mk (.sub (.bits 64))
                        (Arg.var p_63.fst, Arg.imm 2, ())) fun p =>
                     Expr.let_ (Op.mk (.mul (.bits 64)) (Arg.var p.fst, Arg.imm 4, ())) fun p =>
                     Expr.let_ (Op.mk (.add (.bits 64))
                       (Arg.var c.pWstk, Arg.var p.fst, ())) fun p =>
                     Expr.let_ (Op.mk (.and (.bits 32))
                       (Arg.var nl1, Arg.imm 2147483647, ())) fun p_68 =>
                     Expr.store (Arg.var p_68.fst) (Arg.var p.fst)
                       (Expr.jump Js_b.fst (Arg.var p_63.fst, ())))
                    (Expr.let_ (Op.mk (.sub (.bits 64))
                        (Arg.var p_63.fst, Arg.imm 2, ())) fun p =>
                     Expr.let_ (Op.mk (.lshr (.bits 32))
                       (Arg.var ld_10, Arg.imm 31, ())) fun p_68 =>
                     Expr.let_ (Op.mk (.zext 32 64) (Arg.var p_68.fst, ())) fun p_69 =>
                     Expr.let_ (Op.mk (.add (.bits 64))
                       (Arg.var p.fst, Arg.var p_69.fst, ())) fun p =>
                     Expr.jump Js_1.fst (Arg.var p.fst, ())))
                 (Expr.jump Js_b.fst (Arg.var p_63.fst, ()))) Blocks.nil)
           fun Js_l => Expr.jump Js_l.fst (Arg.var p_61.fst, ()))
          (Expr.jump Js.fst ())) m5 := by
  have hmw5_0 := hmw5
  unfold ModeWatchesInv at hmw5_0; simp only [hdm5, ↓reduceIte] at hmw5_0
  have hw5_len := hlen5.core_ok.wstk_len_arr
  have hw5_wle := hlen5.core_ok.wlen_le
  have hwcap_lt := c.hwcap; unfold dimacsBound at hwcap_lt
  have hbnd5 := hmw5_0.layout.bounds l0.toNat hl0_lt5
  have hcr_msb5 : (cref &&& 0x80000000#32) = 0#32 := (m5_bv32_lt_highbit_iff cref).mp hcr_lt5
  let off_n := fullWatchOffCore s5.core l0.toNat
  let sz_n := fullWatchSizeCore s5.core l0.toNat
  let end_n := off_n + sz_n
  have hsame5 : J_out () m5 :=
    hJ_out () m5 ⟨ws5, m5_fullMem_of_eq hm5 (congrArg (fun w => { s5.core with wstk := w }) hws5_c)
      rfl, by rw [← hws5_c, hw5_len], by rw [← hws5_c]; exact hmw5⟩
  have hend64 : (offV + szV).toNat = end_n := by
    rw [BitVec.toNat_add, hoffV, hszV]; exact Nat.mod_eq_of_lt (by omega)
  have hoff2_64 : (offV + 2#64).toNat = off_n + 2 := by
    rw [BitVec.toNat_add, hoffV, show (2#64).toNat = 2 from rfl]; exact Nat.mod_eq_of_lt (by omega)
  refine wp_unroll_group fun Jsz hJsz => ?_
  c0_hsteps_nogrp
  · have hsz2 : 2 ≤ sz_n := by
      have hc' : (2#64).toNat ≤ szV.toNat := by c0_bound
      rw [hszV] at hc'; exact hc'
    refine wp_loop_break_group (brkTs := [i64]) (lpTs := [i64])
      (fun _ ml => ∃ ws_f : List (BitVec 32),
        (FullMem c { s5 with core := { s5.core with wstk := ws_f } } ⋆ R) ml ∧
        ws_f.length = c.wcap ∧ ModeWatchesInv F_cur { s5.core with wstk := ws_f })
      (fun rem (p, ()) ml =>
        ml = m5 ∧ rem = p.toNat - off_n ∧ off_n ≤ p.toNat ∧ p.toNat ≤ end_n ∧
        WatchSliceOk F_cur s5.core l0.toNat off_n (p.toNat - off_n) ∧
        WatchSliceOk F_cur s5.core l0.toNat p.toNat (end_n - p.toNat))
      ?_ ?_ ?_
    · rintro _ _ ml hres; c0_hsteps; exact hJ_out () ml hres
    · rintro B L rem ⟨p, ⟨⟩⟩ ml hB ih ⟨rfl, rfl, hlo, hle, hpre, hsuf⟩
      c0_hsplit
      · have hp_ge2 : off_n + 2 ≤ p.toNat := by
          have hc' : (offV + 2#64).toNat ≤ p.toNat := by c0_bound
          rwa [hoff2_64] at hc'
        have hp1_toNat : (p - 1#64).toNat = p.toNat - 1 := by bv_omega
        have hp2_toNat : (p - 2#64).toNat = p.toNat - 2 := by bv_omega
        have hp1_lt : (p - 1#64).toNat < s5.core.wstk.length := by rw [hp1_toNat]; omega
        let w : BitVec 32 := s5.core.wstk[(p - 1#64).toNat]'hp1_lt
        have hw_some : s5.core.wstk[p.toNat - 1]? = some w := by
          rw [List.getElem?_eq_getElem (by omega : p.toNat - 1 < s5.core.wstk.length)]
          exact congrArg some (by dsimp only [w]; exact (m5_list_getElem_of_idx hp1_toNat).symm)
        c0_hsplit
        · have hw_eq : w = cref := by assumption
          have hp2_lt : (p - 2#64).toNat < s5.core.wstk.length := by rw [hp2_toNat]; omega
          c0_hsteps
          let ws_f := s5.core.wstk.set (p.toNat - 2) (nl1 &&& 0x7FFFFFFF#32)
          have hmw' := m5_loop4_hit_ok hdm5 hmw5 hl0_lt5 hnl1_lt5 h2cv hcr_lt5
            hcref5 hcr_msb5 hw5_len hw5_wle hbnd5 hp_ge2 hle (hw_eq ▸ hw_some) hpre hsuf
          have hm_brk : (FullMem c { s5 with core := { s5.core with wstk := ws_f } } ⋆ R) _ :=
            m5_fullMem_of_eq
              (s1 := { s5 with core := { s5.core with
                wstk := s5.core.wstk.set (p - 2#64).toNat (nl1 &&& 0x7FFFFFFF#32) } })
              (by assumption)
              (congrArg (fun x => { s5.core with wstk := x })
                (by dsimp only [ws_f]; rw [hp2_toNat])) rfl
          exact hB (p, ()) _ ⟨ws_f, hm_brk, by simp [ws_f, hw5_len], hmw'⟩
        · c0_hsteps
          obtain ⟨hdec, hlo', hle', hpre', hsuf'⟩ :=
            m5_loop4_step_ok hp_ge2 hle (by omega) hw_some hpre hsuf
          exact ih _ (p - 2#64 + (w >>> (31 : Nat)).setWidth 64, ()) ml hdec
            ⟨rfl, rfl, hlo', hle', hpre', hsuf'⟩
      · c0_hsteps
        exact hB (p, ()) ml ⟨ws5, m5_fullMem_of_eq hm5
          (congrArg (fun w => { s5.core with wstk := w }) hws5_c) rfl,
          by rw [← hws5_c, hw5_len], by rw [← hws5_c]; exact hmw5⟩
    · intro B L _ hL; c0_hsteps
      refine hL sz_n _ m5 ⟨rfl, by rw [hend64]; omega, by rw [hend64]; omega,
        by rw [hend64]; exact Nat.le_refl _,
        by rw [hend64, show end_n - off_n = sz_n by omega]; exact hmw5_0.slices l0.toNat hl0_lt5,
        by rw [hend64, Nat.sub_self]; exact .empty⟩
  · exact hsame5

end Loop4Blocker

/-! ## 3b. Shared Watch-Stack Headroom (`wcap - wlen < 2ULL`) Defrag Pre-Check (`bool` return) -/

section WstackEnsure2

open Full.FullAnalyzeTactics Full.FullAnalyzeSpecs Full.FullAnalyzeHelpers
open scoped Full.FullAnalyzeTactics

/-- Shared WP for `if (h->wcap - h->wlen < 2ULL) { if (h->wusable > 0ULL) full_wstack_defrag(h);
if (h->wcap - h->wlen < 2ULL) { h->oom = 1ULL; return false; } }` (used by both `full_otfs_large`
and `full_otfs_bin_m5`). -/
theorem m5_wstack_ensure2_ret_false_wp {Γ : Env} {Q : Post [.bool]} {X : XPost}
    {c : FullCfg} {F_cur : List (List Nat)} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} {Jd : Cont []}
    (hDefrag : ∀ a m Q X, Full.fullWstackDefragSpec a m Q X →
      Γ "full_wstack_defrag" [i64] [] a m Q X)
    (hlen : s.LengthsOk c) (hdm : s.core.dense_mode = 0#64)
    (hmw : ModeWatchesInv F_cur s.core) (hm : (FullMem c s ⋆ R) m)
    (hOom : ∀ (s_i : FullState) (wv_i ws_i : List (BitVec 32)) (wl_i : Nat)
      (wu_i : BitVec 64) (wso_i : List (BitVec 32)) (ml_o : Mem 64),
      s_i.core = { s.core with wvec := wv_i, wstk := ws_i, wlen := wl_i, wusable := wu_i } →
      s_i.scratch = { s.scratch with wsort := wso_i } →
      s_i.LengthsOk c → ModeWatchesInv F_cur s_i.core →
      (FullMem c { s_i with core := { s_i.core with oom := 1#64 } } ⋆ R) ml_o →
      Q (false, ()) ml_o)
    (hJd : ∀ xs ml_d,
      (∃ (s_d : FullState) (wv_d ws_d : List (BitVec 32)) (wl_d : Nat) (wu_d : BitVec 64)
        (wso_d : List (BitVec 32)),
        s_d.core = { s.core with wvec := wv_d, wstk := ws_d, wlen := wl_d, wusable := wu_d } ∧
        s_d.scratch = { s.scratch with wsort := wso_d } ∧
        s_d.LengthsOk c ∧ ModeWatchesInv F_cur s_d.core ∧
        (FullMem c s_d ⋆ R) ml_d) →
      Jd xs ml_d) :
    wp Γ Q X
      (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 40, ())) fun p_19 =>
       Expr.load i64 (Arg.var p_19.fst) fun ld =>
       Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 56, ())) fun p_20 =>
       Expr.load i64 (Arg.var p_20.fst) fun ld_5 =>
       Expr.let_ (Op.mk (.sub i64) (Arg.var ld, Arg.var ld_5, ())) fun p_21 =>
       Expr.let_ (Op.mk (.cmp .ult i64 .bool rfl) (Arg.var p_21.fst, Arg.imm 2, ())) fun p_22 =>
       Expr.jnz (Arg.var p_22.fst)
         (Expr.group (fun (_ : Tup Cont [[]]) =>
             Blocks.cons (fun (_ : Tup Val []) =>
               Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 40, ())) fun p_24 =>
               Expr.load i64 (Arg.var p_24.fst) fun ld =>
               Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 56, ())) fun p_25 =>
               Expr.load i64 (Arg.var p_25.fst) fun ld_6 =>
               Expr.let_ (Op.mk (.sub i64) (Arg.var ld, Arg.var ld_6, ())) fun p_26 =>
               Expr.let_ (Op.mk (.cmp .ult i64 .bool rfl)
                 (Arg.var p_26.fst, Arg.imm 2, ())) fun p_27 =>
               Expr.jnz (Arg.var p_27.fst)
                 (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 760, ())) fun p =>
                  Expr.store (t := i64) (Arg.imm 1) (Arg.var p.fst)
                    (Expr.ret (Arg.imm false, ())))
                 (Expr.jump Jd ())) Blocks.nil)
           fun Js =>
           Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 464, ())) fun p_23 =>
           Expr.load i64 (Arg.var p_23.fst) fun ld =>
           Expr.let_ (Op.mk (.cmp .ugt i64 .bool rfl) (Arg.var ld, Arg.imm 0, ())) fun p_24 =>
           Expr.jnz (Arg.var p_24.fst)
             (Expr.call (rs := [.bool]) (as := [i64]) (bs := [])
               "full_wstack_defrag" (Arg.var c.hdr, ()) fun (_ : Tup Val []) =>
               Expr.jump Js.fst ())
             (Expr.jump Js.fst ()))
         (Expr.jump Jd ())) m := by
  have hcv_lt32 : s.core.cur_vars < 2 ^ 32 := by
    have := hlen.core_ok.cur_vars_le; have := c.hmaxv; unfold dimacsBound at *; omega
  have hwcap_lt64 : c.wcap < 2 ^ 64 := by
    have := c.hwcap; unfold dimacsBound at *; omega
  have hwlen_le : s.core.wlen ≤ c.wcap := hlen.core_ok.wlen_le
  have hlay0 : WatchStackLayout s.core := by
    have h := hmw; unfold ModeWatchesInv at h
    simp only [hdm, ↓reduceIte] at h; exact h.layout
  fa_fast_steps_nogrp
  · refine wp_join_group (ts := []) (fun () ml_i =>
      ∃ (s_i : FullState) (wv_i ws_i : List (BitVec 32)) (wl_i : Nat)
        (wu_i : BitVec 64) (wso_i : List (BitVec 32)),
        s_i.core = { s.core with wvec := wv_i, wstk := ws_i, wlen := wl_i, wusable := wu_i } ∧
        s_i.scratch = { s.scratch with wsort := wso_i } ∧
        s_i.LengthsOk c ∧ ModeWatchesInv F_cur s_i.core ∧ (FullMem c s_i ⋆ R) ml_i) ?_ ?_
    · rintro _ ⟨⟩ ml_i ⟨s_i, wv_i, ws_i, wl_i, wu_i, wso_i, hsi_c, hsi_sc, hlen_i, hmw_i, hm_i⟩
      have hwli_le : s_i.core.wlen ≤ c.wcap := hlen_i.core_ok.wlen_le
      fa_fast_steps
      · exact hOom s_i wv_i ws_i wl_i wu_i wso_i _ hsi_c hsi_sc hlen_i hmw_i (by assumption)
      · exact hJd () ml_i ⟨s_i, wv_i, ws_i, wl_i, wu_i, wso_i, hsi_c, hsi_sc, hlen_i, hmw_i, hm_i⟩
    · intro Ji hJi
      fa_fast_steps_nogrp
      · c0_call hDefrag
        refine ⟨c, s, R, rfl, hlen, hlay0, hm,
          fun wv_i ws_i wl_i wso_i ml_i hlen_i hlay_i _ hpres hm_i => ?_⟩
        obtain ⟨s_i, hsi_c, hsi_sc, hm_i'⟩ :=
          m5_otfs_opaque_state (s_old := { s with
            core := { s.core with wvec := wv_i, wstk := ws_i, wlen := wl_i, wusable := 0#64 }
            scratch := { s.scratch with wsort := wso_i } })
            { s.core with wvec := wv_i, wstk := ws_i, wlen := wl_i, wusable := 0#64 }
            { s.scratch with wsort := wso_i } hm_i rfl rfl
        have hmw_i : ModeWatchesInv F_cur s_i.core := by
          rw [hsi_c]
          exact fullWstackDefrag_preserves_modeWatchesInv hmw hlay_i rfl rfl (fun _ hr => hr) hpres
        have hlen_i' : s_i.LengthsOk c :=
          ⟨by rw [hsi_c]; exact hlen_i.core_ok, by rw [hsi_sc]; exact hlen_i.scratch_ok⟩
        exact hJi () ml_i ⟨s_i, wv_i, ws_i, wl_i, 0#64, wso_i, hsi_c, hsi_sc, hlen_i', hmw_i,
          hm_i'⟩
      · exact hJi () m ⟨s, s.core.wvec, s.core.wstk, s.core.wlen, s.core.wusable,
          s.scratch.wsort, rfl, rfl, hlen, hmw, hm⟩
  · exact hJd () m ⟨s, s.core.wvec, s.core.wstk, s.core.wlen, s.core.wusable,
      s.scratch.wsort, rfl, rfl, hlen, hmw, hm⟩

end WstackEnsure2

/-! ## 4. `full_otfs_large_wp` (`Full.fullOtfsLargeSpec`) -/

section OtfsLargeProof

open Full.FullAnalyzeTactics Full.FullAnalyzeHelpers
open scoped Full.FullAnalyzeTactics

private def OtfsShrinkInv (c : FullCfg) (s : FullState) (ar1 : List (BitVec 32))
    (cref l0 uip : BitVec 32) (old_sz r i_nat nsz : Nat)
    (ar_cur : List (BitVec 32)) (origMap : List Nat) : Prop :=
  ar_cur.length = c.arena_cap ∧ r = old_sz - i_nat ∧ 2 ≤ i_nat ∧ i_nat ≤ old_sz ∧
  1 ≤ nsz ∧ nsz = 1 + Full.otfsActCnt s.core cref.toNat i_nat ∧
  origMap.length = nsz ∧ origMap.Pairwise (· < ·) ∧ (∀ p ∈ origMap, p < i_nat) ∧
  ((l0 = s.core.arena[cref.toNat + 3]?.getD 0#32 ∧
      s.core.arena[cref.toNat + 4]?.getD 0#32 = uip ∧ 0 ∈ origMap ∧ 1 ∉ origMap) ∨
   (l0 = s.core.arena[cref.toNat + 4]?.getD 0#32 ∧
      s.core.arena[cref.toNat + 3]?.getD 0#32 = uip ∧ 1 ∈ origMap ∧ 0 ∉ origMap)) ∧
  (∀ p, 2 ≤ p → p < i_nat →
    0 < (s.core.lvl[(s.core.arena[cref.toNat + 3 + p]?.getD 0#32).toNat / 2]?.getD 0#32).toNat →
    p ∈ origMap) ∧
  (∀ k, k < nsz →
    ar_cur[cref.toNat + 3 + k]? = s.core.arena[cref.toNat + 3 + origMap[k]?.getD 0]?) ∧
  (∀ q, q < cref.toNat + 4 ∨ cref.toNat + 3 + nsz ≤ q → ar_cur[q]? = ar1[q]?)

private theorem otfs_shrink_loop_step {c : FullCfg} {s : FullState} {ar1 ar_cur : List (BitVec 32)}
    {cref l0 uip : BitVec 32} {old_sz i_nat nsz : Nat} {origMap : List Nat}
    (har_len : s.core.arena.length = c.arena_cap) (hinv : OtfsShrinkInv c s ar1 cref l0 uip
      old_sz (old_sz - i_nat) i_nat nsz ar_cur origMap)
    (hilt : i_nat < old_sz) (h3o : cref.toNat + 3 + old_sz ≤ c.arena_cap)
    (hlv : 0 < (s.core.lvl[(s.core.arena[cref.toNat + 3 + i_nat]?.getD
      0#32).toNat / 2]?.getD 0#32).toNat) :
    let ot := s.core.arena[cref.toNat + 3 + i_nat]'(by omega)
    let ar' := ar_cur.set (cref.toNat + 3 + nsz) ot
    OtfsShrinkInv c s ar1 cref l0 uip old_sz (old_sz - (i_nat + 1)) (i_nat + 1) (nsz + 1)
      ar' (origMap ++ [i_nat]) := by
  intro ot ar'
  obtain ⟨har_c, _, hi2, _, hns1, hact, hlm, hpw, hlt_m, h01, hcov, hmapeq, hout⟩ := hinv
  have hnsz_lt_i : nsz < i_nat := by have := Full.otfsActCnt_le s.core cref.toNat i_nat; omega
  have hpw' := List.pairwise_append.mpr ⟨hpw, List.pairwise_singleton _ _, fun a ha b hb => by
    simp only [List.mem_singleton] at hb; subst b; exact hlt_m a ha⟩
  have hlt' : ∀ p ∈ origMap ++ [i_nat], p < i_nat + 1 := fun p hp =>
    (List.mem_append.mp hp).elim (fun h => Nat.lt_succ_of_lt (hlt_m p h)) fun h => by
      simp only [List.mem_singleton] at h; omega
  have h01' : (l0 = s.core.arena[cref.toNat + 3]?.getD 0#32 ∧
      s.core.arena[cref.toNat + 4]?.getD 0#32 = uip ∧ 0 ∈ origMap ++ [i_nat] ∧
      1 ∉ origMap ++ [i_nat]) ∨ (l0 = s.core.arena[cref.toNat + 4]?.getD 0#32 ∧
      s.core.arena[cref.toNat + 3]?.getD 0#32 = uip ∧ 1 ∈ origMap ++ [i_nat] ∧
      0 ∉ origMap ++ [i_nat]) := by
    rcases h01 with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
    · exact Or.inl ⟨h1, h2, List.mem_append.mpr (Or.inl h3), fun hm => by
        rcases List.mem_append.mp hm with h | h <;> simp_all <;> omega⟩
    · exact Or.inr ⟨h1, h2, List.mem_append.mpr (Or.inl h3), fun hm => by
        rcases List.mem_append.mp hm with h | h <;> simp_all <;> omega⟩
  refine ⟨by simp [ar', har_c], rfl, by omega, by omega, by omega,
    by rw [hact, Full.otfsActCnt_succ hi2, ite_eq_left hlv, Nat.add_assoc], by simp [hlm], hpw',
    hlt', h01', fun p hp2 hplt hpos => by
      by_cases hpi : p = i_nat
      · subst p; simp
      · exact List.mem_append.mpr (Or.inl (hcov p hp2 (by omega) hpos)),
    fun k hk => by
      by_cases hkn : k = nsz
      · subst k; dsimp only [ar']
        rw [List.getElem?_set_self (by rw [har_c]; omega), List.getElem?_append_right (by omega)]
        simp [hlm, ot, List.getElem?_eq_getElem (by omega : cref.toNat + 3 + i_nat <
          s.core.arena.length)]
      · dsimp only [ar']; rw [List.getElem?_set_ne (by omega), hmapeq k (by omega),
          List.getElem?_append_left (by omega)],
    fun q hq => by
      dsimp only [ar']; rw [List.getElem?_set_ne (by rcases hq with h | h <;> omega)]
      exact hout q (hq.imp_right (by omega))⟩

private theorem otfs_large_fin {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut idx_u : Nat} {s s' : FullState} {cref uip : BitVec 32}
    (hlen : s.LengthsOk c) (hw : FullAnalyzeSpecs.FullWitnessCutInv c F0 F_cur cut s.core)
    (hcref : cref.toNat ∈ fullArenaClauseRefs s) (hng : fullArenaClauseGarb s cref.toNat = false)
    (hiu_cut : idx_u < cut) (hiu_te : idx_u < s.core.trail_end)
    (ht_u : (s.core.trl[idx_u]?.getD 0#32).toNat = uip.toNat)
    (hr_u : s.core.rsns[uip.toNat / 2]?.getD 0xFFFFFFFF#32 = cref)
    (hvals' : s'.core.vals = s.core.vals) (hlvl' : s'.core.lvl = s.core.lvl)
    (htrl' : s'.core.trl = s.core.trl) (hcl' : s'.core.cur_level = s.core.cur_level)
    (hsub : ∀ l ∈ fullArenaClauseLits s' cref.toNat,
      l ≠ uip.toNat ∧ l ∈ fullArenaClauseLits s cref.toNat) :
    ∀ l ∈ fullArenaClauseLits s' cref.toNat,
      l ≠ uip.toNat ∧ l ∈ fullArenaClauseLits s cref.toNat ∧ s'.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
      ((s'.core.lvl[l / 2]?.getD 0#32).toNat = s'.core.cur_level →
        ∃ m < idx_u, (s'.core.trl[m]?.getD 0#32).toNat = l ^^^ 1) := by
  have hwf := hw.arena.refs_wf cref.toNat hcref; have har_le := hlen.core_ok.arena_len_le
  have har_cap := c.harena; unfold dimacsBound at har_cap
  have hcr_lt : cref.toNat < 2 ^ 31 - 1 := by have := hwf.2.2.1; have := hwf.2.2.2.1; omega
  have hrs := hw.reason_inv idx_u hiu_te (Or.inl hiu_cut)
  dsimp only at hrs; rw [ht_u, hr_u] at hrs; have hrs' := hrs (bv32_lit_neq_ff hcr_lt)
  rw [ite_eq_right (fun h => h (bv32_lit_lo31_props (by omega : cref.toNat < 2 ^ 31)).2.2)] at hrs'
  intro l hl; obtain ⟨hne_u, hl_old⟩ := hsub l hl
  have hl_lt : l < 2 * s.core.cur_vars := hw.arena.lits_lt cref.toNat hcref hng l hl_old
  rcases hrs'.2.2 l hl_old with rfl | ⟨m, hm, hmeq, _⟩
  · exact absurd rfl hne_u
  · rw [hvals', hlvl', htrl', hcl']
    exact ⟨hne_u, hl_old, (hw.vals_false_iff l hl_lt).mpr ⟨m, by omega, hmeq⟩,
      fun _ => ⟨m, hm, hmeq⟩⟩

private def OtfsHdrPost (c : FullCfg) (s s2 : FullState) (R : Mem 64 → Prop)
    (cref : BitVec 32) (old_sz nsz : Nat) (origMap : List Nat) (ml3 : Mem 64) : Prop :=
  ∃ ar3 : List (BitVec 32),
    (FullMem c { s2 with core := { s2.core with arena := ar3 } } ⋆ R) ml3 ∧
    ar3.length = c.arena_cap ∧
    ar3[cref.toNat]? = some (if (fullArenaHdrCore s2.core cref.toNat &&& 0x00800000#32) = 0#32
      then fullArenaHdrCore s2.core cref.toNat ||| 0x00800000#32
      else fullArenaHdrCore s2.core cref.toNat) ∧
    ar3[cref.toNat + 2]? = some (BitVec.ofNat 32 nsz) ∧
    (∀ k, k < nsz →
      ar3[cref.toNat + 3 + k]? = s.core.arena[cref.toNat + 3 + origMap[k]?.getD 0]?) ∧
    (∀ j, nsz ≤ j → j < old_sz - 1 →
      ar3[cref.toNat + 3 + j]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32) ∧
    ((fullArenaHdrCore s2.core cref.toNat &&& 0x00800000#32) = 0#32 →
      ar3[cref.toNat + 3 + old_sz - 1]? = some 0xFFFFFFFF#32) ∧
    ((fullArenaHdrCore s2.core cref.toNat &&& 0x00800000#32) ≠ 0#32 →
      ar3[cref.toNat + 3 + old_sz - 1]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32) ∧
    (∀ i, i < cref.toNat ∨ cref.toNat + 3 + old_sz ≤ i → ar3[i]? = s2.core.arena[i]?)

private theorem otfs_large_hdr_ok {c : FullCfg} {s s2 : FullState}
    {ar1 ar_cur ar3_in : List (BitVec 32)} {cref : BitVec 32} {old_sz nsz : Nat}
    {origMap : List Nat} {R : Mem 64 → Prop} {ml3 : Mem 64} (sh0 : Bool)
    (har_len : s.core.arena.length = c.arena_cap) (har_c : ar_cur.length = c.arena_cap)
    (h3o : cref.toNat + 3 + old_sz ≤ c.arena_cap) (h4 : 4 ≤ old_sz)
    (hnsz3 : 3 ≤ nsz) (hnsz_lt : nsz < old_sz)
    (hlits_info : ∀ j < old_sz,
      (s.core.arena[cref.toNat + 3 + j]?.getD 0#32).toNat < 2 * s.core.cur_vars ∧
      s.core.arena[cref.toNat + 3 + j]?.getD 0#32 ≠ 0xFFFFFFFF#32)
    (hmapeq : ∀ k, k < nsz →
      ar_cur[cref.toNat + 3 + k]? = s.core.arena[cref.toNat + 3 + origMap[k]?.getD 0]?)
    (hout_m : ∀ q, q < cref.toNat + 4 ∨ cref.toNat + 3 + nsz ≤ q → ar_cur[q]? = ar1[q]?)
    (har1_q : ∀ q, 2 ≤ q → ar1[cref.toNat + 3 + q]? = s.core.arena[cref.toNat + 3 + q]?)
    (har1_s2 : ∀ i, i < cref.toNat + 3 ∨ cref.toNat + 5 ≤ i → ar1[i]? = s2.core.arena[i]?)
    (hhdr_eq : ar_cur[cref.toNat]? = some (fullArenaHdrCore s2.core cref.toNat))
    (hsh : (sh0 = true ∧ (fullArenaHdrCore s2.core cref.toNat &&& 0x00800000#32) = 0#32) ∨
      (sh0 = false ∧ (fullArenaHdrCore s2.core cref.toNat &&& 0x00800000#32) ≠ 0#32))
    (hm : (FullMem c { s2 with core := { s2.core with arena := ar3_in } } ⋆ R) ml3)
    (har3_def : ar3_in = if sh0 then
        (((ar_cur.set (cref.toNat + 2) (BitVec.ofNat 32 nsz)).set (cref.toNat + 1) 2#32).set
          cref.toNat (fullArenaHdrCore s2.core cref.toNat ||| 0x00800000#32)).set
          (cref.toNat + 3 + old_sz - 1) 0xFFFFFFFF#32
      else (ar_cur.set (cref.toNat + 2) (BitVec.ofNat 32 nsz)).set (cref.toNat + 1) 2#32) :
    OtfsHdrPost c s s2 R cref old_sz nsz origMap ml3 := by
  subst har3_def
  have hkeep_s0 : ∀ j, nsz ≤ j → j < old_sz →
      ar_cur[cref.toNat + 3 + j]?.getD 0xFFFFFFFF#32 =
        s.core.arena[cref.toNat + 3 + j]?.getD 0xFFFFFFFF#32 := fun j hj1 _ => by
    rw [hout_m _ (Or.inr (by omega)), har1_q j (by omega)]
  have hne_old : ∀ j, j < old_sz →
      (s.core.arena[cref.toNat + 3 + j]?.getD 0xFFFFFFFF#32) ≠ 0xFFFFFFFF#32 := fun j hj => by
    have hbd : cref.toNat + 3 + j < s.core.arena.length := by omega
    have hi := (hlits_info j hj).2
    rw [List.getElem?_eq_getElem hbd, Option.getD_some] at hi
    rw [List.getElem?_eq_getElem hbd, Option.getD_some]; exact hi
  cases sh0 <;> rcases hsh with ⟨hb, hshv⟩ | ⟨hb, hshv⟩ <;> try exact absurd hb (by decide)
  · let ar3 := (ar_cur.set (cref.toNat + 2) (BitVec.ofNat 32 nsz)).set (cref.toNat + 1) 2#32
    refine ⟨ar3, hm, by simp [ar3, har_c], by
      simp [hshv]; dsimp only [ar3]
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]; exact hhdr_eq,
      by dsimp only [ar3]
         rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by rw [har_c]; omega)],
      fun k hk => by dsimp only [ar3]; rw [List.getElem?_set_ne (by omega),
        List.getElem?_set_ne (by omega)]; exact hmapeq k hk,
      fun j hj1 hj2 => by dsimp only [ar3]; rw [List.getElem?_set_ne (by omega),
        List.getElem?_set_ne (by omega), hkeep_s0 j hj1 (by omega)]; exact hne_old j (by omega),
      fun h0 => absurd h0 hshv, fun _ => by
        dsimp only [ar3]; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
          show cref.toNat + 3 + old_sz - 1 = cref.toNat + 3 + (old_sz - 1) by omega,
          hkeep_s0 (old_sz - 1) (by omega) (by omega)]; exact hne_old (old_sz - 1) (by omega),
      fun i hi => by
        dsimp only [ar3]; rw [List.getElem?_set_ne (by rcases hi with h | h <;> omega),
          List.getElem?_set_ne (by rcases hi with h | h <;> omega),
          hout_m i (hi.imp (fun h => by omega) (fun h => by omega))]
        exact har1_s2 i (hi.imp (fun h => by omega) (fun h => by omega))⟩
  · let ar_a := (ar_cur.set (cref.toNat + 2) (BitVec.ofNat 32 nsz)).set (cref.toNat + 1) 2#32
    let ar_b := ar_a.set cref.toNat (fullArenaHdrCore s2.core cref.toNat ||| 0x00800000#32)
    let ar3 := ar_b.set (cref.toNat + 3 + old_sz - 1) 0xFFFFFFFF#32
    have har_al : ar_a.length = c.arena_cap := by simp [ar_a, har_c]
    refine ⟨ar3, hm, by simp [ar3, ar_b, har_al], by
      simp [hshv]; dsimp only [ar3, ar_b]
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by rw [har_al]; omega)],
      by dsimp only [ar3, ar_b, ar_a]
         rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
           List.getElem?_set_ne (by omega), List.getElem?_set_self (by rw [har_c]; omega)],
      fun k hk => by dsimp only [ar3, ar_b, ar_a]; rw [List.getElem?_set_ne (by omega),
        List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        List.getElem?_set_ne (by omega)]; exact hmapeq k hk,
      fun j hj1 hj2 => by dsimp only [ar3, ar_b, ar_a]; rw [List.getElem?_set_ne (by omega),
        List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        List.getElem?_set_ne (by omega), hkeep_s0 j hj1 (by omega)]; exact hne_old j (by omega),
      fun _ => by dsimp only [ar3]; rw [List.getElem?_set_self (by simp [ar_b, har_al]; omega)],
      fun hn => absurd hshv hn, fun i hi => by
        dsimp only [ar3, ar_b, ar_a]
        rw [List.getElem?_set_ne (by rcases hi with h | h <;> omega),
          List.getElem?_set_ne (by rcases hi with h | h <;> omega),
          List.getElem?_set_ne (by rcases hi with h | h <;> omega),
          List.getElem?_set_ne (by rcases hi with h | h <;> omega),
          hout_m i (hi.imp (fun h => by omega) (fun h => by omega))]
        exact har1_s2 i (hi.imp (fun h => by omega) (fun h => by omega))⟩

private theorem otfs_ar_idx3_lt_len {ar : List (BitVec 32)} {cref : BitVec 32}
    {cap old_sz j : Nat} (hcap : cap < 2 ^ 31 - 1) (har : ar.length = cap)
    (hold : cref.toNat + 3 + old_sz ≤ cap) (hj : j < old_sz) :
    (cref.setWidth 64 + 3#64 + (BitVec.ofNat 32 j).setWidth 64).toNat = cref.toNat + 3 + j ∧
    (cref.setWidth 64 + 3#64 + (BitVec.ofNat 32 j).setWidth 64).toNat < ar.length := by
  have hz := m5_otfs_bv_idx3_64 cref j (by omega) (by omega); exact ⟨hz, by rw [hz, har]; omega⟩

private theorem otfs_cr_end_z {ar0 : List (BitVec 32)} {cref : BitVec 32}
    {cap old_sz : Nat} (h3o : cref.toNat + 3 + old_sz ≤ cap) (h4_old : 4 ≤ old_sz)
    (hcap : cap < 2 ^ 31 - 1) (hcr2_z : (cref.setWidth 64 + 2#64).toNat = cref.toNat + 2)
    (hcr3_z : (cref.setWidth 64 + 3#64).toNat = cref.toNat + 3)
    (hcr2_bd : (cref.setWidth 64 + 2#64).toNat < ar0.length)
    (hsz32 : ar0[cref.toNat + 2]'(by rw [← hcr2_z]; exact hcr2_bd) = BitVec.ofNat 32 old_sz) :
    (cref.setWidth 64 + 3#64 +
      (ar0[(cref.setWidth 64 + 2#64).toNat]'hcr2_bd).setWidth 64 - 1#64).toNat =
      cref.toNat + 3 + old_sz - 1 := by
  have hsz_at : ar0[(cref.setWidth 64 + 2#64).toNat]'hcr2_bd = BitVec.ofNat 32 old_sz := by
    rw [m5_list_getElem_of_idx (hj := by rw [← hcr2_z]; exact hcr2_bd) hcr2_z]; exact hsz32
  have hz_s : ((BitVec.ofNat 32 old_sz).setWidth 64).toNat = old_sz := by
    rw [zext_toNat _ (by decide), bv32_ofNat_toNat (by omega)]
  have h1_64 : (1#64 : BitVec 64).toNat = 1 := rfl
  have hsum_z : (cref.setWidth 64 + 3#64 + (BitVec.ofNat 32 old_sz).setWidth 64).toNat =
      cref.toNat + 3 + old_sz := by rw [BitVec.toNat_add, hcr3_z, hz_s]; omega
  rw [hsz_at, BitVec.toNat_sub_of_le (by rw [BitVec.le_def, h1_64, hsum_z]; omega), h1_64, hsum_z]

private theorem otfs_large_loop2_init {c : FullCfg} {s : FullState}
    {cref l0 uip : BitVec 32} {old_sz : Nat}
    (har_len : s.core.arena.length = c.arena_cap)
    (h3o : cref.toNat + 3 + old_sz ≤ c.arena_cap) (h4_old : 4 ≤ old_sz)
    (hs01 : (l0 = s.core.arena[cref.toNat + 3]?.getD 0#32 ∧
        s.core.arena[cref.toNat + 4]?.getD 0#32 = uip) ∨
      (l0 = s.core.arena[cref.toNat + 4]?.getD 0#32 ∧
        s.core.arena[cref.toNat + 3]?.getD 0#32 = uip)) :
    let ar1 := (s.core.arena.set (cref.toNat + 3) l0).set (cref.toNat + 4) uip
    ∃ origMap, OtfsShrinkInv c s ar1 cref l0 uip old_sz (old_sz - 2) 2 1 ar1 origMap := by
  intro ar1
  have har1_len : ar1.length = c.arena_cap := by simp [ar1, List.length_set, har_len]
  have har1_0 : ar1[cref.toNat + 3]? = some l0 := by
    dsimp only [ar1]; rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega)]
  have hact0 : Full.otfsActCnt s.core cref.toNat 2 = 0 := by
    simp [Full.otfsActCnt, List.drop_eq_nil_of_le (show (List.range 2).length ≤ 2 by simp)]
  rcases hs01 with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · refine ⟨[0], har1_len, rfl, Nat.le_refl _, by omega, Nat.le_refl _, by rw [hact0], rfl,
      List.pairwise_singleton _ _, fun p hp => by simp only [List.mem_singleton] at hp; omega,
      Or.inl ⟨h0, h1, by decide, by decide⟩, fun _ _ _ => by omega, fun k hk => ?_, fun _ _ => rfl⟩
    have : k = 0 := by omega
    subst this; rw [Nat.add_zero, har1_0, h0, show ([0][0]? : Option Nat).getD 0 = 0 from rfl,
      Nat.add_zero, List.getElem?_eq_getElem (by omega : cref.toNat + 3 < s.core.arena.length),
      Option.getD_some]
  · refine ⟨[1], har1_len, rfl, Nat.le_refl _, by omega, Nat.le_refl _, by rw [hact0], rfl,
      List.pairwise_singleton _ _, fun p hp => by simp only [List.mem_singleton] at hp; omega,
      Or.inr ⟨h0, h1, by decide, by decide⟩, fun _ _ _ => by omega, fun k hk => ?_, fun _ _ => rfl⟩
    have : k = 0 := by omega
    subst this; rw [Nat.add_zero, har1_0, h0, show ([1][0]? : Option Nat).getD 0 = 1 from rfl,
      List.getElem?_eq_getElem (by omega : cref.toNat + 4 < s.core.arena.length), Option.getD_some]

private theorem otfs_large_j4_swap_wp {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {idx_u nsz old_sz hp_n : Nat} {s s3 : FullState} {cref l0 uip : BitVec 32}
    {ar_sw : List (BitVec 32)} {R : Mem 64 → Prop} {ml4 : Mem 64}
    (hlen3 : s3.LengthsOk c) (hw3 : FullAnalyzeSpecs.FullWitnessCutInv c F0 F_cur idx_u s3.core)
    (hnd3 : Full.FullArenaVarsNodup s3) (hcref3 : cref.toNat ∈ fullArenaClauseRefs s3)
    (hsz_3 : fullArenaClauseSize s3 cref.toNat = nsz)
    (hng_3 : fullArenaClauseGarb s3 cref.toNat = false)
    (har3_l0 : s3.core.arena[cref.toNat + 3]? = some l0)
    (hlits_3 : ∀ l ∈ fullArenaClauseLits s3 cref.toNat,
      l ≠ uip.toNat ∧ l ∈ fullArenaClauseLits s cref.toNat)
    (har3_s3_l : s3.core.arena.length = c.arena_cap) (_hnsz_lt : nsz < old_sz)
    (hcr4_z : (cref.setWidth 64 + 4#64).toNat = cref.toNat + 4) (hhp1 : 1 ≤ hp_n)
    (hhp_lt : hp_n < nsz) (h_hp_z : (cref.setWidth 64 + 3#64 +
      (BitVec.ofNat 32 hp_n).setWidth 64).toNat = cref.toNat + 3 + hp_n)
    (hbd_hp : (cref.setWidth 64 + 3#64 + (BitVec.ofNat 32 hp_n).setWidth 64).toNat <
      s3.core.arena.length) (hbd_4 : (cref.setWidth 64 + 4#64).toNat < s3.core.arena.length)
    (har_sw : ar_sw = (s3.core.arena.set (cref.setWidth 64 + 4#64).toNat
      (s3.core.arena[(cref.setWidth 64 + 3#64 +
        (BitVec.ofNat 32 hp_n).setWidth 64).toNat]'hbd_hp)).set (cref.setWidth 64 + 3#64 +
        (BitVec.ofNat 32 hp_n).setWidth 64).toNat
        (s3.core.arena[(cref.setWidth 64 + 4#64).toNat]'hbd_4))
    (hm_sw : (FullMem c { s3 with core := { s3.core with arena := ar_sw } } ⋆ R) ml4) :
    ∃ ar4 : List (BitVec 32),
      (FullMem c { s3 with core := { s3.core with arena := ar4 } } ⋆ R) ml4 ∧
      ar4.length = c.arena_cap ∧
      FullAnalyzeSpecs.FullWitnessCutInv c F0 F_cur idx_u { s3.core with arena := ar4 } ∧
      Full.FullArenaVarsNodup { s3 with core := { s3.core with arena := ar4 } } ∧
      fullArenaClauseRefsCore { s3.core with arena := ar4 } = fullArenaClauseRefsCore s3.core ∧
      fullArenaClauseSizeCore { s3.core with arena := ar4 } cref.toNat = nsz ∧
      fullArenaClauseGarbCore { s3.core with arena := ar4 } cref.toNat = false ∧
      ar4[cref.toNat + 3]? = some l0 ∧
      (∀ l ∈ fullArenaClauseLitsCore { s3.core with arena := ar4 } cref.toNat,
        l ≠ uip.toNat ∧ l ∈ fullArenaClauseLits s cref.toNat) := by
  have h4_s3 : cref.toNat + 4 < s3.core.arena.length := by rw [har3_s3_l]; omega
  have hhp_s3 : cref.toNat + 3 + hp_n < s3.core.arena.length := by rw [har3_s3_l]; omega
  have hget4 : s3.core.arena[(cref.setWidth 64 + 4#64).toNat]'hbd_4 =
      s3.core.arena[cref.toNat + 4]?.getD 0#32 := by
    rw [m5_list_getElem_of_idx (hj := h4_s3) hcr4_z, List.getElem?_eq_getElem h4_s3,
      Option.getD_some]
  have hget_hp : s3.core.arena[(cref.setWidth 64 + 3#64 +
      (BitVec.ofNat 32 hp_n).setWidth 64).toNat]'hbd_hp =
      s3.core.arena[cref.toNat + 3 + hp_n]?.getD 0#32 := by
    rw [m5_list_getElem_of_idx (hj := hhp_s3) h_hp_z, List.getElem?_eq_getElem hhp_s3,
      Option.getD_some]
  let ar4 := (s3.core.arena.set (cref.toNat + 4) (s3.core.arena[cref.toNat + 3 + hp_n]?.getD
    0#32)).set (cref.toNat + 3 + hp_n) (s3.core.arena[cref.toNat + 4]?.getD 0#32)
  have hsw_eq : ar_sw = ar4 := by rw [har_sw]; dsimp only [ar4]; rw [hget4, hget_hp, hcr4_z, h_hp_z]
  let s4 : FullState := { s3 with core := { s3.core with arena := ar4 } }
  obtain ⟨hw4, hrefs4, hsz4, hng4, hperm4, hother4⟩ :=
    fa_swapCl_preserves_fullWitnessCut hlen3.core_ok hw3 hcref3 (i := 1) (j := hp_n)
      (by rw [show fullArenaClauseSizeCore s3.core cref.toNat = nsz from hsz_3]; omega)
      (by rw [show fullArenaClauseSizeCore s3.core cref.toNat = nsz from hsz_3]; exact hhp_lt)
  have hnd4 : Full.FullArenaVarsNodup s4 := fun r hr hngr => by
    change r ∈ fullArenaClauseRefsCore s4.core at hr; rw [hrefs4] at hr
    by_cases hrc : r = cref.toNat
    · subst r; exact (hperm4.map (· / 2)).nodup_iff.mpr (hnd3 cref.toNat hr hng_3)
    · have ho := hother4 r hr hrc; change ((fullArenaClauseLitsCore s4.core r).map (· / 2)).Nodup
      rw [ho.2.2]; exact hnd3 r hr (by
        change fullArenaClauseGarbCore s3.core r = false; rw [← ho.2.1]; exact hngr)
  exact ⟨ar4, m5_fullMem_of_eq hm_sw (by rw [hsw_eq]) rfl, by simp [ar4, har3_s3_l], hw4, hnd4,
    hrefs4, hsz4.trans hsz_3, hng4.trans hng_3,
    by dsimp only [ar4]; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
       exact har3_l0, fun l hl => hlits_3 l (hperm4.mem_iff.mp hl)⟩

private theorem m5_otfs_j4_swap_wp {Γ : Env} {Q : Post [.bool]} {X : XPost}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {idx_u nsz old_sz hp_n : Nat}
    {s s3 : FullState} {cref l0 uip : BitVec 32} {R : Mem 64 → Prop} {ml3 : Mem 64}
    {J4 : Cont []}
    (hlen3 : s3.LengthsOk c)
    (hw3 : FullAnalyzeSpecs.FullWitnessCutInv c F0 F_cur idx_u s3.core)
    (hnd3 : Full.FullArenaVarsNodup s3) (hcref3 : cref.toNat ∈ fullArenaClauseRefsCore s3.core)
    (hsz_3 : fullArenaClauseSizeCore s3.core cref.toNat = nsz)
    (hng_3 : fullArenaClauseGarbCore s3.core cref.toNat = false)
    (har3_l0 : s3.core.arena[cref.toNat + 3]? = some l0)
    (hlits_3 : ∀ l ∈ fullArenaClauseLitsCore s3.core cref.toNat,
      l ≠ uip.toNat ∧ l ∈ fullArenaClauseLits s cref.toNat)
    (har3_s3_l : s3.core.arena.length = c.arena_cap)
    (hcap31 : c.arena_cap < 2 ^ 31 - 1) (har_le : s.core.arena_len ≤ c.arena_cap)
    (hold_bd : cref.toNat + 3 + old_sz ≤ s.core.arena_len)
    (hnsz_lt : nsz < old_sz) (hcr4_z : (cref.setWidth 64 + 4#64).toNat = cref.toNat + 4)
    (hcb1_eq : cref.setWidth 64 + 3#64 + 1#64 = cref.setWidth 64 + 4#64)
    (hhp1 : 1 ≤ hp_n) (hhp_lt : hp_n < nsz) (hm3' : (FullMem c s3 ⋆ R) ml3)
    (hJ4 : ∀ xs ml4, (∃ ar4 : List (BitVec 32),
      (FullMem c { s3 with core := { s3.core with arena := ar4 } } ⋆ R) ml4 ∧
      ar4.length = c.arena_cap ∧
      FullAnalyzeSpecs.FullWitnessCutInv c F0 F_cur idx_u { s3.core with arena := ar4 } ∧
      Full.FullArenaVarsNodup { s3 with core := { s3.core with arena := ar4 } } ∧
      fullArenaClauseRefsCore { s3.core with arena := ar4 } = fullArenaClauseRefsCore s3.core ∧
      fullArenaClauseSizeCore { s3.core with arena := ar4 } cref.toNat = nsz ∧
      fullArenaClauseGarbCore { s3.core with arena := ar4 } cref.toNat = false ∧
      ar4[cref.toNat + 3]? = some l0 ∧
      (∀ l ∈ fullArenaClauseLitsCore { s3.core with arena := ar4 } cref.toNat,
        l ≠ uip.toNat ∧ l ∈ fullArenaClauseLits s cref.toNat)) → J4 xs ml4) :
    wp Γ Q X
      (Expr.let_ (Op.mk (.cmp .ne (.bits 32) .bool rfl)
          (Arg.var (BitVec.ofNat 32 hp_n), Arg.imm 1, ())) fun p =>
        Expr.jnz (Arg.var p.fst)
          (Expr.let_ (Op.mk (.add (.bits 64))
              (Arg.var (cref.setWidth 64 + 3#64), Arg.imm 1, ())) fun p =>
           Expr.let_ (Op.mk (.mul (.bits 64)) (Arg.var p.fst, Arg.imm 4, ())) fun p =>
           Expr.let_ (Op.mk (.add (.bits 64)) (Arg.var c.pArena, Arg.var p.fst, ())) fun p =>
           Expr.load i32 (Arg.var p.fst) fun ld_8 =>
           Expr.let_ (Op.mk (.add (.bits 64))
             (Arg.var (cref.setWidth 64 + 3#64), Arg.imm 1, ())) fun p =>
           Expr.let_ (Op.mk (.mul (.bits 64)) (Arg.var p.fst, Arg.imm 4, ())) fun p =>
           Expr.let_ (Op.mk (.add (.bits 64)) (Arg.var c.pArena, Arg.var p.fst, ())) fun p =>
           Expr.let_ (Op.mk (.zext 32 64) (Arg.var (BitVec.ofNat 32 hp_n), ())) fun p_39 =>
           Expr.let_ (Op.mk (.add (.bits 64))
             (Arg.var (cref.setWidth 64 + 3#64), Arg.var p_39.fst, ())) fun p_40 =>
           Expr.let_ (Op.mk (.mul (.bits 64)) (Arg.var p_40.fst, Arg.imm 4, ())) fun p_41 =>
           Expr.let_ (Op.mk (.add (.bits 64)) (Arg.var c.pArena, Arg.var p_41.fst, ())) fun p_42 =>
           Expr.load i32 (Arg.var p_42.fst) fun ld_9 =>
           Expr.store (Arg.var ld_9) (Arg.var p.fst)
             (Expr.let_ (Op.mk (.zext 32 64) (Arg.var (BitVec.ofNat 32 hp_n), ())) fun p =>
              Expr.let_ (Op.mk (.add (.bits 64))
                (Arg.var (cref.setWidth 64 + 3#64), Arg.var p.fst, ())) fun p =>
              Expr.let_ (Op.mk (.mul (.bits 64)) (Arg.var p.fst, Arg.imm 4, ())) fun p =>
              Expr.let_ (Op.mk (.add (.bits 64)) (Arg.var c.pArena, Arg.var p.fst, ())) fun p =>
              Expr.store (Arg.var ld_8) (Arg.var p.fst) (Expr.jump J4 ())))
          (Expr.jump J4 ())) ml3 := by
  have h_hp_z := m5_otfs_bv_idx3_64 cref hp_n (by omega) (by omega)
  have hbd_hp : (cref.setWidth 64 + 3#64 + (BitVec.ofNat 32 hp_n).setWidth 64).toNat <
      s3.core.arena.length := by rw [h_hp_z, har3_s3_l]; omega
  have hbd_4 : (cref.setWidth 64 + 4#64).toNat < s3.core.arena.length := by
    rw [hcr4_z, har3_s3_l]; omega
  have hbd_cb1 : (BitVec.setWidth 64 cref + 3 + 1).toNat < s3.core.arena.length := by
    rw [show (3 : BitVec 64) = 3#64 from rfl, show (1 : BitVec 64) = 1#64 from rfl, hcb1_eq]
    exact hbd_4
  have hbd_hp_st : (cref.setWidth 64 + 3#64 + (BitVec.ofNat 32 hp_n).setWidth 64).toNat <
      (s3.core.arena.set (BitVec.setWidth 64 cref + 3 + 1).toNat
        (s3.core.arena[(cref.setWidth 64 + 3#64 +
          (BitVec.ofNat 32 hp_n).setWidth 64).toNat]'hbd_hp)).length := by
    rw [List.length_set]; exact hbd_hp
  fa_fast_steps
  · let ar_sw_raw :=
      List.set
        (s3.core.arena.set (BitVec.setWidth 64 cref + 3 + 1).toNat
          (s3.core.arena[(cref.setWidth 64 + 3#64 +
            (BitVec.ofNat 32 hp_n).setWidth 64).toNat]'hbd_hp))
        (cref.setWidth 64 + 3#64 + (BitVec.ofNat 32 hp_n).setWidth 64).toNat
        (s3.core.arena[(BitVec.setWidth 64 cref + 3 + 1).toNat]'hbd_cb1)
    let ar_sw :=
      List.set
        (s3.core.arena.set (cref.setWidth 64 + 4#64).toNat
          (s3.core.arena[(cref.setWidth 64 + 3#64 +
            (BitVec.ofNat 32 hp_n).setWidth 64).toNat]'hbd_hp))
        (cref.setWidth 64 + 3#64 + (BitVec.ofNat 32 hp_n).setWidth 64).toNat
        (s3.core.arena[(cref.setWidth 64 + 4#64).toNat]'hbd_4)
    have har_sw_eq : ar_sw_raw = ar_sw := by
      dsimp only [ar_sw_raw, ar_sw]
      have h31 : (BitVec.setWidth 64 cref + 3 + 1 : BitVec 64) = cref.setWidth 64 + 4#64 := hcb1_eq
      simp only [h31]
    have hm_sw' : (FullMem c { s3 with core := { s3.core with arena := ar_sw } } ⋆ R) _ :=
      m5_fullMem_of_eq (s1 := { s3 with core := { s3.core with arena := ar_sw_raw } })
        (by assumption) (congrArg (fun a => { s3.core with arena := a }) har_sw_eq) rfl
    exact hJ4 () _ (otfs_large_j4_swap_wp hlen3 hw3 hnd3 hcref3 hsz_3 hng_3
      har3_l0 hlits_3 har3_s3_l hnsz_lt hcr4_z hhp1 hhp_lt h_hp_z hbd_hp hbd_4 rfl hm_sw')
  · exact hJ4 () _ ⟨s3.core.arena,
      m5_fullMem_of_eq hm3' (by rcases s3 with ⟨⟨⟩, _⟩; rfl) rfl,
      har3_s3_l, hw3, hnd3, rfl, hsz_3, hng_3, har3_l0, hlits_3⟩

private theorem m5_otfs_j3_hdr_wp {Γ : Env} {Q : Post [.bool]} {X : XPost}
    {c : FullCfg} {s s2 : FullState} {ar1 ar_cur ar_in : List (BitVec 32)}
    {cref hdrV oldSzV : BitVec 32} {old_sz nsz : Nat} {origMap : List Nat}
    {R : Mem 64 → Prop} {ml_in : Mem 64} {J3 : Cont []}
    (har_len : s.core.arena.length = c.arena_cap) (har_c : ar_cur.length = c.arena_cap)
    (h3o : cref.toNat + 3 + old_sz ≤ c.arena_cap) (hcap31 : c.arena_cap < 2 ^ 31 - 1)
    (h4_old : 4 ≤ old_sz) (hnsz3 : 3 ≤ nsz) (hnsz_lt : nsz < old_sz)
    (hcr0_z : (cref.setWidth 64).toNat = cref.toNat)
    (hcr1_z : (cref.setWidth 64 + 1#64).toNat = cref.toNat + 1)
    (hcr2_z : (cref.setWidth 64 + 2#64).toNat = cref.toNat + 2)
    (hcr3_z : (cref.setWidth 64 + 3#64).toNat = cref.toNat + 3)
    (hhdr_v : hdrV = fullArenaHdrCore s2.core cref.toNat)
    (hold_v : oldSzV = BitVec.ofNat 32 old_sz)
    (har_in : ar_in = (ar_cur.set (cref.setWidth 64 + 2#64).toNat (BitVec.ofNat 32 nsz)).set
      (cref.setWidth 64 + 1#64).toNat 2#32)
    (hlits_info : ∀ j < old_sz,
      (s.core.arena[cref.toNat + 3 + j]?.getD 0#32).toNat < 2 * s.core.cur_vars ∧
      s.core.arena[cref.toNat + 3 + j]?.getD 0#32 ≠ 0xFFFFFFFF#32)
    (hmapeq : ∀ k, k < nsz →
      ar_cur[cref.toNat + 3 + k]? = s.core.arena[cref.toNat + 3 + origMap[k]?.getD 0]?)
    (hout_m : ∀ q, q < cref.toNat + 4 ∨ cref.toNat + 3 + nsz ≤ q → ar_cur[q]? = ar1[q]?)
    (har1_q : ∀ q, 2 ≤ q → ar1[cref.toNat + 3 + q]? = s.core.arena[cref.toNat + 3 + q]?)
    (har1_s2 : ∀ i, i < cref.toNat + 3 ∨ cref.toNat + 5 ≤ i → ar1[i]? = s2.core.arena[i]?)
    (hhdr_eq : ar_cur[cref.toNat]? = some (fullArenaHdrCore s2.core cref.toNat))
    (hm_in : (FullMem c { s2 with core := { s2.core with arena := ar_in } } ⋆ R) ml_in)
    (hJ3 : ∀ xs ml3, OtfsHdrPost c s s2 R cref old_sz nsz origMap ml3 → J3 xs ml3) :
    wp Γ Q X
      (Expr.let_ (Op.mk (.and (.bits 32)) (Arg.var hdrV, Arg.imm 8388608, ())) fun p_38 =>
        Expr.let_ (Op.mk (.cmp .eq (.bits 32) .bool rfl) (Arg.var p_38.fst, Arg.imm 0, ()))
          fun p_39 =>
        Expr.jnz (Arg.var p_39.fst)
          (Expr.let_ (Op.mk (.zext 32 64) (Arg.var cref, ())) fun p =>
           Expr.let_ (Op.mk (.mul (.bits 64)) (Arg.var p.fst, Arg.imm 4, ())) fun p =>
           Expr.let_ (Op.mk (.add (.bits 64)) (Arg.var c.pArena, Arg.var p.fst, ())) fun p =>
           Expr.let_ (Op.mk (.or (.bits 32)) (Arg.var hdrV, Arg.imm 8388608, ())) fun p_40 =>
           Expr.store (Arg.var p_40.fst) (Arg.var p.fst)
             (Expr.let_ (Op.mk (.zext 32 64) (Arg.var oldSzV, ())) fun p =>
              Expr.let_ (Op.mk (.add (.bits 64))
                (Arg.var (cref.setWidth 64 + 3#64), Arg.var p.fst, ())) fun p =>
              Expr.let_ (Op.mk (.sub (.bits 64)) (Arg.var p.fst, Arg.imm 1, ())) fun p =>
              Expr.let_ (Op.mk (.mul (.bits 64)) (Arg.var p.fst, Arg.imm 4, ())) fun p =>
              Expr.let_ (Op.mk (.add (.bits 64)) (Arg.var c.pArena, Arg.var p.fst, ())) fun p =>
              Expr.store (t := i32) (Arg.imm 4294967295) (Arg.var p.fst) (Expr.jump J3 ())))
          (Expr.jump J3 ())) ml_in := by
  subst hhdr_v hold_v
  have hcr_end_z : (cref.setWidth 64 + 3#64 + (BitVec.ofNat 32 old_sz).setWidth 64 - 1#64).toNat =
      cref.toNat + 3 + old_sz - 1 := by
    have hz : ((BitVec.ofNat 32 old_sz).setWidth 64).toNat = old_sz := by
      rw [zext_toNat _ (by decide), bv32_ofNat_toNat (by omega)]
    rw [BitVec.toNat_sub_of_le (by
      rw [BitVec.le_def, BitVec.toNat_add, hcr3_z, hz, Nat.mod_eq_of_lt (by omega),
        show (1#64).toNat = 1 from rfl]; omega),
      BitVec.toNat_add, hcr3_z, hz, Nat.mod_eq_of_lt (by omega), show (1#64).toNat = 1 from rfl]
  have har_in_len : ar_in.length = c.arena_cap := by simp [har_in, har_c]
  have har_c0_st : (cref.setWidth 64).toNat < ar_in.length := by
    rw [har_in_len, hcr0_z]; omega
  have har_end_st : (cref.setWidth 64 + 3#64 + (BitVec.ofNat 32 old_sz).setWidth 64 - 1#64).toNat <
      (ar_in.set (cref.setWidth 64).toNat
        (fullArenaHdrCore s2.core cref.toNat ||| 0x00800000#32)).length := by
    rw [List.length_set, har_in_len, hcr_end_z]; omega
  fa_fast_steps
  · have hsh0 : (fullArenaHdrCore s2.core cref.toNat &&& 0x00800000#32) = 0#32 := by assumption
    let ar_st0_raw := (ar_in.set (cref.setWidth 64).toNat
        (fullArenaHdrCore s2.core cref.toNat ||| 0x00800000#32)).set
      (cref.setWidth 64 + 3#64 + (BitVec.ofNat 32 old_sz).setWidth 64 - 1#64).toNat 0xFFFFFFFF#32
    let ar_st0 := (((ar_cur.set (cref.toNat + 2) (BitVec.ofNat 32 nsz)).set (cref.toNat + 1)
        2#32).set cref.toNat (fullArenaHdrCore s2.core cref.toNat ||| 0x00800000#32)).set
      (cref.toNat + 3 + old_sz - 1) 0xFFFFFFFF#32
    have har_st0 : ar_st0_raw = ar_st0 := by
      dsimp only [ar_st0_raw, ar_st0]; rw [har_in, hcr_end_z, hcr0_z, hcr1_z, hcr2_z]
    have hm_st0 : (FullMem c { s2 with core := { s2.core with arena := ar_st0 } } ⋆ R) _ :=
      m5_fullMem_of_eq (s1 := { s2 with core := { s2.core with arena := ar_st0_raw } })
        (by assumption) (congrArg (fun a => { s2.core with arena := a }) har_st0) rfl
    exact hJ3 () _ (otfs_large_hdr_ok true har_len har_c h3o h4_old hnsz3 hnsz_lt hlits_info
      hmapeq hout_m har1_q har1_s2 hhdr_eq (Or.inl ⟨rfl, hsh0⟩) hm_st0 rfl)
  · have hsh1 : (fullArenaHdrCore s2.core cref.toNat &&& 0x00800000#32) ≠ 0#32 := by assumption
    let ar_st1 := (ar_cur.set (cref.toNat + 2) (BitVec.ofNat 32 nsz)).set (cref.toNat + 1) 2#32
    have har_st1 : ar_in = ar_st1 := by rw [har_in, hcr2_z, hcr1_z]
    have hm_st1 : (FullMem c { s2 with core := { s2.core with arena := ar_st1 } } ⋆ R) _ :=
      m5_fullMem_of_eq (s1 := { s2 with core := { s2.core with arena := ar_in } })
        (by assumption) (congrArg (fun a => { s2.core with arena := a }) har_st1) rfl
    exact hJ3 () _ (otfs_large_hdr_ok false har_len har_c h3o h4_old hnsz3 hnsz_lt hlits_info
      hmapeq hout_m har1_q har1_s2 hhdr_eq (Or.inr ⟨rfl, hsh1⟩) hm_st1 rfl)

private theorem m5_otfs_p1_lv_pos {k : FullCoreState} {cref i_nat idx : Nat}
    {hidx : idx < k.arena.length} {hlvl_bd : (k.arena[idx]'hidx).toNat / 2 < k.lvl.length}
    (har_bd : cref + 3 + i_nat < k.arena.length)
    (hv_bd : (k.arena[cref + 3 + i_nat]?.getD 0#32).toNat / 2 < k.lvl.length)
    (hot_eq : k.arena[idx]'hidx = k.arena[cref + 3 + i_nat]'har_bd)
    (hpos : (0#32 : BitVec 32).toNat < (k.lvl[(k.arena[idx]'hidx).toNat / 2]'hlvl_bd).toNat) :
    0 < (k.lvl[(k.arena[cref + 3 + i_nat]?.getD 0#32).toNat / 2]?.getD 0#32).toNat := by
  rw [List.getElem?_eq_getElem har_bd, Option.getD_some,
    List.getElem?_eq_getElem (by rw [List.getElem?_eq_getElem har_bd, Option.getD_some] at hv_bd
                                 exact hv_bd), Option.getD_some]
  exact Nat.lt_of_lt_of_eq hpos (congrArg BitVec.toNat
    (m5_list_getElem_of_idx (congrArg (·.toNat / 2) hot_eq)))

private theorem m5_otfs_p1_lv_zero {k : FullCoreState} {cref i_nat idx : Nat}
    {hidx : idx < k.arena.length} {hlvl_bd : (k.arena[idx]'hidx).toNat / 2 < k.lvl.length}
    (har_bd : cref + 3 + i_nat < k.arena.length)
    (hv_bd : (k.arena[cref + 3 + i_nat]?.getD 0#32).toNat / 2 < k.lvl.length)
    (hot_eq : k.arena[idx]'hidx = k.arena[cref + 3 + i_nat]'har_bd)
    (hzero : ¬ (0#32 : BitVec 32).toNat < (k.lvl[(k.arena[idx]'hidx).toNat / 2]'hlvl_bd).toNat) :
    ¬ 0 < (k.lvl[(k.arena[cref + 3 + i_nat]?.getD 0#32).toNat / 2]?.getD 0#32).toNat :=
  fun hpos => by
    rw [List.getElem?_eq_getElem har_bd, Option.getD_some,
      List.getElem?_eq_getElem (by rw [List.getElem?_eq_getElem har_bd, Option.getD_some] at hv_bd
                                   exact hv_bd), Option.getD_some] at hpos
    exact hzero (Nat.lt_of_lt_of_eq hpos (congrArg BitVec.toNat
      (m5_list_getElem_of_idx (congrArg (·.toNat / 2) hot_eq.symm))))

private theorem m5_otfs_p1_brk {k : FullCoreState} {cref i_nat old_sz : Nat}
    (hi2 : 2 ≤ i_nat) (hilt : i_nat < old_sz)
    (hlv_pos : 0 < (k.lvl[(k.arena[cref + 3 + i_nat]?.getD 0#32).toNat / 2]?.getD 0#32).toNat)
    (hcnt_lt3 : 1 + Full.otfsActCnt k cref i_nat < 3)
    (hge3 : (3#32 : BitVec 32).toNat ≤ (1 + Full.otfsActCnt k cref i_nat + 1) % 2 ^ 32) :
    3 ≤ 1 + Full.otfsActCnt k cref old_sz := by
  have hnext : 1 + Full.otfsActCnt k cref (i_nat + 1) =
      1 + Full.otfsActCnt k cref i_nat + 1 := by
    rw [Full.otfsActCnt_succ hi2, ite_eq_left hlv_pos]; omega
  have hmono := m5_otfsActCnt_mono (k := k) (cref := cref) (i := i_nat + 1) (j := old_sz)
    (by omega) (by omega)
  simp only [BitVec.reduceToNat] at hge3; omega

private theorem m5_otfs_p1_inc {k : FullCoreState} {cref i_nat : Nat} (hi2 : 2 ≤ i_nat)
    (hlv_pos : 0 < (k.lvl[(k.arena[cref + 3 + i_nat]?.getD 0#32).toNat / 2]?.getD 0#32).toNat)
    (hcnt_lt3 : 1 + Full.otfsActCnt k cref i_nat < 3)
    (hlt : ¬ (3#32 : BitVec 32).toNat ≤ (1 + Full.otfsActCnt k cref i_nat + 1) % 2 ^ 32) :
    BitVec.ofNat 32 (1 + Full.otfsActCnt k cref i_nat) + 1 =
      BitVec.ofNat 32 (1 + Full.otfsActCnt k cref (i_nat + 1)) ∧
    1 + Full.otfsActCnt k cref (i_nat + 1) < 3 := by
  have hnext : 1 + Full.otfsActCnt k cref (i_nat + 1) =
      1 + Full.otfsActCnt k cref i_nat + 1 := by
    rw [Full.otfsActCnt_succ hi2, ite_eq_left hlv_pos]; omega
  simp only [BitVec.reduceToNat] at hlt
  refine ⟨BitVec.eq_of_toNat_eq ?_, by omega⟩
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    show (1 : BitVec 32).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), hnext]

private theorem m5_otfs_p2_lv_pos {k k2 : FullCoreState} {ar_cur : List (BitVec 32)}
    {cref i_nat idx : Nat} {hc_idx_bd : idx < ar_cur.length}
    {h2_lvl_bd : (ar_cur[idx]'hc_idx_bd).toNat / 2 < k2.lvl.length}
    (har_bd : cref + 3 + i_nat < k.arena.length)
    (hv_bd : (k.arena[cref + 3 + i_nat]?.getD 0#32).toNat / 2 < k.lvl.length)
    (hlvl_eq : k2.lvl = k.lvl)
    (hot_c_eq : ar_cur[idx]'hc_idx_bd = k.arena[cref + 3 + i_nat]'har_bd)
    (hpos : (0#32 : BitVec 32).toNat <
      (k2.lvl[(ar_cur[idx]'hc_idx_bd).toNat / 2]'h2_lvl_bd).toNat) :
    0 < (k.lvl[(k.arena[cref + 3 + i_nat]?.getD 0#32).toNat / 2]?.getD 0#32).toNat := by
  rw [List.getElem?_eq_getElem har_bd, Option.getD_some,
    List.getElem?_eq_getElem (by rw [List.getElem?_eq_getElem har_bd, Option.getD_some] at hv_bd
                                 exact hv_bd), Option.getD_some]
  exact Nat.lt_of_lt_of_eq hpos (congrArg BitVec.toNat
    (m5_list_getElem_of_list_idx hlvl_eq (congrArg (·.toNat / 2) hot_c_eq)))

private theorem m5_otfs_p2_skip_inv {c : FullCfg} {s s2 : FullState}
    {ar1 ar_cur : List (BitVec 32)} {cref l0 uip : BitVec 32} {old_sz i_nat nsz idx : Nat}
    {origMap : List Nat} {hc_idx_bd : idx < ar_cur.length}
    {h2_lvl_bd : (ar_cur[idx]'hc_idx_bd).toNat / 2 < s2.core.lvl.length}
    (hinv : OtfsShrinkInv c s ar1 cref l0 uip old_sz (old_sz - i_nat) i_nat nsz ar_cur origMap)
    (hilt : i_nat < old_sz) (har_bd : cref.toNat + 3 + i_nat < s.core.arena.length)
    (hv_bd : (s.core.arena[cref.toNat + 3 + i_nat]?.getD 0#32).toNat / 2 < s.core.lvl.length)
    (hlvl_eq : s2.core.lvl = s.core.lvl)
    (hot_c_eq : ar_cur[idx]'hc_idx_bd = s.core.arena[cref.toNat + 3 + i_nat]'har_bd)
    (hzero : ¬ (0#32 : BitVec 32).toNat <
      (s2.core.lvl[(ar_cur[idx]'hc_idx_bd).toNat / 2]'h2_lvl_bd).toNat) :
    OtfsShrinkInv c s ar1 cref l0 uip old_sz (old_sz - (i_nat + 1)) (i_nat + 1) nsz
      ar_cur origMap := by
  obtain ⟨har_c, _, hi2, hile, hns1, hact, hlm, hpw, hlt_m, h01, hcov, hmapeq, hout_m⟩ := hinv
  have hlv_0 : ¬ 0 < (s.core.lvl[(s.core.arena[cref.toNat + 3 + i_nat]?.getD 0#32).toNat / 2]?.getD
      0#32).toNat := fun hpos => by
    rw [List.getElem?_eq_getElem har_bd, Option.getD_some,
      List.getElem?_eq_getElem (by rw [List.getElem?_eq_getElem har_bd, Option.getD_some] at hv_bd
                                   exact hv_bd), Option.getD_some] at hpos
    exact hzero (Nat.lt_of_lt_of_eq hpos (congrArg BitVec.toNat
      (m5_list_getElem_of_list_idx hlvl_eq.symm (congrArg (·.toNat / 2) hot_c_eq.symm))))
  exact ⟨har_c, rfl, by omega, by omega, hns1,
    by rw [hact, Full.otfsActCnt_succ hi2, ite_eq_right hlv_0, Nat.add_zero],
    hlm, hpw, fun p hp => Nat.lt_succ_of_lt (hlt_m p hp), h01,
    fun p hp2 hplt hpos => by
      by_cases hpi : p = i_nat
      · subst p; exact absurd hpos hlv_0
      · exact hcov p hp2 (by omega) hpos, hmapeq, hout_m⟩

private theorem otfs_large_loop1_step_bds {c : FullCfg} {s : FullState} {cref : BitVec 32}
    {old_sz i_nat : Nat} (hcap : c.arena_cap < 2 ^ 31 - 1)
    (hcv_le : s.core.cur_vars ≤ c.max_vars) (hlvl_len : s.core.lvl.length = c.max_vars)
    (har_len : s.core.arena.length = c.arena_cap) (hold_bd : cref.toNat + 3 + old_sz ≤ c.arena_cap)
    (hilt : i_nat < old_sz) (hlits_info : ∀ j < old_sz,
      (s.core.arena[cref.toNat + 3 + j]?.getD 0#32).toNat < 2 * s.core.cur_vars ∧
      s.core.arena[cref.toNat + 3 + j]?.getD 0#32 ≠ 0xFFFFFFFF#32) :
    ∃ (har_bd : cref.toNat + 3 + i_nat < s.core.arena.length)
      (hz_bd : (cref.setWidth 64 + 3#64 + (BitVec.ofNat 32 i_nat).setWidth 64).toNat <
        s.core.arena.length)
      (hc_bd : (cref.toNat + BitVec.toNat (3 : BitVec 64) + i_nat % 2 ^ 32) % 2 ^ 64 <
        s.core.arena.length),
      (cref.toNat + BitVec.toNat (3 : BitVec 64) + i_nat % 2 ^ 32) % 2 ^ 64 =
        cref.toNat + 3 + i_nat ∧
      s.core.arena[(cref.toNat + BitVec.toNat (3 : BitVec 64) +
        i_nat % 2 ^ 32) % 2 ^ 64]'hc_bd = s.core.arena[cref.toNat + 3 + i_nat]'har_bd ∧
      (s.core.arena[(cref.toNat + BitVec.toNat (3 : BitVec 64) +
        i_nat % 2 ^ 32) % 2 ^ 64]'hc_bd).toNat / 2 < s.core.cur_vars ∧
      ((s.core.arena[(cref.setWidth 64 + 3#64 +
        (BitVec.ofNat 32 i_nat).setWidth 64).toNat]'hz_bd >>> 1).setWidth 64).toNat <
        s.core.lvl.length ∧
      (s.core.arena[cref.toNat + 3 + i_nat]?.getD 0#32).toNat / 2 < s.core.lvl.length := by
  have hc_idx : (cref.toNat + BitVec.toNat (3 : BitVec 64) + i_nat % 2 ^ 32) % 2 ^ 64 =
      cref.toNat + 3 + i_nat := by simp only [show BitVec.toNat (3 : BitVec 64) = 3 from rfl]; omega
  have har_bd : cref.toNat + 3 + i_nat < s.core.arena.length := by rw [har_len]; omega
  have hz := m5_otfs_bv_idx3_64 cref i_nat (by omega) (by omega)
  have hz_bd : (cref.setWidth 64 + 3#64 + (BitVec.ofNat 32 i_nat).setWidth 64).toNat <
      s.core.arena.length := by rw [hz]; exact har_bd
  have hc_bd : (cref.toNat + BitVec.toNat (3 : BitVec 64) + i_nat % 2 ^ 32) % 2 ^ 64 <
      s.core.arena.length := by rw [hc_idx]; exact har_bd
  have hot_eq : s.core.arena[(cref.toNat + BitVec.toNat (3 : BitVec 64) +
      i_nat % 2 ^ 32) % 2 ^ 64]'hc_bd = s.core.arena[cref.toNat + 3 + i_nat]'har_bd :=
    m5_list_getElem_of_idx hc_idx
  have hi_lit := (hlits_info i_nat hilt).1
  rw [List.getElem?_eq_getElem har_bd, Option.getD_some] at hi_lit
  exact ⟨har_bd, hz_bd, hc_bd, hc_idx, hot_eq,
    by rw [hot_eq]; exact Nat.div_lt_of_lt_mul hi_lit,
    by rw [bv_c0_zext32_64, bv32_lshr_1, hlvl_len, m5_list_getElem_of_idx (hj := har_bd) hz]
       exact Nat.lt_of_lt_of_le (Nat.div_lt_of_lt_mul hi_lit) hcv_le,
    by rw [hlvl_len, List.getElem?_eq_getElem har_bd, Option.getD_some]
       exact Nat.lt_of_lt_of_le (Nat.div_lt_of_lt_mul hi_lit) hcv_le⟩

private theorem otfs_large_loop2_step_bds {c : FullCfg} {s s2 : FullState}
    {ar1 ar_cur : List (BitVec 32)} {cref l0 uip : BitVec 32}
    {old_sz i_nat nsz : Nat} {origMap : List Nat}
    (hcap : c.arena_cap < 2 ^ 31 - 1) (h3o : cref.toNat + 3 + old_sz ≤ c.arena_cap)
    (hcv_le : s.core.cur_vars ≤ c.max_vars) (hlvl_len : s.core.lvl.length = c.max_vars)
    (hs2_lvl_l : s2.core.lvl.length = c.max_vars) (har_len : s.core.arena.length = c.arena_cap)
    (hinv : OtfsShrinkInv c s ar1 cref l0 uip old_sz (old_sz - i_nat) i_nat nsz ar_cur origMap)
    (hilt : i_nat < old_sz)
    (har1_q : ∀ q, 2 ≤ q → ar1[cref.toNat + 3 + q]? = s.core.arena[cref.toNat + 3 + q]?)
    (hlits_info : ∀ j < old_sz,
      (s.core.arena[cref.toNat + 3 + j]?.getD 0#32).toNat < 2 * s.core.cur_vars ∧
      s.core.arena[cref.toNat + 3 + j]?.getD 0#32 ≠ 0xFFFFFFFF#32) :
    ∃ (hc_bd : (cref.toNat + BitVec.toNat (3 : BitVec 64) + i_nat % 2 ^ 32) % 2 ^ 64 <
        ar_cur.length)
      (hz_bd : (cref.setWidth 64 + 3#64 + (BitVec.ofNat 32 i_nat).setWidth 64).toNat <
        ar_cur.length)
      (_hnsz_bd : (cref.setWidth 64 + 3#64 + (BitVec.ofNat 32 nsz).setWidth 64).toNat <
        ar_cur.length)
      (har_bd : cref.toNat + 3 + i_nat < s.core.arena.length),
      nsz < i_nat ∧
      (cref.toNat + BitVec.toNat (3 : BitVec 64) + i_nat % 2 ^ 32) % 2 ^ 64 =
        cref.toNat + 3 + i_nat ∧
      (cref.setWidth 64 + 3#64 + (BitVec.ofNat 32 i_nat).setWidth 64).toNat =
        cref.toNat + 3 + i_nat ∧
      (cref.setWidth 64 + 3#64 + (BitVec.ofNat 32 nsz).setWidth 64).toNat =
        cref.toNat + 3 + nsz ∧
      ar_cur[(cref.toNat + BitVec.toNat (3 : BitVec 64) +
        i_nat % 2 ^ 32) % 2 ^ 64]'hc_bd = s.core.arena[cref.toNat + 3 + i_nat]'har_bd ∧
      ar_cur[(cref.setWidth 64 + 3#64 +
        (BitVec.ofNat 32 i_nat).setWidth 64).toNat]'hz_bd =
        s.core.arena[cref.toNat + 3 + i_nat]'har_bd ∧
      (ar_cur[(cref.toNat + BitVec.toNat (3 : BitVec 64) +
        i_nat % 2 ^ 32) % 2 ^ 64]'hc_bd).toNat / 2 < s2.core.lvl.length ∧
      (s.core.arena[cref.toNat + 3 + i_nat]?.getD 0#32).toNat / 2 < s.core.lvl.length := by
  have har_c := hinv.1; have hi2 := hinv.2.2.1
  have hnsz_lt_i : nsz < i_nat := by
    have := Full.otfsActCnt_le s.core cref.toNat i_nat; rw [hinv.2.2.2.2.2.1]; omega
  have hc_idx : (cref.toNat + BitVec.toNat (3 : BitVec 64) + i_nat % 2 ^ 32) % 2 ^ 64 =
      cref.toNat + 3 + i_nat := by simp only [show BitVec.toNat (3 : BitVec 64) = 3 from rfl]; omega
  have hc_z := m5_otfs_bv_idx3_64 cref i_nat (by omega) (by omega)
  have hnsz_z := m5_otfs_bv_idx3_64 cref nsz (by omega) (by omega)
  have har_bd : cref.toNat + 3 + i_nat < s.core.arena.length := by omega
  have hc_bd : (cref.toNat + BitVec.toNat (3 : BitVec 64) + i_nat % 2 ^ 32) % 2 ^ 64 <
      ar_cur.length := by rw [hc_idx, har_c]; omega
  have hz_bd : (cref.setWidth 64 + 3#64 + (BitVec.ofNat 32 i_nat).setWidth 64).toNat <
      ar_cur.length := by rw [hc_z, har_c]; omega
  have hnsz_bd : (cref.setWidth 64 + 3#64 + (BitVec.ofNat 32 nsz).setWidth 64).toNat <
      ar_cur.length := by rw [hnsz_z, har_c]; omega
  have hout := hinv.2.2.2.2.2.2.2.2.2.2.2.2
  have hot_c_eq : ar_cur[(cref.toNat + BitVec.toNat (3 : BitVec 64) +
      i_nat % 2 ^ 32) % 2 ^ 64]'hc_bd = s.core.arena[cref.toNat + 3 + i_nat]'har_bd := by
    have ho := hout (cref.toNat + 3 + i_nat) (Or.inr (by omega))
    rw [har1_q i_nat hi2, List.getElem?_eq_getElem har_bd,
      List.getElem?_eq_getElem (by rw [har_c]; omega)] at ho
    exact (m5_list_getElem_of_idx hc_idx).trans (Option.some.inj ho)
  have hot_z_eq : ar_cur[(cref.setWidth 64 + 3#64 +
      (BitVec.ofNat 32 i_nat).setWidth 64).toNat]'hz_bd =
      s.core.arena[cref.toNat + 3 + i_nat]'har_bd :=
    (m5_list_getElem_of_idx (hc_z.trans hc_idx.symm)).trans hot_c_eq
  have hi_lit := (hlits_info i_nat hilt).1
  rw [List.getElem?_eq_getElem har_bd, Option.getD_some] at hi_lit
  exact ⟨hc_bd, hz_bd, hnsz_bd, har_bd, hnsz_lt_i, hc_idx, hc_z, hnsz_z, hot_c_eq, hot_z_eq,
    by rw [hot_c_eq, hs2_lvl_l]; exact Nat.lt_of_lt_of_le (Nat.div_lt_of_lt_mul hi_lit) hcv_le,
    by rw [hlvl_len, List.getElem?_eq_getElem har_bd, Option.getD_some]
       exact Nat.lt_of_lt_of_le (Nat.div_lt_of_lt_mul hi_lit) hcv_le⟩

private theorem otfs_large_swap1_nl1 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {idx_u nsz : Nat} {s s4 : FullState} {ar4 : List (BitVec 32)} {cref : BitVec 32}
    (hw4 : FullAnalyzeSpecs.FullWitnessCutInv c F0 F_cur idx_u s4.core)
    (hcv4 : s4.core.cur_vars = s.core.cur_vars)
    (hs4_ar : s4.core.arena = ar4) (h2cv_lt : 2 * s.core.cur_vars < 2 ^ 31 - 1)
    (hcref4 : cref.toNat ∈ fullArenaClauseRefsCore s4.core)
    (hng4 : fullArenaClauseGarbCore s4.core cref.toNat = false)
    (hsz4 : fullArenaClauseSizeCore s4.core cref.toNat = nsz) (hnsz3 : 3 ≤ nsz)
    (har4_l : ar4.length = c.arena_cap) (hcap : cref.toNat + 3 + nsz ≤ c.arena_cap)
    (h4bd : cref.toNat + 4 < ar4.length) :
    (ar4[cref.toNat + 4]?.getD 0#32).toNat < 2 * s.core.cur_vars ∧
    ((ar4[cref.toNat + 4]'h4bd &&& 0x7FFFFFFF#32) = ar4[cref.toNat + 4]'h4bd ∧
     ((ar4[cref.toNat + 4]'h4bd &&& 0x7FFFFFFF#32) &&& 0x80000000#32) = 0#32 ∧
     (ar4[cref.toNat + 4]'h4bd &&& 0x80000000#32) = 0#32) := by
  have hm_mem : (ar4[cref.toNat + 4]?.getD 0#32).toNat ∈
      fullArenaClauseLitsCore s4.core cref.toNat := by
    simp only [fullArenaClauseLitsCore, List.mem_map]
    refine ⟨ar4[cref.toNat + 4]'h4bd, List.mem_iff_getElem.mpr ⟨1,
      by rw [List.length_take, List.length_drop, hs4_ar, hsz4, har4_l]; omega,
      by simp only [List.getElem_take, List.getElem_drop, Nat.add_assoc]
         exact m5_list_getElem_of_list_idx hs4_ar rfl⟩,
      by rw [List.getElem?_eq_getElem h4bd, Option.getD_some]⟩
  have hlt : (ar4[cref.toNat + 4]?.getD 0#32).toNat < 2 * s.core.cur_vars :=
    hcv4 ▸ hw4.arena.lits_lt _ hcref4 hng4 _ hm_mem
  refine ⟨hlt, bv32_lit_lo31_props (l := ar4[cref.toNat + 4]'h4bd) ?_⟩
  rw [List.getElem?_eq_getElem h4bd, Option.getD_some] at hlt; omega

private theorem otfs_large_nodup_same_arena {s4 s5 : FullState} {ar : List (BitVec 32)}
    (hs5_ar : s5.core.arena = ar) (hs5_al : s5.core.arena_len = s4.core.arena_len)
    (hs4_ar : s4.core.arena = ar) (hnd4 : Full.FullArenaVarsNodup s4) :
    Full.FullArenaVarsNodup s5 := fun r hr hngr => by
  have hrf : fullArenaClauseRefsCore s5.core = fullArenaClauseRefsCore s4.core := by
    simp [fullArenaClauseRefsCore, hs5_ar, hs5_al, hs4_ar]
  have hgr : fullArenaClauseGarb s4 r = false := by
    dsimp only [fullArenaClauseGarb, fullArenaClauseGarbCore, fullArenaHdrCore] at hngr ⊢
    rw [hs4_ar, ← hs5_ar]; exact hngr
  change r ∈ fullArenaClauseRefsCore s5.core at hr; rw [hrf] at hr
  change ((fullArenaClauseLitsCore s5.core r).map (· / 2)).Nodup
  have hl : fullArenaClauseLitsCore s5.core r = fullArenaClauseLitsCore s4.core r := by
    simp [fullArenaClauseLitsCore, fullArenaClauseSizeCore, hs5_ar, hs4_ar]
  rw [hl]; exact hnd4 r hr hgr

private theorem m5_otfs_oom_early_wp {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut idx_u : Nat} {s s_d : FullState} {cref : BitVec 32}
    {R : Mem 64 → Prop} {Q : Post [.bool]} {m_o : Mem 64}
    {wv_d ws_d : List (BitVec 32)} {wl_d : Nat} {wu_d : BitVec 64} {wso_d : List (BitVec 32)}
    (hsd_c : s_d.core =
      { s.core with wvec := wv_d, wstk := ws_d, wlen := wl_d, wusable := wu_d })
    (hsd_sc : s_d.scratch = { s.scratch with wsort := wso_d })
    (hlen_d : s_d.LengthsOk c) (hw_d : Full.FullWitnessCutInv c F0 F_cur cut s_d.core)
    (hnd : Full.FullArenaVarsNodup s) (hiu_cut : idx_u < cut)
    (hm_o : (FullMem c { s_d with core := { s_d.core with oom := 1#64 } } ⋆ R) m_o)
    (hQ : ∀ (ok : Bool) arena' wvec' wstk' wlen' wu' oom' sc' m',
      let s' : FullState :=
        { s with
          core := { s.core with arena := arena', wvec := wvec', wstk := wstk', wlen := wlen',
                                wusable := wu', oom := oom' }
          scratch := sc' }
      s'.LengthsOk c → Full.FullWitnessCutInv c F0 F_cur idx_u s'.core →
      Full.FullArenaVarsNodup s' →
      FullExtScratchPres s s' → sc'.work_stk1 = s.scratch.work_stk1 →
      sc'.work_stk2 = s.scratch.work_stk2 → sc'.res_sz = s.scratch.res_sz →
      fullArenaClauseRefs s' = fullArenaClauseRefs s →
      (ok = true → cref.toNat ∈ fullArenaClauseRefs s' ∧
        fullArenaClauseGarb s' cref.toNat = false ∧
        ∀ l ∈ fullArenaClauseLits s' cref.toNat, s'.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
          ((s'.core.lvl[l / 2]?.getD 0#32).toNat = s'.core.cur_level →
            ∃ m < idx_u, (s'.core.trl[m]?.getD 0#32).toNat = l ^^^ 1)) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    Q (false, ()) m_o := by
  let k_o : FullCoreState :=
    { s.core with wvec := wv_d, wstk := ws_d, wlen := wl_d, wusable := wu_d, oom := 1#64 }
  let sc_o : FullScratch := { s.scratch with wsort := wso_d }
  let s_o : FullState := { s with core := k_o, scratch := sc_o }
  have hk_eq : { s_d.core with oom := 1#64 } = k_o := by rw [hsd_c]
  have hsc_eq : s_d.scratch = sc_o := hsd_sc
  have hlen_o : s_o.LengthsOk c := by
    change ({ s with core := k_o, scratch := sc_o } : FullState).LengthsOk c
    rw [← hk_eq, ← hsc_eq]
    exact ⟨{ hlen_d.core_ok with }, hlen_d.scratch_ok⟩
  have hw_o : Full.FullWitnessCutInv c F0 F_cur idx_u s_o.core := by
    change Full.FullWitnessCutInv c F0 F_cur idx_u k_o; rw [← hk_eq]
    exact m5_canonCut_shrink_cut (m5_canonCut_with_oom hw_d 1#64) (Nat.le_of_lt hiu_cut)
  have hnd_o : Full.FullArenaVarsNodup s_o := hnd
  have hm_o' : (FullMem c s_o ⋆ R) m_o := m5_fullMem_of_eq hm_o hk_eq hsc_eq
  exact hQ false s.core.arena wv_d ws_d wl_d wu_d 1#64 sc_o m_o hlen_o hw_o hnd_o
    ⟨rfl, rfl⟩ rfl rfl rfl rfl (fun hc => by cases hc) hm_o'

private theorem m5_otfs_fin_wp {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut idx_u : Nat} {s s_p s2 s4 : FullState} {ar1 ar4 wv2 ws2 ws_f : List (BitVec 32)}
    {wl_p : Nat} {wu2 : BitVec 64} {wso_p : List (BitVec 32)} {cref uip : BitVec 32}
    {R : Mem 64 → Prop} {Q : Post [.bool]} {m_sc : Mem 64}
    (hlen : s.LengthsOk c) (hw : FullAnalyzeSpecs.FullWitnessCutInv c F0 F_cur cut s.core)
    (hcref : cref.toNat ∈ fullArenaClauseRefs s) (hng : fullArenaClauseGarb s cref.toNat = false)
    (hiu_cut : idx_u < cut) (hiu_te : idx_u < s.core.trail_end)
    (ht_u : (s.core.trl[idx_u]?.getD 0#32).toNat = uip.toNat)
    (hr_u : s.core.rsns[uip.toNat / 2]?.getD 0xFFFFFFFF#32 = cref)
    (hsp_c : s_p.core.oom = s.core.oom)
    (hs2_base : s2.core =
      { s.core with arena := ar1, wvec := wv2, wstk := ws2, wlen := wl_p,
                    wusable := wu2, oom := s.core.oom })
    (hs4_c : s4.core = { s2.core with arena := ar4 })
    (hs4_sc : s4.scratch = { s.scratch with wsort := wso_p })
    (hw4 : FullAnalyzeSpecs.FullWitnessCutInv c F0 F_cur idx_u s4.core)
    (hlen4 : s4.LengthsOk c) (hnd4 : Full.FullArenaVarsNodup s4)
    (hrefs4 : fullArenaClauseRefs s4 = fullArenaClauseRefs s)
    (hcref4 : cref.toNat ∈ fullArenaClauseRefsCore s4.core)
    (hng4 : fullArenaClauseGarb s4 cref.toNat = false)
    (hlits4 : ∀ l ∈ fullArenaClauseLits s4 cref.toNat,
      l ≠ uip.toNat ∧ l ∈ fullArenaClauseLits s cref.toNat)
    (hws_fl : ws_f.length = c.wcap)
    (hmw_f : ModeWatchesInv F_cur { s4.core with wstk := ws_f })
    (hm_sc : (FullMem c
      { s4 with core := { s4.core with wstk := ws_f }
                scratch := { s4.scratch with otfs_cnt := s4.scratch.otfs_cnt + 1#64 } } ⋆ R) m_sc)
    (hQ : ∀ (ok : Bool) arena' wvec' wstk' wlen' wu' oom' sc' m',
      let s' : FullState :=
        { s with
          core := { s.core with arena := arena', wvec := wvec', wstk := wstk', wlen := wlen',
                                wusable := wu', oom := oom' }
          scratch := sc' }
      s'.LengthsOk c → Full.FullWitnessCutInv c F0 F_cur idx_u s'.core →
      Full.FullArenaVarsNodup s' →
      FullExtScratchPres s s' → sc'.work_stk1 = s.scratch.work_stk1 →
      sc'.work_stk2 = s.scratch.work_stk2 → sc'.res_sz = s.scratch.res_sz →
      fullArenaClauseRefs s' = fullArenaClauseRefs s →
      (ok = true → cref.toNat ∈ fullArenaClauseRefs s' ∧
        fullArenaClauseGarb s' cref.toNat = false ∧
        ∀ l ∈ fullArenaClauseLits s' cref.toNat, s'.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
          ((s'.core.lvl[l / 2]?.getD 0#32).toNat = s'.core.cur_level →
            ∃ m < idx_u, (s'.core.trl[m]?.getD 0#32).toNat = l ^^^ 1)) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    Q (true, ()) m_sc := by
  let _ := hsp_c
  let k_fin : FullCoreState :=
    { s.core with arena := ar4, wvec := wv2, wstk := ws_f, wlen := wl_p, wusable := wu2,
                  oom := s.core.oom }
  let sc_fin : FullScratch :=
    { s.scratch with wsort := wso_p, otfs_cnt := s.scratch.otfs_cnt + 1#64 }
  let s_fin : FullState := { s with core := k_fin, scratch := sc_fin }
  have hk_eq : k_fin = { s4.core with wstk := ws_f } := by
    dsimp only [k_fin]; rw [hs4_c, hs2_base]
  have hsc_eq : sc_fin = { s4.scratch with otfs_cnt := s4.scratch.otfs_cnt + 1#64 } := by
    dsimp only [sc_fin]; rw [hs4_sc]
  have hm_f' : (FullMem c s_fin ⋆ R) m_sc := m5_fullMem_of_eq hm_sc hk_eq.symm hsc_eq.symm
  have hw_f_ana : FullAnalyzeSpecs.FullWitnessCutInv c F0 F_cur idx_u s_fin.core := by
    change FullAnalyzeSpecs.FullWitnessCutInv c F0 F_cur idx_u k_fin; rw [hk_eq]
    exact { hw4 with arena := { hw4.arena with len_ok := hw4.arena.len_ok }, watches := hmw_f }
  have hlen_f : s_fin.LengthsOk c := by
    change ({ s with core := k_fin, scratch := sc_fin } : FullState).LengthsOk c; rw [hk_eq, hsc_eq]
    exact ⟨{ hlen4.core_ok with wstk_len_arr := hws_fl }, { hlen4.scratch_ok with }⟩
  have hnd_f : Full.FullArenaVarsNodup s_fin :=
    otfs_large_nodup_same_arena (s4 := s4) (s5 := s_fin) (ar := ar4)
      rfl (by change k_fin.arena_len = s4.core.arena_len; rw [hk_eq])
      (by rw [hs4_c]) hnd4
  have hrefs_s4 : fullArenaClauseRefs s_fin = fullArenaClauseRefs s4 := by
    change fullArenaClauseRefsCore k_fin = fullArenaClauseRefsCore s4.core; rw [hk_eq]; rfl
  have hcref_f : cref.toNat ∈ fullArenaClauseRefs s_fin := by
    change cref.toNat ∈ fullArenaClauseRefsCore s_fin.core
    change cref.toNat ∈ fullArenaClauseRefsCore s4.core at hcref4
    rw [show fullArenaClauseRefsCore s_fin.core = fullArenaClauseRefsCore s4.core from hrefs_s4]
    exact hcref4
  have hng_f : fullArenaClauseGarb s_fin cref.toNat = false := by
    dsimp only [fullArenaClauseGarb, fullArenaClauseGarbCore, fullArenaHdrCore, s_fin, k_fin]
      at hng4 ⊢
    rw [show s4.core.arena = ar4 by rw [hs4_c]] at hng4; exact hng4
  have hlits_f := otfs_large_fin hlen hw hcref hng hiu_cut hiu_te ht_u hr_u (s' := s_fin)
    (by dsimp only [s_fin, k_fin]) (by dsimp only [s_fin, k_fin]) (by dsimp only [s_fin, k_fin])
    (by dsimp only [s_fin, k_fin]) (fun l hl => hlits4 l (by
      dsimp only [fullArenaClauseLits, fullArenaClauseLitsCore, fullArenaClauseSizeCore, s_fin,
        k_fin] at hl ⊢
      rw [show s4.core.arena = ar4 by rw [hs4_c]]; exact hl))
  exact hQ true ar4 wv2 ws_f wl_p wu2 s.core.oom sc_fin m_sc hlen_f
    (m5_anaCut_to_canonCut hw_f_ana (by dsimp only [s_fin, k_fin]; omega)) hnd_f
    ⟨rfl, rfl⟩ rfl rfl rfl (hrefs_s4.trans hrefs4)
    (fun _ => ⟨hcref_f, hng_f, fun l hl => let ⟨_, _, hv, hlv⟩ := hlits_f l hl; ⟨hv, hlv⟩⟩)
    hm_f'

private theorem m5_otfs_s1_facts {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {s s_p s1 : FullState} {ar1 wv_p ws_p wso_p : List (BitVec 32)}
    {wl_p old_sz : Nat} {wu_p : BitVec 64} {cref l0 uip : BitVec 32}
    (hs_ar : s_p.core.arena = s.core.arena) (hsp_c : s_p.core =
      { s.core with wvec := wv_p, wstk := ws_p, wlen := wl_p, wusable := wu_p })
    (hsp_sc : s_p.scratch = { s.scratch with wsort := wso_p })
    (hs1_c : s1.core = { s.core with arena := ar1, wvec := wv_p, wstk := ws_p,
                                      wlen := wl_p, wusable := wu_p })
    (hs1_sc : s1.scratch = { s.scratch with wsort := wso_p })
    (har_len : s.core.arena.length = c.arena_cap) (hlen_p' : s_p.LengthsOk c)
    (har1_def : ar1 = (s.core.arena.set (cref.toNat + 3) l0).set (cref.toNat + 4) uip)
    (hw1 : FullAnalyzeSpecs.FullWitnessCutInv c F0 F_cur cut
      { s_p.core with
          arena := (s_p.core.arena.set (cref.toNat + 3) l0).set (cref.toNat + 4) uip })
    (hnd1 : FullAnalyzeSpecs.FullArenaVarsNodup
      { s_p with
          core := { s_p.core with
                      arena := (s_p.core.arena.set (cref.toNat + 3) l0).set
                        (cref.toNat + 4) uip } })
    (hrefs1 : fullArenaClauseRefsCore
        { s_p.core with
            arena := (s_p.core.arena.set (cref.toNat + 3) l0).set (cref.toNat + 4) uip } =
      fullArenaClauseRefsCore s_p.core)
    (hsz1 : fullArenaClauseSizeCore
        { s_p.core with
            arena := (s_p.core.arena.set (cref.toNat + 3) l0).set (cref.toNat + 4) uip }
        cref.toNat =
      fullArenaClauseSizeCore s_p.core cref.toNat)
    (hng1 : fullArenaClauseGarbCore
        { s_p.core with
            arena := (s_p.core.arena.set (cref.toNat + 3) l0).set (cref.toNat + 4) uip }
        cref.toNat = false)
    (har1_q : ∀ q, 2 ≤ q →
      ((s_p.core.arena.set (cref.toNat + 3) l0).set (cref.toNat + 4) uip)[cref.toNat + 3 + q]? =
      s_p.core.arena[cref.toNat + 3 + q]?)
    (hold_sz : old_sz = fullArenaClauseSizeCore s.core cref.toNat) :
    s1.LengthsOk c ∧
    FullAnalyzeSpecs.FullWitnessCutInv c F0 F_cur cut s1.core ∧
    Full.FullArenaVarsNodup s1 ∧
    fullArenaClauseRefs s1 = fullArenaClauseRefs s ∧
    fullArenaClauseSize s1 cref.toNat = old_sz ∧
    fullArenaClauseGarb s1 cref.toNat = false ∧
    (∀ q, 2 ≤ q → ar1[cref.toNat + 3 + q]? = s.core.arena[cref.toNat + 3 + q]?) := by
  have hs1_sp : s1.core = { s_p.core with arena := ar1 } := by rw [hs1_c, hsp_c]
  have hs1_scr : s1.scratch = s_p.scratch := hs1_sc.trans hsp_sc.symm
  have har1_sp : ar1 = (s_p.core.arena.set (cref.toNat + 3) l0).set (cref.toNat + 4) uip := by
    rw [har1_def, hs_ar]
  have hlen1 : s1.LengthsOk c := by
    have hcore : s1.core.LengthsOk c := by
      rw [hs1_sp]; exact { hlen_p'.core_ok with arena_len_arr := by simp [har1_def, har_len] }
    have hscr : s1.scratch.LengthsOk c := by rw [hs1_scr]; exact hlen_p'.scratch_ok
    exact ⟨hcore, hscr⟩
  have hw1' : FullAnalyzeSpecs.FullWitnessCutInv c F0 F_cur cut s1.core := by
    rw [hs1_sp, har1_sp]; exact hw1
  have hnd1' : Full.FullArenaVarsNodup s1 := by
    unfold Full.FullArenaVarsNodup fullArenaClauseRefs fullArenaClauseGarb fullArenaClauseLits
    unfold FullAnalyzeSpecs.FullArenaVarsNodup at hnd1
    rw [hs1_sp, har1_sp]; exact hnd1
  have hrefs1' : fullArenaClauseRefs s1 = fullArenaClauseRefs s := by
    have hr1 : fullArenaClauseRefs s1 = fullArenaClauseRefs s_p := by
      change fullArenaClauseRefsCore s1.core = fullArenaClauseRefsCore s_p.core
      rw [hs1_sp, har1_sp]; exact hrefs1
    rw [hr1]
    change fullArenaClauseRefsCore s_p.core = fullArenaClauseRefsCore s.core
    simp [fullArenaClauseRefsCore, hsp_c]
  have hsz1' : fullArenaClauseSize s1 cref.toNat = old_sz := by
    change fullArenaClauseSizeCore s1.core cref.toNat = old_sz
    rw [hs1_sp, har1_sp, hsz1, hold_sz]; unfold fullArenaClauseSizeCore; rw [hsp_c]
  have hng1' : fullArenaClauseGarb s1 cref.toNat = false := by
    change fullArenaClauseGarbCore s1.core cref.toNat = false
    rw [hs1_sp, har1_sp]; exact hng1
  have har1_q' : ∀ q, 2 ≤ q → ar1[cref.toNat + 3 + q]? = s.core.arena[cref.toNat + 3 + q]? := by
    simpa only [har1_def, hs_ar] using har1_q
  exact ⟨hlen1, hw1', hnd1', hrefs1', hsz1', hng1', har1_q'⟩

private theorem m5_otfs_s4_facts {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {idx_u nsz : Nat} {s s2 s3 s4 : FullState}
    {ar1 ar3 ar4 wv2 ws2 : List (BitVec 32)} {wl_p : Nat} {wu2 : BitVec 64}
    {cref l0 uip : BitVec 32}
    (_hcref : cref.toNat ∈ fullArenaClauseRefs s) (hdm : s.core.dense_mode = 0#64)
    (hrefs1' : fullArenaClauseRefs s2 = fullArenaClauseRefs s)
    (hs2_base : s2.core =
      { s.core with arena := ar1, wvec := wv2, wstk := ws2, wlen := wl_p,
                    wusable := wu2, oom := s.core.oom })
    (hs3_c : s3.core = { s2.core with arena := ar3 })
    (hlen3 : s3.LengthsOk c)
    (hrefs3 : fullArenaClauseRefsCore s3.core = fullArenaClauseRefsCore s2.core)
    (hcref3 : cref.toNat ∈ fullArenaClauseRefsCore s3.core)
    (hs4_c : s4.core = { s2.core with arena := ar4 })
    (hs4_sc : s4.scratch = s3.scratch) (hcv : s4.core.cur_vars = s.core.cur_vars)
    (h2cv_lt : 2 * s.core.cur_vars < 2 ^ 31 - 1) (hl0_lt : l0.toNat < 2 * s.core.cur_vars)
    (hcr_lt31 : cref.toNat < 0x80000000) (hnsz3 : 3 ≤ nsz)
    (hcap : cref.toNat + 3 + nsz ≤ c.arena_cap) (h4bd : cref.toNat + 4 < ar4.length)
    (har4_l : ar4.length = c.arena_cap) (hcb1_eq : cref.setWidth 64 + 3#64 + 1#64 =
      cref.setWidth 64 + 4#64) (hcr4_z : (cref.setWidth 64 + 4#64).toNat = cref.toNat + 4)
    (hw4 : FullAnalyzeSpecs.FullWitnessCutInv c F0 F_cur idx_u { s3.core with arena := ar4 })
    (hnd4 : Full.FullArenaVarsNodup { s3 with core := { s3.core with arena := ar4 } })
    (hrefs4 : fullArenaClauseRefsCore { s3.core with arena := ar4 } =
      fullArenaClauseRefsCore s3.core)
    (hsz4 : fullArenaClauseSizeCore { s3.core with arena := ar4 } cref.toNat = nsz)
    (hng4 : fullArenaClauseGarbCore { s3.core with arena := ar4 } cref.toNat = false)
    (hlits4 : ∀ l ∈ fullArenaClauseLitsCore { s3.core with arena := ar4 } cref.toNat,
      l ≠ uip.toNat ∧ l ∈ fullArenaClauseLits s cref.toNat) :
    s4.LengthsOk c ∧
    FullAnalyzeSpecs.FullWitnessCutInv c F0 F_cur idx_u s4.core ∧
    Full.FullArenaVarsNodup s4 ∧
    cref.toNat ∈ fullArenaClauseRefsCore s4.core ∧
    fullArenaClauseGarb s4 cref.toNat = false ∧
    (∀ l ∈ fullArenaClauseLits s4 cref.toNat,
      l ≠ uip.toNat ∧ l ∈ fullArenaClauseLits s cref.toNat) ∧
    (ar4[cref.toNat + 4]?.getD 0#32).toNat < 2 * s4.core.cur_vars ∧
    s4.core.dense_mode = 0#64 ∧ 2 * s4.core.cur_vars < 2 ^ 31 - 1 ∧
    (cref &&& 0x80000000#32) = 0#32 ∧ fullArenaClauseRefs s4 = fullArenaClauseRefs s ∧
    (∀ {hbd : (BitVec.setWidth 64 cref + 3 + 1).toNat < s4.core.arena.length},
      s4.core.arena[(BitVec.setWidth 64 cref + 3 + 1).toNat]'hbd = ar4[cref.toNat + 4]?.getD 0#32) ∧
    (BitVec.setWidth 64 l0 <<< (1 : Nat)).toNat = 2 * l0.toNat ∧
    ((BitVec.setWidth 64 l0 <<< (1 : Nat)) + (1 : BitVec 64)).toNat = 2 * l0.toNat + 1 ∧
    (∀ {hbd0 : (BitVec.setWidth 64 l0 <<< (1 : Nat)).toNat < s4.core.wvec.length},
      (BitVec.setWidth 64 (s4.core.wvec[(BitVec.setWidth 64 l0 <<< (1 : Nat)).toNat]'hbd0)).toNat =
      fullWatchOffCore s4.core l0.toNat) ∧
    (∀ {hbd1 : ((BitVec.setWidth 64 l0 <<< (1 : Nat)) + (1 : BitVec 64)).toNat <
        s4.core.wvec.length},
      (BitVec.setWidth 64
        (s4.core.wvec[((BitVec.setWidth 64 l0 <<< (1 : Nat)) +
          (1 : BitVec 64)).toNat]'hbd1)).toNat =
      fullWatchSizeCore s4.core l0.toNat) := by
  have hs4_s3 : s4.core = { s3.core with arena := ar4 } := by rw [hs4_c, hs3_c]
  have hs4_ar : s4.core.arena = ar4 := by rw [hs4_c]
  have hlen4 : s4.LengthsOk c :=
    ⟨by rw [hs4_s3]; exact { hlen3.core_ok with arena_len_arr := har4_l },
     by rw [hs4_sc]; exact hlen3.scratch_ok⟩
  have hw4' : FullAnalyzeSpecs.FullWitnessCutInv c F0 F_cur idx_u s4.core := by
    rw [hs4_s3]; exact hw4
  have hnd4' : Full.FullArenaVarsNodup s4 := by
    unfold Full.FullArenaVarsNodup at hnd4 ⊢
    simpa only [hs4_s3, fullArenaClauseRefs, fullArenaClauseGarb, fullArenaClauseLits,
      fullArenaClauseRefsCore, fullArenaClauseGarbCore, fullArenaClauseLitsCore,
      fullArenaClauseSizeCore, fullArenaHdrCore] using hnd4
  have hcref4 : cref.toNat ∈ fullArenaClauseRefsCore s4.core := by
    rw [hs4_s3]; exact hrefs4 ▸ hcref3
  have hng4' : fullArenaClauseGarb s4 cref.toNat = false := by
    change fullArenaClauseGarbCore s4.core cref.toNat = false; rw [hs4_s3]; exact hng4
  have hsz4' : fullArenaClauseSizeCore s4.core cref.toNat = nsz := by
    rw [hs4_s3]; exact hsz4
  have hlits4' : ∀ l ∈ fullArenaClauseLits s4 cref.toNat,
      l ≠ uip.toNat ∧ l ∈ fullArenaClauseLits s cref.toNat := by
    intro l hl; apply hlits4 l
    simpa only [fullArenaClauseLits, fullArenaClauseLitsCore, fullArenaClauseSizeCore, hs4_s3]
      using hl
  obtain ⟨hnl1_lt, _⟩ := otfs_large_swap1_nl1 hw4' hcv hs4_ar h2cv_lt hcref4 hng4' hsz4' hnsz3
    har4_l hcap h4bd
  have hshl0 : (BitVec.setWidth 64 l0 <<< (1 : Nat)).toNat = 2 * l0.toNat := by
    rw [m5_bv64_shl1_nat _ (by rw [zext_toNat l0 (by decide)]; omega), zext_toNat l0 (by decide)]
  have h2l1_4 : ((BitVec.setWidth 64 l0 <<< (1 : Nat)) + (1 : BitVec 64)).toNat =
      2 * l0.toNat + 1 := by rw [m5_bv64_add1_nat _ (by rw [hshl0]; omega), hshl0]
  have hw4_wvec := hlen4.core_ok.wvec_len
  have hcv4_le : s4.core.cur_vars ≤ c.max_vars := hlen4.core_ok.cur_vars_le
  have hw4_bd0 : 2 * l0.toNat < s4.core.wvec.length := by rw [hw4_wvec]; omega
  have hw4_bd1 : 2 * l0.toNat + 1 < s4.core.wvec.length := by rw [hw4_wvec]; omega
  refine ⟨hlen4, hw4', hnd4', hcref4, hng4', hlits4', by rwa [hcv],
    by rw [hs4_c, hs2_base]; exact hdm, by rwa [hcv], (m5_bv32_lt_highbit_iff cref).mp hcr_lt31,
    ?_, fun {hbd} => ?_, hshl0, h2l1_4, fun {hbd0} => ?_, fun {hbd1} => ?_⟩
  · change fullArenaClauseRefsCore s4.core = fullArenaClauseRefsCore s.core
    change fullArenaClauseRefsCore s2.core = fullArenaClauseRefsCore s.core at hrefs1'
    rw [hs4_s3]; exact hrefs4.trans (hrefs3.trans hrefs1')
  · have h31 :
        (BitVec.setWidth 64 cref + 3 + 1 : BitVec 64) = BitVec.setWidth 64 cref + 4 := hcb1_eq
    have h4_nat : (BitVec.setWidth 64 cref + 4 : BitVec 64).toNat = cref.toNat + 4 := hcr4_z
    have h4_bd_s4 : (BitVec.setWidth 64 cref + 4 : BitVec 64).toNat < s4.core.arena.length := by
      rw [hs4_ar, h4_nat]; exact h4bd
    rw [m5_list_getElem_of_idx (hj := h4_bd_s4) (congrArg BitVec.toNat h31)]
    exact (m5_list_getElem_of_list_idx hs4_ar h4_nat (hj := h4bd)).trans
      (by rw [List.getElem?_eq_getElem h4bd, Option.getD_some])
  · rw [zext_toNat _ (by decide)]; unfold fullWatchOffCore
    rw [List.getElem?_eq_getElem hw4_bd0, Option.getD_some]
    exact congrArg BitVec.toNat (m5_list_getElem_of_idx hshl0)
  · rw [zext_toNat _ (by decide)]; unfold fullWatchSizeCore
    rw [List.getElem?_eq_getElem hw4_bd1, Option.getD_some]
    exact congrArg BitVec.toNat (m5_list_getElem_of_idx h2l1_4)

/-- Canonical `Func.wp` proof for `FullM5Otfs.full_otfs_large` (`Full.fullOtfsLargeSpec`):
early `cnt >= 3` exit, read-only `nl1_pre` scan, headroom check + `full_wstack_defrag` +
`full_watch_push` before arena swap and `full_unwatch_large(uip)`, fused compaction + `hp`,
header/`PH_SHRK`, `hp` swap, and `l0` blocker update. -/
theorem full_otfs_large_wp (Γ : Env)
    (hDefrag : ∀ a m Q X, Full.fullWstackDefragSpec a m Q X →
      Γ "full_wstack_defrag" [i64] [] a m Q X)
    (hUnw : ∀ a m Q X, Full.fullUnwatchLargeSpec a m Q X →
      Γ "full_unwatch_large" [i64, i32, i32] [] a m Q X)
    (hPush : ∀ a m Q X, Full.fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, Full.fullOtfsLargeSpec a m Q X →
      Func.wp Γ full_otfs_large_body a m Q X := by
  rintro ⟨h, cref, uip, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, cut, idx_u, s, R, rfl, hlen, hw_can, hnd, hdm, hcref, hng, hu_lt,
      hiu_cut, ht_u, hr_u, hlev_u, hent_f, hm, hQ⟩
  have hiu_te : idx_u < s.core.trail_end := Nat.lt_of_lt_of_le hiu_cut hw_can.cut_le
  have hw := m5_canonCut_to_anaCut hw_can
  have hwf := hw.arena.refs_wf cref.toNat hcref
  have har_len := hlen.core_ok.arena_len_arr; have har_le := hlen.core_ok.arena_len_le
  have hlvl_len := hlen.core_ok.lvl_len; have hwv_len := hlen.core_ok.wvec_len
  have hcv_le := hlen.core_ok.cur_vars_le; have hcap31_orig := c.harena; have hmaxv := c.hmaxv
  have hwcap_orig := c.hwcap
  unfold dimacsBound at hcap31_orig hmaxv hwcap_orig
  have hcap31 : c.arena_cap < 2 ^ 31 - 1 := by omega
  have h2cv_lt : 2 * s.core.cur_vars < 2 ^ 31 - 1 := by omega
  let old_sz := fullArenaClauseSizeCore s.core cref.toNat
  have hold_bd : cref.toNat + 3 + old_sz ≤ s.core.arena_len := by
    have := hwf.2.2.1; have := hwf.2.2.2.1; dsimp only [old_sz]; omega
  have hlits_info : ∀ j < old_sz,
      (s.core.arena[cref.toNat + 3 + j]?.getD 0#32).toNat < 2 * s.core.cur_vars ∧
      s.core.arena[cref.toNat + 3 + j]?.getD 0#32 ≠ 0xFFFFFFFF#32 := fun j hj => by
    have hm_j : (s.core.arena[cref.toNat + 3 + j]?.getD 0#32).toNat ∈
        fullArenaClauseLits s cref.toNat := by
      simp only [fullArenaClauseLits, fullArenaClauseLitsCore, List.mem_map]
      refine ⟨s.core.arena[cref.toNat + 3 + j]'(by omega), List.mem_iff_getElem.mpr
        ⟨j, by simp; omega, by simp [List.getElem_take, List.getElem_drop]⟩,
        by rw [List.getElem?_eq_getElem (by omega), Option.getD_some]⟩
    have hl_lt := hw.arena.lits_lt cref.toNat hcref hng _ hm_j
    exact ⟨hl_lt, bv32_lit_neq_ff (Nat.lt_trans hl_lt h2cv_lt)⟩
  have hcr0_z : (cref.setWidth 64).toNat = cref.toNat := zext_toNat cref (by decide)
  have hcr_add {k : Nat} (hk : cref.toNat + k < 2 ^ 64) (hk' : k < 2 ^ 64) :
      (cref.setWidth 64 + BitVec.ofNat 64 k).toNat = cref.toNat + k := by
    rw [BitVec.toNat_add, hcr0_z, bv64_ofNat_toNat hk']; omega
  have hcr1_z := hcr_add (k := 1) (by omega) (by decide)
  have hcr2_z := hcr_add (k := 2) (by omega) (by decide)
  have hcr3_z := hcr_add (k := 3) (by omega) (by decide)
  have hcr4_z := hcr_add (k := 4) (by omega) (by decide)
  have hcb1_eq : cref.setWidth 64 + 3#64 + 1#64 = cref.setWidth 64 + 4#64 := by bv_omega
  have hcb1_z : (cref.setWidth 64 + 3#64 + 1#64).toNat = cref.toNat + 4 := by
    rw [hcb1_eq]; exact hcr4_z
  have hsz_eq : (s.core.arena[cref.toNat + 2]'(by omega)).toNat = old_sz := by
    unfold old_sz fullArenaClauseSizeCore
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
  have hsz32 : s.core.arena[cref.toNat + 2]'(by omega) = BitVec.ofNat 32 old_sz :=
    BitVec.eq_of_toNat_eq (by rw [hsz_eq, bv32_ofNat_toNat (by omega)])
  have hcr3_bd : (cref.setWidth 64 + 3#64).toNat < s.core.arena.length := by rw [hcr3_z]; omega
  have hcr4_bd : (cref.setWidth 64 + 4#64).toNat < s.core.arena.length := by rw [hcr4_z]; omega
  have hcb1_bd : (cref.setWidth 64 + 3#64 + 1#64).toNat < s.core.arena.length := by
    rw [hcb1_z]; omega
  let orig0 := s.core.arena[cref.toNat + 3]?.getD 0#32
  let orig1 := s.core.arena[cref.toNat + 4]?.getD 0#32
  have hor0 : s.core.arena[(cref.setWidth 64 + 3#64).toNat]'hcr3_bd = orig0 := by
    rw [m5_list_getElem_of_idx (hj := by omega) hcr3_z]
    simp [orig0, List.getElem?_eq_getElem (by omega : cref.toNat + 3 < s.core.arena.length)]
  have hor1 : s.core.arena[(cref.setWidth 64 + 3#64 + 1#64).toNat]'hcb1_bd = orig1 := by
    rw [m5_list_getElem_of_idx (hj := by omega) hcb1_z]
    simp [orig1, List.getElem?_eq_getElem (by omega : cref.toNat + 4 < s.core.arena.length)]
  have hfail : Q (false, ()) m :=
    hQ false s.core.arena s.core.wvec s.core.wstk s.core.wlen s.core.wusable s.core.oom
      s.scratch _ hlen (m5_canonCut_shrink_cut hw_can (Nat.le_of_lt hiu_cut)) hnd ⟨rfl, rfl⟩
      rfl rfl rfl rfl (fun h => by cases h) hm
  unfold Func.wp full_otfs_large_body
  fa_fast_steps_nogrp
  refine wp_join_group (ts := [i32]) (fun p ml0 => ml0 = m ∧
      ((p.1 = orig0 ∧ orig1 = uip) ∨ (p.1 = orig1 ∧ orig0 = uip))) ?_ ?_
  · rintro _ ⟨l0, ⟨⟩⟩ ml0 ⟨hml0, hs01⟩; subst ml0
    have hl0_lt : l0.toNat < 2 * s.core.cur_vars := by
      rcases hs01 with ⟨rfl, _⟩ | ⟨rfl, _⟩
      · exact (hlits_info 0 (by omega)).1
      · exact (hlits_info 1 (by omega)).1
    have hcr2_bd : (cref.setWidth 64 + 2#64).toNat < s.core.arena.length := by rw [hcr2_z]; omega
    fa_fast_steps_nogrp
    -- Pass 1: early-break active-literal count (`cnt >= 3`)
    refine wp_loop_break_group (brkTs := [i32, i32]) (lpTs := [i32, i32])
      (fun (cnt, _iv, ()) ml => ml = m ∧
        (cnt.toNat < 3 ∨ 3 ≤ 1 + Full.otfsActCnt s.core cref.toNat old_sz))
      (fun r (cnt, iv, ()) ml => ∃ i_nat : Nat,
        ml = m ∧ r = old_sz - i_nat ∧ 2 ≤ i_nat ∧ i_nat ≤ old_sz ∧ iv = BitVec.ofNat 32 i_nat ∧
        cnt = BitVec.ofNat 32 (1 + Full.otfsActCnt s.core cref.toNat i_nat) ∧
        1 + Full.otfsActCnt s.core cref.toNat i_nat < 3) ?_ ?_ ?_
    · rintro _ ⟨cnt, iv, ⟨⟩⟩ ml ⟨hml, hcnt_res⟩; subst ml
      fa_fast_steps_nogrp
      · exact hfail
      · have hcnt3 : 3 ≤ 1 + Full.otfsActCnt s.core cref.toNat old_sz := by
          have hge3 : ¬ cnt.toNat < (3#32).toNat := ‹_›
          exact hcnt_res.resolve_left (by simpa using hge3)
        have hact_lt : 1 + Full.otfsActCnt s.core cref.toNat old_sz < old_sz := by
          have := Full.otfsActCnt_le s.core cref.toNat old_sz; omega
        have h4_old : 4 ≤ old_sz := by omega
        -- Pass 1b: read-only scan for `(hl_pre, nl1_pre)` (max level in `[2 .. old_sz)`)
        refine wp_loop_group
          (fun r (iv1b, hlp, nl1p, ()) ml => ∃ i_b : Nat,
            ml = m ∧ r = old_sz - i_b ∧ 2 ≤ i_b ∧ i_b ≤ old_sz ∧
            iv1b = BitVec.ofNat 32 i_b ∧ nl1p.toNat < 2 * s.core.cur_vars) ?_ ?_
        · rintro L1b r1b ⟨iv1b, hlp, nl1p, ⟨⟩⟩ ml ih1b
            ⟨i_b, hml1b, rfl, hib2, hible, rfl, hnl1p_lt⟩
          subst ml
          fa_fast_steps_nogrp
          · have hib_lt : i_b < old_sz := by
              have hb : (BitVec.ofNat 32 i_b).toNat <
                  (s.core.arena[(cref.setWidth 64 + 2#64).toNat]'hcr2_bd).toNat := ‹_›
              rw [bv32_ofNat_toNat (by omega), m5_list_getElem_of_idx (hj := by omega) hcr2_z,
                hsz_eq] at hb
              exact hb
            obtain ⟨har_bd, hz_bd, hc_bd, hc_idx, hot_eq, _, hlvl1_bd_len, hv_bd⟩ :=
              otfs_large_loop1_step_bds hcap31 hcv_le hlvl_len har_len (by omega) hib_lt hlits_info
            have hot_lt' : (s.core.arena[(cref.setWidth 64 + 3#64 +
                (BitVec.ofNat 32 i_b).setWidth 64).toNat]'hz_bd).toNat <
                2 * s.core.cur_vars := by
              rw [m5_list_getElem_of_idx (m5_otfs_bv_idx3_64 cref i_b (by omega) (by omega))]
              have h1 := (hlits_info i_b hib_lt).1
              rwa [List.getElem?_eq_getElem har_bd, Option.getD_some] at h1
            fa_fast_steps_nogrp
            refine wp_join_group (ts := [i32, i32]) (fun (_hlp', nl1', ()) ml' =>
              ml' = m ∧ nl1'.toNat < 2 * s.core.cur_vars) ?_ ?_
            · rintro _ ⟨hlp', nl1', ⟨⟩⟩ ml' ⟨hml', hnl1'⟩; subst ml'; fa_fast_steps
              rw [m5_bv32_ofNat_add1]
              exact ih1b (old_sz - (i_b + 1)) _ m (by omega)
                ⟨i_b + 1, rfl, rfl, by omega, by omega, rfl, hnl1'⟩
            · intro J1b hJ1b; fa_fast_steps
              · exact hJ1b _ _ ⟨rfl, hot_lt'⟩
              · exact hJ1b _ _ ⟨rfl, hnl1p_lt⟩
          · -- Exit Pass 1b (`nl1p : BitVec 32`, `hnl1p_lt : nl1p.toNat < 2 * s.core.cur_vars`)
            have hcf_done : i_b = old_sz := by
              have hba : ¬ (BitVec.ofNat 32 i_b).toNat <
                  (s.core.arena[(cref.setWidth 64 + 2#64).toNat]'hcr2_bd).toNat := ‹_›
              rw [bv32_ofNat_toNat (by omega), m5_list_getElem_of_idx (hj := by omega) hcr2_z,
                hsz_eq] at hba
              omega
            clear hcf_done
            have hl0_p := bv32_lit_lo31_props (l := l0) (by omega)
            have hcr_ne : cref ≠ 0xFFFFFFFF#32 := bv32_lit_neq_ff (by omega)
            have hcr_lt31 : cref.toNat < 0x80000000 := by omega
            have hl0_m_ne : l0 &&& 0x7FFFFFFF#32 ≠ 0xFFFFFFFF#32 := by
              rw [hl0_p.1]; exact bv32_lit_neq_ff (by omega)
            -- Headroom pre-check + `full_wstack_defrag` -> join `s_d`
            fa_fast_steps_nogrp
            refine wp_join_group (ts := []) (fun () ml_d =>
              ∃ (s_d : FullState) (wv_d ws_d : List (BitVec 32)) (wl_d : Nat) (wu_d : BitVec 64)
                (wso_d : List (BitVec 32)),
                s_d.core = { s.core with wvec := wv_d, wstk := ws_d, wlen := wl_d,
                                         wusable := wu_d } ∧
                s_d.scratch = { s.scratch with wsort := wso_d } ∧
                s_d.LengthsOk c ∧ Full.FullWitnessCutInv c F0 F_cur cut s_d.core ∧
                (FullMem c s_d ⋆ R) ml_d) ?_ ?_
            · rintro _ ⟨⟩ ml_d ⟨s_d, wv_d, ws_d, wl_d, wu_d, wso_d, hsd_c, hsd_sc, hlen_d, hw_d,
                hm_d⟩
              have hsd_cv : s_d.core.cur_vars = s.core.cur_vars := by rw [hsd_c]
              have hsd_dm : s_d.core.dense_mode = 0#64 := by rw [hsd_c]; exact hdm
              have hcref_d : cref.toNat ∈ fullArenaClauseRefsCore s_d.core := by
                change cref.toNat ∈ fullArenaClauseRefsCore s.core at hcref
                rwa [show fullArenaClauseRefsCore s_d.core = fullArenaClauseRefsCore s.core by
                  simp [fullArenaClauseRefsCore, hsd_c]]
              c0_call (m5_anaWatchPush_adapter hPush)
              · refine ⟨c, s_d, R, rfl, hlen_d, by
                  have h := hw_d.watches; unfold ModeWatchesInv at h
                  simp only [hsd_dm, ↓reduceIte] at h; exact h.layout,
                  fun h => absurd h (by decide), fun _ => ⟨hl0_m_ne, hcr_ne⟩, hm_d,
                  fun ok_p wv_p ws_p wl_p wu_p wso_p m_p hlen_p hlay_p hother_p hok_pt hok_pf
                    hm_p => ?_⟩
                clear hm_d
                obtain ⟨s_p, hsp_d_eq, hm_p'⟩ : ∃ s_p : FullState,
                    s_p = { s_d with
                      core := { s_d.core with wvec := wv_p, wstk := ws_p, wlen := wl_p,
                                              wusable := wu_p }
                      scratch := { s_d.scratch with wsort := wso_p } } ∧
                    (FullMem c s_p ⋆ R) m_p := ⟨_, rfl, hm_p⟩
                clear hm_p
                have hsp_c : s_p.core = { s.core with wvec := wv_p, wstk := ws_p, wlen := wl_p,
                                                      wusable := wu_p } := by
                  rw [hsp_d_eq]; dsimp only; rw [hsd_c]
                have hsp_sc : s_p.scratch = { s.scratch with wsort := wso_p } := by
                  rw [hsp_d_eq]; dsimp only; rw [hsd_sc]
                have hlen_p' : s_p.LengthsOk c := by
                  rw [hsp_d_eq]; exact ⟨{ hlen_p.core_ok with }, hlen_p.scratch_ok⟩
                have hcref_p : cref.toNat ∈ fullArenaClauseRefsCore s_p.core := by
                  change cref.toNat ∈ fullArenaClauseRefsCore s.core at hcref
                  rwa [show fullArenaClauseRefsCore s_p.core = fullArenaClauseRefsCore s.core by
                    simp [fullArenaClauseRefsCore, hsp_c]]
                by_cases hok_pt_c : ok_p = true
                · subst hok_pt_c
                  obtain ⟨_, _, hsz_p, hsame_p, hw0_p, hw1_p⟩ := hok_pt rfl
                  have hsp_w_eq : s_p.core =
                      { s_d.core with wvec := wv_p, wstk := ws_p, wlen := wl_p,
                                      wusable := wu_p } := congrArg FullState.core hsp_d_eq
                  have hm_wp : ModeWatchesInv F_cur s_p.core := by
                    rw [hsp_w_eq]
                    exact fa_watchPush_large_preserves hsd_dm hw_d.watches
                      (by rw [hsd_cv]; exact hnl1p_lt) hlay_p hother_p hsz_p hsame_p hw0_p
                      (hw1_p rfl) hl0_p.2.1 hcr_lt31 hcref_d
                  have hw_p : Full.FullWitnessCutInv c F0 F_cur cut s_p.core := by
                    rw [hsp_w_eq] at hm_wp ⊢; exact m5_canonCut_with_watches hw_d hm_wp
                  -- Now `ar[cb] = l0; ar[cb + 1ULL] = uip; full_unwatch_large(h, uip, cref);`
                  let ar1 := (s.core.arena.set (cref.toNat + 3) l0).set (cref.toNat + 4) uip
                  have hsp_ar : s_p.core.arena = s.core.arena := by rw [hsp_c]
                  have hsp_lvl : s_p.core.lvl = s.core.lvl := by rw [hsp_c]
                  have hsp_dm : s_p.core.dense_mode = 0#64 := by rw [hsp_c]; exact hdm
                  have hsp_oom : s_p.core.oom = s.core.oom := by rw [hsp_c]
                  have hnd_p : Full.FullArenaVarsNodup s_p := fun r hr hngr => by
                    change r ∈ fullArenaClauseRefsCore s_p.core at hr
                    have hrf : fullArenaClauseRefsCore s_p.core =
                        fullArenaClauseRefsCore s.core := by
                      simp [fullArenaClauseRefsCore, hsp_c]
                    rw [hrf] at hr
                    change ((fullArenaClauseLitsCore s_p.core r).map (· / 2)).Nodup
                    rw [show fullArenaClauseLitsCore s_p.core r =
                        fullArenaClauseLitsCore s.core r by
                      simp [fullArenaClauseLitsCore, fullArenaClauseSizeCore, hsp_c]]
                    exact hnd r hr (by
                      change fullArenaClauseGarbCore s.core r = false
                      simpa [fullArenaClauseGarbCore, fullArenaHdrCore, hsp_c] using hngr)
                  have hng_p : fullArenaClauseGarb s_p cref.toNat = false := by
                    simpa [fullArenaClauseGarb, fullArenaClauseGarbCore, fullArenaHdrCore, hsp_c]
                      using hng
                  have hs01_p : (l0 = s_p.core.arena[cref.toNat + 3]?.getD 0#32 ∧
                      s_p.core.arena[cref.toNat + 4]?.getD 0#32 = uip) ∨
                    (l0 = s_p.core.arena[cref.toNat + 4]?.getD 0#32 ∧
                      s_p.core.arena[cref.toNat + 3]?.getD 0#32 = uip) := by
                    rw [hsp_ar]; exact hs01
                  obtain ⟨hw1, hnd1, hrefs1, hsz1, hng1, har1_q, har1_0, har1_1⟩ :=
                    Full.otfs_large_swap01 hlen_p' (m5_canonCut_to_anaCut hw_p) hnd_p hcref_p hng_p
                      hs01_p
                  have har1_sym : (s_p.core.arena.set (cref.setWidth 64 + 3#64).toNat l0).set
                      (cref.setWidth 64 + 3#64 + 1#64).toNat uip = ar1 := by
                    dsimp only [ar1]; rw [hsp_ar, hcr3_z, hcb1_z]
                  have hsp3_bd : (cref.setWidth 64 + 3#64).toNat < s_p.core.arena.length := by
                    rw [hsp_ar]; exact hcr3_bd
                  have hsp4_bd : (cref.setWidth 64 + 3#64 + 1#64).toNat <
                      (s_p.core.arena.set (cref.setWidth 64 + 3#64).toNat l0).length := by
                    rw [List.length_set, hsp_ar]; exact hcb1_bd
                  fa_fast_steps_nogrp
                  let ar1_ast := (s_p.core.arena.set (cref.setWidth 64 + 3#64).toNat l0).set
                    (cref.setWidth 64 + 3#64 + 1#64).toNat uip
                  obtain ⟨s1, hs1_c, hs1_sc, hm1'⟩ :=
                    m5_otfs_opaque_state
                      (s_old := { s_p with core := { s_p.core with arena := ar1_ast } })
                      { s.core with arena := ar1, wvec := wv_p, wstk := ws_p,
                                    wlen := wl_p, wusable := wu_p }
                      { s.scratch with wsort := wso_p } (by assumption)
                      (by dsimp only [ar1_ast]; rw [har1_sym, hsp_c]) hsp_sc
                  obtain ⟨hlen1, hw1', hnd1', hrefs1', hsz1', hng1', har1_q'⟩ :=
                    m5_otfs_s1_facts hsp_ar hsp_c hsp_sc hs1_c hs1_sc har_len hlen_p' rfl hw1 hnd1
                      hrefs1 hsz1 hng1 har1_q rfl
                  c0_call hUnw
                  · refine ⟨c, s1, R, rfl, hlen1, by
                      have h := hw1'.watches; unfold ModeWatchesInv at h
                      rw [show s1.core.dense_mode = 0#64 by rw [hs1_c]; exact hdm] at h
                      simp only [↓reduceIte] at h; exact h.layout, hm1',
                      fun wv2 ws2 wu2 m2 hlen2 _ hmw2 hm2 => ?_⟩
                    obtain ⟨s2, hs2_base, hs2_sc, hm2_s2⟩ :=
                      m5_otfs_opaque_state
                        { s.core with arena := ar1, wvec := wv2, wstk := ws2, wlen := wl_p,
                                      wusable := wu2, oom := s.core.oom }
                        { s.scratch with wsort := wso_p } hm2
                        (by dsimp only; rw [hs1_c]) hs1_sc
                    have hs2_s1_c : s2.core =
                        { s1.core with wvec := wv2, wstk := ws2, wusable := wu2 } := by
                      rw [hs2_base, hs1_c]
                    have hlen2' : s2.LengthsOk c :=
                      ⟨by rw [hs2_s1_c]; exact hlen2.core_ok,
                       by rw [hs2_sc, ← hs1_sc]; exact hlen2.scratch_ok⟩
                    have hw2 : FullAnalyzeSpecs.FullWitnessCutInv c F0 F_cur cut s2.core := by
                      rw [hs2_s1_c]; exact hw1'.with_watches (hmw2 F_cur hw1'.watches)
                    have hnd2 : Full.FullArenaVarsNodup s2 := by
                      unfold Full.FullArenaVarsNodup at hnd1' ⊢
                      simpa only [hs2_s1_c, fullArenaClauseRefs, fullArenaClauseGarb,
                        fullArenaClauseLits, fullArenaClauseRefsCore, fullArenaClauseGarbCore,
                        fullArenaClauseLitsCore, fullArenaClauseSizeCore, fullArenaHdrCore]
                        using hnd1'
                    have hrefs2 : fullArenaClauseRefs s2 = fullArenaClauseRefs s := by
                      change fullArenaClauseRefsCore s2.core = fullArenaClauseRefsCore s.core
                      change fullArenaClauseRefsCore s1.core = fullArenaClauseRefsCore s.core
                        at hrefs1'
                      rw [← hrefs1', hs2_s1_c]; rfl
                    have hcref2 : cref.toNat ∈ fullArenaClauseRefs s2 := by
                      rw [hrefs2]; exact hcref
                    have hng2 : fullArenaClauseGarb s2 cref.toNat = false := by
                      simpa only [fullArenaClauseGarb, fullArenaClauseGarbCore, fullArenaHdrCore,
                        hs2_s1_c] using hng1'
                    have hsz2 : fullArenaClauseSize s2 cref.toNat = old_sz := by
                      change fullArenaClauseSizeCore s2.core cref.toNat = old_sz
                      exact (show fullArenaClauseSizeCore s2.core cref.toNat =
                        fullArenaClauseSizeCore s1.core cref.toNat by
                          simp [fullArenaClauseSizeCore, hs2_s1_c]).trans hsz1'
                    have har1_s2 : ∀ i, i < cref.toNat + 3 ∨ cref.toNat + 5 ≤ i →
                        ar1[i]? = s2.core.arena[i]? := by
                      rw [hs2_base]; exact fun _ _ => rfl
                    have hs2_lvl : s2.core.lvl = s.core.lvl := by rw [hs2_base]
                    clear hlen2 hm2 hDefrag hUnw hPush hfail hsd_c hsd_sc hsd_cv hsd_dm
                      hcref_d hsp_c hsp_sc hlen_p' hcref_p hsz_p hsame_p hw0_p hw1_p hsp_w_eq
                      hm_wp hw_p hsp_ar hsp_lvl hsp_dm hnd_p hng_p hs01_p hw1 hnd1 hrefs1
                      hsz1 hng1 har1_q har1_0 har1_1 har1_sym hsp3_bd hsp4_bd
                    fa_fast_steps_nogrp
                    -- Fused Pass 2+3: compact active literals while tracking `hp` / `hl`
                    refine wp_loop_group (fun r (iv, nszv, hpv, hlv, ()) ml =>
                      ∃ (i_n nsz hp_n : Nat) (ar_cur : List (BitVec 32)) (origMap : List Nat),
                        (FullMem c { s2 with core := { s2.core with arena := ar_cur } } ⋆ R) ml ∧
                        iv = BitVec.ofNat 32 i_n ∧ nszv = BitVec.ofNat 32 nsz ∧
                        hpv = BitVec.ofNat 32 hp_n ∧ (hp_n = 1 ∨ (1 ≤ hp_n ∧ hp_n < nsz)) ∧
                        OtfsShrinkInv c s ar1 cref l0 uip old_sz r i_n nsz ar_cur origMap) ?_ ?_
                    · rintro L2 r2 ⟨iv, nszv, hpv, hlv, ⟨⟩⟩ ml ih2
                        ⟨i_nat, nsz, hp_n, ar_cur, origMap, hm_c, rfl, rfl, rfl, hhp_ok, hinv_l⟩
                      have hr2_eq : r2 = old_sz - i_nat := hinv_l.2.1; subst r2
                      have ⟨har_c, _, hi2, hile, hns1, hact, hlm, hpw, hlt_m, h01, hcov, hmapeq,
                        hout_m⟩ := hinv_l
                      let sc : FullState := { s2 with core := { s2.core with arena := ar_cur } }
                      have hlen_c : sc.LengthsOk c :=
                        ⟨{ hlen2'.core_ok with arena_len_arr := har_c }, hlen2'.scratch_ok⟩
                      have har_c_bd : (cref.setWidth 64 + 2#64).toNat < ar_cur.length := by
                        rw [har_c, hcr2_z]; omega
                      have hsz_c : ar_cur[cref.toNat + 2]'(by rw [har_c]; omega) =
                          BitVec.ofNat 32 old_sz := by
                        have hopt := hout_m (cref.toNat + 2) (Or.inl (by omega))
                        rw [List.getElem?_eq_getElem (by rw [har_c]; omega)] at hopt
                        have ho1 : ar1[cref.toNat + 2]? = s.core.arena[cref.toNat + 2]? := by
                          dsimp only [ar1]
                          rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
                        rw [← hopt, List.getElem?_eq_getElem (by omega)] at ho1
                        exact (Option.some.inj ho1).trans hsz32
                      fa_steps_n 3
                      · have hilt : i_nat < old_sz := by
                          have hb : i_nat % 2 ^ 32 < (s.core.arena[(cref.toNat +
                              BitVec.toNat (2 : BitVec 64)) % 2 ^ 64]'(by
                                simp only [BitVec.reduceToNat]; omega)).toNat := ‹_›
                          rw [Nat.mod_eq_of_lt (by omega),
                            m5_list_getElem_of_idx (j := cref.toNat + 2)
                              (hj := by omega) (by simp only [BitVec.reduceToNat]; omega), hsz_eq]
                            at hb
                          exact hb
                        obtain ⟨hc_idx_bd, hc_z_bd, har_nsz_bd2, har_bd, hnsz_lt_i, hc_idx, hc_z,
                          hnsz_z, hot_c_eq, hot_z_eq, h2_lvl_bd, hv_bd⟩ :=
                          otfs_large_loop2_step_bds hcap31 (by omega) hcv_le hlvl_len
                            hlen2'.core_ok.lvl_len har_len hinv_l hilt har1_q' hlits_info
                        fa_fast_steps_nogrp
                        refine wp_join_group (ts := [i32, i32, i32])
                          (fun (nszv', hpv', _hlv', ()) ml' =>
                            ∃ (nsz' hp_n' : Nat) (ar' : List (BitVec 32)) (omap' : List Nat),
                              (FullMem c { s2 with core := { s2.core with arena := ar' } } ⋆
                                R) ml' ∧
                              nszv' = BitVec.ofNat 32 nsz' ∧ hpv' = BitVec.ofNat 32 hp_n' ∧
                              (hp_n' = 1 ∨ (1 ≤ hp_n' ∧ hp_n' < nsz')) ∧
                              OtfsShrinkInv c s ar1 cref l0 uip old_sz
                                (old_sz - (i_nat + 1)) (i_nat + 1) nsz' ar' omap') ?_ ?_
                        · rintro _ ⟨nszv', hpv', hlv', ⟨⟩⟩ ml'
                            ⟨nsz', hp_n', ar', omap', hm', rfl, rfl, hhp', hinv'⟩
                          fa_fast_steps
                          rw [m5_bv32_ofNat_add1]
                          exact ih2 (old_sz - (i_nat + 1)) _ ml' (by omega)
                            ⟨i_nat + 1, nsz', hp_n', ar', omap', hm', rfl, rfl, rfl, hhp', hinv'⟩
                        · intro J2 hJ2
                          fa_fast_steps_nogrp
                          · have hlv_pos := m5_otfs_p2_lv_pos har_bd hv_bd hs2_lvl hot_c_eq
                              (‹(0#32 : BitVec 32).toNat <
                                (s2.core.lvl[(ar_cur[(cref.toNat + BitVec.toNat (3 : BitVec 64) +
                                  i_nat % 2 ^ 32) % 2 ^ 64]'hc_idx_bd).toNat / 2]'h2_lvl_bd).toNat›)
                            let ar' := ar_cur.set (cref.toNat + 3 + nsz)
                              (s.core.arena[cref.toNat + 3 + i_nat]'har_bd)
                            let ar'_raw := ar_cur.set (cref.setWidth 64 + 3#64 +
                                (BitVec.ofNat 32 nsz).setWidth 64).toNat
                              (ar_cur[(cref.setWidth 64 + 3#64 +
                                (BitVec.ofNat 32 i_nat).setWidth 64).toNat]'hc_z_bd)
                            have har_st_eq : ar'_raw = ar' := by
                              dsimp only [ar'_raw, ar']; rw [hnsz_z, hot_z_eq]
                            have hm_st :
                                (FullMem c { s2 with core := { s2.core with arena := ar' } } ⋆
                                  R) _ :=
                              m5_fullMem_of_eq
                                (s1 := { s2 with core := { s2.core with arena := ar'_raw } })
                                (by assumption)
                                (congrArg (fun a => { s2.core with arena := a }) har_st_eq) rfl
                            have hstep_ok :=
                              otfs_shrink_loop_step har_len hinv_l hilt (by omega) hlv_pos
                            refine wp_join_group (ts := [i32, i32])
                              (fun (hpv', _hlv', ()) ml' => ∃ hp_n' : Nat,
                                (FullMem c { s2 with core := { s2.core with arena := ar' } } ⋆ R)
                                  ml' ∧
                                hpv' = BitVec.ofNat 32 hp_n' ∧
                                (hp_n' = 1 ∨ (1 ≤ hp_n' ∧ hp_n' < nsz + 1))) ?_ ?_
                            · rintro _ ⟨hpv', hlv', ⟨⟩⟩ ml' ⟨hp_n', hm_st', rfl, hhp'⟩
                              fa_fast_steps
                              rw [m5_bv32_ofNat_add1]
                              exact hJ2 _ _ ⟨nsz + 1, hp_n', ar', origMap ++ [i_nat], hm_st', rfl,
                                rfl, hhp', hstep_ok⟩
                            · intro Jhp hJhp; fa_fast_steps
                              · exact hJhp _ _ ⟨nsz, hm_st, rfl, Or.inr ⟨hns1, Nat.lt_succ_self _⟩⟩
                              · exact hJhp _ _ ⟨hp_n, hm_st, rfl,
                                  hhp_ok.imp_right fun ⟨h1, h2⟩ => ⟨h1, Nat.lt_succ_of_lt h2⟩⟩
                          · exact hJ2 _ _ ⟨nsz, hp_n, ar_cur, origMap, hm_c, rfl, rfl, hhp_ok,
                              m5_otfs_p2_skip_inv hinv_l hilt har_bd hv_bd hs2_lvl hot_c_eq
                                (‹¬ (0#32 : BitVec 32).toNat <
                                  (s2.core.lvl[(ar_cur[(cref.toNat + BitVec.toNat (3 : BitVec 64) +
                                    i_nat % 2 ^ 32) % 2 ^ 64]'hc_idx_bd).toNat / 2]'
                                    h2_lvl_bd).toNat›)⟩
                      · -- Exit Pass 2+3 -> header update -> `hp` swap -> `m5_loop4_sz_wp` -> ret
                        have hilt : i_nat = old_sz := by
                          have hba : ¬ i_nat % 2 ^ 32 < (s.core.arena[(cref.toNat +
                              BitVec.toNat (2 : BitVec 64)) % 2 ^ 64]'(by
                                simp only [BitVec.reduceToNat]; omega)).toNat := ‹_›
                          rw [Nat.mod_eq_of_lt (by omega),
                            m5_list_getElem_of_idx (j := cref.toNat + 2)
                              (hj := by omega) (by simp only [BitVec.reduceToNat]; omega), hsz_eq]
                            at hba
                          omega
                        subst i_nat
                        have hnsz3 : 3 ≤ nsz := by rw [hact]; exact hcnt3
                        have hnsz_lt : nsz < old_sz := by rw [hact]; exact hact_lt
                        have hhp1 : 1 ≤ hp_n := hhp_ok.elim (fun h => by omega) And.left
                        have hhp_lt : hp_n < nsz := hhp_ok.elim (fun h => by omega) And.right
                        have har1_len : ar1.length = c.arena_cap := by simp [ar1, har_len]
                        have har_c_0 : (cref.setWidth 64).toNat < ar_cur.length := by
                          rw [har_c, hcr0_z]; omega
                        have har_c_1 : (cref.setWidth 64 + 1#64).toNat < ar_cur.length := by
                          rw [har_c, hcr1_z]; omega
                        have har_c_2 : (cref.setWidth 64 + 2#64).toNat < ar_cur.length := by
                          rw [har_c, hcr2_z]; omega
                        have hhdr_eq :
                            ar_cur[cref.toNat]? = some (fullArenaHdrCore s2.core cref.toNat) := by
                          rw [hout_m cref.toNat (Or.inl (by omega))]
                          unfold fullArenaHdrCore
                          rw [hs2_base, List.getElem?_eq_getElem (by rw [har1_len]; omega),
                            Option.getD_some]
                        have hhdr_s2 : ar_cur[(cref.setWidth 64).toNat]'har_c_0 =
                            fullArenaHdrCore s2.core cref.toNat := by
                          have hg := hhdr_eq
                          rw [List.getElem?_eq_getElem (by rw [har_c]; omega)] at hg
                          exact (m5_list_getElem_of_idx hcr0_z).trans (Option.some.inj hg)
                        have hlen_ca : sc.LengthsOk c := hlen_c
                        fa_fast_steps_nogrp
                        refine wp_join_group (ts := []) (fun () ml3 =>
                            OtfsHdrPost c s s2 R cref old_sz nsz origMap ml3) ?_ ?_
                        · rintro _ ⟨⟩ ml3 ⟨ar3, hm3, har3_l, hhdr3, hsz3, hmap3, hpad3, hsent3,
                            hkeep3, hout3⟩
                          obtain ⟨s3, hs3_c, hs3_sc, hm3'⟩ :=
                            m5_otfs_opaque_state
                              { s2.core with arena := ar3 } s2.scratch hm3 rfl rfl
                          obtain ⟨hlen3_w, hw3_w, hnd3_w, hrefs3_w, hcref3_w, hsz_3_w, hng_3_w,
                            har3_l0_w, hlits_3_w, _⟩ :=
                            Full.otfs_large_shrink_ok hlen hw hnd hlen2' hw2 hnd2
                              (by rw [hs2_base]) (by rw [hs2_base]) (by rw [hs2_base])
                              (by rw [hs2_base]) (by rw [hs2_base]) (by rw [hs2_base]) hcref hng
                              hcref2 hng2 hsz2 hiu_cut hiu_te ht_u hr_u hlev_u hent_f hnsz3 hnsz_lt
                              hlm hpw hlt_m h01 hcov hmap3 har3_l hhdr3 hsz3 hpad3 hsent3 hkeep3
                              hout3
                          have hlen3 : s3.LengthsOk c := by
                            rw [show s3 = { s2 with core := { s2.core with arena := ar3 } } by
                              cases s3; simp only [FullState.mk.injEq]; exact ⟨hs3_c, hs3_sc⟩]
                            exact hlen3_w
                          have hw3 : FullAnalyzeSpecs.FullWitnessCutInv c F0 F_cur idx_u s3.core :=
                            by rw [hs3_c]; exact hw3_w
                          have hnd3 : Full.FullArenaVarsNodup s3 := by
                            rw [show s3 = { s2 with core := { s2.core with arena := ar3 } } by
                              cases s3; simp only [FullState.mk.injEq]; exact ⟨hs3_c, hs3_sc⟩]
                            exact hnd3_w
                          have hrefs3 : fullArenaClauseRefsCore s3.core =
                              fullArenaClauseRefsCore s2.core := by
                            change fullArenaClauseRefsCore s3.core =
                              fullArenaClauseRefsCore s2.core
                            rw [hs3_c]; exact hrefs3_w
                          have hcref3 : cref.toNat ∈ fullArenaClauseRefsCore s3.core := by
                            rw [hs3_c]; exact hcref3_w
                          have hsz_3 : fullArenaClauseSizeCore s3.core cref.toNat = nsz := by
                            rw [hs3_c]; exact hsz_3_w
                          have hng_3 : fullArenaClauseGarbCore s3.core cref.toNat = false := by
                            rw [hs3_c]; exact hng_3_w
                          have har3_l0 : s3.core.arena[cref.toNat + 3]? = some l0 := by
                            rw [hs3_c]; exact har3_l0_w
                          have hlits_3 : ∀ l ∈ fullArenaClauseLits s3 cref.toNat,
                              l ≠ uip.toNat ∧ l ∈ fullArenaClauseLits s cref.toNat := by
                            intro l hl; apply hlits_3_w l
                            simpa only [fullArenaClauseLits, fullArenaClauseLitsCore,
                              fullArenaClauseSizeCore, hs3_c] using hl
                          clear hw2 hnd2 hlen2' hw1' hnd1' hinv_l hlen_c hlen_ca
                          have har3_s3_l : s3.core.arena.length = c.arena_cap :=
                            hlen3.core_ok.arena_len_arr
                          have h_hp_bd_pre : (cref.setWidth 64 + 3#64 +
                              (BitVec.ofNat 32 hp_n).setWidth 64).toNat <
                              s3.core.arena.length :=
                            (otfs_ar_idx3_lt_len (cref := cref) (old_sz := old_sz) (j := hp_n)
                              hcap31 har3_s3_l (by omega) (Nat.lt_trans hhp_lt hnsz_lt)).2
                          fa_fast_steps_nogrp
                          refine wp_join_group (ts := []) (fun () ml4 =>
                            ∃ ar4 : List (BitVec 32),
                              (FullMem c { s3 with core := { s3.core with arena := ar4 } } ⋆
                                R) ml4 ∧
                              ar4.length = c.arena_cap ∧
                              FullAnalyzeSpecs.FullWitnessCutInv c F0 F_cur idx_u
                                { s3.core with arena := ar4 } ∧
                              Full.FullArenaVarsNodup
                                { s3 with core := { s3.core with arena := ar4 } } ∧
                              fullArenaClauseRefsCore { s3.core with arena := ar4 } =
                                fullArenaClauseRefsCore s3.core ∧
                              fullArenaClauseSizeCore { s3.core with arena := ar4 } cref.toNat =
                                nsz ∧
                              fullArenaClauseGarbCore { s3.core with arena := ar4 } cref.toNat =
                                false ∧
                              ar4[cref.toNat + 3]? = some l0 ∧
                              (∀ l ∈ fullArenaClauseLitsCore { s3.core with arena := ar4 }
                                cref.toNat, l ≠ uip.toNat ∧ l ∈ fullArenaClauseLits s cref.toNat))
                            ?_ ?_
                          · rintro _ ⟨⟩ ml4 ⟨ar4, hm4, har4_l, hw4, hnd4, hrefs4, hsz4, hng4,
                              har4_l0, hlits4⟩
                            obtain ⟨s4, hs4_c, hs4_sc, hm4'⟩ :=
                              m5_otfs_opaque_state { s2.core with arena := ar4 } s3.scratch hm4
                                (by dsimp only; rw [hs3_c]) rfl
                            clear hm4 hm3 hm3'
                            have hs4_sc' : s4.scratch = { s.scratch with wsort := wso_p } :=
                              hs4_sc.trans (hs3_sc.trans hs2_sc)
                            have hcv4 : s4.core.cur_vars = s.core.cur_vars := by
                              rw [hs4_c, hs2_base]
                            have h4bd : cref.toNat + 4 < ar4.length := by rw [har4_l]; omega
                            obtain ⟨hlen4, hw4', hnd4', hcref4, hng4', hlits4', hnl1_lt5, hdm4,
                              h2cv4, hcr_msb4, hrefs4_fin, h4_get, hshl0, h2l1_4, hoff64, hsz64⟩ :=
                              m5_otfs_s4_facts hcref hdm hrefs2 hs2_base hs3_c hlen3 hrefs3 hcref3
                                hs4_c hs4_sc hcv4 h2cv_lt hl0_lt hcr_lt31 hnsz3 (by omega) h4bd
                                har4_l hcb1_eq hcr4_z hw4 hnd4 hrefs4 hsz4 hng4 hlits4
                            have hl0_lt5 : l0.toNat < 2 * s4.core.cur_vars := by rwa [hcv4]
                            have hws4_c : s4.core.wstk = ws2 := by rw [hs4_c, hs2_base]
                            have hw4_bd0 : (BitVec.setWidth 64 l0 <<< (1 : Nat)).toNat <
                                s4.core.wvec.length := by
                              rw [hshl0, hlen4.core_ok.wvec_len]
                              have := hlen4.core_ok.cur_vars_le; omega
                            have hw4_bd1 : ((BitVec.setWidth 64 l0 <<< (1 : Nat)) +
                                (1 : BitVec 64)).toNat < s4.core.wvec.length := by
                              rw [h2l1_4, hlen4.core_ok.wvec_len]
                              have := hlen4.core_ok.cur_vars_le; omega
                            have h4_z_bd :
                                (BitVec.setWidth 64 cref + 3 + 1).toNat < s4.core.arena.length := by
                              rw [hs4_c, hs2_base]
                              have h4n : (BitVec.setWidth 64 cref + 3 + 1 : BitVec 64).toNat =
                                  cref.toNat + 4 := by
                                rw [show (BitVec.setWidth 64 cref + 3 + 1 : BitVec 64) =
                                  cref.setWidth 64 + 4#64 from hcb1_eq]
                                exact hcr4_z
                              rw [h4n, har4_l]; omega
                            fa_fast_steps_nogrp
                            refine wp_join_group (ts := []) (fun () ml_f =>
                              ∃ ws_f : List (BitVec 32),
                                (FullMem c { s4 with core := { s4.core with wstk := ws_f } } ⋆ R)
                                  ml_f ∧ ws_f.length = c.wcap ∧
                                ModeWatchesInv F_cur { s4.core with wstk := ws_f }) ?_ ?_
                            · rintro _ ⟨⟩ ml_f ⟨ws_f, hm_f, hws_fl, hmw_f⟩
                              fa_fast_steps
                              exact m5_otfs_fin_wp hlen hw hcref hng hiu_cut hiu_te ht_u hr_u
                                hsp_oom hs2_base hs4_c hs4_sc' hw4' hlen4 hnd4' hrefs4_fin
                                hcref4 hng4' hlits4' hws_fl hmw_f (by assumption) hQ
                            · intro J_out hJ_out
                              fa_fast_steps_nogrp
                              · rw [h4_get]
                                exact m5_loop4_sz_wp hdm4 hw4'.watches hlen4 h2cv4 hl0_lt5 hnl1_lt5
                                  hws4_c hcr_lt31 hcref4 hoff64 hsz64 hm4' hJ_out
                              · exact absurd hcr_msb4 ‹_›
                          · intro J4 hJ4
                            exact m5_otfs_j4_swap_wp hlen3 hw3 hnd3 hcref3 hsz_3 hng_3 har3_l0
                              hlits_3 har3_s3_l hcap31 har_le hold_bd hnsz_lt hcr4_z hcb1_eq hhp1
                              hhp_lt hm3' hJ4
                        · intro J3 hJ3
                          have hsz_at : s.core.arena[(cref.setWidth 64 + 2#64).toNat]'hcr2_bd =
                              BitVec.ofNat 32 old_sz :=
                            (m5_list_getElem_of_idx (hj := by omega) hcr2_z).trans hsz32
                          exact m5_otfs_j3_hdr_wp har_len har_c (by omega) hcap31 h4_old hnsz3
                            hnsz_lt hcr0_z hcr1_z hcr2_z hcr3_z hhdr_s2 hsz_at rfl hlits_info
                            hmapeq hout_m har1_q' har1_s2 hhdr_eq (by assumption) hJ3
                    · intro L2 hL2; fa_fast_steps
                      have hm2_ar1 :
                          (FullMem c { s2 with core := { s2.core with arena := ar1 } } ⋆ R) m2 :=
                        m5_fullMem_of_eq (s1 := s2) hm2_s2 (by rw [hs2_base]) rfl
                      obtain ⟨omap0, hinv0⟩ := otfs_large_loop2_init har_len (by omega) h4_old hs01
                      exact hL2 (old_sz - 2) _ m2
                        ⟨2, 1, 1, ar1, omap0, hm2_ar1, rfl, rfl, rfl, Or.inl rfl, hinv0⟩
                · -- `full_watch_push` failed: atomic OOM before any arena swap / unwatch!
                  have hok_f : ok_p = false := Bool.eq_false_iff.mpr hok_pt_c
                  subst hok_f
                  obtain ⟨hsame_f, _⟩ := hok_pf rfl
                  have hsp_w_eq : s_p.core =
                      { s_d.core with wvec := wv_p, wstk := ws_p, wlen := wl_p,
                                      wusable := wu_p } := congrArg FullState.core hsp_d_eq
                  have hm_wpf : ModeWatchesInv F_cur s_p.core := by
                    rw [hsp_w_eq]
                    exact fa_watchPush_fail_preserves hsd_dm hw_d.watches hlay_p fun l hl =>
                      if hle : l = nl1p.toNat then
                        by subst l; exact hsame_f (by rw [hsd_cv]; exact hnl1p_lt)
                      else hother_p l hl hle
                  have hw_pf : Full.FullWitnessCutInv c F0 F_cur cut s_p.core := by
                    rw [hsp_w_eq] at hm_wpf ⊢; exact m5_canonCut_with_watches hw_d hm_wpf
                  fa_fast_steps
                  exact m5_otfs_oom_early_wp hsp_c hsp_sc hlen_p' hw_pf hnd hiu_cut
                    (by assumption) hQ
            · intro Jd hJd
              exact m5_wstack_ensure2_ret_false_wp hDefrag hlen hdm hw_can.watches hm
                (fun s_i wv_i ws_i wl_i wu_i wso_i ml_o hsi_c hsi_sc hlen_i hmw_i hm_o =>
                  m5_otfs_oom_early_wp hsi_c hsi_sc hlen_i (by
                    have hw_i : Full.FullWitnessCutInv c F0 F_cur cut s_i.core := by
                      rw [hsi_c] at hmw_i ⊢; exact m5_canonCut_with_watches hw_can hmw_i
                    exact hw_i) hnd hiu_cut hm_o hQ)
                (fun xs ml_d ⟨s_d, wv_d, ws_d, wl_d, wu_d, wso_d, hsd_c, hsd_sc, hlen_d, hmw_d,
                    hm_d⟩ =>
                  hJd xs ml_d ⟨s_d, wv_d, ws_d, wl_d, wu_d, wso_d, hsd_c, hsd_sc, hlen_d, by
                    rw [hsd_c] at hmw_d ⊢; exact m5_canonCut_with_watches hw_can hmw_d, hm_d⟩)
        · intro L1b hL1b; fa_fast_steps
          exact hL1b (old_sz - 2) _ m ⟨2, rfl, rfl, Nat.le_refl _, by omega, rfl, hu_lt⟩
    · rintro B1 L1 r ⟨cnt, iv, ⟨⟩⟩ ml hB1 ih1 ⟨i_nat, hml, rfl, hi2, hile, rfl, rfl, hcnt_lt3⟩
      subst ml; fa_fast_steps_nogrp
      · have hilt : i_nat < old_sz := by
          have hb : (BitVec.ofNat 32 i_nat).toNat <
              (s.core.arena[(cref.setWidth 64 + 2#64).toNat]'hcr2_bd).toNat := ‹_›
          rw [bv32_ofNat_toNat (by omega), m5_list_getElem_of_idx (hj := by omega) hcr2_z,
            hsz_eq] at hb
          exact hb
        obtain ⟨har_bd, hz_bd, hc_bd, hc_idx, hot_eq, _, hlvl1_bd_len, hv_bd⟩ :=
          otfs_large_loop1_step_bds hcap31 hcv_le hlvl_len har_len (by omega) hilt hlits_info
        fa_fast_steps_nogrp
        refine wp_join_group (ts := [i32]) (fun (cnt', ()) ml' => ml' = m ∧
            cnt' = BitVec.ofNat 32 (1 + Full.otfsActCnt s.core cref.toNat (i_nat + 1)) ∧
            1 + Full.otfsActCnt s.core cref.toNat (i_nat + 1) < 3) ?_ ?_
        · rintro _ ⟨cnt', ⟨⟩⟩ ml' ⟨hml', rfl, hlt3'⟩; subst ml'; fa_fast_steps
          rw [m5_bv32_ofNat_add1]
          exact ih1 (old_sz - (i_nat + 1)) _ m (by omega)
            ⟨i_nat + 1, rfl, rfl, by omega, by omega, rfl, rfl, hlt3'⟩
        · intro J1 hJ1; fa_fast_steps
          · have hlv_pos := m5_otfs_p1_lv_pos har_bd hv_bd hot_eq ‹BitVec.toNat 0 < _›
            exact hB1 _ m ⟨rfl, Or.inr (m5_otfs_p1_brk hi2 hilt hlv_pos hcnt_lt3 hc)⟩
          · have hlv_pos := m5_otfs_p1_lv_pos har_bd hv_bd hot_eq ‹BitVec.toNat 0 < _›
            obtain ⟨hceq, hlt3'⟩ := m5_otfs_p1_inc hi2 hlv_pos hcnt_lt3 hc
            rw [hceq]; exact hJ1 _ _ ⟨rfl, rfl, hlt3'⟩
          · have hlv_0 := m5_otfs_p1_lv_zero har_bd hv_bd hot_eq ‹¬ BitVec.toNat 0 < _›
            have hcnt_eq : Full.otfsActCnt s.core cref.toNat (i_nat + 1) =
                Full.otfsActCnt s.core cref.toNat i_nat := by
              rw [Full.otfsActCnt_succ hi2, ite_eq_right hlv_0, Nat.add_zero]
            exact hJ1 _ _ ⟨rfl, congrArg (fun x => BitVec.ofNat 32 (1 + x)) hcnt_eq.symm,
              by rw [hcnt_eq]; exact hcnt_lt3⟩
      · exact hB1 _ m ⟨rfl, Or.inl (by rw [bv32_ofNat_toNat (by omega)]; exact hcnt_lt3)⟩
    · intro B1 L1 _ hL1; fa_fast_steps
      exact hL1 (old_sz - 2) (1#32, 2#32, ()) m ⟨2, rfl, rfl, Nat.le_refl _, by omega, rfl,
        rfl, by rw [show Full.otfsActCnt s.core cref.toNat 2 = 0 from rfl]; omega⟩
  · intro J0 hJ0; fa_fast_steps
    · exact hJ0 _ _ ⟨rfl, Or.inr ⟨hor1, hor0 ▸ ‹_›⟩⟩
    · exact hfail
    · have h1_eq : s.core.arena[(cref.setWidth 64 + 3#64 + 1#64).toNat]'hcb1_bd = uip := by
        refine (m5_list_getElem_of_idx (j := (cref.toNat + BitVec.toNat (3 : BitVec 64) +
          BitVec.toNat (1 : BitVec 64)) % 2 ^ 64) ?_).trans hc
        rw [hcb1_z]; simp only [BitVec.reduceToNat]; omega
      exact hJ0 _ _ ⟨rfl, Or.inl ⟨hor0, hor1 ▸ h1_eq⟩⟩

end OtfsLargeProof

end LeanQbe.T.Examples.Kissat.FullM5Otfs
