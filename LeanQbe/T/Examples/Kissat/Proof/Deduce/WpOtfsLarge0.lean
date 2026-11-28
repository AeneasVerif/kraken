/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Deduce.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Deduce.WpOtfsBin
public import LeanQbe.T.Examples.Kissat.Src.Deduce
public import LeanQbe.T.Logic.CanonicalEnv
import LeanQbe.T.Examples.Kissat.Proof.Deduce.WpCommon
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts1
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts2
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics1
import LeanQbe.T.Examples.Kissat.Proof.Spec.WitnessInv
import Kraken.Mem
import Kraken.Separation

/-!
# Large OTFS Data, Shrink & Invariant Helpers (`Proof.Deduce.WpOtfsLarge0`)

Pure BitVec, `WatchSliceOk`, active-literal count, swap01, in-place shrink, Step-13 header, and
loop-bounds lemmas for `full_otfs_large_wp` (`public section`, `0` legacy imports, `0` `import all`,
`0` `@[expose]` on theorems/lemmas/sections, every declaration `<= 450` LOC, every line `<= 100`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Deduce

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open Kraken.Bedrock2.Test

open scoped FullArenaTactics DeduceTactics

/-! ## 1. BitVec, `WatchSliceOk` & Active-Literal Helpers -/

theorem otfs_bv32_lt_highbit_iff (r : BitVec 32) :
    r.toNat < 0x80000000 ↔ (r &&& 0x80000000#32) = 0#32 := by
  constructor
  · intro h
    ext i hi
    simp only [BitVec.getElem_and, BitVec.getElem_zero]
    by_cases h31 : i = 31
    · subst h31; rw [BitVec.getElem_eq_testBit_toNat, Nat.testBit_lt_two_pow (by omega)]; simp
    · rw [show (0x80000000#32)[i] = false from by
        rw [BitVec.getElem_eq_testBit_toNat, show (0x80000000#32).toNat = 2 ^ 31 from rfl,
          Nat.testBit_two_pow]; exact decide_eq_false (Ne.symm h31)]
      simp
  · intro h
    have h31 : (r &&& 0x80000000#32)[31] = false := by rw [h]; rfl
    rw [BitVec.getElem_and, show (0x80000000#32)[31] = true from rfl, Bool.and_true] at h31
    have htb := BitVec.getElem_eq_testBit_toNat (x := r) (i := 31) (by decide)
    rw [h31] at htb
    have hmod : (r.toNat / 2 ^ 31) % 2 = 0 := by
      have h1 : (r.toNat >>> 31) &&& 1 = 0 := by
        simpa [Nat.testBit, bne_iff_ne] using htb.symm
      rwa [Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod] at h1
    have hlt := r.isLt; omega

theorem otfs_bv32_lshr31_nat_cases (w : BitVec 32) :
    ((w &&& 0x80000000#32) = 0#32 → (w >>> (31 : Nat)).toNat = 0) ∧
    ((w &&& 0x80000000#32) ≠ 0#32 → (w >>> (31 : Nat)).toNat = 1) ∧
    (w >>> (31 : Nat)).toNat ≤ 1 := by
  have hsh : (w >>> (31 : Nat)).toNat = w.toNat / 2 ^ 31 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hlt := w.isLt
  have hiff := otfs_bv32_lt_highbit_iff w
  refine ⟨fun h => ?_, fun h => ?_, ?_⟩
  · have := hiff.mpr h; rw [hsh]; omega
  · have hge : ¬ w.toNat < 0x80000000 := fun hlt' => h (hiff.mp hlt')
    rw [hsh]; omega
  · rw [hsh]; omega

theorem otfs_bv32_ofNat_add1 (n : Nat) :
    BitVec.ofNat 32 n + 1 = BitVec.ofNat 32 (n + 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, show (1 : BitVec 32).toNat = 1 from rfl,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_add_mod]

theorem otfs_bv_idx3_64 (cref : BitVec 32) (k : Nat) (hbd : cref.toNat + 3 + k < 2 ^ 32)
    (hk : k < 2 ^ 32) :
    (cref.setWidth 64 + 3#64 + (BitVec.ofNat 32 k).setWidth 64).toNat = cref.toNat + 3 + k := by
  have hz1 : (cref.setWidth 64).toNat = cref.toNat := zext_toNat cref (by decide)
  have hz2 : ((BitVec.ofNat 32 k).setWidth 64).toNat = k := by
    rw [zext_toNat _ (by decide), bv32_ofNat_toNat hk]
  bv_omega

theorem otfs_watchSlice_split_last {F_cur : List (List Nat)} {k : FullCoreState} :
    ∀ {lit p len : Nat}, WatchSliceOk F_cur k lit p len → 0 < len →
      (∃ w0, k.wstk[p + len - 1]? = some w0 ∧ (w0 &&& 0x80000000#32) ≠ 0#32 ∧
        w0 ≠ 0xFFFFFFFF#32 ∧ (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k.cur_vars ∧
        (cnfOfClauses F_cur).EntailsClause
          (cnfClause [lit, (w0 &&& 0x7FFFFFFF#32).toNat]) ∧
        WatchSliceOk F_cur k lit p (len - 1)) ∨
      (2 ≤ len ∧ ∃ w0 cr, k.wstk[p + len - 2]? = some w0 ∧
        k.wstk[p + len - 1]? = some cr ∧ (w0 &&& 0x80000000#32) = 0#32 ∧
        cr.toNat < 0x80000000 ∧ cr.toNat ∈ fullArenaClauseRefsCore k ∧
        WatchSliceOk F_cur k lit p (len - 2))
  | _, _, _, .empty, hlen => absurd hlen (Nat.lt_irrefl 0)
  | lit, p, _, .bin (rem := rem) hp hflag hne hlt hent hrest, _ => by
    cases rem with
    | zero =>
      cases hrest
      exact Or.inl ⟨_, by simpa using hp, hflag, hne, hlt, hent, .empty⟩
    | succ rem' =>
      rcases otfs_watchSlice_split_last hrest (Nat.zero_lt_succ _) with
        ⟨w', hw', hf', hn', hl', he', hpre'⟩ |
        ⟨h2, w', cr', hw', hcr', hf', hl', hr', hpre'⟩
      · exact Or.inl ⟨w', by rwa [show p + (rem' + 1 + 1) - 1 = p + 1 + (rem' + 1) - 1 by omega],
          hf', hn', hl', he', by
            rw [show rem' + 1 + 1 - 1 = rem' + 1 - 1 + 1 by omega]
            exact .bin hp hflag hne hlt hent hpre'⟩
      · exact Or.inr ⟨by omega, w', cr',
          by rwa [show p + (rem' + 1 + 1) - 2 = p + 1 + (rem' + 1) - 2 by omega],
          by rwa [show p + (rem' + 1 + 1) - 1 = p + 1 + (rem' + 1) - 1 by omega],
          hf', hl', hr', by
            rw [show rem' + 1 + 1 - 2 = rem' + 1 - 2 + 1 by omega]
            exact .bin hp hflag hne hlt hent hpre'⟩
  | lit, p, _, .large (rem := rem) hp hp1 hflag hlt href hrest, _ => by
    cases rem with
    | zero =>
      cases hrest
      exact Or.inr ⟨Nat.le_refl 2, _, _, by simpa using hp, by simpa using hp1,
        hflag, hlt, href, .empty⟩
    | succ rem' =>
      rcases otfs_watchSlice_split_last hrest (Nat.zero_lt_succ _) with
        ⟨w', hw', hf', hn', hl', he', hpre'⟩ |
        ⟨h2, w', cr', hw', hcr', hf', hl', hr', hpre'⟩
      · exact Or.inl ⟨w', by rwa [show p + (rem' + 1 + 2) - 1 = p + 2 + (rem' + 1) - 1 by omega],
          hf', hn', hl', he', by
            rw [show rem' + 1 + 2 - 1 = rem' + 1 - 1 + 2 by omega]
            exact .large hp hp1 hflag hlt href hpre'⟩
      · exact Or.inr ⟨by omega, w', cr',
          by rwa [show p + (rem' + 1 + 2) - 2 = p + 2 + (rem' + 1) - 2 by omega],
          by rwa [show p + (rem' + 1 + 2) - 1 = p + 2 + (rem' + 1) - 1 by omega],
          hf', hl', hr', by
            rw [show rem' + 1 + 2 - 2 = rem' + 1 - 2 + 2 by omega]
            exact .large hp hp1 hflag hlt href hpre'⟩

theorem otfs_watchSlice_append {F_cur : List (List Nat)} {k : FullCoreState}
    {lit p len1 len2 : Nat}
    (h1 : WatchSliceOk F_cur k lit p len1) (h2 : WatchSliceOk F_cur k lit (p + len1) len2) :
    WatchSliceOk F_cur k lit p (len1 + len2) := by
  induction h1 with
  | empty => simpa using h2
  | @bin p rem w0 hp hflag hne hlt hent _ ih =>
    rw [show rem + 1 + len2 = (rem + len2) + 1 by omega]
    exact .bin hp hflag hne hlt hent
      (ih (by simpa [show p + 1 + rem = p + (rem + 1) by omega] using h2))
  | @large p rem w0 cr hp hp1 hflag hlt href _ ih =>
    rw [show rem + 2 + len2 = (rem + len2) + 2 by omega]
    exact .large hp hp1 hflag hlt href
      (ih (by simpa [show p + 2 + rem = p + (rem + 2) by omega] using h2))

@[expose] def otfsActCnt (k : FullCoreState) (cref j : Nat) : Nat :=
  ((List.range j).drop 2).countP fun q =>
    decide (0 < (k.lvl[(k.arena[cref + 3 + q]?.getD 0#32).toNat / 2]?.getD 0#32).toNat)

theorem otfsActCnt_le (k : FullCoreState) (cref j : Nat) :
    otfsActCnt k cref j ≤ j - 2 := by
  unfold otfsActCnt; refine Nat.le_trans List.countP_le_length ?_
  simp [List.length_drop, List.length_range]

theorem otfsActCnt_succ {k : FullCoreState} {cref j : Nat} (hj : 2 ≤ j) :
    otfsActCnt k cref (j + 1) = otfsActCnt k cref j +
      if 0 < (k.lvl[(k.arena[cref + 3 + j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat then 1
      else 0 := by
  unfold otfsActCnt
  rw [List.range_succ, List.drop_append_of_le_length (by simp [List.length_range]; omega),
    List.countP_append]; simp [List.countP_cons]

theorem otfsActCnt_mono {k : FullCoreState} {cref : Nat} :
    ∀ {i j : Nat}, 2 ≤ i → i ≤ j → otfsActCnt k cref i ≤ otfsActCnt k cref j := by
  intro i j hi hij
  induction hij with
  | refl => exact Nat.le_refl _
  | @step m hm ih => rw [otfsActCnt_succ (Nat.le_trans hi hm)]; omega

/-! ## 2. Pure Swap01 & In-Place Shrink Semantics -/

theorem otfs_large_swap01 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {s : FullState} (hlen : s.LengthsOk c)
    (hw : FullWitnessCutInv c F0 F_cur cut s.core) (hnd : FullArenaVarsNodup s)
    {cref l0 uip : BitVec 32} (hcref : cref.toNat ∈ fullArenaClauseRefs s)
    (hng : fullArenaClauseGarb s cref.toNat = false)
    (hs01 : (l0 = s.core.arena[cref.toNat + 3]?.getD 0#32 ∧
        s.core.arena[cref.toNat + 4]?.getD 0#32 = uip) ∨
      (l0 = s.core.arena[cref.toNat + 4]?.getD 0#32 ∧
        s.core.arena[cref.toNat + 3]?.getD 0#32 = uip)) :
    let ar1 := (s.core.arena.set (cref.toNat + 3) l0).set (cref.toNat + 4) uip
    let s1 : FullState := { s with core := { s.core with arena := ar1 } }
    FullWitnessCutInv c F0 F_cur cut s1.core ∧ FullArenaVarsNodup s1 ∧
    fullArenaClauseRefs s1 = fullArenaClauseRefs s ∧
    fullArenaClauseSize s1 cref.toNat = fullArenaClauseSize s cref.toNat ∧
    fullArenaClauseGarb s1 cref.toNat = false ∧
    (∀ q, 2 ≤ q → ar1[cref.toNat + 3 + q]? = s.core.arena[cref.toNat + 3 + q]?) ∧
    ar1[cref.toNat + 3]? = some l0 ∧ ar1[cref.toNat + 4]? = some uip := by
  intro ar1 s1; have hwf := hw.arena.refs_wf cref.toNat hcref
  have har_len := hlen.core_ok.arena_len_arr; have har_le := hlen.core_ok.arena_len_le
  have h3 : cref.toNat + 3 < s.core.arena.length := by omega
  have h4 : cref.toNat + 4 < s.core.arena.length := by omega
  rcases hs01 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have ha1 : ar1 = s.core.arena := by
      dsimp only [ar1]; rw [List.getElem?_eq_getElem h3, List.getElem?_eq_getElem h4,
        Option.getD_some, Option.getD_some, List.set_getElem_self, List.set_getElem_self]
    have h0 : s.core.arena[cref.toNat + 3]? = some (s.core.arena[cref.toNat + 3]?.getD 0#32) := by
      rw [List.getElem?_eq_getElem h3, Option.getD_some]
    have h1 : s.core.arena[cref.toNat + 4]? = some (s.core.arena[cref.toNat + 4]?.getD 0#32) := by
      rw [List.getElem?_eq_getElem h4, Option.getD_some]
    simpa only [s1, ha1] using (⟨hw, hnd, rfl, rfl, hng, fun _ _ => rfl, h0, h1⟩ :
      FullWitnessCutInv c F0 F_cur cut s.core ∧ FullArenaVarsNodup s ∧
      fullArenaClauseRefs s = fullArenaClauseRefs s ∧
      fullArenaClauseSize s cref.toNat = fullArenaClauseSize s cref.toNat ∧
      fullArenaClauseGarb s cref.toNat = false ∧
      (∀ q, 2 ≤ q → s.core.arena[cref.toNat + 3 + q]? = s.core.arena[cref.toNat + 3 + q]?) ∧
      s.core.arena[cref.toNat + 3]? = some (s.core.arena[cref.toNat + 3]?.getD 0#32) ∧
      s.core.arena[cref.toNat + 4]? = some (s.core.arena[cref.toNat + 4]?.getD 0#32))
  · obtain ⟨hw1, hrefs1, hsz1, hng1, hperm1, hother1⟩ :=
      fa_swapCl_preserves_fullWitnessCut hlen.core_ok hw hcref (i := 0) (j := 1)
        (by omega) (by omega)
    have hnd1 : FullArenaVarsNodup s1 := fun r hr hngr => by
      change r ∈ fullArenaClauseRefsCore s1.core at hr; rw [hrefs1] at hr
      by_cases hrc : r = cref.toNat
      · subst r; exact (hperm1.map (· / 2)).nodup_iff.mpr (hnd _ hr hng)
      · have ho := hother1 r hr hrc; change ((fullArenaClauseLitsCore s1.core r).map (· / 2)).Nodup
        rw [ho.2.2]; exact hnd r hr (by
          change fullArenaClauseGarbCore s.core r = false; rw [← ho.2.1]; exact hngr)
    refine ⟨hw1, hnd1, hrefs1, hsz1, hng1.trans hng, fun q hq => by
        dsimp only [ar1]; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)],
      by dsimp only [ar1]; rw [List.getElem?_set_ne (by omega), List.getElem?_set_self h3],
      by dsimp only [ar1]; rw [List.getElem?_set_self (by simp [h4])]⟩

private theorem pw_lt_map_nodup {α : Type} (f : Nat → α) (bd : Nat)
    (hinj : ∀ p1 p2, p1 < bd → p2 < bd → f p1 = f p2 → p1 = p2) :
    ∀ l : List Nat, l.Pairwise (· < ·) → (∀ p ∈ l, p < bd) → (l.map f).Nodup
  | [], _, _ => List.nodup_nil
  | p :: l, hpw, hlt => by
    rw [List.pairwise_cons] at hpw; rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => ?_, pw_lt_map_nodup f bd hinj l hpw.2 fun q hq =>
      hlt q (List.mem_cons_of_mem _ hq)⟩
    obtain ⟨q, hq, hfeq⟩ := List.mem_map.mp hm
    have heq := hinj q p (hlt q (List.mem_cons_of_mem _ hq)) (hlt p List.mem_cons_self) hfeq
    have := hpw.1 q hq; omega

theorem otfs_large_shrink_ok {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut idx_u nsz : Nat} {s s2 : FullState} {cref l0 uip : BitVec 32}
    {ar3 : List (BitVec 32)} {origMap : List Nat}
    (hlen : s.LengthsOk c) (hw : FullWitnessCutInv c F0 F_cur cut s.core)
    (hnd : FullArenaVarsNodup s) (hlen2 : s2.LengthsOk c)
    (hw2 : FullWitnessCutInv c F0 F_cur cut s2.core) (hnd2 : FullArenaVarsNodup s2)
    (hcv2 : s2.core.cur_vars = s.core.cur_vars) (htrl2 : s2.core.trl = s.core.trl)
    (hrsns2 : s2.core.rsns = s.core.rsns) (hlvl2 : s2.core.lvl = s.core.lvl)
    (hte2 : s2.core.trail_end = s.core.trail_end) (hcl2 : s2.core.cur_level = s.core.cur_level)
    (hcref : cref.toNat ∈ fullArenaClauseRefs s) (hng : fullArenaClauseGarb s cref.toNat = false)
    (hcref2 : cref.toNat ∈ fullArenaClauseRefs s2)
    (hng2 : fullArenaClauseGarb s2 cref.toNat = false)
    (hsz2 : fullArenaClauseSize s2 cref.toNat = fullArenaClauseSize s cref.toNat)
    (hiu_cut : idx_u < cut) (hiu_te : idx_u < s.core.trail_end)
    (ht_u : (s.core.trl[idx_u]?.getD 0#32).toNat = uip.toNat)
    (hr_u : s.core.rsns[uip.toNat / 2]?.getD 0xFFFFFFFF#32 = cref)
    (hlev_u : (s.core.lvl[uip.toNat / 2]?.getD 0#32).toNat = s.core.cur_level)
    (hent_f : (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((fullArenaClauseLits s cref.toNat).filter fun l =>
        decide (l ≠ uip.toNat ∧ (0 < (s.core.lvl[l / 2]?.getD 0#32).toNat ∨
          l = (s.core.arena[cref.toNat + 3]?.getD 0#32).toNat ∨
          l = (s.core.arena[cref.toNat + 4]?.getD 0#32).toNat)))))
    (hnsz3 : 3 ≤ nsz) (hnsz_lt : nsz < fullArenaClauseSize s cref.toNat)
    (hlen_map : origMap.length = nsz) (hpw : origMap.Pairwise (· < ·))
    (hlt_map : ∀ p ∈ origMap, p < fullArenaClauseSize s cref.toNat)
    (h01 : (l0 = s.core.arena[cref.toNat + 3]?.getD 0#32 ∧
        s.core.arena[cref.toNat + 4]?.getD 0#32 = uip ∧ 0 ∈ origMap ∧ 1 ∉ origMap) ∨
      (l0 = s.core.arena[cref.toNat + 4]?.getD 0#32 ∧
        s.core.arena[cref.toNat + 3]?.getD 0#32 = uip ∧ 1 ∈ origMap ∧ 0 ∉ origMap))
    (hcov : ∀ p, 2 ≤ p → p < fullArenaClauseSize s cref.toNat →
      0 < (s.core.lvl[(s.core.arena[cref.toNat + 3 + p]?.getD 0#32).toNat / 2]?.getD 0#32).toNat →
      p ∈ origMap)
    (hmap_eq : ∀ k, k < nsz →
      ar3[cref.toNat + 3 + k]? = s.core.arena[cref.toNat + 3 + origMap[k]?.getD 0]?)
    (har3_len : ar3.length = c.arena_cap)
    (hhdr3 : ar3[cref.toNat]? = some
      (if (fullArenaHdrCore s2.core cref.toNat &&& 0x00800000#32) = 0#32 then
        fullArenaHdrCore s2.core cref.toNat ||| 0x00800000#32
      else fullArenaHdrCore s2.core cref.toNat))
    (hsz3 : ar3[cref.toNat + 2]? = some (BitVec.ofNat 32 nsz))
    (hpad_ne : ∀ j, nsz ≤ j → j < fullArenaClauseSize s cref.toNat - 1 →
      ar3[cref.toNat + 3 + j]? = s2.core.arena[cref.toNat + 3 + j]?)
    (hlast_sent : (fullArenaHdrCore s2.core cref.toNat &&& 0x00800000#32) = 0#32 →
      ar3[cref.toNat + 3 + fullArenaClauseSize s cref.toNat - 1]? = some 0xFFFFFFFF#32)
    (hlast_keep : (fullArenaHdrCore s2.core cref.toNat &&& 0x00800000#32) ≠ 0#32 →
      ar3[cref.toNat + 3 + fullArenaClauseSize s cref.toNat - 1]? =
        s2.core.arena[cref.toNat + 3 + fullArenaClauseSize s cref.toNat - 1]?)
    (hout : ∀ i, i < cref.toNat ∨ cref.toNat + 3 + fullArenaClauseSize s cref.toNat ≤ i →
      ar3[i]? = s2.core.arena[i]?) :
    let s3 : FullState := { s2 with core := { s2.core with arena := ar3 } }
    s3.LengthsOk c ∧ FullWitnessCutInv c F0 F_cur idx_u s3.core ∧ FullArenaVarsNodup s3 ∧
    fullArenaClauseRefsCore s3.core = fullArenaClauseRefsCore s2.core ∧
    cref.toNat ∈ fullArenaClauseRefsCore s3.core ∧
    fullArenaClauseSizeCore s3.core cref.toNat = nsz ∧
    fullArenaClauseGarbCore s3.core cref.toNat = false ∧ ar3[cref.toNat + 3]? = some l0 ∧
    (∀ l ∈ fullArenaClauseLitsCore s3.core cref.toNat,
      l ≠ uip.toNat ∧ l ∈ fullArenaClauseLits s cref.toNat) ∧
    (ar3[cref.toNat + 4]?.getD 0#32).toNat < 2 * s.core.cur_vars := by
  intro s3; let k3 : FullCoreState := s3.core
  let old_sz := fullArenaClauseSizeCore s.core cref.toNat
  unfold fullArenaClauseSize at hsz2 hnsz_lt hlt_map hpad_ne hlast_sent hlast_keep
  have hwf := hw.arena.refs_wf cref.toNat hcref; have hwf2 := hw2.arena.refs_wf cref.toNat hcref2
  have har_len := hlen.core_ok.arena_len_arr; have har_le := hlen.core_ok.arena_len_le
  have har2_le := hlen2.core_ok.arena_len_le
  have hold_bd : cref.toNat + 3 + old_sz ≤ s.core.arena_len := by
    have := hwf.2.2.1; have := hwf.2.2.2.1; dsimp only [old_sz]; omega
  have hnsz_s2 : nsz < fullArenaClauseSizeCore s2.core cref.toNat := by
    change fullArenaClauseSizeCore s2.core cref.toNat = old_sz at hsz2; omega
  have hnsz32 : nsz < 2 ^ 32 := by
    have : old_sz < 2 ^ 32 := (s.core.arena[cref.toNat + 2]?.getD 0#32).isLt; omega
  have hlits_rw : fullArenaClauseLits s cref.toNat =
      (List.range old_sz).map fun p => (s.core.arena[cref.toNat + 3 + p]?.getD 0#32).toNat := by
    have htake : (s.core.arena.drop (cref.toNat + 3)).take old_sz =
        (List.range old_sz).map fun p => s.core.arena[cref.toNat + 3 + p]?.getD 0#32 := by
      refine List.ext_getElem (by simp; omega) fun k _ hk2 => ?_
      simp only [List.length_map, List.length_range] at hk2
      simp only [List.getElem_take, List.getElem_drop, List.getElem_map, List.getElem_range]
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    unfold fullArenaClauseLits fullArenaClauseLitsCore
    change (((s.core.arena.drop (cref.toNat + 3)).take old_sz).map BitVec.toNat) = _
    rw [htake, List.map_map]; rfl
  have hszv : fullArenaClauseSizeCore k3 cref.toNat = nsz := by
    unfold fullArenaClauseSizeCore k3 s3; rw [hsz3, Option.getD_some, bv32_ofNat_toNat hnsz32]
  have hlits_map : fullArenaClauseLitsCore k3 cref.toNat =
      origMap.map fun p => (s.core.arena[cref.toNat + 3 + p]?.getD 0#32).toNat := by
    have htake3 : (ar3.drop (cref.toNat + 3)).take nsz =
        origMap.map fun p => s.core.arena[cref.toNat + 3 + p]?.getD 0#32 := by
      refine List.ext_getElem (by simp [har3_len, hlen_map]; omega) fun k _ hk2 => ?_
      simp only [List.length_map, hlen_map] at hk2
      simp only [List.getElem_take, List.getElem_drop, List.getElem_map]
      have hmp_lt : origMap[k]'(by omega) < old_sz :=
        hlt_map _ (List.getElem_mem (by omega : k < origMap.length))
      have hm := hmap_eq k hk2
      have hbo : cref.toNat + 3 + origMap[k] < s.core.arena.length := by omega
      rw [List.getElem?_eq_getElem (by rw [har3_len]; omega),
        List.getElem?_eq_getElem (by omega : k < origMap.length), Option.getD_some,
        List.getElem?_eq_getElem hbo] at hm
      exact (Option.some.inj hm).trans (by rw [List.getElem?_eq_getElem hbo, Option.getD_some])
    unfold fullArenaClauseLitsCore; dsimp only [k3, s3]; rw [hszv, htake3, List.map_map]; rfl
  have hinj_old : ∀ p1 p2, p1 < old_sz → p2 < old_sz →
      (s.core.arena[cref.toNat + 3 + p1]?.getD 0#32).toNat / 2 =
      (s.core.arena[cref.toNat + 3 + p2]?.getD 0#32).toNat / 2 → p1 = p2 := by
    have hnd_r := hnd cref.toNat hcref hng; rw [hlits_rw, List.map_map] at hnd_r
    have hget := List.pairwise_iff_getElem.mp (List.pairwise_map.mp hnd_r)
    intro p1 p2 hp1 hp2 heq; exact Classical.byContradiction fun hne =>
      (Nat.lt_or_gt_of_ne hne).elim
        (fun h => hget p1 p2 (by simp; omega) (by simp; omega) h (by simpa using heq))
        (fun h => hget p2 p1 (by simp; omega) (by simp; omega) h (by simpa using heq.symm))
  have hlits_sub : ∀ l ∈ fullArenaClauseLitsCore k3 cref.toNat,
      l ≠ uip.toNat ∧ l ∈ fullArenaClauseLits s cref.toNat := fun l hl => by
    rw [hlits_map, List.mem_map] at hl; obtain ⟨p, hp_in, rfl⟩ := hl; have hp_lt := hlt_map p hp_in
    refine ⟨fun heq => ?_, by rw [hlits_rw, List.mem_map]; exact ⟨p, List.mem_range.mpr hp_lt, rfl⟩⟩
    rcases h01 with ⟨_, hu4, _, h1no⟩ | ⟨_, hu3, _, h0no⟩
    · exact h1no (hinj_old p 1 hp_lt (by omega) (by rw [heq, hu4]) ▸ hp_in)
    · exact h0no (hinj_old p 0 hp_lt (by omega) (by rw [heq, hu3]) ▸ hp_in)
  have hlits_lt' : ∀ l ∈ fullArenaClauseLitsCore k3 cref.toNat, l < 2 * s2.core.cur_vars :=
    fun l hl => hcv2 ▸ hw.arena.lits_lt cref.toNat hcref hng l (hlits_sub l hl).2
  have hnodup' : ((fullArenaClauseLitsCore k3 cref.toNat).map (· / 2)).Nodup := by
    rw [hlits_map, List.map_map]; exact pw_lt_map_nodup _ old_sz hinj_old origMap hpw hlt_map
  have hent' : (cnfOfClauses F_cur).EntailsClause
      (cnfClause (fullArenaClauseLitsCore k3 cref.toNat)) := by
    refine entails_of_mem_or_false hent_f fun l hl => Or.inl ?_
    simp only [List.mem_filter, decide_eq_true_eq] at hl; obtain ⟨hl_mem, hne_u, hcond⟩ := hl
    rw [hlits_rw, List.mem_map] at hl_mem; obtain ⟨p, hp_r, rfl⟩ := hl_mem
    have hp_lt := List.mem_range.mp hp_r
    have hp_in : p ∈ origMap := by
      rcases Nat.lt_trichotomy p 1 with hp0 | rfl | hp2
      · have hpz : p = 0 := by omega
        subst hpz; rcases h01 with ⟨_, _, h0, _⟩ | ⟨_, hu3, _, _⟩
        · exact h0
        · exact absurd (congrArg BitVec.toNat hu3) hne_u
      · rcases h01 with ⟨_, hu4, _, _⟩ | ⟨_, _, h1, _⟩
        · exact absurd (congrArg BitVec.toNat hu4) hne_u
        · exact h1
      · refine hcov p (by omega) hp_lt ?_; rcases hcond with hpos | hl3 | hl4
        · exact hpos
        · have := hinj_old p 0 hp_lt (by omega) (by rw [hl3]); omega
        · have := hinj_old p 1 hp_lt (by omega) (by rw [hl4]); omega
    rw [hlits_map, List.mem_map]; exact ⟨p, hp_in, rfl⟩
  have hna := otfs_nonactive_on_trail hw2 hlen2.core_ok hiu_cut (hte2 ▸ hiu_te)
    (htrl2 ▸ ht_u) (hrsns2 ▸ hr_u) (hlvl2 ▸ hcl2 ▸ hlev_u) hcref2
  obtain ⟨hw3, hrefs3, hsz_3, hng_3, hother3⟩ := fa_inPlaceShrink_preserves_fullWitnessCut
    hw2 hlen2.core_ok (Nat.le_of_lt hiu_cut) hcref2 hng2 hnsz3 hnsz_s2 har3_len hhdr3 hsz3
    (fun j hj1 hj2 => hpad_ne j hj1 (by simpa [hsz2] using hj2))
    (by simpa [hsz2] using hlast_sent) (by simpa [hsz2] using hlast_keep)
    (fun i hi => hout i (by simpa [hsz2] using hi)) hlits_lt' hent'
    (fun idx hi hc => hna idx hi (hc.elim (fun h => Or.inl (Nat.lt_min.mpr
      ⟨Nat.lt_trans h hiu_cut, h⟩)) Or.inr))
  have hnd3 : FullArenaVarsNodup s3 := fun r hr hngr => by
    change r ∈ fullArenaClauseRefsCore s3.core at hr; rw [hrefs3] at hr
    by_cases hrc : r = cref.toNat
    · subst r; exact hnodup'
    · have ho := hother3 r hr hrc; change ((fullArenaClauseLitsCore s3.core r).map (· / 2)).Nodup
      rw [ho.2.2]; exact hnd2 r hr (by
        change fullArenaClauseGarbCore s2.core r = false; rw [← ho.2.1]; exact hngr)
  have hcref3 : cref.toNat ∈ fullArenaClauseRefsCore s3.core := by rw [hrefs3]; exact hcref2
  have har3_l0 : ar3[cref.toNat + 3]? = some l0 := by
    rw [hmap_eq 0 (by omega)]; rcases origMap with _ | ⟨a, tl⟩ <;> simp at hlen_map
    · omega
    · simp only [List.pairwise_cons] at hpw
      rcases h01 with ⟨rfl, _, h0in, _⟩ | ⟨rfl, _, h1in, h0no⟩
      · have ha : a = 0 := (List.mem_cons.mp h0in).elim Eq.symm fun h =>
          absurd (hpw.1 0 h) (Nat.not_lt_zero _)
        simp [ha, List.getElem?_eq_getElem (by omega : cref.toNat + 3 < s.core.arena.length)]
      · have ha : a = 1 := (List.mem_cons.mp h1in).elim Eq.symm fun h => by
          have := hpw.1 1 h; have : a ≠ 0 := fun hz => h0no (hz ▸ List.mem_cons_self); omega
        simp [ha, List.getElem?_eq_getElem (by omega : cref.toNat + 4 < s.core.arena.length)]
  have hm4 : (ar3[cref.toNat + 4]?.getD 0#32).toNat ∈
      fullArenaClauseLitsCore s3.core cref.toNat := by
    simp only [fullArenaClauseLitsCore, List.mem_map]; dsimp only [s3]
    refine ⟨ar3[cref.toNat + 4]'(by rw [har3_len]; omega), List.mem_iff_getElem.mpr ⟨1,
      by simp [show fullArenaClauseSizeCore { s2.core with arena := ar3 } cref.toNat = nsz from
        hsz_3, har3_len]; omega, by simp [List.getElem_take, List.getElem_drop]⟩,
      by rw [List.getElem?_eq_getElem (by rw [har3_len]; omega), Option.getD_some]⟩
  exact ⟨⟨{ hlen2.core_ok with arena_len_arr := har3_len }, hlen2.scratch_ok⟩, hw3, hnd3,
    hrefs3, hcref3, hsz_3, hng_3, har3_l0, hlits_sub, hcv2 ▸ hw3.arena.lits_lt _ hcref3 hng_3 _ hm4⟩

/-! ## 3. Shrink Invariants, Step-13 Header & Loop-Step Helpers -/

@[expose] def S13OtfsShrinkInv (c : FullCfg) (s : FullState) (ar1 : List (BitVec 32))
    (cref l0 uip : BitVec 32) (old_sz r i_nat nsz : Nat)
    (ar_cur : List (BitVec 32)) (origMap : List Nat) : Prop :=
  ar_cur.length = c.arena_cap ∧ r = old_sz - i_nat ∧ 2 ≤ i_nat ∧ i_nat ≤ old_sz ∧
  1 ≤ nsz ∧ nsz = 1 + otfsActCnt s.core cref.toNat i_nat ∧
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

@[expose] def S13OtfsHdrPost (c : FullCfg) (s s2 : FullState) (R : Mem 64 → Prop)
    (cref : BitVec 32) (old_sz nsz : Nat) (origMap : List Nat) (ml3 : Mem 64) : Prop :=
  ∃ (ar3 fl3 : List (BitVec 32)),
    (FullMem c { s2 with core := { s2.core with arena := ar3, flags := fl3 } } ⋆ R) ml3 ∧
    ar3.length = c.arena_cap ∧ fl3.length = c.max_vars ∧
    (let hdr0 := fullArenaHdrCore s2.core cref.toNat
     let sh0 := (hdr0 &&& 0x00800000#32) = 0#32
     let hdr_gl :=
       if (hdr0 &&& 0x00400000#32) ≠ 0#32 ∧ nsz ≤ (hdr0 &&& 0x7FFFF#32).toNat then
         (hdr0 &&& ~~~0x7FFFF#32) ||| (BitVec.ofNat 32 nsz - 1#32)
       else hdr0
     ar3[cref.toNat]? = some (if sh0 then hdr_gl ||| 0x00800000#32 else hdr_gl) ∧
     ar3[cref.toNat + 2]? = some (BitVec.ofNat 32 nsz) ∧
     (∀ k, k < nsz →
       ar3[cref.toNat + 3 + k]? = s.core.arena[cref.toNat + 3 + origMap[k]?.getD 0]?) ∧
     (∀ j, nsz ≤ j → j < old_sz - 1 →
       ar3[cref.toNat + 3 + j]? = s2.core.arena[cref.toNat + 3 + j]?) ∧
     ((hdr0 &&& 0x00800000#32) = 0#32 →
       ar3[cref.toNat + 3 + old_sz - 1]? = some 0xFFFFFFFF#32) ∧
     ((hdr0 &&& 0x00800000#32) ≠ 0#32 →
       ar3[cref.toNat + 3 + old_sz - 1]? = s2.core.arena[cref.toNat + 3 + old_sz - 1]?) ∧
     (∀ i, i < cref.toNat ∨ cref.toNat + 3 + old_sz ≤ i → ar3[i]? = s2.core.arena[i]?))

theorem s13_anaWitnessCut_with_flags {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {k : FullCoreState} (hw : FullWitnessCutInv c F0 F_cur cut k)
    (fl' : List (BitVec 32)) :
    FullWitnessCutInv c F0 F_cur cut { k with flags := fl' } :=
  ⟨{ hw.toFullOtfsWitnessInv with
      arena := { hw.arena with len_ok := hw.arena.len_ok }
      watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) },
    hw.cut_le, hw.reason_inv_cut, hw.reason_lit_mem_cut⟩

theorem s13_otfs_shrink_loop_step {c : FullCfg} {s : FullState} {ar1 ar_cur : List (BitVec 32)}
    {cref l0 uip : BitVec 32} {old_sz i_nat nsz : Nat} {origMap : List Nat}
    (har_len : s.core.arena.length = c.arena_cap) (hinv : S13OtfsShrinkInv c s ar1 cref l0 uip
      old_sz (old_sz - i_nat) i_nat nsz ar_cur origMap)
    (hilt : i_nat < old_sz) (h3o : cref.toNat + 3 + old_sz ≤ c.arena_cap)
    (hlv : 0 < (s.core.lvl[(s.core.arena[cref.toNat + 3 + i_nat]?.getD
      0#32).toNat / 2]?.getD 0#32).toNat) :
    let ot := s.core.arena[cref.toNat + 3 + i_nat]'(by omega)
    let ar' := ar_cur.set (cref.toNat + 3 + nsz) ot
    S13OtfsShrinkInv c s ar1 cref l0 uip old_sz (old_sz - (i_nat + 1)) (i_nat + 1) (nsz + 1)
      ar' (origMap ++ [i_nat]) := by
  intro ot ar'
  obtain ⟨har_c, _, hi2, _, hns1, hact, hlm, hpw, hlt_m, h01, hcov, hmapeq, hout⟩ := hinv
  have hnsz_lt_i : nsz < i_nat := by have := otfsActCnt_le s.core cref.toNat i_nat; omega
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
    by rw [hact, otfsActCnt_succ hi2, ite_eq_left hlv, Nat.add_assoc], by simp [hlm], hpw',
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

theorem s13_otfs_large_fin {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut idx_u : Nat} {s s' : FullState} {cref uip : BitVec 32}
    (hlen : s.LengthsOk c) (hw : FullWitnessCutInv c F0 F_cur cut s.core)
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
  have hrs := hw.reason_inv_cut idx_u hiu_cut
  dsimp only at hrs; rw [ht_u, hr_u] at hrs; have hrs' := hrs (bv32_lit_neq_ff hcr_lt)
  rw [ite_eq_right (fun h => h (bv32_lit_lo31_props (by omega : cref.toNat < 2 ^ 31)).2.2)] at hrs'
  intro l hl; obtain ⟨hne_u, hl_old⟩ := hsub l hl
  have hl_lt : l < 2 * s.core.cur_vars := hw.arena.lits_lt cref.toNat hcref hng l hl_old
  rcases hrs'.2.2 l hl_old with rfl | ⟨m, hm, hmeq, _⟩
  · exact absurd rfl hne_u
  · rw [hvals', hlvl', htrl', hcl']
    exact ⟨hne_u, hl_old, (hw.vals_false_iff l hl_lt).mpr ⟨m, by omega, hmeq⟩,
      fun _ => ⟨m, hm, hmeq⟩⟩

private theorem s13_glue_tighten_bits (hdr0 : BitVec 32) (nsz : Nat) (h3 : 3 ≤ nsz)
    (hle : nsz ≤ (hdr0 &&& 0x7FFFF#32).toNat) :
    let g := (hdr0 &&& ~~~0x7FFFF#32) ||| (BitVec.ofNat 32 nsz - 1#32)
    (g &&& 0x00080000#32) = (hdr0 &&& 0x00080000#32) ∧
    (g &&& 0x00800000#32) = (hdr0 &&& 0x00800000#32) := by
  have h19 : (hdr0 &&& 0x7FFFF#32).toNat < 2 ^ 19 := by
    rw [BitVec.toNat_and]; exact Nat.and_lt_two_pow _ (by decide)
  have hnsz19 : nsz < 2 ^ 19 := Nat.lt_of_le_of_lt hle h19
  have hsub_lt : (BitVec.ofNat 32 nsz - 1#32).toNat < 2 ^ 19 := by
    have h1 : (1#32 : BitVec 32).toNat = 1 := rfl
    have hn : (BitVec.ofNat 32 nsz).toNat = nsz := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hn, h1]; omega), hn, h1]; omega
  have h08 : (BitVec.ofNat 32 nsz - 1#32)[19] = false := by
    rw [BitVec.getElem_eq_testBit_toNat, Nat.testBit_lt_two_pow hsub_lt]
  have h23 : (BitVec.ofNat 32 nsz - 1#32)[23] = false := by
    rw [BitVec.getElem_eq_testBit_toNat, Nat.testBit_lt_two_pow (lt_trans hsub_lt (by decide))]
  constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not,
      BitVec.getLsbD_ofNat, decide_eq_true hi, Bool.true_and]
  · by_cases hi19 : i = 19
    · subst hi19
      simp [h08, show Nat.testBit 524287 19 = false from rfl,
        show Nat.testBit 524288 19 = true from rfl]
    · have h0 : Nat.testBit 0x00080000 i = false := by
        rw [show (0x00080000 : Nat) = 2 ^ 19 from rfl, Nat.testBit_two_pow]
        exact decide_eq_false (Ne.symm hi19)
      simp [h0]
  · by_cases hi23 : i = 23
    · subst hi23
      simp [h23, show Nat.testBit 524287 23 = false from rfl,
        show Nat.testBit 8388608 23 = true from rfl]
    · have h0 : Nat.testBit 0x00800000 i = false := by
        rw [show (0x00800000 : Nat) = 2 ^ 23 from rfl, Nat.testBit_two_pow]
        exact decide_eq_false (Ne.symm hi23)
      simp [h0]

theorem s13_otfs_hdr_ok {c : FullCfg} {s s2 : FullState}
    {ar1 ar_cur ar3_in fl3 : List (BitVec 32)} {cref : BitVec 32} {old_sz nsz : Nat}
    {origMap : List Nat} {R : Mem 64 → Prop} {ml3 : Mem 64} (sh0 : Bool)
    (_har_len : s.core.arena.length = c.arena_cap) (har_c : ar_cur.length = c.arena_cap)
    (h3o : cref.toNat + 3 + old_sz ≤ c.arena_cap) (h4 : 4 ≤ old_sz)
    (hnsz3 : 3 ≤ nsz) (hnsz_lt : nsz < old_sz)
    (_hlits_info : ∀ j < old_sz,
      (s.core.arena[cref.toNat + 3 + j]?.getD 0#32).toNat < 2 * s.core.cur_vars ∧
      s.core.arena[cref.toNat + 3 + j]?.getD 0#32 ≠ 0xFFFFFFFF#32)
    (hmapeq : ∀ k, k < nsz →
      ar_cur[cref.toNat + 3 + k]? = s.core.arena[cref.toNat + 3 + origMap[k]?.getD 0]?)
    (hout_m : ∀ q, q < cref.toNat + 4 ∨ cref.toNat + 3 + nsz ≤ q → ar_cur[q]? = ar1[q]?)
    (_har1_q : ∀ q, 2 ≤ q → ar1[cref.toNat + 3 + q]? = s.core.arena[cref.toNat + 3 + q]?)
    (har1_s2 : ∀ i, i < cref.toNat + 3 ∨ cref.toNat + 5 ≤ i → ar1[i]? = s2.core.arena[i]?)
    (hhdr_eq : ar_cur[cref.toNat]? = some (fullArenaHdrCore s2.core cref.toNat))
    (hfl3 : fl3.length = c.max_vars)
    (hsh :
      let hdr0 := fullArenaHdrCore s2.core cref.toNat
      let hdr_gl :=
        if (hdr0 &&& 0x00400000#32) ≠ 0#32 ∧ nsz ≤ (hdr0 &&& 0x7FFFF#32).toNat then
          (hdr0 &&& ~~~0x7FFFF#32) ||| (BitVec.ofNat 32 nsz - 1#32)
        else hdr0
      (sh0 = true ∧ (hdr_gl &&& 0x00800000#32) = 0#32) ∨
      (sh0 = false ∧ (hdr_gl &&& 0x00800000#32) ≠ 0#32))
    (hm :
      (FullMem c { s2 with core := { s2.core with arena := ar3_in, flags := fl3 } } ⋆ R) ml3)
    (har3_def :
      let hdr0 := fullArenaHdrCore s2.core cref.toNat
      let hdr_gl :=
        if (hdr0 &&& 0x00400000#32) ≠ 0#32 ∧ nsz ≤ (hdr0 &&& 0x7FFFF#32).toNat then
          (hdr0 &&& ~~~0x7FFFF#32) ||| (BitVec.ofNat 32 nsz - 1#32)
        else hdr0
      ar3_in =
        let ar_a := (ar_cur.set (cref.toNat + 2) (BitVec.ofNat 32 nsz)).set (cref.toNat + 1) 2#32
        let ar_b :=
          if (hdr0 &&& 0x00400000#32) ≠ 0#32 ∧ nsz ≤ (hdr0 &&& 0x7FFFF#32).toNat then
            ar_a.set cref.toNat hdr_gl
          else ar_a
        if sh0 then ar_b.set cref.toNat (hdr_gl ||| 0x00800000#32) |>.set
          (cref.toNat + 3 + old_sz - 1) 0xFFFFFFFF#32
        else ar_b) :
    S13OtfsHdrPost c s s2 R cref old_sz nsz origMap ml3 := by
  let hdr0 := fullArenaHdrCore s2.core cref.toNat
  let hdr_gl :=
    if (hdr0 &&& 0x00400000#32) ≠ 0#32 ∧ nsz ≤ (hdr0 &&& 0x7FFFF#32).toNat then
      (hdr0 &&& ~~~0x7FFFF#32) ||| (BitVec.ofNat 32 nsz - 1#32)
    else hdr0
  have hgl_shrk : (hdr_gl &&& 0x00800000#32) = (hdr0 &&& 0x00800000#32) := by
    dsimp only [hdr_gl]; split
    · next h => exact (s13_glue_tighten_bits hdr0 nsz hnsz3 h.2).2
    · rfl
  have hkeep_s2 : ∀ j, nsz ≤ j → j < old_sz →
      ar_cur[cref.toNat + 3 + j]? = s2.core.arena[cref.toNat + 3 + j]? := fun j hj1 _ => by
    rw [hout_m _ (Or.inr (by omega)), har1_s2 _ (Or.inr (by omega))]
  have har_a_eq : ∀ (x : List (BitVec 32)), x = (ar_cur.set (cref.toNat + 2)
      (BitVec.ofNat 32 nsz)).set (cref.toNat + 1) 2#32 → x.length = c.arena_cap := fun x hx => by
    subst hx; simp [har_c]
  let ar_a := (ar_cur.set (cref.toNat + 2) (BitVec.ofNat 32 nsz)).set (cref.toNat + 1) 2#32
  have har_al : ar_a.length = c.arena_cap := har_a_eq ar_a rfl
  let ar_b := if (hdr0 &&& 0x00400000#32) ≠ 0#32 ∧ nsz ≤ (hdr0 &&& 0x7FFFF#32).toNat then
    ar_a.set cref.toNat hdr_gl else ar_a
  have har_bl : ar_b.length = c.arena_cap := by
    dsimp only [ar_b]; split <;> simp [har_al]
  have har_b_cref : ar_b[cref.toNat]? = some hdr_gl := by
    dsimp only [ar_b]; split
    · next hc => rw [List.getElem?_set_self (by rw [har_al]; omega)]
    · next hc =>
      have : hdr_gl = hdr0 := ite_eq_right (fun h => absurd h hc)
      rw [this]; dsimp only [ar_a]
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]; exact hhdr_eq
  have har_b_ne : ∀ j, j ≠ cref.toNat → ar_b[j]? = ar_a[j]? := fun j hj => by
    dsimp only [ar_b]; split
    · rw [List.getElem?_set_ne (Ne.symm hj)]
    · rfl
  subst har3_def
  cases sh0 <;> rcases hsh with ⟨hb, hshv⟩ | ⟨hb, hshv⟩ <;> try exact absurd hb (by decide)
  · have hshv0 : (hdr0 &&& 0x00800000#32) ≠ 0#32 := by rwa [← hgl_shrk]
    refine ⟨ar_b, fl3, hm, har_bl, hfl3, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [ite_eq_right hshv0]; exact har_b_cref
    · rw [har_b_ne (cref.toNat + 2) (by omega)]; dsimp only [ar_a]
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by rw [har_c]; omega)]
    · intro k hk; rw [har_b_ne (cref.toNat + 3 + k) (by omega)]; dsimp only [ar_a]
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]; exact hmapeq k hk
    · intro j hj1 hj2; rw [har_b_ne (cref.toNat + 3 + j) (by omega)]; dsimp only [ar_a]
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
      exact hkeep_s2 j hj1 (by omega)
    · intro h0; exact absurd h0 hshv0
    · intro _; rw [har_b_ne (cref.toNat + 3 + old_sz - 1) (by omega)]; dsimp only [ar_a]
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        show cref.toNat + 3 + old_sz - 1 = cref.toNat + 3 + (old_sz - 1) by omega]
      exact hkeep_s2 (old_sz - 1) (by omega) (by omega)
    · intro i hi
      by_cases hic : i = cref.toNat
      · exfalso; rcases hi with h | h <;> omega
      · rw [har_b_ne i hic]; dsimp only [ar_a]
        rw [List.getElem?_set_ne (by rcases hi with h | h <;> omega),
          List.getElem?_set_ne (by rcases hi with h | h <;> omega),
          hout_m i (hi.imp (fun h => by omega) (fun h => by omega))]
        exact har1_s2 i (hi.imp (fun h => by omega) (fun h => by omega))
  · have hshv0 : (hdr0 &&& 0x00800000#32) = 0#32 := by rwa [← hgl_shrk]
    let ar_c := ar_b.set cref.toNat (hdr_gl ||| 0x00800000#32)
    let ar3 := ar_c.set (cref.toNat + 3 + old_sz - 1) 0xFFFFFFFF#32
    have har_cl : ar_c.length = c.arena_cap := by simp [ar_c, har_bl]
    refine ⟨ar3, fl3, hm, by simp [ar3, har_cl], hfl3, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [ite_eq_left hshv0]; dsimp only [ar3, ar_c]
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by rw [har_bl]; omega)]
    · dsimp only [ar3, ar_c]; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        har_b_ne (cref.toNat + 2) (by omega)]
      dsimp only [ar_a]; rw [List.getElem?_set_ne (by omega),
        List.getElem?_set_self (by rw [har_c]; omega)]
    · intro k hk; dsimp only [ar3, ar_c]
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        har_b_ne (cref.toNat + 3 + k) (by omega)]
      dsimp only [ar_a]; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
      exact hmapeq k hk
    · intro j hj1 hj2; dsimp only [ar3, ar_c]
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        har_b_ne (cref.toNat + 3 + j) (by omega)]
      dsimp only [ar_a]; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
      exact hkeep_s2 j hj1 (by omega)
    · intro _; dsimp only [ar3]; rw [List.getElem?_set_self (by rw [har_cl]; omega)]
    · intro hn; exact absurd hshv0 hn
    · intro i hi; dsimp only [ar3, ar_c]
      rw [List.getElem?_set_ne (by rcases hi with h | h <;> omega),
        List.getElem?_set_ne (by rcases hi with h | h <;> omega),
        har_b_ne i (by rcases hi with h | h <;> omega)]
      dsimp only [ar_a]; rw [List.getElem?_set_ne (by rcases hi with h | h <;> omega),
        List.getElem?_set_ne (by rcases hi with h | h <;> omega),
        hout_m i (hi.imp (fun h => by omega) (fun h => by omega))]
      exact har1_s2 i (hi.imp (fun h => by omega) (fun h => by omega))

theorem s13_otfs_shrink_ok_of_hdrPost {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut idx_u old_sz nsz : Nat} {s s2 : FullState} {cref l0 uip : BitVec 32}
    {origMap : List Nat} {R : Mem 64 → Prop} {ml3 : Mem 64}
    (hlen : s.LengthsOk c) (hw : FullWitnessCutInv c F0 F_cur cut s.core)
    (hnd : FullArenaVarsNodup s) (hlen2 : s2.LengthsOk c)
    (hw2 : FullWitnessCutInv c F0 F_cur cut s2.core)
    (hnd2 : FullArenaVarsNodup s2)
    (hcv2 : s2.core.cur_vars = s.core.cur_vars) (htrl2 : s2.core.trl = s.core.trl)
    (hrsns2 : s2.core.rsns = s.core.rsns) (hlvl2 : s2.core.lvl = s.core.lvl)
    (hte2 : s2.core.trail_end = s.core.trail_end) (hcl2 : s2.core.cur_level = s.core.cur_level)
    (hcref : cref.toNat ∈ fullArenaClauseRefs s) (hng : fullArenaClauseGarb s cref.toNat = false)
    (hcref2 : cref.toNat ∈ fullArenaClauseRefs s2)
    (hng2 : fullArenaClauseGarb s2 cref.toNat = false)
    (hsz_orig : fullArenaClauseSize s cref.toNat = old_sz)
    (hsz2 : fullArenaClauseSize s2 cref.toNat = old_sz)
    (hiu_cut : idx_u < cut) (hiu_te : idx_u < s.core.trail_end)
    (ht_u : (s.core.trl[idx_u]?.getD 0#32).toNat = uip.toNat)
    (hr_u : s.core.rsns[uip.toNat / 2]?.getD 0xFFFFFFFF#32 = cref)
    (hlev_u : (s.core.lvl[uip.toNat / 2]?.getD 0#32).toNat = s.core.cur_level)
    (hent_f : (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((fullArenaClauseLits s cref.toNat).filter fun l =>
        decide (l ≠ uip.toNat ∧ (0 < (s.core.lvl[l / 2]?.getD 0#32).toNat ∨
          l = (s.core.arena[cref.toNat + 3]?.getD 0#32).toNat ∨
          l = (s.core.arena[cref.toNat + 4]?.getD 0#32).toNat)))))
    (h3o : cref.toNat + 3 + old_sz ≤ c.arena_cap)
    (hnsz3 : 3 ≤ nsz) (hnsz_lt : nsz < old_sz)
    (hlen_map : origMap.length = nsz) (hpw : origMap.Pairwise (· < ·))
    (hlt_map : ∀ p ∈ origMap, p < old_sz)
    (h01 : (l0 = s.core.arena[cref.toNat + 3]?.getD 0#32 ∧
        s.core.arena[cref.toNat + 4]?.getD 0#32 = uip ∧ 0 ∈ origMap ∧ 1 ∉ origMap) ∨
      (l0 = s.core.arena[cref.toNat + 4]?.getD 0#32 ∧
        s.core.arena[cref.toNat + 3]?.getD 0#32 = uip ∧ 1 ∈ origMap ∧ 0 ∉ origMap))
    (hcov : ∀ p, 2 ≤ p → p < old_sz →
      0 < (s.core.lvl[(s.core.arena[cref.toNat + 3 + p]?.getD 0#32).toNat / 2]?.getD 0#32).toNat →
      p ∈ origMap)
    (hpost : S13OtfsHdrPost c s s2 R cref old_sz nsz origMap ml3) :
    ∃ (s3 : FullState),
      s3.core.arena.length = c.arena_cap ∧ s3.core.flags.length = c.max_vars ∧
      (∃ ar3 fl3, s3 = { s2 with core := { s2.core with arena := ar3, flags := fl3 } }) ∧
      (FullMem c s3 ⋆ R) ml3 ∧
      s3.LengthsOk c ∧ FullWitnessCutInv c F0 F_cur idx_u s3.core ∧
      FullArenaVarsNodup s3 ∧
      fullArenaClauseRefsCore s3.core = fullArenaClauseRefsCore s2.core ∧
      cref.toNat ∈ fullArenaClauseRefsCore s3.core ∧
      fullArenaClauseSizeCore s3.core cref.toNat = nsz ∧
      fullArenaClauseGarbCore s3.core cref.toNat = false ∧
      s3.core.arena[cref.toNat + 3]? = some l0 ∧
      (∀ l ∈ fullArenaClauseLits s3 cref.toNat,
        l ≠ uip.toNat ∧ l ∈ fullArenaClauseLits s cref.toNat) := by
  obtain ⟨ar3, fl3, hm3, har3_l, hfl3, hhdr3, hsz3, hmap3, hpad3, hsent3, hkeep3, hout3⟩ :=
    hpost
  let hdr0 := fullArenaHdrCore s2.core cref.toNat
  let sh0 := (hdr0 &&& 0x00800000#32) = 0#32
  let hdr_can := if sh0 then hdr0 ||| 0x00800000#32 else hdr0
  let hdr_gl :=
    if (hdr0 &&& 0x00400000#32) ≠ 0#32 ∧ nsz ≤ (hdr0 &&& 0x7FFFF#32).toNat then
      (hdr0 &&& ~~~0x7FFFF#32) ||| (BitVec.ofNat 32 nsz - 1#32)
    else hdr0
  let hdr_fin := if sh0 then hdr_gl ||| 0x00800000#32 else hdr_gl
  let ar3_can := ar3.set cref.toNat hdr_can
  have hcr_lt_ar3 : cref.toNat < ar3.length := by rw [har3_l]; omega
  have hcan_ne : ∀ j, j ≠ cref.toNat → ar3_can[j]? = ar3[j]? := fun j hj =>
    List.getElem?_set_ne (Ne.symm hj)
  obtain ⟨hlen_c, hw_c, hnd_c, hrefs_c, hcref_c, hsz_c, hng_c, harc_l0, hlits_c, _⟩ :=
    otfs_large_shrink_ok hlen hw hnd hlen2 hw2 hnd2
      hcv2 htrl2 hrsns2 hlvl2 hte2 hcl2 hcref hng hcref2 hng2 (hsz2.trans hsz_orig.symm)
      hiu_cut hiu_te ht_u hr_u hlev_u hent_f
      hnsz3 (hsz_orig.symm ▸ hnsz_lt) hlen_map hpw (fun p hp => hsz_orig.symm ▸ hlt_map p hp) h01
      (fun p hp2 hplt hpos => hcov p hp2 (hsz_orig ▸ hplt) hpos)
      (fun k hk => by rw [hcan_ne (cref.toNat + 3 + k) (by omega)]; exact hmap3 k hk)
      (by simp [ar3_can, har3_l])
      (by dsimp only [ar3_can]; rw [List.getElem?_set_self hcr_lt_ar3])
      (by rw [hcan_ne (cref.toNat + 2) (by omega)]; exact hsz3)
      (fun j hj1 hj2 => by
        rw [hcan_ne (cref.toNat + 3 + j) (by omega)]
        exact hpad3 j hj1 (hsz_orig ▸ hj2))
      (fun h => by
        rw [hsz_orig, hcan_ne (cref.toNat + 3 + old_sz - 1) (by omega)]
        exact hsent3 h)
      (fun h => by
        rw [hsz_orig, hcan_ne (cref.toNat + 3 + old_sz - 1) (by omega)]
        exact hkeep3 h)
      (fun i hi => by
        rw [hsz_orig] at hi
        rw [hcan_ne i (by rcases hi with h | h <;> omega)]; exact hout3 i hi)
  have har3_eq_set : ar3 = ar3_can.set cref.toNat hdr_fin := by
    dsimp only [ar3_can]
    rw [List.set_set, show hdr_fin = ar3[cref.toNat] from
      (Option.some.inj (by rw [← List.getElem?_eq_getElem hcr_lt_ar3]; exact hhdr3)).symm]
    exact (List.set_getElem_self hcr_lt_ar3).symm
  have hand_or : ∀ (a b c m : BitVec 32), (a &&& m) = (b &&& m) →
      ((a ||| c) &&& m) = ((b ||| c) &&& m) := fun a b c m h => by
    ext i hi; have hi' := congrArg (·[i]) h
    simp only [BitVec.getElem_and, BitVec.getElem_or] at hi' ⊢
    cases hm : m[i]
    · simp
    · simp only [hm, Bool.and_true] at hi' ⊢; rw [hi']
  have hgarb_eq : (hdr_fin &&& 0x00080000#32) = (fullArenaHdrCore { s2.core with arena := ar3_can }
      cref.toNat &&& 0x00080000#32) := by
    have harc_hdr : fullArenaHdrCore { s2.core with arena := ar3_can } cref.toNat = hdr_can := by
      unfold fullArenaHdrCore; dsimp only [ar3_can]
      rw [List.getElem?_set_self hcr_lt_ar3, Option.getD_some]
    rw [harc_hdr]; dsimp only [hdr_fin, hdr_can, hdr_gl]
    by_cases hsh0 : sh0 <;> simp only [hsh0, ↓reduceIte] <;> split
    · next h =>
      exact hand_or _ _ 0x00800000#32 0x00080000#32 (s13_glue_tighten_bits hdr0 nsz hnsz3 h.2).1
    · rfl
    · next h => exact (s13_glue_tighten_bits hdr0 nsz hnsz3 h.2).1
    · rfl
  have hshrk_eq : (hdr_fin &&& 0x00800000#32) = (fullArenaHdrCore { s2.core with arena := ar3_can }
      cref.toNat &&& 0x00800000#32) := by
    have harc_hdr : fullArenaHdrCore { s2.core with arena := ar3_can } cref.toNat = hdr_can := by
      unfold fullArenaHdrCore; dsimp only [ar3_can]
      rw [List.getElem?_set_self hcr_lt_ar3, Option.getD_some]
    rw [harc_hdr]; dsimp only [hdr_fin, hdr_can, hdr_gl]
    by_cases hsh0 : sh0 <;> simp only [hsh0, ↓reduceIte] <;> split
    · next h =>
      exact hand_or _ _ 0x00800000#32 0x00800000#32 (s13_glue_tighten_bits hdr0 nsz hnsz3 h.2).2
    · rfl
    · next h => exact (s13_glue_tighten_bits hdr0 nsz hnsz3 h.2).2
    · rfl
  let k_can : FullCoreState := { s2.core with arena := ar3_can }
  obtain ⟨hw_gl, hrefs_gl, hprops_gl⟩ :=
    hdrBitsUpdate_preserves_fullWitnessCut hlen_c.core_ok hw_c hcref_c (fun _ => hdr_fin)
      k_can.arena_garbage k_can.num_irred k_can.num_redundant hgarb_eq hshrk_eq
  dsimp only [k_can] at hw_gl hrefs_gl hprops_gl
  rw [← har3_eq_set] at hw_gl hrefs_gl hprops_gl
  let s3 : FullState := { s2 with core := { s2.core with arena := ar3, flags := fl3 } }
  have hs3_len : s3.LengthsOk c :=
    ⟨{ hlen2.core_ok with arena_len_arr := har3_l, flags_len := hfl3 }, hlen2.scratch_ok⟩
  have hw3 : FullWitnessCutInv c F0 F_cur idx_u s3.core :=
    s13_anaWitnessCut_with_flags hw_gl fl3
  have hnd3 : FullArenaVarsNodup s3 := fun r hr hngr => by
    change r ∈ fullArenaClauseRefsCore s3.core at hr
    have hrf : fullArenaClauseRefsCore s3.core = fullArenaClauseRefsCore k_can := by
      change fullArenaClauseRefsCore { s2.core with arena := ar3, flags := fl3 } = _
      simpa [fullArenaClauseRefsCore] using hrefs_gl
    rw [hrf] at hr
    have hpr := hprops_gl r hr
    have hgr_can : fullArenaClauseGarb { s2 with core := k_can } r = false := by
      change fullArenaClauseGarbCore k_can r = false
      rw [← hpr.2.1]; simpa [fullArenaClauseGarbCore, fullArenaHdrCore, s3] using hngr
    change ((fullArenaClauseLitsCore s3.core r).map (· / 2)).Nodup
    have hl_eq : fullArenaClauseLitsCore s3.core r = fullArenaClauseLitsCore k_can r := by
      simpa [fullArenaClauseLitsCore, fullArenaClauseSizeCore, s3] using hpr.2.2
    rw [hl_eq]; exact hnd_c r hr hgr_can
  have hcref_gl := hprops_gl cref.toNat hcref_c
  refine ⟨s3, har3_l, hfl3, ⟨ar3, fl3, rfl⟩, hm3, hs3_len, hw3, hnd3,
    by simpa [fullArenaClauseRefsCore, s3] using hrefs_gl.trans hrefs_c,
    by change cref.toNat ∈ fullArenaClauseRefsCore { s2.core with arena := ar3, flags := fl3 }
       rw [show fullArenaClauseRefsCore { s2.core with arena := ar3, flags := fl3 } =
         fullArenaClauseRefsCore { s2.core with arena := ar3 } from rfl, hrefs_gl]
       exact hcref_c,
    by simpa [fullArenaClauseSizeCore, s3] using hcref_gl.1.trans hsz_c,
    by simpa [fullArenaClauseGarbCore, fullArenaHdrCore, s3] using hcref_gl.2.1.trans hng_c,
    by change ar3[cref.toNat + 3]? = some l0
       rw [← hcan_ne (cref.toNat + 3) (by omega)]; exact harc_l0,
    fun l hl => by
      change l ∈ fullArenaClauseLitsCore { s2.core with arena := ar3, flags := fl3 } cref.toNat
        at hl
      rw [show fullArenaClauseLitsCore { s2.core with arena := ar3, flags := fl3 } cref.toNat =
        fullArenaClauseLitsCore { s2.core with arena := ar3 } cref.toNat from rfl,
        hcref_gl.2.2] at hl
      exact hlits_c l hl⟩

theorem s13_otfs_ar_idx3_lt_len {ar : List (BitVec 32)} {cref : BitVec 32}
    {cap old_sz j : Nat} (hcap : cap < 2 ^ 31 - 1) (har : ar.length = cap)
    (hold : cref.toNat + 3 + old_sz ≤ cap) (hj : j < old_sz) :
    (cref.setWidth 64 + 3#64 + (BitVec.ofNat 32 j).setWidth 64).toNat = cref.toNat + 3 + j ∧
    (cref.setWidth 64 + 3#64 + (BitVec.ofNat 32 j).setWidth 64).toNat < ar.length := by
  have hz := otfs_bv_idx3_64 cref j (by omega) (by omega); exact ⟨hz, by rw [hz, har]; omega⟩

theorem s13_otfs_cr_end_z {ar0 : List (BitVec 32)} {cref : BitVec 32}
    {cap old_sz : Nat} (h3o : cref.toNat + 3 + old_sz ≤ cap) (h4_old : 4 ≤ old_sz)
    (hcap : cap < 2 ^ 31 - 1) (hcr2_z : (cref.setWidth 64 + 2#64).toNat = cref.toNat + 2)
    (hcr3_z : (cref.setWidth 64 + 3#64).toNat = cref.toNat + 3)
    (hcr2_bd : (cref.setWidth 64 + 2#64).toNat < ar0.length)
    (hsz32 : ar0[cref.toNat + 2]'(by rw [← hcr2_z]; exact hcr2_bd) = BitVec.ofNat 32 old_sz) :
    (cref.setWidth 64 + 3#64 +
      (ar0[(cref.setWidth 64 + 2#64).toNat]'hcr2_bd).setWidth 64 - 1#64).toNat =
      cref.toNat + 3 + old_sz - 1 := by
  have hsz_at : ar0[(cref.setWidth 64 + 2#64).toNat]'hcr2_bd = BitVec.ofNat 32 old_sz := by
    rw [getElem_eq_of_idx (hj := by rw [← hcr2_z]; exact hcr2_bd) hcr2_z]; exact hsz32
  have hz_s : ((BitVec.ofNat 32 old_sz).setWidth 64).toNat = old_sz := by
    rw [zext_toNat _ (by decide), bv32_ofNat_toNat (by omega)]
  have h1_64 : (1#64 : BitVec 64).toNat = 1 := rfl
  have hsum_z : (cref.setWidth 64 + 3#64 + (BitVec.ofNat 32 old_sz).setWidth 64).toNat =
      cref.toNat + 3 + old_sz := by rw [BitVec.toNat_add, hcr3_z, hz_s]; omega
  rw [hsz_at, BitVec.toNat_sub_of_le (by rw [BitVec.le_def, h1_64, hsum_z]; omega), h1_64, hsum_z]

theorem s13_otfs_loop2_init {c : FullCfg} {s : FullState}
    {cref l0 uip : BitVec 32} {old_sz : Nat}
    (har_len : s.core.arena.length = c.arena_cap)
    (h3o : cref.toNat + 3 + old_sz ≤ c.arena_cap) (h4_old : 4 ≤ old_sz)
    (hs01 : (l0 = s.core.arena[cref.toNat + 3]?.getD 0#32 ∧
        s.core.arena[cref.toNat + 4]?.getD 0#32 = uip) ∨
      (l0 = s.core.arena[cref.toNat + 4]?.getD 0#32 ∧
        s.core.arena[cref.toNat + 3]?.getD 0#32 = uip)) :
    let ar1 := (s.core.arena.set (cref.toNat + 3) l0).set (cref.toNat + 4) uip
    ∃ origMap, S13OtfsShrinkInv c s ar1 cref l0 uip old_sz (old_sz - 2) 2 1 ar1 origMap := by
  intro ar1
  have har1_len : ar1.length = c.arena_cap := by simp [ar1, List.length_set, har_len]
  have har1_0 : ar1[cref.toNat + 3]? = some l0 := by
    dsimp only [ar1]; rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega)]
  have hact0 : otfsActCnt s.core cref.toNat 2 = 0 := by
    simp [otfsActCnt, List.drop_eq_nil_of_le (show (List.range 2).length ≤ 2 by simp)]
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

theorem s13_otfs_p1_lv_pos {k : FullCoreState} {cref i_nat idx : Nat}
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
    (getElem_eq_of_idx (congrArg (·.toNat / 2) hot_eq)))

theorem s13_otfs_p1_lv_zero {k : FullCoreState} {cref i_nat idx : Nat}
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
      (getElem_eq_of_idx (congrArg (·.toNat / 2) hot_eq.symm))))

theorem s13_otfs_p1_brk {k : FullCoreState} {cref i_nat old_sz : Nat}
    (hi2 : 2 ≤ i_nat) (hilt : i_nat < old_sz)
    (hlv_pos : 0 < (k.lvl[(k.arena[cref + 3 + i_nat]?.getD 0#32).toNat / 2]?.getD 0#32).toNat)
    (hcnt_lt3 : 1 + otfsActCnt k cref i_nat < 3)
    (hge3 : (3#32 : BitVec 32).toNat ≤ (1 + otfsActCnt k cref i_nat + 1) % 2 ^ 32) :
    3 ≤ 1 + otfsActCnt k cref old_sz := by
  have hnext : 1 + otfsActCnt k cref (i_nat + 1) = 1 + otfsActCnt k cref i_nat + 1 := by
    rw [otfsActCnt_succ hi2, ite_eq_left hlv_pos]; omega
  have hmono := otfsActCnt_mono (k := k) (cref := cref) (i := i_nat + 1) (j := old_sz)
    (by omega) (by omega)
  simp only [BitVec.reduceToNat] at hge3; omega

theorem s13_otfs_p1_inc {k : FullCoreState} {cref i_nat : Nat} (hi2 : 2 ≤ i_nat)
    (hlv_pos : 0 < (k.lvl[(k.arena[cref + 3 + i_nat]?.getD 0#32).toNat / 2]?.getD 0#32).toNat)
    (hcnt_lt3 : 1 + otfsActCnt k cref i_nat < 3)
    (hlt : ¬ (3#32 : BitVec 32).toNat ≤ (1 + otfsActCnt k cref i_nat + 1) % 2 ^ 32) :
    BitVec.ofNat 32 (1 + otfsActCnt k cref i_nat) + 1 =
      BitVec.ofNat 32 (1 + otfsActCnt k cref (i_nat + 1)) ∧
    1 + otfsActCnt k cref (i_nat + 1) < 3 := by
  have hnext : 1 + otfsActCnt k cref (i_nat + 1) = 1 + otfsActCnt k cref i_nat + 1 := by
    rw [otfsActCnt_succ hi2, ite_eq_left hlv_pos]; omega
  simp only [BitVec.reduceToNat] at hlt
  refine ⟨BitVec.eq_of_toNat_eq ?_, by omega⟩
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    show (1 : BitVec 32).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), hnext]

theorem s13_otfs_p2_lv_pos {k k2 : FullCoreState} {ar_cur : List (BitVec 32)}
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
    (otfs_list_getElem_of_list_idx hlvl_eq (congrArg (·.toNat / 2) hot_c_eq)))

theorem s13_otfs_p2_skip_inv {c : FullCfg} {s s2 : FullState}
    {ar1 ar_cur : List (BitVec 32)} {cref l0 uip : BitVec 32} {old_sz i_nat nsz idx : Nat}
    {origMap : List Nat} {hc_idx_bd : idx < ar_cur.length}
    {h2_lvl_bd : (ar_cur[idx]'hc_idx_bd).toNat / 2 < s2.core.lvl.length}
    (hinv : S13OtfsShrinkInv c s ar1 cref l0 uip old_sz (old_sz - i_nat) i_nat nsz ar_cur origMap)
    (hilt : i_nat < old_sz) (har_bd : cref.toNat + 3 + i_nat < s.core.arena.length)
    (hv_bd : (s.core.arena[cref.toNat + 3 + i_nat]?.getD 0#32).toNat / 2 < s.core.lvl.length)
    (hlvl_eq : s2.core.lvl = s.core.lvl)
    (hot_c_eq : ar_cur[idx]'hc_idx_bd = s.core.arena[cref.toNat + 3 + i_nat]'har_bd)
    (hzero : ¬ (0#32 : BitVec 32).toNat <
      (s2.core.lvl[(ar_cur[idx]'hc_idx_bd).toNat / 2]'h2_lvl_bd).toNat) :
    S13OtfsShrinkInv c s ar1 cref l0 uip old_sz (old_sz - (i_nat + 1)) (i_nat + 1) nsz
      ar_cur origMap := by
  obtain ⟨har_c, _, hi2, hile, hns1, hact, hlm, hpw, hlt_m, h01, hcov, hmapeq, hout_m⟩ := hinv
  have hlv_0 : ¬ 0 < (s.core.lvl[(s.core.arena[cref.toNat + 3 + i_nat]?.getD 0#32).toNat / 2]?.getD
      0#32).toNat := fun hpos => by
    rw [List.getElem?_eq_getElem har_bd, Option.getD_some,
      List.getElem?_eq_getElem (by rw [List.getElem?_eq_getElem har_bd, Option.getD_some] at hv_bd
                                   exact hv_bd), Option.getD_some] at hpos
    exact hzero (Nat.lt_of_lt_of_eq hpos (congrArg BitVec.toNat
      (otfs_list_getElem_of_list_idx hlvl_eq.symm (congrArg (·.toNat / 2) hot_c_eq.symm))))
  exact ⟨har_c, rfl, by omega, by omega, hns1,
    by rw [hact, otfsActCnt_succ hi2, ite_eq_right hlv_0, Nat.add_zero],
    hlm, hpw, fun p hp => Nat.lt_succ_of_lt (hlt_m p hp), h01,
    fun p hp2 hplt hpos => by
      by_cases hpi : p = i_nat
      · subst p; exact absurd hpos hlv_0
      · exact hcov p hp2 (by omega) hpos, hmapeq, hout_m⟩

end LeanQbe.T.Examples.Kissat.Proof.Deduce
