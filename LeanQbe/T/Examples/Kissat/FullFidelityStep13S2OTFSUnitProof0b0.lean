/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S2OTFSUnitProof0a
public import LeanQbe.T.Examples.Kissat.FullM5OtfsLemmas1
public import LeanQbe.T.Examples.Kissat.FullAnalyzeLemmas5
public import LeanQbe.T.Examples.Kissat.FullAnalyzeLemmas1

/-!
# Kissat Fidelity Step 13 `full_otfs_large` Data & State Helpers (`0b0`)

Pure invariants, `FullMem`/arena/flags preservation, bounds helpers, and `S13OtfsHdrPost` ->
`FullWitnessCutInv` bridge (combining `otfs_large_shrink_ok` with
`hdrBitsUpdate_preserves_fullWitnessCut` for Step-13 `PH_RED` glue tightening and `!PH_RED`
`flags[..] |= 24u`). Zero `@[expose]` on theorems/lemmas.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S2

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0HeadStep LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM5Otfs
open LeanQbe.T.Examples.Kissat.Full.FullAnalyzeHelpers
open LeanQbe.T.Examples.Kissat.Full.FullAnalyzeTactics
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open Kraken.Bedrock2.Test

@[expose] def S13OtfsShrinkInv (c : FullCfg) (s : FullState) (ar1 : List (BitVec 32))
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
       ar3[cref.toNat + 3 + j]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32) ∧
     ((hdr0 &&& 0x00800000#32) = 0#32 →
       ar3[cref.toNat + 3 + old_sz - 1]? = some 0xFFFFFFFF#32) ∧
     ((hdr0 &&& 0x00800000#32) ≠ 0#32 →
       ar3[cref.toNat + 3 + old_sz - 1]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32) ∧
     (∀ i, i < cref.toNat ∨ cref.toNat + 3 + old_sz ≤ i → ar3[i]? = s2.core.arena[i]?))

theorem s13_anaWitnessCut_with_flags {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {k : FullCoreState} (hw : FullAnalyzeSpecs.FullWitnessCutInv c F0 F_cur cut k)
    (fl' : List (BitVec 32)) :
    FullAnalyzeSpecs.FullWitnessCutInv c F0 F_cur cut { k with flags := fl' } :=
  { hw with
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) }

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

theorem s13_otfs_large_fin {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
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
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        hkeep_s0 j hj1 (by omega)]
      exact hne_old j (by omega)
    · intro h0; exact absurd h0 hshv0
    · intro _; rw [har_b_ne (cref.toNat + 3 + old_sz - 1) (by omega)]; dsimp only [ar_a]
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        show cref.toNat + 3 + old_sz - 1 = cref.toNat + 3 + (old_sz - 1) by omega,
        hkeep_s0 (old_sz - 1) (by omega) (by omega)]
      exact hne_old (old_sz - 1) (by omega)
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
      dsimp only [ar_a]; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        hkeep_s0 j hj1 (by omega)]
      exact hne_old j (by omega)
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
    (hlen : s.LengthsOk c) (hw : FullAnalyzeSpecs.FullWitnessCutInv c F0 F_cur cut s.core)
    (hnd : FullArenaVarsNodup s) (hlen2 : s2.LengthsOk c)
    (hw2 : FullAnalyzeSpecs.FullWitnessCutInv c F0 F_cur cut s2.core)
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
      s3.LengthsOk c ∧ FullAnalyzeSpecs.FullWitnessCutInv c F0 F_cur idx_u s3.core ∧
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
    Full.otfs_large_shrink_ok hlen hw hnd hlen2 hw2 hnd2
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
  have hw3 : FullAnalyzeSpecs.FullWitnessCutInv c F0 F_cur idx_u s3.core :=
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
  have hz := m5_otfs_bv_idx3_64 cref j (by omega) (by omega); exact ⟨hz, by rw [hz, har]; omega⟩

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
    rw [m5_list_getElem_of_idx (hj := by rw [← hcr2_z]; exact hcr2_bd) hcr2_z]; exact hsz32
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
    (m5_list_getElem_of_idx (congrArg (·.toNat / 2) hot_eq)))

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
      (m5_list_getElem_of_idx (congrArg (·.toNat / 2) hot_eq.symm))))

theorem s13_otfs_p1_brk {k : FullCoreState} {cref i_nat old_sz : Nat}
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

theorem s13_otfs_p1_inc {k : FullCoreState} {cref i_nat : Nat} (hi2 : 2 ≤ i_nat)
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
    (m5_list_getElem_of_list_idx hlvl_eq (congrArg (·.toNat / 2) hot_c_eq)))

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
      (m5_list_getElem_of_list_idx hlvl_eq.symm (congrArg (·.toNat / 2) hot_c_eq.symm))))
  exact ⟨har_c, rfl, by omega, by omega, hns1,
    by rw [hact, Full.otfsActCnt_succ hi2, ite_eq_right hlv_0, Nat.add_zero],
    hlm, hpw, fun p hp => Nat.lt_succ_of_lt (hlt_m p hp), h01,
    fun p hp2 hplt hpos => by
      by_cases hpi : p = i_nat
      · subst p; exact absurd hpos hlv_0
      · exact hcov p hp2 (by omega) hpos, hmapeq, hout_m⟩

theorem s13_otfs_loop1_step_bds {c : FullCfg} {s : FullState} {cref : BitVec 32}
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

theorem s13_otfs_loop2_step_bds {c : FullCfg} {s s2 : FullState}
    {ar1 ar_cur : List (BitVec 32)} {cref l0 uip : BitVec 32}
    {old_sz i_nat nsz : Nat} {origMap : List Nat}
    (hcap : c.arena_cap < 2 ^ 31 - 1) (h3o : cref.toNat + 3 + old_sz ≤ c.arena_cap)
    (hcv_le : s.core.cur_vars ≤ c.max_vars) (hlvl_len : s.core.lvl.length = c.max_vars)
    (hs2_lvl_l : s2.core.lvl.length = c.max_vars) (har_len : s.core.arena.length = c.arena_cap)
    (hinv : S13OtfsShrinkInv c s ar1 cref l0 uip old_sz (old_sz - i_nat) i_nat nsz ar_cur origMap)
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

theorem s13_otfs_swap1_nl1 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
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

theorem s13_otfs_nodup_same_arena {s4 s5 : FullState} {ar : List (BitVec 32)}
    (hs5_ar : s5.core.arena = ar) (hs5_al : s5.core.arena_len = s4.core.arena_len)
    (hs4_ar : s4.core.arena = ar) (hnd4 : FullArenaVarsNodup s4) :
    FullArenaVarsNodup s5 := fun r hr hngr => by
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

theorem s13_otfs_oom_early_wp {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut idx_u : Nat} {s s_d : FullState} {cref : BitVec 32}
    {R : Mem 64 → Prop} {Q : Post [.bool]} {m_o : Mem 64}
    {wv_d ws_d : List (BitVec 32)} {wl_d : Nat} {wu_d : BitVec 64} {wso_d : List (BitVec 32)}
    (hsd_c : s_d.core =
      { s.core with wvec := wv_d, wstk := ws_d, wlen := wl_d, wusable := wu_d })
    (hsd_sc : s_d.scratch = { s.scratch with wsort := wso_d })
    (hlen_d : s_d.LengthsOk c) (hw_d : FullWitnessCutInv c F0 F_cur cut s_d.core)
    (hnd : FullArenaVarsNodup s) (hiu_cut : idx_u < cut)
    (hm_o : (FullMem c { s_d with core := { s_d.core with oom := 1#64 } } ⋆ R) m_o)
    (hQ : ∀ (ok : Bool) flags' arena' wvec' wstk' wlen' wu' oom' sc' m',
      let s' : FullState :=
        { s with
          core := { s.core with flags := flags', arena := arena', wvec := wvec',
                                wstk := wstk', wlen := wlen', wusable := wu', oom := oom' }
          scratch := sc' }
      s'.LengthsOk c → FullWitnessCutInv c F0 F_cur idx_u s'.core →
      FullArenaVarsNodup s' →
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
  have hw_o : FullWitnessCutInv c F0 F_cur idx_u s_o.core := by
    change FullWitnessCutInv c F0 F_cur idx_u k_o; rw [← hk_eq]
    exact m5_canonCut_shrink_cut (m5_canonCut_with_oom hw_d 1#64) (Nat.le_of_lt hiu_cut)
  have hnd_o : FullArenaVarsNodup s_o := hnd
  have hm_o' : (FullMem c s_o ⋆ R) m_o := m5_fullMem_of_eq hm_o hk_eq hsc_eq
  exact hQ false s.core.flags s.core.arena wv_d ws_d wl_d wu_d 1#64 sc_o m_o hlen_o hw_o hnd_o
    ⟨rfl, rfl⟩ rfl rfl rfl rfl (fun hc => by cases hc) hm_o'

theorem s13_otfs_fin_wp {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut idx_u : Nat} {s s_p s2 s4 : FullState}
    {ar1 ar4 fl3 wv2 ws2 ws_f : List (BitVec 32)}
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
    (hs4_c : s4.core = { s2.core with arena := ar4, flags := fl3 })
    (hs4_sc : s4.scratch = { s.scratch with wsort := wso_p })
    (hw4 : FullAnalyzeSpecs.FullWitnessCutInv c F0 F_cur idx_u s4.core)
    (hlen4 : s4.LengthsOk c) (hnd4 : FullArenaVarsNodup s4)
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
    (hQ : ∀ (ok : Bool) flags' arena' wvec' wstk' wlen' wu' oom' sc' m',
      let s' : FullState :=
        { s with
          core := { s.core with flags := flags', arena := arena', wvec := wvec',
                                wstk := wstk', wlen := wlen', wusable := wu', oom := oom' }
          scratch := sc' }
      s'.LengthsOk c → FullWitnessCutInv c F0 F_cur idx_u s'.core →
      FullArenaVarsNodup s' →
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
    { s.core with flags := fl3, arena := ar4, wvec := wv2, wstk := ws_f, wlen := wl_p,
                  wusable := wu2, oom := s.core.oom }
  let sc_fin : FullScratch :=
    { s.scratch with wsort := wso_p, otfs_cnt := s4.scratch.otfs_cnt + 1#64 }
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
  have hnd_f : FullArenaVarsNodup s_fin :=
    s13_otfs_nodup_same_arena (s4 := s4) (s5 := s_fin) (ar := ar4)
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
  have hlits_f := s13_otfs_large_fin hlen hw hcref hng hiu_cut hiu_te ht_u hr_u (s' := s_fin)
    rfl rfl rfl rfl
    (fun l hl => hlits4 l (by
      dsimp only [fullArenaClauseLits, fullArenaClauseLitsCore, fullArenaClauseSizeCore, s_fin,
        k_fin] at hl ⊢
      rw [show s4.core.arena = ar4 by rw [hs4_c]]; exact hl))
  have hot_sc : s4.scratch.otfs_cnt = s.scratch.otfs_cnt := by rw [hs4_sc]
  have hfin_eq : s_fin =
      { s with
        core := { s.core with flags := fl3, arena := ar4, wvec := wv2, wstk := ws_f,
                              wlen := wl_p, wusable := wu2, oom := s.core.oom }
        scratch := { s.scratch with wsort := wso_p, otfs_cnt := s.scratch.otfs_cnt + 1#64 } } := by
    dsimp only [s_fin, k_fin, sc_fin]; rw [hot_sc]
  rw [hfin_eq] at hlen_f hw_f_ana hnd_f hrefs_s4 hcref_f hng_f hlits_f hm_f'
  exact hQ true fl3 ar4 wv2 ws_f wl_p wu2 s.core.oom
    { s.scratch with wsort := wso_p, otfs_cnt := s.scratch.otfs_cnt + 1#64 }
    m_sc hlen_f
    (m5_anaCut_to_canonCut hw_f_ana (by dsimp only; omega)) hnd_f
    ⟨rfl, rfl⟩ rfl rfl rfl (hrefs_s4.trans hrefs4)
    (fun _ => ⟨hcref_f, hng_f, fun l hl => let ⟨_, _, hv, hlv⟩ := hlits_f l hl; ⟨hv, hlv⟩⟩)
    hm_f'

theorem s13_otfs_s1_facts {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
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
    FullArenaVarsNodup s1 ∧
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
  have hnd1' : FullArenaVarsNodup s1 := by
    unfold FullArenaVarsNodup fullArenaClauseRefs fullArenaClauseGarb fullArenaClauseLits
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

theorem s13_otfs_s4_facts {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {idx_u nsz : Nat} {s s2 s3 s4 : FullState}
    {ar1 ar3 ar4 fl3 wv2 ws2 : List (BitVec 32)} {wl_p : Nat} {wu2 : BitVec 64}
    {cref l0 uip : BitVec 32}
    (_hcref : cref.toNat ∈ fullArenaClauseRefs s) (hdm : s.core.dense_mode = 0#64)
    (hrefs1' : fullArenaClauseRefs s2 = fullArenaClauseRefs s)
    (hs2_base : s2.core =
      { s.core with arena := ar1, wvec := wv2, wstk := ws2, wlen := wl_p,
                    wusable := wu2, oom := s.core.oom })
    (hs3_c : s3.core = { s2.core with arena := ar3, flags := fl3 })
    (hlen3 : s3.LengthsOk c)
    (hrefs3 : fullArenaClauseRefsCore s3.core = fullArenaClauseRefsCore s2.core)
    (hcref3 : cref.toNat ∈ fullArenaClauseRefsCore s3.core)
    (hs4_c : s4.core = { s2.core with arena := ar4, flags := fl3 })
    (hs4_sc : s4.scratch = s3.scratch) (hcv : s4.core.cur_vars = s.core.cur_vars)
    (h2cv_lt : 2 * s.core.cur_vars < 2 ^ 31 - 1) (hl0_lt : l0.toNat < 2 * s.core.cur_vars)
    (hcr_lt31 : cref.toNat < 0x80000000) (hnsz3 : 3 ≤ nsz)
    (hcap : cref.toNat + 3 + nsz ≤ c.arena_cap) (h4bd : cref.toNat + 4 < ar4.length)
    (har4_l : ar4.length = c.arena_cap) (hcb1_eq : cref.setWidth 64 + 3#64 + 1#64 =
      cref.setWidth 64 + 4#64) (hcr4_z : (cref.setWidth 64 + 4#64).toNat = cref.toNat + 4)
    (hw4 : FullAnalyzeSpecs.FullWitnessCutInv c F0 F_cur idx_u { s3.core with arena := ar4 })
    (hnd4 : FullArenaVarsNodup { s3 with core := { s3.core with arena := ar4 } })
    (hrefs4 : fullArenaClauseRefsCore { s3.core with arena := ar4 } =
      fullArenaClauseRefsCore s3.core)
    (hsz4 : fullArenaClauseSizeCore { s3.core with arena := ar4 } cref.toNat = nsz)
    (hng4 : fullArenaClauseGarbCore { s3.core with arena := ar4 } cref.toNat = false)
    (hlits4 : ∀ l ∈ fullArenaClauseLitsCore { s3.core with arena := ar4 } cref.toNat,
      l ≠ uip.toNat ∧ l ∈ fullArenaClauseLits s cref.toNat) :
    s4.LengthsOk c ∧
    FullAnalyzeSpecs.FullWitnessCutInv c F0 F_cur idx_u s4.core ∧
    FullArenaVarsNodup s4 ∧
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
  have hnd4' : FullArenaVarsNodup s4 := by
    unfold FullArenaVarsNodup at hnd4 ⊢
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
  obtain ⟨hnl1_lt, _⟩ := s13_otfs_swap1_nl1 hw4' hcv hs4_ar h2cv_lt hcref4 hng4' hsz4' hnsz3
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

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S2
