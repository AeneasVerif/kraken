module

public import LeanQbe.T.Examples.Kissat.PlainMinLemmas2

/-!
# Soundness Proofs for Kissat `D-Plain` Shrink & Minimization (`Wave 2b Shard 5`, Part 3)

Shared block-shrink and minimization invariants, trail-count & reason-coverage lemmas,
state-stepping lemmas for `plain_min_mark`, `shrink_blk_success_finish`, `shrink_after_min_lit_ok`,
and scoped tactic macros (`ml_ld`, `ml_st`) in `PlainMinTactics`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Plain

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test

open scoped PlainMinTactics

/-! ## 1. Pure bitvector, list, and `plain_min_mark` step helpers -/

theorem xor1_div2 (n : Nat) : (n ^^^ 1) / 2 = n / 2 := by
  have h := litVar_litNeg n; unfold litVar litNeg at h; exact h

theorem xor1_xor1 (n : Nat) : (n ^^^ 1) ^^^ 1 = n := by
  have h := litNeg_litNeg n; unfold litNeg at h; exact h

theorem bv32_xor1_toNat_lt {x : BitVec 32} {mv : Nat} (hx : x.toNat < 2 * mv) :
    (x ^^^ 1#32).toNat = x.toNat ^^^ 1 ∧ (x ^^^ 1#32).toNat < 2 * mv := by
  have h1 : (1#32 : BitVec 32).toNat = 1 := rfl
  have hto : (x ^^^ 1#32).toNat = x.toNat ^^^ 1 := by rw [BitVec.toNat_xor, h1]
  have hv := xor1_div2 x.toNat
  exact ⟨hto, by omega⟩

theorem min_bv64_add1 {x : BitVec 64} (hx : x.toNat + 1 < 2 ^ 64) :
    (x + 1).toNat = x.toNat + 1 := by bv_omega
theorem min_bv64_sub1 {x : BitVec 64} (hx : 1 ≤ x.toNat) :
    (x - 1).toNat = x.toNat - 1 := by bv_omega
theorem min_bv64_sub {a b : BitVec 64} (h : b.toNat ≤ a.toNat) :
    (a - b).toNat = a.toNat - b.toNat := by bv_omega
theorem bv64_pos_of_ne0 {x : BitVec 64} (h : ¬x = 0) : 1 ≤ x.toNat := by
  have h0 : (0 : BitVec 64).toNat = 0 := rfl
  exact Nat.pos_of_ne_zero fun hz => h (BitVec.eq_of_toNat_eq (hz.trans h0.symm))
theorem bv32_add1_toNat {x : BitVec 32} (hx : x.toNat + 1 < 2 ^ 32) :
    (x + 1).toNat = x.toNat + 1 := by bv_omega
theorem bv64_zext32_add2 (r : BitVec 32) :
    (r.setWidth 64 + 2).toNat = r.toNat + 2 := by bv_omega
theorem bv64_zext32_add3_add (r i : BitVec 32) :
    (r.setWidth 64 + 3 + i.setWidth 64).toNat = r.toNat + 3 + i.toNat := by bv_omega
theorem bv64_lt_zext32_add3 {a : Nat} (ha : a < 2 ^ 64) (r : BitVec 32) :
    (BitVec.ofNat 64 a).ult (r.setWidth 64 + 3) = true → a < r.toNat + 3 := by
  intro h; rw [BitVec.ult, decide_eq_true_eq] at h; bv_omega
theorem bv64_lt_zext32_add3_add {a : Nat} (ha : a < 2 ^ 64) (r c : BitVec 32) :
    (BitVec.ofNat 64 a).ult (r.setWidth 64 + 3 + c.setWidth 64) = true →
      a < r.toNat + 3 + c.toNat := by
  intro h; rw [BitVec.ult, decide_eq_true_eq] at h; bv_omega

theorem bv8_and2_of_or2 (a : BitVec 8) : ((a ||| 2#8) &&& 2#8) ≠ 0#8 := by revert a; decide
theorem bv8_and8_of_or8 (a : BitVec 8) : ((a ||| 8#8) &&& 8#8) ≠ 0#8 := by revert a; decide
theorem bv8_and8_clear (a : BitVec 8) :
    ((a &&& 0xF7#8) &&& 8#8) = 0#8 := by revert a; decide
theorem bv8_and2_pres_clear8 (a : BitVec 8) : ((a &&& 0xF7#8) &&& 2#8) = (a &&& 2#8) := by
  revert a; decide
theorem bv8_and6_pres_clear8 (a : BitVec 8) : ((a &&& 0xF7#8) &&& 6#8) = (a &&& 6#8) := by
  revert a; decide
theorem bv8_and_dom_clear8 {a : BitVec 8} (h : (a &&& 0xF1#8) = 0#8) :
    ((a &&& 0xF7#8) &&& 0xF1#8) = 0#8 := by revert a h; decide
theorem bv8_and_dom_or2 {a : BitVec 8} (h : (a &&& 0xF1#8) = 0#8) :
    ((a ||| 2#8) &&& 0xF1#8) = 0#8 := by revert a h; decide
theorem bv8_and_dom_or4 {a : BitVec 8} (h : (a &&& 0xF1#8) = 0#8) :
    ((a ||| 4#8) &&& 0xF1#8) = 0#8 := by revert a h; decide
theorem bv8_and2_pres_or4 (a : BitVec 8) : ((a ||| 4#8) &&& 2#8) = (a &&& 2#8) := by
  revert a; decide
theorem bv8_and2_pres_or8 (a : BitVec 8) : ((a ||| 8#8) &&& 2#8) = (a &&& 2#8) := by
  revert a; decide
theorem bv8_and8_pres_or2 {a : BitVec 8} (h : (a &&& 8#8) = 0#8) :
    ((a ||| 2#8) &&& 8#8) = 0#8 := by revert a h; decide
theorem bv8_and8_pres_or4 {a : BitVec 8} (h : (a &&& 8#8) = 0#8) :
    ((a ||| 4#8) &&& 8#8) = 0#8 := by revert a h; decide

theorem bv8_or8_c0 (a : BitVec 8) :
    (a.setWidth 32 ||| (BitVec.setWidth 8 (8 : BitVec 32)).setWidth 32).setWidth 8 = a ||| 8#8 :=
  bv8_or_zext32_trunc8 a 8#8

theorem bv8_and247_c0 (a : BitVec 8) :
    (a.setWidth 32 &&& (BitVec.setWidth 8 (247 : BitVec 32)).setWidth 32).setWidth 8 =
      a &&& 0xF7#8 :=
  bv8_and_zext32_trunc8 a 0xF7#8

theorem mem_filter_map_toNat_take {xs : List (BitVec 32)} {n l : Nat} :
    l ∈ ((xs.take n).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat ↔
      ∃ k < min n xs.length, ∃ b, xs[k]? = some b ∧ b ≠ 0xFFFFFFFF#32 ∧ b.toNat = l := by
  rw [List.mem_map]
  constructor
  · rintro ⟨b, hb, rfl⟩
    rw [List.mem_filter, List.mem_iff_getElem] at hb
    obtain ⟨⟨k, hk, hkb⟩, hne⟩ := hb
    rw [List.length_take] at hk
    rw [List.getElem_take] at hkb
    exact ⟨k, hk, b, by rw [List.getElem?_eq_getElem (by omega), hkb],
      decide_eq_true_eq.mp hne, rfl⟩
  · rintro ⟨k, hk, b, hkb, hne, rfl⟩
    refine ⟨b, List.mem_filter.mpr ⟨List.mem_iff_getElem.mpr
      ⟨k, by rw [List.length_take]; exact hk, ?_⟩, decide_eq_true_eq.mpr hne⟩, rfl⟩
    rw [List.getElem_take]
    rw [List.getElem?_eq_getElem (by omega)] at hkb
    exact Option.some.inj hkb

@[expose] def plainMinMarkStepState (c : PlainCfg) (s : PlainState) (v : Nat) (tag : BitVec 8) :
    PlainState :=
  if (s.mrk[v]?.getD 0#8 &&& tag) ≠ 0#8 then s else plainMinMarkState c s v tag

theorem plainMinMarkSpec_step {c : PlainCfg} {s : PlainState} {R : Mem 64 → Prop}
    {m : Mem 64} {Q' : Post []} {X' : XPost} (hlen : s.LengthsOk c)
    (hm : (PlainMem c s ⋆ R) m) (v : BitVec 32) (hv : v.toNat < c.mv) (tag : BitVec 8)
    (hpost : ∀ m', (PlainMem c (plainMinMarkStepState c s v.toNat tag) ⋆ R) m' → Q' () m') :
    plainMinMarkSpec (c.hdr, v, tag, ()) m Q' X' := by
  refine ⟨c, s, R, rfl, hlen, hm, ?_⟩
  dsimp only [plainMinMarkStepState] at hpost ⊢
  by_cases hset : (s.mrk[v.toNat]?.getD 0#8 &&& tag) ≠ 0#8
  · have hc : c.mv ≤ v.toNat ∨ (s.mrk[v.toNat]?.getD 0#8 &&& tag) ≠ 0#8 := Or.inr hset
    simp only [eq_true hset, ↓reduceIte] at hpost
    simp only [eq_true hc, ↓reduceIte]
    exact hpost m hm
  · have hc : ¬ (c.mv ≤ v.toNat ∨ (s.mrk[v.toNat]?.getD 0#8 &&& tag) ≠ 0#8) := fun h =>
      h.elim (fun hle => by omega) hset
    simp only [eq_false hset, ↓reduceIte] at hpost
    simp only [eq_false hc, ↓reduceIte]
    by_cases hnz : s.mrk[v.toNat]?.getD 0#8 ≠ 0#8
    · simp only [eq_true hnz, ↓reduceIte]
      intro m' hm'
      have hp := hpost m'
      have hne0 : ¬ (s.mrk[v.toNat]?.getD 0#8 = 0#8 ∧ s.min_clr_len < c.mv) := fun h => hnz h.1
      have hne1 : ¬ (s.mrk[v.toNat]?.getD 0#8 = 0#8 ∧ ¬ s.min_clr_len < c.mv) := fun h => hnz h.1
      dsimp only [plainMinMarkState] at hp
      simp only [eq_false hne0, eq_false hne1, ↓reduceIte] at hp
      exact hp hm'
    · have hz : s.mrk[v.toNat]?.getD 0#8 = 0#8 := Decidable.not_not.mp hnz
      simp only [eq_false hnz, ↓reduceIte]
      by_cases hcl : s.min_clr_len < c.mv
      · simp only [eq_true hcl, ↓reduceIte]
        intro m' hm'
        have hp := hpost m'
        have he1 : s.mrk[v.toNat]?.getD 0#8 = 0#8 ∧ s.min_clr_len < c.mv := ⟨hz, hcl⟩
        have he2 : ¬ (s.mrk[v.toNat]?.getD 0#8 = 0#8 ∧ ¬ s.min_clr_len < c.mv) := fun h => h.2 hcl
        dsimp only [plainMinMarkState] at hp
        simp only [eq_true he1, eq_false he2, ↓reduceIte, bv_ofNat_toNat_eq v] at hp
        exact hp hm'
      · simp only [eq_false hcl, ↓reduceIte]
        intro m' hm'
        have hp := hpost m'
        have he1 : ¬ (s.mrk[v.toNat]?.getD 0#8 = 0#8 ∧ s.min_clr_len < c.mv) := fun h => hcl h.2
        have he2 : s.mrk[v.toNat]?.getD 0#8 = 0#8 ∧ ¬ s.min_clr_len < c.mv := ⟨hz, hcl⟩
        dsimp only [plainMinMarkState] at hp
        simp only [eq_false he1, eq_true he2, ↓reduceIte] at hp
        exact hp hm'

theorem plainMinMarkStepState_lengths {c : PlainCfg} {s : PlainState}
    (hlen : s.LengthsOk c) (v : Nat) (tag : BitVec 8) :
    (plainMinMarkStepState c s v tag).LengthsOk c := by
  dsimp only [plainMinMarkStepState, plainMinMarkState]
  by_cases hs : (s.mrk[v]?.getD 0#8 &&& tag) ≠ 0#8
  · simp only [eq_true hs, ↓reduceIte]; exact hlen
  · simp only [eq_false hs, ↓reduceIte]
    by_cases hc : s.mrk[v]?.getD 0#8 = 0#8 ∧ s.min_clr_len < c.mv
    · simp only [eq_true hc, ↓reduceIte]
      exact { hlen with
        mrk_len := by dsimp only; simp [hlen.mrk_len]
        min_clr_len_arr := by dsimp only; simp [hlen.min_clr_len_arr]
        min_clr_len_le := by dsimp only; omega }
    · simp only [eq_false hc, ↓reduceIte]
      exact { hlen with mrk_len := by dsimp only; simp [hlen.mrk_len] }

theorem plainMinMarkStepState_bit8_mono2 {c : PlainCfg} {s : PlainState}
    (hlen : s.LengthsOk c) {v : Nat} (hv : v < c.mv) {tag : BitVec 8}
    (htag : tag = 2#8 ∨ tag = 4#8) (hno8 : (s.mrk[v]?.getD 0#8 &&& 8#8) = 0#8) :
    (∀ w < c.mv, ((plainMinMarkStepState c s v tag).mrk[w]?.getD 0#8 &&& 8#8) =
      (s.mrk[w]?.getD 0#8 &&& 8#8)) ∧
    (∀ w < c.mv, (s.mrk[w]?.getD 0#8 &&& 2#8) ≠ 0#8 →
      ((plainMinMarkStepState c s v tag).mrk[w]?.getD 0#8 &&& 2#8) ≠ 0#8) := by
  dsimp only [plainMinMarkStepState, plainMinMarkState]; split
  · exact ⟨fun _ _ => rfl, fun _ _ h => h⟩
  · refine ⟨fun w hw => ?_, fun w hw h2 => ?_⟩
    · dsimp only; by_cases hwe : w = v
      · subst w; rw [List.getElem?_set_self (by rw [hlen.mrk_len]; exact hv), Option.getD_some]
        rcases htag with rfl | rfl
        · exact (bv8_and8_pres_or2 hno8).trans hno8.symm
        · exact (bv8_and8_pres_or4 hno8).trans hno8.symm
      · rw [List.getElem?_set_ne (Ne.symm hwe)]
    · dsimp only; by_cases hwe : w = v
      · subst w; rw [List.getElem?_set_self (by rw [hlen.mrk_len]; exact hv), Option.getD_some]
        rcases htag with rfl | rfl
        · exact bv8_and2_of_or2 _
        · rwa [bv8_and2_pres_or4]
      · rwa [List.getElem?_set_ne (Ne.symm hwe)]

theorem plainMinMarkStepState_dom_clr {c : PlainCfg} {s : PlainState}
    (hlen : s.LengthsOk c)
    (hdom : ∀ w < c.mv, (s.mrk[w]?.getD 0#8 &&& 0xF1#8) = 0#8)
    (hcov : s.min_clr_full = 0#64 → ∀ w < c.mv, (s.mrk[w]?.getD 0#8 &&& 6#8) ≠ 0#8 →
      ∃ k < s.min_clr_len, (s.min_clr[k]?.getD 0#32).toNat = w)
    {v : Nat} (hv : v < c.mv) {tag : BitVec 8} (htag : tag = 2#8 ∨ tag = 4#8)
    (hno8 : (s.mrk[v]?.getD 0#8 &&& 8#8) = 0#8) :
    let s' := plainMinMarkStepState c s v tag
    (∀ w < c.mv, (s'.mrk[w]?.getD 0#8 &&& 0xF1#8) = 0#8) ∧
    (s'.min_clr_full = 0#64 → ∀ w < c.mv, (s'.mrk[w]?.getD 0#8 &&& 6#8) ≠ 0#8 →
      ∃ k < s'.min_clr_len, (s'.min_clr[k]?.getD 0#32).toNat = w) := by
  dsimp only [plainMinMarkStepState]
  by_cases hset : (s.mrk[v]?.getD 0#8 &&& tag) ≠ 0#8
  · simp only [eq_true hset, ↓reduceIte]; exact ⟨hdom, hcov⟩
  · simp only [eq_false hset, ↓reduceIte]
    refine ⟨fun w hw => ?_, ?_⟩
    · dsimp only [plainMinMarkState]
      by_cases hwe : w = v
      · subst hwe
        rw [List.getElem?_set_self (by rw [hlen.mrk_len]; exact hv), Option.getD_some]
        rcases htag with rfl | rfl
        · exact bv8_and_dom_or2 (hdom w hw)
        · exact bv8_and_dom_or4 (hdom w hw)
      · rw [List.getElem?_set_ne (Ne.symm hwe)]; exact hdom w hw
    · intro hmcf w hw hnz
      dsimp only [plainMinMarkState] at hmcf hnz ⊢
      by_cases hcur0 : s.mrk[v]?.getD 0#8 = 0#8
      · by_cases hlt : s.min_clr_len < c.mv
        · simp only [hcur0, hlt, and_self, not_true_eq_false, and_false,
            ↓reduceIte] at hmcf hnz ⊢
          by_cases hweq : w = v
          · subst w
            have hmv := c.hmv; unfold dimacsBound at hmv
            refine ⟨s.min_clr_len, by omega, ?_⟩
            rw [List.getElem?_set_self (by rw [hlen.min_clr_len_arr]; exact hlt), Option.getD_some,
              bv32_ofNat_toNat (by omega)]
          · have hnz' : (s.mrk[w]?.getD 0#8 &&& 6#8) ≠ 0#8 := by
              simpa [List.getElem?_set_ne (Ne.symm hweq)] using hnz
            obtain ⟨k, hk, hkeq⟩ := hcov hmcf w hw hnz'
            exact ⟨k, by omega, by rw [List.getElem?_set_ne (by omega)]; exact hkeq⟩
        · simp only [hcur0, hlt, not_false_eq_true, and_self, ↓reduceIte] at hmcf
          cases hmcf
      · simp only [hcur0, false_and, ↓reduceIte] at hmcf hnz ⊢
        by_cases hweq : w = v
        · subst w
          exact hcov hmcf v hv (fun h6 => hcur0 (bv8_eq_zero_of_masks _ (hdom v hv) hno8 h6))
        · exact hcov hmcf w hw (by simpa [List.getElem?_set_ne (Ne.symm hweq)] using hnz)

theorem plainMinMarkInv_step_poison {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    {keep : List Nat} (hcore : PlainCoreInv c F0 s) (hmin : PlainMinMarkInv c F0 s keep)
    {v : Nat} (hv : v < c.mv) (hno8 : (s.mrk[v]?.getD 0#8 &&& 8#8) = 0#8) :
    PlainMinMarkInv c F0 (plainMinMarkStepState c s v 4#8) keep := by
  dsimp only [plainMinMarkStepState]
  split
  · exact hmin
  · exact plainMinMarkInv_poison hcore hmin hv hno8

theorem plainMinMarkInv_step_keep {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    {keep : List Nat} (hcore : PlainCoreInv c F0 s) (hmin : PlainMinMarkInv c F0 s keep)
    {l : Nat} (hl : l < 2 * c.mv) (hkeep : l ∈ keep) (hfals : s.vals[l]?.getD 0#8 = 0xFF#8)
    (hno8 : (s.mrk[l / 2]?.getD 0#8 &&& 8#8) = 0#8) :
    PlainMinMarkInv c F0 (plainMinMarkStepState c s (l / 2) 2#8) keep := by
  dsimp only [plainMinMarkStepState]
  split
  · exact hmin
  · exact plainMinMarkInv_mark_keep hcore hmin hl hkeep hfals hno8

@[expose] def shrinkBlkSt (s : PlainState) (tmp1 : List (BitVec 32)) (mrk1 : List (BitVec 8))
    (mstk1 mclr1 : List (BitVec 32)) (mcl1 : Nat) (mcf1 : BitVec 64)
    (sstk1 : List (BitVec 32)) : PlainState :=
  { s with
    tmp := tmp1, mrk := mrk1, min_stk := mstk1, min_clr := mclr1,
    min_clr_len := mcl1, min_clr_full := mcf1,
    heur := { s.heur with shrink_stk := sstk1 } }

theorem coreInv_shrinkBlk {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    (hcore : PlainCoreInv c F0 s) {tmp1 : List (BitVec 32)} {mrk1 : List (BitVec 8)}
    {mstk1 mclr1 sstk1 : List (BitVec 32)} {mcl1 : Nat} {mcf1 : BitVec 64}
    (htmp : tmp1.length = c.mv) (hmrk : mrk1.length = c.mv)
    (hmstk : mstk1.length = 2 * c.minDepth) (hmclr : mclr1.length = c.mv)
    (hmcl : mcl1 ≤ c.mv) (hsstk : sstk1.length = c.mv) :
    PlainCoreInv c F0 (shrinkBlkSt s tmp1 mrk1 mstk1 mclr1 mcl1 mcf1 sstk1) :=
  { hcore with
    lengths := { hcore.lengths with
      tmp_len_arr := htmp, mrk_len := hmrk, min_stk_len := hmstk,
      min_clr_len_arr := hmclr, min_clr_len_le := hmcl,
      heur_ok := { hcore.lengths.heur_ok with shrink_stk_len := hsstk } }
    arena := { hcore.arena with len_ok := hcore.arena.len_ok }
    watches := hcore.watches.with_wstk rfl rfl rfl rfl }

theorem shrinkBlkSt_step {c : PlainCfg} {s : PlainState} {tmp1 : List (BitVec 32)}
    {mrk1 : List (BitVec 8)} {mstk1 mclr1 sstk1 : List (BitVec 32)} {mcl1 : Nat}
    {mcf1 : BitVec 64} (v : Nat) (tag : BitVec 8) :
    let sb := shrinkBlkSt s tmp1 mrk1 mstk1 mclr1 mcl1 mcf1 sstk1
    let sb' := plainMinMarkStepState c sb v tag
    sb' = shrinkBlkSt s tmp1 sb'.mrk mstk1 sb'.min_clr sb'.min_clr_len sb'.min_clr_full sstk1 := by
  intro sb sb'
  dsimp only [sb', plainMinMarkStepState, plainMinMarkState, sb, shrinkBlkSt]
  split
  · rfl
  · split <;> rfl

/-! ## 2. Block-shrink trail count, reason coverage, and finish invariants -/

@[expose] def trailCount8 (trl : List (BitVec 32)) (mrk : List (BitVec 8)) : Nat → Nat
  | 0 => 0
  | n + 1 => trailCount8 trl mrk n +
      if (mrk[(trl[n]?.getD 0#32).toNat / 2]?.getD 0#8 &&& 8#8) ≠ 0#8 then 1 else 0

theorem trailCount8_mono {trl : List (BitVec 32)} {mrk : List (BitVec 8)}
    {a b : Nat} (h : a ≤ b) : trailCount8 trl mrk a ≤ trailCount8 trl mrk b := by
  induction b with
  | zero => simp [show a = 0 by omega]
  | succ b ih =>
    by_cases he : a = b + 1
    · subst he; exact le_refl _
    · exact Nat.le_trans (ih (by omega)) (Nat.le_add_right _ _)

theorem trailCount8_zero_of_all_zero {trl : List (BitVec 32)} {mrk : List (BitVec 8)}
    {mv lim : Nat} (hlt : ∀ i < lim, (trl[i]?.getD 0#32).toNat / 2 < mv)
    (h0 : ∀ w < mv, (mrk[w]?.getD 0#8 &&& 8#8) = 0#8) :
    ∀ n ≤ lim, trailCount8 trl mrk n = 0 := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hn
    have h1 := ih (by omega)
    have h2 : (mrk[(trl[n]?.getD 0#32).toNat / 2]?.getD 0#8 &&& 8#8) = 0#8 :=
      h0 _ (hlt n (by omega))
    simp [trailCount8, h1, h2]

theorem trailCount8_eq_zero_mem {trl : List (BitVec 32)} {mrk : List (BitVec 8)}
    {n j : Nat} (h : trailCount8 trl mrk n = 0) (hj : j < n) :
    (mrk[(trl[j]?.getD 0#32).toNat / 2]?.getD 0#8 &&& 8#8) = 0#8 := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [trailCount8] at h
    by_cases hjn : j = n
    · subst hjn
      by_cases hnz : (mrk[(trl[j]?.getD 0#32).toNat / 2]?.getD 0#8 &&& 8#8) ≠ 0#8
      · simp [hnz] at h
      · exact Decidable.not_not.mp hnz
    · exact ih (by omega) (by omega)

theorem trailCount8_eq_of_bit8_eq {trl : List (BitVec 32)} {mrk1 mrk2 : List (BitVec 8)}
    {n mv : Nat} (hlt : ∀ j < n, (trl[j]?.getD 0#32).toNat / 2 < mv)
    (heq : ∀ w < mv, (mrk2[w]?.getD 0#8 &&& 8#8) = (mrk1[w]?.getD 0#8 &&& 8#8)) :
    trailCount8 trl mrk2 n = trailCount8 trl mrk1 n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [trailCount8, ih (fun j hj => hlt j (by omega)), heq _ (hlt n (Nat.lt_succ_self n))]

theorem trailCount8_set_bit8_le {trl : List (BitVec 32)} {mrk : List (BitVec 8)}
    {lim : Nat} (hnodup : ∀ i j, i < lim → j < lim →
      (trl[i]?.getD 0#32).toNat / 2 = (trl[j]?.getD 0#32).toNat / 2 → i = j)
    (v : Nat) : ∀ n ≤ lim,
    trailCount8 trl (mrk.set v (mrk[v]?.getD 0#8 ||| 8#8)) n ≤ trailCount8 trl mrk n + 1 := by
  intro n
  induction n with
  | zero => intro _; simp [trailCount8]
  | succ n ih =>
    intro hn
    by_cases hve : (trl[n]?.getD 0#32).toNat / 2 = v
    · have hpre : trailCount8 trl (mrk.set v (mrk[v]?.getD 0#8 ||| 8#8)) n =
          trailCount8 trl mrk n := by
        clear ih
        have hind : ∀ m ≤ n,
            trailCount8 trl (mrk.set v (mrk[v]?.getD 0#8 ||| 8#8)) m =
              trailCount8 trl mrk m := by
          intro m
          induction m with
          | zero => intro _; rfl
          | succ m ihm =>
            intro hm
            have hne : (trl[m]?.getD 0#32).toNat / 2 ≠ v := fun he => by
              have := hnodup m n (by omega) (by omega) (he.trans hve.symm); omega
            simp only [trailCount8, ihm (by omega), List.getElem?_set_ne (Ne.symm hne)]
        exact hind n (le_refl n)
      simp only [trailCount8, hpre]; split <;> split <;> omega
    · simp only [trailCount8, List.getElem?_set_ne (Ne.symm hve)]
      have := ih (by omega)
      omega

theorem trailCount8_step_zero {trl : List (BitVec 32)} {mrk : List (BitVec 8)} {n : Nat}
    (h : (mrk[(trl[n]?.getD 0#32).toNat / 2]?.getD 0#8 &&& 8#8) = 0#8) :
    trailCount8 trl mrk (n + 1) = trailCount8 trl mrk n := by
  simp [trailCount8, h]

theorem trailCount8_step_nz {trl : List (BitVec 32)} {mrk : List (BitVec 8)} {n : Nat}
    (h : (mrk[(trl[n]?.getD 0#32).toNat / 2]?.getD 0#8 &&& 8#8) ≠ 0#8) :
    trailCount8 trl mrk (n + 1) = trailCount8 trl mrk n + 1 := by
  simp [trailCount8, h]

theorem trailCount8_eq_of_zero_range {trl : List (BitVec 32)} {mrk : List (BitVec 8)}
    {a b : Nat} (hab : a ≤ b)
    (hz : ∀ j, a ≤ j → j < b → (mrk[(trl[j]?.getD 0#32).toNat / 2]?.getD 0#8 &&& 8#8) = 0#8) :
    trailCount8 trl mrk b = trailCount8 trl mrk a := by
  induction b with
  | zero => simp [show a = 0 by omega]
  | succ b ih =>
    by_cases hbe : a = b + 1
    · subst hbe; rfl
    · rw [trailCount8_step_zero (hz b (by omega) (by omega)),
        ih (by omega) (fun j h1 h2 => hz j h1 (by omega))]

@[expose] def RsnCov (c : PlainCfg) (F0 : CNF Nat) (s : PlainState)
    (P : Nat → Prop) (idx : Nat) : Prop :=
  let p := (s.trl[idx]?.getD 0#32).toNat
  let rsn := s.rsns[p / 2]?.getD 0xFFFFFFFF#32
  rsn ≠ 0xFFFFFFFF#32 ∧
  if (rsn &&& 0x80000000#32) ≠ 0#32 then
    let ot := (rsn &&& 0x7FFFFFFF#32).toNat
    ot < 2 * c.mv ∧ F0.EntailsClause (cnfClause [p, ot]) ∧
    ∃ k < idx, (s.trl[k]?.getD 0#32).toNat = ot ^^^ 1 ∧
      ((s.lvl[ot / 2]?.getD 0#32).toNat = 0 ∨ P (ot / 2))
  else
    rsn.toNat ∈ arenaClauseRefs s ∧ arenaClauseGarb s rsn.toNat = false ∧
    ∀ q ∈ arenaClauseLits s rsn.toNat,
      q = p ∨ ∃ k < idx, (s.trl[k]?.getD 0#32).toNat = q ^^^ 1 ∧
        ((s.lvl[q / 2]?.getD 0#32).toNat = 0 ∨ P (q / 2))

theorem rsnCov_mono {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    (hcore : PlainCoreInv c F0 s) {P1 P2 : Nat → Prop}
    (hP : ∀ w < c.mv, P1 w → P2 w) {idx : Nat} (h : RsnCov c F0 s P1 idx) :
    RsnCov c F0 s P2 idx := by
  dsimp only [RsnCov] at h ⊢
  rcases h with ⟨hne, hif⟩
  refine ⟨hne, ?_⟩
  split at hif <;> split
  · obtain ⟨hot, hent, k, hk, hkeq, hdep⟩ := hif
    exact ⟨hot, hent, k, hk, hkeq, hdep.elim Or.inl fun h1 => Or.inr (hP _ (by omega) h1)⟩
  · rename_i h1 h2; exact absurd h1 h2
  · rename_i h1 h2; exact absurd h2 h1
  · obtain ⟨href, hng, hall⟩ := hif
    refine ⟨href, hng, fun q hq => ?_⟩
    have hqlt := hcore.arena.lits_lt _ href hng _ hq
    rcases hall q hq with rfl | ⟨k, hk, hkeq, hdep⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨k, hk, hkeq, hdep.elim Or.inl fun h1 => Or.inr (hP _ (by omega) h1)⟩

abbrev ShrinkResolved (c : PlainCfg) (F0 : CNF Nat) (s : PlainState)
    (mrk : List (BitVec 8)) (idx : Nat) : Prop :=
  RsnCov c F0 s (fun w => (mrk[w]?.getD 0#8 &&& 2#8) ≠ 0#8 ∨ (mrk[w]?.getD 0#8 &&& 8#8) ≠ 0#8)
    idx

theorem remSound_lift_mrk2 {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    (hcore : PlainCoreInv c F0 s) {mrk1 mrk2 : List (BitVec 8)}
    (hm2 : ∀ w < c.mv, (mrk1[w]?.getD 0#8 &&& 2#8) ≠ 0#8 → (mrk2[w]?.getD 0#8 &&& 2#8) ≠ 0#8)
    {idx : Nat} (h : RsnCov c F0 s (fun w => (mrk1[w]?.getD 0#8 &&& 2#8) ≠ 0#8) idx) :
    RsnCov c F0 s (fun w => (mrk2[w]?.getD 0#8 &&& 2#8) ≠ 0#8) idx :=
  rsnCov_mono hcore hm2 h

theorem shrinkResolved_mono {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    (hcore : PlainCoreInv c F0 s) {mrk1 mrk2 : List (BitVec 8)}
    (hm2 : ∀ w < c.mv, (mrk1[w]?.getD 0#8 &&& 2#8) ≠ 0#8 → (mrk2[w]?.getD 0#8 &&& 2#8) ≠ 0#8)
    (hm8 : ∀ w < c.mv, (mrk1[w]?.getD 0#8 &&& 8#8) ≠ 0#8 → (mrk2[w]?.getD 0#8 &&& 8#8) ≠ 0#8)
    {idx : Nat} (hr : ShrinkResolved c F0 s mrk1 idx) :
    ShrinkResolved c F0 s mrk2 idx :=
  rsnCov_mono hcore (fun w hw h => h.elim (fun h2 => Or.inl (hm2 w hw h2))
    (fun h8 => Or.inr (hm8 w hw h8))) hr

theorem shrinkResolved_to_rem {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    (hcore : PlainCoreInv c F0 s) {mrk1 mrk2 : List (BitVec 8)}
    (hm2 : ∀ w < c.mv, (mrk1[w]?.getD 0#8 &&& 2#8) ≠ 0#8 → (mrk2[w]?.getD 0#8 &&& 2#8) ≠ 0#8)
    (hm8 : ∀ w < c.mv, (mrk1[w]?.getD 0#8 &&& 8#8) ≠ 0#8 → (mrk2[w]?.getD 0#8 &&& 2#8) ≠ 0#8)
    {idx : Nat} (hr : ShrinkResolved c F0 s mrk1 idx) :
    RsnCov c F0 s (fun w => (mrk2[w]?.getD 0#8 &&& 2#8) ≠ 0#8) idx :=
  rsnCov_mono hcore (fun w hw h => h.elim (hm2 w hw) (hm8 w hw)) hr

structure ShrinkBaseInv (c : PlainCfg) (F0 : CNF Nat) (s : PlainState)
    (mrk1 : List (BitVec 8)) (mstk1 mclr1 : List (BitVec 32)) (mcl1 : Nat) (mcf1 : BitVec 64)
    (sstk1 : List (BitVec 32)) (slen : Nat) (keep0 : List Nat) : Prop where
  mrk_len : mrk1.length = c.mv
  mstk_len : mstk1.length = 2 * c.minDepth
  mclr_len : mclr1.length = c.mv
  mcl_le : mcl1 ≤ c.mv
  sstk_len : sstk1.length = c.mv
  slen_le : slen ≤ c.mv
  min_inv : PlainMinMarkInv c F0 (shrinkBlkSt s s.tmp mrk1 mstk1 mclr1 mcl1 mcf1 sstk1) keep0
  mono2 : ∀ w < c.mv, (s.mrk[w]?.getD 0#8 &&& 2#8) ≠ 0#8 → (mrk1[w]?.getD 0#8 &&& 2#8) ≠ 0#8
  bit8_sstk : ∀ w < c.mv, (mrk1[w]?.getD 0#8 &&& 8#8) ≠ 0#8 →
    ∃ j < slen, (sstk1[j]?.getD 0#32).toNat = w
  sstk_lt : ∀ j < slen, (sstk1[j]?.getD 0#32).toNat < c.mv

theorem shrinkBaseInv_core {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    (hcore : PlainCoreInv c F0 s) {mrk1 : List (BitVec 8)} {mstk1 mclr1 sstk1 : List (BitVec 32)}
    {mcl1 slen : Nat} {mcf1 : BitVec 64} {keep0 : List Nat}
    (hb : ShrinkBaseInv c F0 s mrk1 mstk1 mclr1 mcl1 mcf1 sstk1 slen keep0) :
    PlainCoreInv c F0 (shrinkBlkSt s s.tmp mrk1 mstk1 mclr1 mcl1 mcf1 sstk1) :=
  coreInv_shrinkBlk hcore hcore.lengths.tmp_len_arr hb.mrk_len hb.mstk_len hb.mclr_len hb.mcl_le
    hb.sstk_len

theorem shrinkBaseInv_poison {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    (hcore : PlainCoreInv c F0 s) {mrk1 : List (BitVec 8)} {mstk1 mclr1 sstk1 : List (BitVec 32)}
    {mcl1 slen : Nat} {mcf1 : BitVec 64} {keep0 : List Nat}
    (hb : ShrinkBaseInv c F0 s mrk1 mstk1 mclr1 mcl1 mcf1 sstk1 slen keep0)
    {ov : Nat} (hov : ov < c.mv) (hno8 : (mrk1[ov]?.getD 0#8 &&& 8#8) = 0#8) :
    let sb := shrinkBlkSt s s.tmp mrk1 mstk1 mclr1 mcl1 mcf1 sstk1
    let sb' := plainMinMarkStepState c sb ov 4#8
    ShrinkBaseInv c F0 s sb'.mrk mstk1 sb'.min_clr sb'.min_clr_len sb'.min_clr_full
      sstk1 slen keep0 := by
  intro sb sb'
  have hcb := shrinkBaseInv_core hcore hb
  have hln := plainMinMarkStepState_lengths hcb.lengths ov 4#8
  obtain ⟨hbit8, hmono2⟩ := plainMinMarkStepState_bit8_mono2 hcb.lengths hov (Or.inr rfl) hno8
  have hmin' := plainMinMarkInv_step_poison hcb hb.min_inv hov hno8
  rw [shrinkBlkSt_step] at hln hmin'
  exact ⟨hln.mrk_len, hln.min_stk_len, hln.min_clr_len_arr, hln.min_clr_len_le,
    hb.sstk_len, hb.slen_le, hmin', fun w hw h2 => hmono2 w hw (hb.mono2 w hw h2),
    fun w hw h8 => hb.bit8_sstk w hw
      (by have h8' : sb'.mrk[w]?.getD 0#8 &&& 8#8 ≠ 0#8 := h8; rw [hbit8 w hw] at h8'; exact h8'),
    hb.sstk_lt⟩

private structure ShrinkOkInv (c : PlainCfg) (F0 : CNF Nat) (s : PlainState)
    (blvl : BitVec 32) (beg end_b : Nat) (mrk1 : List (BitVec 8))
    (sstk1 : List (BitVec 32)) (open_cnt slen t_lim : Nat) : Prop where
  op_pos : 1 ≤ open_cnt
  op_le : open_cnt ≤ (end_b - beg) + slen
  blk_bit8 : ∀ j, beg ≤ j → j < end_b →
    (mrk1[(s.tmp[j]?.getD 0#32).toNat / 2]?.getD 0#8 &&& 8#8) ≠ 0#8
  sstk_bit8 : ∀ j < slen, (mrk1[(sstk1[j]?.getD 0#32).toNat]?.getD 0#8 &&& 8#8) ≠ 0#8
  bit8_ok : ∀ w < c.mv, (mrk1[w]?.getD 0#8 &&& 8#8) ≠ 0#8 →
    (s.lvl[w]?.getD 0#32).toNat = blvl.toNat ∧
    ∃ idx < s.trail_end, (s.trl[idx]?.getD 0#32).toNat / 2 = w ∧
      (idx ≤ t_lim ∨ ShrinkResolved c F0 s mrk1 idx)
  cnt_le : trailCount8 s.trl mrk1 (min (t_lim + 1) s.trail_end) ≤ open_cnt

theorem shrinkOkInv_lvl_lt_no8 {c : PlainCfg} {s : PlainState} {blvl : BitVec 32}
    {mrk1 : List (BitVec 8)}
    (h8 : ∀ w < c.mv, (mrk1[w]?.getD 0#8 &&& 8#8) ≠ 0#8 →
      (s.lvl[w]?.getD 0#32).toNat = blvl.toNat)
    {ov : Nat} (hlov : (s.lvl[ov]?.getD 0#32).toNat < blvl.toNat) :
    ∀ w < c.mv, (s.lvl[w]?.getD 0#32).toNat ≤ (s.lvl[ov]?.getD 0#32).toNat →
      (mrk1[w]?.getD 0#8 &&& 8#8) = 0#8 := by
  intro w hw hle
  by_cases hnz : (mrk1[w]?.getD 0#8 &&& 8#8) = 0#8
  · exact hnz
  · have heq := h8 w hw hnz; omega

theorem shrinkOt_resolved_child {s : PlainState} {mrk1 : List (BitVec 8)} {ot : Nat}
    (hcond : ¬ ((s.lvl[ot / 2]?.getD 0#32).toNat > 0 ∧ (mrk1[ot / 2]?.getD 0#8 &&& 8#8) = 0#8)) :
    (s.lvl[ot / 2]?.getD 0#32).toNat = 0 ∨ (mrk1[ot / 2]?.getD 0#8 &&& 2#8) ≠ 0#8 ∨
      (mrk1[ot / 2]?.getD 0#8 &&& 8#8) ≠ 0#8 := by
  by_cases hl : (s.lvl[ot / 2]?.getD 0#32).toNat = 0
  · exact Or.inl hl
  · by_cases h8z : (mrk1[ot / 2]?.getD 0#8 &&& 8#8) = 0#8
    · exfalso; apply hcond; exact ⟨by omega, h8z⟩
    · exact Or.inr (Or.inr h8z)

theorem shrink_step_pre_push8 {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    (hcore : PlainCoreInv c F0 s) {blvl : BitVec 32} {beg end_b : Nat}
    {mrk1 : List (BitVec 8)} {mstk1 mclr1 sstk1 : List (BitVec 32)}
    {mcl1 open_cnt slen t_lim idx_uip k_ot : Nat} {mcf1 : BitVec 64} {keep0 : List Nat}
    (hb : ShrinkBaseInv c F0 s mrk1 mstk1 mclr1 mcl1 mcf1 sstk1 slen keep0)
    (hblk_lt : ∀ j, beg ≤ j → j < end_b → (s.tmp[j]?.getD 0#32).toNat / 2 < c.mv)
    (hblk_8 : ∀ j, beg ≤ j → j < end_b →
      (mrk1[(s.tmp[j]?.getD 0#32).toNat / 2]?.getD 0#8 &&& 8#8) ≠ 0#8)
    (hsstk_8 : ∀ j < slen, (mrk1[(sstk1[j]?.getD 0#32).toNat]?.getD 0#8 &&& 8#8) ≠ 0#8)
    (h8_pre : ∀ w < c.mv, (mrk1[w]?.getD 0#8 &&& 8#8) ≠ 0#8 →
      (s.lvl[w]?.getD 0#32).toNat = blvl.toNat ∧
      ∃ idx < s.trail_end, (s.trl[idx]?.getD 0#32).toNat / 2 = w ∧
        (idx ≤ t_lim ∨ ShrinkResolved c F0 s mrk1 idx ∨ idx = idx_uip))
    (hcnt_pre : trailCount8 s.trl mrk1 (min (t_lim + 1) s.trail_end) ≤ open_cnt - 1)
    (hop_ge : 2 ≤ open_cnt) (hop_le : open_cnt ≤ (end_b - beg) + slen)
    (hslen : slen < c.mv) {ot : BitVec 32} (hot : ot.toNat < 2 * c.mv)
    (huip_te : idx_uip < s.trail_end)
    (huip_lvl : (s.lvl[(s.trl[idx_uip]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = blvl.toNat)
    (hk_lt : k_ot < idx_uip) (hk_eq : (s.trl[k_ot]?.getD 0#32).toNat = ot.toNat ^^^ 1)
    (hk_tlim : k_ot ≤ t_lim) (hlov_ge : blvl.toNat ≤ (s.lvl[ot.toNat / 2]?.getD 0#32).toNat) :
    let ov := ot >>> 1
    let mrk2 := mrk1.set ov.toNat (mrk1[ov.toNat]?.getD 0#8 ||| 8#8)
    let sstk2 := sstk1.set slen ov
    ShrinkBaseInv c F0 s mrk2 mstk1 mclr1 mcl1 mcf1 sstk2 (slen + 1) keep0 ∧
    (∀ j, beg ≤ j → j < end_b →
      (mrk2[(s.tmp[j]?.getD 0#32).toNat / 2]?.getD 0#8 &&& 8#8) ≠ 0#8) ∧
    (∀ j < slen + 1, (mrk2[(sstk2[j]?.getD 0#32).toNat]?.getD 0#8 &&& 8#8) ≠ 0#8) ∧
    (∀ w < c.mv, (mrk2[w]?.getD 0#8 &&& 8#8) ≠ 0#8 →
      (s.lvl[w]?.getD 0#32).toNat = blvl.toNat ∧
      ∃ idx < s.trail_end, (s.trl[idx]?.getD 0#32).toNat / 2 = w ∧
        (idx ≤ t_lim ∨ ShrinkResolved c F0 s mrk2 idx ∨ idx = idx_uip)) ∧
    trailCount8 s.trl mrk2 (min (t_lim + 1) s.trail_end) ≤ (open_cnt + 1) - 1 ∧
    2 ≤ open_cnt + 1 ∧ open_cnt + 1 ≤ (end_b - beg) + (slen + 1) ∧
    (mrk2[ot.toNat / 2]?.getD 0#8 &&& 8#8) ≠ 0#8 := by
  intro ov mrk2 sstk2
  have hov_nat : ov.toNat = ot.toNat / 2 := bv32_lshr_1 ot
  have hov_lt : ov.toNat < c.mv := by rw [hov_nat]; omega
  have hcb := shrinkBaseInv_core hcore hb
  have hmin2 := plainMinMarkInv_set_bit8 hcb hb.min_inv hov_lt
  change PlainMinMarkInv c F0 (shrinkBlkSt s s.tmp mrk2 mstk1 mclr1 mcl1 mcf1 sstk1) keep0 at hmin2
  have hmin2' : PlainMinMarkInv c F0 (shrinkBlkSt s s.tmp mrk2 mstk1 mclr1 mcl1 mcf1 sstk2) keep0 :=
    ⟨hmin2.mrk_dom, hmin2.clr_cov, hmin2.rem_sound⟩
  have hmono2 : ∀ w < c.mv, (mrk1[w]?.getD 0#8 &&& 2#8) ≠ 0#8 →
      (mrk2[w]?.getD 0#8 &&& 2#8) ≠ 0#8 := fun w _ hw2 => by
    dsimp only [mrk2]
    by_cases hwe : w = ov.toNat
    · subst w
      rw [List.getElem?_set_self (by rw [hb.mrk_len]; exact hov_lt), Option.getD_some,
        bv8_and2_pres_or8]
      exact hw2
    · rwa [List.getElem?_set_ne (Ne.symm hwe)]
  have hmono8 : ∀ w < c.mv, (mrk1[w]?.getD 0#8 &&& 8#8) ≠ 0#8 →
      (mrk2[w]?.getD 0#8 &&& 8#8) ≠ 0#8 := fun w _ hw8 => by
    dsimp only [mrk2]
    by_cases hwe : w = ov.toNat
    · subst w
      rw [List.getElem?_set_self (by rw [hb.mrk_len]; exact hov_lt), Option.getD_some]
      exact bv8_and8_of_or8 _
    · rwa [List.getElem?_set_ne (Ne.symm hwe)]
  have hlov_le : (s.lvl[ot.toNat / 2]?.getD 0#32).toNat ≤ blvl.toNat := by
    have hk_te : k_ot < s.trail_end := Nat.lt_trans hk_lt huip_te
    have htm := hcore.trail_mono k_ot idx_uip (le_of_lt hk_lt) huip_te
    have hv_k : (s.trl[k_ot]?.getD 0#32).toNat / 2 = ot.toNat / 2 := by
      rw [hk_eq]; exact litVar_litNeg ot.toNat
    rw [hv_k, huip_lvl] at htm; exact htm
  have hlov_eq : (s.lvl[ov.toNat]?.getD 0#32).toNat = blvl.toNat := by rw [hov_nat]; omega
  refine ⟨⟨by simp [mrk2, hb.mrk_len], hb.mstk_len, hb.mclr_len, hb.mcl_le,
      by simp [sstk2, hb.sstk_len], by omega, hmin2',
      fun w hw h2 => hmono2 w hw (hb.mono2 w hw h2), ?_, ?_⟩,
    fun j hj1 hj2 => hmono8 _ (hblk_lt j hj1 hj2) (hblk_8 j hj1 hj2), ?_, ?_, ?_, by omega,
    by omega, ?_⟩
  · intro w hw h8w
    by_cases hwe : w = ov.toNat
    · subst hwe; refine ⟨slen, by omega, ?_⟩
      dsimp only [sstk2]
      rw [List.getElem?_set_self (by rw [hb.sstk_len]; omega), Option.getD_some]
    · dsimp only [mrk2] at h8w; rw [List.getElem?_set_ne (Ne.symm hwe)] at h8w
      obtain ⟨j, hj, hje⟩ := hb.bit8_sstk w hw h8w
      refine ⟨j, by omega, ?_⟩
      dsimp only [sstk2]; rwa [List.getElem?_set_ne (by omega)]
  · intro j hj
    dsimp only [sstk2]
    by_cases hjs : j = slen
    · subst hjs; rw [List.getElem?_set_self (by rw [hb.sstk_len]; omega), Option.getD_some]
      exact hov_lt
    · rw [List.getElem?_set_ne (Ne.symm hjs)]; exact hb.sstk_lt j (by omega)
  · intro j hj
    dsimp only [sstk2]
    by_cases hjs : j = slen
    · subst hjs
      rw [List.getElem?_set_self (by rw [hb.sstk_len]; omega), Option.getD_some]
      dsimp only [mrk2]
      rw [List.getElem?_set_self (by rw [hb.mrk_len]; exact hov_lt), Option.getD_some]
      exact bv8_and8_of_or8 _
    · rw [List.getElem?_set_ne (Ne.symm hjs)]
      exact hmono8 _ (hb.sstk_lt j (by omega)) (hsstk_8 j (by omega))
  · intro w hw h8w
    by_cases hwe : w = ov.toNat
    · subst hwe
      refine ⟨hlov_eq, k_ot, Nat.lt_trans hk_lt huip_te, ?_, Or.inl hk_tlim⟩
      rw [hk_eq, hov_nat]; exact litVar_litNeg ot.toNat
    · dsimp only [mrk2] at h8w; rw [List.getElem?_set_ne (Ne.symm hwe)] at h8w
      obtain ⟨hlw, idx, hidx_te, hidx_v, hdisj⟩ := h8_pre w hw h8w
      refine ⟨hlw, idx, hidx_te, hidx_v, ?_⟩
      rcases hdisj with h1 | h2 | h3
      · exact Or.inl h1
      · exact Or.inr (Or.inl (shrinkResolved_mono hcore hmono2 hmono8 h2))
      · exact Or.inr (Or.inr h3)
  · have htl := trailCount8_set_bit8_le (trl := s.trl) (mrk := mrk1)
      (fun i j hi hj heq => hcore.trail_vars_nodup i j (by omega) (by omega) heq)
      ov.toNat (min (t_lim + 1) s.trail_end) (Nat.min_le_right _ _)
    dsimp only [mrk2]; omega
  · rw [← hov_nat]
    dsimp only [mrk2]
    rw [List.getElem?_set_self (by rw [hb.mrk_len]; exact hov_lt), Option.getD_some]
    exact bv8_and8_of_or8 _

theorem shrink_step_pre_mark2 {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    (hcore : PlainCoreInv c F0 s) {blvl : BitVec 32} {beg end_b : Nat}
    {mrk1 mrk2 : List (BitVec 8)} {mstk2 mclr2 sstk1 : List (BitVec 32)}
    {mcl2 open_cnt slen t_lim idx_uip : Nat} {mcf2 : BitVec 64} {keep0 : List Nat}
    (hb : ShrinkBaseInv c F0 s mrk2 mstk2 mclr2 mcl2 mcf2 sstk1 slen keep0)
    (hmono2 : ∀ w < c.mv, (mrk1[w]?.getD 0#8 &&& 2#8) ≠ 0#8 → (mrk2[w]?.getD 0#8 &&& 2#8) ≠ 0#8)
    (hbit8 : ∀ w < c.mv, (mrk2[w]?.getD 0#8 &&& 8#8) = (mrk1[w]?.getD 0#8 &&& 8#8))
    (hblk_lt : ∀ j, beg ≤ j → j < end_b → (s.tmp[j]?.getD 0#32).toNat / 2 < c.mv)
    (hblk_8 : ∀ j, beg ≤ j → j < end_b →
      (mrk1[(s.tmp[j]?.getD 0#32).toNat / 2]?.getD 0#8 &&& 8#8) ≠ 0#8)
    (hsstk_8 : ∀ j < slen, (mrk1[(sstk1[j]?.getD 0#32).toNat]?.getD 0#8 &&& 8#8) ≠ 0#8)
    (h8_pre : ∀ w < c.mv, (mrk1[w]?.getD 0#8 &&& 8#8) ≠ 0#8 →
      (s.lvl[w]?.getD 0#32).toNat = blvl.toNat ∧
      ∃ idx < s.trail_end, (s.trl[idx]?.getD 0#32).toNat / 2 = w ∧
        (idx ≤ t_lim ∨ ShrinkResolved c F0 s mrk1 idx ∨ idx = idx_uip))
    (hcnt_pre : trailCount8 s.trl mrk1 (min (t_lim + 1) s.trail_end) ≤ open_cnt - 1) :
    (∀ j, beg ≤ j → j < end_b →
      (mrk2[(s.tmp[j]?.getD 0#32).toNat / 2]?.getD 0#8 &&& 8#8) ≠ 0#8) ∧
    (∀ j < slen, (mrk2[(sstk1[j]?.getD 0#32).toNat]?.getD 0#8 &&& 8#8) ≠ 0#8) ∧
    (∀ w < c.mv, (mrk2[w]?.getD 0#8 &&& 8#8) ≠ 0#8 →
      (s.lvl[w]?.getD 0#32).toNat = blvl.toNat ∧
      ∃ idx < s.trail_end, (s.trl[idx]?.getD 0#32).toNat / 2 = w ∧
        (idx ≤ t_lim ∨ ShrinkResolved c F0 s mrk2 idx ∨ idx = idx_uip)) ∧
    trailCount8 s.trl mrk2 (min (t_lim + 1) s.trail_end) ≤ open_cnt - 1 := by
  have hm8 : ∀ w < c.mv, (mrk1[w]?.getD 0#8 &&& 8#8) ≠ 0#8 →
      (mrk2[w]?.getD 0#8 &&& 8#8) ≠ 0#8 := fun w hw h => by rwa [hbit8 w hw]
  refine ⟨fun j hj1 hj2 => by rw [hbit8 _ (hblk_lt j hj1 hj2)]; exact hblk_8 j hj1 hj2,
    fun j hj => by rw [hbit8 _ (hb.sstk_lt j hj)]; exact hsstk_8 j hj,
    fun w hw h8 => ?_, ?_⟩
  · rw [hbit8 w hw] at h8
    obtain ⟨hl, idx, hidx_te, hidx_v, hdisj⟩ := h8_pre w hw h8
    refine ⟨hl, idx, hidx_te, hidx_v, ?_⟩
    rcases hdisj with h1 | h2 | h3
    · exact Or.inl h1
    · exact Or.inr (Or.inl (shrinkResolved_mono hcore hmono2 hm8 h2))
    · exact Or.inr (Or.inr h3)
  · have htc := trailCount8_eq_of_bit8_eq (trl := s.trl) (mrk1 := mrk1) (mrk2 := mrk2)
      (n := min (t_lim + 1) s.trail_end) (fun j hj => by
        have hj_te := Nat.lt_of_lt_of_le hj (Nat.min_le_right _ _)
        have := hcore.trail_lits_lt j hj_te; omega) hbit8
    rw [htc]; exact hcnt_pre

theorem shrink_blk_success_finish {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    (hcore : PlainCoreInv c F0 s) {beg end_b : Nat} {blvl : BitVec 32}
    (hb1 : 1 ≤ beg) (hbe : beg < end_b) (hes : end_b ≤ s.tmp_len) (hsc : s.tmp_len ≤ c.mv)
    (hEnt0 : F0.EntailsClause (cnfClause
      (((s.tmp.take s.tmp_len).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat)))
    (hkeep_spec : ∀ k < s.tmp_len, s.tmp[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
      let l := (s.tmp[k]?.getD 0#32).toNat
      l < 2 * c.mv ∧ s.vals[l]?.getD 0#8 = 0xFF#8 ∧ (s.mrk[l / 2]?.getD 0#8 &&& 2#8) ≠ 0#8)
    {mrk1 mrkf : List (BitVec 8)} {mstk1 mclr1 mclrf sstk1 tmp' : List (BitVec 32)}
    {mcl1 mclf slen idx_uip : Nat} {mcf1 mcff : BitVec 64} {uip : BitVec 32}
    (hb : ShrinkBaseInv c F0 s mrk1 mstk1 mclr1 mcl1 mcf1 sstk1 slen
      (((s.tmp.take s.tmp_len).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat))
    (hmrkf_len : mrkf.length = c.mv) (hmclrf_len : mclrf.length = c.mv) (hmclf_le : mclf ≤ c.mv)
    (htmp_len : tmp'.length = c.mv)
    (hdomf : ∀ w < c.mv, (mrkf[w]?.getD 0#8 &&& 0xF1#8) = 0#8)
    (hcovf : mcff = 0#64 → ∀ w < c.mv, (mrkf[w]?.getD 0#8 &&& 6#8) ≠ 0#8 →
      ∃ k < mclf, (mclrf[k]?.getD 0#32).toNat = w)
    (hmono1f : ∀ w < c.mv, (mrk1[w]?.getD 0#8 &&& 2#8) ≠ 0#8 →
      (mrkf[w]?.getD 0#8 &&& 2#8) ≠ 0#8)
    (h8_to_2f : ∀ w < c.mv, (mrk1[w]?.getD 0#8 &&& 8#8) ≠ 0#8 →
      (mrkf[w]?.getD 0#8 &&& 2#8) ≠ 0#8)
    (hnew2_only : ∀ w < c.mv, (mrkf[w]?.getD 0#8 &&& 2#8) ≠ 0#8 →
      (mrk1[w]?.getD 0#8 &&& 2#8) ≠ 0#8 ∨ (mrk1[w]?.getD 0#8 &&& 8#8) ≠ 0#8)
    (huip_te : idx_uip < s.trail_end)
    (huip_eq : (s.trl[idx_uip]?.getD 0#32).toNat = uip.toNat)
    (huip_8 : (mrk1[uip.toNat / 2]?.getD 0#8 &&& 8#8) ≠ 0#8)
    (huip_lvl : (s.lvl[uip.toNat / 2]?.getD 0#32).toNat = blvl.toNat)
    (hres : ∀ w < c.mv, (mrk1[w]?.getD 0#8 &&& 8#8) ≠ 0#8 →
      w = uip.toNat / 2 ∨ ∃ idx < s.trail_end, idx_uip < idx ∧
        (s.trl[idx]?.getD 0#32).toNat / 2 = w ∧ ShrinkResolved c F0 s mrk1 idx)
    (hblk1 : ∀ j, beg ≤ j → j < end_b →
      (mrk1[(s.tmp[j]?.getD 0#32).toNat / 2]?.getD 0#8 &&& 8#8) ≠ 0#8)
    (htmp_out : ∀ k < s.tmp_len, (k < beg ∨ end_b ≤ k) → tmp'[k]? = s.tmp[k]?)
    (htmp_beg : tmp'[beg]? = some (uip ^^^ 1#32))
    (htmp_rest : ∀ k, beg < k → k < end_b → tmp'[k]? = some 0xFFFFFFFF#32) :
    let keep' := ((tmp'.take s.tmp_len).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat
    let sf := shrinkBlkSt s tmp' mrkf mstk1 mclrf mclf mcff sstk1
    PlainMinMarkInv c F0 sf keep' ∧
    F0.EntailsClause (cnfClause keep') ∧
    (∀ k, beg ≤ k → k < end_b → tmp'[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
      (s.lvl[(tmp'[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = blvl.toNat) ∧
    (∀ k < s.tmp_len, tmp'[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
      let l := (tmp'[k]?.getD 0#32).toNat
      l < 2 * c.mv ∧ sf.vals[l]?.getD 0#8 = 0xFF#8 ∧ (mrkf[l / 2]?.getD 0#8 &&& 2#8) ≠ 0#8) := by
  intro keep' sf
  have huip_lt : uip.toNat < 2 * c.mv := by rw [← huip_eq]; exact hcore.trail_lits_lt _ huip_te
  obtain ⟨hnuip_xor, hnuip_lt⟩ := bv32_xor1_toNat_lt huip_lt
  have hmv := c.hmv; unfold dimacsBound at hmv
  have hnuip_ne : (uip ^^^ 1#32) ≠ 0xFFFFFFFF#32 := by
    intro heq
    have := congrArg BitVec.toNat heq
    have hff : (0xFFFFFFFF#32 : BitVec 32).toNat = 4294967295 := rfl
    rw [hff] at this; omega
  have hnuip_mem : (uip ^^^ 1#32).toNat ∈ keep' := by
    rw [mem_filter_map_toNat_take]
    exact ⟨beg, by rw [htmp_len]; omega, uip ^^^ 1#32, htmp_beg, hnuip_ne, rfl⟩
  have hmin_f : PlainMinMarkInv c F0 sf keep' := by
    refine ⟨hdomf, hcovf, fun idx hi h2f => ?_⟩
    dsimp only [sf, shrinkBlkSt]
    have hv_lt : (s.trl[idx]?.getD 0#32).toNat / 2 < c.mv := by
      have := hcore.trail_lits_lt idx hi; omega
    by_cases hv8 : (mrk1[(s.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#8 &&& 8#8) ≠ 0#8
    · rcases hres _ hv_lt hv8 with hvu | ⟨idx2, hi2, _, hv2, hr2⟩
      · have heq_u : (s.trl[idx]?.getD 0#32).toNat / 2 =
            (s.trl[idx_uip]?.getD 0#32).toNat / 2 := by
          rw [huip_eq]; exact hvu
        have hidx : idx = idx_uip := hcore.trail_vars_nodup idx idx_uip hi huip_te heq_u
        subst hidx
        left; rwa [huip_eq, ← hnuip_xor]
      · have hidx : idx = idx2 := hcore.trail_vars_nodup idx idx2 hi hi2 hv2.symm
        subst hidx
        exact Or.inr (by
          simpa [RsnCov, arenaClauseRefs, arenaClauseGarb, arenaClauseLits, arenaHdr,
            arenaClauseSize] using shrinkResolved_to_rem hcore hmono1f h8_to_2f hr2)
    · have h2_1 : (mrk1[(s.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#8 &&& 2#8) ≠ 0#8 :=
        (hnew2_only _ hv_lt h2f).resolve_right hv8
      rcases hb.min_inv.rem_sound idx hi h2_1 with hin | hok
      · rw [mem_filter_map_toNat_take] at hin
        obtain ⟨k, hk, b, hkb, hne, hbn⟩ := hin
        have hkt : k < s.tmp_len := by omega
        have hkbnd : k < beg ∨ end_b ≤ k := by
          by_cases hlt_b : k < beg
          · exact Or.inl hlt_b
          · by_cases hge_e : end_b ≤ k
            · exact Or.inr hge_e
            · exfalso
              have h8k := hblk1 k (by omega) (by omega)
              have htmp_b : (s.tmp[k]?.getD 0#32).toNat / 2 =
                  (s.trl[idx]?.getD 0#32).toNat / 2 := by
                rw [hkb, Option.getD_some, hbn]; dsimp only [shrinkBlkSt]; exact xor1_div2 _
              rw [htmp_b] at h8k
              exact hv8 h8k
        left; rw [mem_filter_map_toNat_take]
        exact ⟨k, by rw [htmp_len]; omega, b, (htmp_out k hkt hkbnd).trans hkb, hne, hbn⟩
      · exact Or.inr (by
          simpa [RsnCov, arenaClauseRefs, arenaClauseGarb, arenaClauseLits, arenaHdr,
            arenaClauseSize] using remSound_lift_mrk2 hcore hmono1f hok)
  have hcore_f : PlainCoreInv c F0 sf :=
    coreInv_shrinkBlk hcore (mcf1 := mcff) htmp_len hmrkf_len hb.mstk_len hmclrf_len hmclf_le
      hb.sstk_len
  have hEnt_f : F0.EntailsClause (cnfClause keep') := by
    refine plainMinMark_entails hcore_f hmin_f hEnt0 fun l hl => ?_
    rw [mem_filter_map_toNat_take] at hl
    obtain ⟨k, hk, b, hkb, hne, rfl⟩ := hl
    have hkt : k < s.tmp_len := by omega
    have hne' : s.tmp[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := by rwa [hkb, Option.getD_some]
    obtain ⟨hlt, hfals, hm2⟩ := hkeep_spec k hkt hne'
    have hlb : (s.tmp[k]?.getD 0#32).toNat = b.toNat := by rw [hkb, Option.getD_some]
    rw [hlb] at hlt hfals hm2
    exact ⟨hlt, hfals, Or.inr (hmono1f _ (by omega) (hb.mono2 _ (by omega) hm2))⟩
  have hlvl_f : ∀ k, beg ≤ k → k < end_b → tmp'[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
      (s.lvl[(tmp'[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = blvl.toNat := by
    intro k hk1 hk2 hne
    by_cases hkb : k = beg
    · subst k
      have hget : tmp'[beg]?.getD 0#32 = uip ^^^ 1#32 := by rw [htmp_beg, Option.getD_some]
      rw [hget, hnuip_xor, xor1_div2 uip.toNat, huip_lvl]
    · exfalso
      rw [htmp_rest k (by omega) hk2, Option.getD_some] at hne
      exact hne rfl
  refine ⟨hmin_f, hEnt_f, hlvl_f, fun k hk hne => ?_⟩
  by_cases hkbnd : k < beg ∨ end_b ≤ k
  · rw [htmp_out k hk hkbnd] at hne ⊢
    obtain ⟨hlt, hfals, hm2⟩ := hkeep_spec k hk hne
    exact ⟨hlt, hfals, hmono1f _ (by omega) (hb.mono2 _ (by omega) hm2)⟩
  · have hk1 : k = beg := by
      by_cases hke : k = beg
      · exact hke
      · exfalso
        rw [htmp_rest k (by omega) (by omega), Option.getD_some] at hne
        exact hne rfl
    subst k
    have hget : tmp'[beg]?.getD 0#32 = uip ^^^ 1#32 := by rw [htmp_beg, Option.getD_some]
    rw [hget]
    have hsf_vals : sf.vals[(uip ^^^ 1#32).toNat]?.getD 0#8 = 0xFF#8 :=
      (hcore.vals_false_iff _ hnuip_lt).mpr
        ⟨idx_uip, huip_te, by rw [huip_eq, hnuip_xor, xor1_xor1]⟩
    have hvar_u : (uip ^^^ 1#32).toNat / 2 = uip.toNat / 2 := by
      rw [hnuip_xor]; exact xor1_div2 uip.toNat
    exact ⟨hnuip_lt, hsf_vals, h8_to_2f _ (by omega) (by rwa [hvar_u])⟩

theorem shrink_after_min_lit_ok {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    (_hcore : PlainCoreInv c F0 s) {mrk1 : List (BitVec 8)} {mstk1 mclr1 sstk1 : List (BitVec 32)}
    {mcl1 slen : Nat} {mcf1 : BitVec 64} {keep0 : List Nat}
    (hb1 : ShrinkBaseInv c F0 s mrk1 mstk1 mclr1 mcl1 mcf1 sstk1 slen keep0)
    {ov : Nat} (hov : ov < c.mv) (hno8 : (mrk1[ov]?.getD 0#8 &&& 8#8) = 0#8)
    {mrk_ml : List (BitVec 8)} {mstk_ml mclr_ml : List (BitVec 32)} {mcl_ml : Nat}
    {mcf_ml : BitVec 64}
    (hlen_ml : (shrinkBlkSt s s.tmp mrk_ml mstk_ml mclr_ml mcl_ml mcf_ml sstk1).LengthsOk c)
    (hmono_ml : ∀ w < c.mv,
      (mrk1[w]?.getD 0#8 &&& 2#8) ≠ 0#8 → (mrk_ml[w]?.getD 0#8 &&& 2#8) ≠ 0#8)
    (hbit8_ml : ∀ w < c.mv, (mrk_ml[w]?.getD 0#8 &&& 8#8) = (mrk1[w]?.getD 0#8 &&& 8#8))
    (hmin_ml : PlainMinMarkInv c F0
      (shrinkBlkSt s s.tmp mrk_ml mstk_ml mclr_ml mcl_ml mcf_ml sstk1) keep0)
    (hmark2 : PlainMinMarkInv c F0
      (plainMinMarkState c
        (shrinkBlkSt s s.tmp mrk_ml mstk_ml mclr_ml mcl_ml mcf_ml sstk1) ov 2#8) keep0) :
    let sb_ml := shrinkBlkSt s s.tmp mrk_ml mstk_ml mclr_ml mcl_ml mcf_ml sstk1
    let sb2 := plainMinMarkStepState c sb_ml ov 2#8
    ShrinkBaseInv c F0 s sb2.mrk mstk_ml sb2.min_clr sb2.min_clr_len sb2.min_clr_full
      sstk1 slen keep0 ∧
    (∀ w < c.mv, (mrk1[w]?.getD 0#8 &&& 2#8) ≠ 0#8 → (sb2.mrk[w]?.getD 0#8 &&& 2#8) ≠ 0#8) ∧
    (∀ w < c.mv, (sb2.mrk[w]?.getD 0#8 &&& 8#8) = (mrk1[w]?.getD 0#8 &&& 8#8)) ∧
    (sb2.mrk[ov]?.getD 0#8 &&& 2#8) ≠ 0#8 := by
  intro sb_ml sb2
  have hln := plainMinMarkStepState_lengths hlen_ml ov 2#8
  have hno8_ml : (sb_ml.mrk[ov]?.getD 0#8 &&& 8#8) = 0#8 := by
    dsimp only [sb_ml, shrinkBlkSt]; rw [hbit8_ml ov hov]; exact hno8
  obtain ⟨hbit8, hmono2⟩ := plainMinMarkStepState_bit8_mono2 hlen_ml hov (Or.inl rfl) hno8_ml
  have hmin2 : PlainMinMarkInv c F0 sb2 keep0 := by
    dsimp only [sb2, plainMinMarkStepState]
    by_cases hs : (sb_ml.mrk[ov]?.getD 0#8 &&& 2#8) ≠ 0#8
    · simp only [eq_true hs, ↓reduceIte]; exact hmin_ml
    · simp only [eq_false hs, ↓reduceIte]; exact hmark2
  dsimp only [sb2] at hln hmin2; rw [shrinkBlkSt_step] at hln hmin2
  have hbit8_all : ∀ w < c.mv, (sb2.mrk[w]?.getD 0#8 &&& 8#8) = (mrk1[w]?.getD 0#8 &&& 8#8) :=
    fun w hw => (hbit8 w hw).trans (hbit8_ml w hw)
  refine ⟨⟨hln.mrk_len, hln.min_stk_len, hln.min_clr_len_arr, hln.min_clr_len_le,
      hb1.sstk_len, hb1.slen_le, hmin2,
      fun w hw h2 => hmono2 w hw (hmono_ml w hw (hb1.mono2 w hw h2)),
      fun w hw h8 => hb1.bit8_sstk w hw (by rwa [← hbit8_all w hw]), hb1.sstk_lt⟩,
    fun w hw h2 => hmono2 w hw (hmono_ml w hw h2), hbit8_all, ?_⟩
  dsimp only [sb2, plainMinMarkStepState, plainMinMarkState, sb_ml, shrinkBlkSt]
  split
  · assumption
  · have hm_len : mrk_ml.length = c.mv := hlen_ml.mrk_len
    dsimp only; rw [List.getElem?_set_self (by rw [hm_len]; exact hov), Option.getD_some]
    exact bv8_and2_of_or2 _

theorem shrink_arena_lits_mem {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    (hcore : PlainCoreInv c F0 s) {cref pos : Nat} (href : cref ∈ arenaClauseRefs s)
    (hp : pos < arenaClauseSize s cref) :
    (s.arena[cref + 3 + pos]?.getD 0#32).toNat ∈ arenaClauseLits s cref := by
  have hwf := hcore.arena.refs_wf cref href
  have hbd : cref + 3 + arenaClauseSize s cref ≤ s.arena.length := by
    have := hwf.2.2.1; have := hwf.2.2.2.1
    have := hcore.lengths.arena_len_le; have := hcore.lengths.arena_len_arr; omega
  rw [mem_arenaClauseLits_iff hbd]
  exact ⟨pos, hp, by rw [List.getElem?_eq_getElem (by omega), Option.getD_some]⟩

theorem shrink_clause_loop_done {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    (hcore : PlainCoreInv c F0 s) {mrk : List (BitVec 8)} {idx : Nat}
    (hi : idx < s.trail_end)
    (hrs : s.rsns[(s.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32)
    (hbin : (s.rsns[(s.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 &&&
      0x80000000#32) = 0#32)
    (hcov : ∀ j < arenaClauseSize s
        (s.rsns[(s.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat,
      let q := (s.arena[(s.rsns[(s.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat +
        3 + j]?.getD 0#32).toNat
      q = (s.trl[idx]?.getD 0#32).toNat ∨ ∃ k < idx, (s.trl[k]?.getD 0#32).toNat = q ^^^ 1 ∧
        ((s.lvl[q / 2]?.getD 0#32).toNat = 0 ∨ (mrk[q / 2]?.getD 0#8 &&& 2#8) ≠ 0#8 ∨
          (mrk[q / 2]?.getD 0#8 &&& 8#8) ≠ 0#8)) :
    RsnCov c F0 s (fun w => (mrk[w]?.getD 0#8 &&& 2#8) ≠ 0#8 ∨
      (mrk[w]?.getD 0#8 &&& 8#8) ≠ 0#8) idx := by
  have hr := hcore.reason_inv idx hi hrs
  dsimp only at hr hbin ⊢
  simp only [RsnCov, hrs, hbin, ne_eq, not_true_eq_false, ↓reduceIte, not_false_eq_true,
    true_and] at hr ⊢
  refine ⟨hr.1, hr.2.1, fun q hq => ?_⟩
  have hwf := hcore.arena.refs_wf _ hr.1
  have hbd : (s.rsns[(s.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat + 3 +
      arenaClauseSize s (s.rsns[(s.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat ≤
      s.arena.length := by
    have := hwf.2.2.1; have := hwf.2.2.2.1
    have := hcore.lengths.arena_len_le; have := hcore.lengths.arena_len_arr; omega
  obtain ⟨j, hj, hjeq⟩ := (mem_arenaClauseLits_iff hbd).mp hq
  have hqj := hcov j hj
  rwa [List.getElem?_eq_getElem (by omega), Option.getD_some, hjeq] at hqj

theorem shrink_poison_spec {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    (hcore : PlainCoreInv c F0 s) {beg end_b : Nat} {keep0 : List Nat}
    (hblk_lt : ∀ j, beg ≤ j → j < end_b → (s.tmp[j]?.getD 0#32).toNat / 2 < c.mv)
    {mrk_p : List (BitVec 8)} {mstk_p mclr_p sstk_p : List (BitVec 32)}
    {mcl_p slen : Nat} {mcf_p : BitVec 64} {R : Mem 64 → Prop} {ov : BitVec 32} {m_p : Mem 64}
    {Q' : Post []} {X' : XPost}
    (hov : ov.toNat < c.mv) (hno8_p : (mrk_p[ov.toNat]?.getD 0#8 &&& 8#8) = 0#8)
    (hb_p : ShrinkBaseInv c F0 s mrk_p mstk_p mclr_p mcl_p mcf_p sstk_p slen keep0)
    (hblk_p : ∀ j, beg ≤ j → j < end_b →
      (mrk_p[(s.tmp[j]?.getD 0#32).toNat / 2]?.getD 0#8 &&& 8#8) ≠ 0#8)
    (hsstk_p : ∀ j < slen, (mrk_p[(sstk_p[j]?.getD 0#32).toNat]?.getD 0#8 &&& 8#8) ≠ 0#8)
    (hm_p : (PlainMem c (shrinkBlkSt s s.tmp mrk_p mstk_p mclr_p mcl_p mcf_p sstk_p) ⋆ R) m_p)
    (hpost : ∀ (mrk' : List (BitVec 8)) (mstk' mclr' sstk' : List (BitVec 32))
        (mcl' : Nat) (mcf' : BitVec 64) (m_q : Mem 64),
      ShrinkBaseInv c F0 s mrk' mstk' mclr' mcl' mcf' sstk' slen keep0 →
      (∀ j, beg ≤ j → j < end_b →
        (mrk'[(s.tmp[j]?.getD 0#32).toNat / 2]?.getD 0#8 &&& 8#8) ≠ 0#8) →
      (∀ j < slen, (mrk'[(sstk'[j]?.getD 0#32).toNat]?.getD 0#8 &&& 8#8) ≠ 0#8) →
      (PlainMem c (shrinkBlkSt s s.tmp mrk' mstk' mclr' mcl' mcf' sstk') ⋆ R) m_q →
      Q' () m_q) :
    plainMinMarkSpec (c.hdr, ov, (4 : BitVec 32).setWidth 8, ()) m_p Q' X' := by
  have hcb_p := shrinkBaseInv_core hcore hb_p
  refine plainMinMarkSpec_step hcb_p.lengths hm_p ov hov ((4 : BitVec 32).setWidth 8)
    fun m_q hm_q => ?_
  have h4_eq : (4 : BitVec 32).setWidth 8 = 4#8 := rfl
  rw [h4_eq] at hm_q
  let sb_q := plainMinMarkStepState c
    (shrinkBlkSt s s.tmp mrk_p mstk_p mclr_p mcl_p mcf_p sstk_p) ov.toNat 4#8
  have hb_q := shrinkBaseInv_poison hcore hb_p hov hno8_p
  obtain ⟨hbit8_p, _⟩ := plainMinMarkStepState_bit8_mono2 hcb_p.lengths hov (Or.inr rfl)
    (by dsimp only [shrinkBlkSt]; exact hno8_p)
  dsimp only [sb_q] at hm_q hb_q hbit8_p
  rw [shrinkBlkSt_step] at hm_q
  exact hpost sb_q.mrk mstk_p sb_q.min_clr sstk_p sb_q.min_clr_len sb_q.min_clr_full m_q hb_q
    (fun j hj1 hj2 => by rw [hbit8_p _ (hblk_lt j hj1 hj2)]; exact hblk_p j hj1 hj2)
    (fun j hj => by rw [hbit8_p _ (hb_p.sstk_lt j hj)]; exact hsstk_p j hj) hm_q

theorem shrink_ml_ok_spec {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    (hcore : PlainCoreInv c F0 s) {blvl : BitVec 32} {beg end_b : Nat}
    {mrk_i mrk_ml : List (BitVec 8)} {mstk1 mclr1 mstk_ml mclr_ml sstk_i : List (BitVec 32)}
    {mcl1 mcl_ml open_i slen_i t_lim idx_uip : Nat} {mcf1 mcf_ml : BitVec 64} {keep0 : List Nat}
    {R : Mem 64 → Prop} {ov : BitVec 32} {m_ml : Mem 64} {Q' : Post []} {X' : XPost}
    (hb_i : ShrinkBaseInv c F0 s mrk_i mstk1 mclr1 mcl1 mcf1 sstk_i slen_i keep0)
    (hov : ov.toNat < c.mv) (hno8_i : (mrk_i[ov.toNat]?.getD 0#8 &&& 8#8) = 0#8)
    (hlen_ml : (shrinkBlkSt s s.tmp mrk_ml mstk_ml mclr_ml mcl_ml mcf_ml sstk_i).LengthsOk c)
    (hmono_ml : ∀ w < c.mv, (mrk_i[w]?.getD 0#8 &&& 2#8) ≠ 0#8 →
      (mrk_ml[w]?.getD 0#8 &&& 2#8) ≠ 0#8)
    (hbit8_ml : ∀ w < c.mv, (mrk_ml[w]?.getD 0#8 &&& 8#8) = (mrk_i[w]?.getD 0#8 &&& 8#8))
    (hmin_ml : PlainMinMarkInv c F0
      (shrinkBlkSt s s.tmp mrk_ml mstk_ml mclr_ml mcl_ml mcf_ml sstk_i) keep0)
    (hmark2 : PlainMinMarkInv c F0
      (plainMinMarkState c
        (shrinkBlkSt s s.tmp mrk_ml mstk_ml mclr_ml mcl_ml mcf_ml sstk_i) ov.toNat 2#8) keep0)
    (hblk_lt : ∀ j, beg ≤ j → j < end_b → (s.tmp[j]?.getD 0#32).toNat / 2 < c.mv)
    (hblk_i : ∀ j, beg ≤ j → j < end_b →
      (mrk_i[(s.tmp[j]?.getD 0#32).toNat / 2]?.getD 0#8 &&& 8#8) ≠ 0#8)
    (hsstk_i : ∀ j < slen_i, (mrk_i[(sstk_i[j]?.getD 0#32).toNat]?.getD 0#8 &&& 8#8) ≠ 0#8)
    (h8_pre : ∀ w < c.mv, (mrk_i[w]?.getD 0#8 &&& 8#8) ≠ 0#8 →
      (s.lvl[w]?.getD 0#32).toNat = blvl.toNat ∧
      ∃ idx < s.trail_end, (s.trl[idx]?.getD 0#32).toNat / 2 = w ∧
        (idx ≤ t_lim ∨ ShrinkResolved c F0 s mrk_i idx ∨ idx = idx_uip))
    (hcnt_pre : trailCount8 s.trl mrk_i (min (t_lim + 1) s.trail_end) ≤ open_i - 1)
    (hm_ml : (PlainMem c
      (shrinkBlkSt s s.tmp mrk_ml mstk_ml mclr_ml mcl_ml mcf_ml sstk_i) ⋆ R) m_ml)
    (hpost : ∀ (mrk' : List (BitVec 8)) (mstk' mclr' sstk' : List (BitVec 32))
        (mcl' : Nat) (mcf' : BitVec 64) (m_2 : Mem 64),
      ShrinkBaseInv c F0 s mrk' mstk' mclr' mcl' mcf' sstk' slen_i keep0 →
      (∀ w < c.mv, (mrk_i[w]?.getD 0#8 &&& 2#8) ≠ 0#8 → (mrk'[w]?.getD 0#8 &&& 2#8) ≠ 0#8) →
      (∀ w < c.mv, (mrk'[w]?.getD 0#8 &&& 8#8) = (mrk_i[w]?.getD 0#8 &&& 8#8)) →
      (mrk'[ov.toNat]?.getD 0#8 &&& 2#8) ≠ 0#8 →
      (∀ j, beg ≤ j → j < end_b →
        (mrk'[(s.tmp[j]?.getD 0#32).toNat / 2]?.getD 0#8 &&& 8#8) ≠ 0#8) →
      (∀ j < slen_i, (mrk'[(sstk'[j]?.getD 0#32).toNat]?.getD 0#8 &&& 8#8) ≠ 0#8) →
      (∀ w < c.mv, (mrk'[w]?.getD 0#8 &&& 8#8) ≠ 0#8 →
        (s.lvl[w]?.getD 0#32).toNat = blvl.toNat ∧
        ∃ idx < s.trail_end, (s.trl[idx]?.getD 0#32).toNat / 2 = w ∧
          (idx ≤ t_lim ∨ ShrinkResolved c F0 s mrk' idx ∨ idx = idx_uip)) →
      trailCount8 s.trl mrk' (min (t_lim + 1) s.trail_end) ≤ open_i - 1 →
      (PlainMem c (shrinkBlkSt s s.tmp mrk' mstk' mclr' mcl' mcf' sstk') ⋆ R) m_2 →
      Q' () m_2) :
    plainMinMarkSpec (c.hdr, ov, (2 : BitVec 32).setWidth 8, ()) m_ml Q' X' := by
  refine plainMinMarkSpec_step hlen_ml hm_ml ov hov ((2 : BitVec 32).setWidth 8)
    fun m_2 hm_2 => ?_
  have h2_eq : (2 : BitVec 32).setWidth 8 = 2#8 := rfl
  rw [h2_eq] at hm_2
  obtain ⟨hb2, hmono2_all, hbit8_all, hov_2⟩ := shrink_after_min_lit_ok hcore hb_i hov hno8_i
    hlen_ml hmono_ml hbit8_ml hmin_ml hmark2
  obtain ⟨hblk2, hsstk2, h8_2, hcnt2⟩ := shrink_step_pre_mark2 hcore hb2 hmono2_all hbit8_all
    hblk_lt hblk_i hsstk_i h8_pre hcnt_pre
  let sb2 := plainMinMarkStepState c
    (shrinkBlkSt s s.tmp mrk_ml mstk_ml mclr_ml mcl_ml mcf_ml sstk_i) ov.toNat 2#8
  rw [shrinkBlkSt_step] at hm_2
  exact hpost sb2.mrk mstk_ml sb2.min_clr sstk_i sb2.min_clr_len sb2.min_clr_full m_2 hb2
    hmono2_all hbit8_all hov_2 hblk2 hsstk2 h8_2 hcnt2 hm_2

theorem shrink_ml_fail_base {c : PlainCfg} {F0 : CNF Nat} {s : PlainState} {beg end_b : Nat}
    {mrk_i mrk_ml : List (BitVec 8)} {mstk1 mclr1 mstk_ml mclr_ml sstk_i : List (BitVec 32)}
    {mcl1 mcl_ml slen_i : Nat} {mcf1 mcf_ml : BitVec 64} {keep0 : List Nat} {ov : Nat}
    (hb_i : ShrinkBaseInv c F0 s mrk_i mstk1 mclr1 mcl1 mcf1 sstk_i slen_i keep0)
    (hov : ov < c.mv) (hno8_i : (mrk_i[ov]?.getD 0#8 &&& 8#8) = 0#8)
    (hlen_ml : (shrinkBlkSt s s.tmp mrk_ml mstk_ml mclr_ml mcl_ml mcf_ml sstk_i).LengthsOk c)
    (hmono_ml : ∀ w < c.mv, (mrk_i[w]?.getD 0#8 &&& 2#8) ≠ 0#8 →
      (mrk_ml[w]?.getD 0#8 &&& 2#8) ≠ 0#8)
    (hbit8_ml : ∀ w < c.mv, (mrk_ml[w]?.getD 0#8 &&& 8#8) = (mrk_i[w]?.getD 0#8 &&& 8#8))
    (hmin_ml : PlainMinMarkInv c F0
      (shrinkBlkSt s s.tmp mrk_ml mstk_ml mclr_ml mcl_ml mcf_ml sstk_i) keep0)
    (hblk_lt : ∀ j, beg ≤ j → j < end_b → (s.tmp[j]?.getD 0#32).toNat / 2 < c.mv)
    (hblk_i : ∀ j, beg ≤ j → j < end_b →
      (mrk_i[(s.tmp[j]?.getD 0#32).toNat / 2]?.getD 0#8 &&& 8#8) ≠ 0#8)
    (hsstk_i : ∀ j < slen_i, (mrk_i[(sstk_i[j]?.getD 0#32).toNat]?.getD 0#8 &&& 8#8) ≠ 0#8) :
    ShrinkBaseInv c F0 s mrk_ml mstk_ml mclr_ml mcl_ml mcf_ml sstk_i slen_i keep0 ∧
    (∀ j, beg ≤ j → j < end_b →
      (mrk_ml[(s.tmp[j]?.getD 0#32).toNat / 2]?.getD 0#8 &&& 8#8) ≠ 0#8) ∧
    (∀ j < slen_i, (mrk_ml[(sstk_i[j]?.getD 0#32).toNat]?.getD 0#8 &&& 8#8) ≠ 0#8) ∧
    (mrk_ml[ov]?.getD 0#8 &&& 8#8) = 0#8 :=
  ⟨⟨hlen_ml.mrk_len, hlen_ml.min_stk_len, hlen_ml.min_clr_len_arr, hlen_ml.min_clr_len_le,
      hb_i.sstk_len, hb_i.slen_le, hmin_ml,
      fun w hw h2 => hmono_ml w hw (hb_i.mono2 w hw h2),
      fun w hw h8 => hb_i.bit8_sstk w hw (by rwa [← hbit8_ml w hw]), hb_i.sstk_lt⟩,
    fun j hj1 hj2 => by rw [hbit8_ml _ (hblk_lt j hj1 hj2)]; exact hblk_i j hj1 hj2,
    fun j hj => by rw [hbit8_ml _ (hb_i.sstk_lt j hj)]; exact hsstk_i j hj,
    by rw [hbit8_ml _ hov]; exact hno8_i⟩

theorem shrink_set_bit8_monos {mv : Nat} {mrk : List (BitVec 8)} {ov : Nat}
    (hmrk_len : mrk.length = mv) (hov : ov < mv) :
    let mrk2 := mrk.set ov (mrk[ov]?.getD 0#8 ||| 8#8)
    (∀ w < mv, (mrk[w]?.getD 0#8 &&& 2#8) ≠ 0#8 → (mrk2[w]?.getD 0#8 &&& 2#8) ≠ 0#8) ∧
    (∀ w < mv, (mrk[w]?.getD 0#8 &&& 8#8) ≠ 0#8 → (mrk2[w]?.getD 0#8 &&& 8#8) ≠ 0#8) := by
  intro mrk2
  refine ⟨fun w _ h => ?_, fun w _ h => ?_⟩
  · dsimp only [mrk2]; by_cases hwe : w = ov
    · subst w; rw [List.getElem?_set_self (by omega), Option.getD_some, bv8_and2_pres_or8]; exact h
    · rwa [List.getElem?_set_ne (Ne.symm hwe)]
  · dsimp only [mrk2]; by_cases hwe : w = ov
    · subst w; rw [List.getElem?_set_self (by omega), Option.getD_some]; exact bv8_and8_of_or8 _
    · rwa [List.getElem?_set_ne (Ne.symm hwe)]

theorem getElem?_getD_of_getElem {α : Type _} (d : α) {xs ys : List α}
    {i j : Nat} {hj : j < ys.length} (hxy : xs = ys) (hij : i = j) :
    xs[i]?.getD d = ys[j]'hj := by
  subst hxy hij; rw [List.getElem?_eq_getElem hj, Option.getD_some]

@[expose] def ShrinkPoisonInv (c : PlainCfg) (F0 : CNF Nat) (s : PlainState)
    (beg end_b : Nat) (keep0 : List Nat) (slen ov : Nat) (R : Mem 64 → Prop) :
    Tup Val [] → Mem 64 → Prop := fun () m' =>
  ∃ (mrk_p : List (BitVec 8)) (mstk_p mclr_p sstk_p : List (BitVec 32))
    (mcl_p : Nat) (mcf_p : BitVec 64),
    ShrinkBaseInv c F0 s mrk_p mstk_p mclr_p mcl_p mcf_p sstk_p slen keep0 ∧
    (∀ j, beg ≤ j → j < end_b →
      (mrk_p[(s.tmp[j]?.getD 0#32).toNat / 2]?.getD 0#8 &&& 8#8) ≠ 0#8) ∧
    (∀ j < slen, (mrk_p[(sstk_p[j]?.getD 0#32).toNat]?.getD 0#8 &&& 8#8) ≠ 0#8) ∧
    (mrk_p[ov]?.getD 0#8 &&& 8#8) = 0#8 ∧
    (PlainMem c (shrinkBlkSt s s.tmp mrk_p mstk_p mclr_p mcl_p mcf_p sstk_p) ⋆ R) m'

@[expose] def ShrinkAfterInv (c : PlainCfg) (F0 : CNF Nat) (s : PlainState)
    (blvl : BitVec 32) (beg end_b : Nat) (keep0 : List Nat) (R : Mem 64 → Prop) :
    Tup Val [i64, i64, .bool, i32, i64] → Mem 64 → Prop :=
  fun (_, slen_a, failed_a, uip_a, _) m_a =>
    ∃ (mrk_a : List (BitVec 8)) (mstk_a mclr_a sstk_a : List (BitVec 32))
      (mcl_a : Nat) (mcf_a : BitVec 64),
      ShrinkBaseInv c F0 s mrk_a mstk_a mclr_a mcl_a mcf_a sstk_a slen_a.toNat keep0 ∧
      (∀ j < slen_a.toNat, (mrk_a[(sstk_a[j]?.getD 0#32).toNat]?.getD 0#8 &&& 8#8) ≠ 0#8) ∧
      (PlainMem c (shrinkBlkSt s s.tmp mrk_a mstk_a mclr_a mcl_a mcf_a sstk_a) ⋆ R) m_a ∧
      (failed_a = false → uip_a ≠ 0xFFFFFFFF#32 →
        ∃ idx_uip < s.trail_end,
          (s.trl[idx_uip]?.getD 0#32).toNat = uip_a.toNat ∧
          (mrk_a[uip_a.toNat / 2]?.getD 0#8 &&& 8#8) ≠ 0#8 ∧
          (s.lvl[uip_a.toNat / 2]?.getD 0#32).toNat = blvl.toNat ∧
          (∀ j, beg ≤ j → j < end_b →
            (mrk_a[(s.tmp[j]?.getD 0#32).toNat / 2]?.getD 0#8 &&& 8#8) ≠ 0#8) ∧
          ∀ w < c.mv, (mrk_a[w]?.getD 0#8 &&& 8#8) ≠ 0#8 →
            w = uip_a.toNat / 2 ∨ ∃ idx < s.trail_end, idx_uip < idx ∧
              (s.trl[idx]?.getD 0#32).toNat / 2 = w ∧ ShrinkResolved c F0 s mrk_a idx)

@[expose] def ShrinkMainInv (c : PlainCfg) (F0 : CNF Nat) (s : PlainState)
    (blvl : BitVec 32) (beg end_b : Nat) (keep0 : List Nat) (R : Mem 64 → Prop) :
    Nat → Tup Val [i64, i64, .bool, i32, i64] → Mem 64 → Prop :=
  fun n (open_c, slen_c, failed_c, _, t_c, ()) m_c =>
    ∃ (mrk_c : List (BitVec 8)) (mstk_c mclr_c sstk_c : List (BitVec 32))
      (mcl_c : Nat) (mcf_c : BitVec 64),
      n = (if failed_c = true then 0 else min t_c.toNat s.trail_end + 1) ∧
      ShrinkBaseInv c F0 s mrk_c mstk_c mclr_c mcl_c mcf_c sstk_c slen_c.toNat keep0 ∧
      (∀ j, beg ≤ j → j < end_b →
        (mrk_c[(s.tmp[j]?.getD 0#32).toNat / 2]?.getD 0#8 &&& 8#8) ≠ 0#8) ∧
      (∀ j < slen_c.toNat, (mrk_c[(sstk_c[j]?.getD 0#32).toNat]?.getD 0#8 &&& 8#8) ≠ 0#8) ∧
      (PlainMem c (shrinkBlkSt s s.tmp mrk_c mstk_c mclr_c mcl_c mcf_c sstk_c) ⋆ R) m_c ∧
      (failed_c = false →
        1 ≤ open_c.toNat ∧ open_c.toNat ≤ (end_b - beg) + slen_c.toNat ∧
        (∀ w < c.mv, (mrk_c[w]?.getD 0#8 &&& 8#8) ≠ 0#8 →
          (s.lvl[w]?.getD 0#32).toNat = blvl.toNat ∧
          ∃ idx < s.trail_end, (s.trl[idx]?.getD 0#32).toNat / 2 = w ∧
            (idx ≤ t_c.toNat ∨ ShrinkResolved c F0 s mrk_c idx)) ∧
        trailCount8 s.trl mrk_c (min (t_c.toNat + 1) s.trail_end) ≤ open_c.toNat)

@[expose] def ShrinkStepInv (c : PlainCfg) (F0 : CNF Nat) (s : PlainState)
    (blvl : BitVec 32) (beg end_b : Nat) (keep0 : List Nat) (t_next t_in : Nat)
    (R : Mem 64 → Prop) : Tup Val [i64, i64, .bool] → Mem 64 → Prop :=
  fun (open', slen', failed', ()) m' =>
    ∃ (mrk' : List (BitVec 8)) (mstk' mclr' sstk' : List (BitVec 32))
      (mcl' : Nat) (mcf' : BitVec 64),
      ShrinkBaseInv c F0 s mrk' mstk' mclr' mcl' mcf' sstk' slen'.toNat keep0 ∧
      (∀ j, beg ≤ j → j < end_b →
        (mrk'[(s.tmp[j]?.getD 0#32).toNat / 2]?.getD 0#8 &&& 8#8) ≠ 0#8) ∧
      (∀ j < slen'.toNat, (mrk'[(sstk'[j]?.getD 0#32).toNat]?.getD 0#8 &&& 8#8) ≠ 0#8) ∧
      (PlainMem c (shrinkBlkSt s s.tmp mrk' mstk' mclr' mcl' mcf' sstk') ⋆ R) m' ∧
      (failed' = false →
        2 ≤ open'.toNat ∧ open'.toNat ≤ (end_b - beg) + slen'.toNat ∧
        (∀ w < c.mv, (mrk'[w]?.getD 0#8 &&& 8#8) ≠ 0#8 →
          (s.lvl[w]?.getD 0#32).toNat = blvl.toNat ∧
          ∃ idx < s.trail_end, (s.trl[idx]?.getD 0#32).toNat / 2 = w ∧
            (idx ≤ t_next ∨ ShrinkResolved c F0 s mrk' idx ∨ idx = t_in)) ∧
        trailCount8 s.trl mrk' (min (t_next + 1) s.trail_end) ≤ open'.toNat - 1 ∧
        RsnCov c F0 s (fun w =>
          (mrk'[w]?.getD 0#8 &&& 2#8) ≠ 0#8 ∨ (mrk'[w]?.getD 0#8 &&& 8#8) ≠ 0#8) t_in)

@[expose] def ShrinkClInv (c : PlainCfg) (F0 : CNF Nat) (s : PlainState)
    (blvl : BitVec 32) (beg end_b : Nat) (keep0 : List Nat) (t_next t_in csz rsn : Nat)
    (R : Mem 64 → Prop) : Nat → Tup Val [i64, i64, i32] → Mem 64 → Prop :=
  fun n (open_i, slen_i, i_bv, ()) m_i =>
    n = csz - i_bv.toNat ∧ i_bv.toNat ≤ csz ∧
    ∃ (mrk_i : List (BitVec 8)) (mstk_i mclr_i sstk_i : List (BitVec 32))
      (mcl_i : Nat) (mcf_i : BitVec 64),
      ShrinkBaseInv c F0 s mrk_i mstk_i mclr_i mcl_i mcf_i sstk_i slen_i.toNat keep0 ∧
      (∀ j, beg ≤ j → j < end_b →
        (mrk_i[(s.tmp[j]?.getD 0#32).toNat / 2]?.getD 0#8 &&& 8#8) ≠ 0#8) ∧
      (∀ j < slen_i.toNat, (mrk_i[(sstk_i[j]?.getD 0#32).toNat]?.getD 0#8 &&& 8#8) ≠ 0#8) ∧
      (PlainMem c (shrinkBlkSt s s.tmp mrk_i mstk_i mclr_i mcl_i mcf_i sstk_i) ⋆ R) m_i ∧
      2 ≤ open_i.toNat ∧ open_i.toNat ≤ (end_b - beg) + slen_i.toNat ∧
      (∀ w < c.mv, (mrk_i[w]?.getD 0#8 &&& 8#8) ≠ 0#8 →
        (s.lvl[w]?.getD 0#32).toNat = blvl.toNat ∧
        ∃ idx < s.trail_end, (s.trl[idx]?.getD 0#32).toNat / 2 = w ∧
          (idx ≤ t_next ∨ ShrinkResolved c F0 s mrk_i idx ∨ idx = t_in)) ∧
      trailCount8 s.trl mrk_i (min (t_next + 1) s.trail_end) ≤ open_i.toNat - 1 ∧
      ∀ k < i_bv.toNat,
        let q := (s.arena[rsn + 3 + k]?.getD 0#32).toNat
        q = (s.trl[t_in]?.getD 0#32).toNat ∨
        ∃ m < t_in, (s.trl[m]?.getD 0#32).toNat = q ^^^ 1 ∧
          ((s.lvl[q / 2]?.getD 0#32).toNat = 0 ∨ (mrk_i[q / 2]?.getD 0#8 &&& 2#8) ≠ 0#8 ∨
            (mrk_i[q / 2]?.getD 0#8 &&& 8#8) ≠ 0#8)

namespace PlainMinTactics

@[scoped bv_c0] theorem bv_c0_tw0 : BitVec.setWidth 8 (0 : BitVec 32) = 0#8 := rfl
@[scoped bv_c0] theorem bv_c0_tw2 : BitVec.setWidth 8 (2 : BitVec 32) = 2#8 := rfl
@[scoped bv_c0] theorem bv_c0_tw4 : BitVec.setWidth 8 (4 : BitVec 32) = 4#8 := rfl
@[scoped bv_c0] theorem bv_c0_tw8 : BitVec.setWidth 8 (8 : BitVec 32) = 8#8 := rfl
@[scoped bv_c0] theorem bv_c0_zext8_32_0 : BitVec.setWidth 32 0#8 = 0#32 := rfl
@[scoped bv_c0] theorem bv_c0_div2_mod64 (x : BitVec 32) : x.toNat / 2 % 2 ^ 64 = x.toNat / 2 :=
  Nat.mod_eq_of_lt (by have := x.isLt; omega)
@[scoped bv_c0] theorem bv_c0_lt_mod64 (x : BitVec 32) : x.toNat % 2 ^ 64 = x.toNat :=
  Nat.mod_eq_of_lt (by have := x.isLt; omega)

scoped macro "ml_ld " lem:term : tactic =>
  `(tactic| (ml_lets; rw [LeanQbe.T.wp]; refine ⟨_, $lem, ?_⟩))

scoped macro "ml_st " m:ident ", " h:ident " := " lem:term : tactic =>
  `(tactic| ((ml_lets; apply LeanQbe.T.wp_store_sep; · exact $lem); intro $m:ident $h:ident))

end PlainMinTactics

section
open scoped PlainMinTactics

/-- C0 expression for clearing bit `8#8` across `sstk_a[0..<slen]`. -/
@[expose] def shrinkBlkClearExpr (pMark pShrinkStk slen : Val i64) : Expr Val Cont [] :=
  let op64 (c : OpCode [i64, i64] [i64]) (a b : Arg Val i64) : Op Val [i64] :=
    Op.mk c (a, b, ())
  .group (sig := [[i64]]) (fun Js => .cons (fun p =>
    .let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var p.fst, .var slen, ())) fun p_12 =>
    .jnz (.var p_12.fst)
      (.let_ (op64 (.mul i64) (.var p.fst) (.imm 4)) fun p_13 =>
       .let_ (op64 (.add i64) (.var pShrinkStk) (.var p_13.fst)) fun p_14 =>
       .load i32 (.var p_14.fst) fun ld =>
       .let_ (Op.mk (.zext 32 64) (.var ld, ())) fun p_15 =>
       .let_ (op64 (.add i64) (.var pMark) (.var p_15.fst)) fun p_16 =>
       .let_ (Op.mk (.zext 32 64) (.var ld, ())) fun p_17 =>
       .let_ (op64 (.add i64) (.var pMark) (.var p_17.fst)) fun p_18 =>
       .load i8 (.var p_18.fst) fun ld =>
       .let_ (Op.mk (.trunc 32 8) (.imm 247, ())) fun p_19 =>
       .let_ (Op.mk (.zext 8 32) (.var ld, ())) fun p_20 =>
       .let_ (Op.mk (.zext 8 32) (.var p_19.fst, ())) fun p_21 =>
       .let_ (Op.mk (.and i32) (.var p_20.fst, .var p_21.fst, ())) fun p_22 =>
       .let_ (Op.mk (.trunc 32 8) (.var p_22.fst, ())) fun p_23 =>
       .store (.var p_23.fst) (.var p_16.fst)
         (.let_ (op64 (.add i64) (.var p.fst) (.imm 1)) fun p =>
          .jump Js.fst (.var p.fst, ())))
      (.ret ())) .nil)
    (fun Js => .jump Js.fst (.imm 0, ()))

theorem shrink_blk_clear_wp {Γ : Env} {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    {keep0 : List Nat} {R : Mem 64 → Prop} {Q : Post []} {X : XPost}
    (hcore : PlainCoreInv c F0 s)
    {mrk_a : List (BitVec 8)} {mstk_a mclr_a sstk_a : List (BitVec 32)}
    {mcl_a : Nat} {mcf_a : BitVec 64} {slen_a : Val i64} {m_a : Mem 64}
    (hb_a : ShrinkBaseInv c F0 s mrk_a mstk_a mclr_a mcl_a mcf_a sstk_a slen_a.toNat keep0)
    (hm_a : (PlainMem c (shrinkBlkSt s s.tmp mrk_a mstk_a mclr_a mcl_a mcf_a sstk_a) ⋆ R) m_a)
    (hpost : ∀ mrk_f m_f,
      let sf := shrinkBlkSt s s.tmp mrk_f mstk_a mclr_a mcl_a mcf_a sstk_a
      PlainCoreInv c F0 sf → PlainMinMarkInv c F0 sf keep0 →
      (∀ v < c.mv, (mrk_f[v]?.getD 0#8 &&& 8#8) = 0#8) →
      (∀ w < c.mv, (s.mrk[w]?.getD 0#8 &&& 2#8) ≠ 0#8 →
        (mrk_f[w]?.getD 0#8 &&& 2#8) ≠ 0#8) →
      (PlainMem c sf ⋆ R) m_f → Q () m_f) :
    wp Γ Q X (shrinkBlkClearExpr c.pMark c.pShrinkStk slen_a) m_a := by
  dsimp only [shrinkBlkClearExpr]
  have hlen0 := hcore.lengths; have hmv := c.hmv; unfold dimacsBound at hmv
  refine wp_loop_group (ts := [i64]) (fun n (i_bv, ()) m_f =>
      ∃ (mrk_f : List (BitVec 8)),
        n = slen_a.toNat - i_bv.toNat ∧ i_bv.toNat ≤ slen_a.toNat ∧ mrk_f.length = c.mv ∧
        PlainMinMarkInv c F0
          (shrinkBlkSt s s.tmp mrk_f mstk_a mclr_a mcl_a mcf_a sstk_a) keep0 ∧
        (∀ w < c.mv, (s.mrk[w]?.getD 0#8 &&& 2#8) ≠ 0#8 → (mrk_f[w]?.getD 0#8 &&& 2#8) ≠ 0#8) ∧
        (∀ w < c.mv, (mrk_f[w]?.getD 0#8 &&& 8#8) ≠ 0#8 →
          ∃ j, i_bv.toNat ≤ j ∧ j < slen_a.toNat ∧ (sstk_a[j]?.getD 0#32).toNat = w) ∧
        (PlainMem c (shrinkBlkSt s s.tmp mrk_f mstk_a mclr_a mcl_a mcf_a sstk_a) ⋆ R) m_f)
    ?_ ?_
  · rintro Jf n ⟨i_bv, ⟨⟩⟩ m_f hJf ⟨mrk_f, rfl, hilen, hmrf_len, hmin_f, hmono_f, h8_f, hm_f⟩
    rw [Blocks.get_here]; ml_lets; ml_jnz; refine ⟨fun hilt => ?_, fun hdone_f => ?_⟩
    · c0_cond hilt
      have hi_sstk : i_bv.toNat < (shrinkBlkSt s s.tmp mrk_f mstk_a mclr_a mcl_a mcf_a
          sstk_a).heur.shrink_stk.length := by
        dsimp only [shrinkBlkSt]; rw [hb_a.sstk_len]; exact lt_of_lt_of_le hilt hb_a.slen_le
      have hi_stk' : i_bv.toNat < sstk_a.length := by
        dsimp only [shrinkBlkSt] at hi_sstk; exact hi_sstk
      ml_ld c0_load_arena_shrink_stk (s := shrinkBlkSt s s.tmp mrk_f mstk_a mclr_a mcl_a
        mcf_a sstk_a) (i := i_bv) hi_sstk hm_f
      let sv := sstk_a[i_bv.toNat]'hi_sstk
      have hsv_lt : sv.toNat < c.mv := by
        have := hb_a.sstk_lt i_bv.toNat hilt
        rwa [List.getElem?_eq_getElem hi_stk', Option.getD_some] at this
      have hsv64 : (sv.setWidth 64).toNat = sv.toNat := bv_c0_zext32_64 sv
      ml_ld c0_load_arena_mrk (s := shrinkBlkSt s s.tmp mrk_f mstk_a mclr_a mcl_a mcf_a
        sstk_a) (i := sv.setWidth 64)
        (by dsimp only [shrinkBlkSt]; rw [hmrf_len, hsv64]; exact hsv_lt) hm_f
      ml_st m_f2, hm_s := c0_store_arena_mrk (s := shrinkBlkSt s s.tmp mrk_f mstk_a mclr_a
        mcl_a mcf_a sstk_a) (i := sv.setWidth 64) _
        (by dsimp only [shrinkBlkSt]; rw [hmrf_len, hsv64]; exact hsv_lt) hm_f
      let mrk_f2 := mrk_f.set sv.toNat (mrk_f[sv.toNat]?.getD 0#8 &&& 0xF7#8)
      have hm_s' := hm_s
      dsimp only [shrinkBlkSt, sv] at hm_s'
      simp only [bv_c0_zext32_64, Arg.val_var, bv8_and247_c0] at hm_s'
      have hm_f2 : (PlainMem c (shrinkBlkSt s s.tmp mrk_f2 mstk_a mclr_a mcl_a mcf_a
          sstk_a) ⋆ R) m_f2 := by
        dsimp only [shrinkBlkSt, mrk_f2, sv]
        rw [List.getElem?_eq_getElem (by rw [hmrf_len]; exact hsv_lt), Option.getD_some]
        exact hm_s'
      have hcb_f := coreInv_shrinkBlk hcore (mcf1 := mcf_a) hlen0.tmp_len_arr hmrf_len
        hb_a.mstk_len hb_a.mclr_len hb_a.mcl_le hb_a.sstk_len
      have hmin_f2 := plainMinMarkInv_clear_bit8 hcb_f hmin_f hsv_lt
      change PlainMinMarkInv c F0 (shrinkBlkSt s s.tmp mrk_f2 mstk_a mclr_a mcl_a mcf_a
        sstk_a) keep0 at hmin_f2
      have hi1 : (i_bv + 1).toNat = i_bv.toNat + 1 :=
        min_bv64_add1 (by have := hb_a.slen_le; omega)
      refine hJf (slen_a.toNat - (i_bv + 1).toNat) (i_bv + 1, ()) _ (by omega)
        ⟨mrk_f2, rfl, by omega, by simp [mrk_f2, hmrf_len], hmin_f2,
          fun w hw h2 => ?_, fun w hw h8 => ?_, hm_f2⟩
      · dsimp only [mrk_f2]; by_cases hwe : w = sv.toNat
        · subst w; rw [List.getElem?_set_self (by omega), Option.getD_some,
            bv8_and2_pres_clear8]
          exact hmono_f _ hw h2
        · rw [List.getElem?_set_ne (Ne.symm hwe)]; exact hmono_f w hw h2
      · rw [hi1]; by_cases hwe : w = sv.toNat
        · subst w; dsimp only [mrk_f2] at h8
          rw [List.getElem?_set_self (by omega), Option.getD_some] at h8
          exact absurd (bv8_and8_clear _) h8
        · dsimp only [mrk_f2] at h8; rw [List.getElem?_set_ne (Ne.symm hwe)] at h8
          obtain ⟨j, hj1, hj2, hjw⟩ := h8_f w hw h8
          refine ⟨j, ?_, hj2, hjw⟩
          by_cases hji : j = i_bv.toNat
          · subst j; exfalso; apply hwe
            rw [← hjw, List.getElem?_eq_getElem (l := sstk_a) hi_stk', Option.getD_some]
            rfl
          · omega
    · ml_lets; rw [wp]; c0_cond hdone_f
      have hno8_f : ∀ w < c.mv, (mrk_f[w]?.getD 0#8 &&& 8#8) = 0#8 := fun w hw => by
        by_cases hnz : (mrk_f[w]?.getD 0#8 &&& 8#8) = 0#8
        · exact hnz
        · obtain ⟨j, hj1, hj2, _⟩ := h8_f w hw hnz; omega
      have hcore_f := coreInv_shrinkBlk hcore (mcf1 := mcf_a) hlen0.tmp_len_arr hmrf_len
        hb_a.mstk_len hb_a.mclr_len hb_a.mcl_le hb_a.sstk_len
      exact hpost mrk_f m_f hcore_f hmin_f hno8_f hmono_f hm_f
  · exact fun Jf hJf => by
      ml_lets
      exact hJf slen_a.toNat (0#64, ()) m_a ⟨mrk_a, rfl, Nat.zero_le _, hb_a.mrk_len,
        hb_a.min_inv, hb_a.mono2, fun w hw h8 =>
          let ⟨j, hj, hjw⟩ := hb_a.bit8_sstk w hw h8; ⟨j, Nat.zero_le _, hj, hjw⟩, hm_a⟩

end

end LeanQbe.T.Examples.Kissat.Plain
