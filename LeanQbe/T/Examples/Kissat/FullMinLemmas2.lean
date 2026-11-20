module

public import LeanQbe.T.Examples.Kissat.FullMinLemmas1
import all Kraken.Mem
import all Kraken.Separation

/-!
# Soundness Proofs for Kissat `D-Full` Minimization & Shrinking (`Stage 4`, Part 2)

Proves parametric `(Γ : Env)` `Func.wp` theorems for:
- `full_sort_tmp_sift` (`full_sort_tmp_sift_wp`)
- `full_sort_tmp` (`full_sort_tmp_wp`)
- `full_shrink_lower` (`full_shrink_lower_wp`)

And provides shared `full_min_mark` step lemmas, `shrinkBlkSt`, `trailCount8`,
purely structural `RsnCov` / `ShrinkResolved`, and `ShrinkBaseInv`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test

open FullArenaTactics FullMinSpecs
open scoped FullMinTactics

/-! ## 1. Pure bitvector, list, and `full_min_mark` step helpers -/

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

theorem fullMinMarkSpec_step {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} {Q' : Post []} {X' : XPost} (hlen : s.LengthsOk c)
    (hm : (FullMem c s ⋆ R) m) (v : BitVec 32) (hv : v.toNat < s.core.cur_vars) (tag : BitVec 8)
    (hpost : ∀ m', (FullMem c (fullMinMarkStepState s v.toNat tag) ⋆ R) m' → Q' () m') :
    fullMinMarkSpec (c.hdr, v, tag, ()) m Q' X' := by
  refine ⟨c, s, R, rfl, hlen, hm, ?_⟩
  dsimp only [fullMinMarkStepState, fullMinMarkStepCore] at hpost ⊢
  by_cases hset : (s.core.mrk[v.toNat]?.getD 0#8 &&& tag) ≠ 0#8
  · have hc : s.core.cur_vars ≤ v.toNat ∨ (s.core.mrk[v.toNat]?.getD 0#8 &&& tag) ≠ 0#8 :=
      Or.inr hset
    simp only [eq_true hc, ↓reduceIte] at hpost ⊢
    exact hpost m hm
  · have hc : ¬ (s.core.cur_vars ≤ v.toNat ∨ (s.core.mrk[v.toNat]?.getD 0#8 &&& tag) ≠ 0#8) :=
      fun h => h.elim (fun hle => by omega) hset
    simp only [eq_false hc, ↓reduceIte] at hpost ⊢
    by_cases hnz : s.core.mrk[v.toNat]?.getD 0#8 ≠ 0#8
    · simp only [eq_true hnz, ↓reduceIte]
      intro m' hm'
      have hp := hpost m'
      have hne0 : ¬ (s.core.mrk[v.toNat]?.getD 0#8 = 0#8 ∧ s.core.min_clr_len < s.core.cur_vars) :=
        fun h => hnz h.1
      have hne1 : ¬ (s.core.mrk[v.toNat]?.getD 0#8 = 0#8 ∧
          ¬ s.core.min_clr_len < s.core.cur_vars) :=
        fun h => hnz h.1
      dsimp only [fullMinMarkCore] at hp
      simp only [eq_false hne0, eq_false hne1, ↓reduceIte] at hp
      exact hp hm'
    · have hz : s.core.mrk[v.toNat]?.getD 0#8 = 0#8 := Decidable.not_not.mp hnz
      simp only [eq_false hnz, ↓reduceIte]
      by_cases hcl : s.core.min_clr_len < s.core.cur_vars
      · simp only [eq_true hcl, ↓reduceIte]
        intro m' hm'
        have hp := hpost m'
        have he1 : s.core.mrk[v.toNat]?.getD 0#8 = 0#8 ∧ s.core.min_clr_len < s.core.cur_vars :=
          ⟨hz, hcl⟩
        have he2 : ¬ (s.core.mrk[v.toNat]?.getD 0#8 = 0#8 ∧
            ¬ s.core.min_clr_len < s.core.cur_vars) := fun h => h.2 hcl
        dsimp only [fullMinMarkCore] at hp
        simp only [eq_true he1, eq_false he2, ↓reduceIte, bv_ofNat_toNat_eq v] at hp
        exact hp hm'
      · simp only [eq_false hcl, ↓reduceIte]
        intro m' hm'
        have hp := hpost m'
        have he1 : ¬ (s.core.mrk[v.toNat]?.getD 0#8 = 0#8 ∧
            s.core.min_clr_len < s.core.cur_vars) := fun h => hcl h.2
        have he2 : s.core.mrk[v.toNat]?.getD 0#8 = 0#8 ∧ ¬ s.core.min_clr_len < s.core.cur_vars :=
          ⟨hz, hcl⟩
        dsimp only [fullMinMarkCore] at hp
        simp only [eq_false he1, eq_true he2, ↓reduceIte] at hp
        exact hp hm'

theorem fullMinMarkStepState_lengths {c : FullCfg} {s : FullState}
    (hlen : s.LengthsOk c) (v : Nat) (tag : BitVec 8) :
    (fullMinMarkStepState s v tag).LengthsOk c := by
  dsimp only [fullMinMarkStepState, fullMinMarkStepCore]
  split
  · exact hlen
  · exact ⟨fullMinMarkCore_lengths hlen.core_ok tag, hlen.scratch_ok⟩

theorem fullMinMarkStepState_mrk_above {s : FullState} {v : Nat}
    (hv : v < s.core.cur_vars) (tag : BitVec 8) :
    ∀ w, s.core.cur_vars ≤ w → (fullMinMarkStepState s v tag).core.mrk[w]? = s.core.mrk[w]? := by
  intro w hw
  dsimp only [fullMinMarkStepState, fullMinMarkStepCore]
  split
  · rfl
  · exact fullMinMarkCore_mrk_above hv w hw

theorem fullMinMarkStepState_bit8_mono2 {c : FullCfg} {s : FullState}
    (hlen : s.LengthsOk c) {v : Nat} (hv : v < s.core.cur_vars) {tag : BitVec 8}
    (htag : tag = 2#8 ∨ tag = 4#8) (hno8 : (s.core.mrk[v]?.getD 0#8 &&& 8#8) = 0#8) :
    (∀ w < s.core.cur_vars, ((fullMinMarkStepState s v tag).core.mrk[w]?.getD 0#8 &&& 8#8) =
      (s.core.mrk[w]?.getD 0#8 &&& 8#8)) ∧
    (∀ w < s.core.cur_vars, (s.core.mrk[w]?.getD 0#8 &&& 2#8) ≠ 0#8 →
      ((fullMinMarkStepState s v tag).core.mrk[w]?.getD 0#8 &&& 2#8) ≠ 0#8) := by
  have hv_mrk : v < s.core.mrk.length := by
    rw [hlen.core_ok.mrk_len]; have := hlen.core_ok.cur_vars_le; omega
  dsimp only [fullMinMarkStepState, fullMinMarkStepCore, fullMinMarkCore]; split
  · exact ⟨fun _ _ => rfl, fun _ _ h => h⟩
  · refine ⟨fun w _ => ?_, fun w _ h2 => ?_⟩
    · dsimp only; by_cases hwe : w = v
      · subst w; rw [List.getElem?_set_self hv_mrk, Option.getD_some]
        rcases htag with rfl | rfl
        · exact (bv8_and8_pres_or2 hno8).trans hno8.symm
        · exact (bv8_and8_pres_or4 hno8).trans hno8.symm
      · rw [List.getElem?_set_ne (Ne.symm hwe)]
    · dsimp only; by_cases hwe : w = v
      · subst w; rw [List.getElem?_set_self hv_mrk, Option.getD_some]
        rcases htag with rfl | rfl
        · exact bv8_and2_of_or2 _
        · rwa [bv8_and2_pres_or4]
      · rwa [List.getElem?_set_ne (Ne.symm hwe)]

theorem fullMinMarkStepState_dom_clr {c : FullCfg} {s : FullState}
    (hlen : s.LengthsOk c)
    (hdom : ∀ w < s.core.cur_vars, (s.core.mrk[w]?.getD 0#8 &&& 0xF1#8) = 0#8)
    (hcov : s.core.min_clr_full = 0#64 →
      ∀ w < s.core.cur_vars, (s.core.mrk[w]?.getD 0#8 &&& 6#8) ≠ 0#8 →
        ∃ k < s.core.min_clr_len, (s.core.min_clr[k]?.getD 0#32).toNat = w)
    {v : Nat} (hv : v < s.core.cur_vars) {tag : BitVec 8} (htag : tag = 2#8 ∨ tag = 4#8)
    (hno8 : (s.core.mrk[v]?.getD 0#8 &&& 8#8) = 0#8) :
    let s' := fullMinMarkStepState s v tag
    (∀ w < s.core.cur_vars, (s'.core.mrk[w]?.getD 0#8 &&& 0xF1#8) = 0#8) ∧
    (s'.core.min_clr_full = 0#64 →
      ∀ w < s.core.cur_vars, (s'.core.mrk[w]?.getD 0#8 &&& 6#8) ≠ 0#8 →
        ∃ k < s'.core.min_clr_len, (s'.core.min_clr[k]?.getD 0#32).toNat = w) := by
  have hcv := hlen.core_ok.cur_vars_le
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hv_mrk : v < s.core.mrk.length := by rw [hlen.core_ok.mrk_len]; omega
  dsimp only [fullMinMarkStepState, fullMinMarkStepCore]
  split
  · exact ⟨hdom, hcov⟩
  · refine ⟨fun w hw => ?_, ?_⟩
    · dsimp only [fullMinMarkCore]
      by_cases hwe : w = v
      · subst hwe
        rw [List.getElem?_set_self hv_mrk, Option.getD_some]
        rcases htag with rfl | rfl
        · exact bv8_and_dom_or2 (hdom w hw)
        · exact bv8_and_dom_or4 (hdom w hw)
      · rw [List.getElem?_set_ne (Ne.symm hwe)]; exact hdom w hw
    · intro hmcf w hw hnz
      dsimp only [fullMinMarkCore] at hmcf hnz ⊢
      by_cases hcur0 : s.core.mrk[v]?.getD 0#8 = 0#8
      · by_cases hlt : s.core.min_clr_len < s.core.cur_vars
        · simp only [hcur0, hlt, and_self, not_true_eq_false, and_false,
            ↓reduceIte] at hmcf hnz ⊢
          by_cases hweq : w = v
          · subst w
            refine ⟨s.core.min_clr_len, by omega, ?_⟩
            rw [List.getElem?_set_self (by rw [hlen.core_ok.min_clr_len_arr]; omega),
              Option.getD_some, bv32_ofNat_toNat (by omega)]
          · have hnz' : (s.core.mrk[w]?.getD 0#8 &&& 6#8) ≠ 0#8 := by
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

theorem fullMinMarkInv_step_poison {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    {keep : List Nat} (hcore : FullCoreInv c F0 s) (hmin : FullMinMarkInv s.core keep)
    {v : Nat} (hv : v < s.core.cur_vars) (hno8 : (s.core.mrk[v]?.getD 0#8 &&& 8#8) = 0#8) :
    FullMinMarkInv (fullMinMarkStepState s v 4#8).core keep := by
  dsimp only [fullMinMarkStepState, fullMinMarkStepCore]
  split
  · exact hmin
  · exact fullMinMarkInv_poison hcore hmin hv hno8

theorem fullMinMarkInv_step_keep {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    {keep : List Nat} (hcore : FullCoreInv c F0 s) (hmin : FullMinMarkInv s.core keep)
    {l : Nat} (hl : l < 2 * s.core.cur_vars) (hkeep : l ∈ keep)
    (hfals : s.core.vals[l]?.getD 0#8 = 0xFF#8)
    (hno8 : (s.core.mrk[l / 2]?.getD 0#8 &&& 8#8) = 0#8) :
    FullMinMarkInv (fullMinMarkStepState s (l / 2) 2#8).core keep := by
  dsimp only [fullMinMarkStepState, fullMinMarkStepCore]
  split
  · exact hmin
  · exact fullMinMarkInv_mark_keep hcore hmin hl hkeep hfals hno8

theorem minLitState_step {s : FullState} {mrk1 : List (BitVec 8)}
    {mstk1 mclr1 : List (BitVec 32)} {mcl1 : Nat} {mcf1 : BitVec 64} (v : Nat) (tag : BitVec 8) :
    let st := minLitState s mrk1 mstk1 mclr1 mcl1 mcf1
    let st' := fullMinMarkStepState st v tag
    st' = minLitState s st'.core.mrk mstk1 st'.core.min_clr st'.core.min_clr_len
      st'.core.min_clr_full := by
  intro st st'
  dsimp only [st', fullMinMarkStepState, fullMinMarkStepCore, fullMinMarkCore, st, minLitState]
  split
  · rfl
  · rfl

/-! ## 2. `full_sort_tmp_sift_wp` and `full_sort_tmp_wp` -/

private theorem tmpLe_refl (lvl tpos : List (BitVec 32)) (a : BitVec 32) :
    tmpLe lvl tpos a a := by
  simp only [tmpLe, tmpLt]; omega

private theorem tmpLt_mono_le {lvl tpos : List (BitVec 32)} {a b : BitVec 32}
    (h : tmpLt lvl tpos a b) : tmpLe lvl tpos a b := by
  simp only [tmpLe, tmpLt] at h ⊢; omega

private theorem tmpLe_trans {lvl tpos : List (BitVec 32)} {a b c : BitVec 32}
    (h1 : tmpLe lvl tpos a b) (h2 : tmpLe lvl tpos b c) : tmpLe lvl tpos a c := by
  simp only [tmpLe, tmpLt] at h1 h2 ⊢; omega

private theorem tmpLe_of_decide_false {lvl tpos : List (BitVec 32)} {a b : BitVec 32}
    (h : decide ((tmpKey lvl tpos a).1 < (tmpKey lvl tpos b).1 ∨
      ((tmpKey lvl tpos a).1 = (tmpKey lvl tpos b).1 ∧
       (tmpKey lvl tpos a).2 < (tmpKey lvl tpos b).2)) = false) :
    tmpLe lvl tpos b a := by
  simp only [decide_eq_false_iff_not] at h; exact h

private theorem tmpLt_of_decide_true {lvl tpos : List (BitVec 32)} {a b : BitVec 32}
    (h : decide ((tmpKey lvl tpos a).1 < (tmpKey lvl tpos b).1 ∨
      ((tmpKey lvl tpos a).1 = (tmpKey lvl tpos b).1 ∧
       (tmpKey lvl tpos a).2 < (tmpKey lvl tpos b).2)) = true) :
    tmpLt lvl tpos a b := by
  simp only [decide_eq_true_eq] at h; exact h

private theorem tmpLe_lvl {lvl tpos : List (BitVec 32)} {a b : BitVec 32}
    (h : tmpLe lvl tpos a b) :
    (lvl[a.toNat / 2]?.getD 0#32).toNat ≤ (lvl[b.toNat / 2]?.getD 0#32).toNat := by
  simp only [tmpLe, tmpLt, tmpKey] at h; omega

private theorem sortSliceEq_refl (a : List (BitVec 32)) (hi : Nat) : SortSliceEq a a hi :=
  ⟨fun j h1 h2 => ⟨j, h1, h2, rfl⟩, fun i h1 h2 => ⟨i, h1, h2, rfl⟩⟩

private theorem sortSliceEq_trans {a b c : List (BitVec 32)} {hi : Nat}
    (h1 : SortSliceEq a b hi) (h2 : SortSliceEq b c hi) : SortSliceEq a c hi := by
  refine ⟨fun j hj1 hj2 => ?_, fun i hi1 hi2 => ?_⟩
  · obtain ⟨k, hk1, hk2, hjk⟩ := h1.1 j hj1 hj2
    obtain ⟨i, hi1, hi2, hki⟩ := h2.1 k hk1 hk2
    exact ⟨i, hi1, hi2, hjk.trans hki⟩
  · obtain ⟨k, hk1, hk2, hik⟩ := h2.2 i hi1 hi2
    obtain ⟨j, hj1, hj2, hkj⟩ := h1.2 k hk1 hk2
    exact ⟨j, hj1, hj2, hik.trans hkj⟩

private theorem sortSliceEq_widen {a b : List (BitVec 32)} {lo hi : Nat}
    (hlo : lo ≤ hi) (hsub : SortSliceEq a b lo)
    (hout : ∀ k, lo ≤ k → a[k]? = b[k]?) : SortSliceEq a b hi := by
  refine ⟨fun j hj1 hj2 => ?_, fun i hi1 hi2 => ?_⟩
  · by_cases h : j < lo
    · obtain ⟨i, hi1, hi2, heq⟩ := hsub.1 j hj1 h
      exact ⟨i, hi1, by omega, heq⟩
    · exact ⟨j, hj1, hj2, hout j (by omega)⟩
  · by_cases h : i < lo
    · obtain ⟨j, hj1, hj2, heq⟩ := hsub.2 i hi1 h
      exact ⟨j, hj1, by omega, heq⟩
    · exact ⟨i, hi1, hi2, (hout i (by omega)).symm⟩

private def sortSwap (xs : List (BitVec 32)) (u v : Nat)
    (hu : u < xs.length) (hv : v < xs.length) : List (BitVec 32) :=
  (xs.set u xs[v]).set v xs[u]

private theorem sortSwap_length {xs : List (BitVec 32)} {u v : Nat}
    {hu : u < xs.length} {hv : v < xs.length} :
    (sortSwap xs u v hu hv).length = xs.length := by
  simp [sortSwap]

private theorem sortSwap_getElem? {xs : List (BitVec 32)} {u v k : Nat}
    {hu : u < xs.length} {hv : v < xs.length} :
    (sortSwap xs u v hu hv)[k]? =
      if k = v then some xs[u] else if k = u then some xs[v] else xs[k]? := by
  dsimp only [sortSwap]
  by_cases hkv : k = v
  · subst hkv; simp [hv]
  · simp only [hkv, ↓reduceIte, List.getElem?_set_ne (Ne.symm hkv)]
    by_cases hku : k = u
    · subst hku; simp [hu]
    · simp [hku, List.getElem?_set_ne (Ne.symm hku)]

private theorem sortSwap_sliceEq {xs : List (BitVec 32)} {hi u v : Nat}
    {hu : u < xs.length} {hv : v < xs.length}
    (hu1 : 1 ≤ u) (hu2 : u < hi) (hv1 : 1 ≤ v) (hv2 : v < hi) :
    SortSliceEq (sortSwap xs u v hu hv) xs hi := by
  refine ⟨fun j hj1 hj2 => ?_, fun i hi1 hi2 => ?_⟩
  · rw [sortSwap_getElem?]
    by_cases h1 : j = v
    · subst h1; exact ⟨u, hu1, hu2, by simp [List.getElem?_eq_getElem hu]⟩
    · by_cases h2 : j = u
      · subst h2; exact ⟨v, hv1, hv2, by simp [h1, List.getElem?_eq_getElem hv]⟩
      · exact ⟨j, hj1, hj2, by simp [h1, h2]⟩
  · by_cases h1 : i = u
    · subst h1
      refine ⟨v, hv1, hv2, ?_⟩
      rw [sortSwap_getElem?, List.getElem?_eq_getElem hu]; simp
    · by_cases h2 : i = v
      · subst h2
        refine ⟨u, hu1, hu2, ?_⟩
        rw [sortSwap_getElem?, List.getElem?_eq_getElem hv]; simp [Ne.symm h1]
      · refine ⟨i, hi1, hi2, ?_⟩
        rw [sortSwap_getElem?]; simp [h1, h2]

private theorem heap_root_max {lvl tpos tmp : List (BitVec 32)} {lim : Nat}
    (hh : IsMaxHeapFrom lvl tpos tmp 0 lim) :
    ∀ k, k < lim → tmpLe lvl tpos (tmp[1 + k]?.getD 0#32) (tmp[1]?.getD 0#32) := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro hk
    rcases k with _ | k'
    · simpa using tmpLe_refl lvl tpos (tmp[1]?.getD 0#32)
    · let p := k' / 2
      have hpr := ih p (by omega) (by omega)
      have hnode := hh p (Nat.zero_le _) (by omega)
      have hchild : tmpLe lvl tpos (tmp[1 + (k' + 1)]?.getD 0#32) (tmp[1 + p]?.getD 0#32) := by
        rcases Nat.mod_two_eq_zero_or_one k' with hm | hm
        · have heq : k' + 1 = 2 * p + 1 := by omega
          simpa [heq] using hnode.1 (by omega)
        · have heq : k' + 1 = 2 * p + 2 := by omega
          simpa [heq] using hnode.2 (by omega)
      exact tmpLe_trans hchild hpr

private def SiftInv (lvl tpos tmp_init tmp : List (BitVec 32))
    (r0 lim r : Nat) : Prop :=
  tmp.length = tmp_init.length ∧
  (∀ k, (k = 0 ∨ 1 + lim ≤ k) → tmp[k]? = tmp_init[k]?) ∧
  SortSliceEq tmp tmp_init (1 + lim) ∧
  (∀ k, 1 ≤ k → k < 1 + lim →
    (tmp[k]?.getD 0#32).toNat / 2 < lvl.length ∧
    (tmp[k]?.getD 0#32).toNat / 2 < tpos.length) ∧
  r < lim ∧ r0 ≤ r ∧
  (∀ i, r0 ≤ i → i < lim → i ≠ r → IsHeapAt lvl tpos tmp i lim) ∧
  (r0 < r → 0 < r ∧
    (2 * r + 1 < lim →
      tmpLe lvl tpos (tmp[1 + (2 * r + 1)]?.getD 0#32)
        (tmp[1 + (r - 1) / 2]?.getD 0#32)) ∧
    (2 * r + 2 < lim →
      tmpLe lvl tpos (tmp[1 + (2 * r + 2)]?.getD 0#32)
        (tmp[1 + (r - 1) / 2]?.getD 0#32)))

private theorem siftInv_done_of_oob {lvl tpos tmp_init tmp : List (BitVec 32)} {r0 lim r : Nat}
    (hi : SiftInv lvl tpos tmp_init tmp r0 lim r) (hoob : lim ≤ 2 * r + 1) :
    IsMaxHeapFrom lvl tpos tmp r0 lim := by
  intro i hi1 hi2
  by_cases hir : i = r
  · subst i; exact ⟨fun h => by omega, fun h => by omega⟩
  · exact hi.2.2.2.2.2.2.1 i hi1 hi2 hir

private theorem siftInv_done_of_ge {lvl tpos tmp_init tmp : List (BitVec 32)} {r0 lim r ch : Nat}
    (hi : SiftInv lvl tpos tmp_init tmp r0 lim r) (_hc : ch < lim)
    (hch_eq : ch = 2 * r + 1 ∨ ch = 2 * r + 2)
    (hge : tmpLe lvl tpos (tmp[1 + ch]?.getD 0#32) (tmp[1 + r]?.getD 0#32))
    (hmax : 2 * r + 2 < lim →
      tmpLe lvl tpos (tmp[1 + (2 * r + 1)]?.getD 0#32) (tmp[1 + ch]?.getD 0#32) ∧
      tmpLe lvl tpos (tmp[1 + (2 * r + 2)]?.getD 0#32) (tmp[1 + ch]?.getD 0#32)) :
    IsMaxHeapFrom lvl tpos tmp r0 lim := by
  intro i hi1 hi2
  by_cases hir : i = r
  · subst i
    constructor
    · intro _
      by_cases h2 : 2 * r + 2 < lim
      · exact tmpLe_trans (hmax h2).1 hge
      · rcases hch_eq with rfl | rfl
        · exact hge
        · omega
    · intro h2; exact tmpLe_trans (hmax h2).2 hge
  · exact hi.2.2.2.2.2.2.1 i hi1 hi2 hir

private theorem siftInv_swap {lvl tpos tmp_init tmp : List (BitVec 32)} {r0 lim r ch : Nat}
    (hi : SiftInv lvl tpos tmp_init tmp r0 lim r) (hlim_len : 1 + lim ≤ tmp_init.length)
    (hc1 : 2 * r + 1 ≤ ch) (hc2 : ch ≤ 2 * r + 2) (hch_lim : ch < lim)
    (hlt : tmpLt lvl tpos (tmp[1 + r]?.getD 0#32) (tmp[1 + ch]?.getD 0#32))
    (hmax : 2 * r + 2 < lim →
      tmpLe lvl tpos (tmp[1 + (2 * r + 1)]?.getD 0#32) (tmp[1 + ch]?.getD 0#32) ∧
      tmpLe lvl tpos (tmp[1 + (2 * r + 2)]?.getD 0#32) (tmp[1 + ch]?.getD 0#32)) :
    let hlen := hi.1
    let hu : 1 + r < tmp.length := by have := hi.2.2.2.2.1; omega
    let hv : 1 + ch < tmp.length := by omega
    SiftInv lvl tpos tmp_init (sortSwap tmp (1 + r) (1 + ch) hu hv) r0 lim ch := by
  intro hlen hu hv
  let tmp' := sortSwap tmp (1 + r) (1 + ch) hu hv
  have hrc_ne : r ≠ ch := by omega
  have hget (idx : Nat) :
      tmp'[idx]?.getD 0#32 =
        if idx = 1 + ch then tmp[1 + r]?.getD 0#32
        else if idx = 1 + r then tmp[1 + ch]?.getD 0#32
        else tmp[idx]?.getD 0#32 := by
    dsimp only [tmp']; rw [sortSwap_getElem?]
    by_cases h1 : idx = 1 + ch
    · simp only [h1, ↓reduceIte, List.getElem?_eq_getElem hu, Option.getD_some]
    · by_cases h2 : idx = 1 + r
      · rw [h2]; simp only [show 1 + r ≠ 1 + ch by omega, ↓reduceIte,
          List.getElem?_eq_getElem hv, Option.getD_some]
      · simp only [h1, h2, ↓reduceIte]
  have hpar_ch : (ch - 1) / 2 = r := by omega
  rcases hi with ⟨_, hout, hseq, hbd, hr_lim, hr0_r, hheap, hgp⟩
  refine ⟨sortSwap_length.trans hlen, ?_, ?_, ?_, hch_lim, by omega, ?_, ?_⟩
  · intro k hk; rw [sortSwap_getElem?]
    have h1 : k ≠ 1 + ch := by rcases hk with rfl | h <;> omega
    have h2 : k ≠ 1 + r := by rcases hk with rfl | h <;> omega
    simp only [h1, h2, ↓reduceIte]; exact hout k hk
  · exact sortSliceEq_trans (sortSwap_sliceEq (by omega) (by omega) (by omega) (by omega)) hseq
  · intro k hk1 hk2; rw [sortSwap_getElem?]
    by_cases h1 : k = 1 + ch
    · simp only [h1, ↓reduceIte]; have := hbd (1 + r) (by omega) (by omega)
      rwa [List.getElem?_eq_getElem hu, Option.getD_some] at this
    · by_cases h2 : k = 1 + r
      · rw [h2]; simp only [show 1 + r ≠ 1 + ch by omega, ↓reduceIte]
        have := hbd (1 + ch) (by omega) (by omega)
        rwa [List.getElem?_eq_getElem hv, Option.getD_some] at this
      · simp only [h1, h2, ↓reduceIte]; exact hbd k hk1 hk2
  · intro i hi1 hi2 hine
    by_cases hir : i = r
    · subst i
      have hrootv : tmp'[1 + r]?.getD 0#32 = tmp[1 + ch]?.getD 0#32 := by
        rw [hget]; simp only [show 1 + r ≠ 1 + ch by omega, ↓reduceIte]
      constructor
      · intro _
        rw [hrootv]
        by_cases hc : 2 * r + 1 = ch
        · rw [hc, hget]; simp only [↓reduceIte]; exact tmpLt_mono_le hlt
        · have h2 : 2 * r + 2 < lim := by omega
          rw [hget]
          simp only [show 1 + (2 * r + 1) ≠ 1 + ch by omega,
            show 1 + (2 * r + 1) ≠ 1 + r by omega, ↓reduceIte]
          exact (hmax h2).1
      · intro h2
        rw [hrootv]
        by_cases hc : 2 * r + 2 = ch
        · rw [hc, hget]; simp only [↓reduceIte]; exact tmpLt_mono_le hlt
        · rw [hget]
          simp only [show 1 + (2 * r + 2) ≠ 1 + ch by omega,
            show 1 + (2 * r + 2) ≠ 1 + r by omega, ↓reduceIte]
          exact (hmax h2).2
    · have hiv : tmp'[1 + i]?.getD 0#32 = tmp[1 + i]?.getD 0#32 := by
        rw [hget]
        simp only [show 1 + i ≠ 1 + ch by omega, show 1 + i ≠ 1 + r by omega, ↓reduceIte]
      have hheap_i := hheap i hi1 hi2 hir
      constructor
      · intro h1
        rw [hiv]
        by_cases hcr : 2 * i + 1 = r
        · have hgt : r0 < r := by omega
          rw [hcr, hget]; simp only [show 1 + r ≠ 1 + ch by omega, ↓reduceIte]
          have hgp' := hgp hgt
          rcases Nat.lt_or_eq_of_le hc1 with _ | hc1_eq
          · have hch2 : ch = 2 * r + 2 := by omega
            rw [hch2]; simpa [show (r - 1) / 2 = i by omega] using hgp'.2.2 (by omega)
          · rw [← hc1_eq]; simpa [show (r - 1) / 2 = i by omega] using hgp'.2.1 (by omega)
        · rw [hget]
          simp only [show 1 + (2 * i + 1) ≠ 1 + ch by omega,
            show 1 + (2 * i + 1) ≠ 1 + r by omega, ↓reduceIte]
          exact hheap_i.1 h1
      · intro h2
        rw [hiv]
        by_cases hcr : 2 * i + 2 = r
        · have hgt : r0 < r := by omega
          rw [hcr, hget]; simp only [show 1 + r ≠ 1 + ch by omega, ↓reduceIte]
          have hgp' := hgp hgt
          rcases Nat.lt_or_eq_of_le hc1 with _ | hc1_eq
          · have hch2 : ch = 2 * r + 2 := by omega
            rw [hch2]; simpa [show (r - 1) / 2 = i by omega] using hgp'.2.2 (by omega)
          · rw [← hc1_eq]; simpa [show (r - 1) / 2 = i by omega] using hgp'.2.1 (by omega)
        · rw [hget]
          simp only [show 1 + (2 * i + 2) ≠ 1 + ch by omega,
            show 1 + (2 * i + 2) ≠ 1 + r by omega, ↓reduceIte]
          exact hheap_i.2 h2
  · intro _; refine ⟨by omega, ?_, ?_⟩
    · intro h1
      have hheap_c := hheap ch (by omega) hch_lim (by omega)
      rw [hget, hget, hpar_ch]
      simp only [show 1 + (2 * ch + 1) ≠ 1 + ch by omega,
        show 1 + (2 * ch + 1) ≠ 1 + r by omega, show 1 + r ≠ 1 + ch by omega, ↓reduceIte]
      exact hheap_c.1 h1
    · intro h2
      have hheap_c := hheap ch (by omega) hch_lim (by omega)
      rw [hget, hget, hpar_ch]
      simp only [show 1 + (2 * ch + 2) ≠ 1 + ch by omega,
        show 1 + (2 * ch + 2) ≠ 1 + r by omega, show 1 + r ≠ 1 + ch by omega, ↓reduceIte]
      exact hheap_c.2 h2

private theorem arr_load_i32_bv {a i : BitVec 64} {xs : List (BitVec 32)} {F : Mem 64 → Prop}
    {m : Mem 64} (hi : i.toNat < xs.length) (h : (array (t := i32) a xs ⋆ F) m) :
    loadVal m i32 (a + i * 4) = some xs[i.toNat] := by
  rw [show a + i * 4 = a + BitVec.ofNat 64 (4 * i.toNat) from by
    rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_mul_ofNat]]
  exact loadVal_array (t := i32) (by decide) hi h

private theorem arr_store_i32_bv {a i : BitVec 64} {xs : List (BitVec 32)} {F : Mem 64 → Prop}
    {m : Mem 64} (v : BitVec 32) (hi : i.toNat < xs.length)
    (h : (array (t := i32) a xs ⋆ F) m) :
    storeOk m i32 (a + i * 4) ∧
      (array (t := i32) a (xs.set i.toNat v) ⋆ F) (storeMem m i32 (a + i * 4) v) := by
  rw [show a + i * 4 = a + BitVec.ofNat 64 (4 * i.toNat) from by
    rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_mul_ofNat]]
  exact store_array (t := i32) v (by decide) hi h

theorem full_sort_tmp_sift_wp (Γ : Env)
    (hTl : ∀ args m Q X, fullTmpLessSpec args m Q X →
      Γ "full_tmp_less" [i64, i64, i32, i32] [.bool] args m Q X) :
    ∀ args m Q X, fullSortTmpSiftSpec args m Q X →
      Func.wp Γ full_sort_tmp_sift_body args m Q X := by
  rintro ⟨tmp_ptr, lvl_ptr, tpos_ptr, start, lim, ⟨⟩⟩ m0 Q X
    ⟨tmp_init, lvl, tpos, R, hst_lt, hlim_len, hlim_60, hbd0, hheap0, hm0, hQ⟩
  unfold Func.wp full_sort_tmp_sift_body; dsimp only [full_sort_tmp_sift_body]
  let BrkP : Tup Val [i64] → Mem 64 → Prop := fun (_, ()) m' =>
    ∃ tmp', tmp'.length = tmp_init.length ∧
      (∀ k, (k = 0 ∨ 1 + lim.toNat ≤ k) → tmp'[k]? = tmp_init[k]?) ∧
      SortSliceEq tmp' tmp_init (1 + lim.toNat) ∧
      IsMaxHeapFrom lvl tpos tmp' start.toNat lim.toNat ∧
      (array (t := i32) tmp_ptr tmp' ⋆ array (t := i32) lvl_ptr lvl ⋆
        array (t := i32) tpos_ptr tpos ⋆ R) m'
  refine wp_join_group (ts := [i64]) BrkP ?_ ?_
  · rintro _ ⟨_, ⟨⟩⟩ m' ⟨tmp', hlen', hout', hseq', hh', hm'⟩
    rw [Blocks.get_here, wp]
    exact hQ tmp' m' hlen' hout' hseq' hh' hm'
  · rintro Jbrk hJbrk
    let SiftLp : Nat → Tup Val [i64] → Mem 64 → Prop := fun dec (r, ()) m1 =>
      dec = lim.toNat - r.toNat ∧
      ∃ tmp1, SiftInv lvl tpos tmp_init tmp1 start.toNat lim.toNat r.toNat ∧
        (array (t := i32) tmp_ptr tmp1 ⋆ array (t := i32) lvl_ptr lvl ⋆
          array (t := i32) tpos_ptr tpos ⋆ R) m1
    refine wp_loop_group (ts := [i64]) SiftLp ?_ ?_
    · rintro J dec ⟨r, ⟨⟩⟩ m1 hJ ⟨rfl, tmp1, hsi, hm1⟩
      rw [Blocks.get_here, wp]; refine ⟨fun _ => ?_, fun h => by cases h⟩
      ml_lets
      have hsi_cp := hsi
      rcases hsi with ⟨htl, hout, hseq, hbd, hr_lim, hr0_r, hheap, hgp⟩
      have hc1_nat : ((r <<< ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64)) + 1).toNat =
          2 * r.toNat + 1 := bv64_shl1_add1_toNat (x := r) (by omega)
      ml_jnz; refine ⟨fun hoob => ?_, fun hch_in => ?_⟩
      · change BitVec.ule lim ((r <<< _) + 1) = true at hoob
        rw [BitVec.ule, decide_eq_true_eq, hc1_nat] at hoob
        exact hJbrk (r, ()) m1 ⟨tmp1, htl, hout, hseq, siftInv_done_of_oob hsi_cp hoob, hm1⟩
      · have hc1_lt : 2 * r.toNat + 1 < lim.toNat := by
          change BitVec.ule lim ((r <<< _) + 1) = false at hch_in
          rw [BitVec.ule, decide_eq_false_iff_not, hc1_nat] at hch_in; omega
        let c1 : BitVec 64 := r <<< ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64) + 1
        have hc1_eq : c1.toNat = 2 * r.toNat + 1 := hc1_nat
        let ChJoin : Tup Val [i64] → Mem 64 → Prop := fun (ch, ()) m2 =>
          m2 = m1 ∧ 2 * r.toNat + 1 ≤ ch.toNat ∧ ch.toNat ≤ 2 * r.toNat + 2 ∧
          ch.toNat < lim.toNat ∧
          (2 * r.toNat + 2 < lim.toNat →
            tmpLe lvl tpos (tmp1[1 + (2 * r.toNat + 1)]?.getD 0#32)
              (tmp1[1 + ch.toNat]?.getD 0#32) ∧
            tmpLe lvl tpos (tmp1[1 + (2 * r.toNat + 2)]?.getD 0#32)
              (tmp1[1 + ch.toNat]?.getD 0#32))
        refine wp_join_group (ts := [i64]) ChJoin ?_ ?_
        · rintro _ ⟨ch, ⟨⟩⟩ m2 ⟨rfl, hc_lo, hc_hi, hch_lim, hch_max⟩
          rw [Blocks.get_here]; ml_lets
          have hc1_bv : ((1 : BitVec 64) + r).toNat = 1 + r.toNat := by
            have h1 : (1 : BitVec 64).toNat = 1 := rfl
            rw [BitVec.toNat_add, h1, Nat.mod_eq_of_lt (by omega)]
          have hc2_bv : ((1 : BitVec 64) + ch).toNat = 1 + ch.toNat := by
            have h1 : (1 : BitVec 64).toNat = 1 := rfl
            rw [BitVec.toNat_add, h1, Nat.mod_eq_of_lt (by omega)]
          have hi_r : ((1 : BitVec 64) + r).toNat < tmp1.length := by rw [hc1_bv, htl]; omega
          have hi_c : ((1 : BitVec 64) + ch).toNat < tmp1.length := by rw [hc2_bv, htl]; omega
          have hm_tmp : (array (t := i32) tmp_ptr tmp1 ⋆
              (array (t := i32) lvl_ptr lvl ⋆ array (t := i32) tpos_ptr tpos ⋆ R)) m2 :=
            sep_ac hm1
          ml_ld arr_load_i32_bv hi_r hm_tmp
          ml_ld arr_load_i32_bv hi_c hm_tmp
          ml_lets
          let vr := tmp1[((1 : BitVec 64) + r).toNat]'hi_r
          let vc := tmp1[((1 : BitVec 64) + ch).toNat]'hi_c
          have hvr_eq : vr = tmp1[1 + r.toNat]'(by rw [htl]; omega) := by simp only [vr, hc1_bv]
          have hvc_eq : vc = tmp1[1 + ch.toNat]'(by rw [htl]; omega) := by simp only [vc, hc2_bv]
          have hvr_bd : vr.toNat / 2 < lvl.length ∧ vr.toNat / 2 < tpos.length := by
            have := hbd (1 + r.toNat) (by omega) (by omega)
            rw [List.getElem?_eq_getElem (by rw [htl]; omega), Option.getD_some] at this
            rwa [hvr_eq]
          have hvc_bd : vc.toNat / 2 < lvl.length ∧ vc.toNat / 2 < tpos.length := by
            have := hbd (1 + ch.toNat) (by omega) (by omega)
            rw [List.getElem?_eq_getElem (by rw [htl]; omega), Option.getD_some] at this
            rwa [hvc_eq]
          apply wp_call_of_spec; apply hTl
          refine ⟨lvl, tpos, array (t := i32) tmp_ptr tmp1 ⋆ R,
            hvr_bd.1, hvc_bd.1, hvr_bd.2, hvc_bd.2, by dsimp only [Arg.val]; exact sep_ac hm1, ?_⟩
          · dsimp only; ml_lets; ml_jnz; refine ⟨fun hless => ?_, fun hge => ?_⟩
            · have hlt' : tmpLt lvl tpos
                  (tmp1[1 + r.toNat]?.getD 0#32) (tmp1[1 + ch.toNat]?.getD 0#32) := by
                rw [List.getElem?_eq_getElem (by rw [htl]; omega),
                  List.getElem?_eq_getElem (by rw [htl]; omega), Option.getD_some,
                  Option.getD_some, ← hvr_eq, ← hvc_eq]
                exact tmpLt_of_decide_true hless
              ml_ld arr_load_i32_bv hi_r hm_tmp
              ml_ld arr_load_i32_bv hi_c hm_tmp
              ml_lets; rw [wp]
              obtain ⟨hok1, hm2⟩ := arr_store_i32_bv (i := 1 + r)
                (tmp1[((1 : BitVec 64) + ch).toNat]'hi_c) hi_r hm_tmp
              refine ⟨hok1, ?_⟩
              ml_lets; rw [wp]
              let tmp1b := tmp1.set ((1 : BitVec 64) + r).toNat
                (tmp1[((1 : BitVec 64) + ch).toNat]'hi_c)
              have hi_c' : ((1 : BitVec 64) + ch).toNat < tmp1b.length := by
                simpa [tmp1b] using hi_c
              obtain ⟨hok2, hm3⟩ := arr_store_i32_bv (i := 1 + ch)
                (tmp1[((1 : BitVec 64) + r).toNat]'hi_r) hi_c' hm2
              refine ⟨hok2, ?_⟩
              let tmp2 := sortSwap tmp1 (1 + r.toNat) (1 + ch.toNat)
                (by rw [htl]; omega) (by rw [htl]; omega)
              have hm3' : (array (t := i32) tmp_ptr tmp2 ⋆ array (t := i32) lvl_ptr lvl ⋆
                  array (t := i32) tpos_ptr tpos ⋆ R)
                  (storeMem (storeMem m2 i32 (tmp_ptr + ((1 : BitVec 64) + r) * 4)
                    (tmp1[((1 : BitVec 64) + ch).toNat]'hi_c)) i32
                    (tmp_ptr + ((1 : BitVec 64) + ch) * 4)
                    (tmp1[((1 : BitVec 64) + r).toNat]'hi_r)) := by
                have h3 : (array (t := i32) tmp_ptr tmp2 ⋆ (array (t := i32) lvl_ptr lvl ⋆
                    array (t := i32) tpos_ptr tpos ⋆ R))
                    (storeMem (storeMem m2 i32 (tmp_ptr + ((1 : BitVec 64) + r) * 4)
                      (tmp1[((1 : BitVec 64) + ch).toNat]'hi_c)) i32
                      (tmp_ptr + ((1 : BitVec 64) + ch) * 4)
                      (tmp1[((1 : BitVec 64) + r).toNat]'hi_r)) := by
                  simpa only [tmp2, tmp1b, sortSwap, hc1_bv, hc2_bv, Nat.add_comm 1] using hm3
                exact sep_ac h3
              exact hJ (lim.toNat - ch.toNat) (ch, ()) _ (by omega)
                ⟨rfl, tmp2, siftInv_swap hsi_cp hlim_len hc_lo hc_hi hch_lim hlt' hch_max, hm3'⟩
            · have hge' : tmpLe lvl tpos
                  (tmp1[1 + ch.toNat]?.getD 0#32) (tmp1[1 + r.toNat]?.getD 0#32) := by
                rw [List.getElem?_eq_getElem (by rw [htl]; omega),
                  List.getElem?_eq_getElem (by rw [htl]; omega), Option.getD_some,
                  Option.getD_some, ← hvr_eq, ← hvc_eq]
                exact tmpLe_of_decide_false hge
              have hch_eq' : ch.toNat = 2 * r.toNat + 1 ∨ ch.toNat = 2 * r.toNat + 2 := by omega
              exact hJbrk (r, ()) m2 ⟨tmp1, htl, hout, hseq,
                siftInv_done_of_ge hsi_cp hch_lim hch_eq' hge' hch_max, hm1⟩
        · rintro J2 hJ2; ml_lets
          have hc2_bv : (c1 + 1).toNat = 2 * r.toNat + 2 := by
            have h1 : (1 : BitVec 64).toNat = 1 := rfl
            rw [BitVec.toNat_add, hc1_eq, h1, Nat.mod_eq_of_lt (by omega)]
          ml_jnz; refine ⟨fun hc2_lt => ?_, fun hc2_ge => ?_⟩
          · change (c1 + 1).ult lim = true at hc2_lt
            rw [BitVec.ult, decide_eq_true_eq, hc2_bv] at hc2_lt
            have h1c1 : ((1 : BitVec 64) + c1).toNat = 1 + (2 * r.toNat + 1) := by
              have h1 : (1 : BitVec 64).toNat = 1 := rfl
              rw [BitVec.toNat_add, hc1_eq, h1, Nat.mod_eq_of_lt (by omega)]
            have h2c1 : ((2 : BitVec 64) + c1).toNat = 1 + (2 * r.toNat + 2) := by
              have h2 : (2 : BitVec 64).toNat = 2 := rfl
              rw [BitVec.toNat_add, hc1_eq, h2, Nat.mod_eq_of_lt (by omega)]; omega
            have hi1 : ((1 : BitVec 64) + c1).toNat < tmp1.length := by rw [h1c1, htl]; omega
            have hi2 : ((2 : BitVec 64) + c1).toNat < tmp1.length := by rw [h2c1, htl]; omega
            have hm_tmp : (array (t := i32) tmp_ptr tmp1 ⋆
                (array (t := i32) lvl_ptr lvl ⋆ array (t := i32) tpos_ptr tpos ⋆ R)) m1 :=
              sep_ac hm1
            ml_ld arr_load_i32_bv hi1 hm_tmp
            ml_ld arr_load_i32_bv hi2 hm_tmp
            ml_lets
            let v1 := tmp1[((1 : BitVec 64) + c1).toNat]'hi1
            let v2 := tmp1[((2 : BitVec 64) + c1).toNat]'hi2
            have hv1_eq : v1 = tmp1[1 + (2 * r.toNat + 1)]'(by rw [htl]; omega) := by
              simp only [v1, h1c1]
            have hv2_eq : v2 = tmp1[1 + (2 * r.toNat + 2)]'(by rw [htl]; omega) := by
              simp only [v2, h2c1]
            have hv1_bd : v1.toNat / 2 < lvl.length ∧ v1.toNat / 2 < tpos.length := by
              have := hbd (1 + (2 * r.toNat + 1)) (by omega) (by omega)
              rw [List.getElem?_eq_getElem (by rw [htl]; omega), Option.getD_some] at this
              rwa [hv1_eq]
            have hv2_bd : v2.toNat / 2 < lvl.length ∧ v2.toNat / 2 < tpos.length := by
              have := hbd (1 + (2 * r.toNat + 2)) (by omega) (by omega)
              rw [List.getElem?_eq_getElem (by rw [htl]; omega), Option.getD_some] at this
              rwa [hv2_eq]
            apply wp_call_of_spec; apply hTl
            refine ⟨lvl, tpos, array (t := i32) tmp_ptr tmp1 ⋆ R,
              hv1_bd.1, hv2_bd.1, hv1_bd.2, hv2_bd.2, by dsimp only [Arg.val]; exact sep_ac hm1, ?_⟩
            · dsimp only; ml_lets; ml_jnz; refine ⟨fun hless => ?_, fun hge => ?_⟩
              · have hlt' : tmpLt lvl tpos
                    (tmp1[1 + (2 * r.toNat + 1)]?.getD 0#32)
                    (tmp1[1 + (2 * r.toNat + 2)]?.getD 0#32) := by
                  rw [List.getElem?_eq_getElem (by rw [htl]; omega),
                    List.getElem?_eq_getElem (by rw [htl]; omega), Option.getD_some,
                    Option.getD_some, ← hv1_eq, ← hv2_eq]
                  exact tmpLt_of_decide_true hless
                ml_lets; apply hJ2; change ChJoin (c1 + 1, ()) m1
                refine ⟨rfl, by rw [hc2_bv]; omega, by rw [hc2_bv]; omega,
                  by rw [hc2_bv]; exact hc2_lt, fun _ => ?_⟩
                rw [hc2_bv]; exact ⟨tmpLt_mono_le hlt', tmpLe_refl _ _ _⟩
              · have hge' : tmpLe lvl tpos
                    (tmp1[1 + (2 * r.toNat + 2)]?.getD 0#32)
                    (tmp1[1 + (2 * r.toNat + 1)]?.getD 0#32) := by
                  rw [List.getElem?_eq_getElem (by rw [htl]; omega),
                    List.getElem?_eq_getElem (by rw [htl]; omega), Option.getD_some,
                    Option.getD_some, ← hv1_eq, ← hv2_eq]
                  exact tmpLe_of_decide_false hge
                ml_lets; apply hJ2; change ChJoin (c1, ()) m1
                refine ⟨rfl, by rw [hc1_eq]; omega, by rw [hc1_eq]; omega,
                  by rw [hc1_eq]; exact hc1_lt, fun _ => ?_⟩
                rw [hc1_eq]; exact ⟨tmpLe_refl _ _ _, hge'⟩
          · change (c1 + 1).ult lim = false at hc2_ge
            rw [BitVec.ult, decide_eq_false_iff_not, hc2_bv] at hc2_ge
            ml_lets; apply hJ2; change ChJoin (c1, ()) m1
            exact ⟨rfl, by rw [hc1_eq]; omega, by rw [hc1_eq]; omega,
              by rw [hc1_eq]; exact hc1_lt, fun h => by omega⟩
    · intro J hJ; wp_unfold
      have hsift0 : SiftInv lvl tpos tmp_init tmp_init start.toNat lim.toNat start.toNat :=
        ⟨rfl, fun _ _ => rfl, sortSliceEq_refl _ _, hbd0, hst_lt, le_refl _,
          fun i hi1 hi2 hine => hheap0 i (by omega) hi2,
          fun hlt => absurd hlt (Nat.lt_irrefl _)⟩
      exact hJ (lim.toNat - start.toNat) (start, ()) m0 ⟨rfl, tmp_init, hsift0, hm0⟩

private theorem fullMem_focus_sort {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem c s ⋆ R) m) :
    ∃ R_sift : Mem 64 → Prop,
      (array (t := i32) c.pTmp s.core.tmp ⋆ array (t := i32) c.pLevel s.core.lvl ⋆
        array (t := i32) c.pTrailPos s.core.trail_pos ⋆ R_sift) m ∧
      ∀ tmp' m',
        (array (t := i32) c.pTmp tmp' ⋆ array (t := i32) c.pLevel s.core.lvl ⋆
          array (t := i32) c.pTrailPos s.core.trail_pos ⋆ R_sift) m' →
        (FullMem c { s with core := { s.core with tmp := tmp' } } ⋆ R) m' := by
  have hm1 := hm
  rw [fullMem_eq_coreU32A] at hm1
  unfold FullCoreU32A at hm1
  refine ⟨array (t := i32) c.pFlags s.core.flags ⋆ array (t := i32) c.pReason s.core.rsns ⋆
      array (t := i32) c.pTrail s.core.trl ⋆ array (t := i32) c.pMinClr s.core.min_clr ⋆
      (FullCoreByteArrs c s.core ⋆ FullCoreU32B c s.core ⋆
        FullCoreDynArrs c s.core ⋆ fullCoreOuter c s) ⋆ R,
    sep_ac hm1, fun tmp' m' hm' => ?_⟩
  rw [fullMem_eq_coreU32A]
  unfold FullCoreU32A; dsimp only
  have h1 : FullCoreByteArrs c { s.core with tmp := tmp' } = FullCoreByteArrs c s.core := rfl
  have h2 : FullCoreU32B c { s.core with tmp := tmp' } = FullCoreU32B c s.core := rfl
  have h3 : FullCoreDynArrs c { s.core with tmp := tmp' } = FullCoreDynArrs c s.core := rfl
  have h4 : fullCoreOuter c { s with core := { s.core with tmp := tmp' } } =
      fullCoreOuter c s := rfl
  rw [h1, h2, h3, h4]
  exact sep_ac hm'

theorem full_sort_tmp_wp (Γ : Env)
    (hSift : ∀ args m Q X, fullSortTmpSiftSpec args m Q X →
      Γ "full_sort_tmp_sift" [i64, i64, i64, i64, i64] [] args m Q X) :
    ∀ args m Q X, fullSortTmpSpec args m Q X →
      Func.wp Γ full_sort_tmp_body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, htle, hbd0, hm, hQ⟩
  unfold Func.wp full_sort_tmp_body; dsimp only [full_sort_tmp_body]
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have htmp_len := hlen.core_ok.tmp_len_arr
  have hlvl_len := hlen.core_ok.lvl_len
  have htpos_len := hlen.core_ok.trail_pos_len
  ml_ld load_full_tmp_len hm
  ml_lets; ml_jnz; refine ⟨fun hle2 => ?_, fun hgt2 => ?_⟩
  · c0_cond hle2
    have htl2 : s.core.tmp_len ≤ 2 := by bv_omega
    ml_lets; rw [wp]
    refine hQ s.core.tmp m htmp_len (fun _ => rfl)
      (fun j h1 h2 => ⟨j, h1, h2, rfl⟩) (fun i h1 h2 => ⟨i, h1, h2, rfl⟩)
      (fun i j hi hij hj => by
        have hij' : i = j := by omega
        subst hij'; exact le_refl _)
      hm
  · have htl2 : 2 < s.core.tmp_len := by
      change (BitVec.ofNat 64 s.core.tmp_len).ule 2 = false at hgt2
      rw [BitVec.ule, decide_eq_false_iff_not] at hgt2
      have : (2 : BitVec 64).toNat = 2 := rfl
      rw [this, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hgt2; omega
    let n : BitVec 64 := BitVec.ofNat 64 s.core.tmp_len - 1
    have hn_eq : n.toNat = s.core.tmp_len - 1 := by
      dsimp only [n]
      have h1 : (1 : BitVec 64).toNat = 1 := rfl
      rw [BitVec.toNat_sub_of_le (by bv_omega), h1, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega)]
    ml_ld load_full_tmp_lits_ptr hm
    ml_ld load_full_level_ptr hm
    ml_ld load_full_trail_pos_ptr hm
    ml_lets
    let Loop1Inv : Nat → Tup Val [i64] → Mem 64 → Prop := fun dec (start, ()) m1 =>
      dec = start.toNat ∧ start.toNat ≤ n.toNat / 2 ∧
      ∃ tmp1, tmp1.length = c.max_vars ∧
        (0 < s.core.tmp_len → tmp1[0]? = s.core.tmp[0]?) ∧
        SortSliceEq tmp1 s.core.tmp s.core.tmp_len ∧
        (∀ k, 1 ≤ k → k < s.core.tmp_len → (tmp1[k]?.getD 0#32).toNat < 2 * c.max_vars) ∧
        IsMaxHeapFrom s.core.lvl s.core.trail_pos tmp1 start.toNat n.toNat ∧
        (FullMem c { s with core := { s.core with tmp := tmp1 } } ⋆ R) m1
    refine wp_loop_group (ts := [i64]) Loop1Inv ?_ ?_
    · rintro J1 dec ⟨start, ⟨⟩⟩ m1 hJ1 ⟨rfl, hst_le, tmp1, htl1, h01, hseq1, hbd1, hh1, hm1⟩
      rw [Blocks.get_here]; ml_lets
      ml_jnz; refine ⟨fun hst_pos => ?_, fun hst0 => ?_⟩
      · have hst_gt0 : 0 < start.toNat := by c0_cond hst_pos; bv_omega
        have hst_m1 : (start - 1).toNat = start.toNat - 1 := by
          have h1 : (1 : BitVec 64).toNat = 1 := rfl
          rw [BitVec.toNat_sub_of_le (by bv_omega), h1]
        ml_lets
        obtain ⟨R_sift, hm1_sift, hm1_unfocus⟩ := fullMem_focus_sort hm1
        apply wp_call_of_spec; apply hSift
        dsimp only [fullSortTmpSiftSpec, vals, Arg.val]
        have hn_eq' : (BitVec.ofNat 64 s.core.tmp_len - 1).toNat = s.core.tmp_len - 1 := hn_eq
        refine ⟨tmp1, s.core.lvl, s.core.trail_pos, R_sift, by omega, by omega, by omega,
          fun k hk1 hk2 => by
            have := hbd1 k hk1 (by omega); exact ⟨by omega, by omega⟩,
          by rw [hst_m1, Nat.sub_add_cancel hst_gt0]; exact hh1, hm1_sift, ?_⟩
        intro tmp2 m2 htl2' hout2 hseq2 hh2 hm2_sift
        have hm2 := hm1_unfocus tmp2 m2 hm2_sift
        have h02 : 0 < s.core.tmp_len → tmp2[0]? = s.core.tmp[0]? := fun hp =>
          (hout2 0 (Or.inl rfl)).trans (h01 hp)
        have hseq2' : SortSliceEq tmp2 s.core.tmp s.core.tmp_len := by
          rw [show 1 + n.toNat = s.core.tmp_len by omega] at hseq2
          exact sortSliceEq_trans hseq2 hseq1
        have hbd2 : ∀ k, 1 ≤ k → k < s.core.tmp_len →
            (tmp2[k]?.getD 0#32).toNat < 2 * c.max_vars := fun k hk1 hk2 => by
          obtain ⟨j, hj1, hj2, hkj⟩ := hseq2'.1 k hk1 hk2
          rw [hkj]; exact hbd0 j hj1 hj2
        exact hJ1 (start - 1).toNat (start - 1, ()) m2 (by rw [hst_m1]; omega)
          ⟨rfl, by rw [hst_m1]; omega, tmp2, htl2'.trans htl1, h02, hseq2', hbd2, hh2, hm2⟩
      · have hst_eq0 : start.toNat = 0 := by
          change (0 : BitVec 64).ult start = false at hst0
          rw [BitVec.ult, decide_eq_false_iff_not] at hst0; bv_omega
        rw [hst_eq0] at hh1
        ml_lets
        let e0 : BitVec 64 := n - 1
        have he0 : e0.toNat = n.toNat - 1 := by
          dsimp only [e0]; have h1 : (1 : BitVec 64).toNat = 1 := rfl
          rw [BitVec.toNat_sub_of_le (by bv_omega), h1]
        let Loop2Inv : Nat → Tup Val [i64] → Mem 64 → Prop := fun dec2 (e, ()) m2 =>
          dec2 = e.toNat ∧ e.toNat < n.toNat ∧
          ∃ tmp2, tmp2.length = c.max_vars ∧
            (0 < s.core.tmp_len → tmp2[0]? = s.core.tmp[0]?) ∧
            SortSliceEq tmp2 s.core.tmp s.core.tmp_len ∧
            (∀ k, 1 ≤ k → k < s.core.tmp_len → (tmp2[k]?.getD 0#32).toNat < 2 * c.max_vars) ∧
            IsMaxHeapFrom s.core.lvl s.core.trail_pos tmp2 0 (e.toNat + 1) ∧
            (∀ j, e.toNat + 1 ≤ j → j < n.toNat → ∀ i, i ≤ j →
              tmpLe s.core.lvl s.core.trail_pos
                (tmp2[1 + i]?.getD 0#32) (tmp2[1 + j]?.getD 0#32)) ∧
            (FullMem c { s with core := { s.core with tmp := tmp2 } } ⋆ R) m2
        refine wp_loop_group (ts := [i64]) Loop2Inv ?_ ?_
        · rintro J2 dec2 ⟨e, ⟨⟩⟩ m2 hJ2 ⟨rfl, he_lt, tmp2, htl2', h02, hseq2, hbd2,
            hh2, hsorted2, hm2⟩
          rw [Blocks.get_here]; ml_lets
          ml_jnz; refine ⟨fun he_pos => ?_, fun he0' => ?_⟩
          · have he_gt0 : 0 < e.toNat := by c0_cond he_pos; bv_omega
            have h1n : (1 : BitVec 64).toNat = 1 := rfl
            have h1e_bv : ((1 : BitVec 64) + e).toNat = 1 + e.toNat := by
              rw [BitVec.toNat_add, h1n, Nat.mod_eq_of_lt (by omega)]
            have hi1 : (1 : BitVec 64).toNat <
                ({ s with core := { s.core with tmp := tmp2 } } : FullState).core.tmp.length := by
              dsimp only; rw [h1n, htl2']; omega
            have hie : ((1 : BitVec 64) + e).toNat <
                ({ s with core := { s.core with tmp := tmp2 } } : FullState).core.tmp.length := by
              dsimp only; rw [h1e_bv, htl2']; omega
            ml_ld c0_load_full_tmp (s := { s with core := { s.core with tmp := tmp2 } })
              (i := (1 : BitVec 64)) hi1 hm2
            ml_ld c0_load_full_tmp (s := { s with core := { s.core with tmp := tmp2 } })
              hie hm2
            ml_lets; rw [wp]
            obtain ⟨hok1, hm3⟩ := c0_store_full_tmp
              (s := { s with core := { s.core with tmp := tmp2 } })
              (i := (1 : BitVec 64)) (tmp2[((1 : BitVec 64) + e).toNat]'hie) hi1 hm2
            refine ⟨hok1, ?_⟩
            ml_lets; rw [wp]
            let tmp2b := tmp2.set (1 : BitVec 64).toNat
              (tmp2[((1 : BitVec 64) + e).toNat]'hie)
            have hie' : ((1 : BitVec 64) + e).toNat <
                ({ s with core := { s.core with tmp := tmp2b } } : FullState).core.tmp.length := by
              simpa [tmp2b] using hie
            obtain ⟨hok2, hm4⟩ := c0_store_full_tmp
              (s := { s with core := { s.core with tmp := tmp2b } })
              (i := 1 + e) (tmp2[(1 : BitVec 64).toNat]'hi1) hie' hm3
            refine ⟨hok2, ?_⟩
            let tmp3 := sortSwap tmp2 1 (1 + e.toNat) (by rw [htl2']; omega) (by rw [htl2']; omega)
            have hm4' : (FullMem c { s with core := { s.core with tmp := tmp3 } } ⋆ R)
                (storeMem (storeMem m2 i32 (c.pTmp + (1 : BitVec 64) * 4)
                  (tmp2[((1 : BitVec 64) + e).toNat]'hie)) i32
                  (c.pTmp + ((1 : BitVec 64) + e) * 4) (tmp2[(1 : BitVec 64).toNat]'hi1)) := by
              simpa only [tmp3, tmp2b, sortSwap, h1n, h1e_bv] using hm4
            have hget3 (idx : Nat) : tmp3[idx]?.getD 0#32 =
                if idx = 1 + e.toNat then tmp2[1]?.getD 0#32
                else if idx = 1 then tmp2[1 + e.toNat]?.getD 0#32
                else tmp2[idx]?.getD 0#32 := by
              dsimp only [tmp3]; rw [sortSwap_getElem?]
              by_cases h1 : idx = 1 + e.toNat
              · simp only [h1, ↓reduceIte,
                  List.getElem?_eq_getElem (by rw [htl2']; omega : 1 < tmp2.length),
                  Option.getD_some]
              · by_cases h2 : idx = 1
                · rw [h2]; simp only [show (1 : Nat) ≠ 1 + e.toNat by omega, ↓reduceIte,
                    List.getElem?_eq_getElem (by rw [htl2']; omega : 1 + e.toNat < tmp2.length),
                    Option.getD_some]
                · simp only [h1, h2, ↓reduceIte]
            have htl3 : tmp3.length = c.max_vars := sortSwap_length.trans htl2'
            have h03 : 0 < s.core.tmp_len → tmp3[0]? = s.core.tmp[0]? := fun htp => by
              rw [sortSwap_getElem?]
              simp only [show 0 ≠ 1 + e.toNat by omega, show (0 : Nat) ≠ 1 by omega, ↓reduceIte]
              exact h02 htp
            have hseq3 : SortSliceEq tmp3 s.core.tmp s.core.tmp_len :=
              sortSliceEq_trans (sortSwap_sliceEq (by omega) (by omega) (by omega) (by omega)) hseq2
            have hbd3 : ∀ k, 1 ≤ k → k < s.core.tmp_len →
                (tmp3[k]?.getD 0#32).toNat < 2 * c.max_vars := fun k hk1 hk2 => by
              obtain ⟨j, hj1, hj2, hkj⟩ := hseq3.1 k hk1 hk2
              rw [hkj]; exact hbd0 j hj1 hj2
            have hmax3_tail : ∀ j, e.toNat ≤ j → j < n.toNat → ∀ i, i ≤ j →
                tmpLe s.core.lvl s.core.trail_pos
                  (tmp3[1 + i]?.getD 0#32) (tmp3[1 + j]?.getD 0#32) := by
              intro j hj1 hj2 i hij
              by_cases hje : j = e.toNat
              · subst hje
                rw [hget3 (1 + e.toNat)]; simp only [↓reduceIte]
                by_cases hie' : i = e.toNat
                · subst hie'; rw [hget3 (1 + e.toNat)]; simp only [↓reduceIte]
                  exact tmpLe_refl _ _ _
                · by_cases hi0 : i = 0
                  · subst hi0; rw [hget3 1]
                    simp only [show (1 : Nat) ≠ 1 + e.toNat by omega, ↓reduceIte]
                    exact heap_root_max hh2 e.toNat (by omega)
                  · rw [hget3 (1 + i)]
                    simp only [show 1 + i ≠ 1 + e.toNat by omega, show 1 + i ≠ 1 by omega,
                      ↓reduceIte]
                    exact heap_root_max hh2 i (by omega)
              · have hje1 : e.toNat + 1 ≤ j := by omega
                rw [hget3 (1 + j)]
                simp only [show 1 + j ≠ 1 + e.toNat by omega, show 1 + j ≠ 1 by omega, ↓reduceIte]
                by_cases hie' : i = e.toNat
                · subst hie'; rw [hget3 (1 + e.toNat)]; simp only [↓reduceIte]
                  exact hsorted2 j hje1 hj2 0 (by omega)
                · by_cases hi0 : i = 0
                  · subst hi0; rw [hget3 1]
                    simp only [show (1 : Nat) ≠ 1 + e.toNat by omega, ↓reduceIte]
                    exact hsorted2 j hje1 hj2 e.toNat (by omega)
                  · rw [hget3 (1 + i)]
                    simp only [show 1 + i ≠ 1 + e.toNat by omega, show 1 + i ≠ 1 by omega,
                      ↓reduceIte]
                    exact hsorted2 j hje1 hj2 i hij
            have hheap3 : IsMaxHeapFrom s.core.lvl s.core.trail_pos tmp3 1 e.toNat := by
              intro i hi1 hi2
              have hhi2 := hh2 i (Nat.zero_le _) (by omega)
              have hiv : tmp3[1 + i]?.getD 0#32 = tmp2[1 + i]?.getD 0#32 := by
                rw [hget3]
                simp only [show 1 + i ≠ 1 + e.toNat by omega, show 1 + i ≠ 1 by omega, ↓reduceIte]
              constructor
              · intro h1; rw [hiv, hget3]
                simp only [show 1 + (2 * i + 1) ≠ 1 + e.toNat by omega,
                  show 1 + (2 * i + 1) ≠ 1 by omega, ↓reduceIte]
                exact hhi2.1 (by omega)
              · intro h2; rw [hiv, hget3]
                simp only [show 1 + (2 * i + 2) ≠ 1 + e.toNat by omega,
                  show 1 + (2 * i + 2) ≠ 1 by omega, ↓reduceIte]
                exact hhi2.2 (by omega)
            ml_lets
            obtain ⟨R_sift, hm4_sift, hm4_unfocus⟩ := fullMem_focus_sort hm4'
            have he_m1 : (e - 1).toNat = e.toNat - 1 := by
              have h1 : (1 : BitVec 64).toNat = 1 := rfl
              rw [BitVec.toNat_sub_of_le (by bv_omega), h1]
            apply wp_call_of_spec; apply hSift
            dsimp only [fullSortTmpSiftSpec, vals, Arg.val]
            refine ⟨tmp3, s.core.lvl, s.core.trail_pos, R_sift,
              by simpa using he_gt0, by omega, by omega,
              fun k hk1 hk2 => by have := hbd3 k hk1 (by omega); exact ⟨by omega, by omega⟩,
              by simpa using hheap3, hm4_sift, ?_⟩
            intro tmp4 m4 htl4 hout4 hseq4 hh4 hm4_sift'
            have hm4_out := hm4_unfocus tmp4 m4 hm4_sift'
            have h04 : 0 < s.core.tmp_len → tmp4[0]? = s.core.tmp[0]? := fun hp =>
              (hout4 0 (Or.inl rfl)).trans (h03 hp)
            have hseq4_full : SortSliceEq tmp4 s.core.tmp s.core.tmp_len :=
              sortSliceEq_trans
                (sortSliceEq_widen (by omega) hseq4 (fun k hk => hout4 k (Or.inr hk)))
                hseq3
            have hbd4 : ∀ k, 1 ≤ k → k < s.core.tmp_len →
                (tmp4[k]?.getD 0#32).toNat < 2 * c.max_vars := fun k hk1 hk2 => by
              obtain ⟨j, hj1, hj2, hkj⟩ := hseq4_full.1 k hk1 hk2
              rw [hkj]; exact hbd0 j hj1 hj2
            have hsorted4 : ∀ j, e.toNat ≤ j → j < n.toNat → ∀ i, i ≤ j →
                tmpLe s.core.lvl s.core.trail_pos
                  (tmp4[1 + i]?.getD 0#32) (tmp4[1 + j]?.getD 0#32) := by
              intro j hj1 hj2 i hij
              rw [hout4 (1 + j) (Or.inr (by omega))]
              by_cases hie_c : i < e.toNat
              · obtain ⟨k, hk1, hk2, hik⟩ := hseq4.1 (1 + i) (by omega) (by omega)
                rw [hik]
                simpa [show 1 + (k - 1) = k by omega] using
                  hmax3_tail j hj1 hj2 (k - 1) (by omega)
              · rw [hout4 (1 + i) (Or.inr (by omega))]
                exact hmax3_tail j hj1 hj2 i hij
            ml_lets
            exact hJ2 (e - 1).toNat (e - 1, ()) m4 (by rw [he_m1]; omega)
              ⟨rfl, by rw [he_m1]; omega, tmp4, htl4.trans htl3, h04, hseq4_full, hbd4,
                by rw [he_m1, Nat.sub_add_cancel he_gt0]; simpa using hh4,
                by rw [he_m1, Nat.sub_add_cancel he_gt0]; exact hsorted4, hm4_out⟩
          · have he_eq0 : e.toNat = 0 := by
              change (0 : BitVec 64).ult e = false at he0'
              rw [BitVec.ult, decide_eq_false_iff_not] at he0'; bv_omega
            rw [he_eq0] at hsorted2
            ml_lets; rw [wp]
            refine hQ tmp2 m2 htl2' h02 hseq2.1 hseq2.2 (fun i j hi1 hij hj => ?_) hm2
            by_cases hj1 : j = 1
            · subst hj1
              have hij' : i = 1 := by omega
              subst hij'; exact le_refl _
            · exact tmpLe_lvl (by
                simpa [show 1 + (i - 1) = i by omega, show 1 + (j - 1) = j by omega] using
                  hsorted2 (j - 1) (by omega) (by omega) (i - 1) (by omega))
        · intro J2 hJ2; wp_unfold
          exact hJ2 e0.toNat (e0, ()) m1 ⟨rfl, by omega, tmp1, htl1, h01, hseq1, hbd1,
            by rw [he0, Nat.sub_add_cancel (by omega)]; exact hh1,
            fun j hj1 => by rw [he0] at hj1; omega, hm1⟩
    · intro J1 hJ1; wp_unfold
      have hsh : ((n >>> ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64))).toNat =
          n.toNat / 2 := by
        have h1 : BitVec.signExtend 64 (1 : BitVec 32) = (1 : BitVec 64) := rfl
        have hm' : (1 : BitVec 64).toNat % 64 = 1 := rfl
        rw [h1, hm', bv64_lshr_1]
      have hh0 : IsMaxHeapFrom s.core.lvl s.core.trail_pos s.core.tmp (n.toNat / 2) n.toNat := by
        intro i hi1 hi2; exact ⟨fun h => by omega, fun h => by omega⟩
      exact hJ1 _ _ m ⟨hsh, le_refl _, s.core.tmp, htmp_len, fun _ => rfl,
        sortSliceEq_refl _ _, hbd0, hh0, hm⟩

/-! ## 3. `full_shrink_lower_wp` -/

theorem full_shrink_lower_wp (Γ : Env)
    (hMm : ∀ args m Q X, fullMinMarkSpec args m Q X →
      Γ "full_min_mark" [i64, i32, i8] [] args m Q X)
    (hMl : ∀ args m Q X, fullMinLitSpec args m Q X →
      Γ "full_min_lit" [i64, i32] [.bool] args m Q X) :
    ∀ args m Q X, fullShrinkLowerSpec args m Q X →
      Func.wp Γ full_shrink_lower_body args m Q X := by
  rintro ⟨h, ot, ov, ⟨⟩⟩ m Q X
    ⟨c, F0, s, keepSet, R, rfl, hcore, hmin, hov_eq, hot_lt, hval, hno8, hm, hQ⟩
  unfold Func.wp full_shrink_lower_body; dsimp only [full_shrink_lower_body]
  have hlen := hcore.lengths
  have hov_lt : ov.toNat < s.core.cur_vars := by omega
  have hov_mrk : (ov.setWidth 64).toNat < s.core.mrk.length := by
    rw [bv_c0_zext32_64, hlen.core_ok.mrk_len]; have := hlen.core_ok.cur_vars_le; omega
  have hov_mrk' : ov.toNat < s.core.mrk.length := by
    rwa [bv_c0_zext32_64] at hov_mrk
  ml_ld load_full_mark_ptr hm
  ml_ld c0_load_full_mrk (i := ov.setWidth 64) hov_mrk hm
  ml_lets; ml_jnz; refine ⟨fun hbit2 => ?_, fun hnbit2 => ?_⟩
  · have hb2 : (s.core.mrk[ov.toNat]?.getD 0#8 &&& 2#8) ≠ 0#8 := by
      rw [List.getElem?_eq_getElem hov_mrk', Option.getD_some]
      rw [show BitVec.setWidth 32 (BitVec.setWidth 8 (2 : BitVec 32)) = (2#8).setWidth 32 from rfl,
        show BitVec.setWidth 32 (BitVec.setWidth 8 (0 : BitVec 32)) = 0#32 from rfl] at hbit2
      c0_cond hbit2
      simpa [bv_c0_zext32_64] using hbit2
    ml_lets; rw [wp]
    exact hQ true s.core.mrk s.core.min_stk s.core.min_clr s.core.min_clr_len
      s.core.min_clr_full m hlen (fun _ _ => rfl) (fun _ _ h => h) (fun _ _ => rfl)
      hmin (fun _ => hb2) hm
  · let FailJoin : Tup Val [] → Mem 64 → Prop := fun () m1 =>
      ∃ mrk1 mstk1 mclr1 mcl1 mcf1,
        let s1 := minLitState s mrk1 mstk1 mclr1 mcl1 mcf1
        s1.LengthsOk c ∧
        (∀ v, s.core.cur_vars ≤ v → mrk1[v]? = s.core.mrk[v]?) ∧
        (∀ v < s.core.cur_vars,
          (s.core.mrk[v]?.getD 0#8 &&& 2#8) ≠ 0#8 → (mrk1[v]?.getD 0#8 &&& 2#8) ≠ 0#8) ∧
        (∀ v < s.core.cur_vars,
          (mrk1[v]?.getD 0#8 &&& 8#8) = (s.core.mrk[v]?.getD 0#8 &&& 8#8)) ∧
        FullMinMarkInv s1.core keepSet ∧
        (FullMem c s1 ⋆ R) m1
    refine wp_join_group (ts := []) FailJoin ?_ ?_
    · rintro _ ⟨⟩ m1 ⟨mrk1, mstk1, mclr1, mcl1, mcf1, hlen1, hab1, hm2_1, h8_1, hmin1, hm1⟩
      rw [Blocks.get_here]; ml_lets
      apply wp_call_of_spec; apply hMm
      refine fullMinMarkSpec_step hlen1 hm1 ov hov_lt ((4 : BitVec 32).setWidth 8)
        fun m2 hm2 => ?_
      have h4 : (4 : BitVec 32).setWidth 8 = 4#8 := rfl
      rw [h4] at hm2
      let s1 := minLitState s mrk1 mstk1 mclr1 mcl1 mcf1
      let s2 := fullMinMarkStepState s1 ov.toNat 4#8
      have hcore1 : FullCoreInv c F0 s1 :=
        fullCoreInv_with_min hcore hlen1.core_ok.mrk_len hlen1.core_ok.min_stk_len
          hlen1.core_ok.min_clr_len_arr hlen1.core_ok.min_clr_len_le
      have hno8_1 : (s1.core.mrk[ov.toNat]?.getD 0#8 &&& 8#8) = 0#8 := by
        dsimp only [s1, minLitState]
        rw [h8_1 ov.toNat hov_lt]
        exact hno8 ov.toNat hov_lt (le_refl _)
      have hlen2 := fullMinMarkStepState_lengths hlen1 ov.toNat 4#8
      have hab2 := fullMinMarkStepState_mrk_above (s := s1) hov_lt 4#8
      obtain ⟨h8_2, hm2_2⟩ := fullMinMarkStepState_bit8_mono2 hlen1 hov_lt (Or.inr rfl) hno8_1
      have hmin2 := fullMinMarkInv_step_poison hcore1 hmin1 hov_lt hno8_1
      have hst2 : s2 = minLitState s s2.core.mrk mstk1 s2.core.min_clr
          s2.core.min_clr_len s2.core.min_clr_full := minLitState_step ov.toNat 4#8
      change FullState.LengthsOk c s2 at hlen2
      change FullMinMarkInv s2.core keepSet at hmin2
      change (FullMem c s2 ⋆ R) m2 at hm2
      rw [hst2] at hlen2 hmin2 hm2
      ml_lets; rw [wp]
      exact hQ false s2.core.mrk mstk1 s2.core.min_clr s2.core.min_clr_len
        s2.core.min_clr_full m2 hlen2
        (fun v hv => (hab2 v hv).trans (hab1 v hv))
        (fun v hv h2 => hm2_2 v hv (hm2_1 v hv h2))
        (fun v hv => (h8_2 v hv).trans (h8_1 v hv))
        hmin2 (fun hc => by cases hc) hm2
    · rintro Jf hJf
      ml_ld c0_load_full_mrk (i := ov.setWidth 64) hov_mrk hm
      ml_lets; ml_jnz; refine ⟨fun _ => ?_, fun _ => ?_⟩
      · exact hJf () m ⟨s.core.mrk, s.core.min_stk, s.core.min_clr, s.core.min_clr_len,
          s.core.min_clr_full, hlen, fun _ _ => rfl, fun _ _ h => h, fun _ _ => rfl, hmin, hm⟩
      · apply wp_call_of_spec; apply hMl
        dsimp only [fullMinLitSpec, vals, Arg.val]
        refine ⟨c, F0, s, keepSet, R, rfl, hcore, hmin, hot_lt, hval,
          fun v hv hle => hno8 v hv (by rwa [hov_eq]), hm, ?_⟩
        intro ok mrk1 mstk1 mclr1 mcl1 mcf1 m1 hlen1 hab1 hm2_1 h8_1 hmin1 hok1 hm1
        ml_lets; ml_jnz; refine ⟨fun hok_t => ?_, fun _ => ?_⟩
        · have hmark2 := (hok1 hok_t).2
          rw [← hov_eq] at hmark2
          ml_lets; apply wp_call_of_spec; apply hMm
          refine fullMinMarkSpec_step hlen1 hm1 ov hov_lt ((2 : BitVec 32).setWidth 8)
            fun m2 hm2 => ?_
          have h2eq : (2 : BitVec 32).setWidth 8 = 2#8 := rfl
          rw [h2eq] at hm2
          let s1 := minLitState s mrk1 mstk1 mclr1 mcl1 mcf1
          let s2 := fullMinMarkStepState s1 ov.toNat 2#8
          have hno8_1 : (s1.core.mrk[ov.toNat]?.getD 0#8 &&& 8#8) = 0#8 := by
            dsimp only [s1, minLitState]
            rw [h8_1 ov.toNat hov_lt]
            exact hno8 ov.toNat hov_lt (le_refl _)
          have hlen2 := fullMinMarkStepState_lengths hlen1 ov.toNat 2#8
          have hab2 := fullMinMarkStepState_mrk_above (s := s1) hov_lt 2#8
          obtain ⟨h8_2, hm2_2⟩ := fullMinMarkStepState_bit8_mono2 hlen1 hov_lt (Or.inl rfl) hno8_1
          have hmin2 : FullMinMarkInv s2.core keepSet := by
            dsimp only [s2, fullMinMarkStepState, fullMinMarkStepCore]
            split
            · exact hmin1
            · exact hmark2
          have hov2 : (s2.core.mrk[ov.toNat]?.getD 0#8 &&& 2#8) ≠ 0#8 := by
            dsimp only [s2, fullMinMarkStepState, fullMinMarkStepCore, fullMinMarkCore]
            split
            · rename_i hc
              rcases hc with hge | hset
              · exact absurd hov_lt (Nat.not_lt.mpr hge)
              · exact hset
            · have hm_len : mrk1.length = c.max_vars := hlen1.core_ok.mrk_len
              have hcv := hlen.core_ok.cur_vars_le
              dsimp only [s1, minLitState]
              rw [List.getElem?_set_self (by omega), Option.getD_some]
              exact bv8_and2_of_or2 _
          have hst2 : s2 = minLitState s s2.core.mrk mstk1 s2.core.min_clr
              s2.core.min_clr_len s2.core.min_clr_full := minLitState_step ov.toNat 2#8
          change FullState.LengthsOk c s2 at hlen2
          change FullMinMarkInv s2.core keepSet at hmin2
          change (FullMem c s2 ⋆ R) m2 at hm2
          rw [hst2] at hlen2 hmin2 hm2
          ml_lets; rw [wp]
          exact hQ true s2.core.mrk mstk1 s2.core.min_clr s2.core.min_clr_len
            s2.core.min_clr_full m2 hlen2
            (fun v hv => (hab2 v hv).trans (hab1 v hv))
            (fun v hv h2 => hm2_2 v hv (hm2_1 v hv h2))
            (fun v hv => (h8_2 v hv).trans (h8_1 v hv))
            hmin2 (fun _ => hov2) hm2
        · exact hJf () m1 ⟨mrk1, mstk1, mclr1, mcl1, mcf1, hlen1, hab1, hm2_1, h8_1, hmin1, hm1⟩

/-! ## 4. Block-shrink state, `trailCount8`, structural `RsnCov`, and `ShrinkBaseInv` -/

def shrinkBlkSt (s : FullState) (tmp1 : List (BitVec 32)) (mrk1 : List (BitVec 8))
    (mstk1 mclr1 : List (BitVec 32)) (mcl1 : Nat) (mcf1 : BitVec 64)
    (sstk1 : List (BitVec 32)) : FullState :=
  { core := { s.core with
      tmp := tmp1, mrk := mrk1, min_stk := mstk1, min_clr := mclr1,
      min_clr_len := mcl1, min_clr_full := mcf1 }
    scratch := { s.scratch with shrink_stk := sstk1 } }

theorem coreInv_shrinkBlk {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hcore : FullCoreInv c F0 s) {tmp1 : List (BitVec 32)} {mrk1 : List (BitVec 8)}
    {mstk1 mclr1 sstk1 : List (BitVec 32)} {mcl1 : Nat} {mcf1 : BitVec 64}
    (htmp : tmp1.length = c.max_vars) (hmrk : mrk1.length = c.max_vars)
    (hmstk : mstk1.length = 2 * c.minDepth) (hmclr : mclr1.length = c.max_vars)
    (hmcl : mcl1 ≤ c.max_vars) (hsstk : sstk1.length = c.max_vars) :
    FullCoreInv c F0 (shrinkBlkSt s tmp1 mrk1 mstk1 mclr1 mcl1 mcf1 sstk1) :=
  fullCoreInv_with_min_tmp hcore htmp hcore.lengths.core_ok.tmp_len_le hmrk hmstk hmclr hmcl
    { hcore.lengths.scratch_ok with shrink_stk_len := hsstk }

theorem shrinkBlkSt_step {s : FullState} {tmp1 : List (BitVec 32)}
    {mrk1 : List (BitVec 8)} {mstk1 mclr1 sstk1 : List (BitVec 32)} {mcl1 : Nat}
    {mcf1 : BitVec 64} (v : Nat) (tag : BitVec 8) :
    let sb := shrinkBlkSt s tmp1 mrk1 mstk1 mclr1 mcl1 mcf1 sstk1
    let sb' := fullMinMarkStepState sb v tag
    sb' = shrinkBlkSt s tmp1 sb'.core.mrk mstk1 sb'.core.min_clr sb'.core.min_clr_len
      sb'.core.min_clr_full sstk1 := by
  intro sb sb'
  dsimp only [sb', fullMinMarkStepState, fullMinMarkStepCore, fullMinMarkCore, sb, shrinkBlkSt]
  split
  · rfl
  · rfl

/-- Purely structural reason coverage predicate (independent of `F_cur`). -/
def RsnCov (k : FullCoreState) (P : Nat → Prop) (idx : Nat) : Prop :=
  let p := (k.trl[idx]?.getD 0#32).toNat
  let rsn := k.rsns[p / 2]?.getD 0xFFFFFFFF#32
  rsn ≠ 0xFFFFFFFF#32 ∧
  if (rsn &&& 0x80000000#32) ≠ 0#32 then
    let ot := (rsn &&& 0x7FFFFFFF#32).toNat
    ot < 2 * k.cur_vars ∧
    ∃ j < idx, (k.trl[j]?.getD 0#32).toNat = ot ^^^ 1 ∧
      ((k.lvl[ot / 2]?.getD 0#32).toNat = 0 ∨ P (ot / 2))
  else
    rsn.toNat ∈ fullArenaClauseRefsCore k ∧ fullArenaClauseGarbCore k rsn.toNat = false ∧
    ∀ q ∈ fullArenaClauseLitsCore k rsn.toNat,
      q = p ∨ ∃ j < idx, (k.trl[j]?.getD 0#32).toNat = q ^^^ 1 ∧
        ((k.lvl[q / 2]?.getD 0#32).toNat = 0 ∨ P (q / 2))

theorem rsnCov_mono {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hcore : FullCoreInv c F0 s) {P1 P2 : Nat → Prop}
    (hP : ∀ w < s.core.cur_vars, P1 w → P2 w) {idx : Nat} (h : RsnCov s.core P1 idx) :
    RsnCov s.core P2 idx := by
  obtain ⟨F_cur, hw⟩ := hcore.witness
  dsimp only [RsnCov] at h ⊢
  rcases h with ⟨hne, hif⟩
  refine ⟨hne, ?_⟩
  split at hif <;> split
  · obtain ⟨hot, j, hj, hjeq, hdep⟩ := hif
    exact ⟨hot, j, hj, hjeq, hdep.elim Or.inl fun h1 => Or.inr (hP _ (by omega) h1)⟩
  · rename_i h1 h2; exact absurd h1 h2
  · rename_i h1 h2; exact absurd h2 h1
  · obtain ⟨href, hng, hall⟩ := hif
    refine ⟨href, hng, fun q hq => ?_⟩
    have hqlt := hw.arena.lits_lt _ href hng _ hq
    rcases hall q hq with rfl | ⟨j, hj, hjeq, hdep⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨j, hj, hjeq, hdep.elim Or.inl fun h1 => Or.inr (hP _ (by omega) h1)⟩

abbrev ShrinkResolved (k : FullCoreState) (mrk : List (BitVec 8)) (idx : Nat) : Prop :=
  RsnCov k (fun w => (mrk[w]?.getD 0#8 &&& 2#8) ≠ 0#8 ∨ (mrk[w]?.getD 0#8 &&& 8#8) ≠ 0#8) idx

theorem remSound_lift_mrk2 {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hcore : FullCoreInv c F0 s) {mrk1 mrk2 : List (BitVec 8)}
    (hm2 : ∀ w < s.core.cur_vars,
      (mrk1[w]?.getD 0#8 &&& 2#8) ≠ 0#8 → (mrk2[w]?.getD 0#8 &&& 2#8) ≠ 0#8)
    {idx : Nat} (h : RsnCov s.core (fun w => (mrk1[w]?.getD 0#8 &&& 2#8) ≠ 0#8) idx) :
    RsnCov s.core (fun w => (mrk2[w]?.getD 0#8 &&& 2#8) ≠ 0#8) idx :=
  rsnCov_mono hcore hm2 h

theorem shrinkResolved_mono {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hcore : FullCoreInv c F0 s) {mrk1 mrk2 : List (BitVec 8)}
    (hm2 : ∀ w < s.core.cur_vars,
      (mrk1[w]?.getD 0#8 &&& 2#8) ≠ 0#8 → (mrk2[w]?.getD 0#8 &&& 2#8) ≠ 0#8)
    (hm8 : ∀ w < s.core.cur_vars,
      (mrk1[w]?.getD 0#8 &&& 8#8) ≠ 0#8 → (mrk2[w]?.getD 0#8 &&& 8#8) ≠ 0#8)
    {idx : Nat} (hr : ShrinkResolved s.core mrk1 idx) :
    ShrinkResolved s.core mrk2 idx :=
  rsnCov_mono hcore (fun w hw h => h.elim (fun h2 => Or.inl (hm2 w hw h2))
    (fun h8 => Or.inr (hm8 w hw h8))) hr

theorem shrinkResolved_to_rem {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hcore : FullCoreInv c F0 s) {mrk1 mrk2 : List (BitVec 8)}
    (hm2 : ∀ w < s.core.cur_vars,
      (mrk1[w]?.getD 0#8 &&& 2#8) ≠ 0#8 → (mrk2[w]?.getD 0#8 &&& 2#8) ≠ 0#8)
    (hm8 : ∀ w < s.core.cur_vars,
      (mrk1[w]?.getD 0#8 &&& 8#8) ≠ 0#8 → (mrk2[w]?.getD 0#8 &&& 2#8) ≠ 0#8)
    {idx : Nat} (hr : ShrinkResolved s.core mrk1 idx) :
    RsnCov s.core (fun w => (mrk2[w]?.getD 0#8 &&& 2#8) ≠ 0#8) idx :=
  rsnCov_mono hcore (fun w hw h => h.elim (hm2 w hw) (hm8 w hw)) hr

structure ShrinkBaseInv (c : FullCfg) (s : FullState)
    (mrk1 : List (BitVec 8)) (mstk1 mclr1 : List (BitVec 32)) (mcl1 : Nat) (mcf1 : BitVec 64)
    (sstk1 : List (BitVec 32)) (slen : Nat) (keep0 : List Nat) : Prop where
  mrk_len : mrk1.length = c.max_vars
  mstk_len : mstk1.length = 2 * c.minDepth
  mclr_len : mclr1.length = c.max_vars
  mcl_le : mcl1 ≤ c.max_vars
  sstk_len : sstk1.length = c.max_vars
  slen_le : slen ≤ s.core.cur_vars
  mrk_above : ∀ w, s.core.cur_vars ≤ w → mrk1[w]? = s.core.mrk[w]?
  min_inv : FullMinMarkInv (shrinkBlkSt s s.core.tmp mrk1 mstk1 mclr1 mcl1 mcf1 sstk1).core keep0
  mono2 : ∀ w < s.core.cur_vars,
    (s.core.mrk[w]?.getD 0#8 &&& 2#8) ≠ 0#8 → (mrk1[w]?.getD 0#8 &&& 2#8) ≠ 0#8
  bit8_sstk : ∀ w < s.core.cur_vars, (mrk1[w]?.getD 0#8 &&& 8#8) ≠ 0#8 →
    ∃ j < slen, (sstk1[j]?.getD 0#32).toNat = w
  sstk_lt : ∀ j < slen, (sstk1[j]?.getD 0#32).toNat < s.core.cur_vars

theorem shrinkBaseInv_core {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hcore : FullCoreInv c F0 s) {mrk1 : List (BitVec 8)} {mstk1 mclr1 sstk1 : List (BitVec 32)}
    {mcl1 slen : Nat} {mcf1 : BitVec 64} {keep0 : List Nat}
    (hb : ShrinkBaseInv c s mrk1 mstk1 mclr1 mcl1 mcf1 sstk1 slen keep0) :
    FullCoreInv c F0 (shrinkBlkSt s s.core.tmp mrk1 mstk1 mclr1 mcl1 mcf1 sstk1) :=
  coreInv_shrinkBlk hcore hcore.lengths.core_ok.tmp_len_arr hb.mrk_len hb.mstk_len hb.mclr_len
    hb.mcl_le hb.sstk_len

theorem getElem?_getD_of_getElem {α : Type _} (d : α) {xs ys : List α}
    {i j : Nat} {hj : j < ys.length} (hxy : xs = ys) (hij : i = j) :
    xs[i]?.getD d = ys[j]'hj := by
  subst hxy hij; rw [List.getElem?_eq_getElem hj, Option.getD_some]

end LeanQbe.T.Examples.Kissat.Full
