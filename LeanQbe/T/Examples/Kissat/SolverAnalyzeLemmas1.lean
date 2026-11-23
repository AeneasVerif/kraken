module

public import LeanQbe.T.Examples.Kissat.SolverSpec
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Min` C0 Conflict-Analysis Helper & Decision `Func.wp` Proofs (Part 1)

Builds on `SolverSpec` to specify and verify:
1. `kissat_clear_marks` (`kissatClearMarksSpec`, `kissat_clear_marks_wp`).
2. `kissat_decide` (`kissatDecideSpec`, `kissat_decide_wp`).
3. `kissat_analyze_clause` (`kissatAnalyzeClauseSpec`, `kissat_analyze_clause_wp`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open Kraken.Bedrock2.Test

/-! ## 1. Private bit-vector, list-counting, and analysis-invariant helpers -/

theorem bv8_zext32_eq_zero (b : BitVec 8) : b.setWidth 32 = 0#32 ↔ b = 0#8 := by
  constructor
  · intro h
    apply BitVec.eq_of_toNat_eq
    have hb := b.isLt
    have ht := congrArg BitVec.toNat h
    simp [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega : b.toNat < 2 ^ 32)] at ht
    exact ht
  · rintro rfl; rfl

private theorem bv64_shl1_or1_trunc32 {v : Nat} (hv : 2 * v + 1 < 2 ^ 32) :
    (BitVec.ofNat 64 (2 * v) ||| 1#64).setWidth 32 = BitVec.ofNat 32 (2 * v + 1) := by
  have hor : (2 * v) ||| 1 = 2 * v + 1 := by
    apply Nat.eq_of_testBit_eq; intro i
    cases i with
    | zero =>
      simp [Nat.testBit_zero]
    | succ k =>
      simp only [Nat.testBit_or]
      rw [Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ]
      have h1 : (1 / 2 : Nat) = 0 := rfl
      have hd : (2 * v + 1) / 2 = v := by omega
      have hd2 : (2 * v) / 2 = v := by omega
      rw [h1, hd, hd2]; simp
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_or, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : 2 * v < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : 2 * v + 1 < 2 ^ 32)]
  change ((2 * v) ||| 1) % 2 ^ 32 = 2 * v + 1
  rw [hor, Nat.mod_eq_of_lt hv]

private theorem filter_length_flip_one {α : Type} (p p' : α → Bool) (k : α) :
    ∀ (xs : List α), xs.Nodup → k ∈ xs →
      p k = false → p' k = true →
      (∀ x ∈ xs, x ≠ k → p' x = p x) →
      (xs.filter p').length = (xs.filter p).length + 1
  | [], _, hmem, _, _, _ => by simp at hmem
  | x :: xs, hnd, hmem, hpk, hp'k, hagree => by
    rw [List.nodup_cons] at hnd
    rcases List.mem_cons.mp hmem with rfl | hmem'
    · have hfeq : xs.filter p' = xs.filter p := List.filter_congr fun y hy =>
        hagree y (List.mem_cons_of_mem _ hy) (fun heq => hnd.1 (heq ▸ hy))
      simp [hpk, hp'k, hfeq]
    · have hne : x ≠ k := fun heq => hnd.1 (heq ▸ hmem')
      have hx := hagree x List.mem_cons_self hne
      have ih := filter_length_flip_one p p' k xs hnd.2 hmem' hpk hp'k
        fun y hy => hagree y (List.mem_cons_of_mem _ hy)
      cases hp : p x <;> simp [hx, hp, ih] <;> omega

private theorem filter_length_eq_zero_of_false {α : Type} {p : α → Bool} {xs : List α}
    (h : ∀ x ∈ xs, p x = false) : (xs.filter p).length = 0 := by
  have : xs.filter p = [] := List.filter_eq_nil_iff.mpr fun x hx => by simp [h x hx]
  simp [this]

/-- Decision assignment (`cur_level := s.cur_level + 1`, `rsn := 0xFFFFFFFF#32`) preserves
`SolverCoreInv`. -/
private theorem decide_assign_preserves_core {c : ArenaCfg} {F0 : CNF Nat} {s : ArenaState}
    (hinv : SolverCoreInv c F0 s) {lit : BitVec 32}
    (hlit : lit.toNat < 2 * c.mv)
    (hun : s.vals[lit.toNat]?.getD 0#8 = 0#8) :
    let v := lit.toNat / 2
    let s' : ArenaState :=
      { s with
        cur_level := s.cur_level + 1
        vals := (s.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8
        lvl := s.lvl.set v (BitVec.ofNat 32 (s.cur_level + 1))
        rsns := s.rsns.set v 0xFFFFFFFF#32
        trl := s.trl.set s.trail_end lit
        trail_end := s.trail_end + 1 }
    SolverCoreInv c F0 s' := by
  intro v s'
  have hmv := c.hmv; unfold dimacsBound at hmv
  have hte_lt : s.trail_end < c.mv := hinv.trail_end_lt_of_unassigned hlit hun
  have hnot_var : ∀ i < s.trail_end, (s.trl[i]?.getD 0#32).toNat / 2 ≠ v :=
    (hinv.vals_zero_iff hlit).mp hun
  have hnlit_lt : (lit.toNat ^^^ 1) < 2 * c.mv := litNeg_lt_two_mul hlit
  have hne_lit : lit.toNat ^^^ 1 ≠ lit.toNat := litNeg_ne_self lit.toNat
  have hlen := hinv.lengths
  have hcur_le := hinv.cur_level_le
  have hcur1_lt : s.cur_level + 1 < 2 ^ 32 := by omega
  have htrl_get : ∀ i < s.trail_end + 1,
      (s'.trl[i]?.getD 0#32).toNat =
        if i = s.trail_end then lit.toNat else (s.trl[i]?.getD 0#32).toNat := by
    intro i hi
    by_cases he : i = s.trail_end
    · subst he; simp [s', List.getElem?_set_self (by rw [hlen.trl_len]; omega)]
    · simp [s', he, List.getElem?_set_ne (Ne.symm he)]
  have hlvl_get : ∀ w < c.mv,
      (s'.lvl[w]?.getD 0#32).toNat =
        if w = v then s.cur_level + 1 else (s.lvl[w]?.getD 0#32).toNat := by
    intro w hw
    by_cases he : w = v
    · subst he
      simp [s', List.getElem?_set_self (by rw [hlen.lvl_len]; omega), bv32_ofNat_toNat hcur1_lt]
    · simp [s', he, List.getElem?_set_ne (Ne.symm he)]
  have hvals_get : ∀ l < 2 * c.mv,
      s'.vals[l]?.getD 0#8 =
        if l = lit.toNat ^^^ 1 then 0xFF#8
        else if l = lit.toNat then 1#8
        else s.vals[l]?.getD 0#8 := by
    intro l hl
    by_cases h1 : l = lit.toNat ^^^ 1
    · subst h1; dsimp only [s']; simp only [↓reduceIte]
      rw [List.getElem?_set_self (by simp [hlen.vals_len]; exact hnlit_lt)]; rfl
    · dsimp only [s']; simp only [h1, ↓reduceIte]
      rw [List.getElem?_set_ne (Ne.symm h1)]
      by_cases h2 : l = lit.toNat
      · subst h2; simp only [↓reduceIte]
        rw [List.getElem?_set_self (by rw [hlen.vals_len]; exact hlit)]; rfl
      · simp only [h2, ↓reduceIte]; rw [List.getElem?_set_ne (Ne.symm h2)]
  have hpr_le := hlen.propagated_le
  have hs'_te : s'.trail_end = s.trail_end + 1 := rfl
  have hs'_pr : s'.propagated = s.propagated := rfl
  have hs'_cl : s'.cur_level = s.cur_level + 1 := rfl
  have hs'_nc : s'.num_clauses = s.num_clauses := rfl
  have hs'_cls : s'.cls = s.cls := rfl
  have hs'_lp : s'.lpool = s.lpool := rfl
  refine ⟨⟨by simp [s', hlen.vals_len], hlen.mrk_len, by simp [s', hlen.lvl_len],
      by simp [s', hlen.rsns_len], by simp [s', hlen.trl_len], hlen.tmp_len_arr, hlen.wh_len,
      hlen.cls_len, hlen.wn_len, hlen.lpool_len, hlen.lit_len_le, hlen.num_clauses_le,
      by omega, by omega, hcur1_lt, hlen.tmp_cnt_lt, hlen.tmp_len_lt⟩,
    ⟨hinv.clauses.bounds, hinv.clauses.disjoint, hinv.clauses.lits_lt, hinv.clauses.entails⟩,
    by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi; rw [hs'_te] at hi; rw [htrl_get i hi]; split
    · exact hlit
    · exact hinv.trail_lits_lt i (by omega)
  · intro i j hi hj hveq
    rw [hs'_te] at hi hj; rw [htrl_get i hi, htrl_get j hj] at hveq
    split at hveq <;> split at hveq
    · omega
    · exact absurd hveq.symm (hnot_var j (by omega))
    · exact absurd hveq (hnot_var i (by omega))
    · exact hinv.trail_vars_nodup i j (by omega) (by omega) hveq
  · intro l hl; rw [hvals_get l hl]
    split; · exact Or.inr (Or.inr rfl)
    split; · exact Or.inr (Or.inl rfl)
    exact hinv.vals_domain l hl
  · intro l hl; rw [hvals_get l hl, hs'_te]
    constructor
    · intro h1
      by_cases hneg : l = lit.toNat ^^^ 1
      · simp [hneg] at h1
      · simp only [hneg, ↓reduceIte] at h1
        by_cases hpos : l = lit.toNat
        · exact ⟨s.trail_end, by omega, by rw [htrl_get _ (by omega)]; simp [hpos]⟩
        · simp only [hpos, ↓reduceIte] at h1
          obtain ⟨i, hi, heq⟩ := (hinv.vals_true_iff l hl).mp h1
          exact ⟨i, by omega,
            by rw [htrl_get i (by omega)]; simp [show i ≠ s.trail_end by omega, heq]⟩
    · rintro ⟨i, hi, heq⟩
      rw [htrl_get i hi] at heq
      by_cases hie : i = s.trail_end
      · simp only [hie, ↓reduceIte] at heq; subst heq; simp [Ne.symm hne_lit]
      · simp only [hie, ↓reduceIte] at heq
        have hlv : l / 2 ≠ v := by rw [← heq]; exact hnot_var i (by omega)
        have h1 : l ≠ lit.toNat ^^^ 1 := fun h => hlv (by rw [h]; exact litVar_litNeg _)
        have h2 : l ≠ lit.toNat := fun h => hlv (by rw [h])
        simp only [h1, h2, ↓reduceIte]; exact (hinv.vals_true_iff l hl).mpr ⟨i, by omega, heq⟩
  · intro l hl; rw [hvals_get l hl, hs'_te]
    constructor
    · intro h1
      by_cases hneg : l = lit.toNat ^^^ 1
      · refine ⟨s.trail_end, by omega, ?_⟩
        rw [htrl_get _ (by omega)]; simp only [↓reduceIte, hneg]; exact (litNeg_litNeg _).symm
      · simp only [hneg, ↓reduceIte] at h1
        by_cases hpos : l = lit.toNat
        · simp [hpos] at h1
        · simp only [hpos, ↓reduceIte] at h1
          obtain ⟨i, hi, heq⟩ := (hinv.vals_false_iff l hl).mp h1
          exact ⟨i, by omega,
            by rw [htrl_get i (by omega)]; simp [show i ≠ s.trail_end by omega, heq]⟩
    · rintro ⟨i, hi, heq⟩
      rw [htrl_get i hi] at heq
      by_cases hie : i = s.trail_end
      · simp only [hie, ↓reduceIte] at heq
        have hl_eq : l = lit.toNat ^^^ 1 := by
          have h := congrArg litNeg heq
          have h1 : litNeg (l ^^^ 1) = l := litNeg_litNeg l
          rw [h1] at h; exact h.symm
        simp [hl_eq]
      · simp only [hie, ↓reduceIte] at heq
        have hlv : l / 2 ≠ v := by
          have h := hnot_var i (by omega); rw [heq] at h
          have h1 : (l ^^^ 1) / 2 = l / 2 := litVar_litNeg l; rwa [h1] at h
        have h1 : l ≠ lit.toNat ^^^ 1 := fun h => hlv (by rw [h]; exact litVar_litNeg _)
        have h2 : l ≠ lit.toNat := fun h => hlv (by rw [h])
        simp only [h1, h2, ↓reduceIte]; exact (hinv.vals_false_iff l hl).mpr ⟨i, by omega, heq⟩
  · intro i hi; rw [hs'_te] at hi; rw [hs'_cl, htrl_get i hi]
    by_cases hie : i = s.trail_end
    · simp only [hie, ↓reduceIte]; rw [hlvl_get v (by omega)]; simp
    · simp only [hie, ↓reduceIte]
      have hilt : i < s.trail_end := by omega
      rw [hlvl_get _ (by have := hinv.trail_lits_lt i hilt; omega)]
      simp only [hnot_var i hilt, ↓reduceIte]; have := hinv.lvl_le i hilt; omega
  · intro i j hij hj; rw [hs'_te] at hj; rw [htrl_get i (by omega), htrl_get j hj]
    by_cases hje : j = s.trail_end
    · simp only [hje, ↓reduceIte]; rw [hlvl_get v (by omega)]; simp only [↓reduceIte]
      by_cases hie : i = s.trail_end
      · simp only [hie, ↓reduceIte]; rw [hlvl_get v (by omega)]; simp
      · simp only [hie, ↓reduceIte]
        have hilt : i < s.trail_end := by omega
        rw [hlvl_get _ (by have := hinv.trail_lits_lt i hilt; omega)]
        simp only [hnot_var i hilt, ↓reduceIte]; have := hinv.lvl_le i hilt; omega
    · have hjlt : j < s.trail_end := by omega
      have hilt : i < s.trail_end := by omega
      simp only [show i ≠ s.trail_end by omega, hje, ↓reduceIte]
      rw [hlvl_get _ (by have := hinv.trail_lits_lt i hilt; omega),
        hlvl_get _ (by have := hinv.trail_lits_lt j hjlt; omega)]
      simp only [hnot_var i hilt, hnot_var j hjlt, ↓reduceIte]
      exact hinv.trail_mono i j hij hjlt
  · intro L hL1 hLle; rw [hs'_cl] at hLle; rw [hs'_te]
    by_cases hLeq : L = s.cur_level + 1
    · subst hLeq
      refine ⟨s.trail_end, by omega, ?_⟩
      rw [htrl_get _ (by omega)]; simp only [↓reduceIte]; rw [hlvl_get v (by omega)]; simp
    · obtain ⟨i, hi, hli⟩ := hinv.levels_inhabited L hL1 (by omega)
      refine ⟨i, by omega, ?_⟩
      rw [htrl_get i (by omega)]; simp only [show i ≠ s.trail_end by omega, ↓reduceIte]
      rw [hlvl_get _ (by have := hinv.trail_lits_lt i hi; omega)]
      simp [hnot_var i hi, hli]
  · intro i hi hli; rw [hs'_te] at hi; rw [htrl_get i hi] at hli ⊢
    by_cases hie : i = s.trail_end
    · simp only [hie, ↓reduceIte] at hli; rw [hlvl_get v (by omega)] at hli; simp at hli
    · simp only [hie, ↓reduceIte] at hli ⊢
      have hilt : i < s.trail_end := by omega
      rw [hlvl_get _ (by have := hinv.trail_lits_lt i hilt; omega)] at hli
      simp only [hnot_var i hilt, ↓reduceIte] at hli
      exact hinv.level0_sound i hilt hli
  · intro idx hidx; rw [hs'_te] at hidx; dsimp only; rw [htrl_get idx hidx]
    by_cases hie : idx = s.trail_end
    · simp only [hie, ↓reduceIte]
      have hr : s'.rsns[v]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 := by
        dsimp only [s']; rw [List.getElem?_set_self (by rw [hlen.rsns_len]; omega)]; rfl
      rw [hr]; intro hne; exact absurd rfl hne
    · simp only [hie, ↓reduceIte]
      have hilt : idx < s.trail_end := by omega
      have hnv : (s.trl[idx]?.getD 0#32).toNat / 2 ≠ v := hnot_var idx hilt
      have hr : s'.rsns[(s.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 =
          s.rsns[(s.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 := by
        simp [s', List.getElem?_set_ne (Ne.symm hnv)]
      rw [hr]; intro hne
      obtain ⟨hrc, hall⟩ := hinv.reason_inv idx hilt hne
      refine ⟨by rw [hs'_nc]; exact hrc, fun q hq => ?_⟩
      have hq' : q ∈ clauseLits s
          (s.rsns[(s.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat := by
        simpa [clauseLits, clauseOff, clauseSize, hs'_cls, hs'_lp] using hq
      exact (hall q hq').elim Or.inl fun ⟨k, hk, hkeq⟩ => Or.inr ⟨k, hk, by
        rw [htrl_get k (by omega)]; simp [show k ≠ s.trail_end by omega, hkeq]⟩

/-! ## 2. `kissat_clear_marks` specification and `Func.wp` proof -/

/-- Specification of `kissat_clear_marks(h, trail_from)`. -/
def kissatClearMarksSpec : Spec [i64, i64] [] :=
  fun (h, trail_from, ()) m Q _ =>
    ∃ (c : ArenaCfg) (s : ArenaState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ s.tmp_len ≤ c.mv ∧ (ArenaMem c s ⋆ R) m ∧
      ∀ (mrk' : List (BitVec 8)) (m' : Mem 64),
        mrk'.length = c.mv →
        (∀ v < c.mv, s.mrk[v]?.getD 0#8 = 0#8 → mrk'[v]?.getD 0#8 = 0#8) →
        (∀ i, 1 ≤ i → i < s.tmp_len → (s.tmp[i]?.getD 0#32).toNat / 2 < c.mv →
          mrk'[(s.tmp[i]?.getD 0#32).toNat / 2]?.getD 0#8 = 0#8) →
        (∀ j, trail_from.toNat ≤ j → j < s.trail_end → (s.trl[j]?.getD 0#32).toNat / 2 < c.mv →
          mrk'[(s.trl[j]?.getD 0#32).toNat / 2]?.getD 0#8 = 0#8) →
        (ArenaMem c { s with mrk := mrk' } ⋆ R) m' → Q () m'

theorem kissat_clear_marks_wp (Γ : Env) :
    ∀ args m Q X, kissatClearMarksSpec args m Q X →
      Func.wp Γ kissat_clear_marks_body args m Q X := by
  rintro ⟨h, trail_from, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, htl_mv, hm, hQ⟩
  unfold Func.wp kissat_clear_marks_body; wp_unfold
  have hmv := c.hmv; unfold dimacsBound at hmv
  refine ⟨_, load_arena_mark hm, _, load_arena_tmp_lits hm, _, load_arena_trail hm,
    _, load_arena_mv hm, ?_⟩
  refine wp_loop_group
    (fun r (iv, ()) ml => ∃ i mrk1,
      1 ≤ i ∧ i ≤ max 1 s.tmp_len ∧ r = max 1 s.tmp_len - i ∧ iv = BitVec.ofNat 64 i ∧
      mrk1.length = c.mv ∧
      (∀ v < c.mv, s.mrk[v]?.getD 0#8 = 0#8 → mrk1[v]?.getD 0#8 = 0#8) ∧
      (∀ k, 1 ≤ k → k < i → k < s.tmp_len → (s.tmp[k]?.getD 0#32).toNat / 2 < c.mv →
        mrk1[(s.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#8 = 0#8) ∧
      (ArenaMem c { s with mrk := mrk1 } ⋆ R) ml) ?_ ?_
  · rintro L r ⟨iv, ⟨⟩⟩ ml ih ⟨i, mrk1, hi1, hile, rfl, rfl, hml1, hpres1, hclr1, hmem1⟩
    wp_unfold
    refine ⟨_, load_arena_tmp_len hmem1, ?_⟩
    rw [bv_ult_eq (by omega) (by dsimp; omega)]
    simp only [decide_eq_true_eq, decide_eq_false_iff_not]
    refine ⟨fun hilt => ?_, fun hige => ?_⟩
    · rw [bv64_mul4_nat]
      have hi_tmp : i < s.tmp.length := by rw [hlen.tmp_len_arr]; omega
      refine ⟨_, load_arena_tmp (s := { s with mrk := mrk1 }) hi_tmp hmem1, ?_⟩
      let v := (s.tmp[i]'hi_tmp).toNat / 2
      have hv_eq : ((s.tmp[i]'hi_tmp) >>> 1).setWidth 64 = BitVec.ofNat 64 v := by
        rw [bv32_zext64_eq, bv32_lshr_1]
      have hv64 : v < 2 ^ 64 := by have := (s.tmp[i]'hi_tmp).isLt; omega
      refine wp_join_group
        (fun () m2 => ∃ mrk2,
          mrk2.length = c.mv ∧
          (∀ w < c.mv, s.mrk[w]?.getD 0#8 = 0#8 → mrk2[w]?.getD 0#8 = 0#8) ∧
          (∀ k, 1 ≤ k → k < i + 1 → k < s.tmp_len → (s.tmp[k]?.getD 0#32).toNat / 2 < c.mv →
            mrk2[(s.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#8 = 0#8) ∧
          (ArenaMem c { s with mrk := mrk2 } ⋆ R) m2) ?_ ?_
      · rintro _ ⟨⟩ m2 ⟨mrk2, hml2, hpres2, hclr2, hmem2⟩
        wp_unfold
        rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, bv_add_ofNat]
        exact ih (max 1 s.tmp_len - (i + 1)) _ _ (by omega)
          ⟨i + 1, mrk2, by omega, by omega, rfl, rfl, hml2, hpres2, hclr2, hmem2⟩
      · intro J hJ; wp_unfold
        rw [hv_eq, bv_ult_eq hv64 (by omega)]
        simp only [decide_eq_true_eq, decide_eq_false_iff_not]
        refine ⟨fun hvlt => ?_, fun hvge => ?_⟩
        · rw [trunc32_8_zero]
          obtain ⟨oks, hms⟩ := store_arena_mrk (i := v) 0#8 (by simp [hml1]; exact hvlt) hmem1
          refine ⟨oks, hJ () _ ⟨mrk1.set v 0#8, by simp [hml1], ?_, ?_, hms⟩⟩
          · intro w hw hz
            by_cases hwe : w = v
            · subst hwe; rw [List.getElem?_set_self (by omega)]; rfl
            · rw [List.getElem?_set_ne (Ne.symm hwe)]; exact hpres1 w hw hz
          · intro k hk1 hki hkt hkv
            by_cases hke : k = i
            · subst hke
              have heq : (s.tmp[k]?.getD 0#32).toNat / 2 = v := by
                rw [List.getElem?_eq_getElem hi_tmp, Option.getD_some]
              rw [heq, List.getElem?_set_self (by omega)]; rfl
            · by_cases hve : (s.tmp[k]?.getD 0#32).toNat / 2 = v
              · rw [hve, List.getElem?_set_self (by omega)]; rfl
              · rw [List.getElem?_set_ne (Ne.symm hve)]
                exact hclr1 k hk1 (by omega) hkt hkv
        · refine hJ () _ ⟨mrk1, hml1, hpres1, ?_, hmem1⟩
          intro k hk1 hki hkt hkv
          by_cases hke : k = i
          · subst hke
            have heq : (s.tmp[k]?.getD 0#32).toNat / 2 = v := by
              rw [List.getElem?_eq_getElem hi_tmp, Option.getD_some]
            omega
          · exact hclr1 k hk1 (by omega) hkt hkv
    · have hclr_all : ∀ k, 1 ≤ k → k < s.tmp_len → (s.tmp[k]?.getD 0#32).toNat / 2 < c.mv →
          mrk1[(s.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#8 = 0#8 :=
        fun k hk1 hkt hkv => hclr1 k hk1 (by omega) hkt hkv
      refine wp_loop_group
        (fun r2 (jv, ()) m2 => ∃ j mrk2,
          trail_from.toNat ≤ j ∧ j ≤ max trail_from.toNat s.trail_end ∧
          r2 = max trail_from.toNat s.trail_end - j ∧ jv = BitVec.ofNat 64 j ∧
          mrk2.length = c.mv ∧
          (∀ v < c.mv, s.mrk[v]?.getD 0#8 = 0#8 → mrk2[v]?.getD 0#8 = 0#8) ∧
          (∀ k, 1 ≤ k → k < s.tmp_len → (s.tmp[k]?.getD 0#32).toNat / 2 < c.mv →
            mrk2[(s.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#8 = 0#8) ∧
          (∀ k, trail_from.toNat ≤ k → k < j → k < s.trail_end →
            (s.trl[k]?.getD 0#32).toNat / 2 < c.mv →
            mrk2[(s.trl[k]?.getD 0#32).toNat / 2]?.getD 0#8 = 0#8) ∧
          (ArenaMem c { s with mrk := mrk2 } ⋆ R) m2) ?_ ?_
      · rintro L2 r2 ⟨jv, ⟨⟩⟩ m2 ih2
          ⟨j, mrk2, hjlo, hjhi, rfl, rfl, hml2, hpres2, hclrt2, hclrr2, hmem2⟩
        wp_unfold
        have hte_le := hlen.trail_end_le
        have hj64 : j < 2 ^ 64 := by have := trail_from.isLt; omega
        refine ⟨_, load_arena_trail_end hmem2, ?_⟩
        rw [bv_ult_eq hj64 (by dsimp; omega)]
        simp only [decide_eq_true_eq, decide_eq_false_iff_not]
        refine ⟨fun hjlt => ?_, fun hjge => ?_⟩
        · rw [bv64_mul4_nat]
          have hj_trl : j < s.trl.length := by rw [hlen.trl_len]; omega
          refine ⟨_, load_arena_trl (s := { s with mrk := mrk2 }) hj_trl hmem2, ?_⟩
          let tv := (s.trl[j]'hj_trl).toNat / 2
          have htv_eq : ((s.trl[j]'hj_trl) >>> 1).setWidth 64 = BitVec.ofNat 64 tv := by
            rw [bv32_zext64_eq, bv32_lshr_1]
          have htv64 : tv < 2 ^ 64 := by have := (s.trl[j]'hj_trl).isLt; omega
          refine wp_join_group
            (fun () m3 => ∃ mrk3,
              mrk3.length = c.mv ∧
              (∀ w < c.mv, s.mrk[w]?.getD 0#8 = 0#8 → mrk3[w]?.getD 0#8 = 0#8) ∧
              (∀ k, 1 ≤ k → k < s.tmp_len → (s.tmp[k]?.getD 0#32).toNat / 2 < c.mv →
                mrk3[(s.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#8 = 0#8) ∧
              (∀ k, trail_from.toNat ≤ k → k < j + 1 → k < s.trail_end →
                (s.trl[k]?.getD 0#32).toNat / 2 < c.mv →
                mrk3[(s.trl[k]?.getD 0#32).toNat / 2]?.getD 0#8 = 0#8) ∧
              (ArenaMem c { s with mrk := mrk3 } ⋆ R) m3) ?_ ?_
          · rintro _ ⟨⟩ m3 ⟨mrk3, hml3, hpres3, hclrt3, hclrr3, hmem3⟩
            wp_unfold
            rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, bv_add_ofNat]
            exact ih2 (max trail_from.toNat s.trail_end - (j + 1)) _ _ (by omega)
              ⟨j + 1, mrk3, by omega, by omega, rfl, rfl, hml3, hpres3, hclrt3, hclrr3, hmem3⟩
          · intro J hJ; wp_unfold
            rw [htv_eq, bv_ult_eq htv64 (by omega)]
            simp only [decide_eq_true_eq, decide_eq_false_iff_not]
            refine ⟨fun htvlt => ?_, fun htvge => ?_⟩
            · rw [trunc32_8_zero]
              obtain ⟨oks, hms⟩ := store_arena_mrk (i := tv) 0#8 (by simp [hml2]; exact htvlt) hmem2
              refine ⟨oks, hJ () _ ⟨mrk2.set tv 0#8, by simp [hml2], ?_, ?_, ?_, hms⟩⟩
              · intro w hw hz
                by_cases hwe : w = tv
                · subst hwe; rw [List.getElem?_set_self (by omega)]; rfl
                · rw [List.getElem?_set_ne (Ne.symm hwe)]; exact hpres2 w hw hz
              · intro k hk1 hkt hkv
                by_cases hve : (s.tmp[k]?.getD 0#32).toNat / 2 = tv
                · rw [hve, List.getElem?_set_self (by omega)]; rfl
                · rw [List.getElem?_set_ne (Ne.symm hve)]; exact hclrt2 k hk1 hkt hkv
              · intro k hklo hkj hkt hkv
                by_cases hke : k = j
                · subst hke
                  have heq : (s.trl[k]?.getD 0#32).toNat / 2 = tv := by
                    rw [List.getElem?_eq_getElem hj_trl, Option.getD_some]
                  rw [heq, List.getElem?_set_self (by omega)]; rfl
                · by_cases hve : (s.trl[k]?.getD 0#32).toNat / 2 = tv
                  · rw [hve, List.getElem?_set_self (by omega)]; rfl
                  · rw [List.getElem?_set_ne (Ne.symm hve)]
                    exact hclrr2 k hklo (by omega) hkt hkv
            · refine hJ () _ ⟨mrk2, hml2, hpres2, hclrt2, ?_, hmem2⟩
              intro k hklo hkj hkt hkv
              by_cases hke : k = j
              · subst hke
                have heq : (s.trl[k]?.getD 0#32).toNat / 2 = tv := by
                  rw [List.getElem?_eq_getElem hj_trl, Option.getD_some]
                omega
              · exact hclrr2 k hklo (by omega) hkt hkv
        · exact hQ mrk2 m2 hml2 hpres2 hclrt2
            (fun k hklo hkt hkv => hclrr2 k hklo (by omega) hkt hkv) hmem2
      · intro L2 hL2; wp_unfold
        exact hL2 (max trail_from.toNat s.trail_end - trail_from.toNat) _ _
          ⟨trail_from.toNat, mrk1, Nat.le_refl _, Nat.le_max_left _ _, rfl,
            (bv_ofNat_toNat_eq trail_from).symm, hml1, hpres1, hclr_all,
            fun _ h1 h2 => by omega, hmem1⟩
  · intro L hL; wp_unfold
    exact hL (max 1 s.tmp_len - 1) _ m
      ⟨1, s.mrk, Nat.le_refl _, Nat.le_max_left _ _, rfl, rfl, hlen.mrk_len,
        fun _ _ h => h, fun _ h1 h2 => by omega, hm⟩

/-! ## 3. `kissat_decide` specification and `Func.wp` proof -/

/-- Specification of `kissat_decide(h)`. -/
def kissatDecideSpec : Spec [i64] [i64] :=
  fun (h, ()) m Q _ =>
    ∃ (c : ArenaCfg) (F0 : CNF Nat) (s : ArenaState) (R : Mem 64 → Prop),
      h = c.hdr ∧ SolverInv c F0 s ∧ (ArenaMem c s ⋆ R) m ∧
      ∀ r s' m',
        SolverInv c F0 s' →
        s'.d_cur = s.d_cur → s'.d_val = s.d_val → s'.fuel = s.fuel →
        (r = 0#64 ∨ r = 1#64) →
        (r = 0#64 → s' = s) →
        ((∀ v < c.mv, s.vals[2 * v]?.getD 0#8 ≠ 0#8) → r = 0#64 ∧ s' = s) →
        (ArenaMem c s' ⋆ R) m' → Q (r, ()) m'

theorem kissat_decide_wp (Γ : Env)
    (hAssign : ∀ args m Q X, kissatAssignSpec args m Q X →
      Γ "kissat_assign" [i64, i32, i32] [] args m Q X) :
    ∀ args m Q X, kissatDecideSpec args m Q X →
      Func.wp Γ kissat_decide_body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hm, hQ⟩
  unfold Func.wp kissat_decide_body; wp_unfold
  have hmv := c.hmv; unfold dimacsBound at hmv
  have hcore := hinv.core; have hlen := hcore.lengths
  refine ⟨_, load_arena_values hm, _, load_arena_mv hm, ?_⟩
  refine wp_loop_group
    (fun r (vv, ()) ml => ∃ v,
      v ≤ c.mv ∧ r = c.mv - v ∧ vv = BitVec.ofNat 64 v ∧
      (∀ w < v, s.vals[2 * w]?.getD 0#8 ≠ 0#8) ∧
      (ArenaMem c s ⋆ R) ml) ?_ ?_
  · rintro L r ⟨vv, ⟨⟩⟩ ml ih ⟨v, hvle, rfl, rfl, hall_nz, hml⟩
    wp_unfold
    rw [bv_ult_eq (by omega) (by omega)]
    simp only [decide_eq_true_eq, decide_eq_false_iff_not]
    refine ⟨fun hvlt => ?_, fun hvge => ?_⟩
    · rw [bv_shl_sext1]
      have h2v : 2 * v < s.vals.length := by rw [hlen.vals_len]; omega
      refine ⟨_, load_arena_vals h2v hml, ?_⟩
      have hval_dom : s.vals[2 * v]'h2v = 0#8 ∨ s.vals[2 * v]'h2v = 1#8 ∨
          s.vals[2 * v]'h2v = 0xFF#8 := by
        have := hcore.vals_domain (2 * v) (by omega)
        rwa [List.getElem?_eq_getElem h2v, Option.getD_some] at this
      rw [show (BitVec.setWidth 8 (0 : BitVec 32)).signExtend 32 = 0#32 from rfl,
        i8_vals_eq0 hval_dom]
      refine ⟨fun hz => ?_, fun hnz => ?_⟩
      · have hz_get : s.vals[2 * v]?.getD 0#8 = 0#8 := by
          rw [List.getElem?_eq_getElem h2v, Option.getD_some]; exact hz
        have hte_lt : s.trail_end < c.mv :=
          hcore.trail_end_lt_of_unassigned (by omega : 2 * v < 2 * c.mv) hz_get
        have hcur_le := hcore.cur_level_le
        refine ⟨_, load_arena_cur_level hml, ?_⟩
        rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, bv_add_ofNat]
        obtain ⟨okc, hmc⟩ := store_arena_cur_level (s.cur_level + 1) hml
        refine ⟨okc, ?_⟩
        let s1 : ArenaState := { s with cur_level := s.cur_level + 1 }
        have hs1_len : s1.LengthsOk c :=
          ⟨hlen.vals_len, hlen.mrk_len, hlen.lvl_len, hlen.rsns_len, hlen.trl_len,
            hlen.tmp_len_arr, hlen.wh_len, hlen.cls_len, hlen.wn_len, hlen.lpool_len,
            hlen.lit_len_le, hlen.num_clauses_le, hlen.trail_end_le, hlen.propagated_le,
            by dsimp [s1]; omega, hlen.tmp_cnt_lt, hlen.tmp_len_lt⟩
        rw [bv64_shl1_or1_trunc32 (by omega)]
        apply wp_call_of_spec; apply hAssign
        let lit : BitVec 32 := BitVec.ofNat 32 (2 * v + 1)
        have hlit_nat : lit.toNat = 2 * v + 1 := bv32_ofNat_toNat (by omega)
        have hnot_oob : ¬ (c.mv ≤ lit.toNat / 2 ∨ c.mv ≤ s1.trail_end) := by
          dsimp [s1]; omega
        refine ⟨c, s1, R, rfl, hs1_len, hmc, ?_⟩
        simp only [Arg.val_var, Arg.val_imm]
        change if c.mv ≤ lit.toNat / 2 ∨ c.mv ≤ s1.trail_end then _ else _
        simp only [hnot_oob, ↓reduceIte]
        intro mf _ hmf
        wp_unfold
        have hz_lit : s.vals[lit.toNat]?.getD 0#8 = 0#8 := by
          rw [hcore.vals_zero_iff (by omega : lit.toNat < 2 * c.mv)]
          have h0 := (hcore.vals_zero_iff (by omega : 2 * v < 2 * c.mv)).mp hz_get
          intro i hi; have := h0 i hi; omega
        have hcore' := decide_assign_preserves_core hcore (by omega : lit.toNat < 2 * c.mv) hz_lit
        exact hQ 1#64 _ mf ⟨hcore', hinv.marks⟩ rfl rfl rfl (Or.inr rfl)
          (fun h => by cases h)
          (fun hall => absurd hz_get (hall v hvlt)) hmf
      · rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, bv_add_ofNat]
        refine ih (c.mv - (v + 1)) _ _ (by omega) ⟨v + 1, by omega, rfl, rfl, ?_, hml⟩
        intro w hw
        by_cases hwv : w = v
        · subst hwv; rw [List.getElem?_eq_getElem h2v, Option.getD_some]; exact hnz
        · exact hall_nz w (by omega)
    · exact hQ 0#64 s ml hinv rfl rfl rfl (Or.inl rfl) (fun _ => rfl)
        (fun _ => ⟨rfl, rfl⟩) hml
  · intro L hL; wp_unfold
    exact hL c.mv _ m ⟨0, Nat.zero_le _, by simp, rfl, fun _ h => by omega, hm⟩

/-! ## 4. `kissat_analyze_clause` specification and `Func.wp` proof -/

/-- Specification of `kissat_analyze_clause(h, cid, skip_var)`. -/
def kissatAnalyzeClauseSpec : Spec [i64, i32, i32] [.bool] :=
  fun (h, cid, skip_var, ()) m Q _ =>
    ∃ (c : ArenaCfg) (s : ArenaState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ s.tmp_len ≤ c.mv ∧ s.tmp_cnt + c.mv < 2 ^ 64 ∧
      (ArenaMem c s ⋆ R) m ∧
      ∀ (ok : Bool) (mrk' : List (BitVec 8)) (tmp' : List (BitVec 32))
        (tc' tl' : Nat) (m' : Mem 64),
        let s' : ArenaState :=
          { s with mrk := mrk', tmp := tmp', tmp_cnt := tc', tmp_len := tl' }
        s'.LengthsOk c →
        s.tmp_len ≤ tl' → tl' ≤ c.mv →
        s.tmp_cnt ≤ tc' →
        (∀ v < c.mv, s.mrk[v]?.getD 0#8 ≠ 0#8 → mrk'[v]?.getD 0#8 = s.mrk[v]?.getD 0#8) →
        (∀ k < s.tmp_len, tmp'[k]? = s.tmp[k]?) →
        (∀ v < c.mv, s.mrk[v]?.getD 0#8 = 0#8 → mrk'[v]?.getD 0#8 ≠ 0#8 →
          ∃ l ∈ clauseLits s cid.toNat,
            l / 2 = v ∧ v ≠ skip_var.toNat ∧
            0 < (s.lvl[v]?.getD 0#32).toNat ∧ (s.lvl[v]?.getD 0#32).toNat ≤ s.cur_level) →
        (∀ j, s.tmp_len ≤ j → j < tl' →
          let l := (tmp'[j]?.getD 0#32).toNat
          l ∈ clauseLits s cid.toNat ∧ l < 2 * c.mv ∧ l / 2 ≠ skip_var.toNat ∧
          0 < (s.lvl[l / 2]?.getD 0#32).toNat ∧ (s.lvl[l / 2]?.getD 0#32).toNat < s.cur_level ∧
          mrk'[l / 2]?.getD 0#8 ≠ 0#8) →
        tc' - s.tmp_cnt =
          ((List.range c.mv).filter fun v =>
            decide (s.mrk[v]?.getD 0#8 = 0#8) &&
            decide (mrk'[v]?.getD 0#8 ≠ 0#8) &&
            decide ((s.lvl[v]?.getD 0#32).toNat = s.cur_level)).length →
        (ok = true →
          cid.toNat < s.num_clauses ∧
          clauseOff s cid.toNat + clauseSize s cid.toNat ≤ s.lit_len ∧
          ∀ l ∈ clauseLits s cid.toNat,
            l / 2 < c.mv ∧
            (l / 2 ≠ skip_var.toNat →
              (0 < (s.lvl[l / 2]?.getD 0#32).toNat → mrk'[l / 2]?.getD 0#8 ≠ 0#8) ∧
              (s.mrk[l / 2]?.getD 0#8 = 0#8 →
                (s.lvl[l / 2]?.getD 0#32).toNat ≤ s.cur_level ∧
                (0 < (s.lvl[l / 2]?.getD 0#32).toNat →
                  (s.lvl[l / 2]?.getD 0#32).toNat < s.cur_level →
                  ∃ j, s.tmp_len ≤ j ∧ j < tl' ∧ (tmp'[j]?.getD 0#32).toNat / 2 = l / 2)))) →
        (ArenaMem c s' ⋆ R) m' → Q (ok, ()) m'

theorem kissat_analyze_clause_wp (Γ : Env) :
    ∀ args m Q X, kissatAnalyzeClauseSpec args m Q X →
      Func.wp Γ kissat_analyze_clause_body args m Q X := by
  rintro ⟨h, cid, skip_var, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, htl_mv, htc_fit, hm, hQ⟩
  unfold Func.wp kissat_analyze_clause_body; wp_unfold
  have hmv := c.hmv; have hmc := c.hmax_c; have hlc := c.hlcap
  unfold dimacsBound at hmv hmc hlc
  have hnc_le := hlen.num_clauses_le; have hll_le := hlen.lit_len_le
  have hcid64 : cid.toNat < 2 ^ 64 := by have := cid.isLt; omega
  have hret_same : Q (false, ()) m := by
    refine hQ false s.mrk s.tmp s.tmp_cnt s.tmp_len m hlen (Nat.le_refl _) htl_mv (Nat.le_refl _)
      (fun _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ h0 hnz => absurd h0 hnz)
      (fun _ h1 h2 => by omega) ?_ (fun hc => by cases hc) hm
    rw [Nat.sub_self, filter_length_eq_zero_of_false]
    intro v _; by_cases h0 : s.mrk[v]?.getD 0#8 = 0#8 <;> simp [h0]
  refine ⟨_, load_arena_num_clauses hm, ?_⟩
  rw [bv32_zext64_eq, bv_ule_eq (by omega) hcid64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  refine ⟨fun _ => hret_same, fun hcid_lt => ?_⟩
  refine ⟨_, load_arena_clauses hm, ?_⟩
  rw [bv64_mul16_nat]
  have hc0 : 4 * cid.toNat < s.cls.length := by rw [hlen.cls_len]; omega
  have hc1 : 4 * cid.toNat + 1 < s.cls.length := by rw [hlen.cls_len]; omega
  refine ⟨_, load_arena_cls hc0 hm, ?_⟩
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, ptr_add_ofNat,
    show 4 * (4 * cid.toNat) + 4 = 4 * (4 * cid.toNat + 1) by omega]
  refine ⟨_, load_arena_cls hc1 hm, ?_⟩
  generalize hoff_def : s.cls[4 * cid.toNat]'hc0 = off_bv
  generalize hsz_def : s.cls[4 * cid.toNat + 1]'hc1 = sz_bv
  have hoff_eq : clauseOff s cid.toNat = off_bv.toNat := by
    unfold clauseOff; rw [List.getElem?_eq_getElem hc0, Option.getD_some, hoff_def]
  have hsz_eq : clauseSize s cid.toNat = sz_bv.toNat := by
    unfold clauseSize; rw [List.getElem?_eq_getElem hc1, Option.getD_some, hsz_def]
  have hoff64 : off_bv.toNat < 2 ^ 64 := by have := off_bv.isLt; omega
  have hsz64 : sz_bv.toNat < 2 ^ 64 := by have := sz_bv.isLt; omega
  refine ⟨_, load_arena_lit_len hm, ?_⟩
  rw [bv32_zext64_eq, bv32_zext64_eq, bv_ult_eq (by omega) hoff64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  refine ⟨fun _ => hret_same, fun hoff_le => ?_⟩
  refine ⟨_, load_arena_lit_len hm, ?_⟩
  rw [bv_sub_ofNat (by omega) (by omega), bv_ult_eq (by omega) hsz64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  refine ⟨fun _ => hret_same, fun hsz_le => ?_⟩
  have hbd : clauseOff s cid.toNat + clauseSize s cid.toNat ≤ s.lit_len := by
    rw [hoff_eq, hsz_eq]; omega
  have hbd_lp : clauseOff s cid.toNat + clauseSize s cid.toNat ≤ s.lpool.length := by
    rw [hlen.lpool_len]; omega
  have hoff_sz_lp : off_bv.toNat + sz_bv.toNat ≤ s.lpool.length := by
    rw [← hoff_eq, ← hsz_eq]; exact hbd_lp
  refine ⟨_, load_arena_lit_pool hm, _, load_arena_mark hm, _, load_arena_level hm,
    _, load_arena_tmp_lits hm, _, load_arena_cur_level hm, ?_⟩
  let LoopInv (i : Nat) (mrk' : List (BitVec 8)) (tmp' : List (BitVec 32))
      (tc' tl' : Nat) : Prop :=
    i ≤ sz_bv.toNat ∧
    mrk'.length = c.mv ∧ tmp'.length = c.mv ∧
    s.tmp_len ≤ tl' ∧ tl' ≤ c.mv ∧ s.tmp_cnt ≤ tc' ∧
    (∀ v < c.mv, s.mrk[v]?.getD 0#8 ≠ 0#8 → mrk'[v]?.getD 0#8 = s.mrk[v]?.getD 0#8) ∧
    (∀ k < s.tmp_len, tmp'[k]? = s.tmp[k]?) ∧
    (∀ v < c.mv, s.mrk[v]?.getD 0#8 = 0#8 → mrk'[v]?.getD 0#8 ≠ 0#8 →
      ∃ l ∈ clauseLits s cid.toNat,
        l / 2 = v ∧ v ≠ skip_var.toNat ∧
        0 < (s.lvl[v]?.getD 0#32).toNat ∧ (s.lvl[v]?.getD 0#32).toNat ≤ s.cur_level) ∧
    (∀ v < c.mv, s.mrk[v]?.getD 0#8 = 0#8 → mrk'[v]?.getD 0#8 ≠ 0#8 →
      (s.lvl[v]?.getD 0#32).toNat < s.cur_level →
      ∃ j, s.tmp_len ≤ j ∧ j < tl' ∧ (tmp'[j]?.getD 0#32).toNat / 2 = v) ∧
    (∀ j, s.tmp_len ≤ j → j < tl' →
      let l := (tmp'[j]?.getD 0#32).toNat
      l ∈ clauseLits s cid.toNat ∧ l < 2 * c.mv ∧ l / 2 ≠ skip_var.toNat ∧
      0 < (s.lvl[l / 2]?.getD 0#32).toNat ∧ (s.lvl[l / 2]?.getD 0#32).toNat < s.cur_level ∧
      mrk'[l / 2]?.getD 0#8 ≠ 0#8) ∧
    tc' - s.tmp_cnt =
      ((List.range c.mv).filter fun v =>
        decide (s.mrk[v]?.getD 0#8 = 0#8) &&
        decide (mrk'[v]?.getD 0#8 ≠ 0#8) &&
        decide ((s.lvl[v]?.getD 0#32).toNat = s.cur_level)).length ∧
    (∀ k < i,
      let l := (s.lpool[off_bv.toNat + k]?.getD 0#32).toNat
      l / 2 < c.mv ∧
      (l / 2 ≠ skip_var.toNat →
        (0 < (s.lvl[l / 2]?.getD 0#32).toNat → mrk'[l / 2]?.getD 0#8 ≠ 0#8) ∧
        (s.mrk[l / 2]?.getD 0#8 = 0#8 →
          (s.lvl[l / 2]?.getD 0#32).toNat ≤ s.cur_level ∧
          (0 < (s.lvl[l / 2]?.getD 0#32).toNat →
            (s.lvl[l / 2]?.getD 0#32).toNat < s.cur_level →
            ∃ j, s.tmp_len ≤ j ∧ j < tl' ∧ (tmp'[j]?.getD 0#32).toNat / 2 = l / 2))))
  have hret_false : ∀ i mrk' tmp' tc' tl' ml, LoopInv i mrk' tmp' tc' tl' →
      (ArenaMem c { s with mrk := mrk', tmp := tmp', tmp_cnt := tc', tmp_len := tl' } ⋆ R) ml →
      Q (false, ()) ml := by
    intro i mrk' tmp' tc' tl' ml hli hml
    obtain ⟨_, hml_len, htl_len, htl_ge, htl_le, htc_ge, hmpres, htpres,
      hnewm, _, hnewt, hcnt, _⟩ := hli
    have hcnt_le : tc' - s.tmp_cnt ≤ c.mv := by
      rw [hcnt]; exact Nat.le_trans (List.length_filter_le _ _) (by simp)
    exact hQ false mrk' tmp' tc' tl' ml
      ⟨hlen.vals_len, hml_len, hlen.lvl_len, hlen.rsns_len, hlen.trl_len, htl_len,
        hlen.wh_len, hlen.cls_len, hlen.wn_len, hlen.lpool_len, hlen.lit_len_le,
        hlen.num_clauses_le, hlen.trail_end_le, hlen.propagated_le, hlen.cur_level_lt,
        by dsimp; omega, by dsimp; omega⟩
      htl_ge htl_le htc_ge hmpres htpres hnewm hnewt hcnt (fun hc => by cases hc) hml
  refine wp_loop_group
    (fun r (iv, ()) ml => ∃ i mrk' tmp' tc' tl',
      r = sz_bv.toNat - i ∧ iv = BitVec.ofNat 64 i ∧
      LoopInv i mrk' tmp' tc' tl' ∧
      (ArenaMem c { s with mrk := mrk', tmp := tmp', tmp_cnt := tc', tmp_len := tl' } ⋆ R) ml)
    ?_ ?_
  · rintro L r ⟨iv, ⟨⟩⟩ ml ih ⟨i, mrk', tmp', tc', tl', rfl, rfl, hli, hml⟩
    obtain ⟨hile, hml_len, htl_len, htl_ge, htl_le, htc_ge, hmpres, htpres, hnewm, hnewlow,
      hnewt, hcnt, hdone⟩ := hli
    have hli' : LoopInv i mrk' tmp' tc' tl' :=
      ⟨hile, hml_len, htl_len, htl_ge, htl_le, htc_ge, hmpres, htpres, hnewm, hnewlow,
        hnewt, hcnt, hdone⟩
    wp_unfold
    rw [bv_ult_eq (by omega) hsz64]
    simp only [decide_eq_true_eq, decide_eq_false_iff_not]
    refine ⟨fun hilt => ?_, fun hige => ?_⟩
    · rw [show BitVec.ofNat 64 off_bv.toNat * 4#64 = BitVec.ofNat 64 (4 * off_bv.toNat) by grind,
        show BitVec.ofNat 64 i * 4#64 = BitVec.ofNat 64 (4 * i) by grind,
        ptr_add_ofNat, ← Nat.mul_add]
      have hi_lp : off_bv.toNat + i < s.lpool.length := by omega
      let st : ArenaState := { s with mrk := mrk', tmp := tmp', tmp_cnt := tc', tmp_len := tl' }
      refine ⟨_, load_arena_lpool (s := st) hi_lp hml, ?_⟩
      let l_bv := s.lpool[off_bv.toNat + i]'hi_lp
      have hl_get : (s.lpool[off_bv.toNat + i]?.getD 0#32).toNat = l_bv.toNat := by
        rw [List.getElem?_eq_getElem hi_lp, Option.getD_some]
      have hl_mem : l_bv.toNat ∈ clauseLits s cid.toNat :=
        (mem_clauseLits_iff hbd_lp).mpr ⟨i, by rw [hsz_eq]; exact hilt, by simp [l_bv, hoff_eq]⟩
      let v := l_bv.toNat / 2
      have hv_eq : (l_bv >>> 1).setWidth 64 = BitVec.ofNat 64 v := by
        rw [bv32_zext64_eq, bv32_lshr_1]
      have hv64 : v < 2 ^ 64 := by have := l_bv.isLt; omega
      refine ⟨_, load_arena_mv hml, ?_⟩
      rw [hv_eq, bv_ule_eq (by omega) hv64]
      simp only [decide_eq_true_eq, decide_eq_false_iff_not]
      refine ⟨fun _ => hret_false i mrk' tmp' tc' tl' ml hli' hml, fun hvlt_n => ?_⟩
      have hvlt : v < c.mv := by omega
      refine wp_join_group
        (fun () m2 => ∃ mrk2 tmp2 tc2 tl2,
          LoopInv (i + 1) mrk2 tmp2 tc2 tl2 ∧
          (ArenaMem c { s with mrk := mrk2, tmp := tmp2, tmp_cnt := tc2, tmp_len := tl2 } ⋆ R) m2)
        ?_ ?_
      · rintro _ ⟨⟩ m2 ⟨mrk2, tmp2, tc2, tl2, hli2, hm2⟩
        wp_unfold
        rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, bv_add_ofNat]
        exact ih (sz_bv.toNat - (i + 1)) _ _ (by omega)
          ⟨i + 1, mrk2, tmp2, tc2, tl2, rfl, rfl, hli2, hm2⟩
      · intro J hJ; wp_unfold
        have hstep_same :
            (v = skip_var.toNat ∨
              (v ≠ skip_var.toNat ∧
                (0 < (s.lvl[v]?.getD 0#32).toNat → mrk'[v]?.getD 0#8 ≠ 0#8) ∧
                (s.mrk[v]?.getD 0#8 = 0#8 →
                  (s.lvl[v]?.getD 0#32).toNat ≤ s.cur_level ∧
                  (0 < (s.lvl[v]?.getD 0#32).toNat →
                    (s.lvl[v]?.getD 0#32).toNat < s.cur_level →
                    ∃ j, s.tmp_len ≤ j ∧ j < tl' ∧ (tmp'[j]?.getD 0#32).toNat / 2 = v)))) →
            J () ml := fun hcur => by
          refine hJ () ml ⟨mrk', tmp', tc', tl',
            ⟨by omega, hml_len, htl_len, htl_ge, htl_le, htc_ge, hmpres, htpres, hnewm, hnewlow,
              hnewt, hcnt, ?_⟩, hml⟩
          intro k hk
          by_cases hki : k = i
          · subst hki; dsimp only; rw [hl_get]
            refine ⟨hvlt, fun hne => ?_⟩
            rcases hcur with heq | ⟨_, h1, h2⟩
            · exact absurd heq hne
            · exact ⟨h1, h2⟩
          · exact hdone k (by omega)
        have hveq_iff : (l_bv >>> 1 = skip_var) ↔ v = skip_var.toNat := by
          constructor
          · intro h; have := congrArg BitVec.toNat h; rwa [bv32_lshr_1] at this
          · intro h; apply BitVec.eq_of_toNat_eq; rw [bv32_lshr_1]; exact h
        rw [hveq_iff]
        refine ⟨fun hne_skip => ?_, fun heq_skip => hstep_same (Or.inl heq_skip)⟩
        rw [hv_eq]
        refine ⟨_, load_arena_mrk (s := st) (i := v) (by simp [st, hml_len]; exact hvlt) hml, ?_⟩
        rw [show ((0 : BitVec 32).setWidth 8).setWidth 32 = 0#32 from rfl, bv8_zext32_eq_zero]
        have hmrk_get : mrk'[v]'(by rw [hml_len]; exact hvlt) = mrk'[v]?.getD 0#8 := by
          rw [List.getElem?_eq_getElem (by rw [hml_len]; exact hvlt), Option.getD_some]
        rw [hmrk_get]
        refine ⟨fun hmrk0 => ?_, fun hmrknz => ?_⟩
        · have hsmrk0 : s.mrk[v]?.getD 0#8 = 0#8 := by
            cases hsnz : s.mrk[v]?.getD 0#8 == 0#8
            · exfalso
              have hne : s.mrk[v]?.getD 0#8 ≠ 0#8 := by simpa using hsnz
              rw [hmpres v hvlt hne] at hmrk0; exact hne hmrk0
            · simpa using hsnz
          rw [show (4#64 : BitVec 64) = 4 from rfl, bv64_mul4_nat]
          refine ⟨_, load_arena_lvl (s := st) (i := v) (by rw [hlen.lvl_len]; exact hvlt) hml, ?_⟩
          generalize hvl_def : s.lvl[v]'(by rw [hlen.lvl_len]; exact hvlt) = vlvl_bv
          have hvlvl_eq : vlvl_bv.toNat = (s.lvl[v]?.getD 0#32).toNat := by
            rw [List.getElem?_eq_getElem (by rw [hlen.lvl_len]; exact hvlt), Option.getD_some,
              hvl_def]
          rw [bv64_trunc32_ofNat hlen.cur_level_lt,
            show vlvl_bv = BitVec.ofNat 32 vlvl_bv.toNat from (bv_ofNat_toNat_eq vlvl_bv).symm,
            bv32_ult_eq hlen.cur_level_lt vlvl_bv.isLt]
          simp only [decide_eq_true_eq, decide_eq_false_iff_not]
          refine ⟨fun _ => hret_false i mrk' tmp' tc' tl' ml hli' hml, fun hvl_le => ?_⟩
          refine wp_unroll_group fun _ hJ1 => ?_; wp_unfold
          rw [show (0 : BitVec 32) = BitVec.ofNat 32 0 from rfl,
            bv32_ult_eq (by decide) vlvl_bv.isLt]
          simp only [decide_eq_true_eq, decide_eq_false_iff_not]
          refine ⟨fun hvl_pos => ?_, fun hvl_zero => hJ1 () ml (by
            wp_unfold
            exact hstep_same (Or.inr ⟨hne_skip, fun hp => by omega,
              fun _ => ⟨by omega, fun hp => by omega⟩⟩))⟩
          refine wp_unroll_group fun _ hJ2 => ?_; wp_unfold
          have hJ2_of : ∀ m', J () m' → _ := fun m' hm' =>
            hJ2 () m' (by wp_unfold; exact hJ1 () m' (by wp_unfold; exact hm'))
          have heq_cl : (BitVec.ofNat 32 vlvl_bv.toNat = BitVec.ofNat 32 s.cur_level) ↔
              vlvl_bv.toNat = s.cur_level := by
            constructor
            · intro h; have := congrArg BitVec.toNat h
              rwa [bv32_ofNat_toNat vlvl_bv.isLt, bv32_ofNat_toNat hlen.cur_level_lt] at this
            · intro h; rw [h]
          rw [heq_cl]
          refine ⟨fun hvl_eq => ?_, fun hvl_ne => ?_⟩
          · rw [trunc32_8_one, bv32_zext64_eq, bv32_lshr_1]
            obtain ⟨okm, hmm⟩ := store_arena_mrk (i := v) 1#8 (by simp [hml_len]; exact hvlt) hml
            refine ⟨okm, _, load_arena_tmp_cnt hmm, ?_⟩
            rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, bv_add_ofNat]
            obtain ⟨oktc, hmtc⟩ := store_arena_tmp_cnt (tc' + 1) hmm
            have hmrk2_get : ∀ w < c.mv,
                (mrk'.set v 1#8)[w]?.getD 0#8 = if w = v then 1#8 else mrk'[w]?.getD 0#8 := by
              intro w hw
              by_cases hwe : w = v
              · subst hwe; rw [List.getElem?_set_self (by omega)]; simp
              · rw [List.getElem?_set_ne (Ne.symm hwe)]; simp [hwe]
            have hcnt2 : tc' + 1 - s.tmp_cnt =
                ((List.range c.mv).filter fun w =>
                  decide (s.mrk[w]?.getD 0#8 = 0#8) &&
                  decide ((mrk'.set v 1#8)[w]?.getD 0#8 ≠ 0#8) &&
                  decide ((s.lvl[w]?.getD 0#32).toNat = s.cur_level)).length := by
              have hflip := filter_length_flip_one
                (fun w => decide (s.mrk[w]?.getD 0#8 = 0#8) &&
                  decide (mrk'[w]?.getD 0#8 ≠ 0#8) &&
                  decide ((s.lvl[w]?.getD 0#32).toNat = s.cur_level))
                (fun w => decide (s.mrk[w]?.getD 0#8 = 0#8) &&
                  decide ((mrk'.set v 1#8)[w]?.getD 0#8 ≠ 0#8) &&
                  decide ((s.lvl[w]?.getD 0#32).toNat = s.cur_level))
                v (List.range c.mv) List.nodup_range (List.mem_range.mpr hvlt)
                (by simp [hmrk0])
                (by simp [hsmrk0, hmrk2_get v hvlt, ← hvlvl_eq, hvl_eq])
                (fun w hw hne => by
                  rw [hmrk2_get w (List.mem_range.mp hw), ite_eq_right hne])
              rw [hflip, ← hcnt]; omega
            refine ⟨oktc, hJ2_of _ (hJ () _ ⟨mrk'.set v 1#8, tmp', tc' + 1, tl',
              ⟨by omega, by simp [hml_len], htl_len, htl_ge, htl_le, by omega,
                ?_, htpres, ?_, ?_, ?_, hcnt2, ?_⟩, hmtc⟩)⟩
            · intro w hw hnz
              rw [hmrk2_get w hw]
              by_cases hwe : w = v
              · subst hwe; exact absurd hsmrk0 hnz
              · simp [hwe, hmpres w hw hnz]
            · intro w hw hs0 hmnz
              rw [hmrk2_get w hw] at hmnz
              by_cases hwe : w = v
              · subst hwe
                exact ⟨l_bv.toNat, hl_mem, rfl, hne_skip, by omega, by omega⟩
              · simp only [hwe, ↓reduceIte] at hmnz
                exact hnewm w hw hs0 hmnz
            · intro w hw hs0 hmnz hltcl
              rw [hmrk2_get w hw] at hmnz
              by_cases hwe : w = v
              · subst hwe; omega
              · simp only [hwe, ↓reduceIte] at hmnz
                exact hnewlow w hw hs0 hmnz hltcl
            · intro j hj1 hj2
              obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hnewt j hj1 hj2
              refine ⟨h1, h2, h3, h4, h5, ?_⟩
              rw [hmrk2_get _ (by omega)]
              split
              · decide
              · exact h6
            · intro k hk
              by_cases hki : k = i
              · subst hki; dsimp only; rw [hl_get]
                change v < c.mv ∧ (v ≠ skip_var.toNat →
                  (0 < (s.lvl[v]?.getD 0#32).toNat → (mrk'.set v 1#8)[v]?.getD 0#8 ≠ 0#8) ∧
                  (s.mrk[v]?.getD 0#8 = 0#8 →
                    (s.lvl[v]?.getD 0#32).toNat ≤ s.cur_level ∧
                    (0 < (s.lvl[v]?.getD 0#32).toNat →
                      (s.lvl[v]?.getD 0#32).toNat < s.cur_level →
                      ∃ j, s.tmp_len ≤ j ∧ j < tl' ∧ (tmp'[j]?.getD 0#32).toNat / 2 = v)))
                refine ⟨hvlt, fun _ => ⟨fun _ => by rw [hmrk2_get v hvlt]; simp, fun _ =>
                  ⟨by omega, fun _ hlt => by omega⟩⟩⟩
              · obtain ⟨hkv, hkrest⟩ := hdone k (by omega)
                refine ⟨hkv, fun hne => ?_⟩
                obtain ⟨h1, h2⟩ := hkrest hne
                refine ⟨fun hp => ?_, h2⟩
                rw [hmrk2_get _ hkv]
                split
                · decide
                · exact h1 hp
          · refine ⟨_, load_arena_tmp_len hml, _, load_arena_mv hml, ?_⟩
            rw [bv_ule_eq (by omega) (by dsimp; omega)]
            simp only [decide_eq_true_eq, decide_eq_false_iff_not]
            refine ⟨fun _ => hret_false i mrk' tmp' tc' tl' ml hli' hml, fun htl_lt => ?_⟩
            rw [trunc32_8_one, bv32_zext64_eq, bv32_lshr_1]
            obtain ⟨okm, hmm⟩ := store_arena_mrk (i := v) 1#8 (by simp [hml_len]; exact hvlt) hml
            refine ⟨okm, _, load_arena_tmp_len hmm, ?_⟩
            rw [bv64_mul4_nat]
            obtain ⟨okt, hmt⟩ := store_arena_tmp (i := tl') l_bv
              (by simp [htl_len]; omega) hmm
            refine ⟨okt, _, load_arena_tmp_len hmt, ?_⟩
            rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, bv_add_ofNat]
            obtain ⟨oktl, hmtl⟩ := store_arena_tmp_len (tl' + 1) hmt
            have hmrk2_get : ∀ w < c.mv,
                (mrk'.set v 1#8)[w]?.getD 0#8 = if w = v then 1#8 else mrk'[w]?.getD 0#8 := by
              intro w hw
              by_cases hwe : w = v
              · subst hwe; rw [List.getElem?_set_self (by omega)]; simp
              · rw [List.getElem?_set_ne (Ne.symm hwe)]; simp [hwe]
            have hcnt2 : tc' - s.tmp_cnt =
                ((List.range c.mv).filter fun w =>
                  decide (s.mrk[w]?.getD 0#8 = 0#8) &&
                  decide ((mrk'.set v 1#8)[w]?.getD 0#8 ≠ 0#8) &&
                  decide ((s.lvl[w]?.getD 0#32).toNat = s.cur_level)).length := by
              rw [hcnt]; congr 1; apply List.filter_congr; intro w hw
              have hwlt := List.mem_range.mp hw
              rw [hmrk2_get w hwlt]
              by_cases hwe : w = v
              · subst hwe; simp [show (s.lvl[v]?.getD 0#32).toNat ≠ s.cur_level by omega]
              · simp [hwe]
            refine ⟨oktl, hJ2_of _ (hJ () _ ⟨mrk'.set v 1#8, tmp'.set tl' l_bv, tc', tl' + 1,
              ⟨by omega, by simp [hml_len], by simp [htl_len], by omega, by omega, htc_ge,
                ?_, ?_, ?_, ?_, ?_, hcnt2, ?_⟩, hmtl⟩)⟩
            · intro w hw hnz
              rw [hmrk2_get w hw]
              by_cases hwe : w = v
              · subst hwe; exact absurd hsmrk0 hnz
              · simp [hwe, hmpres w hw hnz]
            · intro k hk
              rw [List.getElem?_set_ne (by omega)]; exact htpres k hk
            · intro w hw hs0 hmnz
              rw [hmrk2_get w hw] at hmnz
              by_cases hwe : w = v
              · subst hwe
                exact ⟨l_bv.toNat, hl_mem, rfl, hne_skip, by omega, by omega⟩
              · simp only [hwe, ↓reduceIte] at hmnz; exact hnewm w hw hs0 hmnz
            · intro w hw hs0 hmnz hltcl
              rw [hmrk2_get w hw] at hmnz
              by_cases hwe : w = v
              · subst hwe
                refine ⟨tl', htl_ge, by omega, ?_⟩
                rw [List.getElem?_set_self (by omega)]; rfl
              · simp only [hwe, ↓reduceIte] at hmnz
                obtain ⟨j, hj1, hj2, hjeq⟩ := hnewlow w hw hs0 hmnz hltcl
                exact ⟨j, hj1, by omega, by rw [List.getElem?_set_ne (by omega)]; exact hjeq⟩
            · intro j hj1 hj2
              by_cases hje : j = tl'
              · subst hje
                rw [List.getElem?_set_self (by omega), Option.getD_some]
                change l_bv.toNat ∈ clauseLits s cid.toNat ∧ l_bv.toNat < 2 * c.mv ∧
                  v ≠ skip_var.toNat ∧ 0 < (s.lvl[v]?.getD 0#32).toNat ∧
                  (s.lvl[v]?.getD 0#32).toNat < s.cur_level ∧
                  (mrk'.set v 1#8)[v]?.getD 0#8 ≠ 0#8
                refine ⟨hl_mem, by omega, hne_skip, by omega, by omega, ?_⟩
                rw [hmrk2_get v hvlt]; simp
              · rw [List.getElem?_set_ne (Ne.symm hje)]
                obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hnewt j hj1 (by omega)
                refine ⟨h1, h2, h3, h4, h5, ?_⟩
                rw [hmrk2_get _ (by omega)]
                split
                · decide
                · exact h6
            · intro k hk
              by_cases hki : k = i
              · subst hki; dsimp only; rw [hl_get]
                change v < c.mv ∧ (v ≠ skip_var.toNat →
                  (0 < (s.lvl[v]?.getD 0#32).toNat → (mrk'.set v 1#8)[v]?.getD 0#8 ≠ 0#8) ∧
                  (s.mrk[v]?.getD 0#8 = 0#8 →
                    (s.lvl[v]?.getD 0#32).toNat ≤ s.cur_level ∧
                    (0 < (s.lvl[v]?.getD 0#32).toNat →
                      (s.lvl[v]?.getD 0#32).toNat < s.cur_level →
                      ∃ j, s.tmp_len ≤ j ∧ j < tl' + 1 ∧
                        ((tmp'.set tl' l_bv)[j]?.getD 0#32).toNat / 2 = v)))
                refine ⟨hvlt, fun _ => ⟨fun _ => by rw [hmrk2_get v hvlt]; simp, fun _ =>
                  ⟨by omega, fun _ _ => ⟨tl', htl_ge, by omega,
                    by rw [List.getElem?_set_self (by omega)]; rfl⟩⟩⟩⟩
              · obtain ⟨hkv, hkrest⟩ := hdone k (by omega)
                refine ⟨hkv, fun hne => ?_⟩
                obtain ⟨h1, h2⟩ := hkrest hne
                refine ⟨fun hp => ?_, fun hs0 => ?_⟩
                · rw [hmrk2_get _ hkv]
                  split
                  · decide
                  · exact h1 hp
                · obtain ⟨hle, hlow⟩ := h2 hs0
                  refine ⟨hle, fun hp hlt => ?_⟩
                  obtain ⟨j, hj1, hj2, hjeq⟩ := hlow hp hlt
                  exact ⟨j, hj1, by omega, by rw [List.getElem?_set_ne (by omega)]; exact hjeq⟩
        · refine hstep_same (Or.inr ⟨hne_skip, fun _ => hmrknz, fun hs0 => ?_⟩)
          obtain ⟨_, _, _, _, _, hle⟩ := hnewm v hvlt hs0 hmrknz
          exact ⟨hle, fun _ hlt => hnewlow v hvlt hs0 hmrknz hlt⟩
    · have hieq : i = sz_bv.toNat := by omega
      subst hieq
      have hcnt_le : tc' - s.tmp_cnt ≤ c.mv := by
        rw [hcnt]; exact Nat.le_trans (List.length_filter_le _ _) (by simp)
      refine hQ true mrk' tmp' tc' tl' ml
        ⟨hlen.vals_len, hml_len, hlen.lvl_len, hlen.rsns_len, hlen.trl_len, htl_len,
          hlen.wh_len, hlen.cls_len, hlen.wn_len, hlen.lpool_len, hlen.lit_len_le,
          hlen.num_clauses_le, hlen.trail_end_le, hlen.propagated_le, hlen.cur_level_lt,
          by dsimp; omega, by dsimp; omega⟩
        htl_ge htl_le htc_ge hmpres htpres hnewm hnewt hcnt ?_ hml
      intro _
      refine ⟨by omega, hbd, fun l hl => ?_⟩
      obtain ⟨k, hk, hget⟩ := (mem_clauseLits_iff hbd_lp).mp hl
      have hk' : k < sz_bv.toNat := by rwa [hsz_eq] at hk
      have hdk := hdone k hk'
      have hget' : (s.lpool[off_bv.toNat + k]?.getD 0#32).toNat = l := by
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; simpa [hoff_eq] using hget
      simpa [hget'] using hdk
  · intro L hL; wp_unfold
    refine hL sz_bv.toNat _ m ⟨0, s.mrk, s.tmp, s.tmp_cnt, s.tmp_len, by simp, rfl,
      ⟨Nat.zero_le _, hlen.mrk_len, hlen.tmp_len_arr, Nat.le_refl _, htl_mv, Nat.le_refl _,
        fun _ _ _ => rfl, fun _ _ => rfl, fun _ _ h0 hnz => absurd h0 hnz,
        fun _ _ h0 hnz _ => absurd h0 hnz, fun _ h1 h2 => by omega, ?_,
        fun _ h => by omega⟩, hm⟩
    rw [Nat.sub_self, filter_length_eq_zero_of_false]
    intro v _; by_cases h0 : s.mrk[v]?.getD 0#8 = 0#8 <;> simp [h0]

end LeanQbe.T.Examples.Kissat
