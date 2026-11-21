module

public import LeanQbe.T.Examples.Kissat.FullSpec
public import LeanQbe.T.Examples.Kissat.FullAnalyzeLemmas1
public import LeanQbe.T.Examples.Kissat.FullAnalyzeLemmas2
public import LeanQbe.T.Examples.Kissat.FullAnalyzeLemmas3
public import LeanQbe.T.Examples.Kissat.FullAnalyzeLemmas5
public import LeanQbe.T.Examples.Kissat.FullWalkExtLemmas2
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Full` `full_deduce_1uip` Lemmas — Part 1 (Helpers & Resolvent Theory)

Proves:
1. Adapters between `FullAnalyzeSpecs` and canonical `FullSpec1`/`FullSpec2` invariants.
2. Pure 1-UIP resolvent theory (`fullLowerLits`, `fullCurTrailIdxs`, `fullCurLits`,
   `fullActiveResolvent`, `FullLowerInv`, `FullMarksCov`, `FullCurMarksCut`, `res_sz` partition
   identities, and pigeonhole OTFS clause entailment under `res_sz < ant_sz`).
3. Factored state invariants, semantic step lemmas, and exit/clear WP building blocks
   used by `FullDeduce1UipLemmas.lean` (`full_deduce_1uip_wp`, `fullFns[79]?`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.C0Step
open Kraken.Bedrock2.Test
open FullAnalyzeTactics FullAnalyzeHelpers

open scoped FullArenaTactics FullAnalyzeTactics

/-! ## 1. Local `C0Step` helpers -/

section Adapters

namespace Deduce1UipTactics

@[scoped bv_c0] theorem d1_bv32_lshr_1 (x : BitVec 32) : (x >>> 1#32).toNat = x.toNat / 2 :=
  bv32_lshr_1 x

@[scoped bv_c0] theorem d1_bv64_add_0 (x : BitVec 64) : x + 0#64 = x :=
  BitVec.add_zero x

@[scoped bv_c0] theorem d1_i8_sext32_eq0_prop (v : BitVec 8) :
    (v.signExtend 32 = 0#32) = (v = 0#8) := propext (by revert v; decide)

@[scoped bv_c0] theorem d1_u8_zext32_eq0_prop (v : BitVec 8) :
    (v.setWidth 32 = 0#32) = (v = 0#8) := propext (by revert v; decide)

@[scoped bv_c0] theorem d1_bv64_0_mul_4 : (0#64 : BitVec 64) * 4#64 = 0#64 := rfl

@[scoped bv_c0] theorem d1_bv64_1_toNat : (1#64 : BitVec 64).toNat = 1 := rfl

@[scoped bv_c0] theorem d1_bv64_3_toNat : (3#64 : BitVec 64).toNat = 3 := rfl

@[scoped c0_store] theorem d1_store_full_tmp0_off {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) (hi : 0 < s.core.tmp.length)
    (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 (c.pTmp + 0#64) ∧
      (FullMem c { s with core := { s.core with tmp := s.core.tmp.set 0 v } } ⋆ R)
        (storeMem m i32 (c.pTmp + 0#64) v) := by
  simpa using FullArenaTactics.store_full_tmp (i := 0) v hi hm

@[scoped c0_store] theorem d1_store_full_tmp0_mul {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) (hi : 0 < s.core.tmp.length)
    (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 (c.pTmp + 0#64 * 4#64) ∧
      (FullMem c { s with core := { s.core with tmp := s.core.tmp.set 0 v } } ⋆ R)
        (storeMem m i32 (c.pTmp + 0#64 * 4#64) v) := by
  simpa [d1_bv64_0_mul_4] using FullArenaTactics.store_full_tmp (i := 0) v hi hm

end Deduce1UipTactics

open scoped Deduce1UipTactics

private theorem canonCut_to_anaCut {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {k : FullCoreState} (h : FullWitnessCutInv c F0 F_cur cut k) :
    FullAnalyzeSpecs.FullWitnessCutInv c F0 F_cur cut k :=
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

end Adapters

/-! ## 2. Pure 1-UIP resolvent theory, `res_sz` partition & OTFS entailment -/

section ResolventTheory

private theorem nodup_length_le_of_subset {α : Type} [DecidableEq α] :
    ∀ {xs ys : List α}, xs.Nodup → (∀ x ∈ xs, x ∈ ys) → xs.length ≤ ys.length
  | [], _, _, _ => Nat.zero_le _
  | x :: xs, ys, hnd, hsub => by
    rw [List.nodup_cons] at hnd
    have hx : x ∈ ys := hsub x List.mem_cons_self
    have hle := nodup_length_le_of_subset hnd.2 fun y hy =>
      (List.mem_erase_of_ne (by rintro rfl; exact hnd.1 hy)).mpr
        (hsub y (List.mem_cons_of_mem _ hy))
    have hlen := List.length_erase_of_mem hx
    have hpos := List.length_pos_of_mem hx
    simp only [List.length_cons]; omega

private theorem nodup_length_eq_of_bij {xs ys : List Nat} (f : Nat → Nat)
    (hxs : xs.Nodup) (hys : ys.Nodup) (hmap : ∀ x ∈ xs, f x ∈ ys)
    (hinj : ∀ x1 ∈ xs, ∀ x2 ∈ xs, f x1 = f x2 → x1 = x2)
    (hsurj : ∀ y ∈ ys, ∃ x ∈ xs, f x = y) : xs.length = ys.length := by
  have h1 : (xs.map f).length ≤ ys.length :=
    nodup_length_le_of_subset (nodup_map_of_inj hxs hinj) fun y hy => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy; exact hmap x hx
  have h2 : ys.length ≤ (xs.map f).length :=
    nodup_length_le_of_subset hys fun y hy => by
      obtain ⟨x, hx, rfl⟩ := hsurj y hy; exact List.mem_map_of_mem hx
  rw [List.length_map] at h1 h2; omega

private theorem filter_length_add_of_disj {α : Type} (p1 p2 : α → Bool) :
    ∀ (xs : List α), (∀ x ∈ xs, ¬ (p1 x = true ∧ p2 x = true)) →
      (xs.filter fun x => p1 x || p2 x).length = (xs.filter p1).length + (xs.filter p2).length
  | [], _ => rfl
  | x :: xs, hdisj => by
    have htail := filter_length_add_of_disj p1 p2 xs fun y hy => hdisj y (List.mem_cons_of_mem _ hy)
    have hx := hdisj x List.mem_cons_self
    cases hp1 : p1 x <;> cases hp2 : p2 x <;> simp_all <;> omega

private theorem range_succ_filter (n : Nat) (p : Nat → Bool) :
    (List.range (n + 1)).filter p = (List.range n).filter p ++ if p n then [n] else [] := by
  rw [List.range_succ, List.filter_append]; cases hp : p n <;> simp [hp]

private theorem nodup_subset_of_superset_le_length :
    ∀ {xs ys : List Nat}, xs.Nodup → (∀ x ∈ xs, x ∈ ys) → ys.length ≤ xs.length →
      ∀ y ∈ ys, y ∈ xs
  | [], ys, _, _, hle, y, hy => by
    simp only [List.length_nil] at hle
    have hnil : ys = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hnil; cases hy
  | x :: xs, ys, hnd, hsub, hle, y, hy => by
    rw [List.nodup_cons] at hnd
    have hx : x ∈ ys := hsub x List.mem_cons_self
    have hlen := List.length_erase_of_mem hx
    have hpos := List.length_pos_of_mem hx
    have hsub' : ∀ z ∈ xs, z ∈ ys.erase x := fun z hz =>
      (List.mem_erase_of_ne fun he => hnd.1 (by subst he; exact hz)).mpr
        (hsub z (List.mem_cons_of_mem _ hz))
    by_cases hyx : y = x
    · exact hyx ▸ List.mem_cons_self
    · have hy' : y ∈ ys.erase x := (List.mem_erase_of_ne hyx).mpr hy
      exact List.mem_cons_of_mem _
        (nodup_subset_of_superset_le_length hnd.2 hsub' (by simp at hle; omega) y hy')

/-- Lower-level literals accumulated in `tmp[1 ..< tl)`. -/
def fullLowerLits (tmp : List (BitVec 32)) (tl : Nat) : List Nat :=
  ((tmp.drop 1).take (tl - 1)).map BitVec.toNat

/-- Marked current-level trail indices strictly below `idx`. -/
def fullCurTrailIdxs (k : FullCoreState) (mrk : List (BitVec 8)) (idx : Nat) : List Nat :=
  (List.range idx).filter fun j =>
    let v := (k.trl[j]?.getD 0#32).toNat / 2
    decide (mrk[v]?.getD 0#8 ≠ 0#8) &&
      decide ((k.lvl[v]?.getD 0#32).toNat = k.cur_level)

/-- Negated marked current-level trail literals strictly below `idx`. -/
def fullCurLits (k : FullCoreState) (mrk : List (BitVec 8)) (idx : Nat) : List Nat :=
  (fullCurTrailIdxs k mrk idx).map fun j => (k.trl[j]?.getD 0#32).toNat ^^^ 1

/-- Active 1-UIP resolvent clause (`fullLowerLits ++ fullCurLits`). -/
def fullActiveResolvent (k : FullCoreState) (tmp : List (BitVec 32)) (mrk : List (BitVec 8))
    (tl idx : Nat) : List Nat :=
  fullLowerLits tmp tl ++ fullCurLits k mrk idx

/-- Well-formedness and variable distinctness of lower-level literals in `tmp[1 ..< tl)`. -/
def FullLowerInv (c : FullCfg) (k : FullCoreState) (tmp : List (BitVec 32))
    (mrk : List (BitVec 8)) (tl : Nat) : Prop :=
  (∀ j, 1 ≤ j → j < tl →
    let l := (tmp[j]?.getD 0#32).toNat
    l < 2 * k.cur_vars ∧ k.vals[l]?.getD 0#8 = 0xFF#8 ∧
    0 < (k.lvl[l / 2]?.getD 0#32).toNat ∧ (k.lvl[l / 2]?.getD 0#32).toNat < k.cur_level ∧
    mrk[l / 2]?.getD 0#8 ≠ 0#8 ∧ l / 2 < c.max_vars) ∧
  (∀ j1 j2, 1 ≤ j1 → j1 < j2 → j2 < tl →
    (tmp[j1]?.getD 0#32).toNat / 2 ≠ (tmp[j2]?.getD 0#32).toNat / 2)

/-- Coverage of all nonzero entries in `mrk` by `tmp[1 ..< tl)` or `cur_level` trail entries. -/
def FullMarksCov (k : FullCoreState) (tmp : List (BitVec 32)) (mrk : List (BitVec 8))
    (tl : Nat) : Prop :=
  ∀ v < k.cur_vars, mrk[v]?.getD 0#8 ≠ 0#8 →
    (∃ j, 1 ≤ j ∧ j < tl ∧ (tmp[j]?.getD 0#32).toNat / 2 = v) ∨
    (∃ j < k.trail_end, (k.trl[j]?.getD 0#32).toNat / 2 = v ∧
      (k.lvl[v]?.getD 0#32).toNat = k.cur_level)

/-- Every marked `cur_level` trail entry below `bound` lies strictly below `cut`. -/
def FullCurMarksBelow (bound : Nat) (k : FullCoreState) (mrk : List (BitVec 8))
    (cut : Nat) : Prop :=
  ∀ j < bound, mrk[(k.trl[j]?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8 →
    (k.lvl[(k.trl[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = k.cur_level →
    j < cut

theorem mem_fullLowerLits_iff {tmp : List (BitVec 32)} {tl l : Nat}
    (h1 : 1 ≤ tl) (hle : tl ≤ tmp.length) :
    l ∈ fullLowerLits tmp tl ↔ ∃ j, 1 ≤ j ∧ j < tl ∧ (tmp[j]?.getD 0#32).toNat = l := by
  unfold fullLowerLits; rw [List.mem_map]; constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨k, hk, hget⟩ := List.mem_iff_getElem.mp hx
    have hklt : k < tl - 1 := by rw [List.length_take, List.length_drop] at hk; omega
    rw [List.getElem_take, List.getElem_drop] at hget
    refine ⟨1 + k, by omega, by omega, ?_⟩
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some, hget]
  · rintro ⟨j, hj1, hjlt, hget⟩
    have hlt : j - 1 < ((tmp.drop 1).take (tl - 1)).length := by
      rw [List.length_take, List.length_drop]; omega
    refine ⟨tmp[j]'(by omega), ?_, ?_⟩
    · have hmem := List.getElem_mem hlt
      have hidx : 1 + (j - 1) = j := by omega
      simpa [List.getElem_take, List.getElem_drop, Nat.add_comm, hidx] using hmem
    · rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at hget

theorem fullLowerLits_length {tmp : List (BitVec 32)} {tl : Nat}
    (h1 : 1 ≤ tl) (hle : tl ≤ tmp.length) :
    (fullLowerLits tmp tl).length = tl - 1 := by
  unfold fullLowerLits
  rw [List.length_map, List.length_take, List.length_drop]
  omega

theorem fullCurTrailIdxs_succ_true {k : FullCoreState} {mrk : List (BitVec 8)} {idx : Nat}
    (hm : mrk[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8)
    (hl : (k.lvl[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = k.cur_level) :
    fullCurTrailIdxs k mrk (idx + 1) = fullCurTrailIdxs k mrk idx ++ [idx] := by
  unfold fullCurTrailIdxs; rw [range_succ_filter]; simp [hm, hl]

theorem fullCurTrailIdxs_succ_false {k : FullCoreState} {mrk : List (BitVec 8)} {idx : Nat}
    (h : ¬ (mrk[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8 ∧
      (k.lvl[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = k.cur_level)) :
    fullCurTrailIdxs k mrk (idx + 1) = fullCurTrailIdxs k mrk idx := by
  unfold fullCurTrailIdxs; rw [range_succ_filter]
  by_cases h1 : mrk[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8
  · have h2 : (k.lvl[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≠ k.cur_level :=
      fun he => h ⟨h1, he⟩
    simp [h1, h2]
  · simp [h1]

theorem fullCurLits_succ_true {k : FullCoreState} {mrk : List (BitVec 8)} {idx : Nat}
    (hm : mrk[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8)
    (hl : (k.lvl[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = k.cur_level) :
    fullCurLits k mrk (idx + 1) =
      fullCurLits k mrk idx ++ [(k.trl[idx]?.getD 0#32).toNat ^^^ 1] := by
  unfold fullCurLits; rw [fullCurTrailIdxs_succ_true hm hl, List.map_append]; rfl

theorem fullCurLits_succ_false {k : FullCoreState} {mrk : List (BitVec 8)} {idx : Nat}
    (h : ¬ (mrk[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8 ∧
      (k.lvl[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = k.cur_level)) :
    fullCurLits k mrk (idx + 1) = fullCurLits k mrk idx := by
  unfold fullCurLits; rw [fullCurTrailIdxs_succ_false h]

theorem fullCurTrailIdxs_of_marksClear {c : FullCfg} {k : FullCoreState} {s : FullState}
    {idx : Nat} (hk : k = s.core) (hclr : FullLitMarksClear c s)
    (hlen : k.cur_vars ≤ c.max_vars) (hidx : idx ≤ k.trail_end)
    (htrl : ∀ i < k.trail_end, (k.trl[i]?.getD 0#32).toNat < 2 * k.cur_vars) :
    fullCurTrailIdxs k k.mrk idx = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro j hj
  rw [fullCurTrailIdxs, List.mem_filter, List.mem_range] at hj
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hj
  have hj_lt : (k.trl[j]?.getD 0#32).toNat < 2 * k.cur_vars := htrl j (by omega)
  have hm0 : k.mrk[(k.trl[j]?.getD 0#32).toNat / 2]?.getD 0#8 = 0#8 := by
    subst hk; exact hclr.1 _ (by omega)
  exact hj.2.1 hm0

private theorem litNeg_div2 (l : Nat) : (l ^^^ 1) / 2 = l / 2 := by
  simpa [litVar, litNeg] using litVar_litNeg l

theorem fullWitnessCutInv_falsified_lit_unique {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {cut : Nat} {k : FullCoreState}
    (hw : FullWitnessCutInv c F0 F_cur cut k) {l1 l2 : Nat}
    (h1lt : l1 < 2 * k.cur_vars) (h2lt : l2 < 2 * k.cur_vars)
    (hvar : l1 / 2 = l2 / 2) (hf1 : k.vals[l1]?.getD 0#8 = 0xFF#8)
    (hf2 : k.vals[l2]?.getD 0#8 = 0xFF#8) : l1 = l2 := by
  rcases (litVar_eq_iff l1 l2).mp hvar with heq | hneg
  · exact heq
  · obtain ⟨i1, hi1, he1⟩ := (hw.vals_false_iff l1 h1lt).mp hf1
    obtain ⟨i2, hi2, he2⟩ := (hw.vals_false_iff l2 h2lt).mp hf2
    have hvar' : (k.trl[i1]?.getD 0#32).toNat / 2 = (k.trl[i2]?.getD 0#32).toNat / 2 := by
      rw [he1, he2, litNeg_div2, litNeg_div2, hvar]
    have hieq := hw.trail_vars_nodup i1 i2 hi1 hi2 hvar'
    rw [hieq] at he1
    have hx := (congrArg (· ^^^ 1) (he1.symm.trans he2))
    rw [show (l1 ^^^ 1) ^^^ 1 = l1 from litNeg_litNeg l1,
      show (l2 ^^^ 1) ^^^ 1 = l2 from litNeg_litNeg l2] at hx
    exact hx

theorem fullAnalyzeStep_preserves {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {k : FullCoreState} (hlen : k.LengthsOk c)
    (hw : FullWitnessCutInv c F0 F_cur cut k) (LitPred : Nat → Prop)
    {mrk mrk' : List (BitVec 8)} {tmp tmp' : List (BitVec 32)}
    {tc tc' tl tl' idx skip_var : Nat}
    (hidx : idx ≤ k.trail_end) (h1 : 1 ≤ tl) (htl_le : tl ≤ tl') (htl'_cv : tl' ≤ k.cur_vars)
    (ht_len : tmp.length = c.max_vars) (ht'_len : tmp'.length = c.max_vars)
    (htc_eq : tc = (fullCurTrailIdxs k mrk idx).length) (htc_le : tc ≤ tc')
    (hlow : FullLowerInv c k tmp mrk tl) (hcov : FullMarksCov k tmp mrk tl)
    (hcm : FullCurMarksBelow idx k mrk cut)
    (hlits_lt : ∀ q, LitPred q → q < 2 * k.cur_vars)
    (hclause : ∀ q, LitPred q →
      q / 2 = skip_var ∨ ∃ m < idx, (k.trl[m]?.getD 0#32).toNat = q ^^^ 1)
    (hclause_cut : ∀ q, LitPred q → q / 2 ≠ skip_var →
      (k.lvl[q / 2]?.getD 0#32).toNat = k.cur_level →
      ∃ m < cut, (k.trl[m]?.getD 0#32).toNat = q ^^^ 1)
    (hmpres : ∀ v < k.cur_vars, mrk[v]?.getD 0#8 ≠ 0#8 → mrk'[v]?.getD 0#8 = mrk[v]?.getD 0#8)
    (htpres : ∀ j < tl, tmp'[j]? = tmp[j]?)
    (hnewm : ∀ v < k.cur_vars, mrk[v]?.getD 0#8 = 0#8 → mrk'[v]?.getD 0#8 ≠ 0#8 →
      ∃ l, LitPred l ∧ l / 2 = v ∧ v ≠ skip_var ∧
        0 < (k.lvl[v]?.getD 0#32).toNat ∧ (k.lvl[v]?.getD 0#32).toNat ≤ k.cur_level)
    (hnewt : ∀ j, tl ≤ j → j < tl' →
      let l := (tmp'[j]?.getD 0#32).toNat
      LitPred l ∧ l < 2 * k.cur_vars ∧ l / 2 ≠ skip_var ∧ mrk[l / 2]?.getD 0#8 = 0#8 ∧
      0 < (k.lvl[l / 2]?.getD 0#32).toNat ∧ (k.lvl[l / 2]?.getD 0#32).toNat < k.cur_level ∧
      mrk'[l / 2]?.getD 0#8 ≠ 0#8)
    (hnd_new : ∀ j1 j2, tl ≤ j1 → j1 < j2 → j2 < tl' →
      (tmp'[j1]?.getD 0#32).toNat / 2 ≠ (tmp'[j2]?.getD 0#32).toNat / 2)
    (hcnt : tc' - tc =
      ((List.range k.cur_vars).filter fun v =>
        decide (mrk[v]?.getD 0#8 = 0#8) &&
        decide (mrk'[v]?.getD 0#8 ≠ 0#8) &&
        decide ((k.lvl[v]?.getD 0#32).toNat = k.cur_level)).length)
    (hall : ∀ l, LitPred l →
      l / 2 < k.cur_vars ∧
      (l / 2 ≠ skip_var →
        (0 < (k.lvl[l / 2]?.getD 0#32).toNat → mrk'[l / 2]?.getD 0#8 ≠ 0#8) ∧
        (mrk[l / 2]?.getD 0#8 = 0#8 →
          (k.lvl[l / 2]?.getD 0#32).toNat ≤ k.cur_level ∧
          (0 < (k.lvl[l / 2]?.getD 0#32).toNat →
            (k.lvl[l / 2]?.getD 0#32).toNat < k.cur_level →
            ∃ j, tl ≤ j ∧ j < tl' ∧ (tmp'[j]?.getD 0#32).toNat / 2 = l / 2)))) :
    tc' = (fullCurTrailIdxs k mrk' idx).length ∧
    FullLowerInv c k tmp' mrk' tl' ∧
    FullMarksCov k tmp' mrk' tl' ∧
    FullCurMarksBelow idx k mrk' cut ∧
    (∀ l ∈ fullLowerLits tmp tl, l ∈ fullLowerLits tmp' tl') ∧
    (∀ l ∈ fullCurLits k mrk idx, l ∈ fullCurLits k mrk' idx) ∧
    (∀ q, LitPred q →
      q / 2 = skip_var ∨ q ∈ fullActiveResolvent k tmp' mrk' tl' idx ∨
        (cnfOfClauses F_cur).EntailsClause (cnfClause [litNeg q])) := by
  have hcv_le := hlen.cur_vars_le
  have hlow' : FullLowerInv c k tmp' mrk' tl' := by
    refine ⟨fun j hj1 hjlt => ?_, fun j1 j2 hj1 hj12 hj2 => ?_⟩
    · by_cases hjold : j < tl
      · rw [htpres j hjold]
        obtain ⟨h1', h2', h3', h4', h5', h6'⟩ := hlow.1 j hj1 hjold
        exact ⟨h1', h2', h3', h4', by rw [hmpres _ (by omega) h5']; exact h5', h6'⟩
      · obtain ⟨hmem, hlt, hne, _, hpos, hcl, hmk⟩ := hnewt j (by omega) hjlt
        rcases hclause _ hmem with heq | ⟨m, hm, hmeq⟩
        · exact absurd heq hne
        · exact ⟨hlt, (hw.vals_false_iff _ hlt).mpr ⟨m, by omega, hmeq⟩, hpos, hcl, hmk, by omega⟩
    · by_cases hj2_old : j2 < tl
      · rw [htpres j1 (by omega), htpres j2 hj2_old]; exact hlow.2 j1 j2 hj1 hj12 hj2_old
      · by_cases hj1_old : j1 < tl
        · rw [htpres j1 hj1_old]
          have h1' := (hlow.1 j1 hj1 hj1_old).2.2.2.2.1
          have h2' := (hnewt j2 (by omega) hj2).2.2.2.1
          intro heq; rw [heq] at h1'; exact absurd h2' h1'
        · exact hnd_new j1 j2 (by omega) hj12 hj2
  have hcov' : FullMarksCov k tmp' mrk' tl' := by
    intro v hv hnz'
    by_cases hv0 : mrk[v]?.getD 0#8 = 0#8
    · obtain ⟨l, hlmem, rfl, hne, hpos, _⟩ := hnewm v hv hv0 hnz'
      by_cases hcl : (k.lvl[l / 2]?.getD 0#32).toNat = k.cur_level
      · rcases hclause l hlmem with heq | ⟨m, hm, hmeq⟩
        · exact absurd heq hne
        · exact Or.inr ⟨m, by omega, by rw [hmeq]; exact litVar_litNeg l, hcl⟩
      · obtain ⟨_, hrest⟩ := hall l hlmem
        have hle' := ((hrest hne).2 hv0).1
        obtain ⟨j, hj1, hj2, hjeq⟩ := ((hrest hne).2 hv0).2 hpos (by omega)
        exact Or.inl ⟨j, by omega, hj2, hjeq⟩
    · rcases hcov v hv hv0 with ⟨j, hj1, hj2, hjeq⟩ | htrl
      · exact Or.inl ⟨j, hj1, by omega, by rw [htpres j hj2]; exact hjeq⟩
      · exact Or.inr htrl
  have hcm' : FullCurMarksBelow idx k mrk' cut := by
    intro j hj hnz' hcl
    have hj_te : j < k.trail_end := Nat.lt_of_lt_of_le hj hidx
    have hvlt : (k.trl[j]?.getD 0#32).toNat / 2 < k.cur_vars := by
      have := hw.trail_lits_lt j hj_te; omega
    by_cases hv0 : mrk[(k.trl[j]?.getD 0#32).toNat / 2]?.getD 0#8 = 0#8
    · obtain ⟨l, hlmem, hleq, hne, _, _⟩ := hnewm _ hvlt hv0 hnz'
      obtain ⟨m, hm, hmeq⟩ := hclause_cut l hlmem (hleq ▸ hne) (hleq ▸ hcl)
      have hm_te : m < k.trail_end := Nat.lt_of_lt_of_le hm hw.cut_le
      have hvar : (k.trl[m]?.getD 0#32).toNat / 2 = (k.trl[j]?.getD 0#32).toNat / 2 := by
        rw [hmeq, litNeg_div2, hleq]
      have hieq := hw.trail_vars_nodup m j hm_te hj_te hvar
      rwa [← hieq]
    · exact hcm j hj hv0 hcl
  have htc' : tc' = (fullCurTrailIdxs k mrk' idx).length := by
    let pOld : Nat → Bool := fun j =>
      let v := (k.trl[j]?.getD 0#32).toNat / 2
      decide (mrk[v]?.getD 0#8 ≠ 0#8) && decide ((k.lvl[v]?.getD 0#32).toNat = k.cur_level)
    let pNew : Nat → Bool := fun j =>
      let v := (k.trl[j]?.getD 0#32).toNat / 2
      decide (mrk[v]?.getD 0#8 = 0#8) && decide (mrk'[v]?.getD 0#8 ≠ 0#8) &&
        decide ((k.lvl[v]?.getD 0#32).toNat = k.cur_level)
    have hsplit : fullCurTrailIdxs k mrk' idx =
        (List.range idx).filter (fun j => pOld j || pNew j) := by
      unfold fullCurTrailIdxs; apply List.filter_congr; intro j hj
      have hjlt : j < idx := List.mem_range.mp hj
      have hvlt : (k.trl[j]?.getD 0#32).toNat / 2 < k.cur_vars := by
        have := hw.trail_lits_lt j (by omega); omega
      dsimp only [pOld, pNew]
      by_cases h0 : mrk[(k.trl[j]?.getD 0#32).toNat / 2]?.getD 0#8 = 0#8
      · simp [h0]
      · rw [hmpres _ hvlt h0]; simp [h0]
    have hadd : (fullCurTrailIdxs k mrk' idx).length =
        ((List.range idx).filter pOld).length + ((List.range idx).filter pNew).length := by
      rw [hsplit]
      exact filter_length_add_of_disj pOld pNew (List.range idx) fun j _ ⟨h1, h2⟩ => by
        simp [pOld, pNew] at h1 h2; exact h1.1 h2.1.1
    have hbij : ((List.range idx).filter pNew).length =
        ((List.range k.cur_vars).filter fun v =>
          decide (mrk[v]?.getD 0#8 = 0#8) &&
          decide (mrk'[v]?.getD 0#8 ≠ 0#8) &&
          decide ((k.lvl[v]?.getD 0#32).toNat = k.cur_level)).length := by
      refine nodup_length_eq_of_bij (fun j => (k.trl[j]?.getD 0#32).toNat / 2)
        (List.Nodup.sublist List.filter_sublist List.nodup_range)
        (List.Nodup.sublist List.filter_sublist List.nodup_range)
        (fun j hj => ?_) (fun j1 hj1 j2 hj2 heq => ?_) (fun v hv => ?_)
      · rw [List.mem_filter, List.mem_range] at hj ⊢
        have hvlt : (k.trl[j]?.getD 0#32).toNat / 2 < k.cur_vars := by
          have := hw.trail_lits_lt j (by omega); omega
        exact ⟨hvlt, hj.2⟩
      · rw [List.mem_filter, List.mem_range] at hj1 hj2
        exact hw.trail_vars_nodup j1 j2 (by omega) (by omega) heq
      · rw [List.mem_filter, List.mem_range] at hv
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
        obtain ⟨hvlt, ⟨hm0, hmnz'⟩, hcl⟩ := hv
        obtain ⟨l, hlmem, rfl, hne, _, _⟩ := hnewm v hvlt hm0 hmnz'
        rcases hclause l hlmem with heq | ⟨m, hm, hmeq⟩
        · exact absurd heq hne
        · have hmvar : (k.trl[m]?.getD 0#32).toNat / 2 = l / 2 := by
            rw [hmeq]; exact litVar_litNeg l
          refine ⟨m, List.mem_filter.mpr ⟨List.mem_range.mpr hm, ?_⟩, hmvar⟩
          simp [pNew, hmvar, hm0, hmnz', hcl]
    have hold_eq : ((List.range idx).filter pOld).length = tc := htc_eq.symm
    omega
  have hlow_sub : ∀ l ∈ fullLowerLits tmp tl, l ∈ fullLowerLits tmp' tl' := by
    intro l hl
    rw [mem_fullLowerLits_iff h1 (by omega)] at hl
    obtain ⟨j, hj1, hj2, hget⟩ := hl
    rw [mem_fullLowerLits_iff (by omega) (by omega)]
    exact ⟨j, hj1, by omega, by rw [htpres j hj2]; exact hget⟩
  have hcur_sub : ∀ l ∈ fullCurLits k mrk idx, l ∈ fullCurLits k mrk' idx := by
    intro l hl
    unfold fullCurLits fullCurTrailIdxs at hl ⊢
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hl
    rw [List.mem_filter, List.mem_range] at hj
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hj
    have hvlt : (k.trl[j]?.getD 0#32).toNat / 2 < k.cur_vars := by
      have := hw.trail_lits_lt j (by omega); omega
    refine List.mem_map.mpr ⟨j, List.mem_filter.mpr ⟨List.mem_range.mpr hj.1, ?_⟩, rfl⟩
    simp [hmpres _ hvlt hj.2.1, hj.2.1, hj.2.2]
  have hq_res : ∀ q, LitPred q →
      q / 2 = skip_var ∨ q ∈ fullActiveResolvent k tmp' mrk' tl' idx ∨
        (cnfOfClauses F_cur).EntailsClause (cnfClause [litNeg q]) := by
    intro q hq
    rcases hclause q hq with heq | ⟨m, hm, hmeq⟩
    · exact Or.inl heq
    · by_cases hskip : q / 2 = skip_var
      · exact Or.inl hskip
      · right
        have hqlt : q < 2 * k.cur_vars := hlits_lt q hq
        have hq_fals : k.vals[q]?.getD 0#8 = 0xFF#8 :=
          (hw.vals_false_iff q hqlt).mpr ⟨m, by omega, hmeq⟩
        have hmvar : (k.trl[m]?.getD 0#32).toNat / 2 = q / 2 := by
          rw [hmeq]; exact litVar_litNeg q
        have hvl_le : (k.lvl[q / 2]?.getD 0#32).toNat ≤ k.cur_level := by
          rw [← hmvar]; exact hw.lvl_le m (by omega)
        by_cases hvl0 : (k.lvl[q / 2]?.getD 0#32).toNat = 0
        · right
          have hs0 := hw.level0_sound m (by omega) (by rw [hmvar]; exact hvl0)
          rwa [hmeq] at hs0
        · left
          obtain ⟨_, hq_rest⟩ := hall q hq
          have hq_mrk' : mrk'[q / 2]?.getD 0#8 ≠ 0#8 := (hq_rest hskip).1 (by omega)
          by_cases hcl : (k.lvl[q / 2]?.getD 0#32).toNat = k.cur_level
          · apply List.mem_append_right
            refine List.mem_map.mpr ⟨m, List.mem_filter.mpr ⟨List.mem_range.mpr hm, ?_⟩, ?_⟩
            · simp [hmvar, hq_mrk', hcl]
            · rw [hmeq]; exact litNeg_litNeg q
          · apply List.mem_append_left
            rw [mem_fullLowerLits_iff (by omega) (by omega)]
            rcases hcov' (q / 2) (by omega) hq_mrk' with ⟨j, hj1, hj2, hjeq⟩ | ⟨_, _, _, hbad⟩
            · obtain ⟨hl_lt, hl_fals, _, _, _⟩ := hlow'.1 j hj1 hj2
              exact ⟨j, hj1, hj2, fullWitnessCutInv_falsified_lit_unique hw hl_lt hqlt hjeq
                hl_fals hq_fals⟩
            · omega
  exact ⟨htc', hlow', hcov', hcm', hlow_sub, hcur_sub, hq_res⟩

/-- Exact cardinality identity for newly added lower literals + newly marked `cur_level` literals
across `full_analyze_rsn` (`res'` partition identity). -/
theorem analyzeRsn_tl_sub_eq {k : FullCoreState} {mrk mrk' : List (BitVec 8)}
    {tmp' : List (BitVec 32)} {tl tl' : Nat}
    (htl_le : tl ≤ tl')
    (hnewt : ∀ j, tl ≤ j → j < tl' →
      let l := (tmp'[j]?.getD 0#32).toNat
      l / 2 < k.cur_vars ∧ mrk[l / 2]?.getD 0#8 = 0#8 ∧
      0 < (k.lvl[l / 2]?.getD 0#32).toNat ∧ (k.lvl[l / 2]?.getD 0#32).toNat < k.cur_level ∧
      mrk'[l / 2]?.getD 0#8 ≠ 0#8)
    (hnd : ∀ j1 j2, tl ≤ j1 → j1 < j2 → j2 < tl' →
      (tmp'[j1]?.getD 0#32).toNat / 2 ≠ (tmp'[j2]?.getD 0#32).toNat / 2)
    (hnewm : ∀ w < k.cur_vars, mrk[w]?.getD 0#8 = 0#8 → mrk'[w]?.getD 0#8 ≠ 0#8 →
      0 < (k.lvl[w]?.getD 0#32).toNat ∧ (k.lvl[w]?.getD 0#32).toNat ≤ k.cur_level)
    (hsurj : ∀ w < k.cur_vars, mrk[w]?.getD 0#8 = 0#8 → mrk'[w]?.getD 0#8 ≠ 0#8 →
      0 < (k.lvl[w]?.getD 0#32).toNat → (k.lvl[w]?.getD 0#32).toNat < k.cur_level →
      ∃ j, tl ≤ j ∧ j < tl' ∧ (tmp'[j]?.getD 0#32).toNat / 2 = w) :
    tl' - tl =
      ((List.range k.cur_vars).filter fun w =>
        decide (mrk[w]?.getD 0#8 = 0#8) &&
        decide (mrk'[w]?.getD 0#8 ≠ 0#8) &&
        decide ((k.lvl[w]?.getD 0#32).toNat < k.cur_level)).length := by
  let idxs := (List.range tl').filter fun j => decide (tl ≤ j)
  have hidxs_len : idxs.length = tl' - tl := by
    have hbij : idxs.length = (List.range (tl' - tl)).length :=
      nodup_length_eq_of_bij (fun j => j - tl)
        (List.Nodup.sublist List.filter_sublist List.nodup_range) List.nodup_range
        (fun j hj => by
          rw [List.mem_filter, List.mem_range] at hj
          simp only [decide_eq_true_eq] at hj
          exact List.mem_range.mpr (by omega))
        (fun j1 hj1 j2 hj2 heq => by
          rw [List.mem_filter, List.mem_range] at hj1 hj2
          simp only [decide_eq_true_eq] at hj1 hj2; omega)
        (fun y hy => by
          rw [List.mem_range] at hy
          exact ⟨tl + y, List.mem_filter.mpr ⟨List.mem_range.mpr (by omega), by simp⟩, by omega⟩)
    simpa [List.length_range] using hbij
  rw [← hidxs_len]
  refine nodup_length_eq_of_bij (fun j => (tmp'[j]?.getD 0#32).toNat / 2)
    (List.Nodup.sublist List.filter_sublist List.nodup_range)
    (List.Nodup.sublist List.filter_sublist List.nodup_range) ?_ ?_ ?_
  · intro j hj
    rw [List.mem_filter, List.mem_range] at hj
    simp only [decide_eq_true_eq] at hj
    obtain ⟨hv, hm0, _, hcl, hm'⟩ := hnewt j hj.2 hj.1
    rw [List.mem_filter, List.mem_range]
    exact ⟨hv, by simp [hm0, hm', hcl]⟩
  · intro j1 hj1 j2 hj2 heq
    rw [List.mem_filter, List.mem_range] at hj1 hj2
    simp only [decide_eq_true_eq] at hj1 hj2
    rcases Nat.lt_trichotomy j1 j2 with h | h | h
    · exact absurd heq (hnd j1 j2 hj1.2 h hj2.1)
    · exact h
    · exact absurd heq.symm (hnd j2 j1 hj2.2 h hj1.1)
  · intro w hw
    rw [List.mem_filter, List.mem_range] at hw
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hw
    obtain ⟨hv, ⟨hm0, hm'⟩, hltcl⟩ := hw
    have hpos := (hnewm w hv hm0 hm').1
    obtain ⟨j, hj1, hj2, hjeq⟩ := hsurj w hv hm0 hm' hpos hltcl
    exact ⟨j, List.mem_filter.mpr ⟨List.mem_range.mpr hj2, by simp [hj1]⟩, hjeq⟩

theorem analyzeRsn_all_marked_eq {k : FullCoreState} {mrk mrk' : List (BitVec 8)}
    (hnewm : ∀ w < k.cur_vars, mrk[w]?.getD 0#8 = 0#8 → mrk'[w]?.getD 0#8 ≠ 0#8 →
      0 < (k.lvl[w]?.getD 0#32).toNat ∧ (k.lvl[w]?.getD 0#32).toNat ≤ k.cur_level) :
    ((List.range k.cur_vars).filter fun w =>
      decide (mrk[w]?.getD 0#8 = 0#8) && decide (mrk'[w]?.getD 0#8 ≠ 0#8)).length =
    ((List.range k.cur_vars).filter fun w =>
      decide (mrk[w]?.getD 0#8 = 0#8) && decide (mrk'[w]?.getD 0#8 ≠ 0#8) &&
      decide ((k.lvl[w]?.getD 0#32).toNat = k.cur_level)).length +
    ((List.range k.cur_vars).filter fun w =>
      decide (mrk[w]?.getD 0#8 = 0#8) && decide (mrk'[w]?.getD 0#8 ≠ 0#8) &&
      decide ((k.lvl[w]?.getD 0#32).toNat < k.cur_level)).length := by
  let p1 : Nat → Bool := fun w =>
    decide (mrk[w]?.getD 0#8 = 0#8) && decide (mrk'[w]?.getD 0#8 ≠ 0#8) &&
    decide ((k.lvl[w]?.getD 0#32).toNat = k.cur_level)
  let p2 : Nat → Bool := fun w =>
    decide (mrk[w]?.getD 0#8 = 0#8) && decide (mrk'[w]?.getD 0#8 ≠ 0#8) &&
    decide ((k.lvl[w]?.getD 0#32).toNat < k.cur_level)
  have hcongr : (List.range k.cur_vars).filter (fun w =>
      decide (mrk[w]?.getD 0#8 = 0#8) && decide (mrk'[w]?.getD 0#8 ≠ 0#8)) =
      (List.range k.cur_vars).filter (fun w => p1 w || p2 w) := by
    apply List.filter_congr; intro w hw
    have hwlt := List.mem_range.mp hw
    dsimp only [p1, p2]
    by_cases h0 : mrk[w]?.getD 0#8 = 0#8
    · by_cases h1 : mrk'[w]?.getD 0#8 ≠ 0#8
      · have hle := (hnewm w hwlt h0 h1).2
        simp only [h0, decide_true, Bool.true_and]
        by_cases hc : (k.lvl[w]?.getD 0#32).toNat = k.cur_level
        · simp [h1, hc]
        · simp [h1, hc, Nat.lt_of_le_of_ne hle hc]
      · simp [h0, h1]
    · simp [h0]
  rw [hcongr]
  exact filter_length_add_of_disj p1 p2 (List.range k.cur_vars) fun w _ ⟨ha, hb⟩ => by
    simp only [p1, p2, Bool.and_eq_true, decide_eq_true_eq] at ha hb; omega

private theorem list_nodup_of_getElem_ne {α : Type} :
    ∀ {xs : List α},
      (∀ i j (hi : i < xs.length) (hj : j < xs.length), i < j → xs[i] ≠ xs[j]) → xs.Nodup
  | [], _ => List.nodup_nil
  | _ :: _, h => by
    rw [List.nodup_cons]
    refine ⟨fun hx => ?_, list_nodup_of_getElem_ne fun i j hi hj hij =>
      h (i + 1) (j + 1) (Nat.succ_lt_succ hi) (Nat.succ_lt_succ hj) (Nat.succ_lt_succ hij)⟩
    obtain ⟨k, hk, hget⟩ := List.mem_iff_getElem.mp hx
    exact h 0 (k + 1) (Nat.zero_lt_succ _) (Nat.succ_lt_succ hk) (Nat.zero_lt_succ _) hget.symm

theorem fullLowerVars_nodup {tmp : List (BitVec 32)} {tl : Nat}
    (htl_arr : tl ≤ tmp.length)
    (hnd : ∀ j1 j2, 1 ≤ j1 → j1 < j2 → j2 < tl →
      (tmp[j1]?.getD 0#32).toNat / 2 ≠ (tmp[j2]?.getD 0#32).toNat / 2) :
    ((((tmp.drop 1).take (tl - 1)).map fun x => x.toNat / 2)).Nodup := by
  refine list_nodup_of_getElem_ne fun i j hi hj hij => ?_
  simp only [List.length_map, List.length_take, List.length_drop] at hi hj
  simp only [List.getElem_map, List.getElem_take, List.getElem_drop]
  have h1 := hnd (1 + i) (1 + j) (by omega) (by omega) (by omega)
  rwa [List.getElem?_eq_getElem (by omega), Option.getD_some,
    List.getElem?_eq_getElem (by omega), Option.getD_some] at h1

theorem fullTmpTake_uip_nodup {c : FullCfg} {k : FullCoreState}
    {tmp : List (BitVec 32)} {mrk : List (BitVec 8)} {tl : Nat} {uip : BitVec 32}
    (h1 : 1 ≤ tl) (htl_arr : tl ≤ tmp.length) (h0 : tmp[0]? = some uip)
    (hlow : FullLowerInv c k tmp mrk tl)
    (huip_cl : (k.lvl[uip.toNat / 2]?.getD 0#32).toNat = k.cur_level) :
    ((tmp.take tl).map fun x => x.toNat / 2).Nodup := by
  have htake : (tmp.take tl).map (fun x => x.toNat / 2) =
      (uip.toNat / 2) :: ((tmp.drop 1).take (tl - 1)).map (fun x => x.toNat / 2) := by
    cases tmp with
    | nil => simp at h0
    | cons x xs =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h0; subst h0
      cases tl with
      | zero => omega
      | succ n => simp
  rw [htake, List.nodup_cons]
  refine ⟨fun hmem => ?_, fullLowerVars_nodup htl_arr hlow.2⟩
  obtain ⟨y, hy, heq⟩ := List.mem_map.mp hmem
  obtain ⟨p, hp, hget⟩ := List.mem_iff_getElem.mp hy
  have hplt : p < tl - 1 := by rw [List.length_take, List.length_drop] at hp; omega
  rw [List.getElem_take, List.getElem_drop] at hget
  have hcl := (hlow.1 (1 + p) (by omega) (by omega)).2.2.2.1
  rw [(List.getElem?_eq_getElem (by omega) : tmp[1 + p]? = some _), Option.getD_some,
    hget, heq, huip_cl] at hcl
  omega

theorem fullActiveResolvent_le_cur_vars {c : FullCfg} {k : FullCoreState}
    {tmp : List (BitVec 32)} {mrk : List (BitVec 8)} {tl idx : Nat}
    (hidx : idx ≤ k.trail_end) (h1 : 1 ≤ tl) (htl_arr : tl ≤ tmp.length)
    (hlow : FullLowerInv c k tmp mrk tl)
    (htrl_lt : ∀ i < k.trail_end, (k.trl[i]?.getD 0#32).toNat < 2 * k.cur_vars)
    (htrl_nd : ∀ i j, i < k.trail_end → j < k.trail_end →
      (k.trl[i]?.getD 0#32).toNat / 2 = (k.trl[j]?.getD 0#32).toNat / 2 → i = j) :
    (tl - 1) + (fullCurTrailIdxs k mrk idx).length ≤ k.cur_vars := by
  let lowVars := ((tmp.drop 1).take (tl - 1)).map fun x => x.toNat / 2
  let curVars := (fullCurTrailIdxs k mrk idx).map fun j => (k.trl[j]?.getD 0#32).toNat / 2
  have hlow_len : lowVars.length = tl - 1 := by
    simp [lowVars, List.length_map, List.length_take]; omega
  have hcur_len : curVars.length = (fullCurTrailIdxs k mrk idx).length := by
    simp [curVars, List.length_map]
  have hlow_nd : lowVars.Nodup := fullLowerVars_nodup htl_arr hlow.2
  have hcur_nd : curVars.Nodup :=
    nodup_map_of_inj (List.Nodup.sublist List.filter_sublist List.nodup_range)
      fun i1 hi1 i2 hi2 heq => by
        rw [fullCurTrailIdxs, List.mem_filter, List.mem_range] at hi1 hi2
        exact htrl_nd i1 i2 (by omega) (by omega) heq
  have hdisj : ∀ v ∈ lowVars, v ∉ curVars := by
    intro v hvl hvc
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hvl
    obtain ⟨p, hp, hget⟩ := List.mem_iff_getElem.mp hx
    have hplt : p < tl - 1 := by rw [List.length_take, List.length_drop] at hp; omega
    rw [List.getElem_take, List.getElem_drop] at hget
    have hlow_lt := (hlow.1 (1 + p) (by omega) (by omega)).2.2.2.1
    rw [(List.getElem?_eq_getElem (by omega) : tmp[1 + p]? = some _), Option.getD_some,
      hget] at hlow_lt
    obtain ⟨j, hj, heq⟩ := List.mem_map.mp hvc
    rw [fullCurTrailIdxs, List.mem_filter] at hj
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hj
    rw [← heq, hj.2.2] at hlow_lt; omega
  have hnd : (lowVars ++ curVars).Nodup :=
    List.nodup_append.mpr ⟨hlow_nd, hcur_nd, fun a ha b hb he => hdisj a ha (he ▸ hb)⟩
  have hsub : ∀ v ∈ lowVars ++ curVars, v < k.cur_vars := by
    intro v hv; rcases List.mem_append.mp hv with hl | hc
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hl
      obtain ⟨p, hp, hget⟩ := List.mem_iff_getElem.mp hx
      have hplt : p < tl - 1 := by rw [List.length_take, List.length_drop] at hp; omega
      rw [List.getElem_take, List.getElem_drop] at hget
      have h1lt := (hlow.1 (1 + p) (by omega) (by omega)).1
      rw [(List.getElem?_eq_getElem (by omega) : tmp[1 + p]? = some _), Option.getD_some,
        hget] at h1lt; omega
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hc
      rw [fullCurTrailIdxs, List.mem_filter, List.mem_range] at hj
      have := htrl_lt j (by omega); omega
  have hle := nodup_length_le_of_lt k.cur_vars (lowVars ++ curVars) hnd hsub
  rw [List.length_append, hlow_len, hcur_len] at hle; exact hle

theorem fullActiveResolvent_length {k : FullCoreState} {tmp : List (BitVec 32)}
    {mrk : List (BitVec 8)} {tl idx : Nat} (h1 : 1 ≤ tl) (htl_arr : tl ≤ tmp.length) :
    (fullActiveResolvent k tmp mrk tl idx).length =
      (tl - 1) + (fullCurTrailIdxs k mrk idx).length := by
  unfold fullActiveResolvent fullCurLits
  rw [List.length_append, fullLowerLits_length h1 htl_arr, List.length_map]

private theorem nodup_of_map_fn {α β : Type} (f : α → β) :
    ∀ {xs : List α}, (xs.map f).Nodup → xs.Nodup
  | [], _ => List.nodup_nil
  | _ :: _, h => by
    rw [List.map_cons, List.nodup_cons] at h
    exact List.nodup_cons.mpr ⟨fun hm => h.1 (List.mem_map_of_mem hm), nodup_of_map_fn f h.2⟩

private theorem countP_eq_len_filter {α : Type} (p : α → Bool) :
    ∀ (xs : List α), xs.countP p = (xs.filter p).length
  | [] => rfl
  | x :: xs => by
    cases hp : p x <;> simp [hp, countP_eq_len_filter p xs]

private theorem filter_pred_eq_singleton {α : Type} [DecidableEq α] (pred : α → Bool) (a : α) :
    ∀ {xs : List α}, xs.Nodup → a ∈ xs → pred a = true →
      xs.filter (fun l => pred l && decide (l = a)) = [a]
  | [], _, ha, _ => by cases ha
  | x :: xs, hnd, ha, hpa => by
    rw [List.nodup_cons] at hnd
    rcases List.mem_cons.mp ha with rfl | hm'
    · have hnil : xs.filter (fun l => pred l && decide (l = a)) = [] :=
        List.filter_eq_nil_iff.mpr fun z hz => by
          have hza : z ≠ a := fun he => hnd.1 (he ▸ hz)
          simp [hza]
      simp [hpa, hnil]
    · have hxne : x ≠ a := fun he => hnd.1 (he ▸ hm')
      simp [hxne, filter_pred_eq_singleton pred a hnd.2 hm' hpa]

theorem otfs_rsn_pos_lits_props {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut idx' : Nat} {s : FullState} {p rsn : BitVec 32}
    (hw : FullWitnessCutInv c F0 F_cur cut s.core) (hnd : FullArenaVarsNodup s)
    (hiu_cut : idx' < cut) (hiu_te : idx' < s.core.trail_end)
    (ht_u : (s.core.trl[idx']?.getD 0#32).toNat = p.toNat)
    (hr_u : s.core.rsns[p.toNat / 2]?.getD 0xFFFFFFFF#32 = rsn)
    (hlev_u : (s.core.lvl[p.toNat / 2]?.getD 0#32).toNat = s.core.cur_level)
    (hcl_pos : 0 < s.core.cur_level)
    (hrsn_ne : rsn ≠ 0xFFFFFFFF#32) (hrsn_lg : (rsn &&& 0x80000000#32) = 0#32)
    {ant_sz : BitVec 64}
    (hant_eq : ant_sz = BitVec.ofNat 64 ((fullRsnLits s rsn).countP fun l =>
      decide (l / 2 < s.core.cur_vars ∧ 0 < (s.core.lvl[l / 2]?.getD 0#32).toNat ∧
        (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ s.core.cur_level))) :
    let lits := fullArenaClauseLits s rsn.toNat
    let S := lits.filter fun l => decide (l ≠ p.toNat ∧ 0 < (s.core.lvl[l / 2]?.getD 0#32).toNat)
    rsn.toNat ∈ fullArenaClauseRefs s ∧ fullArenaClauseGarb s rsn.toNat = false ∧
    S.Nodup ∧ (∀ l ∈ S, l / 2 ≠ p.toNat / 2) ∧
    BitVec.ofNat 64 (S.length + 1) = ant_sz := by
  intro lits S
  have hri := hw.reason_inv_cut idx' hiu_cut
  dsimp only at hri; rw [ht_u, hr_u] at hri
  have hri := hri hrsn_ne
  rw [ite_eq_right (fun h => absurd hrsn_lg h)] at hri
  obtain ⟨href, hng, hl_inv⟩ := hri
  have hpmem : p.toNat ∈ lits := by
    have hm := hw.reason_lit_mem_cut idx' hiu_cut
    dsimp only at hm; rw [ht_u, hr_u] at hm; exact hm hrsn_ne hrsn_lg
  have hl_nodup_var : (lits.map (· / 2)).Nodup := hnd rsn.toNat href hng
  have hS_nd : S.Nodup :=
    List.Nodup.sublist List.filter_sublist (nodup_of_map_fn _ hl_nodup_var)
  have hS_ne_pv : ∀ l ∈ S, l / 2 ≠ p.toNat / 2 := fun l hl heq => by
    rw [List.mem_filter] at hl
    simp only [decide_eq_true_eq] at hl
    have : ∀ {xs : List Nat}, (xs.map (· / 2)).Nodup → ∀ a ∈ xs, ∀ b ∈ xs,
        a / 2 = b / 2 → a = b := by
      intro xs hnd' a ha b hb hab
      induction xs with
      | nil => cases ha
      | cons x xs ih =>
        rw [List.map_cons, List.nodup_cons] at hnd'
        rcases List.mem_cons.mp ha with rfl | ha' <;>
          rcases List.mem_cons.mp hb with rfl | hb'
        · rfl
        · exact absurd (hab ▸ List.mem_map_of_mem hb') hnd'.1
        · exact absurd (hab.symm ▸ List.mem_map_of_mem ha') hnd'.1
        · exact ih hnd'.2 ha' hb'
    exact hl.2.1 (this hl_nodup_var l hl.1 p.toNat hpmem heq)
  have hfull_eq : lits = fullRsnLits s rsn := by
    simp [fullRsnLits, hrsn_ne, hrsn_lg, fullArenaClauseLits]; rfl
  let pred : Nat → Bool := fun l =>
    decide (l / 2 < s.core.cur_vars ∧ 0 < (s.core.lvl[l / 2]?.getD 0#32).toNat ∧
      (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ s.core.cur_level)
  have hp_pred : pred p.toNat = true := by
    have hp_lt := hw.trail_lits_lt idx' hiu_te; rw [ht_u] at hp_lt
    simp [pred, hlev_u, hcl_pos]; omega
  have hS_eq : S = lits.filter (fun l => pred l && decide (l ≠ p.toNat)) := by
    apply List.filter_congr; intro l hl
    have hl_lt := hw.arena.lits_lt rsn.toNat href hng l hl
    have hl_le : (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ s.core.cur_level := by
      rcases hl_inv l hl with rfl | ⟨_, _, _, hle⟩
      · exact hlev_u ▸ Nat.le_refl _
      · exact Nat.le_trans hle (hlev_u ▸ Nat.le_refl _)
    simp only [pred]
    by_cases hne : l = p.toNat <;> simp [hne, show l / 2 < s.core.cur_vars by omega, hl_le]
  have hcount : lits.countP pred = S.length + 1 := by
    rw [countP_eq_len_filter pred lits]
    rw [hS_eq]
    have hsplit : (lits.filter pred).length =
        (lits.filter (fun l => pred l && decide (l = p.toNat))).length +
        (lits.filter (fun l => pred l && decide (l ≠ p.toNat))).length := by
      let pA : Nat → Bool := fun l => pred l && decide (l = p.toNat)
      let pB : Nat → Bool := fun l => pred l && decide (l ≠ p.toNat)
      have hc : lits.filter pred = lits.filter (fun l => pA l || pB l) := by
        apply List.filter_congr; intro l _
        by_cases hpe : l = p.toNat
        · subst hpe; simp [pA, pB]
        · cases hp : pred l <;> simp [pA, pB, hp, hpe]
      rw [hc]
      exact filter_length_add_of_disj pA pB lits fun l _ ⟨h1, h2⟩ => by
        simp only [pA, pB, Bool.and_eq_true, decide_eq_true_eq] at h1 h2; exact h2.2 h1.2
    have h1 := filter_pred_eq_singleton pred p.toNat (nodup_of_map_fn _ hl_nodup_var) hpmem hp_pred
    rw [hsplit, h1, List.length_singleton]; omega
  rw [hant_eq, ← hfull_eq, hcount]
  exact ⟨href, hng, hS_nd, hS_ne_pv, rfl⟩

theorem otfs_entails_rsn_pos_lits {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut idx' : Nat} {k : FullCoreState} {tmp : List (BitVec 32)} {mrk : List (BitVec 8)}
    {tl tc : Nat} {p rsn : BitVec 32}
    (hw : FullWitnessCutInv c F0 F_cur cut k)
    (h1 : 1 ≤ tl) (htl_arr : tl ≤ tmp.length)
    (hlow : FullLowerInv c k tmp mrk tl) (hcov : FullMarksCov k tmp mrk tl)
    (htc_eq : tc = (fullCurTrailIdxs k mrk idx').length)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause (fullActiveResolvent k tmp mrk tl idx')))
    (hiu_cut : idx' < cut) (hiu_te : idx' < k.trail_end)
    (ht_u : (k.trl[idx']?.getD 0#32).toNat = p.toNat)
    (hr_u : k.rsns[p.toNat / 2]?.getD 0xFFFFFFFF#32 = rsn)
    (hrsn_ne : rsn ≠ 0xFFFFFFFF#32) (hrsn_lg : (rsn &&& 0x80000000#32) = 0#32)
    (hall : ∀ l ∈ fullArenaClauseLitsCore k rsn.toNat,
      l / 2 ≠ p.toNat / 2 → 0 < (k.lvl[l / 2]?.getD 0#32).toNat → mrk[l / 2]?.getD 0#8 ≠ 0#8)
    (S : List Nat) (hS_nd : S.Nodup)
    (hS_sub : ∀ l ∈ S, l ∈ fullArenaClauseLitsCore k rsn.toNat ∧ l ≠ p.toNat ∧
      l / 2 ≠ p.toNat / 2 ∧ 0 < (k.lvl[l / 2]?.getD 0#32).toNat)
    (hres_lt : (tl - 1) + tc < S.length + 1) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause S) := by
  have hri := hw.reason_inv_cut idx' hiu_cut
  dsimp only at hri; rw [ht_u, hr_u] at hri
  have hri := hri hrsn_ne
  rw [ite_eq_right (fun h => absurd hrsn_lg h)] at hri
  obtain ⟨href, hng, hl_inv⟩ := hri
  have hS_in_res : ∀ l ∈ S, l ∈ fullActiveResolvent k tmp mrk tl idx' := by
    intro l hl
    obtain ⟨hmem, hnep, hnev, hpos⟩ := hS_sub l hl
    have hllt := hw.arena.lits_lt rsn.toNat href hng l hmem
    obtain ⟨m, hm, hmeq, _⟩ := (hl_inv l hmem).resolve_left hnep
    have hlfals : k.vals[l]?.getD 0#8 = 0xFF#8 :=
      (hw.vals_false_iff l hllt).mpr ⟨m, by omega, hmeq⟩
    have hmvar : (k.trl[m]?.getD 0#32).toNat / 2 = l / 2 := by rw [hmeq]; exact litVar_litNeg l
    have hmrk : mrk[l / 2]?.getD 0#8 ≠ 0#8 := hall l hmem hnev hpos
    by_cases hcl : (k.lvl[l / 2]?.getD 0#32).toNat = k.cur_level
    · apply List.mem_append_right
      refine List.mem_map.mpr ⟨m, List.mem_filter.mpr ⟨List.mem_range.mpr hm, ?_⟩, ?_⟩
      · simp [hmvar, hmrk, hcl]
      · rw [hmeq]; exact litNeg_litNeg l
    · apply List.mem_append_left
      rw [mem_fullLowerLits_iff h1 htl_arr]
      rcases hcov (l / 2) (by omega) hmrk with ⟨j, hj1, hj2, hjeq⟩ | ⟨_, _, _, hbad⟩
      · obtain ⟨hl_lt, hl_fals, _, _, _, _⟩ := hlow.1 j hj1 hj2
        exact ⟨j, hj1, hj2, fullWitnessCutInv_falsified_lit_unique hw hl_lt hllt hjeq hl_fals
          hlfals⟩
      · omega
  have hlen_res : (fullActiveResolvent k tmp mrk tl idx').length ≤ S.length := by
    rw [fullActiveResolvent_length h1 htl_arr, ← htc_eq]; omega
  have hres_sub_S := nodup_subset_of_superset_le_length hS_nd hS_in_res hlen_res
  exact entails_of_mem_or_false hent fun l hl => Or.inl (hres_sub_S l hl)

theorem otfs_entails_bin_of_res_lt_ant {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut idx' : Nat} {s : FullState} {tmp : List (BitVec 32)} {mrk : List (BitVec 8)}
    {tl tc : Nat} {p rsn : BitVec 32} {res_sz ant_sz : BitVec 64}
    (hw : FullWitnessCutInv c F0 F_cur cut s.core) (hnd : FullArenaVarsNodup s)
    (hlen : s.LengthsOk c) (h1 : 1 ≤ tl) (htl_cv : tl ≤ s.core.cur_vars)
    (htl_arr : tl ≤ tmp.length) (hlow : FullLowerInv c s.core tmp mrk tl)
    (hcov : FullMarksCov s.core tmp mrk tl)
    (htc_eq : tc = (fullCurTrailIdxs s.core mrk idx').length)
    (hent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause (fullActiveResolvent s.core tmp mrk tl idx')))
    (hiu_cut : idx' < cut) (hiu_te : idx' < s.core.trail_end)
    (ht_u : (s.core.trl[idx']?.getD 0#32).toNat = p.toNat)
    (hr_u : s.core.rsns[p.toNat / 2]?.getD 0xFFFFFFFF#32 = rsn)
    (hlev_u : (s.core.lvl[p.toNat / 2]?.getD 0#32).toNat = s.core.cur_level)
    (hcl_pos : 0 < s.core.cur_level)
    (hrsn_ne : rsn ≠ 0xFFFFFFFF#32) (hrsn_lg : (rsn &&& 0x80000000#32) = 0#32)
    (hall : ∀ l ∈ fullArenaClauseLitsCore s.core rsn.toNat,
      l / 2 ≠ p.toNat / 2 → 0 < (s.core.lvl[l / 2]?.getD 0#32).toNat → mrk[l / 2]?.getD 0#8 ≠ 0#8)
    (hres_eq : res_sz = BitVec.ofNat 64 ((tl - 1) + tc))
    (hant_eq : ant_sz = BitVec.ofNat 64 ((fullRsnLits s rsn).countP fun l =>
      decide (l / 2 < s.core.cur_vars ∧ 0 < (s.core.lvl[l / 2]?.getD 0#32).toNat ∧
        (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ s.core.cur_level)))
    (hlt : res_sz.ult ant_sz = true) (hant3 : ant_sz = 3#64) :
    ∀ f0 f1 : BitVec 32,
      f0.toNat ∈ fullArenaClauseLits s rsn.toNat → f1.toNat ∈ fullArenaClauseLits s rsn.toNat →
      f0 ≠ p → f1 ≠ p → f0 ≠ f1 →
      0 < (s.core.lvl[f0.toNat / 2]?.getD 0#32).toNat →
      0 < (s.core.lvl[f1.toNat / 2]?.getD 0#32).toNat →
      (cnfOfClauses F_cur).EntailsClause (cnfClause [f0.toNat, f1.toNat]) := by
  let S := (fullArenaClauseLits s rsn.toNat).filter fun l =>
    decide (l ≠ p.toNat ∧ 0 < (s.core.lvl[l / 2]?.getD 0#32).toNat)
  have ⟨_, _, hS_nd, hS_pv, hS_ant⟩ :=
    otfs_rsn_pos_lits_props hw hnd hiu_cut hiu_te ht_u hr_u hlev_u hcl_pos hrsn_ne hrsn_lg hant_eq
  have hS_bd : S.length + 1 < 2 ^ 64 := by
    have : S.length ≤ (fullArenaClauseLits s rsn.toNat).length := List.length_filter_le _ _
    have ha := c.harena; have hal := hlen.core_ok.arena_len_arr; unfold dimacsBound at ha
    have : (fullArenaClauseLits s rsn.toNat).length ≤ c.arena_cap := by
      simp [fullArenaClauseLits, fullArenaClauseLitsCore]; omega
    omega
  have hS_len2 : S.length = 2 := by
    have heq : BitVec.ofNat 64 (S.length + 1) = 3#64 := hS_ant.trans hant3
    have := congrArg BitVec.toNat heq
    rw [bv64_ofNat_toNat hS_bd] at this
    have : (3#64 : BitVec 64).toNat = 3 := rfl; omega
  have hres_bd : (tl - 1) + tc < 2 ^ 64 := by
    have hcv := hlen.core_ok.cur_vars_le; have hmx := c.hmaxv; unfold dimacsBound at hmx
    have := fullActiveResolvent_le_cur_vars (Nat.le_of_lt hiu_te) h1 htl_arr hlow
      hw.trail_lits_lt hw.trail_vars_nodup
    rw [← htc_eq] at this; omega
  have hres_lt : (tl - 1) + tc < S.length + 1 := by
    rw [hres_eq, hant3] at hlt
    have hult : ((BitVec.ofNat 64 ((tl - 1) + tc)).toNat) < (3#64 : BitVec 64).toNat := by
      simpa [BitVec.ult] using hlt
    have h3 : (3#64 : BitVec 64).toNat = 3 := rfl
    rw [bv64_ofNat_toNat hres_bd, h3] at hult; omega
  have hentS := otfs_entails_rsn_pos_lits hw h1 htl_arr hlow hcov htc_eq hent
    hiu_cut hiu_te ht_u hr_u hrsn_ne hrsn_lg hall S hS_nd
    (fun l hl => by
      rw [List.mem_filter] at hl
      simp only [decide_eq_true_eq] at hl
      exact ⟨hl.1, hl.2.1, hS_pv l (by simpa [S]), hl.2.2⟩)
    hres_lt
  intro f0 f1 hf0 hf1 hf0p hf1p hf01 hp0 hp1
  have hf0_ne : f0.toNat ≠ p.toNat := fun h => hf0p (BitVec.eq_of_toNat_eq h)
  have hf1_ne : f1.toNat ≠ p.toNat := fun h => hf1p (BitVec.eq_of_toNat_eq h)
  have h0S : f0.toNat ∈ S := List.mem_filter.mpr ⟨hf0, by simp [hf0_ne, hp0]⟩
  have h1S : f1.toNat ∈ S := List.mem_filter.mpr ⟨hf1, by simp [hf1_ne, hp1]⟩
  have hne : f0.toNat ≠ f1.toNat := fun h => hf01 (BitVec.eq_of_toNat_eq h)
  have hsub2 : ∀ l ∈ S, l ∈ [f0.toNat, f1.toNat] := by
    have : [f0.toNat, f1.toNat].Nodup := by simp [hne]
    exact nodup_subset_of_superset_le_length this
      (fun l hl => by rcases List.mem_cons.mp hl with rfl | h'
                      · exact h0S
                      · rw [List.mem_singleton.mp h']; exact h1S)
      (by simp [hS_len2])
  exact entails_of_mem_or_false hentS fun l hl => Or.inl (hsub2 l hl)

theorem otfs_entails_large_of_res_lt_ant {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut idx' : Nat} {s : FullState} {tmp : List (BitVec 32)} {mrk : List (BitVec 8)}
    {tl tc : Nat} {p rsn : BitVec 32} {res_sz ant_sz : BitVec 64}
    (hw : FullWitnessCutInv c F0 F_cur cut s.core) (hnd : FullArenaVarsNodup s)
    (hlen : s.LengthsOk c) (h1 : 1 ≤ tl) (htl_arr : tl ≤ tmp.length)
    (hlow : FullLowerInv c s.core tmp mrk tl) (hcov : FullMarksCov s.core tmp mrk tl)
    (htc_eq : tc = (fullCurTrailIdxs s.core mrk idx').length)
    (hent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause (fullActiveResolvent s.core tmp mrk tl idx')))
    (hiu_cut : idx' < cut) (hiu_te : idx' < s.core.trail_end)
    (ht_u : (s.core.trl[idx']?.getD 0#32).toNat = p.toNat)
    (hr_u : s.core.rsns[p.toNat / 2]?.getD 0xFFFFFFFF#32 = rsn)
    (hlev_u : (s.core.lvl[p.toNat / 2]?.getD 0#32).toNat = s.core.cur_level)
    (hcl_pos : 0 < s.core.cur_level)
    (hrsn_ne : rsn ≠ 0xFFFFFFFF#32) (hrsn_lg : (rsn &&& 0x80000000#32) = 0#32)
    (hall : ∀ l ∈ fullArenaClauseLitsCore s.core rsn.toNat,
      l / 2 ≠ p.toNat / 2 → 0 < (s.core.lvl[l / 2]?.getD 0#32).toNat → mrk[l / 2]?.getD 0#8 ≠ 0#8)
    (hres_eq : res_sz = BitVec.ofNat 64 ((tl - 1) + tc))
    (hant_eq : ant_sz = BitVec.ofNat 64 ((fullRsnLits s rsn).countP fun l =>
      decide (l / 2 < s.core.cur_vars ∧ 0 < (s.core.lvl[l / 2]?.getD 0#32).toNat ∧
        (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ s.core.cur_level)))
    (hlt : res_sz.ult ant_sz = true) :
    (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((fullArenaClauseLits s rsn.toNat).filter fun l =>
        decide (l ≠ p.toNat ∧ (0 < (s.core.lvl[l / 2]?.getD 0#32).toNat ∨
          l = (s.core.arena[rsn.toNat + 3]?.getD 0#32).toNat ∨
          l = (s.core.arena[rsn.toNat + 4]?.getD 0#32).toNat)))) := by
  let S := (fullArenaClauseLits s rsn.toNat).filter fun l =>
    decide (l ≠ p.toNat ∧ 0 < (s.core.lvl[l / 2]?.getD 0#32).toNat)
  have ⟨_, _, hS_nd, hS_pv, hS_ant⟩ :=
    otfs_rsn_pos_lits_props hw hnd hiu_cut hiu_te ht_u hr_u hlev_u hcl_pos hrsn_ne hrsn_lg hant_eq
  have hS_bd : S.length + 1 < 2 ^ 64 := by
    have : S.length ≤ (fullArenaClauseLits s rsn.toNat).length := List.length_filter_le _ _
    have ha := c.harena; have hal := hlen.core_ok.arena_len_arr; unfold dimacsBound at ha
    have : (fullArenaClauseLits s rsn.toNat).length ≤ c.arena_cap := by
      simp [fullArenaClauseLits, fullArenaClauseLitsCore]; omega
    omega
  have hres_bd : (tl - 1) + tc < 2 ^ 64 := by
    have hcv := hlen.core_ok.cur_vars_le; have hmx := c.hmaxv; unfold dimacsBound at hmx
    have := fullActiveResolvent_le_cur_vars (Nat.le_of_lt hiu_te) h1 htl_arr hlow
      hw.trail_lits_lt hw.trail_vars_nodup
    rw [← htc_eq] at this; omega
  have hres_lt : (tl - 1) + tc < S.length + 1 := by
    have hult : res_sz.toNat < ant_sz.toNat := by simpa [BitVec.ult] using hlt
    rw [hres_eq, ← hS_ant, bv64_ofNat_toNat hres_bd, bv64_ofNat_toNat hS_bd] at hult
    exact hult
  have hentS := otfs_entails_rsn_pos_lits hw h1 htl_arr hlow hcov htc_eq hent
    hiu_cut hiu_te ht_u hr_u hrsn_ne hrsn_lg hall S hS_nd
    (fun l hl => by
      rw [List.mem_filter] at hl
      simp only [decide_eq_true_eq] at hl
      exact ⟨hl.1, hl.2.1, hS_pv l (by simpa [S]), hl.2.2⟩)
    hres_lt
  refine entails_of_mem_or_false hentS fun l hl => Or.inl ?_
  rw [List.mem_filter] at hl ⊢
  simp only [decide_eq_true_eq] at hl ⊢
  exact ⟨hl.1, hl.2.1, Or.inl hl.2.2⟩

end ResolventTheory

/-! ## 3. Factored invariants, exit/OTFS helpers & `full_deduce_1uip_core_wp` -/

section Deduce1UipCore

private theorem range_filter_eq_of_ge_false (p : Nat → Bool) {a b : Nat} (hle : a ≤ b)
    (hf : ∀ j, a ≤ j → j < b → p j = false) :
    (List.range b).filter p = (List.range a).filter p := by
  induction hd : b - a generalizing b with
  | zero =>
    have hba : b = a := by omega
    subst b; rfl
  | succ _ ih =>
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show b ≠ 0 by omega)
    have hle' : a ≤ n := by omega
    rw [range_succ_filter, hf n hle' (Nat.lt_succ_self _)]
    simpa using ih hle' (fun j hj1 hj2 => hf j hj1 (Nat.lt_succ_of_lt hj2)) (by omega)

private theorem fullCurMarksBelow_ge_false {cut j : Nat} {k : FullCoreState}
    {mrk : List (BitVec 8)}
    (hcm : FullCurMarksBelow k.trail_end k mrk cut) (hj : j < k.trail_end) (hge : cut ≤ j) :
    ¬ (mrk[(k.trl[j]?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8 ∧
       (k.lvl[(k.trl[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = k.cur_level) := by
  rintro ⟨hm, hl⟩
  exact absurd (hcm j hj hm hl) (by omega)

private theorem fullCurTrailIdxs_eq_cut {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {cut : Nat} {k : FullCoreState}
    (hw : FullWitnessCutInv c F0 F_cur cut k) {mrk : List (BitVec 8)}
    (hcm : FullCurMarksBelow k.trail_end k mrk cut) :
    fullCurTrailIdxs k mrk k.trail_end = fullCurTrailIdxs k mrk cut := by
  unfold fullCurTrailIdxs
  apply range_filter_eq_of_ge_false _ hw.cut_le
  intro j hj1 hj2
  simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
  by_cases h1 : mrk[(k.trl[j]?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8
  · exact Or.inr (fun h2 => fullCurMarksBelow_ge_false hcm hj2 hj1 ⟨h1, h2⟩)
  · exact Or.inl h1

private theorem fullCurLits_eq_cut {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {cut : Nat} {k : FullCoreState}
    (hw : FullWitnessCutInv c F0 F_cur cut k) {mrk : List (BitVec 8)}
    (hcm : FullCurMarksBelow k.trail_end k mrk cut) :
    fullCurLits k mrk k.trail_end = fullCurLits k mrk cut := by
  unfold fullCurLits; rw [fullCurTrailIdxs_eq_cut hw hcm]

theorem fullCurTrailIdxs_succ_eq_self {k : FullCoreState} {mrk : List (BitVec 8)}
    {idx' : Nat} (hm : ¬ (mrk[(k.trl[idx']?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8 ∧
      (k.lvl[(k.trl[idx']?.getD 0#32).toNat / 2]?.getD 0#32).toNat = k.cur_level)) :
    fullCurTrailIdxs k mrk (idx' + 1) = fullCurTrailIdxs k mrk idx' :=
  fullCurTrailIdxs_succ_false hm

theorem fullCurLits_succ_eq_self {k : FullCoreState} {mrk : List (BitVec 8)}
    {idx' : Nat} (hm : ¬ (mrk[(k.trl[idx']?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8 ∧
      (k.lvl[(k.trl[idx']?.getD 0#32).toNat / 2]?.getD 0#32).toNat = k.cur_level)) :
    fullCurLits k mrk (idx' + 1) = fullCurLits k mrk idx' :=
  fullCurLits_succ_false hm

theorem deduce_same_core_cut {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {k : FullCoreState} (hw : FullWitnessCutInv c F0 F_cur cut k)
    (mrk' : List (BitVec 8)) (tmp' : List (BitVec 32)) (tc' tl' mcl' : Nat) :
    FullWitnessCutInv c F0 F_cur cut
      { k with mrk := mrk', tmp := tmp', tmp_cnt := tc', tmp_len := tl', min_clr_len := mcl' } :=
  { hw with
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl fun _ hr => hr }

structure FullDeduceStaticEq (k0 k : FullCoreState) : Prop where
  cv : k.cur_vars = k0.cur_vars
  cl : k.cur_level = k0.cur_level
  te : k.trail_end = k0.trail_end
  trl : k.trl = k0.trl
  lvl : k.lvl = k0.lvl
  rsns : k.rsns = k0.rsns
  vals : k.vals = k0.vals
  fuel : k.fuel = k0.fuel
  dm : k.dense_mode = k0.dense_mode
  lm : k.lit_mark = k0.lit_mark

theorem fullDeduceStaticEq_refl (k : FullCoreState) : FullDeduceStaticEq k k :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem FullDeduceStaticEq.repack {k0 k1 k2 : FullCoreState} (h : FullDeduceStaticEq k0 k1)
    (hcv : k2.cur_vars = k1.cur_vars := by rfl) (hcl : k2.cur_level = k1.cur_level := by rfl)
    (hte : k2.trail_end = k1.trail_end := by rfl) (htrl : k2.trl = k1.trl := by rfl)
    (hlvl : k2.lvl = k1.lvl := by rfl) (hrsns : k2.rsns = k1.rsns := by rfl)
    (hvals : k2.vals = k1.vals := by rfl) (hfuel : k2.fuel = k1.fuel := by rfl)
    (hdm : k2.dense_mode = k1.dense_mode := by rfl) (hlm : k2.lit_mark = k1.lit_mark := by rfl) :
    FullDeduceStaticEq k0 k2 :=
  ⟨hcv.trans h.1, hcl.trans h.2, hte.trans h.3, htrl.trans h.4, hlvl.trans h.5,
   hrsns.trans h.6, hvals.trans h.7, hfuel.trans h.8, hdm.trans h.9, hlm.trans h.10⟩

private theorem fullDeduceStaticEq_trans {k0 k1 k2 : FullCoreState}
    (h1 : FullDeduceStaticEq k0 k1) (h2 : FullDeduceStaticEq k1 k2) :
    FullDeduceStaticEq k0 k2 :=
  ⟨h2.cv.trans h1.cv, h2.cl.trans h1.cl, h2.te.trans h1.te, h2.trl.trans h1.trl,
   h2.lvl.trans h1.lvl, h2.rsns.trans h1.rsns, h2.vals.trans h1.vals, h2.fuel.trans h1.fuel,
   h2.dm.trans h1.dm, h2.lm.trans h1.lm⟩

structure FullDeduceStateInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (cut idx : Nat) (s s1 : FullState) : Prop where
  len : s1.LengthsOk c
  hw : FullWitnessCutInv c F0 F_cur cut s1.core
  cov : FullAnaMarksCov c s1
  ext : FullExtScratchPres s s1
  ws2 : s1.scratch.work_stk2 = s.scratch.work_stk2
  nd : FullArenaVarsNodup s1
  hrefs : fullArenaClauseRefs s1 = fullArenaClauseRefs s
  stat : FullDeduceStaticEq s.core s1.core
  tl_ge : 1 ≤ s1.core.tmp_len
  tl_cv : s1.core.tmp_len ≤ s1.core.cur_vars
  tc_eq : s1.core.tmp_cnt = (fullCurTrailIdxs s1.core s1.core.mrk idx).length
  low : FullLowerInv c s1.core s1.core.tmp s1.core.mrk s1.core.tmp_len
  mcov : FullMarksCov s1.core s1.core.tmp s1.core.mrk s1.core.tmp_len
  cmcut : FullCurMarksBelow idx s1.core s1.core.mrk cut
  ent : (cnfOfClauses F_cur).EntailsClause
    (cnfClause (fullActiveResolvent s1.core s1.core.tmp s1.core.mrk s1.core.tmp_len idx))
  res_eq : s1.scratch.res_sz = BitVec.ofNat 64 ((s1.core.tmp_len - 1) + s1.core.tmp_cnt)

private theorem fullLitMarksClear_of_mrk {c : FullCfg} {s s' : FullState}
    (h0 : FullLitMarksClear c s) (hlm : s'.core.lit_mark = s.core.lit_mark)
    (hmrk : ∀ v < c.max_vars, s'.core.mrk[v]?.getD 0#8 = 0#8) :
    FullLitMarksClear c s' :=
  ⟨hmrk, fun l hl => by rw [hlm]; exact h0.2 l hl⟩

private theorem deduce_otfsInvW_of {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut' : Nat} {s s' : FullState}
    (hlen : s'.LengthsOk c) (hw : FullWitnessCutInv c F0 F_cur cut' s'.core)
    (hmrk : FullLitMarksClear c s') (hnd : FullArenaVarsNodup s')
    (hext0 : FullExtScratchOk c s) (hext : FullExtScratchPres s s')
    (hrefs : fullArenaClauseRefs s' = fullArenaClauseRefs s)
    (hdm : s'.core.dense_mode = 0#64) : FullOtfsInvW c F0 F_cur s' :=
  ⟨hlen, hw.toFullOtfsWitnessInv, hmrk, hnd,
   ⟨fun i hi => by
      change (let cr := s'.scratch.last_learned[i]?.getD 0xFFFFFFFF#32; _); rw [hext.1]
      rcases hext0.1 i hi with h | h
      · exact Or.inl h
      · exact Or.inr (hrefs ▸ h),
    by rw [hext.2]; exact hext0.2⟩,
   hdm⟩

private theorem deduce_clear_ana_wp {Γ : Env}
    (hClear : ∀ a m Q X, fullClearAnaSpec a m Q X → Γ "full_clear_ana" [i64] [] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {cut' : Nat}
    {s s1 : FullState} {R : Mem 64 → Prop} {K : Tup Val [] → Expr Val Cont [i64]}
    {Q : Post [i64]} {X : XPost} {m1 : Mem 64}
    (hlen1 : s1.LengthsOk c) (hw1 : FullWitnessCutInv c F0 F_cur cut' s1.core)
    (hcov1 : FullAnaMarksCov c s1) (hext0 : FullExtScratchOk c s) (hext1 : FullExtScratchPres s s1)
    (hnd1 : FullArenaVarsNodup s1) (hrefs1 : fullArenaClauseRefs s1 = fullArenaClauseRefs s)
    (hlm1 : s1.core.lit_mark = s.core.lit_mark) (hdm1 : s1.core.dense_mode = 0#64)
    (hm0_lm : FullLitMarksClear c s) (hm1 : (FullMem c s1 ⋆ R) m1)
    (hK : ∀ mrk' m_clr,
      let s_clr : FullState := { s1 with core := { s1.core with mrk := mrk', min_clr_len := 0 } }
      s_clr.LengthsOk c →
      FullOtfsInvW c F0 F_cur s_clr →
      FullWitnessCutInv c F0 F_cur cut' s_clr.core →
      (FullMem c s_clr ⋆ R) m_clr →
      wp Γ Q X (K ()) m_clr) :
    wp Γ Q X (.call (rs := [i64]) (as := [i64]) (bs := []) "full_clear_ana" (Arg.var c.hdr, ()) K)
      m1 := by
  refine wp_call_of_spec _ _ (hClear (c.hdr, ()) _ _ _ ⟨c, s1, R, rfl, hlen1, hm1, ?_⟩)
  intro mrk' m_c hm'_len _ _ hm'_cov hm_c
  let s_c : FullState := { s1 with core := { s1.core with mrk := mrk', min_clr_len := 0 } }
  have hlen_c : s_c.LengthsOk c :=
    ⟨{ hlen1.core_ok with mrk_len := hm'_len, min_clr_len_le := Nat.zero_le _ }, hlen1.scratch_ok⟩
  have hw_c : FullWitnessCutInv c F0 F_cur cut' s_c.core :=
    deduce_same_core_cut hw1 mrk' s1.core.tmp s1.core.tmp_cnt s1.core.tmp_len 0
  have hlm_c : FullLitMarksClear c s_c :=
    fullLitMarksClear_of_mrk hm0_lm hlm1 (hm'_cov hcov1)
  have hotfs_c := deduce_otfsInvW_of hlen_c hw_c hlm_c hnd1 hext0 hext1 hrefs1 hdm1
  exact hK mrk' m_c hlen_c hotfs_c hw_c hm_c

private theorem deduce_clear_unsat_ret_wp {Γ : Env}
    (hClear : ∀ a m Q X, fullClearAnaSpec a m Q X → Γ "full_clear_ana" [i64] [] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {cut' : Nat}
    {s s1 : FullState} {R : Mem 64 → Prop} {K : Tup Val [] → Expr Val Cont [i64]}
    {Q : Post [i64]} {X : XPost} {m1 : Mem 64}
    (hlen1 : s1.LengthsOk c) (hw1 : FullWitnessCutInv c F0 F_cur cut' s1.core)
    (hcov1 : FullAnaMarksCov c s1) (hext0 : FullExtScratchOk c s) (hext1 : FullExtScratchPres s s1)
    (hnd1 : FullArenaVarsNodup s1) (hrefs1 : fullArenaClauseRefs s1 = fullArenaClauseRefs s)
    (hstat1 : FullDeduceStaticEq s.core s1.core) (hdm0 : s.core.dense_mode = 0#64)
    (hm0_lm : FullLitMarksClear c s) (hm1 : (FullMem c s1 ⋆ R) m1)
    (hK : ∀ mrk' m_clr,
      let s_clr : FullState := { s1 with core := { s1.core with mrk := mrk', min_clr_len := 0 } }
      s_clr.LengthsOk c →
      FullOtfsInvW c F0 F_cur s_clr →
      s_clr.core.cur_vars = s.core.cur_vars →
      s_clr.core.fuel = s.core.fuel →
      s_clr.core.cur_level = s.core.cur_level →
      s_clr.core.dense_mode = 0#64 →
      (FullMem c s_clr ⋆ R) m_clr →
      wp Γ Q X (K ()) m_clr) :
    wp Γ Q X (.call (rs := [i64]) (as := [i64]) (bs := []) "full_clear_ana" (Arg.var c.hdr, ()) K)
      m1 := by
  have hdm1 : s1.core.dense_mode = 0#64 := hstat1.dm.trans hdm0
  refine deduce_clear_ana_wp hClear hlen1 hw1 hcov1 hext0 hext1 hnd1 hrefs1 hstat1.lm hdm1
    hm0_lm hm1 fun mrk' m_clr hlen_c hotfs_c _ hm_c =>
    hK mrk' m_clr hlen_c hotfs_c hstat1.cv hstat1.fuel hstat1.cl hdm1 hm_c

private theorem deduce_analyze_lit_res_tc {k : FullCoreState} {mrk' : List (BitVec 8)}
    {tmp' : List (BitVec 32)} {tl tl' tc tc' skip_var : Nat} {lit : BitVec 32}
    {res_sz res' : BitVec 64}
    (htl_ge : 1 ≤ tl) (htl_le : tl ≤ tl')
    (hres0 : res_sz = BitVec.ofNat 64 ((tl - 1) + tc))
    (hnewm : ∀ v < k.cur_vars, k.mrk[v]?.getD 0#8 = 0#8 → mrk'[v]?.getD 0#8 ≠ 0#8 →
      lit.toNat / 2 = v ∧ v ≠ skip_var ∧
      0 < (k.lvl[v]?.getD 0#32).toNat ∧ (k.lvl[v]?.getD 0#32).toNat ≤ k.cur_level)
    (hnewt : ∀ j, tl ≤ j → j < tl' →
      (tmp'[j]?.getD 0#32).toNat = lit.toNat ∧ lit.toNat / 2 < k.cur_vars ∧
      lit.toNat / 2 ≠ skip_var ∧ k.mrk[lit.toNat / 2]?.getD 0#8 = 0#8 ∧
      0 < (k.lvl[lit.toNat / 2]?.getD 0#32).toNat ∧
      (k.lvl[lit.toNat / 2]?.getD 0#32).toNat < k.cur_level ∧ mrk'[lit.toNat / 2]?.getD 0#8 ≠ 0#8)
    (htc_eq : tc' = tc +
      if lit.toNat / 2 < k.cur_vars ∧ k.mrk[lit.toNat / 2]?.getD 0#8 = 0#8 ∧
        mrk'[lit.toNat / 2]?.getD 0#8 ≠ 0#8 ∧ (k.lvl[lit.toNat / 2]?.getD 0#32).toNat = k.cur_level
      then 1 else 0)
    (hres_eq : res' = res_sz +
      (if lit.toNat / 2 < k.cur_vars ∧ k.mrk[lit.toNat / 2]?.getD 0#8 = 0#8 ∧
        mrk'[lit.toNat / 2]?.getD 0#8 ≠ 0#8 then 1#64 else 0#64))
    (hok : lit.toNat / 2 < k.cur_vars ∧
      (lit.toNat / 2 ≠ skip_var →
        (0 < (k.lvl[lit.toNat / 2]?.getD 0#32).toNat → mrk'[lit.toNat / 2]?.getD 0#8 ≠ 0#8) ∧
        (k.mrk[lit.toNat / 2]?.getD 0#8 = 0#8 →
          (k.lvl[lit.toNat / 2]?.getD 0#32).toNat ≤ k.cur_level ∧
          (0 < (k.lvl[lit.toNat / 2]?.getD 0#32).toNat →
            (k.lvl[lit.toNat / 2]?.getD 0#32).toNat = k.cur_level → tc' = tc + 1) ∧
          (0 < (k.lvl[lit.toNat / 2]?.getD 0#32).toNat →
            (k.lvl[lit.toNat / 2]?.getD 0#32).toNat < k.cur_level →
            tl' = tl + 1 ∧ tmp'[tl]? = some lit))))
    (hskip : lit.toNat / 2 ≠ skip_var) :
    res' = BitVec.ofNat 64 ((tl' - 1) + tc') := by
  have hvlt : lit.toNat / 2 < k.cur_vars := hok.1
  by_cases hcond : k.mrk[lit.toNat / 2]?.getD 0#8 = 0#8 ∧ mrk'[lit.toNat / 2]?.getD 0#8 ≠ 0#8
  · obtain ⟨_, _, hpos, hle⟩ := hnewm _ hvlt hcond.1 hcond.2
    have hres_add : res' = res_sz + 1#64 := by
      simpa [hvlt, hcond.1, hcond.2] using hres_eq
    by_cases hcl : (k.lvl[lit.toNat / 2]?.getD 0#32).toNat = k.cur_level
    · have htc1 : tc' = tc + 1 := ((hok.2 hskip).2 hcond.1).2.1 hpos hcl
      have htl_same : tl' = tl := by
        by_cases heq : tl' = tl
        · exact heq
        · have hlt : tl < tl' := Nat.lt_of_le_of_ne htl_le (Ne.symm heq)
          have := (hnewt tl (Nat.le_refl _) hlt).2.2.2.2.2.1
          omega
      rw [hres_add, hres0, htc1, htl_same, show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl,
        ← BitVec.ofNat_add]
      exact congrArg (BitVec.ofNat 64) (by omega)
    · have hlt_cl : (k.lvl[lit.toNat / 2]?.getD 0#32).toNat < k.cur_level := by omega
      have htc_same : tc' = tc := by simp [hvlt, hcl] at htc_eq; exact htc_eq
      have htl1 : tl' = tl + 1 := (((hok.2 hskip).2 hcond.1).2.2 hpos hlt_cl).1
      rw [hres_add, hres0, htc_same, htl1, show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl,
        ← BitVec.ofNat_add]
      exact congrArg (BitVec.ofNat 64) (by omega)
  · have htc_same : tc' = tc := by
      rw [htc_eq, ite_eq_right (fun h => hcond ⟨h.2.1, h.2.2.1⟩), Nat.add_zero]
    have htl_same : tl' = tl := by
      by_cases heq : tl' = tl
      · exact heq
      · have hlt : tl < tl' := Nat.lt_of_le_of_ne htl_le (Ne.symm heq)
        have hnt := hnewt tl (Nat.le_refl _) hlt
        exact absurd ⟨hnt.2.2.2.1, hnt.2.2.2.2.2.2⟩ hcond
    have hres_same : res' = res_sz := by
      rw [hres_eq, ite_eq_right (fun h => hcond ⟨h.2.1, h.2.2⟩), BitVec.add_zero]
    rw [hres_same, htl_same, htc_same, hres0]

theorem deduce_seed_lit_step {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {s sa : FullState} {lit : BitVec 32}
    {mrk' : List (BitVec 8)} {tmp' ws1' : List (BitVec 32)} {mcl' tc' tl' : Nat}
    {ant' res' : BitVec 64}
    (hlena : sa.LengthsOk c) (hwa : FullWitnessCutInv c F0 F_cur cut sa.core)
    (hnda : FullArenaVarsNodup sa) (hrefsa : fullArenaClauseRefs sa = fullArenaClauseRefs s)
    (hstata : FullDeduceStaticEq s.core sa.core)
    (htl_ge : 1 ≤ sa.core.tmp_len) (htc_eq : sa.core.tmp_cnt =
      (fullCurTrailIdxs sa.core sa.core.mrk sa.core.trail_end).length)
    (hlow : FullLowerInv c sa.core sa.core.tmp sa.core.mrk sa.core.tmp_len)
    (hmcov : FullMarksCov sa.core sa.core.tmp sa.core.mrk sa.core.tmp_len)
    (hcm : FullCurMarksBelow sa.core.trail_end sa.core sa.core.mrk cut)
    (hres0 : sa.scratch.res_sz =
      BitVec.ofNat 64 ((sa.core.tmp_len - 1) + sa.core.tmp_cnt))
    (hlit_lt : lit.toNat < 2 * sa.core.cur_vars)
    (hlit_fals : sa.core.vals[lit.toNat]?.getD 0#8 = 0xFF#8)
    (hlit_cut : (sa.core.lvl[lit.toNat / 2]?.getD 0#32).toNat = sa.core.cur_level →
      ∃ m < cut, (sa.core.trl[m]?.getD 0#32).toNat = lit.toNat ^^^ 1)
    (hlen' : ({ sa with
      core := { sa.core with mrk := mrk', tmp := tmp', tmp_cnt := tc', tmp_len := tl',
                             min_clr_len := mcl' }
      scratch := { sa.scratch with work_stk1 := ws1', ant_sz := ant', res_sz := res' } } :
      FullState).LengthsOk c)
    (hcov' : FullAnaMarksCov c
      { sa with
        core := { sa.core with mrk := mrk', tmp := tmp', tmp_cnt := tc', tmp_len := tl',
                               min_clr_len := mcl' }
        scratch := { sa.scratch with work_stk1 := ws1', ant_sz := ant', res_sz := res' } })
    (htl'_cv : tl' ≤ sa.core.cur_vars) (htl_le : sa.core.tmp_len ≤ tl')
    (htc_le : sa.core.tmp_cnt ≤ tc')
    (hmpres : ∀ w < sa.core.cur_vars, sa.core.mrk[w]?.getD 0#8 ≠ 0#8 →
      mrk'[w]?.getD 0#8 = sa.core.mrk[w]?.getD 0#8)
    (htpres : ∀ j < sa.core.tmp_len, tmp'[j]? = sa.core.tmp[j]?)
    (hnewm : ∀ w < sa.core.cur_vars, sa.core.mrk[w]?.getD 0#8 = 0#8 → mrk'[w]?.getD 0#8 ≠ 0#8 →
      lit.toNat / 2 = w ∧ w ≠ (0xFFFFFFFF#32).toNat ∧
      0 < (sa.core.lvl[w]?.getD 0#32).toNat ∧ (sa.core.lvl[w]?.getD 0#32).toNat ≤ sa.core.cur_level)
    (hnewt : ∀ j, sa.core.tmp_len ≤ j → j < tl' →
      (tmp'[j]?.getD 0#32).toNat = lit.toNat ∧ lit.toNat / 2 < sa.core.cur_vars ∧
      lit.toNat / 2 ≠ (0xFFFFFFFF#32).toNat ∧ sa.core.mrk[lit.toNat / 2]?.getD 0#8 = 0#8 ∧
      0 < (sa.core.lvl[lit.toNat / 2]?.getD 0#32).toNat ∧
      (sa.core.lvl[lit.toNat / 2]?.getD 0#32).toNat < sa.core.cur_level ∧
      mrk'[lit.toNat / 2]?.getD 0#8 ≠ 0#8)
    (hres_eq : res' = sa.scratch.res_sz +
      if lit.toNat / 2 < sa.core.cur_vars ∧ sa.core.mrk[lit.toNat / 2]?.getD 0#8 = 0#8 ∧
        mrk'[lit.toNat / 2]?.getD 0#8 ≠ 0#8 then 1#64 else 0#64)
    (htc_eq' : tc' = sa.core.tmp_cnt +
      if lit.toNat / 2 < sa.core.cur_vars ∧ sa.core.mrk[lit.toNat / 2]?.getD 0#8 = 0#8 ∧
        mrk'[lit.toNat / 2]?.getD 0#8 ≠ 0#8 ∧
        (sa.core.lvl[lit.toNat / 2]?.getD 0#32).toNat = sa.core.cur_level
      then 1 else 0)
    (hok : lit.toNat / 2 < sa.core.cur_vars ∧
      (lit.toNat / 2 ≠ (0xFFFFFFFF#32).toNat →
        (0 < (sa.core.lvl[lit.toNat / 2]?.getD 0#32).toNat → mrk'[lit.toNat / 2]?.getD 0#8 ≠ 0#8) ∧
        (sa.core.mrk[lit.toNat / 2]?.getD 0#8 = 0#8 →
          (sa.core.lvl[lit.toNat / 2]?.getD 0#32).toNat ≤ sa.core.cur_level ∧
          (0 < (sa.core.lvl[lit.toNat / 2]?.getD 0#32).toNat →
            (sa.core.lvl[lit.toNat / 2]?.getD 0#32).toNat = sa.core.cur_level →
            tc' = sa.core.tmp_cnt + 1) ∧
          (0 < (sa.core.lvl[lit.toNat / 2]?.getD 0#32).toNat →
            (sa.core.lvl[lit.toNat / 2]?.getD 0#32).toNat < sa.core.cur_level →
            tl' = sa.core.tmp_len + 1 ∧ tmp'[sa.core.tmp_len]? = some lit))))
    (hext : FullExtScratchPres s sa) (hws2 : sa.scratch.work_stk2 = s.scratch.work_stk2) :
    let sb : FullState :=
      { sa with
        core := { sa.core with mrk := mrk', tmp := tmp', tmp_cnt := tc', tmp_len := tl',
                               min_clr_len := mcl' }
        scratch := { sa.scratch with work_stk1 := ws1', ant_sz := ant', res_sz := res' } }
    sb.LengthsOk c ∧ FullWitnessCutInv c F0 F_cur cut sb.core ∧ FullAnaMarksCov c sb ∧
    FullExtScratchPres s sb ∧ sb.scratch.work_stk2 = s.scratch.work_stk2 ∧
    FullArenaVarsNodup sb ∧ fullArenaClauseRefs sb = fullArenaClauseRefs s ∧
    FullDeduceStaticEq s.core sb.core ∧ 1 ≤ tl' ∧ tl' ≤ sb.core.cur_vars ∧
    tc' = (fullCurTrailIdxs sb.core mrk' sb.core.trail_end).length ∧
    FullLowerInv c sb.core tmp' mrk' tl' ∧
    FullMarksCov sb.core tmp' mrk' tl' ∧ FullCurMarksBelow sb.core.trail_end sb.core mrk' cut ∧
    (∀ l ∈ fullActiveResolvent sa.core sa.core.tmp sa.core.mrk sa.core.tmp_len sa.core.trail_end,
      l ∈ fullActiveResolvent sb.core tmp' mrk' tl' sb.core.trail_end) ∧
    (lit.toNat ∈ fullActiveResolvent sb.core tmp' mrk' tl' sb.core.trail_end ∨
      (cnfOfClauses F_cur).EntailsClause (cnfClause [litNeg lit.toNat])) ∧
    res' = BitVec.ofNat 64 ((tl' - 1) + tc') := by
  intro sb
  have hcv_le := hlena.core_ok.cur_vars_le
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  have hskip : lit.toNat / 2 ≠ (0xFFFFFFFF#32).toNat := by
    have : (0xFFFFFFFF#32).toNat = 2 ^ 32 - 1 := rfl; omega
  have hcnt := filter_step_of_lit (fun w => decide ((sa.core.lvl[w]?.getD 0#32).toNat =
      sa.core.cur_level)) (mv := sa.core.cur_vars) (tc0 := sa.core.tmp_cnt)
      (tc1 := sa.core.tmp_cnt) (v := lit.toNat / 2) (fun _ _ _ => rfl) hmpres
      (fun w hw h0 hnz => (hnewm w hw h0 hnz).1) (Nat.le_refl _)
      (by rw [Nat.sub_self, List.filter_eq_nil_iff.mpr (fun _ _ => by simp)]; rfl)
      (by simpa only [decide_eq_true_eq] using htc_eq')
  have hclause : ∀ q, q = lit.toNat → q / 2 = (0xFFFFFFFF#32).toNat ∨
      ∃ m < sa.core.trail_end, (sa.core.trl[m]?.getD 0#32).toNat = q ^^^ 1 := fun q hq => by
    subst hq; right; exact (hwa.vals_false_iff lit.toNat hlit_lt).mp hlit_fals
  have hnd_new : ∀ j1 j2, sa.core.tmp_len ≤ j1 → j1 < j2 → j2 < tl' →
      (tmp'[j1]?.getD 0#32).toNat / 2 ≠ (tmp'[j2]?.getD 0#32).toNat / 2 := by
    intro j1 j2 h1 h12 h2
    have hnt1 := hnewt j1 h1 (by omega)
    have hok1 := ((hok.2 hnt1.2.2.1).2 hnt1.2.2.2.1).2.2 hnt1.2.2.2.2.1 hnt1.2.2.2.2.2.1
    omega
  obtain ⟨htc', hlow', hmcov', hcm', hlow_sub, hcur_sub, hq_res⟩ := fullAnalyzeStep_preserves
    hlena.core_ok hwa (· = lit.toNat) (mrk := sa.core.mrk) (mrk' := mrk') (tmp := sa.core.tmp)
    (tmp' := tmp') (tc := sa.core.tmp_cnt) (tc' := tc') (tl := sa.core.tmp_len) (tl' := tl')
    (Nat.le_refl _) htl_ge htl_le htl'_cv hlena.core_ok.tmp_len_arr hlen'.core_ok.tmp_len_arr
    htc_eq htc_le hlow hmcov hcm (fun _ h => h ▸ hlit_lt) hclause
    (fun q hq _ hcl => by subst hq; exact hlit_cut hcl) hmpres htpres
    (fun v hv h0 hnz => let ⟨he, hr⟩ := hnewm v hv h0 hnz; ⟨lit.toNat, rfl, he, hr⟩)
    (fun j h1 h2 => let ⟨he, hr⟩ := hnewt j h1 h2; ⟨he, by rw [he]; exact ⟨hlit_lt, hr.2⟩⟩)
    hnd_new hcnt
    (fun l hl => by
      subst hl; refine ⟨hok.1, fun hn => ⟨(hok.2 hn).1, fun h0 => ?_⟩⟩
      obtain ⟨hl1, h1, h2⟩ := (hok.2 hn).2 h0
      exact ⟨hl1, fun hp hlt => let ⟨_, htget⟩ := h2 hp hlt
        ⟨sa.core.tmp_len, Nat.le_refl _, by omega, by rw [htget]; rfl⟩⟩)
  have hres_new := deduce_analyze_lit_res_tc htl_ge htl_le hres0 hnewm hnewt htc_eq' hres_eq hok
    hskip
  have hin_res : ∀ l ∈ fullActiveResolvent sa.core sa.core.tmp sa.core.mrk sa.core.tmp_len
      sa.core.trail_end, l ∈ fullActiveResolvent sb.core tmp' mrk' tl' sb.core.trail_end := by
    intro l hl; rcases List.mem_append.mp hl with h1 | h2
    · exact List.mem_append_left _ (hlow_sub l h1)
    · exact List.mem_append_right _ (hcur_sub l h2)
  have hlit_mem : lit.toNat ∈ fullActiveResolvent sb.core tmp' mrk' tl' sb.core.trail_end ∨
      (cnfOfClauses F_cur).EntailsClause (cnfClause [litNeg lit.toNat]) :=
    (hq_res lit.toNat rfl).resolve_left (fun he => hskip he)
  exact ⟨hlen', deduce_same_core_cut hwa mrk' tmp' tc' tl' mcl', hcov',
    hext, hws2, hnda, hrefsa,
    ⟨hstata.1, hstata.2, hstata.3, hstata.4, hstata.5, hstata.6, hstata.7, hstata.8,
     hstata.9, hstata.10⟩,
    Nat.le_trans htl_ge htl_le, htl'_cv, htc', hlow', hmcov', hcm', hin_res, hlit_mem, hres_new⟩

theorem deduce_seed_bin_sem {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {s s0 sa sb : FullState}
    (h0_lt : s.core.confl_lit0.toNat < 2 * s.core.cur_vars)
    (h1_lt : s.core.confl_lit1.toNat < 2 * s.core.cur_vars)
    (hent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause [s.core.confl_lit0.toNat, s.core.confl_lit1.toNat]))
    (hsub : ∀ l ∈ fullActiveResolvent sa.core sa.core.tmp sa.core.mrk sa.core.tmp_len
      sa.core.trail_end, l ∈ fullActiveResolvent sb.core sb.core.tmp sb.core.mrk sb.core.tmp_len
      sb.core.trail_end)
    (hl0_res : (s0.core.confl_lit0.setWidth 32).toNat ∈ fullActiveResolvent sa.core sa.core.tmp
      sa.core.mrk sa.core.tmp_len sa.core.trail_end ∨
      (cnfOfClauses F_cur).EntailsClause
        (cnfClause [litNeg (s0.core.confl_lit0.setWidth 32).toNat]))
    (hl1_res : (s0.core.confl_lit1.setWidth 32).toNat ∈ fullActiveResolvent sb.core sb.core.tmp
      sb.core.mrk sb.core.tmp_len sb.core.trail_end ∨
      (cnfOfClauses F_cur).EntailsClause
        (cnfClause [litNeg (s0.core.confl_lit1.setWidth 32).toNat]))
    (hct : sb.LengthsOk c) (hw : FullWitnessCutInv c F0 F_cur cut sb.core)
    (hcov : FullAnaMarksCov c sb) (hext : FullExtScratchPres s sb)
    (hws2 : sb.scratch.work_stk2 = s.scratch.work_stk2) (hnd : FullArenaVarsNodup sb)
    (hrefs : fullArenaClauseRefs sb = fullArenaClauseRefs s)
    (hstat : FullDeduceStaticEq s.core sb.core)
    (htl_ge : 1 ≤ sb.core.tmp_len) (htl_cv : sb.core.tmp_len ≤ sb.core.cur_vars)
    (htc_eq : sb.core.tmp_cnt =
      (fullCurTrailIdxs sb.core sb.core.mrk sb.core.trail_end).length)
    (hlow : FullLowerInv c sb.core sb.core.tmp sb.core.mrk sb.core.tmp_len)
    (hmcov : FullMarksCov sb.core sb.core.tmp sb.core.mrk sb.core.tmp_len)
    (hcm : FullCurMarksBelow sb.core.trail_end sb.core sb.core.mrk cut)
    (hres : sb.scratch.res_sz = BitVec.ofNat 64 ((sb.core.tmp_len - 1) + sb.core.tmp_cnt))
    (h0_eq : s0.core.confl_lit0 = s.core.confl_lit0)
    (h1_eq : s0.core.confl_lit1 = s.core.confl_lit1) :
    FullDeduceStateInv c F0 F_cur cut sb.core.trail_end s sb := by
  have hmaxv := c.hmaxv; have hcv_le := hstat.cv ▸ hct.core_ok.cur_vars_le
  unfold dimacsBound at hmaxv
  have h0_tr : (s0.core.confl_lit0.setWidth 32).toNat = s.core.confl_lit0.toNat := by
    rw [h0_eq, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
  have h1_tr : (s0.core.confl_lit1.setWidth 32).toNat = s.core.confl_lit1.toNat := by
    rw [h1_eq, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
  rw [h0_tr] at hl0_res; rw [h1_tr] at hl1_res
  refine ⟨hct, hw, hcov, hext, hws2, hnd, hrefs, hstat, htl_ge, htl_cv, htc_eq, hlow, hmcov, hcm,
    entails_of_mem_or_false hent fun l hl => ?_, hres⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl
  · exact hl0_res.imp (fun h => hsub _ h) id
  · exact hl1_res

theorem deduce_seed_rsn_sem {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {s s0 : FullState}
    {mrk' : List (BitVec 8)} {tmp' arena' : List (BitVec 32)}
    {mcl' tc' tl' : Nat} {sc' : FullScratch}
    (hs0_len : s0.LengthsOk c) (hs0_hw : FullWitnessCutInv c F0 F_cur cut s0.core)
    (hs0_st : FullDeduceStaticEq s.core s0.core)
    (h0_res : s0.scratch.res_sz = 0#64) (h0_tl : s0.core.tmp_len = 1)
    (h0_tc : s0.core.tmp_cnt = 0)
    (h0_mrk : ∀ v < c.max_vars, s0.core.mrk[v]?.getD 0#8 = 0#8)
    (h0_cref : s0.core.confl_ref = s.core.confl_ref) (h0_ar : s0.core.arena = s.core.arena)
    (hct2 : s.core.confl_type = 2#64) (hconfl : FullConflictOkCut F_cur cut s)
    (hw1 : FullWitnessCutInv c F0 F_cur cut
      { s0.core with mrk := mrk', tmp := tmp', tmp_cnt := tc', tmp_len := tl',
                     min_clr_len := mcl', arena := arena' })
    (hlen1 : ({ s0 with
      core := { s0.core with mrk := mrk', tmp := tmp', tmp_cnt := tc', tmp_len := tl',
                             min_clr_len := mcl', arena := arena' }
      scratch := sc' } : FullState).LengthsOk c)
    (hcov1 : FullAnaMarksCov c
      { s0 with
        core := { s0.core with mrk := mrk', tmp := tmp', tmp_cnt := tc', tmp_len := tl',
                               min_clr_len := mcl', arena := arena' }
        scratch := sc' })
    (hext' : FullExtScratchPres s0
      { s0 with
        core := { s0.core with mrk := mrk', tmp := tmp', tmp_cnt := tc', tmp_len := tl',
                               min_clr_len := mcl', arena := arena' }
        scratch := sc' })
    (hws2' : sc'.work_stk2 = s0.scratch.work_stk2)
    (htl_ge : s0.core.tmp_len ≤ tl') (htl_cv : tl' ≤ s0.core.cur_vars)
    (htc_le : s0.core.tmp_cnt ≤ tc')
    (hrefs1 : fullArenaClauseRefs
      { s0 with
        core := { s0.core with mrk := mrk', tmp := tmp', tmp_cnt := tc', tmp_len := tl',
                               min_clr_len := mcl', arena := arena' }
        scratch := sc' } = fullArenaClauseRefs s0)
    (hnd1 : FullArenaVarsNodup
      { s0 with
        core := { s0.core with mrk := mrk', tmp := tmp', tmp_cnt := tc', tmp_len := tl',
                               min_clr_len := mcl', arena := arena' }
        scratch := sc' })
    (hmpres : ∀ w < s0.core.cur_vars, s0.core.mrk[w]?.getD 0#8 ≠ 0#8 →
      mrk'[w]?.getD 0#8 = s0.core.mrk[w]?.getD 0#8)
    (htpres : ∀ k < s0.core.tmp_len, tmp'[k]? = s0.core.tmp[k]?)
    (hnewm : ∀ w < s0.core.cur_vars, s0.core.mrk[w]?.getD 0#8 = 0#8 → mrk'[w]?.getD 0#8 ≠ 0#8 →
      ∃ l ∈ fullRsnLits s0 (s0.core.confl_ref.setWidth 32),
        l / 2 = w ∧ w ≠ (0xFFFFFFFF#32).toNat ∧
        0 < (s0.core.lvl[w]?.getD 0#32).toNat ∧
        (s0.core.lvl[w]?.getD 0#32).toNat ≤ s0.core.cur_level)
    (hnewt : ∀ j, s0.core.tmp_len ≤ j → j < tl' →
      let l := (tmp'[j]?.getD 0#32).toNat
      l ∈ fullRsnLits s0 (s0.core.confl_ref.setWidth 32) ∧ l < 2 * s0.core.cur_vars ∧
      l / 2 ≠ (0xFFFFFFFF#32).toNat ∧ s0.core.mrk[l / 2]?.getD 0#8 = 0#8 ∧
      0 < (s0.core.lvl[l / 2]?.getD 0#32).toNat ∧
      (s0.core.lvl[l / 2]?.getD 0#32).toNat < s0.core.cur_level ∧ mrk'[l / 2]?.getD 0#8 ≠ 0#8)
    (hnd_t : ∀ j1 j2, s0.core.tmp_len ≤ j1 → j1 < j2 → j2 < tl' →
      (tmp'[j1]?.getD 0#32).toNat / 2 ≠ (tmp'[j2]?.getD 0#32).toNat / 2)
    (hcnt : tc' - s0.core.tmp_cnt = ((List.range s0.core.cur_vars).filter fun w =>
      decide (s0.core.mrk[w]?.getD 0#8 = 0#8) && decide (mrk'[w]?.getD 0#8 ≠ 0#8) &&
      decide ((s0.core.lvl[w]?.getD 0#32).toNat = s0.core.cur_level)).length)
    (hres_f : sc'.res_sz = s0.scratch.res_sz + BitVec.ofNat 64
      ((List.range s0.core.cur_vars).filter fun w =>
      decide (s0.core.mrk[w]?.getD 0#8 = 0#8) && decide (mrk'[w]?.getD 0#8 ≠ 0#8)).length)
    (hok : s0.core.confl_ref.setWidth 32 ≠ 0xFFFFFFFF#32 ∧
      ∀ l ∈ fullRsnLits s0 (s0.core.confl_ref.setWidth 32), l / 2 < s0.core.cur_vars ∧
        (l / 2 ≠ (0xFFFFFFFF#32).toNat →
          (0 < (s0.core.lvl[l / 2]?.getD 0#32).toNat → mrk'[l / 2]?.getD 0#8 ≠ 0#8) ∧
          (s0.core.mrk[l / 2]?.getD 0#8 = 0#8 →
            (s0.core.lvl[l / 2]?.getD 0#32).toNat ≤ s0.core.cur_level ∧
            (0 < (s0.core.lvl[l / 2]?.getD 0#32).toNat →
              (s0.core.lvl[l / 2]?.getD 0#32).toNat < s0.core.cur_level →
              ∃ j, s0.core.tmp_len ≤ j ∧ j < tl' ∧
                (tmp'[j]?.getD 0#32).toNat / 2 = l / 2))))
    (hext : FullExtScratchPres s s0) (hws2 : s0.scratch.work_stk2 = s.scratch.work_stk2)
    (hrefs0 : fullArenaClauseRefs s0 = fullArenaClauseRefs s) :
    let s1 : FullState :=
      { s0 with
        core := { s0.core with mrk := mrk', tmp := tmp', tmp_cnt := tc', tmp_len := tl',
                               min_clr_len := mcl', arena := arena' }
        scratch := sc' }
    FullDeduceStateInv c F0 F_cur cut s1.core.trail_end s s1 := by
  intro s1
  have hmaxv := c.hmaxv; have har_cap := c.harena; unfold dimacsBound at hmaxv har_cap
  have hcv_le := hs0_len.core_ok.cur_vars_le; have hal_le := hs0_len.core_ok.arena_len_le
  have hcr_info : s.core.confl_ref.toNat ∈ fullArenaClauseRefs s ∧
      fullArenaClauseGarb s s.core.confl_ref.toNat = false ∧
      (∀ l ∈ fullArenaClauseLits s s.core.confl_ref.toNat,
        s.core.vals[l]?.getD 0#8 = 0xFF#8) ∧
      (∀ l ∈ fullArenaClauseLits s s.core.confl_ref.toNat,
        (s.core.lvl[l / 2]?.getD 0#32).toNat = s.core.cur_level →
        ∃ m < cut, (s.core.trl[m]?.getD 0#32).toNat = l ^^^ 1) := by
    have h1 := hconfl.1; have h2 := hconfl.2
    have hne1 : s.core.confl_type ≠ 1#64 := fun he => by rw [hct2] at he; cases he
    rw [ite_eq_right hne1] at h2
    rcases h1 with ⟨hb, _⟩ | ⟨_, hr, hg, hf⟩
    · exact absurd (hct2.symm.trans hb) (by decide)
    · exact ⟨hr, hg, hf, h2⟩
  obtain ⟨href, hng, hfals, hcut_l⟩ := hcr_info
  have href0 : s.core.confl_ref.toNat ∈ fullArenaClauseRefsCore s0.core := by
    change _ ∈ fullArenaClauseRefs s0; rw [hrefs0]; exact href
  have hcr_lt : s.core.confl_ref.toNat < 2 ^ 31 - 1 := by
    have := (hs0_hw.arena.refs_wf _ href0).1; omega
  obtain ⟨hcr_tr, hcr_ne, hcr_lg⟩ := bv64_confl_ref_u32 hcr_lt
  rw [← h0_cref] at hcr_tr hcr_ne hcr_lg
  have hrsn_lits : fullRsnLits s0 (s0.core.confl_ref.setWidth 32) =
      fullArenaClauseLits s s.core.confl_ref.toNat := by
    unfold fullRsnLits fullArenaClauseLits fullArenaClauseLitsCore fullArenaClauseSizeCore
    rw [ite_eq_right (fun h => hcr_ne h), ite_eq_right (fun h => absurd hcr_lg h),
      hcr_tr, h0_cref, h0_ar]
  have hm0_all : ∀ v < s0.core.cur_vars, s0.core.mrk[v]?.getD 0#8 = 0#8 :=
    fun v hv => h0_mrk v (by omega)
  have htl1 : 1 ≤ s0.core.tmp_len := by omega
  have hlow0 : FullLowerInv c s0.core s0.core.tmp s0.core.mrk s0.core.tmp_len := by
    rw [h0_tl]; exact ⟨fun _ h1 h2 => by omega, fun _ _ h1 _ h2 => by omega⟩
  have hmcov0 : FullMarksCov s0.core s0.core.tmp s0.core.mrk s0.core.tmp_len := by
    rw [h0_tl]; exact fun v hv hnz => absurd (hm0_all v hv) hnz
  have hcm0 : FullCurMarksBelow s0.core.trail_end s0.core s0.core.mrk cut := by
    intro j hj hnz _; have hjv : (s0.core.trl[j]?.getD 0#32).toNat / 2 < s0.core.cur_vars := by
      have := hs0_hw.trail_lits_lt j hj; omega
    exact absurd (hm0_all _ hjv) hnz
  have hct0 : (fullCurTrailIdxs s0.core s0.core.mrk s0.core.trail_end).length = 0 := by
    rw [fullCurTrailIdxs, List.filter_eq_nil_iff.mpr fun j hj => by
      rw [List.mem_range] at hj
      have hv : (s0.core.trl[j]?.getD 0#32).toNat / 2 < s0.core.cur_vars := by
        have := hs0_hw.trail_lits_lt j hj; omega
      simp [hm0_all _ hv]]
    rfl
  have hlow1_lits : ∀ q, q ∈ fullRsnLits s0 (s0.core.confl_ref.setWidth 32) →
      q < 2 * s0.core.cur_vars := by
    intro q hq; rw [hrsn_lits] at hq
    have hng0 : fullArenaClauseGarbCore s0.core s.core.confl_ref.toNat = false := by
      change fullArenaClauseGarbCore s.core s.core.confl_ref.toNat = false at hng
      unfold fullArenaClauseGarbCore fullArenaHdrCore; rw [h0_ar]; exact hng
    exact hs0_hw.arena.lits_lt _ href0 hng0 q (by
      unfold fullArenaClauseLits at hq; unfold fullArenaClauseLitsCore fullArenaClauseSizeCore
      rw [h0_ar]; exact hq)
  have hclause : ∀ q, q ∈ fullRsnLits s0 (s0.core.confl_ref.setWidth 32) →
      q / 2 = (0xFFFFFFFF#32).toNat ∨
      ∃ m < s0.core.trail_end, (s0.core.trl[m]?.getD 0#32).toNat = q ^^^ 1 := by
    intro q hq; right
    have hql := hlow1_lits q hq
    rw [hrsn_lits] at hq
    have hqf : s0.core.vals[q]?.getD 0#8 = 0xFF#8 := by rw [hs0_st.vals]; exact hfals q hq
    exact (hs0_hw.vals_false_iff q hql).mp hqf
  have hclause_cut : ∀ q, q ∈ fullRsnLits s0 (s0.core.confl_ref.setWidth 32) →
      q / 2 ≠ (0xFFFFFFFF#32).toNat →
      (s0.core.lvl[q / 2]?.getD 0#32).toNat = s0.core.cur_level →
      ∃ m < cut, (s0.core.trl[m]?.getD 0#32).toNat = q ^^^ 1 := by
    intro q hq _ hcl; rw [hrsn_lits] at hq
    obtain ⟨m, hm, hmeq⟩ := hcut_l q hq (by rwa [← hs0_st.lvl, ← hs0_st.cl])
    exact ⟨m, hm, by rw [hs0_st.trl]; exact hmeq⟩
  obtain ⟨htc1, hlow1, hmcov1, hcm1, _, _, hq_res⟩ := fullAnalyzeStep_preserves
    (k := s0.core) (mrk := s0.core.mrk) (mrk' := mrk') (tmp := s0.core.tmp) (tmp' := tmp')
    (tc := s0.core.tmp_cnt) (tc' := tc') (tl := s0.core.tmp_len) (tl' := tl')
    hs0_len.core_ok hs0_hw (· ∈ fullRsnLits s0 (s0.core.confl_ref.setWidth 32))
    (Nat.le_refl _) htl1 htl_ge htl_cv hs0_len.core_ok.tmp_len_arr hlen1.core_ok.tmp_len_arr
    (by rw [h0_tc, hct0]) htc_le hlow0 hmcov0 hcm0 hlow1_lits hclause
    hclause_cut hmpres htpres hnewm hnewt hnd_t hcnt hok.2
  have hsurj : ∀ w < s0.core.cur_vars, s0.core.mrk[w]?.getD 0#8 = 0#8 →
      mrk'[w]?.getD 0#8 ≠ 0#8 → 0 < (s0.core.lvl[w]?.getD 0#32).toNat →
      (s0.core.lvl[w]?.getD 0#32).toNat < s0.core.cur_level →
      ∃ j, s0.core.tmp_len ≤ j ∧ j < tl' ∧ (tmp'[j]?.getD 0#32).toNat / 2 = w := by
    intro w hw h0 hnz hpos hlt
    obtain ⟨l, hl, hlw, hne, _⟩ := hnewm w hw h0 hnz
    subst hlw
    obtain ⟨j, hj1, hj2, hjeq⟩ := (((hok.2 l hl).2 hne).2 h0).2 hpos hlt
    exact ⟨j, hj1, hj2, hjeq⟩
  have htl_sub := analyzeRsn_tl_sub_eq (k := s0.core) (mrk := s0.core.mrk) (mrk' := mrk')
    (tmp' := tmp') htl_ge
    (fun j h1 h2 => let h := hnewt j h1 h2; ⟨by have := h.2.1; omega, h.2.2.2.1, h.2.2.2.2.1,
      h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩)
    hnd_t (fun w hw h0 hnz => let ⟨_, _, _, _, h1, h2⟩ := hnewm w hw h0 hnz; ⟨h1, h2⟩) hsurj
  have hall_eq := analyzeRsn_all_marked_eq (k := s0.core) (mrk := s0.core.mrk) (mrk' := mrk')
    (fun w hw h0 hnz => let ⟨_, _, _, _, h1, h2⟩ := hnewm w hw h0 hnz; ⟨h1, h2⟩)
  have hres1 : sc'.res_sz = BitVec.ofNat 64 ((tl' - 1) + tc') := by
    rw [hres_f, h0_res, BitVec.zero_add, hall_eq, ← htl_sub, ← hcnt]
    exact congrArg (BitVec.ofNat 64) (by omega)
  have hent_src : (cnfOfClauses F_cur).EntailsClause
      (cnfClause (fullRsnLits s0 (s0.core.confl_ref.setWidth 32))) := by
    rw [hrsn_lits]
    have hng0 : fullArenaClauseGarbCore s0.core s.core.confl_ref.toNat = false := by
      change fullArenaClauseGarbCore s.core s.core.confl_ref.toNat = false at hng
      unfold fullArenaClauseGarbCore fullArenaHdrCore; rw [h0_ar]; exact hng
    have he := hs0_hw.arena.entails _ href0 hng0
    change (cnfOfClauses F_cur).EntailsClause
      (cnfClause (fullArenaClauseLitsCore s.core s.core.confl_ref.toNat))
    unfold fullArenaClauseLitsCore fullArenaClauseSizeCore; rw [← h0_ar]; exact he
  have hent1 : (cnfOfClauses F_cur).EntailsClause
      (cnfClause (fullActiveResolvent s0.core tmp' mrk' tl' s0.core.trail_end)) :=
    entails_of_mem_or_false hent_src fun q hq => by
      have hql := hlow1_lits q hq
      have hqne : q / 2 ≠ (0xFFFFFFFF#32).toNat := by
        have : (0xFFFFFFFF#32).toNat = 2 ^ 32 - 1 := rfl; omega
      exact (hq_res q hq).resolve_left (fun he => absurd he hqne)
  exact ⟨hlen1, hw1, hcov1, ⟨hext'.1.trans hext.1, hext'.2.trans hext.2⟩, hws2'.trans hws2, hnd1,
    hrefs1.trans hrefs0,
    ⟨hs0_st.1, hs0_st.2, hs0_st.3, hs0_st.4, hs0_st.5, hs0_st.6, hs0_st.7, hs0_st.8,
     hs0_st.9, hs0_st.10⟩,
    Nat.le_trans htl1 htl_ge, htl_cv, htc1, hlow1, hmcov1, hcm1, hent1, hres1⟩

theorem deduce_loop_rsn_sem {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut idx' : Nat} {s sl1 : FullState}
    {mrk' : List (BitVec 8)} {tmp' arena' : List (BitVec 32)}
    {mcl' tc' tl' : Nat} {sc' : FullScratch} {p rsn : BitVec 32}
    (hs1_len : sl1.LengthsOk c) (hs1_hw : FullWitnessCutInv c F0 F_cur cut sl1.core)
    (hs1_st : FullDeduceStaticEq s.core sl1.core)
    (h1_res : sl1.scratch.res_sz = BitVec.ofNat 64 ((sl1.core.tmp_len - 1) + sl1.core.tmp_cnt + 1))
    (h1_tl1 : 1 ≤ sl1.core.tmp_len)
    (h1_tc_eq : sl1.core.tmp_cnt = (fullCurTrailIdxs sl1.core sl1.core.mrk idx').length)
    (h1_low : FullLowerInv c sl1.core sl1.core.tmp sl1.core.mrk sl1.core.tmp_len)
    (h1_mcov : FullMarksCov sl1.core sl1.core.tmp sl1.core.mrk sl1.core.tmp_len)
    (h1_cm : FullCurMarksBelow idx' sl1.core sl1.core.mrk cut)
    (h1_ent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause (fullActiveResolvent sl1.core sl1.core.tmp sl1.core.mrk sl1.core.tmp_len
        (idx' + 1))))
    (hiu_cut : idx' < cut) (hiu_te : idx' < sl1.core.trail_end)
    (hp_get : (sl1.core.trl[idx']?.getD 0#32).toNat = p.toNat)
    (hr_get : sl1.core.rsns[p.toNat / 2]?.getD 0xFFFFFFFF#32 = rsn)
    (hmnz : sl1.core.mrk[p.toNat / 2]?.getD 0#8 ≠ 0#8)
    (hpl_cl : (sl1.core.lvl[p.toNat / 2]?.getD 0#32).toNat = sl1.core.cur_level)
    (hw2 : FullWitnessCutInv c F0 F_cur cut
      { sl1.core with mrk := mrk', tmp := tmp', tmp_cnt := tc', tmp_len := tl',
                      min_clr_len := mcl', arena := arena' })
    (hlen2 : ({ sl1 with
      core := { sl1.core with mrk := mrk', tmp := tmp', tmp_cnt := tc', tmp_len := tl',
                              min_clr_len := mcl', arena := arena' }
      scratch := sc' } : FullState).LengthsOk c)
    (hcov2 : FullAnaMarksCov c
      { sl1 with
        core := { sl1.core with mrk := mrk', tmp := tmp', tmp_cnt := tc', tmp_len := tl',
                                min_clr_len := mcl', arena := arena' }
        scratch := sc' })
    (hext' : FullExtScratchPres sl1
      { sl1 with
        core := { sl1.core with mrk := mrk', tmp := tmp', tmp_cnt := tc', tmp_len := tl',
                                min_clr_len := mcl', arena := arena' }
        scratch := sc' })
    (hws2' : sc'.work_stk2 = sl1.scratch.work_stk2)
    (htl_ge : sl1.core.tmp_len ≤ tl') (htl_cv : tl' ≤ sl1.core.cur_vars)
    (htc_le : sl1.core.tmp_cnt ≤ tc')
    (hrefs2 : fullArenaClauseRefs
      { sl1 with
        core := { sl1.core with mrk := mrk', tmp := tmp', tmp_cnt := tc', tmp_len := tl',
                                min_clr_len := mcl', arena := arena' }
        scratch := sc' } = fullArenaClauseRefs sl1)
    (hnd2 : FullArenaVarsNodup
      { sl1 with
        core := { sl1.core with mrk := mrk', tmp := tmp', tmp_cnt := tc', tmp_len := tl',
                                min_clr_len := mcl', arena := arena' }
        scratch := sc' })
    (hmpres : ∀ w < sl1.core.cur_vars, sl1.core.mrk[w]?.getD 0#8 ≠ 0#8 →
      mrk'[w]?.getD 0#8 = sl1.core.mrk[w]?.getD 0#8)
    (htpres : ∀ k < sl1.core.tmp_len, tmp'[k]? = sl1.core.tmp[k]?)
    (hnewm : ∀ w < sl1.core.cur_vars, sl1.core.mrk[w]?.getD 0#8 = 0#8 → mrk'[w]?.getD 0#8 ≠ 0#8 →
      ∃ l ∈ fullRsnLits sl1 rsn, l / 2 = w ∧ w ≠ p.toNat / 2 ∧
        0 < (sl1.core.lvl[w]?.getD 0#32).toNat ∧
        (sl1.core.lvl[w]?.getD 0#32).toNat ≤ sl1.core.cur_level)
    (hnewt : ∀ j, sl1.core.tmp_len ≤ j → j < tl' →
      let l := (tmp'[j]?.getD 0#32).toNat
      l ∈ fullRsnLits sl1 rsn ∧ l < 2 * sl1.core.cur_vars ∧ l / 2 ≠ p.toNat / 2 ∧
      sl1.core.mrk[l / 2]?.getD 0#8 = 0#8 ∧ 0 < (sl1.core.lvl[l / 2]?.getD 0#32).toNat ∧
      (sl1.core.lvl[l / 2]?.getD 0#32).toNat < sl1.core.cur_level ∧ mrk'[l / 2]?.getD 0#8 ≠ 0#8)
    (hnd_t : ∀ j1 j2, sl1.core.tmp_len ≤ j1 → j1 < j2 → j2 < tl' →
      (tmp'[j1]?.getD 0#32).toNat / 2 ≠ (tmp'[j2]?.getD 0#32).toNat / 2)
    (hcnt : tc' - sl1.core.tmp_cnt = ((List.range sl1.core.cur_vars).filter fun w =>
      decide (sl1.core.mrk[w]?.getD 0#8 = 0#8) && decide (mrk'[w]?.getD 0#8 ≠ 0#8) &&
      decide ((sl1.core.lvl[w]?.getD 0#32).toNat = sl1.core.cur_level)).length)
    (hres_f : sc'.res_sz = sl1.scratch.res_sz +
      BitVec.ofNat 64 ((List.range sl1.core.cur_vars).filter
      fun w => decide (sl1.core.mrk[w]?.getD 0#8 = 0#8) &&
        decide (mrk'[w]?.getD 0#8 ≠ 0#8)).length)
    (hok : rsn ≠ 0xFFFFFFFF#32 ∧
      ∀ l ∈ fullRsnLits sl1 rsn, l / 2 < sl1.core.cur_vars ∧
        (l / 2 ≠ p.toNat / 2 →
          (0 < (sl1.core.lvl[l / 2]?.getD 0#32).toNat → mrk'[l / 2]?.getD 0#8 ≠ 0#8) ∧
          (sl1.core.mrk[l / 2]?.getD 0#8 = 0#8 →
            (sl1.core.lvl[l / 2]?.getD 0#32).toNat ≤ sl1.core.cur_level ∧
            (0 < (sl1.core.lvl[l / 2]?.getD 0#32).toNat →
              (sl1.core.lvl[l / 2]?.getD 0#32).toNat < sl1.core.cur_level →
              ∃ j, sl1.core.tmp_len ≤ j ∧ j < tl' ∧
                (tmp'[j]?.getD 0#32).toNat / 2 = l / 2))))
    (hext : FullExtScratchPres s sl1) (hws2 : sl1.scratch.work_stk2 = s.scratch.work_stk2)
    (hrefs0 : fullArenaClauseRefs sl1 = fullArenaClauseRefs s) :
    let s2 : FullState :=
      { sl1 with
        core := { sl1.core with mrk := mrk', tmp := tmp', tmp_cnt := tc', tmp_len := tl',
                                min_clr_len := mcl', arena := arena' }
        scratch := sc' }
    s2.LengthsOk c ∧ FullWitnessCutInv c F0 F_cur cut s2.core ∧ FullAnaMarksCov c s2 ∧
    FullExtScratchPres s s2 ∧ s2.scratch.work_stk2 = s.scratch.work_stk2 ∧
    FullArenaVarsNodup s2 ∧ fullArenaClauseRefs s2 = fullArenaClauseRefs s ∧
    FullDeduceStaticEq s.core s2.core ∧ 1 ≤ tl' ∧ tl' ≤ s2.core.cur_vars ∧
    tc' = (fullCurTrailIdxs s2.core mrk' idx').length ∧
    FullLowerInv c s2.core tmp' mrk' tl' ∧
    FullMarksCov s2.core tmp' mrk' tl' ∧ FullCurMarksBelow idx' s2.core mrk' cut ∧
    (cnfOfClauses F_cur).EntailsClause
      (cnfClause (fullActiveResolvent s2.core tmp' mrk' tl' idx')) ∧
    sc'.res_sz = BitVec.ofNat 64 ((tl' - 1) + tc' + 1) ∧
    (∀ l ∈ fullRsnLits sl1 rsn, l / 2 ≠ p.toNat / 2 →
      0 < (s2.core.lvl[l / 2]?.getD 0#32).toNat → mrk'[l / 2]?.getD 0#8 ≠ 0#8) := by
  intro s2
  have _ := hmnz; have _ := hpl_cl
  have hri := hs1_hw.reason_inv_cut idx' hiu_cut
  dsimp only at hri; rw [hp_get, hr_get] at hri
  have hri := hri hok.1
  have hr_lits_prop : (∀ q ∈ fullRsnLits sl1 rsn, q < 2 * sl1.core.cur_vars) ∧
      (∀ q ∈ fullRsnLits sl1 rsn, q / 2 = p.toNat / 2 ∨
        ∃ m < idx', (sl1.core.trl[m]?.getD 0#32).toNat = q ^^^ 1) ∧
      (∀ q ∈ fullRsnLits sl1 rsn, q / 2 ≠ p.toNat / 2 →
        (sl1.core.lvl[q / 2]?.getD 0#32).toNat = sl1.core.cur_level →
        ∃ m < cut, (sl1.core.trl[m]?.getD 0#32).toNat = q ^^^ 1) := by
    by_cases hbin : (rsn &&& 0x80000000#32) ≠ 0#32
    · rw [ite_eq_left hbin] at hri
      obtain ⟨hot_lt, _, m, hm, hmeq, _⟩ := hri
      have hlits : fullRsnLits sl1 rsn = [(rsn &&& 0x7FFFFFFF#32).toNat] := by
        simp [fullRsnLits, hok.1, hbin]
      refine ⟨fun q hq => by rw [hlits, List.mem_singleton] at hq; exact hq ▸ hot_lt,
        fun q hq => by rw [hlits, List.mem_singleton] at hq; exact Or.inr ⟨m, hm, hq ▸ hmeq⟩,
        fun q hq _ _ => by rw [hlits, List.mem_singleton] at hq; exact ⟨m, by omega, hq ▸ hmeq⟩⟩
    · rw [ite_eq_right hbin] at hri
      obtain ⟨href, hng, hmem⟩ := hri
      have hbin_eq : (rsn &&& 0x80000000#32) = 0#32 := Classical.not_not.mp hbin
      have hlits : fullRsnLits sl1 rsn = fullArenaClauseLitsCore sl1.core rsn.toNat := by
        simp [fullRsnLits, hok.1, hbin_eq, fullArenaClauseLits]
      refine ⟨fun q hq => hs1_hw.arena.lits_lt rsn.toNat href hng q (hlits ▸ hq),
        fun q hq => by
          rcases hmem q (hlits ▸ hq) with rfl | ⟨m, hm, hmeq, _⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨m, hm, hmeq⟩,
        fun q hq hnev _ => by
          rcases hmem q (hlits ▸ hq) with rfl | ⟨m, hm, hmeq, _⟩
          · exact absurd rfl hnev
          · exact ⟨m, by omega, hmeq⟩⟩
  obtain ⟨htc2, hlow2, hmcov2, hcm2, hlow_sub, hcur_sub, hq_res⟩ := fullAnalyzeStep_preserves
    (k := sl1.core) (mrk := sl1.core.mrk) (mrk' := mrk') (tmp := sl1.core.tmp) (tmp' := tmp')
    (tc := sl1.core.tmp_cnt) (tc' := tc') (tl := sl1.core.tmp_len) (tl' := tl')
    hs1_len.core_ok hs1_hw (· ∈ fullRsnLits sl1 rsn) (Nat.le_of_lt hiu_te) h1_tl1 htl_ge htl_cv
    hs1_len.core_ok.tmp_len_arr hlen2.core_ok.tmp_len_arr h1_tc_eq htc_le h1_low h1_mcov h1_cm
    hr_lits_prop.1 hr_lits_prop.2.1 hr_lits_prop.2.2 hmpres htpres hnewm hnewt hnd_t hcnt hok.2
  have hsurj : ∀ w < sl1.core.cur_vars, sl1.core.mrk[w]?.getD 0#8 = 0#8 →
      mrk'[w]?.getD 0#8 ≠ 0#8 → 0 < (sl1.core.lvl[w]?.getD 0#32).toNat →
      (sl1.core.lvl[w]?.getD 0#32).toNat < sl1.core.cur_level →
      ∃ j, sl1.core.tmp_len ≤ j ∧ j < tl' ∧ (tmp'[j]?.getD 0#32).toNat / 2 = w := by
    intro w hw h0 hnz hpos hlt
    obtain ⟨l, hl, hlw, hne, _⟩ := hnewm w hw h0 hnz
    subst hlw
    obtain ⟨j, hj1, hj2, hjeq⟩ := (((hok.2 l hl).2 hne).2 h0).2 hpos hlt
    exact ⟨j, hj1, hj2, hjeq⟩
  have htl_sub := analyzeRsn_tl_sub_eq (k := sl1.core) (mrk := sl1.core.mrk) (mrk' := mrk')
    (tmp' := tmp') htl_ge
    (fun j h1 h2 => let h := hnewt j h1 h2; ⟨by have := h.2.1; omega, h.2.2.2.1, h.2.2.2.2.1,
      h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩)
    hnd_t (fun w hw h0 hnz => let ⟨_, _, _, _, h1, h2⟩ := hnewm w hw h0 hnz; ⟨h1, h2⟩) hsurj
  have hall_eq := analyzeRsn_all_marked_eq (k := sl1.core) (mrk := sl1.core.mrk) (mrk' := mrk')
    (fun w hw h0 hnz => let ⟨_, _, _, _, h1, h2⟩ := hnewm w hw h0 hnz; ⟨h1, h2⟩)
  have hres2 : sc'.res_sz = BitVec.ofNat 64 ((tl' - 1) + tc' + 1) := by
    rw [hres_f, h1_res, hall_eq, ← htl_sub, ← hcnt, ← BitVec.ofNat_add]
    exact congrArg (BitVec.ofNat 64) (by omega)
  have hent2 : (cnfOfClauses F_cur).EntailsClause
      (cnfClause (fullActiveResolvent sl1.core tmp' mrk' tl' idx')) := by
    have hresol : ∀ cRsn : List Nat, (cnfOfClauses F_cur).EntailsClause (cnfClause cRsn) →
        (∀ q ∈ cRsn, q = p.toNat ∨
          (q ∈ fullRsnLits sl1 rsn ∧ q / 2 ≠ p.toNat / 2)) →
        (cnfOfClauses F_cur).EntailsClause
          (cnfClause (fullActiveResolvent sl1.core tmp' mrk' tl' idx')) := by
      intro cRsn hce hsub
      refine entails_resolve_to (p := p.toNat ^^^ 1) h1_ent hce (fun l hl => ?_) (fun q hq => ?_)
      · unfold fullActiveResolvent at hl
        rcases List.mem_append.mp hl with hl_lo | hl_cu
        · exact Or.inr (Or.inl (List.mem_append_left _ (hlow_sub l hl_lo)))
        · unfold fullCurLits at hl_cu
          obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hl_cu
          rw [fullCurTrailIdxs, List.mem_filter, List.mem_range] at hj
          by_cases hji : j = idx'
          · subst j; rw [hp_get]; exact Or.inl rfl
          · right; left; apply List.mem_append_right
            refine hcur_sub _ (List.mem_map.mpr ⟨j, List.mem_filter.mpr
              ⟨List.mem_range.mpr (by omega), hj.2⟩, rfl⟩)
      · rcases hsub q hq with rfl | ⟨hq_r, hq_ne⟩
        · exact Or.inl (by change p.toNat = litNeg (litNeg p.toNat); rw [litNeg_litNeg])
        · right; exact (hq_res q hq_r).resolve_left hq_ne
    by_cases hbin : (rsn &&& 0x80000000#32) ≠ 0#32
    · rw [ite_eq_left hbin] at hri
      obtain ⟨_, hce, m, hm, hmeq, _⟩ := hri
      refine hresol _ hce fun q hq => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact Or.inl rfl
      · right; refine ⟨by simp [fullRsnLits, hok.1, hbin], fun he => ?_⟩
        have hidx_eq := hs1_hw.trail_vars_nodup m idx' (by omega) hiu_te
          (by rw [hmeq, litNeg_div2, hp_get, he])
        omega
    · rw [ite_eq_right hbin] at hri
      obtain ⟨href, hng, hmem⟩ := hri
      have hbin_eq : (rsn &&& 0x80000000#32) = 0#32 := Classical.not_not.mp hbin
      refine hresol _ (hs1_hw.arena.entails rsn.toNat href hng) fun q hq => ?_
      rcases hmem q hq with rfl | ⟨m, hm, hmeq, _⟩
      · exact Or.inl rfl
      · right; refine ⟨by simpa [fullRsnLits, hok.1, hbin_eq, fullArenaClauseLits] using hq,
          fun he => ?_⟩
        have hidx_eq := hs1_hw.trail_vars_nodup m idx' (by omega) hiu_te
          (by rw [hmeq, litNeg_div2, hp_get, he])
        omega
  exact ⟨hlen2, hw2, hcov2, ⟨hext'.1.trans hext.1, hext'.2.trans hext.2⟩, hws2'.trans hws2, hnd2,
    hrefs2.trans hrefs0,
    ⟨hs1_st.1, hs1_st.2, hs1_st.3, hs1_st.4, hs1_st.5, hs1_st.6, hs1_st.7, hs1_st.8,
     hs1_st.9, hs1_st.10⟩,
    Nat.le_trans h1_tl1 htl_ge, htl_cv, htc2, hlow2, hmcov2, hcm2, hent2, hres2,
    fun l hl hne hpos => ((hok.2 l hl).2 hne).1 hpos⟩

theorem deduce_otfs_old_cr_nonactive {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {cut idx' : Nat} {s s_sub : FullState}
    {p rsn : BitVec 32} {old_ct old_cr : BitVec 64}
    (hw0 : FullWitnessCutInv c F0 F_cur cut s.core) (hconfl : FullConflictOkCut F_cur cut s)
    (hiu_cut : idx' < cut) (hiu_te : idx' < s.core.trail_end)
    (hp_get : (s.core.trl[idx']?.getD 0#32).toNat = p.toNat)
    (hr_get : s.core.rsns[p.toNat / 2]?.getD 0xFFFFFFFF#32 = rsn)
    (hrsn_ne : rsn ≠ 0xFFFFFFFF#32) (hrsn_lg : (rsn &&& 0x80000000#32) = 0#32)
    (hct_eq : old_ct = s.core.confl_type) (hcr_eq : old_cr = s.core.confl_ref)
    (hstat : FullDeduceStaticEq s.core s_sub.core) :
    old_ct = 2#64 → old_cr ≠ 0xFFFFFFFF#64 →
    rsn.toNat ≠ old_cr.toNat ∧
    ∀ t < s_sub.core.trail_end,
      let v := (s_sub.core.trl[t]?.getD 0#32).toNat / 2
      let rsn_t := s_sub.core.rsns[v]?.getD 0xFFFFFFFF#32
      (t < idx' ∨ (s_sub.core.lvl[v]?.getD 0#32).toNat < s_sub.core.cur_level) →
      rsn_t ≠ 0xFFFFFFFF#32 → (rsn_t &&& 0x80000000#32) = 0#32 →
      rsn_t.toNat ≠ old_cr.toNat := by
  intro ho2 _
  have hct2 : s.core.confl_type = 2#64 := hct_eq.symm.trans ho2
  rcases hconfl.1 with ⟨h1, _⟩ | ⟨_, _, _, hfals⟩
  · exact absurd (hct2.symm.trans h1) (by decide)
  · rw [← hcr_eq] at hfals
    have hrsn_ne_cr : rsn.toNat ≠ old_cr.toNat := fun heq => by
      have hp_mem : p.toNat ∈ fullArenaClauseLits s old_cr.toNat := by
        rw [← heq]
        have hm := hw0.reason_lit_mem_cut idx' hiu_cut
        dsimp only at hm; rw [hp_get, hr_get] at hm; exact hm hrsn_ne hrsn_lg
      have hp_t : s.core.vals[p.toNat]?.getD 0#8 = 1#8 :=
        (hw0.vals_true_iff _ (by rw [← hp_get]; exact hw0.trail_lits_lt idx' hiu_te)).mpr
          ⟨idx', hiu_te, hp_get⟩
      have hp_f := hfals _ hp_mem
      rw [hp_t] at hp_f; cases hp_f
    refine ⟨hrsn_ne_cr, fun t ht hcond hne hlg => ?_⟩
    rw [hstat.te] at ht
    rw [hstat.trl, hstat.lvl, hstat.cl] at hcond
    rw [hstat.trl, hstat.rsns] at hne hlg ⊢
    exact falsified_clause_nonactive (canonCut_to_anaCut hw0) hfals t ht
      (hcond.elim (fun h => Or.inl (Nat.lt_trans h hiu_cut)) Or.inr) hne hlg

theorem fullExtScratchPres_trans {s0 s1 s2 : FullState}
    (h1 : FullExtScratchPres s0 s1) (h2 : FullExtScratchPres s1 s2) :
    FullExtScratchPres s0 s2 :=
  ⟨h2.1.trans h1.1, h2.2.trans h1.2⟩

theorem fullAnaMarksCov_of_clear {c : FullCfg} {s : FullState}
    (hmrk : ∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8) (hmcl : s.core.min_clr_len = 0) :
    FullAnaMarksCov c s :=
  ⟨by omega, by simp [hmcl], fun _ hk => by omega, fun v hv hnz => absurd (hmrk v hv) hnz⟩

private theorem fullArenaClauseGarb_of_ar_eq {s1 s2 : FullState}
    (har : s2.core.arena = s1.core.arena) {r : Nat} :
    fullArenaClauseGarb s2 r = fullArenaClauseGarb s1 r := by
  unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore; rw [har]

private theorem fullArenaClauseLits_of_ar_eq {s1 s2 : FullState}
    (har : s2.core.arena = s1.core.arena) {r : Nat} :
    fullArenaClauseLits s2 r = fullArenaClauseLits s1 r := by
  unfold fullArenaClauseLits fullArenaClauseLitsCore fullArenaClauseSizeCore; rw [har]

theorem fullDeduce_uip_entails {F_cur : List (List Nat)} {k : FullCoreState}
    {tmp : List (BitVec 32)} {mrk : List (BitVec 8)} {tl idx' : Nat} {p : BitVec 32}
    (hct0 : (fullCurTrailIdxs k mrk idx').length = 0)
    (hcl : fullCurLits k mrk (idx' + 1) = fullCurLits k mrk idx' ++ [p.toNat ^^^ 1])
    (hent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause (fullActiveResolvent k tmp mrk tl (idx' + 1)))) :
    (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((p ^^^ 1#32).toNat :: fullLowerLits tmp tl)) := by
  have hcur_nil : fullCurLits k mrk idx' = [] := by
    unfold fullCurLits; rw [List.eq_nil_of_length_eq_zero hct0]; rfl
  have hpx : (p ^^^ 1#32).toNat = p.toNat ^^^ 1 := bv32_xor_1 p
  refine entails_of_mem_or_false hent fun l hl => Or.inl ?_
  unfold fullActiveResolvent at hl; rw [hcl, hcur_nil, List.nil_append] at hl
  rcases List.mem_append.mp hl with hl1 | hl2
  · exact List.mem_cons_of_mem _ hl1
  · rw [List.mem_singleton.mp hl2, hpx]; exact List.mem_cons_self

private theorem fullLowerLits_tmp_take {tmp : List (BitVec 32)} {tl : Nat} {uip : BitVec 32}
    (h1 : 1 ≤ tl) (htl : tl ≤ tmp.length) (h0 : tmp[0]? = some uip) :
    (tmp.take tl).map BitVec.toNat = uip.toNat :: fullLowerLits tmp tl := by
  cases tmp with
  | nil => simp at h0
  | cons x xs =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h0; subst h0
    cases tl with
    | zero => omega
    | succ n => simp [fullLowerLits]

theorem deduce_clear_ret0_wp {Γ : Env}
    (hClear : ∀ a m Q X, fullClearAnaSpec a m Q X → Γ "full_clear_ana" [i64] [] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {cut' : Nat}
    {s s1 : FullState} {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost} {m1 : Mem 64}
    (hQ : ∀ r s' m',
      s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 2#64 ∨ r = 20#64) →
      s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      (r = 20#64 → F0.Unsat ∧ FullOtfsInvW c F0 F_cur s' ∧
        s'.core.cur_level ≤ s.core.cur_level ∧ s'.core.dense_mode = s.core.dense_mode) →
      (r = 0#64 → FullOtfsInvW c F0 F_cur s') →
      (r = 1#64 → FullOtfsInvW c F0 F_cur s' ∧ s'.core.cur_level = s.core.cur_level ∧
        1 ≤ s'.core.tmp_len ∧ s'.core.tmp_len ≤ s'.core.cur_vars ∧
        ((s'.core.tmp.take s'.core.tmp_len).map fun x => x.toNat / 2).Nodup ∧
        (∀ k < s'.core.tmp_len, let l := (s'.core.tmp[k]?.getD 0#32).toNat
          l < 2 * s'.core.cur_vars ∧ s'.core.vals[l]?.getD 0#8 = 0xFF#8) ∧
        (∀ k, 1 ≤ k → k < s'.core.tmp_len →
          let lv := (s'.core.lvl[(s'.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
          0 < lv ∧ lv < s'.core.cur_level) ∧
        (s'.core.lvl[(s'.core.tmp[0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat =
          s'.core.cur_level ∧
        (cnfOfClauses F_cur).EntailsClause
          (cnfClause ((s'.core.tmp.take s'.core.tmp_len).map BitVec.toNat))) →
      (r = 2#64 → ∃ cut' ≤ s'.core.trail_end,
        FullCutInvW c F0 F_cur cut' s' ∧ s'.core.cur_level = s.core.cur_level ∧
        FullConflictOkCut F_cur cut' s') →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m')
    (hlen1 : s1.LengthsOk c) (hw1 : FullWitnessCutInv c F0 F_cur cut' s1.core)
    (hcov1 : FullAnaMarksCov c s1) (hext0 : FullExtScratchOk c s) (hext1 : FullExtScratchPres s s1)
    (hws2 : s1.scratch.work_stk2 = s.scratch.work_stk2) (hnd1 : FullArenaVarsNodup s1)
    (hrefs1 : fullArenaClauseRefs s1 = fullArenaClauseRefs s)
    (hstat1 : FullDeduceStaticEq s.core s1.core) (hdm0 : s.core.dense_mode = 0#64)
    (hm0_lm : FullLitMarksClear c s) (hm1 : (FullMem c s1 ⋆ R) m1) :
    wp Γ Q X (.call (rs := [i64]) (as := [i64]) (bs := []) "full_clear_ana" (Arg.var c.hdr, ())
      (fun _ => .ret (Arg.imm 0#64, ()))) m1 := by
  refine deduce_clear_ana_wp hClear hlen1 hw1 hcov1 hext0 hext1 hnd1 hrefs1 hstat1.lm
    (hstat1.dm.trans hdm0) hm0_lm hm1 fun mrk' m_c hlen_c hotfs_c _ hm_c => ?_
  fa_fast_steps
  exact hQ 0#64 _ m_c hlen_c (Or.inl rfl) hstat1.cv hstat1.fuel hws2
    (fun h => by cases h) (fun _ => hotfs_c) (fun h => by cases h) (fun h => by cases h) hm_c

theorem deduce_bump_clear_ret_wp {Γ : Env}
    (hBump : ∀ a m Q X, fullBumpAnalyzedSpec a m Q X →
      Γ "full_bump_analyzed" [i64] [] a m Q X)
    (hClear : ∀ a m Q X, fullClearAnaSpec a m Q X → Γ "full_clear_ana" [i64] [] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {cut' : Nat}
    {s s1 : FullState} {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost} {m1 : Mem 64}
    (retv : BitVec 64)
    (hlen1 : s1.LengthsOk c) (hw1 : FullWitnessCutInv c F0 F_cur cut' s1.core)
    (hcov1 : FullAnaMarksCov c s1) (hext0 : FullExtScratchOk c s) (hext1 : FullExtScratchPres s s1)
    (hws2 : s1.scratch.work_stk2 = s.scratch.work_stk2) (hnd1 : FullArenaVarsNodup s1)
    (hrefs1 : fullArenaClauseRefs s1 = fullArenaClauseRefs s)
    (hstat1 : FullDeduceStaticEq s.core s1.core) (hdm0 : s.core.dense_mode = 0#64)
    (hm0_lm : FullLitMarksClear c s) (hm1 : (FullMem c s1 ⋆ R) m1)
    (hK : ∀ mrk_c sc_b m_c,
      let s_c : FullState :=
        { s1 with core := { s1.core with mrk := mrk_c, min_clr_len := 0 }, scratch := sc_b }
      s_c.LengthsOk c → FullOtfsInvW c F0 F_cur s_c → FullWitnessCutInv c F0 F_cur cut' s_c.core →
      FullCutInvW c F0 F_cur cut' s_c → s_c.core.cur_vars = s.core.cur_vars →
      s_c.core.cur_level = s.core.cur_level → s_c.core.fuel = s.core.fuel →
      s_c.scratch.work_stk2 = s.scratch.work_stk2 → (FullMem c s_c ⋆ R) m_c →
      Q (retv, ()) m_c) :
    wp Γ Q X (.call (rs := [i64]) (as := [i64]) (bs := []) "full_bump_analyzed" (Arg.var c.hdr, ())
      (fun _ => .call (rs := [i64]) (as := [i64]) (bs := []) "full_clear_ana" (Arg.var c.hdr, ())
        (fun _ => .ret (Arg.imm retv, ())))) m1 := by
  refine wp_call_of_spec _ _ (hBump (c.hdr, ()) _ _ _ ⟨c, s1, R, rfl, hlen1, hcov1, hm1, ?_⟩)
  intro mrk_b mcl_b sc_b m_b _ hlen_b hcov_b hext_b hws2_b hm_b
  let s_b : FullState :=
    { s1 with core := { s1.core with mrk := mrk_b, min_clr_len := mcl_b }, scratch := sc_b }
  have hw_b : FullWitnessCutInv c F0 F_cur cut' s_b.core :=
    deduce_same_core_cut hw1 mrk_b s1.core.tmp s1.core.tmp_cnt s1.core.tmp_len mcl_b
  have hext_sb := fullExtScratchPres_trans hext1 hext_b
  have hnd_b : FullArenaVarsNodup s_b := hnd1
  have hrefs_b : fullArenaClauseRefs s_b = fullArenaClauseRefs s := hrefs1
  have hdm_b : s_b.core.dense_mode = 0#64 := hstat1.dm.trans hdm0
  refine deduce_clear_ana_wp hClear hlen_b hw_b hcov_b hext0 hext_sb hnd_b hrefs_b hstat1.lm
    hdm_b hm0_lm hm_b fun mrk_c m_c hlen_c hotfs_c hw_c hm_c => ?_
  fa_fast_steps
  let s_c : FullState :=
    { s1 with core := { s1.core with mrk := mrk_c, min_clr_len := 0 }, scratch := sc_b }
  have hcutw : FullCutInvW c F0 F_cur cut' s_c :=
    ⟨hlen_c, hw_c, hotfs_c.2.2.1, hotfs_c.2.2.2.1, hotfs_c.2.2.2.2.1, hotfs_c.2.2.2.2.2⟩
  exact hK mrk_c sc_b m_c hlen_c hotfs_c hw_c hcutw hstat1.cv hstat1.cl hstat1.fuel
    (hws2_b.trans hws2) hm_c

theorem deduce_conflOk_same_of_clear {F_cur : List (List Nat)} {cut' : Nat}
    {s1 s2 : FullState}
    (hc : FullConflictOkCut F_cur cut' s1)
    (hct : s2.core.confl_type = s1.core.confl_type)
    (hcr : s2.core.confl_ref = s1.core.confl_ref)
    (hc0 : s2.core.confl_lit0 = s1.core.confl_lit0)
    (hc1 : s2.core.confl_lit1 = s1.core.confl_lit1)
    (hcv : s2.core.cur_vars = s1.core.cur_vars)
    (hvals : s2.core.vals = s1.core.vals)
    (hlvl : s2.core.lvl = s1.core.lvl)
    (htrl : s2.core.trl = s1.core.trl)
    (hcl : s2.core.cur_level = s1.core.cur_level)
    (har : s2.core.arena = s1.core.arena) (hal : s2.core.arena_len = s1.core.arena_len) :
    FullConflictOkCut F_cur cut' s2 := by
  rcases hc with ⟨h1, h2⟩
  refine ⟨?_, ?_⟩
  · rcases h1 with ⟨ht, h0, h1l, hf0, hf1, hen⟩ | ⟨ht, hr, hg, hfa⟩
    · left; refine ⟨hct.trans ht, by simpa [hc0, hcv] using h0, by simpa [hc1, hcv] using h1l,
        by simpa [hvals, hc0] using hf0, by simpa [hvals, hc1] using hf1,
        by simpa [hc0, hc1] using hen⟩
    · right; refine ⟨hct.trans ht, ?_, ?_, ?_⟩
      · change s1.core.confl_ref.toNat ∈ fullArenaClauseRefsCore s1.core at hr
        change s2.core.confl_ref.toNat ∈ fullArenaClauseRefsCore s2.core
        rw [hcr]; simpa [fullArenaClauseRefsCore, har, hal] using hr
      · rw [hcr, fullArenaClauseGarb_of_ar_eq har]; exact hg
      · intro l hl; rw [hcr, fullArenaClauseLits_of_ar_eq har] at hl; rw [hvals]; exact hfa l hl
  · simp only [hct]; split
    · rename_i heq; simp only [heq, ↓reduceIte] at h2; simpa [hlvl, hc0, hcl, htrl, hc1] using h2
    · rename_i hne; simp only [ite_eq_right hne] at h2
      intro l hl hlc; rw [hcr, fullArenaClauseLits_of_ar_eq har] at hl
      rw [htrl]; exact h2 l hl (by simpa [hlvl, hcl] using hlc)

theorem deduce_conflOk_of_subsume {F_cur : List (List Nat)} {cut' : Nat}
    {s1 s2 : FullState} (h1 : FullConflictOkCut F_cur cut' s1)
    (hct_eq : s2.core.confl_type = s1.core.confl_type)
    (hcr_eq : s2.core.confl_ref = s1.core.confl_ref)
    (hc0_eq : s2.core.confl_lit0 = s1.core.confl_lit0)
    (hc1_eq : s2.core.confl_lit1 = s1.core.confl_lit1)
    (hcv : s2.core.cur_vars = s1.core.cur_vars)
    (hvals : s2.core.vals = s1.core.vals)
    (hlvl : s2.core.lvl = s1.core.lvl)
    (htrl : s2.core.trl = s1.core.trl)
    (hcl : s2.core.cur_level = s1.core.cur_level)
    (hrefs : fullArenaClauseRefs s2 = fullArenaClauseRefs s1)
    (hkeep : ∀ r ∈ fullArenaClauseRefs s1, fullArenaClauseLits s2 r = fullArenaClauseLits s1 r ∧
      (s1.core.confl_type = 2#64 → r = s1.core.confl_ref.toNat →
        fullArenaClauseGarb s2 r = fullArenaClauseGarb s1 r)) :
    FullConflictOkCut F_cur cut' s2 := by
  rcases h1 with ⟨ha, hb⟩
  refine ⟨?_, ?_⟩
  · rcases ha with ⟨ht, h0, h1l, hf0, hf1, hen⟩ | ⟨ht, hr, hg, hfa⟩
    · left; refine ⟨hct_eq.trans ht, by simpa [hc0_eq, hcv] using h0,
        by simpa [hc1_eq, hcv] using h1l, by simpa [hvals, hc0_eq] using hf0,
        by simpa [hvals, hc1_eq] using hf1, by simpa [hc0_eq, hc1_eq] using hen⟩
    · right; refine ⟨hct_eq.trans ht, by rw [hcr_eq, hrefs]; exact hr, ?_, ?_⟩
      · rw [hcr_eq, (hkeep _ hr).2 ht rfl]; exact hg
      · intro l hl; rw [hcr_eq, (hkeep _ hr).1] at hl; rw [hvals]; exact hfa l hl
  · simp only [hct_eq]; split
    · rename_i heq; simp only [heq, ↓reduceIte] at hb
      simpa [hlvl, hc0_eq, hcl, htrl, hc1_eq] using hb
    · rename_i hne; simp only [ite_eq_right hne] at hb
      intro l hl hlc
      rcases ha with ⟨ht1, _⟩ | ⟨_, hr, _, _⟩
      · exact absurd ht1 hne
      · rw [hcr_eq, (hkeep _ hr).1] at hl
        rw [htrl]; exact hb l hl (by simpa [hlvl, hcl] using hlc)

theorem deduce_otfs_ret2_post {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut' : Nat} {s s_c : FullState} {R : Mem 64 → Prop} {Q : Post [i64]} {m_c : Mem 64}
    (hQ : ∀ r s' m',
      s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 2#64 ∨ r = 20#64) →
      s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      (r = 20#64 → F0.Unsat ∧ FullOtfsInvW c F0 F_cur s' ∧
        s'.core.cur_level ≤ s.core.cur_level ∧ s'.core.dense_mode = s.core.dense_mode) →
      (r = 0#64 → FullOtfsInvW c F0 F_cur s') →
      (r = 1#64 → FullOtfsInvW c F0 F_cur s' ∧ s'.core.cur_level = s.core.cur_level ∧
        1 ≤ s'.core.tmp_len ∧ s'.core.tmp_len ≤ s'.core.cur_vars ∧
        ((s'.core.tmp.take s'.core.tmp_len).map fun x => x.toNat / 2).Nodup ∧
        (∀ k < s'.core.tmp_len, let l := (s'.core.tmp[k]?.getD 0#32).toNat
          l < 2 * s'.core.cur_vars ∧ s'.core.vals[l]?.getD 0#8 = 0xFF#8) ∧
        (∀ k, 1 ≤ k → k < s'.core.tmp_len →
          let lv := (s'.core.lvl[(s'.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
          0 < lv ∧ lv < s'.core.cur_level) ∧
        (s'.core.lvl[(s'.core.tmp[0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat =
          s'.core.cur_level ∧
        (cnfOfClauses F_cur).EntailsClause
          (cnfClause ((s'.core.tmp.take s'.core.tmp_len).map BitVec.toNat))) →
      (r = 2#64 → ∃ cut' ≤ s'.core.trail_end,
        FullCutInvW c F0 F_cur cut' s' ∧ s'.core.cur_level = s.core.cur_level ∧
        FullConflictOkCut F_cur cut' s') →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m')
    (hlen_c : s_c.LengthsOk c) (hcut_le : cut' ≤ s_c.core.trail_end)
    (hcutw : FullCutInvW c F0 F_cur cut' s_c) (hconfl_c : FullConflictOkCut F_cur cut' s_c)
    (hcv : s_c.core.cur_vars = s.core.cur_vars) (hcl : s_c.core.cur_level = s.core.cur_level)
    (hfuel : s_c.core.fuel = s.core.fuel) (hws2 : s_c.scratch.work_stk2 = s.scratch.work_stk2)
    (hm_c : (FullMem c s_c ⋆ R) m_c) : Q (2#64, ()) m_c :=
  hQ 2#64 s_c m_c hlen_c (Or.inr (Or.inr (Or.inl rfl))) hcv hfuel hws2
    (fun h => by cases h) (fun h => by cases h) (fun h => by cases h)
    (fun _ => ⟨cut', hcut_le, hcutw, hcl, hconfl_c⟩) hm_c

theorem deduce_large_conflOk_of {F_cur : List (List Nat)} {cut' : Nat}
    {s : FullState} {rsn : BitVec 32}
    (href : rsn.toNat ∈ fullArenaClauseRefs s)
    (hng : fullArenaClauseGarb s rsn.toNat = false)
    (hlits : ∀ l ∈ fullArenaClauseLits s rsn.toNat, s.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
      ((s.core.lvl[l / 2]?.getD 0#32).toNat = s.core.cur_level →
        ∃ m < cut', (s.core.trl[m]?.getD 0#32).toNat = l ^^^ 1)) :
    FullConflictOkCut F_cur cut'
      { s with core := { s.core with confl_type := 2#64, confl_ref := rsn.setWidth 64 } } := by
  have hcr : (rsn.setWidth 64).toNat = rsn.toNat := zext_toNat rsn (by decide)
  refine ⟨Or.inr ⟨rfl, by simpa [fullArenaClauseRefs, fullArenaClauseRefsCore, hcr] using href,
    by simpa [fullArenaClauseGarb, fullArenaClauseGarbCore, fullArenaHdrCore, hcr] using hng,
    fun l hl => (hlits l (by
      simpa [fullArenaClauseLits, fullArenaClauseLitsCore, fullArenaClauseSizeCore, hcr]
        using hl)).1⟩, ?_⟩
  simp only [show (2#64 : BitVec 64) ≠ 1#64 from by decide, ↓reduceIte]
  intro l hl hcl
  exact (hlits l (by
    simpa [fullArenaClauseLits, fullArenaClauseLitsCore, fullArenaClauseSizeCore, hcr]
      using hl)).2 hcl

theorem deduce_clear_unsat_goal_wp {Γ : Env}
    (hClear : ∀ a m Q X, fullClearAnaSpec a m Q X → Γ "full_clear_ana" [i64] [] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {cut' : Nat}
    {s s1 : FullState} {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost} {m1 : Mem 64}
    {seed_ok : Bool}
    (hQ : ∀ r s' m',
      s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 2#64 ∨ r = 20#64) →
      s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      (r = 20#64 → F0.Unsat ∧ FullOtfsInvW c F0 F_cur s' ∧
        s'.core.cur_level ≤ s.core.cur_level ∧ s'.core.dense_mode = s.core.dense_mode) →
      (r = 0#64 → FullOtfsInvW c F0 F_cur s') →
      (r = 1#64 → FullOtfsInvW c F0 F_cur s' ∧ s'.core.cur_level = s.core.cur_level ∧
        1 ≤ s'.core.tmp_len ∧ s'.core.tmp_len ≤ s'.core.cur_vars ∧
        ((s'.core.tmp.take s'.core.tmp_len).map fun x => x.toNat / 2).Nodup ∧
        (∀ k < s'.core.tmp_len, let l := (s'.core.tmp[k]?.getD 0#32).toNat
          l < 2 * s'.core.cur_vars ∧ s'.core.vals[l]?.getD 0#8 = 0xFF#8) ∧
        (∀ k, 1 ≤ k → k < s'.core.tmp_len →
          let lv := (s'.core.lvl[(s'.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
          0 < lv ∧ lv < s'.core.cur_level) ∧
        (s'.core.lvl[(s'.core.tmp[0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat =
          s'.core.cur_level ∧
        (cnfOfClauses F_cur).EntailsClause
          (cnfClause ((s'.core.tmp.take s'.core.tmp_len).map BitVec.toNat))) →
      (r = 2#64 → ∃ cut' ≤ s'.core.trail_end,
        FullCutInvW c F0 F_cur cut' s' ∧ s'.core.cur_level = s.core.cur_level ∧
        FullConflictOkCut F_cur cut' s') →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m')
    (hlen1 : s1.LengthsOk c) (hw1 : FullWitnessCutInv c F0 F_cur cut' s1.core)
    (hcov1 : FullAnaMarksCov c s1) (hext0 : FullExtScratchOk c s) (hext1 : FullExtScratchPres s s1)
    (hws2 : s1.scratch.work_stk2 = s.scratch.work_stk2) (hnd1 : FullArenaVarsNodup s1)
    (hrefs1 : fullArenaClauseRefs s1 = fullArenaClauseRefs s)
    (hstat1 : FullDeduceStaticEq s.core s1.core) (hdm0 : s.core.dense_mode = 0#64)
    (hm0_lm : FullLitMarksClear c s)
    (hunsat : seed_ok = true → s1.core.tmp_len = 1 → F0.Unsat)
    (hm1 : (FullMem c s1 ⋆ R) m1) :
    wp Γ Q X (.call (rs := [i64]) (as := [i64]) (bs := []) "full_clear_ana" (Arg.var c.hdr, ())
      fun _ => .jnz (Arg.var seed_ok)
        (.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 192, ())) fun p =>
          .load i64 (Arg.var p.fst) fun ld =>
            .let_ (Op.mk (.cmp .eq i64 .bool rfl) (Arg.var ld, Arg.imm 1#64, ())) fun p =>
              .jnz (Arg.var p.fst) (.ret (Arg.imm 20#64, ())) (.ret (Arg.imm 0#64, ())))
        (.ret (Arg.imm 0#64, ()))) m1 := by
  refine deduce_clear_unsat_ret_wp hClear hlen1 hw1 hcov1 hext0 hext1 hnd1 hrefs1 hstat1 hdm0
    hm0_lm hm1 fun mrk' m_c hlen_c hotfs_c hcv_c hfuel_c hcl_c hdm_c hm_c => ?_
  have hmaxv := c.hmaxv; have hcv_le := hlen1.core_ok.cur_vars_le; unfold dimacsBound at hmaxv
  have htl_lt : s1.core.tmp_len < 2 ^ 64 := by have := hlen1.core_ok.tmp_len_le; omega
  refine wp_jnz_of (fun hso => ?_) (fun _ => ?_)
  · simp only [Arg.val_var] at hso
    fa_fast_steps
    · have htl1 : s1.core.tmp_len = 1 := by
        have heq : BitVec.ofNat 64 s1.core.tmp_len = 1#64 := by assumption
        have := congrArg BitVec.toNat heq; rw [bv64_ofNat_toNat htl_lt] at this
        simpa using this
      exact hQ 20#64 _ m_c hlen_c (Or.inr (Or.inr (Or.inr rfl))) hcv_c hfuel_c hws2
        (fun _ => ⟨hunsat hso htl1, hotfs_c, le_of_eq hcl_c, hdm_c.trans hdm0.symm⟩)
        (fun h => by cases h) (fun h => by cases h) (fun h => by cases h) hm_c
    · exact hQ 0#64 _ m_c hlen_c (Or.inl rfl) hcv_c hfuel_c hws2
        (fun h => by cases h) (fun _ => hotfs_c) (fun h => by cases h) (fun h => by cases h) hm_c
  · fa_fast_steps
    exact hQ 0#64 _ m_c hlen_c (Or.inl rfl) hcv_c hfuel_c hws2
      (fun h => by cases h) (fun _ => hotfs_c) (fun h => by cases h) (fun h => by cases h) hm_c

theorem deduce_uip_exit_body_wp {Γ : Env}
    (hBump : ∀ a m Q X, fullBumpAnalyzedSpec a m Q X →
      Γ "full_bump_analyzed" [i64] [] a m Q X)
    (hClear : ∀ a m Q X, fullClearAnaSpec a m Q X → Γ "full_clear_ana" [i64] [] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {cut_b idx_u : Nat}
    {s sb : FullState} {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost} {mb : Mem 64}
    {p_bv : BitVec 32}
    (hQ : ∀ r s' m',
      s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 2#64 ∨ r = 20#64) →
      s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      (r = 20#64 → F0.Unsat ∧ FullOtfsInvW c F0 F_cur s' ∧
        s'.core.cur_level ≤ s.core.cur_level ∧ s'.core.dense_mode = s.core.dense_mode) →
      (r = 0#64 → FullOtfsInvW c F0 F_cur s') →
      (r = 1#64 → FullOtfsInvW c F0 F_cur s' ∧ s'.core.cur_level = s.core.cur_level ∧
        1 ≤ s'.core.tmp_len ∧ s'.core.tmp_len ≤ s'.core.cur_vars ∧
        ((s'.core.tmp.take s'.core.tmp_len).map fun x => x.toNat / 2).Nodup ∧
        (∀ k < s'.core.tmp_len, let l := (s'.core.tmp[k]?.getD 0#32).toNat
          l < 2 * s'.core.cur_vars ∧ s'.core.vals[l]?.getD 0#8 = 0xFF#8) ∧
        (∀ k, 1 ≤ k → k < s'.core.tmp_len →
          let lv := (s'.core.lvl[(s'.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
          0 < lv ∧ lv < s'.core.cur_level) ∧
        (s'.core.lvl[(s'.core.tmp[0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat =
          s'.core.cur_level ∧
        (cnfOfClauses F_cur).EntailsClause
          (cnfClause ((s'.core.tmp.take s'.core.tmp_len).map BitVec.toNat))) →
      (r = 2#64 → ∃ cut' ≤ s'.core.trail_end,
        FullCutInvW c F0 F_cur cut' s' ∧ s'.core.cur_level = s.core.cur_level ∧
        FullConflictOkCut F_cur cut' s') →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m')
    (hext0 : FullExtScratchOk c s) (hdm0 : s.core.dense_mode = 0#64)
    (hm0_lm : FullLitMarksClear c s)
    (hlen_b : sb.LengthsOk c) (hw_b : FullWitnessCutInv c F0 F_cur cut_b sb.core)
    (hcov_b : FullAnaMarksCov c sb) (hext_b : FullExtScratchPres s sb)
    (hws2_b : sb.scratch.work_stk2 = s.scratch.work_stk2) (hnd_b : FullArenaVarsNodup sb)
    (hrefs_b : fullArenaClauseRefs sb = fullArenaClauseRefs s)
    (hstat_b : FullDeduceStaticEq s.core sb.core)
    (htl1 : 1 ≤ sb.core.tmp_len) (htl_cv : sb.core.tmp_len ≤ sb.core.cur_vars)
    (hlow_b : FullLowerInv c sb.core sb.core.tmp sb.core.mrk sb.core.tmp_len)
    (hiu_te : idx_u < sb.core.trail_end)
    (hp_get : (sb.core.trl[idx_u]?.getD 0#32).toNat = p_bv.toNat)
    (hpl_cl : (sb.core.lvl[p_bv.toNat / 2]?.getD 0#32).toNat = sb.core.cur_level)
    (hent_b : (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((p_bv ^^^ 1#32).toNat :: fullLowerLits sb.core.tmp sb.core.tmp_len)))
    (hmb : (FullMem c sb ⋆ R) mb) :
    wp Γ Q X (.let_ (Op.mk (.cmp .eq i32 .bool rfl)
        (Arg.var (p_bv ^^^ 1#32), Arg.imm 0xFFFFFFFF#32, ())) fun p19 =>
      .jnz (Arg.var p19.fst)
        (.call (rs := [i64]) (as := [i64]) (bs := []) "full_clear_ana" (Arg.var c.hdr, ())
          fun _ => .ret (Arg.imm 0#64, ()))
        (.let_ (Op.mk (.sext 32 64) (Arg.imm 0#32, ())) fun p20 =>
          .let_ (Op.mk (.mul i64) (Arg.var p20.fst, Arg.imm 4#64, ())) fun p21 =>
            .let_ (Op.mk (.add i64) (Arg.var c.pTmp, Arg.var p21.fst, ())) fun p22 =>
              .store (Arg.var (t := i32) (p_bv ^^^ 1#32)) (Arg.var p22.fst)
                (.call (rs := [i64]) (as := [i64]) (bs := []) "full_bump_analyzed"
                  (Arg.var c.hdr, ()) fun _ =>
                  .call (rs := [i64]) (as := [i64]) (bs := []) "full_clear_ana"
                    (Arg.var c.hdr, ()) fun _ => .ret (Arg.imm 1#64, ())))) mb := by
  let uip := p_bv ^^^ 1#32
  have hmaxv := c.hmaxv; have hcv_le := hlen_b.core_ok.cur_vars_le; unfold dimacsBound at hmaxv
  have hp_lt : p_bv.toNat < 2 * sb.core.cur_vars := hp_get ▸ hw_b.trail_lits_lt idx_u hiu_te
  have huip_nat : uip.toNat = p_bv.toNat ^^^ 1 := bv32_xor_1 p_bv
  have huip_lt : uip.toNat < 2 * sb.core.cur_vars := huip_nat ▸ litNeg_lt_two_mul hp_lt
  have huip_ne : uip ≠ 0xFFFFFFFF#32 := bv32_lit_neq_ff (by omega)
  have htb_len : sb.core.tmp.length = c.max_vars := hlen_b.core_ok.tmp_len_arr
  have h0_tb : 0 < sb.core.tmp.length := by have := hw_b.cur_level_le; omega
  let tmp0 := sb.core.tmp.set 0 uip
  have htmp0_len : tmp0.length = c.max_vars := by rw [List.length_set, htb_len]
  let s0 : FullState := { sb with core := { sb.core with tmp := tmp0 } }
  have htmp0_gt0 : ∀ j, 1 ≤ j → tmp0[j]? = sb.core.tmp[j]? := fun _ _ =>
    List.getElem?_set_ne (by omega)
  have htmp0_0 : tmp0[0]? = some uip := List.getElem?_set_self h0_tb
  have hlow0 : FullLowerInv c s0.core tmp0 sb.core.mrk sb.core.tmp_len :=
    ⟨fun j h1 h2 => htmp0_gt0 j h1 ▸ hlow_b.1 j h1 h2,
     fun j1 j2 h1 h12 h2 => by
       have := hlow_b.2 j1 j2 h1 h12 h2
       rwa [htmp0_gt0 j1 h1, htmp0_gt0 j2 (by omega)]⟩
  have hlowLits0 : fullLowerLits tmp0 sb.core.tmp_len =
      fullLowerLits sb.core.tmp sb.core.tmp_len := by
    change fullLowerLits (sb.core.tmp.set 0 uip) sb.core.tmp_len =
      fullLowerLits sb.core.tmp sb.core.tmp_len
    unfold fullLowerLits; cases sb.core.tmp <;> rfl
  have hs0_len : s0.LengthsOk c :=
    ⟨{ hlen_b.core_ok with tmp_len_arr := by dsimp [s0, tmp0]; simp [htb_len] }, hlen_b.scratch_ok⟩
  have hw0 : FullWitnessCutInv c F0 F_cur cut_b s0.core :=
    deduce_same_core_cut hw_b sb.core.mrk tmp0 sb.core.tmp_cnt sb.core.tmp_len sb.core.min_clr_len
  have hcov0 : FullAnaMarksCov c s0 := hcov_b
  have hnd0 : FullArenaVarsNodup s0 := hnd_b
  have hrefs0 : fullArenaClauseRefs s0 = fullArenaClauseRefs s := hrefs_b
  have hstat0 : FullDeduceStaticEq s.core s0.core :=
    ⟨hstat_b.1, hstat_b.2, hstat_b.3, hstat_b.4, hstat_b.5, hstat_b.6, hstat_b.7, hstat_b.8,
     hstat_b.9, hstat_b.10⟩
  have huip_fals : sb.core.vals[uip.toNat]?.getD 0#8 = 0xFF#8 :=
    (hw_b.vals_false_iff uip.toNat huip_lt).mpr ⟨idx_u, hiu_te, by
      rw [hp_get, huip_nat]; exact (litNeg_litNeg _).symm⟩
  have huip_cl : (sb.core.lvl[uip.toNat / 2]?.getD 0#32).toNat = sb.core.cur_level := by
    rwa [huip_nat, litNeg_div2]
  fa_fast_steps
  · exact absurd hc huip_ne
  · refine wp_store_sep (Deduce1UipTactics.d1_store_full_tmp0_mul uip h0_tb hmb)
      (fun m_st hm_st => ?_)
    fa_fast_steps
    refine deduce_bump_clear_ret_wp hBump hClear 1#64 hs0_len hw0 hcov0 hext0 hext_b hws2_b
      hnd0 hrefs0 hstat0 hdm0 hm0_lm hm_st
      fun mrk_c sc_b m_c hlen_c hotfs_c _ _ hcv_c hcl_c hfuel_c hws2_c hm_c => ?_
    let s_c : FullState :=
      { s0 with core := { s0.core with mrk := mrk_c, min_clr_len := 0 }, scratch := sc_b }
    have hsc_tl_len : s_c.core.tmp.length = c.max_vars := htmp0_len
    have hnd_uip := fullTmpTake_uip_nodup htl1 (by omega)
      htmp0_0 hlow0 huip_cl
    refine hQ 1#64 s_c m_c hlen_c (Or.inr (Or.inl rfl)) hcv_c hfuel_c hws2_c
      (fun h => by cases h) (fun h => by cases h) (fun _ => ?_) (fun h => by cases h) hm_c
    refine ⟨hotfs_c, hcl_c, htl1, htl_cv, hnd_uip, fun k hk => ?_, fun k hk1 hk2 => ?_, ?_, ?_⟩
    · cases k with
      | zero => rw [htmp0_0, Option.getD_some]; exact ⟨huip_lt, huip_fals⟩
      | succ k' => let hlk := hlow0.1 (k' + 1) (by omega) hk; exact ⟨hlk.1, hlk.2.1⟩
    · let hlk := hlow0.1 k hk1 hk2; exact ⟨hlk.2.2.1, hlk.2.2.2.1⟩
    · rw [htmp0_0, Option.getD_some]; exact huip_cl
    · rw [fullLowerLits_tmp_take htl1 (by omega) htmp0_0, hlowLits0]
      exact hent_b


end Deduce1UipCore

end LeanQbe.T.Examples.Kissat.Full
