module

public import LeanQbe.T.Examples.Kissat.SolverAnalyzeLemmas1
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat C0 1UIP Conflict Analysis `Func.wp` Proof (`X1` Stage B2, Part 2)

Builds on `SolverAnalyzeLemmas1` (`kissat_analyze_clause`, `kissat_clear_marks`, `kissat_decide`)
to specify and verify `kissat_analyze` (`kissatAnalyzeSpec`, `kissat_analyze_wp`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open Kraken.Bedrock2.Test

/-! ## 1. Private counting, bit-vector, and 1UIP semantic-resolvent helpers -/

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
    (hxs : xs.Nodup) (hys : ys.Nodup)
    (hmap : ∀ x ∈ xs, f x ∈ ys)
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
  rw [List.range_succ, List.filter_append]
  cases hp : p n <;> simp [hp]

/-- Lower-level literals accumulated in `tmp[1 ..< tl)`. -/
private def lowerLits (tmp : List (BitVec 32)) (tl : Nat) : List Nat :=
  ((tmp.drop 1).take (tl - 1)).map BitVec.toNat

/-- Marked current-level trail indices strictly below `idx`. -/
private def curTrailIdxs (s : ArenaState) (mrk : List (BitVec 8)) (idx : Nat) : List Nat :=
  (List.range idx).filter fun j =>
    let v := (s.trl[j]?.getD 0#32).toNat / 2
    decide (mrk[v]?.getD 0#8 ≠ 0#8) &&
      decide ((s.lvl[v]?.getD 0#32).toNat = s.cur_level)

/-- Negated marked current-level trail literals strictly below `idx`. -/
private def curLits (s : ArenaState) (mrk : List (BitVec 8)) (idx : Nat) : List Nat :=
  (curTrailIdxs s mrk idx).map fun j => (s.trl[j]?.getD 0#32).toNat ^^^ 1

/-- Active 1UIP resolvent clause (`lowerLits ++ curLits`). -/
private def activeResolvent (s : ArenaState) (tmp : List (BitVec 32)) (mrk : List (BitVec 8))
    (tl idx : Nat) : List Nat :=
  lowerLits tmp tl ++ curLits s mrk idx

/-- Well-formedness of lower-level literals in `tmp[1 ..< tl)`. -/
private def LowerInv (c : ArenaCfg) (s : ArenaState) (tmp : List (BitVec 32))
    (mrk : List (BitVec 8)) (tl : Nat) : Prop :=
  ∀ j, 1 ≤ j → j < tl →
    let l := (tmp[j]?.getD 0#32).toNat
    l < 2 * c.mv ∧
    s.vals[l]?.getD 0#8 = 0xFF#8 ∧
    0 < (s.lvl[l / 2]?.getD 0#32).toNat ∧
    (s.lvl[l / 2]?.getD 0#32).toNat < s.cur_level ∧
    mrk[l / 2]?.getD 0#8 ≠ 0#8

/-- Coverage of all nonzero entries in `mrk` by `tmp[1 ..< tl)` or `cur_level` trail entries. -/
private def MarksCov (c : ArenaCfg) (s : ArenaState) (tmp : List (BitVec 32))
    (mrk : List (BitVec 8)) (tl : Nat) : Prop :=
  ∀ v < c.mv, mrk[v]?.getD 0#8 ≠ 0#8 →
    (∃ j, 1 ≤ j ∧ j < tl ∧ (tmp[j]?.getD 0#32).toNat / 2 = v) ∨
    (∃ j < s.trail_end, (s.trl[j]?.getD 0#32).toNat / 2 = v ∧
      (s.lvl[v]?.getD 0#32).toNat = s.cur_level)

private theorem mem_lowerLits_iff {tmp : List (BitVec 32)} {tl l : Nat}
    (h1 : 1 ≤ tl) (hle : tl ≤ tmp.length) :
    l ∈ lowerLits tmp tl ↔ ∃ j, 1 ≤ j ∧ j < tl ∧ (tmp[j]?.getD 0#32).toNat = l := by
  unfold lowerLits
  rw [List.mem_map]
  constructor
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

private theorem curTrailIdxs_succ_true {s : ArenaState} {mrk : List (BitVec 8)} {idx : Nat}
    (hm : mrk[(s.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8)
    (hl : (s.lvl[(s.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = s.cur_level) :
    curTrailIdxs s mrk (idx + 1) = curTrailIdxs s mrk idx ++ [idx] := by
  unfold curTrailIdxs; rw [range_succ_filter]; simp [hm, hl]

private theorem curTrailIdxs_succ_false {s : ArenaState} {mrk : List (BitVec 8)} {idx : Nat}
    (h : ¬ (mrk[(s.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8 ∧
      (s.lvl[(s.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = s.cur_level)) :
    curTrailIdxs s mrk (idx + 1) = curTrailIdxs s mrk idx := by
  unfold curTrailIdxs; rw [range_succ_filter]
  have hf : (decide (mrk[(s.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8) &&
      decide ((s.lvl[(s.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = s.cur_level)) =
      false := by
    by_cases h1 : mrk[(s.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8
    · have h2 : (s.lvl[(s.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≠ s.cur_level :=
        fun he => h ⟨h1, he⟩
      simp [h1, h2]
    · simp [h1]
  rw [hf]; simp

private theorem curLits_succ_true {s : ArenaState} {mrk : List (BitVec 8)} {idx : Nat}
    (hm : mrk[(s.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8)
    (hl : (s.lvl[(s.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = s.cur_level) :
    curLits s mrk (idx + 1) = curLits s mrk idx ++ [(s.trl[idx]?.getD 0#32).toNat ^^^ 1] := by
  unfold curLits; rw [curTrailIdxs_succ_true hm hl, List.map_append]; rfl

private theorem curLits_succ_false {s : ArenaState} {mrk : List (BitVec 8)} {idx : Nat}
    (h : ¬ (mrk[(s.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8 ∧
      (s.lvl[(s.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = s.cur_level)) :
    curLits s mrk (idx + 1) = curLits s mrk idx := by
  unfold curLits; rw [curTrailIdxs_succ_false h]

private theorem same_core_lengths {c : ArenaCfg} {s : ArenaState}
    (hlen : s.LengthsOk c) {mrk' : List (BitVec 8)} {tmp' : List (BitVec 32)} {tc' tl' : Nat}
    (hm : mrk'.length = c.mv) (ht : tmp'.length = c.mv) (htc : tc' < 2 ^ 64) (htl : tl' < 2 ^ 64) :
    ({ s with mrk := mrk', tmp := tmp', tmp_cnt := tc', tmp_len := tl' } : ArenaState).LengthsOk
      c :=
  ⟨hlen.vals_len, hm, hlen.lvl_len, hlen.rsns_len, hlen.trl_len, ht, hlen.wh_len, hlen.cls_len,
    hlen.wn_len, hlen.lpool_len, hlen.lit_len_le, hlen.num_clauses_le, hlen.trail_end_le,
    hlen.propagated_le, hlen.cur_level_lt, htc, htl⟩

private theorem same_core_solverCoreInv {c : ArenaCfg} {F0 : CNF Nat} {s : ArenaState}
    (hcore : SolverCoreInv c F0 s) {mrk' : List (BitVec 8)} {tmp' : List (BitVec 32)}
    {tc' tl' : Nat} (hm : mrk'.length = c.mv) (ht : tmp'.length = c.mv)
    (htc : tc' < 2 ^ 64) (htl : tl' < 2 ^ 64) :
    SolverCoreInv c F0 { s with mrk := mrk', tmp := tmp', tmp_cnt := tc', tmp_len := tl' } :=
  ⟨same_core_lengths hcore.lengths hm ht htc htl,
    ⟨hcore.clauses.bounds, hcore.clauses.disjoint, hcore.clauses.lits_lt, hcore.clauses.entails⟩,
    hcore.cur_level_le, hcore.trail_lits_lt, hcore.trail_vars_nodup, hcore.vals_domain,
    hcore.vals_true_iff, hcore.vals_false_iff, hcore.lvl_le, hcore.trail_mono,
    hcore.levels_inhabited, hcore.level0_sound, hcore.reason_inv⟩

/-- Bridge from `kissatAnalyzeClauseSpec` (`ok = true`) to the 1UIP analysis invariant. -/
private theorem analyzeClause_preserves {c : ArenaCfg} {F0 : CNF Nat} {s : ArenaState}
    (hcore : SolverCoreInv c F0 s)
    {mrk mrk' : List (BitVec 8)} {tmp tmp' : List (BitVec 32)}
    {tc tc' tl tl' idx cid skip_var : Nat}
    (hidx : idx ≤ s.trail_end) (h1 : 1 ≤ tl) (htl_le : tl ≤ tl') (htl'_mv : tl' ≤ c.mv)
    (hm_len : mrk.length = c.mv) (ht_len : tmp.length = c.mv)
    (hm'_len : mrk'.length = c.mv) (ht'_len : tmp'.length = c.mv)
    (htc_eq : tc = (curTrailIdxs s mrk idx).length) (htc_le : tc ≤ tc')
    (hlow : LowerInv c s tmp mrk tl) (hcov : MarksCov c s tmp mrk tl)
    (hcid : cid < s.num_clauses)
    (hclause : ∀ q ∈ clauseLits s cid,
      q / 2 = skip_var ∨ ∃ k < idx, (s.trl[k]?.getD 0#32).toNat = q ^^^ 1)
    (hmpres : ∀ v < c.mv, mrk[v]?.getD 0#8 ≠ 0#8 → mrk'[v]?.getD 0#8 = mrk[v]?.getD 0#8)
    (htpres : ∀ k < tl, tmp'[k]? = tmp[k]?)
    (hnewm : ∀ v < c.mv, mrk[v]?.getD 0#8 = 0#8 → mrk'[v]?.getD 0#8 ≠ 0#8 →
      ∃ l ∈ clauseLits s cid,
        l / 2 = v ∧ v ≠ skip_var ∧
        0 < (s.lvl[v]?.getD 0#32).toNat ∧ (s.lvl[v]?.getD 0#32).toNat ≤ s.cur_level)
    (hnewt : ∀ j, tl ≤ j → j < tl' →
      let l := (tmp'[j]?.getD 0#32).toNat
      l ∈ clauseLits s cid ∧ l < 2 * c.mv ∧ l / 2 ≠ skip_var ∧
      0 < (s.lvl[l / 2]?.getD 0#32).toNat ∧ (s.lvl[l / 2]?.getD 0#32).toNat < s.cur_level ∧
      mrk'[l / 2]?.getD 0#8 ≠ 0#8)
    (hcnt : tc' - tc =
      ((List.range c.mv).filter fun v =>
        decide (mrk[v]?.getD 0#8 = 0#8) &&
        decide (mrk'[v]?.getD 0#8 ≠ 0#8) &&
        decide ((s.lvl[v]?.getD 0#32).toNat = s.cur_level)).length)
    (hall : ∀ l ∈ clauseLits s cid,
      l / 2 < c.mv ∧
      (l / 2 ≠ skip_var →
        (0 < (s.lvl[l / 2]?.getD 0#32).toNat → mrk'[l / 2]?.getD 0#8 ≠ 0#8) ∧
        (mrk[l / 2]?.getD 0#8 = 0#8 →
          (s.lvl[l / 2]?.getD 0#32).toNat ≤ s.cur_level ∧
          (0 < (s.lvl[l / 2]?.getD 0#32).toNat →
            (s.lvl[l / 2]?.getD 0#32).toNat < s.cur_level →
            ∃ j, tl ≤ j ∧ j < tl' ∧ (tmp'[j]?.getD 0#32).toNat / 2 = l / 2)))) :
    tc' = (curTrailIdxs s mrk' idx).length ∧
    LowerInv c s tmp' mrk' tl' ∧
    MarksCov c s tmp' mrk' tl' ∧
    (∀ l ∈ lowerLits tmp tl, l ∈ lowerLits tmp' tl') ∧
    (∀ l ∈ curLits s mrk idx, l ∈ curLits s mrk' idx) ∧
    (∀ q ∈ clauseLits s cid,
      q / 2 = skip_var ∨ q ∈ activeResolvent s tmp' mrk' tl' idx ∨
        F0.EntailsClause (cnfClause [litNeg q])) := by
  have hlow' : LowerInv c s tmp' mrk' tl' := by
    intro j hj1 hjlt
    by_cases hjold : j < tl
    · rw [htpres j hjold]
      obtain ⟨h1', h2', h3', h4', h5'⟩ := hlow j hj1 hjold
      exact ⟨h1', h2', h3', h4', by rw [hmpres _ (by omega) h5']; exact h5'⟩
    · obtain ⟨hmem, hlt, hne, hpos, hcl, hmk⟩ := hnewt j (by omega) hjlt
      rcases hclause _ hmem with heq | ⟨k, hk, hkeq⟩
      · exact absurd heq hne
      · have hfals : s.vals[(tmp'[j]?.getD 0#32).toNat]?.getD 0#8 = 0xFF#8 :=
          (hcore.vals_false_iff _ hlt).mpr ⟨k, by omega, hkeq⟩
        exact ⟨hlt, hfals, hpos, hcl, hmk⟩
  have hcov' : MarksCov c s tmp' mrk' tl' := by
    intro v hv hnz'
    by_cases hv0 : mrk[v]?.getD 0#8 = 0#8
    · obtain ⟨l, hlmem, rfl, hne, hpos, hle⟩ := hnewm v hv hv0 hnz'
      by_cases hcl : (s.lvl[l / 2]?.getD 0#32).toNat = s.cur_level
      · rcases hclause l hlmem with heq | ⟨k, hk, hkeq⟩
        · exact absurd heq hne
        · exact Or.inr ⟨k, by omega, by rw [hkeq]; exact litVar_litNeg l, hcl⟩
      · obtain ⟨_, hrest⟩ := hall l hlmem
        obtain ⟨j, hj1, hj2, hjeq⟩ := (hrest hne).2 hv0 |>.2 hpos (by omega)
        exact Or.inl ⟨j, by omega, hj2, hjeq⟩
    · rcases hcov v hv hv0 with ⟨j, hj1, hj2, hjeq⟩ | htrl
      · exact Or.inl ⟨j, hj1, by omega, by rw [htpres j hj2]; exact hjeq⟩
      · exact Or.inr htrl
  have htc' : tc' = (curTrailIdxs s mrk' idx).length := by
    let pOld : Nat → Bool := fun j =>
      let v := (s.trl[j]?.getD 0#32).toNat / 2
      decide (mrk[v]?.getD 0#8 ≠ 0#8) && decide ((s.lvl[v]?.getD 0#32).toNat = s.cur_level)
    let pNew : Nat → Bool := fun j =>
      let v := (s.trl[j]?.getD 0#32).toNat / 2
      decide (mrk[v]?.getD 0#8 = 0#8) && decide (mrk'[v]?.getD 0#8 ≠ 0#8) &&
        decide ((s.lvl[v]?.getD 0#32).toNat = s.cur_level)
    have hsplit : curTrailIdxs s mrk' idx =
        (List.range idx).filter (fun j => pOld j || pNew j) := by
      unfold curTrailIdxs; apply List.filter_congr; intro j hj
      have hjlt : j < idx := List.mem_range.mp hj
      have hvlt : (s.trl[j]?.getD 0#32).toNat / 2 < c.mv := by
        have := hcore.trail_lits_lt j (by omega); omega
      dsimp only [pOld, pNew]
      by_cases h0 : mrk[(s.trl[j]?.getD 0#32).toNat / 2]?.getD 0#8 = 0#8
      · simp [h0]
      · rw [hmpres _ hvlt h0]; simp [h0]
    have hadd : (curTrailIdxs s mrk' idx).length =
        ((List.range idx).filter pOld).length + ((List.range idx).filter pNew).length := by
      rw [hsplit]
      exact filter_length_add_of_disj pOld pNew (List.range idx) fun j _ ⟨h1, h2⟩ => by
        simp [pOld, pNew] at h1 h2; exact h1.1 h2.1.1
    have hbij : ((List.range idx).filter pNew).length =
        ((List.range c.mv).filter fun v =>
          decide (mrk[v]?.getD 0#8 = 0#8) &&
          decide (mrk'[v]?.getD 0#8 ≠ 0#8) &&
          decide ((s.lvl[v]?.getD 0#32).toNat = s.cur_level)).length := by
      refine nodup_length_eq_of_bij (fun j => (s.trl[j]?.getD 0#32).toNat / 2)
        (List.Nodup.sublist List.filter_sublist List.nodup_range)
        (List.Nodup.sublist List.filter_sublist List.nodup_range)
        (fun j hj => ?_) (fun j1 hj1 j2 hj2 heq => ?_) (fun v hv => ?_)
      · rw [List.mem_filter, List.mem_range] at hj ⊢
        have hvlt : (s.trl[j]?.getD 0#32).toNat / 2 < c.mv := by
          have := hcore.trail_lits_lt j (by omega); omega
        exact ⟨hvlt, hj.2⟩
      · rw [List.mem_filter, List.mem_range] at hj1 hj2
        exact hcore.trail_vars_nodup j1 j2 (by omega) (by omega) heq
      · rw [List.mem_filter, List.mem_range] at hv
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
        obtain ⟨hvlt, ⟨hm0, hmnz'⟩, hcl⟩ := hv
        obtain ⟨l, hlmem, rfl, hne, _, _⟩ := hnewm v hvlt hm0 hmnz'
        rcases hclause l hlmem with heq | ⟨k, hk, hkeq⟩
        · exact absurd heq hne
        · have hkvar : (s.trl[k]?.getD 0#32).toNat / 2 = l / 2 := by
            rw [hkeq]; exact litVar_litNeg l
          refine ⟨k, List.mem_filter.mpr ⟨List.mem_range.mpr hk, ?_⟩, hkvar⟩
          simp [pNew, hkvar, hm0, hmnz', hcl]
    have hold_eq : ((List.range idx).filter pOld).length = tc := htc_eq.symm
    omega
  have hlow_sub : ∀ l ∈ lowerLits tmp tl, l ∈ lowerLits tmp' tl' := by
    intro l hl
    rw [mem_lowerLits_iff h1 (by omega)] at hl
    obtain ⟨j, hj1, hj2, hget⟩ := hl
    rw [mem_lowerLits_iff (by omega) (by omega)]
    exact ⟨j, hj1, by omega, by rw [htpres j hj2]; exact hget⟩
  have hcur_sub : ∀ l ∈ curLits s mrk idx, l ∈ curLits s mrk' idx := by
    intro l hl
    unfold curLits curTrailIdxs at hl ⊢
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hl
    rw [List.mem_filter, List.mem_range] at hj
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hj
    have hvlt : (s.trl[j]?.getD 0#32).toNat / 2 < c.mv := by
      have := hcore.trail_lits_lt j (by omega); omega
    refine List.mem_map.mpr ⟨j, List.mem_filter.mpr ⟨List.mem_range.mpr hj.1, ?_⟩, rfl⟩
    simp [hmpres _ hvlt hj.2.1, hj.2.1, hj.2.2]
  have hq_res : ∀ q ∈ clauseLits s cid,
      q / 2 = skip_var ∨ q ∈ activeResolvent s tmp' mrk' tl' idx ∨
        F0.EntailsClause (cnfClause [litNeg q]) := by
    intro q hq
    rcases hclause q hq with heq | ⟨k, hk, hkeq⟩
    · exact Or.inl heq
    · by_cases hskip : q / 2 = skip_var
      · exact Or.inl hskip
      · right
        have hqlt : q < 2 * c.mv := hcore.clauses.lits_lt cid hcid q hq
        have hq_fals : s.vals[q]?.getD 0#8 = 0xFF#8 :=
          (hcore.vals_false_iff q hqlt).mpr ⟨k, by omega, hkeq⟩
        have hkvar : (s.trl[k]?.getD 0#32).toNat / 2 = q / 2 := by
          rw [hkeq]; exact litVar_litNeg q
        have hvl_le : (s.lvl[q / 2]?.getD 0#32).toNat ≤ s.cur_level := by
          rw [← hkvar]; exact hcore.lvl_le k (by omega)
        by_cases hvl0 : (s.lvl[q / 2]?.getD 0#32).toNat = 0
        · right
          have hs0 := hcore.level0_sound k (by omega) (by rw [hkvar]; exact hvl0)
          rwa [hkeq] at hs0
        · left
          obtain ⟨_, hq_rest⟩ := hall q hq
          have hq_mrk' : mrk'[q / 2]?.getD 0#8 ≠ 0#8 := (hq_rest hskip).1 (by omega)
          by_cases hcl : (s.lvl[q / 2]?.getD 0#32).toNat = s.cur_level
          · apply List.mem_append_right
            refine List.mem_map.mpr ⟨k, List.mem_filter.mpr ⟨List.mem_range.mpr hk, ?_⟩, ?_⟩
            · simp [hkvar, hq_mrk', hcl]
            · rw [hkeq]; exact litNeg_litNeg q
          · apply List.mem_append_left
            rw [mem_lowerLits_iff (by omega) (by omega)]
            rcases hcov' (q / 2) (by omega) hq_mrk' with ⟨j, hj1, hj2, hjeq⟩ | ⟨_, _, _, hbad⟩
            · obtain ⟨hl_lt, hl_fals, _, _, _⟩ := hlow' j hj1 hj2
              have hl_eq := hcore.falsified_lit_unique hl_lt hqlt hjeq hl_fals hq_fals
              exact ⟨j, hj1, hj2, hl_eq⟩
            · omega
  exact ⟨htc', hlow', hcov', hlow_sub, hcur_sub, hq_res⟩

/-- `kissat_clear_marks(h, idx)` restores `MarksClear` once `curTrailIdxs s mrk idx = []`. -/
private theorem clear_marks_restores_marksClear {c : ArenaCfg} {s : ArenaState}
    {tmp : List (BitVec 32)} {mrk mrk' : List (BitVec 8)} {tl idx : Nat}
    (hcov : MarksCov c s tmp mrk tl)
    (hzero : (curTrailIdxs s mrk idx).length = 0)
    (hpres : ∀ v < c.mv, mrk[v]?.getD 0#8 = 0#8 → mrk'[v]?.getD 0#8 = 0#8)
    (hclrt : ∀ i, 1 ≤ i → i < tl → (tmp[i]?.getD 0#32).toNat / 2 < c.mv →
      mrk'[(tmp[i]?.getD 0#32).toNat / 2]?.getD 0#8 = 0#8)
    (hclrr : ∀ j, idx ≤ j → j < s.trail_end → (s.trl[j]?.getD 0#32).toNat / 2 < c.mv →
      mrk'[(s.trl[j]?.getD 0#32).toNat / 2]?.getD 0#8 = 0#8) :
    ∀ v < c.mv, mrk'[v]?.getD 0#8 = 0#8 := by
  intro v hv
  by_cases hm0 : mrk[v]?.getD 0#8 = 0#8
  · exact hpres v hv hm0
  · rcases hcov v hv hm0 with ⟨i, hi1, hilt, hveq⟩ | ⟨j, hjlt, hveq, hcl⟩
    · rw [← hveq]; exact hclrt i hi1 hilt (by omega)
    · have hjge : idx ≤ j := by
        by_cases hlt : j < idx
        · exfalso
          have hmem : j ∈ curTrailIdxs s mrk idx :=
            List.mem_filter.mpr ⟨List.mem_range.mpr hlt, by simp [hveq, hm0, hcl]⟩
          have hpos := List.length_pos_of_mem hmem; omega
        · omega
      rw [← hveq]; exact hclrr j hjge hjlt (by omega)

private theorem tmp_take_eq_cons_lowerLits {tmp : List (BitVec 32)} {tl : Nat} {uip : BitVec 32}
    (h1 : 1 ≤ tl) (hle : tl ≤ tmp.length) (h0 : tmp[0]? = some uip) :
    (tmp.take tl).map BitVec.toNat = uip.toNat :: lowerLits tmp tl := by
  unfold lowerLits
  cases tmp with
  | nil => simp at h0
  | cons x xs =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h0; subst h0
    cases tl with
    | zero => omega
    | succ k => simp [List.take_succ_cons]

private theorem swap_tmp_props {tmp : List (BitVec 32)} {tl max_idx : Nat} {uip : BitVec 32}
    (h2 : 2 ≤ tl) (hle : tl ≤ tmp.length) (hm1 : 1 ≤ max_idx) (hmlt : max_idx < tl)
    (h0 : tmp[0]? = some uip) :
    let w1 := tmp[1]'(by omega)
    let wm := tmp[max_idx]'(by omega)
    let tmp_sw := (tmp.set 1 wm).set max_idx w1
    (∀ l, l ∈ (tmp_sw.take tl).map BitVec.toNat ↔ l ∈ (tmp.take tl).map BitVec.toNat) ∧
    (∀ l ∈ (tmp_sw.take tl).map BitVec.toNat,
      l = uip.toNat ∨ ∃ j, 1 ≤ j ∧ j < tl ∧ (tmp[j]?.getD 0#32).toNat = l) := by
  intro w1 wm tmp_sw
  have hlen_sw : tmp_sw.length = tmp.length := by simp [tmp_sw]
  have hmem_take : ∀ (xs : List (BitVec 32)), tl ≤ xs.length → ∀ l,
      l ∈ (xs.take tl).map BitVec.toNat ↔ ∃ j, j < tl ∧ (xs[j]?.getD 0#32).toNat = l := by
    intro xs hxs l
    rw [List.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp hx
      have hjlt : j < tl := by rw [List.length_take] at hj; omega
      rw [List.getElem_take] at hget
      exact ⟨j, hjlt, by rw [List.getElem?_eq_getElem (by omega), Option.getD_some, hget]⟩
    · rintro ⟨j, hj, hget⟩
      have hj' : j < (xs.take tl).length := by rw [List.length_take]; omega
      refine ⟨xs[j]'(by omega), ?_, ?_⟩
      · simpa [List.getElem_take] using List.getElem_mem hj'
      · rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at hget
  have hiff : ∀ l, l ∈ (tmp_sw.take tl).map BitVec.toNat ↔ l ∈ (tmp.take tl).map BitVec.toNat := by
    intro l
    rw [hmem_take tmp_sw (by omega), hmem_take tmp hle]
    constructor
    · rintro ⟨j, hj, hget⟩
      by_cases hjm : j = max_idx
      · subst j
        rw [show tmp_sw[max_idx]? = some w1 from List.getElem?_set_self (by simp; omega),
          Option.getD_some] at hget
        exact ⟨1, by omega,
          by rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; exact hget⟩
      · rw [show tmp_sw[j]? = (tmp.set 1 wm)[j]? from List.getElem?_set_ne (Ne.symm hjm)] at hget
        by_cases hj1 : j = 1
        · subst j
          rw [List.getElem?_set_self (by omega), Option.getD_some] at hget
          exact ⟨max_idx, hmlt,
            by rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; exact hget⟩
        · rw [List.getElem?_set_ne (Ne.symm hj1)] at hget
          exact ⟨j, hj, hget⟩
    · rintro ⟨j, hj, hget⟩
      by_cases hj1 : j = 1
      · subst j
        refine ⟨max_idx, hmlt, ?_⟩
        rw [show tmp_sw[max_idx]? = some w1 from List.getElem?_set_self (by simp; omega),
          Option.getD_some]
        rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at hget
      · by_cases hjm : j = max_idx
        · subst j
          refine ⟨1, by omega, ?_⟩
          have hne : max_idx ≠ 1 := hj1
          rw [show tmp_sw[1]? = (tmp.set 1 wm)[1]? from List.getElem?_set_ne hne,
            List.getElem?_set_self (by omega), Option.getD_some]
          rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at hget
        · refine ⟨j, hj, ?_⟩
          rw [show tmp_sw[j]? = (tmp.set 1 wm)[j]? from List.getElem?_set_ne (Ne.symm hjm),
            List.getElem?_set_ne (Ne.symm hj1)]
          exact hget
  refine ⟨hiff, fun l hl => ?_⟩
  rw [hiff, hmem_take tmp hle] at hl
  obtain ⟨j, hj, hget⟩ := hl
  cases j with
  | zero => rw [h0, Option.getD_some] at hget; exact Or.inl hget.symm
  | succ k => exact Or.inr ⟨k + 1, by omega, hj, hget⟩

/-! ## 2. `kissat_analyze` specification and `Func.wp` proof -/

/-- Specification of `kissat_analyze(h, confl_cid)`. -/
def kissatAnalyzeSpec : Spec [i64, i64] [i64] :=
  fun (h, confl_cid, ()) m Q _ =>
    ∃ (c : ArenaCfg) (F0 : CNF Nat) (s : ArenaState) (R : Mem 64 → Prop),
      h = c.hdr ∧ SolverInv c F0 s ∧ confl_cid.toNat < s.num_clauses ∧
      (∀ l ∈ clauseLits s confl_cid.toNat, s.vals[l]?.getD 0#8 = 0xFF#8) ∧
      (ArenaMem c s ⋆ R) m ∧
      ∀ r s' m',
        s'.LengthsOk c →
        (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
        s'.d_cur = s.d_cur → s'.d_val = s.d_val → s'.fuel = s.fuel →
        (r = 20#64 → F0.Unsat) →
        (r = 1#64 → SolverInv c F0 s') →
        (ArenaMem c s' ⋆ R) m' → Q (r, ()) m'

theorem kissat_analyze_wp (Γ : Env)
    (hAc : ∀ args m Q X, kissatAnalyzeClauseSpec args m Q X →
      Γ "kissat_analyze_clause" [i64, i32, i32] [.bool] args m Q X)
    (hCm : ∀ args m Q X, kissatClearMarksSpec args m Q X →
      Γ "kissat_clear_marks" [i64, i64] [] args m Q X)
    (hBt : ∀ args m Q X, kissatBacktrackSpec args m Q X →
      Γ "kissat_backtrack" [i64, i64] [] args m Q X)
    (hAddCl : ∀ args m Q X, kissatAddClauseSpec args m Q X →
      Γ "kissat_add_clause" [i64, i32] [i64] args m Q X)
    (hAssign : ∀ args m Q X, kissatAssignSpec args m Q X →
      Γ "kissat_assign" [i64, i32, i32] [] args m Q X) :
    ∀ args m Q X, kissatAnalyzeSpec args m Q X →
      Func.wp Γ kissat_analyze_body args m Q X := by
  rintro ⟨h, confl_cid, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hcid, hfals, hm, hQ⟩
  unfold Func.wp kissat_analyze_body; wp_unfold
  have hmv := c.hmv; have hmc := c.hmax_c; have hlc := c.hlcap
  unfold dimacsBound at hmv hmc hlc
  have hcore := hinv.core; have hlen := hcore.lengths
  have hcl64 : s.cur_level < 2 ^ 64 := by have := hlen.cur_level_lt; omega
  have hnc_le := hlen.num_clauses_le
  have hte_le := hlen.trail_end_le
  -- Helper for returning `0ULL` after `kissat_clear_marks(h, 0ULL)`
  have hfail_cm : ∀ (st : ArenaState) (ml : Mem 64),
      st.LengthsOk c → st.tmp_len ≤ c.mv →
      st.d_cur = s.d_cur → st.d_val = s.d_val → st.fuel = s.fuel →
      (ArenaMem c st ⋆ R) ml →
      wp Γ Q X
        (Expr.call (rs := [i64]) (as := [i64, i64]) (bs := []) "kissat_clear_marks"
          (Arg.var c.hdr, Arg.imm 0#64, ())
          fun _ => Expr.ret (rs := [i64]) (Arg.imm 0#64, ())) ml := by
    intro st ml hstl htl_mv hd1 hd2 hfu hml
    apply wp_call_of_spec; apply hCm
    refine ⟨c, st, R, rfl, hstl, htl_mv, hml, fun mrk' m' hml' _ _ _ hm' => ?_⟩
    wp_unfold
    exact hQ 0#64 { st with mrk := mrk' } m'
      (same_core_lengths hstl hml' hstl.tmp_len_arr hstl.tmp_cnt_lt hstl.tmp_len_lt)
      (Or.inl rfl) hd1 hd2 hfu (fun hc => by cases hc) (fun hc => by cases hc) hm'
  -- Step 1: if (h->cur_level == 0ULL) return 20ULL;
  refine ⟨_, load_arena_cur_level hm, ?_⟩
  rw [bv_eq_zero_iff hcl64]
  refine ⟨fun hcl0 => ?_, fun hcl_nz => ?_⟩
  · exact hQ 20#64 s m hlen (Or.inr (Or.inr rfl)) rfl rfl rfl
      (fun _ => hcore.level0_unsat_of_conflict hcl0 hcid hfals) (fun hc => by cases hc) hm
  have hcur_pos : 0 < s.cur_level := by omega
  have hmv_pos : 1 ≤ c.mv := by have := hcore.cur_level_le; omega
  -- Step 2: h->tmp_cnt = 0ULL; h->tmp_len = 1ULL;
  obtain ⟨ok_tc0, hm1⟩ := store_arena_tmp_cnt 0 hm
  refine ⟨ok_tc0, ?_⟩
  obtain ⟨ok_tl1, hm2⟩ := store_arena_tmp_len 1 hm1
  refine ⟨ok_tl1, ?_⟩
  let s1 : ArenaState := { s with tmp_cnt := 0, tmp_len := 1 }
  have hs1_len : s1.LengthsOk c :=
    same_core_lengths hlen hlen.mrk_len hlen.tmp_len_arr (by decide) (by decide)
  -- Step 3: kissat_analyze_clause(h, (u32)confl_cid, 0xFFFFFFFFu)
  apply wp_call_of_spec; apply hAc
  refine ⟨c, s1, R, rfl, hs1_len, hmv_pos, by dsimp [s1]; omega, hm2, ?_⟩
  intro ok1 mrk1 tmp1 tc1 tl1 m3 s2_ac hs2_len htl1_ge htl1_le htc1_ge hmp1 htp1 hnm1 hnt1 hcnt1
    hall1 hm3
  dsimp only [s2_ac, s1] at hs2_len htl1_ge htc1_ge hmp1 htp1 hnm1 hnt1 hcnt1 hall1 hm3
  clear s2_ac
  wp_unfold
  simp only [Arg.val_var, Arg.val_imm] at *
  cases ok1 with
  | false =>
    wp_unfold
    exact hfail_cm _ m3 hs2_len htl1_le rfl rfl rfl hm3
  | true =>
    wp_unfold
    have hcid32 : (confl_cid.setWidth 32).toNat = confl_cid.toNat := by
      simp [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega : confl_cid.toNat < 2 ^ 32)]
    have hct0 : (curTrailIdxs s s.mrk s.trail_end).length = 0 := by
      have hnil : curTrailIdxs s s.mrk s.trail_end = [] :=
        List.filter_eq_nil_iff.mpr fun j hj => by
          have hjlt := List.mem_range.mp hj
          have hvlt : (s.trl[j]?.getD 0#32).toNat / 2 < c.mv := by
            have := hcore.trail_lits_lt j hjlt; omega
          simp [hinv.marks _ hvlt]
      simp [hnil]
    have hcl_confl : ∀ q ∈ clauseLits s confl_cid.toNat,
        q / 2 = (0xFFFFFFFF#32).toNat ∨ ∃ k < s.trail_end, (s.trl[k]?.getD 0#32).toNat = q ^^^ 1 :=
      fun q hq =>
        Or.inr ((hcore.vals_false_iff q (hcore.clauses.lits_lt _ hcid q hq)).mp (hfals q hq))
    have hnm1' := hcid32 ▸ hnm1; have hnt1' := hcid32 ▸ hnt1
    have hall1' := (hcid32 ▸ (hall1 rfl)).2.2
    obtain ⟨htc1_eq, hlow1, hcov1, _, _, hq1⟩ :=
      analyzeClause_preserves hcore (Nat.le_refl _) (Nat.le_refl _) htl1_ge htl1_le
        hlen.mrk_len hlen.tmp_len_arr hs2_len.mrk_len hs2_len.tmp_len_arr
        hct0.symm htc1_ge (fun _ h1 h2 => by omega)
        (fun v hv hnz => absurd (hinv.marks v hv) hnz) hcid hcl_confl
        hmp1 htp1 hnm1' hnt1' hcnt1 hall1'
    have hent1 : F0.EntailsClause (cnfClause (activeResolvent s tmp1 mrk1 tl1 s.trail_end)) := by
      refine entails_of_mem_or_false (hcore.clauses.entails confl_cid.toNat hcid) fun q hq => ?_
      rcases hq1 q hq with hskip | hmem | hf
      · have hqlt := hcore.clauses.lits_lt confl_cid.toNat hcid q hq
        have : (0xFFFFFFFF#32).toNat = 2 ^ 32 - 1 := rfl
        omega
      · exact Or.inl hmem
      · exact Or.inr hf
    let s2 : ArenaState := { s with mrk := mrk1, tmp := tmp1, tmp_cnt := tc1, tmp_len := tl1 }
    have htc1_le_mv : tc1 ≤ c.mv := by
      rw [htc1_eq]; exact Nat.le_trans (List.length_filter_le _ _) (by simp; omega)
    -- Step 4: if (h->tmp_cnt == 0ULL) clear marks and return 20 (if empty) or 0
    refine ⟨_, load_arena_tmp_cnt (s := s2) hm3, ?_⟩
    dsimp only [s2]
    rw [bv_eq_zero_iff (by omega)]
    refine ⟨fun htc1_0 => ?_, fun htc1_nz => ?_⟩
    · apply wp_call_of_spec; apply hCm
      refine ⟨c, s2, R, rfl, hs2_len, htl1_le, hm3, fun mrk_z m_z hmlz _ _ _ hm_z => ?_⟩
      wp_unfold
      refine ⟨_, load_arena_tmp_len (s := { s2 with mrk := mrk_z }) hm_z, ?_⟩
      change (BitVec.ofNat 64 tl1 = 1 → _) ∧ (¬ BitVec.ofNat 64 tl1 = 1 → _)
      have htl1_eq1 : (BitVec.ofNat 64 tl1 = (1 : BitVec 64)) ↔ tl1 = 1 := by
        constructor
        · intro he; have := congrArg BitVec.toNat he
          simpa [Nat.mod_eq_of_lt (by omega : tl1 < 2 ^ 64)] using this
        · intro he; rw [he]; rfl
      rw [htl1_eq1]
      have hz_len : ({ s2 with mrk := mrk_z } : ArenaState).LengthsOk c :=
        same_core_lengths hs2_len hmlz hs2_len.tmp_len_arr hs2_len.tmp_cnt_lt hs2_len.tmp_len_lt
      refine ⟨fun htl_is1 => ?_, fun _ =>
        hQ 0#64 _ m_z hz_len (Or.inl rfl) rfl rfl rfl
          (fun hc => by cases hc) (fun hc => by cases hc) hm_z⟩
      refine hQ 20#64 _ m_z hz_len (Or.inr (Or.inr rfl)) rfl rfl rfl (fun _ => ?_)
        (fun hc => by cases hc) hm_z
      have hres_nil : activeResolvent s tmp1 mrk1 tl1 s.trail_end = [] := by
        unfold activeResolvent lowerLits curLits
        have hct_nil : curTrailIdxs s mrk1 s.trail_end = [] :=
          List.eq_nil_of_length_eq_zero (by rw [← htc1_eq]; exact htc1_0)
        simp [htl_is1, hct_nil]
      rw [hres_nil] at hent1
      exact unsat_of_entails_nil hent1
    -- Step 5: load pointers & enter 1UIP loop
    refine ⟨_, load_arena_mark (s := s2) hm3, _, load_arena_level (s := s2) hm3,
      _, load_arena_reason (s := s2) hm3, _, load_arena_trail (s := s2) hm3,
      _, load_arena_tmp_lits (s := s2) hm3, _, load_arena_values (s := s2) hm3,
      _, load_arena_cur_level (s := s2) hm3, _, load_arena_trail_end (s := s2) hm3, ?_⟩
    -- 1UIP loop with break: loop var is `(idx_v, ())`, break vars are `(idx_v, uip_v, ())`
    refine wp_loop_break_group
      (fun (idx_v, uip_v, ()) mb => ∃ idx mrk_b tmp_b tl_b p_bv,
        idx < s.trail_end ∧ idx_v = BitVec.ofNat 64 idx ∧
        s.trl[idx]? = some p_bv ∧
        uip_v = p_bv ^^^ 1#32 ∧
        (s.lvl[p_bv.toNat / 2]?.getD 0#32).toNat = s.cur_level ∧
        mrk_b.length = c.mv ∧ tmp_b.length = c.mv ∧
        1 ≤ tl_b ∧ tl_b ≤ c.mv ∧
        (curTrailIdxs s mrk_b idx).length = 0 ∧
        LowerInv c s tmp_b mrk_b tl_b ∧
        MarksCov c s tmp_b mrk_b tl_b ∧
        F0.EntailsClause (cnfClause (uip_v.toNat :: lowerLits tmp_b tl_b)) ∧
        (ArenaMem c { s with mrk := mrk_b, tmp := tmp_b, tmp_cnt := 0, tmp_len := tl_b } ⋆ R) mb)
      (fun r (idx_v, ()) ml => ∃ idx mrk_l tmp_l tc_l tl_l,
        idx ≤ s.trail_end ∧ r = idx ∧ idx_v = BitVec.ofNat 64 idx ∧
        mrk_l.length = c.mv ∧ tmp_l.length = c.mv ∧
        1 ≤ tl_l ∧ tl_l ≤ c.mv ∧
        0 < tc_l ∧ tc_l = (curTrailIdxs s mrk_l idx).length ∧
        LowerInv c s tmp_l mrk_l tl_l ∧
        MarksCov c s tmp_l mrk_l tl_l ∧
        F0.EntailsClause (cnfClause (activeResolvent s tmp_l mrk_l tl_l idx)) ∧
        (ArenaMem c { s with mrk := mrk_l, tmp := tmp_l, tmp_cnt := tc_l, tmp_len := tl_l } ⋆ R) ml)
      ?_ ?_ ?_
    · -- Post-1UIP-loop continuation (lines 618-655)
      rintro _ ⟨idx_v, uip_v, ⟨⟩⟩ mb
        ⟨idx, mrk_b, tmp_b, tl_b, p_bv, hidx_lt, rfl, hp_def, rfl, hp_cl,
          hmb_len, htb_len, htlb1, htlb_mv, hct_b0, hlow_b, hcov_b, hent_b, hmb⟩
      wp_unfold
      have hp_lt : p_bv.toNat < 2 * c.mv := by
        have := hcore.trail_lits_lt idx hidx_lt
        rwa [hp_def, Option.getD_some] at this
      let uip := p_bv ^^^ 1#32
      have huip_nat : uip.toNat = p_bv.toNat ^^^ 1 := bv32_xor_1 p_bv
      have huip_lt : uip.toNat < 2 * c.mv := by rw [huip_nat]; exact litNeg_lt_two_mul hp_lt
      have huip_ne : uip ≠ 0xFFFFFFFF#32 := by
        intro heq; have := congrArg BitVec.toNat heq; change uip.toNat = 2 ^ 32 - 1 at this; omega
      refine ⟨fun heq => absurd heq huip_ne, fun _ => ?_⟩
      -- tmp[0] = uip_lit;
      let sb : ArenaState := { s with mrk := mrk_b, tmp := tmp_b, tmp_cnt := 0, tmp_len := tl_b }
      rw [show ((0 : BitVec 32).signExtend 64) * (4 : BitVec 64) = BitVec.ofNat 64 (4 * 0) from rfl]
      obtain ⟨ok_t0, hmt0⟩ := store_arena_tmp (s := sb) (i := 0) uip
        (by dsimp [sb]; omega) hmb
      refine ⟨ok_t0, ?_⟩
      let tmp0 := tmp_b.set 0 uip
      let st0 : ArenaState := { s with mrk := mrk_b, tmp := tmp0, tmp_cnt := 0, tmp_len := tl_b }
      have hst0_len : st0.LengthsOk c :=
        same_core_lengths hlen hmb_len (by simp [tmp0, htb_len]) (by decide) (by omega)
      have htmp0_gt0 : ∀ j, 1 ≤ j → tmp0[j]? = tmp_b[j]? := fun j hj =>
        List.getElem?_set_ne (by omega)
      have hlow0 : LowerInv c s tmp0 mrk_b tl_b := fun j hj1 hj2 => by
        rw [htmp0_gt0 j hj1]; exact hlow_b j hj1 hj2
      have hcov0 : MarksCov c s tmp0 mrk_b tl_b := fun v hv hnz =>
        (hcov_b v hv hnz).elim
          (fun ⟨j, hj1, hj2, hjeq⟩ => Or.inl ⟨j, hj1, hj2, by rw [htmp0_gt0 j hj1]; exact hjeq⟩)
          Or.inr
      have hlowLits0 : lowerLits tmp0 tl_b = lowerLits tmp_b tl_b := by
        change lowerLits (tmp_b.set 0 uip) tl_b = lowerLits tmp_b tl_b
        unfold lowerLits
        cases tmp_b with
        | nil => rfl
        | cons x xs => rfl
      -- kissat_clear_marks(h, idx);
      apply wp_call_of_spec; apply hCm
      refine ⟨c, st0, R, rfl, hst0_len, htlb_mv, hmt0,
        fun mrk_c m_c hmc_len hmc_pres hmc_clrt hmc_clrr hm_c => ?_⟩
      wp_unfold
      have hidx_nat : (BitVec.ofNat 64 idx).toNat = idx := bv64_ofNat_toNat (by omega)
      have hmc_clrr' := hidx_nat ▸ hmc_clrr
      let sc : ArenaState := { s with mrk := mrk_c, tmp := tmp0, tmp_cnt := 0, tmp_len := tl_b }
      have hmarks_c : MarksClear c sc :=
        clear_marks_restores_marksClear hcov0 hct_b0 hmc_pres hmc_clrt hmc_clrr'
      have hsc_core : SolverCoreInv c F0 sc :=
        same_core_solverCoreInv hcore hmc_len (by simp [tmp0, htb_len]) (by decide) (by omega)
      have hsc_inv : SolverInv c F0 sc := ⟨hsc_core, hmarks_c⟩
      -- if (h->tmp_len == 1ULL) { ... }
      refine ⟨_, load_arena_tmp_len (s := sc) hm_c, ?_⟩
      change (BitVec.ofNat 64 tl_b = 1 → _) ∧ (¬ BitVec.ofNat 64 tl_b = 1 → _)
      have htlb_eq1 : (BitVec.ofNat 64 tl_b = (1 : BitVec 64)) ↔ tl_b = 1 := by
        constructor
        · intro he; have := congrArg BitVec.toNat he
          simpa [Nat.mod_eq_of_lt (by omega : tl_b < 2 ^ 64)] using this
        · intro he; rw [he]; rfl
      rw [htlb_eq1]
      refine ⟨fun htl_is1 => ?_, fun htl_ne1 => ?_⟩
      · -- Unit learned clause branch (lines 624-631)
        have hent_unit : F0.EntailsClause (cnfClause [uip.toNat]) := by
          have hnil : lowerLits tmp_b tl_b = [] := by unfold lowerLits; simp [htl_is1]
          rw [huip_nat]; simpa [hnil] using hent_b
        apply wp_call_of_spec; apply hBt
        refine ⟨c, F0, sc, R, rfl, hsc_inv, Nat.zero_le _, hm_c,
          fun sbt mbt hbt_inv hbt_d1 hbt_d2 _ _ hbt_cl _ hbt_fu _ _ _ _ _ _ _ _ _ _ hmbt => ?_⟩
        wp_unfold
        simp only [Arg.val_imm] at hbt_cl
        have hbt_cl0 : sbt.cur_level = 0 := hbt_cl
        rw [bv32_zext64_eq]
        have huip_vlen : uip.toNat < sbt.vals.length := by
          rw [hbt_inv.core.lengths.vals_len]; exact huip_lt
        refine ⟨_, load_arena_vals (s := sbt) huip_vlen hmbt, ?_⟩
        have hdom : sbt.vals[uip.toNat]'huip_vlen = 0#8 ∨ sbt.vals[uip.toNat]'huip_vlen = 1#8 ∨
            sbt.vals[uip.toNat]'huip_vlen = 0xFF#8 := by
          have := hbt_inv.core.vals_domain uip.toNat huip_lt
          rwa [List.getElem?_eq_getElem huip_vlen, Option.getD_some] at this
        rw [show (BitVec.setWidth 8 (0 : BitVec 32)).signExtend 32 = 0#32 from rfl,
          i8_vals_eq0 hdom]
        refine ⟨fun hnz => hQ 0#64 sbt mbt hbt_inv.core.lengths (Or.inl rfl) hbt_d1 hbt_d2 hbt_fu
            (fun hc => by cases hc) (fun hc => by cases hc) hmbt,
          fun hz => ?_⟩
        have hz_get : sbt.vals[uip.toNat]?.getD 0#8 = 0#8 := by
          rw [List.getElem?_eq_getElem huip_vlen, Option.getD_some]; exact hz
        have hbt_te_lt : sbt.trail_end < c.mv :=
          hbt_inv.core.trail_end_lt_of_unassigned huip_lt hz_get
        have hnot_oob : ¬ (c.mv ≤ uip.toNat / 2 ∨ c.mv ≤ sbt.trail_end) := by omega
        apply wp_call_of_spec; apply hAssign
        refine ⟨c, sbt, R, rfl, hbt_inv.core.lengths, hmbt, ?_⟩
        simp only [Arg.val_var, Arg.val_imm]
        change if c.mv ≤ uip.toNat / 2 ∨ c.mv ≤ sbt.trail_end then _ else _
        simp only [hnot_oob, ↓reduceIte]
        intro mf hflen hmf
        wp_unfold
        have hfin_core := assign_preserves_core hbt_inv.core (lit := uip) (rsn := 0xFFFFFFFF#32)
          huip_lt hz_get (by omega) (fun L h1 h2 => by omega) (fun _ => hent_unit)
          (fun hne => absurd rfl hne)
        exact hQ 1#64 _ mf hflen (Or.inr (Or.inl rfl)) hbt_d1 hbt_d2 hbt_fu
          (fun hc => by cases hc) (fun _ => ⟨hfin_core, hbt_inv.marks⟩) hmf
      · -- Non-unit learned clause branch (`tl_b ≥ 2`, lines 632-655)
        have htl_ge2 : 2 ≤ tl_b := by omega
        rw [show ((1 : BitVec 32).signExtend 64) * (4 : BitVec 64) =
          BitVec.ofNat 64 (4 * 1) from rfl]
        have h1_lt : 1 < tmp0.length := by simp [tmp0, htb_len]; omega
        refine ⟨_, load_arena_tmp (s := sc) h1_lt hm_c, ?_⟩
        have hlow1_sc := hlow0 1 (Nat.le_refl _) (by omega)
        have htmp0_1 : (tmp0[1]'h1_lt).toNat = (tmp0[1]?.getD 0#32).toNat := by
          rw [List.getElem?_eq_getElem h1_lt, Option.getD_some]
        have hv1_lt : (tmp0[1]'h1_lt).toNat / 2 < c.mv := by omega
        rw [bv32_mul4_eq, bv32_lshr_1]
        refine ⟨_, load_arena_lvl (s := sc) (i := (tmp0[1]'h1_lt).toNat / 2)
          (by dsimp [sc, st0, sb]; rw [hlen.lvl_len]; exact hv1_lt) hm_c, ?_⟩
        generalize hml1_def :
          s.lvl[(tmp0[1]'h1_lt).toNat / 2]'(by rw [hlen.lvl_len]; exact hv1_lt) = ml1_bv
        have hml1_eq : ml1_bv.toNat = (s.lvl[(tmp0[1]?.getD 0#32).toNat / 2]?.getD 0#32).toNat := by
          rw [← htmp0_1, List.getElem?_eq_getElem (by rw [hlen.lvl_len]; exact hv1_lt),
            Option.getD_some, hml1_def]
        -- Loop: while (k < h->tmp_len) find max_lvl and max_idx
        refine wp_loop_group
          (fun r (midx_v, mlvl_v, k_v, ()) mk => ∃ midx mlvl k,
            2 ≤ k ∧ k ≤ tl_b ∧ r = tl_b - k ∧
            1 ≤ midx ∧ midx < k ∧
            0 < mlvl ∧ mlvl < s.cur_level ∧
            midx_v = BitVec.ofNat 64 midx ∧ mlvl_v = BitVec.ofNat 64 mlvl ∧
            k_v = BitVec.ofNat 64 k ∧
            (∀ j, 1 ≤ j → j < k → (s.lvl[(tmp0[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ mlvl) ∧
            (ArenaMem c sc ⋆ R) mk) ?_ ?_
        · rintro L r ⟨midx_v, mlvl_v, k_v, ⟨⟩⟩ mk ih
            ⟨midx, mlvl, k, hk2, hkle, rfl, hmi1, hmik, hml_pos, hml_lt, rfl, rfl, rfl,
              hall_ml, hmk⟩
          wp_unfold
          refine ⟨_, load_arena_tmp_len (s := sc) hmk, ?_⟩
          dsimp only [sc]
          rw [bv_ult_eq (by omega) (by omega)]
          simp only [decide_eq_true_eq, decide_eq_false_iff_not]
          refine ⟨fun hklt => ?_, fun hkge => ?_⟩
          · rw [bv64_mul4_nat]
            have hk_t : k < tmp0.length := by simp [tmp0, htb_len]; omega
            refine ⟨_, load_arena_tmp (s := sc) hk_t hmk, ?_⟩
            have hlowk := hlow0 k (by omega) hklt
            have htmp0_k : (tmp0[k]'hk_t).toNat = (tmp0[k]?.getD 0#32).toNat := by
              rw [List.getElem?_eq_getElem hk_t, Option.getD_some]
            have hvk_lt : (tmp0[k]'hk_t).toNat / 2 < c.mv := by omega
            rw [bv32_mul4_eq, bv32_lshr_1]
            refine ⟨_, load_arena_lvl (s := sc) (i := (tmp0[k]'hk_t).toNat / 2)
              (by dsimp [sc, st0, sb]; rw [hlen.lvl_len]; exact hvk_lt) hmk, ?_⟩
            generalize hkl_def :
              s.lvl[(tmp0[k]'hk_t).toNat / 2]'(by rw [hlen.lvl_len]; exact hvk_lt) = kl_bv
            have hkl_eq : kl_bv.toNat =
                (s.lvl[(tmp0[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat := by
              rw [← htmp0_k, List.getElem?_eq_getElem (by rw [hlen.lvl_len]; exact hvk_lt),
                Option.getD_some, hkl_def]
            refine wp_join_group
              (fun (mi_v, ml_v, ()) m2 => ∃ mi' ml',
                1 ≤ mi' ∧ mi' < k + 1 ∧ 0 < ml' ∧ ml' < s.cur_level ∧
                mi_v = BitVec.ofNat 64 mi' ∧ ml_v = BitVec.ofNat 64 ml' ∧
                (∀ j, 1 ≤ j → j < k + 1 →
                  (s.lvl[(tmp0[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ ml') ∧
                (ArenaMem c sc ⋆ R) m2) ?_ ?_
            · rintro _ ⟨mi_v, ml_v, ⟨⟩⟩ m2 ⟨mi', ml', h1', h2', h3', h4', rfl, rfl, hall', hm2'⟩
              wp_unfold
              rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, bv_add_ofNat]
              exact ih (tl_b - (k + 1)) _ _ (by omega)
                ⟨mi', ml', k + 1, by omega, by omega, rfl, h1', h2', h3', h4', rfl, rfl, rfl,
                  hall', hm2'⟩
            · intro J hJ; wp_unfold
              rw [bv32_zext64_eq, bv_ult_eq (by omega) (by have := kl_bv.isLt; omega)]
              simp only [decide_eq_true_eq, decide_eq_false_iff_not]
              refine ⟨fun hgt => ?_, fun hle => ?_⟩
              · refine hJ _ mk ⟨k, kl_bv.toNat, by omega, by omega, by omega, by omega,
                  rfl, rfl, ?_, hmk⟩
                intro j hj1 hjk
                by_cases hjk_eq : j = k
                · subst hjk_eq; omega
                · have := hall_ml j hj1 (by omega); omega
              · refine hJ _ mk ⟨midx, mlvl, hmi1, by omega, hml_pos, hml_lt, rfl, rfl, ?_, hmk⟩
                intro j hj1 hjk
                by_cases hjk_eq : j = k
                · subst hjk_eq; omega
                · exact hall_ml j hj1 (by omega)
          · -- After max_lvl loop (`k = tl_b`)
            have hkeq : k = tl_b := by omega
            subst k
            refine wp_join_group
              (fun (ml_v, ()) m2 => ml_v = BitVec.ofNat 64 mlvl ∧ (ArenaMem c sc ⋆ R) m2) ?_ ?_
            · rintro _ ⟨ml_v, ⟨⟩⟩ m2 ⟨rfl, hm2'⟩
              wp_unfold
              -- Swap tmp[1] and tmp[midx]
              rw [show ((1 : BitVec 32).signExtend 64) * (4 : BitVec 64) =
                BitVec.ofNat 64 (4 * 1) from rfl]
              refine ⟨_, load_arena_tmp (s := sc) h1_lt hm2', ?_⟩
              rw [bv64_mul4_nat]
              have hmi_t : midx < tmp0.length := by simp [tmp0, htb_len]; omega
              refine ⟨_, load_arena_tmp (s := sc) hmi_t hm2', ?_⟩
              obtain ⟨ok_sw1, hm_sw1⟩ := store_arena_tmp (s := sc) (i := 1)
                (tmp0[midx]'hmi_t) h1_lt hm2'
              refine ⟨ok_sw1, ?_⟩
              obtain ⟨ok_sw2, hm_sw2⟩ := store_arena_tmp
                (s := { sc with tmp := tmp0.set 1 (tmp0[midx]'hmi_t) })
                (i := midx) (tmp0[1]'h1_lt) (by simp [hmi_t]) hm_sw1
              refine ⟨ok_sw2, ?_⟩
              let tmp_sw := (tmp0.set 1 (tmp0[midx]'hmi_t)).set midx (tmp0[1]'h1_lt)
              let s_sw : ArenaState :=
                { s with mrk := mrk_c, tmp := tmp_sw, tmp_cnt := 0, tmp_len := tl_b }
              have hsw_len : tmp_sw.length = c.mv := by simp [tmp_sw, tmp0, htb_len]
              have hsw_inv : SolverInv c F0 s_sw :=
                ⟨same_core_solverCoreInv hcore hmc_len hsw_len (by decide) (by omega), hmarks_c⟩
              have htmp0_0 : tmp0[0]? = some uip := List.getElem?_set_self (by omega)
              obtain ⟨hsw_iff, hsw_mem⟩ := swap_tmp_props htl_ge2 (by simp [tmp0, htb_len]; omega)
                hmi1 hmik htmp0_0
              have hent_sw :
                  F0.EntailsClause (cnfClause ((tmp_sw.take tl_b).map BitVec.toNat)) := by
                have hent0 : F0.EntailsClause (cnfClause ((tmp0.take tl_b).map BitVec.toNat)) := by
                  rw [tmp_take_eq_cons_lowerLits htlb1 (by simp [tmp0, htb_len]; omega) htmp0_0,
                    hlowLits0]
                  exact hent_b
                exact entails_of_mem_or_false hent0 fun l hl => Or.inl ((hsw_iff l).mpr hl)
              -- kissat_backtrack(h, max_lvl)
              have hmlvl_nat : (BitVec.ofNat 64 mlvl).toNat = mlvl := bv64_ofNat_toNat (by omega)
              apply wp_call_of_spec; apply hBt
              refine ⟨c, F0, s_sw, R, rfl, hsw_inv, by
                  simp only [Arg.val_var]; dsimp [s_sw]; rw [hmlvl_nat]; omega,
                hm_sw2,
                fun sbt mbt hbt_inv hbt_d1 hbt_d2 _ _ hbt_cl hbt_te_le hbt_fu _ _ hbt_tl
                  hbt_tmp _ _ _ _ hbt_trl hbt_keep hmbt => ?_⟩
              wp_unfold
              simp only [Arg.val_var] at hbt_cl hbt_keep
              dsimp only [s_sw] at hbt_tl hbt_d1 hbt_d2 hbt_fu hbt_tmp hbt_trl hbt_keep
              rw [hmlvl_nat] at hbt_cl hbt_keep
              -- kissat_add_clause(h, (u32)h->tmp_len)
              refine ⟨_, load_arena_tmp_len (s := sbt) hmbt, ?_⟩
              have htl_tr : (BitVec.ofNat 64 sbt.tmp_len).setWidth 32 = BitVec.ofNat 32 tl_b := by
                rw [hbt_tl]; exact bv64_trunc32_ofNat (by omega)
              rw [htl_tr]
              apply wp_call_of_spec; apply hAddCl
              have htl32_nat : (BitVec.ofNat 32 tl_b).toNat = tl_b := bv32_ofNat_toNat (by omega)
              refine ⟨c, sbt, R, rfl, hbt_inv.core.lengths,
                by simp only [Arg.val_var]; omega, hmbt, ?_⟩
              simp only [Arg.val_var]
              by_cases hoom :
                  c.max_c ≤ sbt.num_clauses ∨ c.lcap - sbt.lit_len < (BitVec.ofNat 32 tl_b).toNat
              · simp only [hoom, ↓reduceIte]
                wp_unfold
                exact ⟨fun _ => hQ 0#64 sbt mbt hbt_inv.core.lengths (Or.inl rfl) hbt_d1 hbt_d2
                  hbt_fu (fun hc => by cases hc) (fun hc => by cases hc) hmbt,
                  fun hc => absurd rfl hc⟩
              · simp only [hoom, ↓reduceIte]
                intro sac mac hac_len hac_d1 hac_d2 hac_ll hac_nc hac_te _ hac_cl hac_fu _ _ _
                  hac_vals hac_mrk hac_lvl hac_rsns hac_trl _ hac_meta hac_lp hac_off hac_sz
                  hac_lits hmac
                wp_unfold
                have hnc_lt : sbt.num_clauses < c.max_c := by omega
                have hcid_ne : BitVec.ofNat 64 sbt.num_clauses ≠ 0xFFFFFFFF#64 := by
                  intro heq; have := congrArg BitVec.toNat heq
                  rw [bv64_ofNat_toNat (by omega)] at this
                  change sbt.num_clauses = 0xFFFFFFFF at this; omega
                refine ⟨fun heq => absurd heq hcid_ne, fun _ => ?_⟩
                rw [bv32_zext64_eq]
                have huip_vlen : uip.toNat < sac.vals.length := by
                  rw [hac_len.vals_len]; exact huip_lt
                refine ⟨_, load_arena_vals (s := sac) huip_vlen hmac, ?_⟩
                have hdom : sac.vals[uip.toNat]'huip_vlen = 0#8 ∨
                    sac.vals[uip.toNat]'huip_vlen = 1#8 ∨
                    sac.vals[uip.toNat]'huip_vlen = 0xFF#8 := by
                  have := hbt_inv.core.vals_domain uip.toNat huip_lt
                  rwa [← hac_vals, List.getElem?_eq_getElem huip_vlen, Option.getD_some] at this
                rw [show (BitVec.setWidth 8 (0 : BitVec 32)).signExtend 32 = 0#32 from rfl,
                  i8_vals_eq0 hdom]
                refine ⟨fun _ => hQ 0#64 sac mac hac_len (Or.inl rfl) (by rw [hac_d1, hbt_d1])
                    (by rw [hac_d2, hbt_d2]) (by rw [hac_fu, hbt_fu])
                    (fun hc => by cases hc) (fun hc => by cases hc) hmac,
                  fun hz => ?_⟩
                -- Both `new_cid ≠ 0xFFFFFFFF` and `vals[uip_lit] == 0` -> call `kissat_assign`!
                have hlits_lt : ∀ l ∈ (sbt.tmp.take tl_b).map BitVec.toNat, l < 2 * c.mv := by
                  rw [hbt_tmp]; intro l hl
                  rcases hsw_mem l hl with rfl | ⟨j, hj1, hj2, hjeq⟩
                  · exact huip_lt
                  · rw [← hjeq]; exact (hlow0 j hj1 hj2).1
                have hac_core : SolverCoreInv c F0 sac :=
                  addClause_preserves_core hbt_inv.core hac_len htl_ge2
                    (by simpa [htl32_nat] using hlits_lt)
                    (by simpa [htl32_nat, hbt_tmp] using hent_sw)
                    (by omega) hac_nc hac_te hac_cl hac_vals hac_lvl hac_rsns hac_trl
                    hac_meta hac_lp hac_off (by omega) (by simpa [htl32_nat] using hac_lits)
                have hz_get : sac.vals[uip.toNat]?.getD 0#8 = 0#8 := by
                  rw [List.getElem?_eq_getElem huip_vlen, Option.getD_some]; exact hz
                have hac_te_lt : sac.trail_end < c.mv :=
                  hac_core.trail_end_lt_of_unassigned huip_lt hz_get
                have hnot_oob : ¬ (c.mv ≤ uip.toNat / 2 ∨ c.mv ≤ sac.trail_end) := by omega
                apply wp_call_of_spec; apply hAssign
                refine ⟨c, sac, R, rfl, hac_len, hmac, ?_⟩
                simp only [Arg.val_var]
                change if c.mv ≤ uip.toNat / 2 ∨ c.mv ≤ sac.trail_end then _ else _
                simp only [hnot_oob, ↓reduceIte]
                intro mf hflen hmf
                wp_unfold
                have hrsn_tr : (BitVec.ofNat 64 sbt.num_clauses).setWidth 32 =
                    BitVec.ofNat 32 sbt.num_clauses := bv64_trunc32_ofNat (by omega)
                have hfin_core : SolverCoreInv c F0
                    { sac with
                      vals := (sac.vals.set uip.toNat 1#8).set (uip.toNat ^^^ 1) 0xFF#8
                      lvl := sac.lvl.set (uip.toNat / 2) (BitVec.ofNat 32 sac.cur_level)
                      rsns := sac.rsns.set (uip.toNat / 2)
                        ((BitVec.ofNat 64 sbt.num_clauses).setWidth 32)
                      trl := sac.trl.set sac.trail_end uip
                      trail_end := sac.trail_end + 1 } := by
                  refine assign_preserves_core hac_core huip_lt hz_get
                    (by have := hac_core.cur_level_le; omega)
                    (fun L h1 h2 => Or.inr (hac_core.levels_inhabited L h1 h2))
                    (fun h0 => by omega)
                    (fun _ => ?_)
                  rw [hrsn_tr, bv32_ofNat_toNat (by omega)]
                  refine ⟨by omega, fun q hq => ?_⟩
                  rw [hac_lits, htl32_nat, hbt_tmp] at hq
                  rcases hsw_mem q hq with rfl | ⟨j, hj1, hj2, hjeq⟩
                  · exact Or.inl rfl
                  · right
                    obtain ⟨hq_lt, hq_fals, _, _, _⟩ := hlow0 j hj1 hj2
                    rw [hjeq] at hq_lt hq_fals
                    obtain ⟨idx_k, hidx_k, hkeq⟩ := (hcore.vals_false_iff q hq_lt).mp hq_fals
                    have hklvl : (s.lvl[(s.trl[idx_k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
                        mlvl := by
                      have hvar : (s.trl[idx_k]?.getD 0#32).toNat / 2 = q / 2 := by
                        rw [hkeq]; exact litVar_litNeg q
                      rw [hvar, ← hjeq]; exact hall_ml j hj1 hj2
                    have hk_bt : idx_k < sbt.trail_end := hbt_keep idx_k hidx_k hklvl
                    exact ⟨idx_k, by omega, by rw [hac_trl, hbt_trl idx_k hk_bt]; exact hkeq⟩
                exact hQ 1#64 _ mf hflen (Or.inr (Or.inl rfl))
                  (by rw [hac_d1, hbt_d1]) (by rw [hac_d2, hbt_d2]) (by rw [hac_fu, hbt_fu])
                  (fun hc => by cases hc)
                  (fun _ => ⟨hfin_core, fun v hv => by simpa [hac_mrk] using hbt_inv.marks v hv⟩)
                  hmf
            · intro J hJ; wp_unfold
              rw [bv32_zext64_eq, bv64_trunc32_ofNat hlen.cur_level_lt,
                bv32_ofNat_toNat hlen.cur_level_lt, bv_ule_eq (by omega) (by omega)]
              simp only [decide_eq_true_eq, decide_eq_false_iff_not]
              exact ⟨fun hbad => by omega, fun _ => hJ _ mk ⟨rfl, hmk⟩⟩
        · intro L hL; wp_unfold
          rw [bv32_zext64_eq]
          refine hL (tl_b - 2) _ m_c ⟨1, ml1_bv.toNat, 2, Nat.le_refl _, htl_ge2, rfl,
            Nat.le_refl _, by omega, by omega, by omega, rfl, rfl, rfl, ?_, hm_c⟩
          intro j hj1 hj2
          have hj_eq : j = 1 := by omega
          subst hj_eq; omega
    · -- 1UIP loop body (lines 593-617)
      rintro B L r_cnt ⟨idx_v, ⟨⟩⟩ ml hB ih
        ⟨idx, mrk_l, tmp_l, tc_l, tl_l, hidx_le, hr_eq, rfl, hml_len, htl_len, htl1, htl_mv,
          htc_pos, htc_eq, hlow_l, hcov_l, hent_l, hml⟩
      subst r_cnt
      wp_unfold
      let sl : ArenaState := { s with mrk := mrk_l, tmp := tmp_l, tmp_cnt := tc_l, tmp_len := tl_l }
      have htc_le_mv : tc_l ≤ c.mv := by
        rw [htc_eq]; exact Nat.le_trans (List.length_filter_le _ _) (by simp; omega)
      have hsl_len : sl.LengthsOk c :=
        same_core_lengths hlen hml_len htl_len (by omega) (by omega)
      refine ⟨_, load_arena_tmp_cnt (s := sl) hml, ?_⟩
      dsimp only [sl]
      rw [show (0 : BitVec 64) = BitVec.ofNat 64 0 from rfl,
        bv_ult_eq (by decide) (by omega)]
      simp only [decide_eq_true_eq, decide_eq_false_iff_not]
      refine ⟨fun _ => ?_, fun hbad => by omega⟩
      -- if (idx == 0ULL) { kissat_clear_marks(h, 0ULL); return 0ULL; }
      rw [show (0#64 : BitVec 64) = (0 : BitVec 64) from rfl, bv_eq_zero_iff (by omega)]
      refine ⟨fun _ => hfail_cm sl ml hsl_len htl_mv rfl rfl rfl hml, fun hidx_nz => ?_⟩
      have hidx_pos : 0 < idx := by omega
      have hsub : BitVec.ofNat 64 idx - (1 : BitVec 64) = BitVec.ofNat 64 (idx - 1) := by
        rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl]
        exact bv_sub_ofNat (by omega) (by omega)
      rw [hsub, bv64_mul4_nat]
      have hi_trl : idx - 1 < s.trl.length := by rw [hlen.trl_len]; omega
      refine ⟨_, load_arena_trl (s := sl) hi_trl hml, ?_⟩
      generalize hp_def : s.trl[idx - 1]'hi_trl = p_bv
      have hp_get : (s.trl[idx - 1]?.getD 0#32).toNat = p_bv.toNat := by
        rw [List.getElem?_eq_getElem hi_trl, Option.getD_some, hp_def]
      have hp_lt : p_bv.toNat < 2 * c.mv := by
        have := hcore.trail_lits_lt (idx - 1) (by omega); rwa [hp_get] at this
      let pv := p_bv.toNat / 2
      have hpv_lt : pv < c.mv := by omega
      have hpv_eq : (p_bv >>> 1).setWidth 64 = BitVec.ofNat 64 pv := by
        rw [bv32_zext64_eq, bv32_lshr_1]
      refine ⟨_, load_arena_mv (s := sl) hml, ?_⟩
      rw [hpv_eq, bv_ule_eq (by omega) (by omega)]
      simp only [decide_eq_true_eq, decide_eq_false_iff_not]
      refine ⟨fun hbad => by omega, fun _ => ?_⟩
      -- Join point at end of loop body (jumps back to L)
      refine wp_join_group
        (fun (_uip_j, ()) m2 => ∃ mrk2 tmp2 tc2 tl2,
          mrk2.length = c.mv ∧ tmp2.length = c.mv ∧ 1 ≤ tl2 ∧ tl2 ≤ c.mv ∧
          0 < tc2 ∧ tc2 = (curTrailIdxs s mrk2 (idx - 1)).length ∧
          LowerInv c s tmp2 mrk2 tl2 ∧ MarksCov c s tmp2 mrk2 tl2 ∧
          F0.EntailsClause (cnfClause (activeResolvent s tmp2 mrk2 tl2 (idx - 1))) ∧
          (ArenaMem c { s with mrk := mrk2, tmp := tmp2, tmp_cnt := tc2, tmp_len := tl2 } ⋆ R) m2)
        ?_ ?_
      · rintro _ ⟨_uip_j, ⟨⟩⟩ m2 ⟨mrk2, tmp2, tc2, tl2, hm2l, ht2l, h12, hmv2, hpos2, heq2, hlow2,
          hcov2, hent2, hm2'⟩
        wp_unfold
        exact ih (idx - 1) _ _ (by omega)
          ⟨idx - 1, mrk2, tmp2, tc2, tl2, by omega, rfl, rfl, hm2l, ht2l, h12, hmv2, hpos2, heq2,
            hlow2, hcov2, hent2, hm2'⟩
      · intro J hJ; wp_unfold
        have hskip_step :
            ¬ (mrk_l[pv]?.getD 0#8 ≠ 0#8 ∧ (s.lvl[pv]?.getD 0#32).toNat = s.cur_level) →
            J (0xFFFFFFFF#32, ()) ml := fun hnot => by
          have hnot' : ¬ (mrk_l[(s.trl[idx - 1]?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8 ∧
              (s.lvl[(s.trl[idx - 1]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = s.cur_level) := by
            simpa [hp_get] using hnot
          have hidx_eq : idx - 1 + 1 = idx := by omega
          have hct_same : curTrailIdxs s mrk_l idx = curTrailIdxs s mrk_l (idx - 1) := by
            rw [← hidx_eq]; exact curTrailIdxs_succ_false hnot'
          have hcl_same : curLits s mrk_l idx = curLits s mrk_l (idx - 1) := by
            rw [← hidx_eq]; exact curLits_succ_false hnot'
          refine hJ (0xFFFFFFFF#32, ()) ml ⟨mrk_l, tmp_l, tc_l, tl_l, hml_len, htl_len, htl1,
            htl_mv, htc_pos, by rw [← hct_same]; exact htc_eq, hlow_l, hcov_l, ?_, hml⟩
          unfold activeResolvent at hent_l ⊢; rwa [hcl_same] at hent_l
        rw [hpv_eq]
        refine ⟨_, load_arena_mrk (s := sl) (i := pv)
          (by dsimp [sl]; rw [hml_len]; exact hpv_lt) hml, ?_⟩
        rw [show ((0 : BitVec 32).setWidth 8).setWidth 32 = 0#32 from rfl, bv8_zext32_eq_zero]
        have hmrk_pv : mrk_l[pv]'(by rw [hml_len]; exact hpv_lt) = mrk_l[pv]?.getD 0#8 := by
          rw [List.getElem?_eq_getElem (by rw [hml_len]; exact hpv_lt), Option.getD_some]
        rw [hmrk_pv]
        refine ⟨fun hmnz => ?_, fun hm0 => hskip_step (fun h => h.1 hm0)⟩
        rw [bv64_mul4_nat]
        refine ⟨_, load_arena_lvl (s := sl) (i := pv)
          (by dsimp [sl]; rw [hlen.lvl_len]; exact hpv_lt) hml, ?_⟩
        generalize hpl_def : s.lvl[pv]'(by rw [hlen.lvl_len]; exact hpv_lt) = pl_bv
        have hpl_eq : pl_bv.toNat = (s.lvl[pv]?.getD 0#32).toNat := by
          rw [List.getElem?_eq_getElem (by rw [hlen.lvl_len]; exact hpv_lt), Option.getD_some,
            hpl_def]
        rw [bv64_trunc32_ofNat hlen.cur_level_lt]
        have hpl_iff : (pl_bv = BitVec.ofNat 32 s.cur_level) ↔
            (s.lvl[pv]?.getD 0#32).toNat = s.cur_level := by
          constructor
          · intro h; rw [← hpl_eq, h, bv32_ofNat_toNat hlen.cur_level_lt]
          · intro h; apply BitVec.eq_of_toNat_eq
            rw [hpl_eq, h, bv32_ofNat_toNat hlen.cur_level_lt]
        rw [hpl_iff]
        refine ⟨fun hpl_cl => ?_, fun hpl_ne => hskip_step (fun h => hpl_ne h.2)⟩
        -- Both `mrk[pv] ≠ 0` and `lvl[pv] == cur_lvl`!
        have hidx_eq : idx - 1 + 1 = idx := by omega
        have hmnz' : mrk_l[(s.trl[idx - 1]?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8 := by
          simpa [hp_get] using hmnz
        have hpl_cl' : (s.lvl[(s.trl[idx - 1]?.getD 0#32).toNat / 2]?.getD 0#32).toNat =
            s.cur_level := by simpa [hp_get] using hpl_cl
        have hct_succ : curTrailIdxs s mrk_l idx = curTrailIdxs s mrk_l (idx - 1) ++ [idx - 1] := by
          rw [← hidx_eq]; exact curTrailIdxs_succ_true hmnz' hpl_cl'
        have hcl_succ : curLits s mrk_l idx =
            curLits s mrk_l (idx - 1) ++ [p_bv.toNat ^^^ 1] := by
          rw [← hidx_eq, ← hp_get]; exact curLits_succ_true hmnz' hpl_cl'
        have htc_sub : tc_l - 1 = (curTrailIdxs s mrk_l (idx - 1)).length := by
          rw [htc_eq, hct_succ, List.length_append, List.length_singleton]; omega
        -- h->tmp_cnt = h->tmp_cnt - 1ULL;
        refine ⟨_, load_arena_tmp_cnt (s := sl) hml, ?_⟩
        dsimp only [sl]
        rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl,
          bv_sub_ofNat (by omega) (by omega)]
        obtain ⟨ok_tc, hmtc⟩ := store_arena_tmp_cnt (s := sl) (tc_l - 1) hml
        let sl1 : ArenaState :=
          { s with mrk := mrk_l, tmp := tmp_l, tmp_cnt := tc_l - 1, tmp_len := tl_l }
        refine ⟨ok_tc, _, load_arena_tmp_cnt (s := sl1) hmtc, ?_⟩
        dsimp only [sl1]
        rw [bv_eq_zero_iff (by omega)]
        refine ⟨fun htc_hit0 => ?_, fun htc_gt0 => ?_⟩
        · -- Found 1UIP! Break!
          have htc_is1 : tc_l - 1 = 0 := htc_hit0
          have hct_nil : curTrailIdxs s mrk_l (idx - 1) = [] :=
            List.eq_nil_of_length_eq_zero (by omega)
          have hcl_nil : curLits s mrk_l (idx - 1) = [] := by unfold curLits; simp [hct_nil]
          have hent_uip :
              F0.EntailsClause (cnfClause ((p_bv ^^^ 1#32).toNat :: lowerLits tmp_l tl_l)) := by
            unfold activeResolvent at hent_l
            rw [hcl_succ, hcl_nil, List.nil_append] at hent_l
            refine entails_of_mem_or_false hent_l fun l hl => Or.inl ?_
            rcases List.mem_append.mp hl with h1 | h2
            · exact List.mem_cons_of_mem _ h1
            · simp only [List.mem_singleton] at h2
              rw [h2, ← bv32_xor_1]; exact List.mem_cons_self
          let sb' : ArenaState :=
            { s with mrk := mrk_l, tmp := tmp_l, tmp_cnt := 0, tmp_len := tl_l }
          have hm_b : (ArenaMem c sb' ⋆ R)
              (storeMem ml i64 (c.hdr + 184) (BitVec.ofNat 64 (tc_l - 1))) := by
            simpa [sb', sl, htc_is1] using hmtc
          have hp_some : s.trl[idx - 1]? = some p_bv := by
            rw [List.getElem?_eq_getElem hi_trl, hp_def]
          exact hB _ _ ⟨idx - 1, mrk_l, tmp_l, tl_l, p_bv, by omega, rfl, hp_some, rfl,
            hpl_cl, hml_len, htl_len, htl1, htl_mv, by omega, hlow_l, hcov_l, hent_uip, hm_b⟩
        · -- Resolve with reason clause `rsns[pv]`
          have hsl1_len : sl1.LengthsOk c :=
            same_core_lengths hlen hml_len htl_len (by omega) (by omega)
          refine ⟨_, load_arena_rsns (s := sl1) (i := pv)
            (by dsimp [sl1]; rw [hlen.rsns_len]; exact hpv_lt) hmtc, ?_⟩
          generalize hrc_def : s.rsns[pv]'(by rw [hlen.rsns_len]; exact hpv_lt) = rcid_bv
          have hrc_get : s.rsns[(s.trl[idx - 1]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 =
              rcid_bv := by
            rw [hp_get, List.getElem?_eq_getElem (by rw [hlen.rsns_len]; exact hpv_lt),
              Option.getD_some, hrc_def]
          refine wp_join_group
            (fun () m_fail => ∃ sf, sf.LengthsOk c ∧ sf.tmp_len ≤ c.mv ∧
              sf.d_cur = s.d_cur ∧ sf.d_val = s.d_val ∧ sf.fuel = s.fuel ∧
              (ArenaMem c sf ⋆ R) m_fail)
            ?_ ?_
          · rintro _ ⟨⟩ m_fail ⟨sf, hsfl, hsfmv, hd1, hd2, hfu, hmf⟩
            wp_unfold
            exact hfail_cm sf m_fail hsfl hsfmv hd1 hd2 hfu hmf
          · intro Jf hJf; wp_unfold
            refine ⟨fun _ => hJf () _ ⟨sl1, hsl1_len, htl_mv, rfl, rfl, rfl, hmtc⟩,
              fun hrc_ne => ?_⟩
            have hrc_ne' : s.rsns[(s.trl[idx - 1]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 ≠
                0xFFFFFFFF#32 := by rwa [hrc_get]
            obtain ⟨hrc_lt, hrc_inv⟩ := hcore.reason_inv (idx - 1) (by omega) hrc_ne'
            rw [hrc_get] at hrc_lt hrc_inv
            rw [hp_get] at hrc_inv
            apply wp_call_of_spec; apply hAc
            refine ⟨c, sl1, R, rfl, hsl1_len, htl_mv, by dsimp [sl1]; omega, hmtc, ?_⟩
            intro ok2 mrk2 tmp2 tc2 tl2 m2 s3_ac hs3_len htl2_ge htl2_le htc2_ge hmp2 htp2 hnm2
              hnt2 hcnt2 hall2 hm2
            dsimp only [s3_ac, sl1] at hs3_len htl2_ge htc2_ge hmp2 htp2 hnm2 hnt2 hcnt2 hall2 hm2
            clear s3_ac
            wp_unfold
            simp only [Arg.val_var] at *
            cases ok2 with
            | false =>
              wp_unfold
              exact hJf () m2 ⟨{ s with mrk := mrk2, tmp := tmp2, tmp_cnt := tc2, tmp_len := tl2 },
                hs3_len, htl2_le, rfl, rfl, rfl, hm2⟩
            | true =>
              wp_unfold
              have hpv_tr : (p_bv >>> 1).toNat = pv := bv32_lshr_1 p_bv
              have hclause_r : ∀ q ∈ clauseLits s rcid_bv.toNat,
                  q / 2 = pv ∨ ∃ k < idx - 1, (s.trl[k]?.getD 0#32).toNat = q ^^^ 1 :=
                fun q hq => (hrc_inv q hq).elim (fun he => Or.inl (by rw [he])) Or.inr
              have hnm2' := hpv_tr ▸ hnm2; have hnt2' := hpv_tr ▸ hnt2
              have hall2' := hpv_tr ▸ (hall2 rfl).2.2
              obtain ⟨htc2_eq, hlow2, hcov2, hlow_sub, hcur_sub, hq2⟩ :=
                analyzeClause_preserves hcore (by omega) htl1 htl2_ge htl2_le
                  hml_len htl_len hs3_len.mrk_len hs3_len.tmp_len_arr
                  htc_sub htc2_ge hlow_l hcov_l hrc_lt hclause_r
                  hmp2 htp2 hnm2' hnt2' hcnt2 hall2'
              have hent2 : F0.EntailsClause
                  (cnfClause (activeResolvent s tmp2 mrk2 tl2 (idx - 1))) := by
                refine entails_resolve_to (p := p_bv.toNat)
                  (hcore.clauses.entails rcid_bv.toNat hrc_lt) hent_l ?_ ?_
                · intro q hq
                  rcases hq2 q hq with hv_eq | hmem | hf
                  · rcases hrc_inv q hq with rfl | ⟨k, hk, hkeq⟩
                    · exact Or.inl rfl
                    · exfalso
                      have hk_eq := hcore.trail_vars_nodup k (idx - 1) (by omega) (by omega)
                        (by rw [hkeq, hp_get]; exact (litVar_litNeg q).trans hv_eq)
                      omega
                  · exact Or.inr (Or.inl hmem)
                  · exact Or.inr (Or.inr hf)
                · intro l hl
                  unfold activeResolvent at hl
                  rcases List.mem_append.mp hl with hl1 | hl2
                  · exact Or.inr (Or.inl (List.mem_append_left _ (hlow_sub l hl1)))
                  · rw [hcl_succ] at hl2
                    rcases List.mem_append.mp hl2 with hl2a | hl2b
                    · exact Or.inr (Or.inl (List.mem_append_right _ (hcur_sub l hl2a)))
                    · simp only [List.mem_singleton] at hl2b; exact Or.inl hl2b
              exact hJ (0xFFFFFFFF#32, ()) m2 ⟨mrk2, tmp2, tc2, tl2, hs3_len.mrk_len,
                hs3_len.tmp_len_arr, by omega, htl2_le, by omega, htc2_eq, hlow2, hcov2,
                hent2, hm2⟩
    · -- Entry into 1UIP loop
      intro B L _ hL; wp_unfold
      exact hL s.trail_end _ m3 ⟨s.trail_end, mrk1, tmp1, tc1, tl1, Nat.le_refl _, rfl, rfl,
        hs2_len.mrk_len, hs2_len.tmp_len_arr, htl1_ge, htl1_le, by omega, htc1_eq, hlow1, hcov1,
        hent1, hm3⟩

end LeanQbe.T.Examples.Kissat
