module

public import LeanQbe.T.Examples.Kissat.SolverArena
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat C0 `SolverInv` and Core Helper `Func.wp` Proofs (`X1` Stage B2)

Builds on `SolverArena` to define:
1. Clause-slice projections (`clauseOff`, `clauseSize`, `clauseLits`) and the inductive solver
   invariant (`ClausesInv`, `SolverCoreInv`, `MarksClear`, `SolverInv`).
2. Preservation lemmas (`assign_preserves_core`, `addClause_preserves_core`,
   `swapClause_preserves_core`).
3. `Func.wp` specifications and proofs for the 5 low-level solver helpers:
   `kissat_assign`, `kissat_add_watch`, `kissat_add_clause`, `kissat_backtrack`, and
   `kissat_zero_tables`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open Kraken.Bedrock2.Test

/-! ## 1. Clause projections and inductive solver invariant (`SolverInv`) -/

/-- Starting offset in `s.lpool` of clause `cid`. -/
def clauseOff (s : ArenaState) (cid : Nat) : Nat :=
  (s.cls[4 * cid]?.getD 0#32).toNat

/-- Literal count of clause `cid`. -/
def clauseSize (s : ArenaState) (cid : Nat) : Nat :=
  (s.cls[4 * cid + 1]?.getD 0#32).toNat

/-- Literal list of clause `cid` as 0-based Kissat `Nat` literals. -/
def clauseLits (s : ArenaState) (cid : Nat) : List Nat :=
  ((s.lpool.drop (clauseOff s cid)).take (clauseSize s cid)).map BitVec.toNat

theorem mem_clauseLits_iff {s : ArenaState} {cid l : Nat}
    (h : clauseOff s cid + clauseSize s cid ≤ s.lpool.length) :
    l ∈ clauseLits s cid ↔
      ∃ (k : Nat) (_hk : k < clauseSize s cid),
        (s.lpool[clauseOff s cid + k]'(by omega)).toNat = l := by
  unfold clauseLits
  rw [List.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨k, hk, hget⟩ := List.mem_iff_getElem.mp hx
    have hk' : k < clauseSize s cid := by
      rw [List.length_take, List.length_drop] at hk; omega
    refine ⟨k, hk', ?_⟩
    rw [List.getElem_take, List.getElem_drop] at hget
    exact congrArg BitVec.toNat hget
  · rintro ⟨k, hk, hget⟩
    refine ⟨s.lpool[clauseOff s cid + k]'(by omega), ?_, hget⟩
    have hlt : k < ((s.lpool.drop (clauseOff s cid)).take (clauseSize s cid)).length := by
      rw [List.length_take, List.length_drop]; omega
    have hmem := List.getElem_mem hlt
    simpa [List.getElem_take, List.getElem_drop] using hmem

/-- Clause-database invariant (`ClausesInv`): ordered disjoint slices in `0..s.lit_len`,
size `≥ 2`, literals `< 2*mv`, semantically entailed by `F0`. -/
structure ClausesInv (c : ArenaCfg) (F0 : CNF Nat) (s : ArenaState) : Prop where
  bounds : ∀ cid < s.num_clauses,
    2 ≤ clauseSize s cid ∧ clauseOff s cid + clauseSize s cid ≤ s.lit_len
  disjoint : ∀ cid1 cid2, cid1 < cid2 → cid2 < s.num_clauses →
    clauseOff s cid1 + clauseSize s cid1 ≤ clauseOff s cid2
  lits_lt : ∀ cid < s.num_clauses, ∀ l ∈ clauseLits s cid, l < 2 * c.mv
  entails : ∀ cid < s.num_clauses, F0.EntailsClause (cnfClause (clauseLits s cid))

/-- Mark-agnostic core CDCL solver invariant. -/
structure SolverCoreInv (c : ArenaCfg) (F0 : CNF Nat) (s : ArenaState) : Prop where
  lengths : s.LengthsOk c
  clauses : ClausesInv c F0 s
  cur_level_le : s.cur_level ≤ s.trail_end
  trail_lits_lt : ∀ i < s.trail_end, (s.trl[i]?.getD 0#32).toNat < 2 * c.mv
  trail_vars_nodup : ∀ i j, i < s.trail_end → j < s.trail_end →
    (s.trl[i]?.getD 0#32).toNat / 2 = (s.trl[j]?.getD 0#32).toNat / 2 → i = j
  vals_domain : ∀ l < 2 * c.mv,
    s.vals[l]?.getD 0#8 = 0#8 ∨ s.vals[l]?.getD 0#8 = 1#8 ∨ s.vals[l]?.getD 0#8 = 0xFF#8
  vals_true_iff : ∀ l < 2 * c.mv,
    s.vals[l]?.getD 0#8 = 1#8 ↔ ∃ i < s.trail_end, (s.trl[i]?.getD 0#32).toNat = l
  vals_false_iff : ∀ l < 2 * c.mv,
    s.vals[l]?.getD 0#8 = 0xFF#8 ↔ ∃ i < s.trail_end, (s.trl[i]?.getD 0#32).toNat = l ^^^ 1
  lvl_le : ∀ i < s.trail_end,
    (s.lvl[(s.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ s.cur_level
  trail_mono : ∀ i j, i ≤ j → j < s.trail_end →
    (s.lvl[(s.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
    (s.lvl[(s.trl[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
  levels_inhabited : ∀ L, 1 ≤ L → L ≤ s.cur_level →
    ∃ i < s.trail_end, (s.lvl[(s.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = L
  level0_sound : ∀ i < s.trail_end,
    (s.lvl[(s.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 →
    F0.EntailsClause (cnfClause [(s.trl[i]?.getD 0#32).toNat])
  reason_inv : ∀ idx < s.trail_end,
    let p := (s.trl[idx]?.getD 0#32).toNat
    let rsn := s.rsns[p / 2]?.getD 0xFFFFFFFF#32
    rsn ≠ 0xFFFFFFFF#32 →
      rsn.toNat < s.num_clauses ∧
      ∀ q ∈ clauseLits s rsn.toNat,
        q = p ∨ ∃ k < idx, (s.trl[k]?.getD 0#32).toNat = q ^^^ 1

/-- All entries of `s.mrk` are zero. -/
def MarksClear (c : ArenaCfg) (s : ArenaState) : Prop :=
  ∀ v < c.mv, s.mrk[v]?.getD 0#8 = 0#8

/-- Full CDCL solver invariant (`SolverCoreInv` + `MarksClear`). -/
structure SolverInv (c : ArenaCfg) (F0 : CNF Nat) (s : ArenaState) : Prop where
  core : SolverCoreInv c F0 s
  marks : MarksClear c s

theorem SolverCoreInv.mono {c : ArenaCfg} {F0 F1 : CNF Nat} {s : ArenaState}
    (hF : F1.Entails F0) (h : SolverCoreInv c F0 s) : SolverCoreInv c F1 s :=
  { h with
    clauses := { h.clauses with
      entails := fun cid hcid => CNF.entails_clause_trans hF (h.clauses.entails cid hcid) }
    level0_sound := fun i hi hl0 => CNF.entails_clause_trans hF (h.level0_sound i hi hl0) }

theorem SolverInv.mono {c : ArenaCfg} {F0 F1 : CNF Nat} {s : ArenaState}
    (hF : F1.Entails F0) (h : SolverInv c F0 s) : SolverInv c F1 s :=
  ⟨h.core.mono hF, h.marks⟩

theorem SolverCoreInv.vals_zero_iff {c : ArenaCfg} {F0 : CNF Nat} {s : ArenaState}
    (h : SolverCoreInv c F0 s) {l : Nat} (hl : l < 2 * c.mv) :
    s.vals[l]?.getD 0#8 = 0#8 ↔ ∀ i < s.trail_end, (s.trl[i]?.getD 0#32).toNat / 2 ≠ l / 2 := by
  constructor
  · intro hz i hi hvar
    have hcases := (litVar_eq_iff _ l).mp hvar
    rcases hcases with h1 | h2
    · have ht := (h.vals_true_iff l hl).mpr ⟨i, hi, h1⟩; rw [hz] at ht; cases ht
    · have hf := (h.vals_false_iff l hl).mpr ⟨i, hi, h2⟩; rw [hz] at hf; cases hf
  · intro hnone
    rcases h.vals_domain l hl with h0 | h1 | h2
    · exact h0
    · obtain ⟨i, hi, heq⟩ := (h.vals_true_iff l hl).mp h1
      exact absurd (by rw [heq]) (hnone i hi)
    · obtain ⟨i, hi, heq⟩ := (h.vals_false_iff l hl).mp h2
      have hvar : (l ^^^ 1) / 2 = l / 2 := litVar_litNeg l
      exact absurd (by rw [heq, hvar]) (hnone i hi)

theorem SolverCoreInv.trail_end_lt_of_unassigned {c : ArenaCfg} {F0 : CNF Nat} {s : ArenaState}
    (h : SolverCoreInv c F0 s) {l : Nat} (hl : l < 2 * c.mv)
    (hun : s.vals[l]?.getD 0#8 = 0#8) : s.trail_end < c.mv := by
  have hmiss := (h.vals_zero_iff hl).mp hun
  exact inj_lt_of_missing (fun i => (s.trl[i]?.getD 0#32).toNat / 2)
    (fun i j hi hj heq => h.trail_vars_nodup i j hi hj heq)
    (fun i hi => by have := h.trail_lits_lt i hi; omega)
    (by omega : l / 2 < c.mv) hmiss

theorem SolverCoreInv.level0_unsat_of_conflict {c : ArenaCfg} {F0 : CNF Nat} {s : ArenaState}
    (h : SolverCoreInv c F0 s) (hl0 : s.cur_level = 0) {cid : Nat} (hcid : cid < s.num_clauses)
    (hfals : ∀ l ∈ clauseLits s cid, s.vals[l]?.getD 0#8 = 0xFF#8) : F0.Unsat := by
  have hent := h.clauses.entails cid hcid
  have hnil : F0.EntailsClause (cnfClause []) := by
    refine entails_of_mem_or_false hent fun l hl => Or.inr ?_
    have hlt := h.clauses.lits_lt cid hcid l hl
    obtain ⟨i, hi, hieq⟩ := (h.vals_false_iff l hlt).mp (hfals l hl)
    have hli : (s.lvl[(s.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by
      have := h.lvl_le i hi; omega
    have hs := h.level0_sound i hi hli
    rwa [hieq] at hs
  exact unsat_of_entails_nil hnil

theorem SolverCoreInv.falsified_lit_unique {c : ArenaCfg} {F0 : CNF Nat} {s : ArenaState}
    (h : SolverCoreInv c F0 s) {l1 l2 : Nat} (hl1 : l1 < 2 * c.mv) (hl2 : l2 < 2 * c.mv)
    (hv : l1 / 2 = l2 / 2) (hf1 : s.vals[l1]?.getD 0#8 = 0xFF#8)
    (hf2 : s.vals[l2]?.getD 0#8 = 0xFF#8) : l1 = l2 := by
  obtain ⟨i1, hi1, he1⟩ := (h.vals_false_iff l1 hl1).mp hf1
  obtain ⟨i2, hi2, he2⟩ := (h.vals_false_iff l2 hl2).mp hf2
  have hi : i1 = i2 := h.trail_vars_nodup i1 i2 hi1 hi2 (by
    rw [he1, he2]
    have h1 := litVar_litNeg l1; have h2 := litVar_litNeg l2
    unfold litVar litNeg at h1 h2; omega)
  subst hi
  have hx : litNeg l1 = litNeg l2 := he1.symm.trans he2
  have := congrArg litNeg hx
  simpa using this

/-! ## 2. Invariant preservation helpers (`assign`, `addClause`, `swapClause`) -/

/-- Pushing an unassigned literal onto the trail preserves `SolverCoreInv`. -/
theorem assign_preserves_core {c : ArenaCfg} {F0 : CNF Nat} {s : ArenaState}
    (hinv : SolverCoreInv c F0 s) {lit rsn : BitVec 32}
    (hlit : lit.toNat < 2 * c.mv)
    (hun : s.vals[lit.toNat]?.getD 0#8 = 0#8)
    (hcur_le : s.cur_level ≤ s.trail_end + 1)
    (hinhab : ∀ L, 1 ≤ L → L ≤ s.cur_level →
      L = s.cur_level ∨
        ∃ i < s.trail_end, (s.lvl[(s.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = L)
    (hl0 : s.cur_level = 0 → F0.EntailsClause (cnfClause [lit.toNat]))
    (hrsn : rsn ≠ 0xFFFFFFFF#32 →
      rsn.toNat < s.num_clauses ∧
      ∀ q ∈ clauseLits s rsn.toNat,
        q = lit.toNat ∨ ∃ k < s.trail_end, (s.trl[k]?.getD 0#32).toNat = q ^^^ 1) :
    let v := lit.toNat / 2
    let s' : ArenaState :=
      { s with
        vals := (s.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8
        lvl := s.lvl.set v (BitVec.ofNat 32 s.cur_level)
        rsns := s.rsns.set v rsn
        trl := s.trl.set s.trail_end lit
        trail_end := s.trail_end + 1 }
    SolverCoreInv c F0 s' := by
  intro v s'
  have hte_lt : s.trail_end < c.mv := hinv.trail_end_lt_of_unassigned hlit hun
  have hnot_var : ∀ i < s.trail_end, (s.trl[i]?.getD 0#32).toNat / 2 ≠ v :=
    (hinv.vals_zero_iff hlit).mp hun
  have hnlit_lt : (lit.toNat ^^^ 1) < 2 * c.mv := litNeg_lt_two_mul hlit
  have hne_lit : lit.toNat ^^^ 1 ≠ lit.toNat := litNeg_ne_self lit.toNat
  have hlen := hinv.lengths
  have hcur_lt32 : s.cur_level < 2 ^ 32 := hlen.cur_level_lt
  have htrl_get : ∀ i < s.trail_end + 1,
      (s'.trl[i]?.getD 0#32).toNat =
        if i = s.trail_end then lit.toNat else (s.trl[i]?.getD 0#32).toNat := by
    intro i hi
    by_cases he : i = s.trail_end
    · subst he; simp [s', List.getElem?_set_self (by rw [hlen.trl_len]; omega)]
    · simp [s', he, List.getElem?_set_ne (Ne.symm he)]
  have hlvl_get : ∀ w < c.mv,
      (s'.lvl[w]?.getD 0#32).toNat =
        if w = v then s.cur_level else (s.lvl[w]?.getD 0#32).toNat := by
    intro w hw
    by_cases he : w = v
    · subst he
      simp [s', List.getElem?_set_self (by rw [hlen.lvl_len]; omega), bv32_ofNat_toNat hcur_lt32]
    · simp [s', he, List.getElem?_set_ne (Ne.symm he)]
  have hvals_get : ∀ l < 2 * c.mv,
      s'.vals[l]?.getD 0#8 =
        if l = lit.toNat ^^^ 1 then 0xFF#8
        else if l = lit.toNat then 1#8
        else s.vals[l]?.getD 0#8 := by
    intro l hl
    by_cases h1 : l = lit.toNat ^^^ 1
    · subst h1
      dsimp only [s']
      simp only [↓reduceIte]
      rw [List.getElem?_set_self (by simp [hlen.vals_len]; exact hnlit_lt)]
      rfl
    · dsimp only [s']
      simp only [h1, ↓reduceIte]
      rw [List.getElem?_set_ne (Ne.symm h1)]
      by_cases h2 : l = lit.toNat
      · subst h2
        simp only [↓reduceIte]
        rw [List.getElem?_set_self (by rw [hlen.vals_len]; exact hlit)]
        rfl
      · simp only [h2, ↓reduceIte]
        rw [List.getElem?_set_ne (Ne.symm h2)]
  have hpr_le : s.propagated ≤ s.trail_end := hlen.propagated_le
  have hs'_te : s'.trail_end = s.trail_end + 1 := rfl
  have hs'_pr : s'.propagated = s.propagated := rfl
  have hs'_cl : s'.cur_level = s.cur_level := rfl
  have hs'_nc : s'.num_clauses = s.num_clauses := rfl
  have hs'_cls : s'.cls = s.cls := rfl
  have hs'_lp : s'.lpool = s.lpool := rfl
  refine ⟨⟨by simp [s', hlen.vals_len], hlen.mrk_len, by simp [s', hlen.lvl_len],
      by simp [s', hlen.rsns_len], by simp [s', hlen.trl_len], hlen.tmp_len_arr, hlen.wh_len,
      hlen.cls_len, hlen.wn_len, hlen.lpool_len, hlen.lit_len_le, hlen.num_clauses_le,
      by omega, by omega, hlen.cur_level_lt, hlen.tmp_cnt_lt, hlen.tmp_len_lt⟩,
    ⟨hinv.clauses.bounds, hinv.clauses.disjoint, hinv.clauses.lits_lt, hinv.clauses.entails⟩,
    by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi; rw [hs'_te] at hi; rw [htrl_get i hi]; split
    · exact hlit
    · exact hinv.trail_lits_lt i (by omega)
  · intro i j hi hj hveq
    rw [hs'_te] at hi hj
    rw [htrl_get i hi, htrl_get j hj] at hveq
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
      · simp only [hie, ↓reduceIte] at heq; subst heq
        simp [Ne.symm hne_lit]
      · simp only [hie, ↓reduceIte] at heq
        have hlv : l / 2 ≠ v := by rw [← heq]; exact hnot_var i (by omega)
        have h1 : l ≠ lit.toNat ^^^ 1 := fun h => hlv (by rw [h]; exact litVar_litNeg _)
        have h2 : l ≠ lit.toNat := fun h => hlv (by rw [h])
        simp only [h1, h2, ↓reduceIte]
        exact (hinv.vals_true_iff l hl).mpr ⟨i, by omega, heq⟩
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
          have h1 : (l ^^^ 1) / 2 = l / 2 := litVar_litNeg l
          rwa [h1] at h
        have h1 : l ≠ lit.toNat ^^^ 1 := fun h => hlv (by rw [h]; exact litVar_litNeg _)
        have h2 : l ≠ lit.toNat := fun h => hlv (by rw [h])
        simp only [h1, h2, ↓reduceIte]
        exact (hinv.vals_false_iff l hl).mpr ⟨i, by omega, heq⟩
  · intro i hi; rw [hs'_te] at hi; rw [hs'_cl]
    rw [htrl_get i hi]
    by_cases hie : i = s.trail_end
    · simp only [hie, ↓reduceIte]; rw [hlvl_get v (by omega)]; simp
    · simp only [hie, ↓reduceIte]
      have hilt : i < s.trail_end := by omega
      rw [hlvl_get _ (by have := hinv.trail_lits_lt i hilt; omega)]
      simp only [hnot_var i hilt, ↓reduceIte]; exact hinv.lvl_le i hilt
  · intro i j hij hj; rw [hs'_te] at hj
    rw [htrl_get i (by omega), htrl_get j hj]
    by_cases hje : j = s.trail_end
    · simp only [hje, ↓reduceIte]; rw [hlvl_get v (by omega)]; simp only [↓reduceIte]
      by_cases hie : i = s.trail_end
      · simp only [hie, ↓reduceIte]; rw [hlvl_get v (by omega)]; simp
      · simp only [hie, ↓reduceIte]
        have hilt : i < s.trail_end := by omega
        rw [hlvl_get _ (by have := hinv.trail_lits_lt i hilt; omega)]
        simp only [hnot_var i hilt, ↓reduceIte]; exact hinv.lvl_le i hilt
    · have hjlt : j < s.trail_end := by omega
      have hilt : i < s.trail_end := by omega
      simp only [show i ≠ s.trail_end by omega, hje, ↓reduceIte]
      rw [hlvl_get _ (by have := hinv.trail_lits_lt i hilt; omega),
        hlvl_get _ (by have := hinv.trail_lits_lt j hjlt; omega)]
      simp only [hnot_var i hilt, hnot_var j hjlt, ↓reduceIte]
      exact hinv.trail_mono i j hij hjlt
  · intro L hL1 hLle; rw [hs'_cl] at hLle; rw [hs'_te]
    rcases hinhab L hL1 hLle with rfl | ⟨i, hi, hli⟩
    · refine ⟨s.trail_end, by omega, ?_⟩
      rw [htrl_get _ (by omega)]; simp only [↓reduceIte]; rw [hlvl_get v (by omega)]; simp
    · refine ⟨i, by omega, ?_⟩
      rw [htrl_get i (by omega)]; simp only [show i ≠ s.trail_end by omega, ↓reduceIte]
      rw [hlvl_get _ (by have := hinv.trail_lits_lt i hi; omega)]
      simp [hnot_var i hi, hli]
  · intro i hi hli; rw [hs'_te] at hi
    rw [htrl_get i hi] at hli ⊢
    by_cases hie : i = s.trail_end
    · simp only [hie, ↓reduceIte] at hli ⊢
      rw [hlvl_get v (by omega)] at hli; simp only [↓reduceIte] at hli
      exact hl0 hli
    · simp only [hie, ↓reduceIte] at hli ⊢
      have hilt : i < s.trail_end := by omega
      rw [hlvl_get _ (by have := hinv.trail_lits_lt i hilt; omega)] at hli
      simp only [hnot_var i hilt, ↓reduceIte] at hli
      exact hinv.level0_sound i hilt hli
  · intro idx hidx; rw [hs'_te] at hidx
    dsimp only
    rw [htrl_get idx hidx]
    by_cases hie : idx = s.trail_end
    · simp only [hie, ↓reduceIte]
      have hr : s'.rsns[v]?.getD 0xFFFFFFFF#32 = rsn := by
        dsimp only [s']; rw [List.getElem?_set_self (by rw [hlen.rsns_len]; omega)]; rfl
      rw [hr]; intro hne
      obtain ⟨hrc, hall⟩ := hrsn hne
      refine ⟨by rw [hs'_nc]; exact hrc, fun q hq => ?_⟩
      have hq' : q ∈ clauseLits s rsn.toNat := by
        simpa [clauseLits, clauseOff, clauseSize, hs'_cls, hs'_lp] using hq
      exact (hall q hq').elim Or.inl fun ⟨k, hk, hkeq⟩ => Or.inr ⟨k, hk, by
        rw [htrl_get k (by omega)]; simp [show k ≠ s.trail_end by omega, hkeq]⟩
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

/-- Appending an entailed clause of length `≥ 2` (via `kissat_add_clause`) preserves
`SolverCoreInv`. -/
theorem addClause_preserves_core {c : ArenaCfg} {F0 : CNF Nat} {s s' : ArenaState} {len : Nat}
    (hinv : SolverCoreInv c F0 s) (hlen' : s'.LengthsOk c)
    (hge2 : 2 ≤ len)
    (hlits_lt : ∀ l ∈ (s.tmp.take len).map BitVec.toNat, l < 2 * c.mv)
    (hent : F0.EntailsClause (cnfClause ((s.tmp.take len).map BitVec.toNat)))
    (hll : s'.lit_len = s.lit_len + len)
    (hnc : s'.num_clauses = s.num_clauses + 1)
    (hte : s'.trail_end = s.trail_end) (hcl : s'.cur_level = s.cur_level)
    (hvals : s'.vals = s.vals) (hlvl : s'.lvl = s.lvl) (hrsns : s'.rsns = s.rsns)
    (htrl : s'.trl = s.trl)
    (hold_meta : ∀ cid < s.num_clauses,
      clauseOff s' cid = clauseOff s cid ∧ clauseSize s' cid = clauseSize s cid)
    (hold_lpool : ∀ k < s.lit_len, s'.lpool[k]? = s.lpool[k]?)
    (hoff_new : clauseOff s' s.num_clauses = s.lit_len)
    (hsz_new : clauseSize s' s.num_clauses = len)
    (hlits_new : clauseLits s' s.num_clauses = (s.tmp.take len).map BitVec.toNat) :
    SolverCoreInv c F0 s' := by
  have hold_lits : ∀ cid < s.num_clauses, clauseLits s' cid = clauseLits s cid := by
    intro cid hcid
    obtain ⟨ho, hs⟩ := hold_meta cid hcid
    have hbd := (hinv.clauses.bounds cid hcid).2
    have hl1 := hinv.lengths.lpool_len; have hl2 := hlen'.lpool_len
    have hll_le := hinv.lengths.lit_len_le
    unfold clauseLits; rw [ho, hs]
    apply List.ext_getElem
    · simp [hl1, hl2]
    · intro k hk1 _
      simp only [List.getElem_map, List.getElem_take, List.getElem_drop]
      have hklt : clauseOff s cid + k < s.lit_len := by
        simp only [List.length_map, List.length_take, List.length_drop, hl2] at hk1; omega
      have heq := hold_lpool (clauseOff s cid + k) hklt
      rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at heq
      exact congrArg BitVec.toNat (Option.some.inj heq)
  refine ⟨hlen', ⟨?_, ?_, ?_, ?_⟩,
    by rw [hcl, hte]; exact hinv.cur_level_le,
    by rw [hte, htrl]; exact hinv.trail_lits_lt,
    by rw [hte, htrl]; exact hinv.trail_vars_nodup,
    by rw [hvals]; exact hinv.vals_domain,
    by rw [hvals, hte, htrl]; exact hinv.vals_true_iff,
    by rw [hvals, hte, htrl]; exact hinv.vals_false_iff,
    by rw [hte, hcl, htrl, hlvl]; exact hinv.lvl_le,
    by rw [hte, htrl, hlvl]; exact hinv.trail_mono,
    by rw [hte, hcl, htrl, hlvl]; exact hinv.levels_inhabited,
    by rw [hte, htrl, hlvl]; exact hinv.level0_sound, ?_⟩
  · intro cid hcid
    rw [hnc] at hcid
    rcases Nat.lt_succ_iff_lt_or_eq.mp hcid with hlt | rfl
    · obtain ⟨ho, hs⟩ := hold_meta cid hlt
      have hbd := hinv.clauses.bounds cid hlt
      rw [ho, hs, hll]; omega
    · rw [hoff_new, hsz_new, hll]; omega
  · intro c1 c2 h12 h2
    rw [hnc] at h2
    rcases Nat.lt_succ_iff_lt_or_eq.mp h2 with h2lt | rfl
    · obtain ⟨ho1, hs1⟩ := hold_meta c1 (by omega)
      obtain ⟨ho2, _⟩ := hold_meta c2 h2lt
      rw [ho1, hs1, ho2]; exact hinv.clauses.disjoint c1 c2 h12 h2lt
    · obtain ⟨ho1, hs1⟩ := hold_meta c1 h12
      rw [ho1, hs1, hoff_new]; exact (hinv.clauses.bounds c1 h12).2
  · intro cid hcid
    rw [hnc] at hcid
    rcases Nat.lt_succ_iff_lt_or_eq.mp hcid with hlt | rfl
    · rw [hold_lits cid hlt]; exact hinv.clauses.lits_lt cid hlt
    · rw [hlits_new]; exact hlits_lt
  · intro cid hcid
    rw [hnc] at hcid
    rcases Nat.lt_succ_iff_lt_or_eq.mp hcid with hlt | rfl
    · rw [hold_lits cid hlt]; exact hinv.clauses.entails cid hlt
    · rw [hlits_new]; exact hent
  · intro idx hidx; dsimp only
    rw [hte] at hidx
    rw [htrl, hrsns, hnc]
    intro hne
    obtain ⟨hrc, hall⟩ := hinv.reason_inv idx hidx hne
    refine ⟨by omega, fun q hq => ?_⟩
    rw [hold_lits _ hrc] at hq
    exact hall q hq

/-- Swapping two literals inside clause `cid` (and optionally updating `searched`, `wh`, `wn`)
preserves `SolverCoreInv`. -/
theorem swapClause_preserves_core {c : ArenaCfg} {F0 : CNF Nat} {s : ArenaState}
    (hinv : SolverCoreInv c F0 s) {cid k1 k2 : Nat} {srch : BitVec 32}
    {wh' wn' : List (BitVec 32)}
    (hcid : cid < s.num_clauses)
    (hk1 : k1 < clauseSize s cid) (hk2 : k2 < clauseSize s cid)
    (hwl : wh'.length = 2 * c.mv) (hwnl : wn'.length = 2 * c.max_c) :
    let off := clauseOff s cid
    let hlen := hinv.lengths
    have hbd : off + clauseSize s cid ≤ s.lpool.length := by
      have := (hinv.clauses.bounds cid hcid).2; have := hlen.lit_len_le; have := hlen.lpool_len
      omega
    let l1 := s.lpool[off + k1]'(by omega)
    let l2 := s.lpool[off + k2]'(by omega)
    let s' : ArenaState :=
      { s with
        cls := s.cls.set (4 * cid + 2) srch
        lpool := (s.lpool.set (off + k1) l2).set (off + k2) l1
        wh := wh', wn := wn' }
    SolverCoreInv c F0 s' := by
  intro off hlen hbd l1 l2 s'
  have hmc := hlen.num_clauses_le
  have hoff_eq : ∀ id, clauseOff s' id = clauseOff s id := fun id => by
    unfold clauseOff s'
    rw [List.getElem?_set_ne (by omega : 4 * cid + 2 ≠ 4 * id)]
  have hsz_eq : ∀ id, clauseSize s' id = clauseSize s id := fun id => by
    unfold clauseSize s'
    rw [List.getElem?_set_ne (by omega : 4 * cid + 2 ≠ 4 * id + 1)]
  have hlen' : s'.LengthsOk c :=
    ⟨hlen.vals_len, hlen.mrk_len, hlen.lvl_len, hlen.rsns_len, hlen.trl_len, hlen.tmp_len_arr,
      hwl, by simp [s', hlen.cls_len], hwnl, by simp [s', hlen.lpool_len], hlen.lit_len_le,
      hlen.num_clauses_le, hlen.trail_end_le, hlen.propagated_le, hlen.cur_level_lt,
      hlen.tmp_cnt_lt, hlen.tmp_len_lt⟩
  have hmem_iff : ∀ id < s.num_clauses, ∀ l, l ∈ clauseLits s' id ↔ l ∈ clauseLits s id := by
    intro id hid l
    have hbd_id : clauseOff s id + clauseSize s id ≤ s.lpool.length := by
      have := (hinv.clauses.bounds id hid).2; have := hlen.lit_len_le; have := hlen.lpool_len
      omega
    have hbd_id' : clauseOff s' id + clauseSize s' id ≤ s'.lpool.length := by
      rw [hoff_eq, hsz_eq]; simp [s', hbd_id]
    rw [mem_clauseLits_iff hbd_id', mem_clauseLits_iff hbd_id]
    simp only [hoff_eq, hsz_eq]
    by_cases hid_eq : id = cid
    · subst hid_eq
      constructor
      · rintro ⟨k, hk, hget⟩
        by_cases hkk2 : k = k2
        · subst k
          have hv : s'.lpool[off + k2]'(by simp [s']; omega) = l1 := by
            dsimp only [s']; rw [List.getElem_set_self]
          exact ⟨k1, hk1, by rw [← hget]; exact congrArg BitVec.toNat hv.symm⟩
        · by_cases hkk1 : k = k1
          · subst k
            have hv : s'.lpool[off + k1]'(by simp [s']; omega) = l2 := by
              dsimp only [s']
              rw [List.getElem_set_ne (by omega : off + k2 ≠ off + k1), List.getElem_set_self]
            exact ⟨k2, hk2, by rw [← hget]; exact congrArg BitVec.toNat hv.symm⟩
          · have hv : s'.lpool[off + k]'(by simp [s']; omega) = s.lpool[off + k]'(by omega) := by
              dsimp only [s']
              rw [List.getElem_set_ne (by omega : off + k2 ≠ off + k),
                List.getElem_set_ne (by omega : off + k1 ≠ off + k)]
            exact ⟨k, hk, by rw [← hget]; exact congrArg BitVec.toNat hv.symm⟩
      · rintro ⟨k, hk, hget⟩
        by_cases hkk1 : k = k1
        · subst k
          refine ⟨k2, hk2, ?_⟩
          have hv : s'.lpool[off + k2]'(by simp [s']; omega) = l1 := by
            dsimp only [s']; rw [List.getElem_set_self]
          rw [hv]; exact hget
        · by_cases hkk2 : k = k2
          · subst k
            refine ⟨k1, hk1, ?_⟩
            have hv : s'.lpool[off + k1]'(by simp [s']; omega) = l2 := by
              dsimp only [s']
              rw [List.getElem_set_ne (by omega : off + k2 ≠ off + k1), List.getElem_set_self]
            rw [hv]; exact hget
          · refine ⟨k, hk, ?_⟩
            have hv : s'.lpool[off + k]'(by simp [s']; omega) = s.lpool[off + k]'(by omega) := by
              dsimp only [s']
              rw [List.getElem_set_ne (by omega : off + k2 ≠ off + k),
                List.getElem_set_ne (by omega : off + k1 ≠ off + k)]
            rw [hv]; exact hget
    · have hdisj : clauseOff s id + clauseSize s id ≤ off ∨
          off + clauseSize s cid ≤ clauseOff s id := by
        rcases Nat.lt_or_gt_of_ne hid_eq with hlt | hgt
        · exact Or.inl (hinv.clauses.disjoint id cid hlt hcid)
        · exact Or.inr (hinv.clauses.disjoint cid id hgt hid)
      have hget_eq : ∀ k (hk : k < clauseSize s id),
          s'.lpool[clauseOff s id + k]'(by simp [s']; omega) =
            s.lpool[clauseOff s id + k]'(by omega) := fun k hk => by
        have hne1 : off + k1 ≠ clauseOff s id + k := by omega
        have hne2 : off + k2 ≠ clauseOff s id + k := by omega
        simp [s', List.getElem_set_ne hne2, List.getElem_set_ne hne1]
      exact ⟨fun ⟨k, hk, h⟩ => ⟨k, hk, by rw [← hget_eq k hk]; exact h⟩,
        fun ⟨k, hk, h⟩ => ⟨k, hk, by rw [hget_eq k hk]; exact h⟩⟩
  refine ⟨hlen', ⟨fun id hid => by rw [hoff_eq, hsz_eq]; exact hinv.clauses.bounds id hid,
      fun c1 c2 h12 h2 => by
        rw [hoff_eq, hsz_eq, hoff_eq]; exact hinv.clauses.disjoint c1 c2 h12 h2,
      fun id hid l hl => hinv.clauses.lits_lt id hid l ((hmem_iff id hid l).mp hl),
      fun id hid => entails_of_mem_or_false (hinv.clauses.entails id hid) fun l hl =>
        Or.inl ((hmem_iff id hid l).mpr hl)⟩,
    hinv.cur_level_le, hinv.trail_lits_lt, hinv.trail_vars_nodup, hinv.vals_domain,
    hinv.vals_true_iff, hinv.vals_false_iff, hinv.lvl_le, hinv.trail_mono,
    hinv.levels_inhabited, hinv.level0_sound, ?_⟩
  intro idx hidx; dsimp only; intro hne
  obtain ⟨hrc, hall⟩ := hinv.reason_inv idx hidx hne
  exact ⟨hrc, fun q hq => hall q ((hmem_iff _ hrc q).mp hq)⟩

/-! ## 3. Specifications and `Func.wp` proofs for the 5 low-level helpers -/

/-- Specification of `kissat_assign(h, lit, rsn)`. -/
def kissatAssignSpec : Spec [i64, i32, i32] [] := fun (h, lit, rsn, ()) m Q _ =>
  ∃ (c : ArenaCfg) (s : ArenaState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (ArenaMem c s ⋆ R) m ∧
    if c.mv ≤ lit.toNat / 2 ∨ c.mv ≤ s.trail_end then
      Q () m
    else
      let v := lit.toNat / 2
      let s' : ArenaState :=
        { s with
          vals := (s.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8
          lvl := s.lvl.set v (BitVec.ofNat 32 s.cur_level)
          rsns := s.rsns.set v rsn
          trl := s.trl.set s.trail_end lit
          trail_end := s.trail_end + 1 }
      ∀ m', s'.LengthsOk c → (ArenaMem c s' ⋆ R) m' → Q () m'

theorem kissat_assign_wp (Γ : Env) :
    ∀ args m Q X, kissatAssignSpec args m Q X → Func.wp Γ kissat_assign_body args m Q X := by
  rintro ⟨h, lit, rsn, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  unfold Func.wp kissat_assign_body; wp_unfold
  have hmv := c.hmv; unfold dimacsBound at hmv
  have hv_eq : (lit >>> 1).setWidth 64 = BitVec.ofNat 64 (lit.toNat / 2) := by
    rw [bv32_zext64_eq, bv32_lshr_1]
  have hv_lt : lit.toNat / 2 < 2 ^ 64 := by have := lit.isLt; omega
  refine ⟨_, load_arena_mv hm, ?_⟩
  rw [hv_eq, bv_ule_eq (by omega) hv_lt]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  refine ⟨fun hge => by simpa [hge] using hQ, fun hvlt => ?_⟩
  have hte64 : s.trail_end < 2 ^ 64 := by have := hlen.trail_end_le; omega
  refine ⟨_, load_arena_trail_end hm, _, load_arena_mv hm, ?_⟩
  rw [bv_ule_eq (by omega) hte64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  refine ⟨fun hte_ge => by simpa [hte_ge] using hQ, fun hte_lt => ?_⟩
  have hnot : ¬ (c.mv ≤ lit.toNat / 2 ∨ c.mv ≤ s.trail_end) := by omega
  simp only [hnot, ↓reduceIte] at hQ
  have hlit_lt : lit.toNat < 2 * c.mv := by omega
  have hnlit_lt : (lit.toNat ^^^ 1) < 2 * c.mv := litNeg_lt_two_mul hlit_lt
  refine ⟨_, load_arena_values hm, _, load_arena_level hm, _, load_arena_reason hm,
    _, load_arena_trail hm, ?_⟩
  rw [bv32_zext64_eq, trunc32_8_one]
  obtain ⟨ok1, hm1⟩ := store_arena_vals 1#8 (by rw [hlen.vals_len]; exact hlit_lt) hm
  refine ⟨ok1, ?_⟩
  rw [bv32_zext64_eq, bv32_xor_1, trunc32_8_neg1]
  obtain ⟨ok2, hm2⟩ := store_arena_vals 0xFF#8
    (by simp [hlen.vals_len]; exact hnlit_lt) hm1
  refine ⟨ok2, _, load_arena_cur_level hm2, ?_⟩
  rw [bv64_mul4_nat, bv64_trunc32_ofNat hlen.cur_level_lt]
  obtain ⟨ok3, hm3⟩ := store_arena_lvl (i := lit.toNat / 2) (BitVec.ofNat 32 s.cur_level)
    (by simp [hlen.lvl_len]; omega) hm2
  refine ⟨ok3, ?_⟩
  obtain ⟨ok4, hm4⟩ := store_arena_rsns (i := lit.toNat / 2) rsn
    (by simp [hlen.rsns_len]; omega) hm3
  refine ⟨ok4, _, load_arena_trail_end hm4, ?_⟩
  rw [bv64_mul4_nat]
  obtain ⟨ok5, hm5⟩ := store_arena_trl (i := s.trail_end) lit (by simp [hlen.trl_len]; omega) hm4
  refine ⟨ok5, _, load_arena_trail_end hm5, ?_⟩
  rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, bv_add_ofNat]
  obtain ⟨ok6, hm6⟩ := store_arena_trail_end (s.trail_end + 1) hm5
  refine ⟨ok6, hQ _ ?_ hm6⟩
  have hpr_le := hlen.propagated_le
  exact ⟨by simp [hlen.vals_len], hlen.mrk_len, by simp [hlen.lvl_len], by simp [hlen.rsns_len],
    by simp [hlen.trl_len], hlen.tmp_len_arr, hlen.wh_len, hlen.cls_len, hlen.wn_len,
    hlen.lpool_len, hlen.lit_len_le, hlen.num_clauses_le, by dsimp; omega, by dsimp; omega,
    hlen.cur_level_lt, hlen.tmp_cnt_lt, hlen.tmp_len_lt⟩

/-- Specification of `kissat_add_watch(h, w, lit)`. -/
def kissatAddWatchSpec : Spec [i64, i32, i32] [] := fun (h, _w, _lit, ()) m Q _ =>
  ∃ (c : ArenaCfg) (s : ArenaState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (ArenaMem c s ⋆ R) m ∧
    ∀ wh' wn' m',
      wh'.length = 2 * c.mv → wn'.length = 2 * c.max_c →
      (ArenaMem c { s with wh := wh', wn := wn' } ⋆ R) m' → Q () m'

theorem kissat_add_watch_wp (Γ : Env) :
    ∀ args m Q X, kissatAddWatchSpec args m Q X → Func.wp Γ kissat_add_watch_body args m Q X := by
  rintro ⟨h, w, lit, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  unfold Func.wp kissat_add_watch_body; wp_unfold
  have hmv := c.hmv; have hmc := c.hmax_c; unfold dimacsBound at hmv hmc
  have hlit64 : lit.toNat < 2 ^ 64 := by have := lit.isLt; omega
  have hw64 : w.toNat < 2 ^ 64 := by have := w.isLt; omega
  refine ⟨_, load_arena_mv hm, ?_⟩
  rw [bv32_zext64_eq, bv_shl_sext1, bv_ule_eq (by omega) hlit64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  refine ⟨fun _ => hQ s.wh s.wn m hlen.wh_len hlen.wn_len hm, fun hlit_lt => ?_⟩
  refine ⟨_, load_arena_max_clauses hm, ?_⟩
  rw [bv32_zext64_eq, bv_shl_sext1, bv_ule_eq (by omega) hw64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  refine ⟨fun _ => hQ s.wh s.wn m hlen.wh_len hlen.wn_len hm, fun hw_lt => ?_⟩
  refine ⟨_, load_arena_watch_head hm, _, load_arena_watch_next hm, ?_⟩
  rw [bv64_mul4_nat, bv64_mul4_nat]
  refine ⟨_, load_arena_wh (by rw [hlen.wh_len]; omega) hm, ?_⟩
  obtain ⟨ok1, hm1⟩ := store_arena_wn (i := w.toNat) _ (by rw [hlen.wn_len]; omega) hm
  refine ⟨ok1, ?_⟩
  obtain ⟨ok2, hm2⟩ := store_arena_wh (i := lit.toNat) w (by simp [hlen.wh_len]; omega) hm1
  exact ⟨ok2, hQ _ _ _ (by simp [hlen.wh_len]) (by simp [hlen.wn_len]) hm2⟩

/-- Specification of `kissat_add_clause(h, len)`. -/
def kissatAddClauseSpec : Spec [i64, i32] [i64] := fun (h, len, ()) m Q _ =>
  ∃ (c : ArenaCfg) (s : ArenaState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ len.toNat ≤ c.mv ∧ (ArenaMem c s ⋆ R) m ∧
    if c.max_c ≤ s.num_clauses ∨ c.lcap - s.lit_len < len.toNat then
      Q (0xFFFFFFFF#64, ()) m
    else
      ∀ s' m',
        s'.LengthsOk c →
        s'.d_cur = s.d_cur → s'.d_val = s.d_val →
        s'.lit_len = s.lit_len + len.toNat →
        s'.num_clauses = s.num_clauses + 1 →
        s'.trail_end = s.trail_end → s'.propagated = s.propagated →
        s'.cur_level = s.cur_level → s'.fuel = s.fuel → s'.confl_cid = s.confl_cid →
        s'.tmp_cnt = s.tmp_cnt → s'.tmp_len = s.tmp_len →
        s'.vals = s.vals → s'.mrk = s.mrk → s'.lvl = s.lvl →
        s'.rsns = s.rsns → s'.trl = s.trl → s'.tmp = s.tmp →
        (∀ cid < s.num_clauses,
          clauseOff s' cid = clauseOff s cid ∧
          clauseSize s' cid = clauseSize s cid) →
        (∀ k < s.lit_len, s'.lpool[k]? = s.lpool[k]?) →
        clauseOff s' s.num_clauses = s.lit_len →
        clauseSize s' s.num_clauses = len.toNat →
        clauseLits s' s.num_clauses = (s.tmp.take len.toNat).map BitVec.toNat →
        (ArenaMem c s' ⋆ R) m' →
        Q (BitVec.ofNat 64 s.num_clauses, ()) m'

theorem kissat_add_clause_wp (Γ : Env)
    (hAw : ∀ args m Q X, kissatAddWatchSpec args m Q X →
      Γ "kissat_add_watch" [i64, i32, i32] [] args m Q X) :
    ∀ args m Q X, kissatAddClauseSpec args m Q X →
      Func.wp Γ kissat_add_clause_body args m Q X := by
  rintro ⟨h, len, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hlen_mv, hm, hQ⟩
  unfold Func.wp kissat_add_clause_body; wp_unfold
  have hmv := c.hmv; have hmc := c.hmax_c; have hlc := c.hlcap
  unfold dimacsBound at hmv hmc hlc
  have hnc_le := hlen.num_clauses_le; have hll_le := hlen.lit_len_le
  refine ⟨_, load_arena_num_clauses hm, _, load_arena_max_clauses hm, ?_⟩
  rw [bv_ule_eq (by omega) (by omega)]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  refine ⟨fun hge => by simpa [hge] using hQ, fun hnc_lt => ?_⟩
  refine ⟨_, load_arena_lit_cap hm, _, load_arena_lit_len hm, ?_⟩
  rw [bv32_zext64_eq, bv_sub_ofNat hll_le (by omega), bv_ult_eq (by omega) (by omega)]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  refine ⟨fun hgt => by simpa [hgt] using hQ, fun hcap_ok => ?_⟩
  have hnot : ¬ (c.max_c ≤ s.num_clauses ∨ c.lcap - s.lit_len < len.toNat) := by omega
  simp only [hnot, ↓reduceIte] at hQ
  refine ⟨_, load_arena_num_clauses hm, _, load_arena_num_clauses hm, ?_⟩
  rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, bv_add_ofNat]
  obtain ⟨ok1, hm1⟩ := store_arena_num_clauses (s.num_clauses + 1) hm
  refine ⟨ok1, _, load_arena_lit_len hm1, _, load_arena_lit_len hm1, ?_⟩
  rw [bv_add_ofNat]
  obtain ⟨ok2, hm2⟩ := store_arena_lit_len (s.lit_len + len.toNat) hm1
  refine ⟨ok2, _, load_arena_tmp_lits hm2, _, load_arena_lit_pool hm2, ?_⟩
  let s0 : ArenaState :=
    { s with num_clauses := s.num_clauses + 1, lit_len := s.lit_len + len.toNat }
  have hcid_eq : (BitVec.ofNat 64 s.num_clauses).setWidth 32 = BitVec.ofNat 32 s.num_clauses :=
    bv64_trunc32_ofNat (by omega)
  have hoff_eq : (BitVec.ofNat 64 s.lit_len).setWidth 32 = BitVec.ofNat 32 s.lit_len :=
    bv64_trunc32_ofNat (by omega)
  refine wp_loop_group
    (fun r (iv, ()) ml => ∃ i lpool',
      i ≤ len.toNat ∧ r = len.toNat - i ∧ iv = BitVec.ofNat 32 i ∧
      lpool'.length = c.lcap ∧
      (∀ k < s.lit_len, lpool'[k]? = s.lpool[k]?) ∧
      (∀ k < i, lpool'[s.lit_len + k]? = s.tmp[k]?) ∧
      (ArenaMem c { s0 with lpool := lpool' } ⋆ R) ml) ?_ ?_
  · rintro L r ⟨iv, ⟨⟩⟩ ml ih ⟨i, lpool', hi_le, rfl, rfl, hlpl, hpre, hcpy, hml⟩
    wp_unfold
    rw [show len = BitVec.ofNat 32 len.toNat from (bv_ofNat_toNat_eq len).symm,
      bv32_ult_eq (by omega) (by omega)]
    simp only [decide_eq_true_eq, decide_eq_false_iff_not]
    refine ⟨fun hilt => ?_, fun hige => ?_⟩
    · rw [hoff_eq, bv32_zext64_eq, bv32_zext64_eq, bv32_ofNat_toNat (by omega),
        bv32_ofNat_toNat (by omega), bv_add_ofNat, bv64_mul4_nat, bv64_mul4_nat]
      refine ⟨_, load_arena_tmp (by simp [s0, hlen.tmp_len_arr]; omega) hml, ?_⟩
      obtain ⟨oks, hms⟩ := store_arena_lpool (i := s.lit_len + i)
        (s.tmp[i]'(by rw [hlen.tmp_len_arr]; omega)) (by simp [hlpl]; omega) hml
      refine ⟨oks, ?_⟩
      rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
        show BitVec.ofNat 32 i + BitVec.ofNat 32 1 = BitVec.ofNat 32 (i + 1) by grind]
      refine ih (len.toNat - (i + 1)) _ _ (by omega)
        ⟨i + 1, lpool'.set (s.lit_len + i) (s.tmp[i]'(by rw [hlen.tmp_len_arr]; omega)),
          by omega, rfl, rfl, by simp [hlpl], ?_, ?_, hms⟩
      · intro k hk
        rw [List.getElem?_set_ne (by omega)]; exact hpre k hk
      · intro k hk
        by_cases hki : k = i
        · subst k
          rw [List.getElem?_set_self (by omega),
            List.getElem?_eq_getElem (by rw [hlen.tmp_len_arr]; omega)]
        · rw [List.getElem?_set_ne (by omega)]; exact hcpy k (by omega)
    · have hieq : i = len.toNat := by omega
      subst hieq
      refine ⟨_, load_arena_clauses hml, ?_⟩
      rw [hcid_eq, bv32_mul16_eq, bv32_ofNat_toNat (by omega), hoff_eq]
      obtain ⟨okc0, hmc0⟩ := store_arena_cls (i := 4 * s.num_clauses)
        (BitVec.ofNat 32 s.lit_len) (by simp [s0, hlen.cls_len]; omega) hml
      refine ⟨okc0, ?_⟩
      rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, ptr_add_ofNat,
        show 4 * (4 * s.num_clauses) + 4 = 4 * (4 * s.num_clauses + 1) by omega]
      obtain ⟨okc1, hmc1⟩ := store_arena_cls (i := 4 * s.num_clauses + 1)
        (BitVec.ofNat 32 len.toNat) (by simp [s0, hlen.cls_len]; omega) hmc0
      refine ⟨okc1, ?_⟩
      rw [show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, ptr_add_ofNat,
        show 4 * (4 * s.num_clauses) + 8 = 4 * (4 * s.num_clauses + 2) by omega]
      obtain ⟨okc2, hmc2⟩ := store_arena_cls (i := 4 * s.num_clauses + 2)
        2#32 (by simp [s0, hlen.cls_len]; omega) hmc1
      refine ⟨okc2, ?_⟩
      rw [show (12 : BitVec 64) = BitVec.ofNat 64 12 from rfl, ptr_add_ofNat,
        show 4 * (4 * s.num_clauses) + 12 = 4 * (4 * s.num_clauses + 3) by omega]
      obtain ⟨okc3, hmc3⟩ := store_arena_cls (i := 4 * s.num_clauses + 3)
        0#32 (by simp [s0, hlen.cls_len]; omega) hmc2
      let cls' := (((s.cls.set (4 * s.num_clauses) (BitVec.ofNat 32 s.lit_len)).set
        (4 * s.num_clauses + 1) (BitVec.ofNat 32 len.toNat)).set
        (4 * s.num_clauses + 2) 2#32).set (4 * s.num_clauses + 3) 0#32
      let s1 : ArenaState := { s0 with lpool := lpool', cls := cls' }
      have hlen_s1 : s1.LengthsOk c :=
        ⟨hlen.vals_len, hlen.mrk_len, hlen.lvl_len, hlen.rsns_len, hlen.trl_len,
          hlen.tmp_len_arr, hlen.wh_len, by simp [s1, cls', hlen.cls_len], hlen.wn_len, hlpl,
          by dsimp [s1, s0]; omega, by dsimp [s1, s0]; omega, hlen.trail_end_le,
          hlen.propagated_le, hlen.cur_level_lt, hlen.tmp_cnt_lt, hlen.tmp_len_lt⟩
      have hfinish : ∀ wh' wn' mf, wh'.length = 2 * c.mv → wn'.length = 2 * c.max_c →
          (ArenaMem c { s1 with wh := wh', wn := wn' } ⋆ R) mf →
          Q ((BitVec.ofNat 32 s.num_clauses).setWidth 64, ()) mf := by
        intro wh' wn' mf hwl hwnl hmf
        have hret : (BitVec.ofNat 32 s.num_clauses).setWidth 64 =
            BitVec.ofNat 64 s.num_clauses := by
          rw [bv32_zext64_eq, bv32_ofNat_toNat (by omega)]
        rw [hret]
        let sf : ArenaState := { s1 with wh := wh', wn := wn' }
        have hoff_new : clauseOff sf s.num_clauses = s.lit_len := by
          unfold clauseOff sf s1 cls'
          rw [List.getElem?_set_ne (by omega : 4 * s.num_clauses + 3 ≠ 4 * s.num_clauses),
            List.getElem?_set_ne (by omega : 4 * s.num_clauses + 2 ≠ 4 * s.num_clauses),
            List.getElem?_set_ne (by omega : 4 * s.num_clauses + 1 ≠ 4 * s.num_clauses),
            List.getElem?_set_self (by rw [hlen.cls_len]; omega)]
          exact bv32_ofNat_toNat (by omega)
        have hsz_new : clauseSize sf s.num_clauses = len.toNat := by
          unfold clauseSize sf s1 cls'
          rw [List.getElem?_set_ne (by omega : 4 * s.num_clauses + 3 ≠ 4 * s.num_clauses + 1),
            List.getElem?_set_ne (by omega : 4 * s.num_clauses + 2 ≠ 4 * s.num_clauses + 1),
            List.getElem?_set_self (by simp [hlen.cls_len]; omega)]
          exact bv32_ofNat_toNat (by omega)
        refine hQ sf mf ⟨hlen_s1.vals_len, hlen_s1.mrk_len, hlen_s1.lvl_len, hlen_s1.rsns_len,
          hlen_s1.trl_len, hlen_s1.tmp_len_arr, hwl, hlen_s1.cls_len, hwnl, hlen_s1.lpool_len,
          hlen_s1.lit_len_le, hlen_s1.num_clauses_le, hlen_s1.trail_end_le, hlen_s1.propagated_le,
          hlen_s1.cur_level_lt, hlen_s1.tmp_cnt_lt, hlen_s1.tmp_len_lt⟩
          rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl ?_ hpre
          hoff_new hsz_new ?_ hmf
        · intro cid hcid
          refine ⟨?_, ?_⟩
          · unfold clauseOff sf s1 cls'
            simp [List.getElem?_set_ne (by omega : 4 * s.num_clauses + 3 ≠ 4 * cid),
              List.getElem?_set_ne (by omega : 4 * s.num_clauses + 2 ≠ 4 * cid),
              List.getElem?_set_ne (by omega : 4 * s.num_clauses + 1 ≠ 4 * cid),
              List.getElem?_set_ne (by omega : 4 * s.num_clauses ≠ 4 * cid)]
          · unfold clauseSize sf s1 cls'
            simp [List.getElem?_set_ne (by omega : 4 * s.num_clauses + 3 ≠ 4 * cid + 1),
              List.getElem?_set_ne (by omega : 4 * s.num_clauses + 2 ≠ 4 * cid + 1),
              List.getElem?_set_ne (by omega : 4 * s.num_clauses + 1 ≠ 4 * cid + 1),
              List.getElem?_set_ne (by omega : 4 * s.num_clauses ≠ 4 * cid + 1)]
        · unfold clauseLits
          rw [hoff_new, hsz_new]
          apply List.ext_getElem
          · simp [sf, s1, hlpl, hlen.tmp_len_arr]; omega
          · intro k hk1 hk2
            simp only [List.getElem_map, List.getElem_take, List.getElem_drop]
            have hklt : k < len.toNat := by
              simp only [List.length_map, List.length_take, hlen.tmp_len_arr] at hk2; omega
            have heq := hcpy k hklt
            rw [List.getElem?_eq_getElem (by omega),
              List.getElem?_eq_getElem (by rw [hlen.tmp_len_arr]; omega)] at heq
            exact congrArg BitVec.toNat (Option.some.inj heq)
      refine ⟨okc3, ?_⟩
      refine wp_join_group
        (fun () mf => ∃ wh' wn', wh'.length = 2 * c.mv ∧ wn'.length = 2 * c.max_c ∧
          (ArenaMem c { s1 with wh := wh', wn := wn' } ⋆ R) mf) ?_ ?_
      · rintro _ ⟨⟩ mf ⟨wh', wn', hwl, hwnl, hmf⟩
        wp_unfold; exact hfinish wh' wn' mf hwl hwnl hmf
      · intro J hJ; wp_unfold
        rw [show (2 : BitVec 32) = BitVec.ofNat 32 2 from rfl, bv32_ule_eq (by decide) (by omega)]
        simp only [decide_eq_true_eq, decide_eq_false_iff_not]
        refine ⟨fun hge2 => ?_, fun _ => hJ () _ ⟨s.wh, s.wn, hlen.wh_len, hlen.wn_len, hmc3⟩⟩
        rw [show ((0 : BitVec 32).signExtend 64) * 4#64 = BitVec.ofNat 64 (4 * 0) from rfl]
        have htmp0 := load_arena_tmp (s := s1) (i := 0) (by rw [hlen_s1.tmp_len_arr]; omega) hmc3
        refine ⟨_, htmp0, ?_⟩
        apply wp_call_of_spec; apply hAw
        refine ⟨c, s1, R, rfl, hlen_s1, hmc3, fun wh1 wn1 m1 hwl1 hwnl1 hm1' => ?_⟩
        wp_unfold
        rw [show ((1 : BitVec 32).signExtend 64) * 4#64 = BitVec.ofNat 64 (4 * 1) from rfl]
        have htmp1 := load_arena_tmp (s := { s1 with wh := wh1, wn := wn1 }) (i := 1)
          (by rw [hlen_s1.tmp_len_arr]; omega) hm1'
        refine ⟨_, htmp1, ?_⟩
        apply wp_call_of_spec; apply hAw
        refine ⟨c, { s1 with wh := wh1, wn := wn1 }, R, rfl,
          ⟨hlen_s1.vals_len, hlen_s1.mrk_len, hlen_s1.lvl_len, hlen_s1.rsns_len, hlen_s1.trl_len,
            hlen_s1.tmp_len_arr, hwl1, hlen_s1.cls_len, hwnl1, hlen_s1.lpool_len,
            hlen_s1.lit_len_le, hlen_s1.num_clauses_le, hlen_s1.trail_end_le, hlen_s1.propagated_le,
            hlen_s1.cur_level_lt, hlen_s1.tmp_cnt_lt, hlen_s1.tmp_len_lt⟩,
          hm1', fun wh2 wn2 m2 hwl2 hwnl2 hm2' => hJ () m2 ⟨wh2, wn2, hwl2, hwnl2, hm2'⟩⟩
  · intro L hL; wp_unfold
    exact hL len.toNat _ _ ⟨0, s.lpool, Nat.zero_le _, by simp, rfl, hlen.lpool_len,
      fun _ _ => rfl, fun _ h => by omega, hm2⟩

/-- Specification of `kissat_backtrack(h, target_lvl)`. -/
def kissatBacktrackSpec : Spec [i64, i64] [] := fun (h, target_lvl, ()) m Q _ =>
  ∃ (c : ArenaCfg) (F0 : CNF Nat) (s : ArenaState) (R : Mem 64 → Prop),
    h = c.hdr ∧ SolverInv c F0 s ∧ target_lvl.toNat ≤ s.cur_level ∧ (ArenaMem c s ⋆ R) m ∧
    ∀ s' m',
      SolverInv c F0 s' →
      s'.d_cur = s.d_cur → s'.d_val = s.d_val →
      s'.lit_len = s.lit_len → s'.num_clauses = s.num_clauses →
      s'.cur_level = target_lvl.toNat →
      s'.trail_end ≤ s.trail_end →
      s'.fuel = s.fuel → s'.confl_cid = s.confl_cid →
      s'.tmp_cnt = s.tmp_cnt → s'.tmp_len = s.tmp_len →
      s'.tmp = s.tmp → s'.cls = s.cls → s'.lpool = s.lpool →
      s'.wh = s.wh → s'.wn = s.wn →
      (∀ i < s'.trail_end, s'.trl[i]? = s.trl[i]?) →
      (∀ i < s.trail_end,
        (s.lvl[(s.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ target_lvl.toNat →
        i < s'.trail_end) →
      (ArenaMem c s' ⋆ R) m' → Q () m'

theorem kissat_backtrack_wp (Γ : Env) :
    ∀ args m Q X, kissatBacktrackSpec args m Q X → Func.wp Γ kissat_backtrack_body args m Q X := by
  rintro ⟨h, target_lvl, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, htgt_le, hm, hQ⟩
  unfold Func.wp kissat_backtrack_body; wp_unfold
  have hmv := c.hmv; unfold dimacsBound at hmv
  have hcore := hinv.core; have hlen := hcore.lengths
  have htgt_lt : target_lvl.toNat < 2 ^ 64 := target_lvl.isLt
  refine ⟨_, load_arena_values hm, _, load_arena_level hm, _, load_arena_reason hm,
    _, load_arena_trail hm, _, load_arena_trail_end hm, ?_⟩
  let PopInv (te : Nat) (st : ArenaState) : Prop :=
    te ≤ s.trail_end ∧
    st.d_cur = s.d_cur ∧ st.d_val = s.d_val ∧
    st.lit_len = s.lit_len ∧ st.num_clauses = s.num_clauses ∧
    st.trail_end = s.trail_end ∧ st.propagated = s.propagated ∧
    st.cur_level = s.cur_level ∧ st.fuel = s.fuel ∧ st.confl_cid = s.confl_cid ∧
    st.tmp_cnt = s.tmp_cnt ∧ st.tmp_len = s.tmp_len ∧
    st.mrk = s.mrk ∧ st.trl = s.trl ∧ st.tmp = s.tmp ∧
    st.wh = s.wh ∧ st.cls = s.cls ∧ st.wn = s.wn ∧ st.lpool = s.lpool ∧
    st.vals.length = 2 * c.mv ∧ st.lvl.length = c.mv ∧ st.rsns.length = c.mv ∧
    (∀ l < 2 * c.mv,
      st.vals[l]?.getD 0#8 = 0#8 ∨ st.vals[l]?.getD 0#8 = 1#8 ∨ st.vals[l]?.getD 0#8 = 0xFF#8) ∧
    (∀ l < 2 * c.mv,
      st.vals[l]?.getD 0#8 = 1#8 ↔ ∃ i < te, (s.trl[i]?.getD 0#32).toNat = l) ∧
    (∀ l < 2 * c.mv,
      st.vals[l]?.getD 0#8 = 0xFF#8 ↔ ∃ i < te, (s.trl[i]?.getD 0#32).toNat = l ^^^ 1) ∧
    (∀ i < te,
      st.lvl[(s.trl[i]?.getD 0#32).toNat / 2]? = s.lvl[(s.trl[i]?.getD 0#32).toNat / 2]? ∧
      st.rsns[(s.trl[i]?.getD 0#32).toNat / 2]? = s.rsns[(s.trl[i]?.getD 0#32).toNat / 2]?) ∧
    (∀ i, te ≤ i → i < s.trail_end →
      target_lvl.toNat < (s.lvl[(s.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat)
  refine wp_loop_break_group
    (fun (te_v, ()) mb => ∃ te st,
      te_v = BitVec.ofNat 64 te ∧ PopInv te st ∧
      (∀ i < te, (s.lvl[(s.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ target_lvl.toNat) ∧
      (ArenaMem c st ⋆ R) mb)
    (fun r (te_v, ()) ml => ∃ te st,
      r = te ∧ te_v = BitVec.ofNat 64 te ∧ PopInv te st ∧ (ArenaMem c st ⋆ R) ml) ?_ ?_ ?_
  · rintro _ ⟨te_v, ⟨⟩⟩ mb ⟨te, st, rfl, hpi, hall_le, hmb⟩
    obtain ⟨hte_le, hd1, hd2, hll, hnc, _, hpr, _, hfu, hcf, htc, htl, hmrk, htrl, htmp, hwh, hcls,
      hwn, hlpool, hvl, hllv, hrsl, hvdom, hvt, hvf, hlr, hpopped⟩ := hpi
    wp_unfold
    obtain ⟨ok1, hm1⟩ := store_arena_trail_end te hmb
    refine ⟨ok1, ?_⟩
    refine wp_join_group (fun () m2 => ∃ prop', prop' ≤ te ∧
        (ArenaMem c { st with trail_end := te, propagated := prop' } ⋆ R) m2) ?_ ?_
    · rintro _ ⟨⟩ m2 ⟨prop', hple, hm2⟩
      wp_unfold
      obtain ⟨okc, hmc⟩ := store_arena_cur_level target_lvl.toNat hm2
      rw [bv_ofNat_toNat_eq target_lvl] at hmc
      refine ⟨okc, ?_⟩
      let sf : ArenaState :=
        { st with trail_end := te, propagated := prop', cur_level := target_lvl.toNat }
      have hsf_te : sf.trail_end = te := rfl
      have hsf_cl : sf.cur_level = target_lvl.toNat := rfl
      have hsf_len : sf.LengthsOk c :=
        ⟨hvl, by simp [sf, hmrk, hlen.mrk_len], hllv, hrsl, by simp [sf, htrl, hlen.trl_len],
          by simp [sf, htmp, hlen.tmp_len_arr], by simp [sf, hwh, hlen.wh_len],
          by simp [sf, hcls, hlen.cls_len], by simp [sf, hwn, hlen.wn_len],
          by simp [sf, hlpool, hlen.lpool_len], by simp [sf, hll, hlen.lit_len_le],
          by simp [sf, hnc, hlen.num_clauses_le], by rw [hsf_te]; have := hlen.trail_end_le; omega,
          hple, by rw [hsf_cl]; have := hlen.cur_level_lt; omega,
          by simp [sf, htc, hlen.tmp_cnt_lt], by simp [sf, htl, hlen.tmp_len_lt]⟩
      have hsf_inhab : ∀ L, 1 ≤ L → L ≤ target_lvl.toNat →
          ∃ i < te, (sf.lvl[(sf.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = L := by
        intro L hL1 hLle
        obtain ⟨i, hi, hli⟩ := hcore.levels_inhabited L hL1 (by omega)
        have hite : i < te := by
          by_cases hlt : i < te
          · exact hlt
          · have hgt := hpopped i (by omega) hi; omega
        refine ⟨i, hite, ?_⟩
        simp only [sf, htrl, (hlr i hite).1, hli]
      have hcur_le : target_lvl.toNat ≤ te :=
        le_of_surj_range1 (fun i => (sf.lvl[(sf.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat)
          hsf_inhab
      have hsf_clauses : ClausesInv c F0 sf := by
        have hco : ∀ cid, clauseOff sf cid = clauseOff s cid := fun cid => by
          unfold clauseOff; simp [sf, hcls]
        have hcs : ∀ cid, clauseSize sf cid = clauseSize s cid := fun cid => by
          unfold clauseSize; simp [sf, hcls]
        have hcl' : ∀ cid, clauseLits sf cid = clauseLits s cid := fun cid => by
          unfold clauseLits; rw [hco, hcs]; simp [sf, hlpool]
        refine ⟨fun cid hcid => ?_, fun c1 c2 h12 h2 => ?_, fun cid hcid => ?_, fun cid hcid => ?_⟩
        · rw [hco, hcs]; simp only [sf, hll, hnc] at hcid ⊢; exact hcore.clauses.bounds cid hcid
        · rw [hco, hcs, hco]; simp only [sf, hnc] at h2; exact hcore.clauses.disjoint c1 c2 h12 h2
        · rw [hcl']; simp only [sf, hnc] at hcid; exact hcore.clauses.lits_lt cid hcid
        · rw [hcl']; simp only [sf, hnc] at hcid; exact hcore.clauses.entails cid hcid
      have hsf_inv : SolverInv c F0 sf := by
        refine ⟨⟨hsf_len, hsf_clauses, hcur_le, ?_, ?_, hvdom, ?_, ?_, ?_, ?_, hsf_inhab, ?_, ?_⟩,
          fun v hv => by simpa [sf, hmrk] using hinv.marks v hv⟩
        · intro i hi; rw [hsf_te] at hi; simp only [sf, htrl]
          exact hcore.trail_lits_lt i (by omega)
        · intro i j hi hj heq; rw [hsf_te] at hi hj; simp only [sf, htrl] at heq
          exact hcore.trail_vars_nodup i j (by omega) (by omega) heq
        · intro l hl; rw [hsf_te]; simp only [sf, htrl]; exact hvt l hl
        · intro l hl; rw [hsf_te]; simp only [sf, htrl]; exact hvf l hl
        · intro i hi; rw [hsf_te] at hi; rw [hsf_cl]
          simp only [sf, htrl, (hlr i hi).1]; exact hall_le i hi
        · intro i j hij hj; rw [hsf_te] at hj
          simp only [sf, htrl, (hlr i (by omega)).1, (hlr j hj).1]
          exact hcore.trail_mono i j hij (by omega)
        · intro i hi hli; rw [hsf_te] at hi
          simp only [sf, htrl, (hlr i hi).1] at hli ⊢
          exact hcore.level0_sound i (by omega) hli
        · intro idx hidx; rw [hsf_te] at hidx; dsimp only
          simp only [sf, htrl, (hlr idx hidx).2, hnc]
          intro hne
          obtain ⟨hrc, hall⟩ := hcore.reason_inv idx (by omega) hne
          refine ⟨hrc, fun q hq => ?_⟩
          have hq' : q ∈ clauseLits s
              (s.rsns[(s.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat := by
            simpa [clauseLits, clauseOff, clauseSize, hcls, hlpool] using hq
          exact hall q hq'
      exact hQ sf _ hsf_inv hd1 hd2 hll hnc rfl hte_le hfu hcf htc htl htmp hcls hlpool hwh hwn
        (fun i _ => by simp [sf, htrl])
        (fun i hi hle => by
          by_cases hlt : i < te
          · exact hlt
          · have hgt := hpopped i (by omega) hi; omega) hmc
    · intro J hJ; wp_unfold
      refine ⟨_, load_arena_propagated hm1, ?_⟩
      have hte64 : te < 2 ^ 64 := by have := hlen.trail_end_le; omega
      have hpr64 : s.propagated < 2 ^ 64 := by
        have := hlen.propagated_le; have := hlen.trail_end_le; omega
      rw [hpr, bv_ult_eq hte64 hpr64]
      simp only [decide_eq_true_eq, decide_eq_false_iff_not]
      refine ⟨fun hgt => ?_, fun hle => hJ () _ ⟨s.propagated, by omega, by simpa [hpr] using hm1⟩⟩
      obtain ⟨okp, hmp⟩ := store_arena_propagated te hm1
      exact ⟨okp, hJ () _ ⟨te, Nat.le_refl _, hmp⟩⟩
  · rintro B L r ⟨te_v, ⟨⟩⟩ ml hB ih ⟨te, st, hr, rfl, hpi, hml⟩
    subst r
    obtain ⟨hte_le, hd1, hd2, hll, hnc, hte_st, hpr, hcl, hfu, hcf, htc, htl, hmrk, htrl, htmp,
      hwh, hcls, hwn, hlpool, hvl, hllv, hrsl, hvdom, hvt, hvf, hlr, hpopped⟩ := hpi
    wp_unfold
    have hte_le_mv : s.trail_end ≤ c.mv := hlen.trail_end_le
    have hte64 : te < 2 ^ 64 := by omega
    rw [show (0 : BitVec 64) = BitVec.ofNat 64 0 from rfl, bv_ult_eq (by decide) hte64]
    simp only [decide_eq_true_eq, decide_eq_false_iff_not]
    refine ⟨fun hpos => ?_, fun hzero => ?_⟩
    · have hsub : BitVec.ofNat 64 te - 1 = BitVec.ofNat 64 (te - 1) :=
        bv_sub_ofNat (a := te) (b := 1) (by omega) hte64
      rw [hsub, bv64_mul4_nat]
      have hidx : te - 1 < st.trl.length := by rw [htrl, hlen.trl_len]; omega
      refine ⟨_, load_arena_trl hidx hml, ?_⟩
      let lit := st.trl[te - 1]'hidx
      have hlit_eq : lit = s.trl[te - 1]'(by rw [hlen.trl_len]; omega) := by simp [lit, htrl]
      have hlit_lt : lit.toNat < 2 * c.mv := by
        have := hcore.trail_lits_lt (te - 1) (by omega)
        rwa [List.getElem?_eq_getElem (by rw [hlen.trl_len]; omega), Option.getD_some,
          ← hlit_eq] at this
      have hv_lt : lit.toNat / 2 < c.mv := by omega
      rw [bv32_mul4_eq, bv32_lshr_1]
      refine ⟨_, load_arena_lvl (by rw [hllv]; exact hv_lt) hml, ?_⟩
      have hlvl_st_eq : st.lvl[lit.toNat / 2]'(by rw [hllv]; exact hv_lt) =
          s.lvl[(s.trl[te - 1]?.getD 0#32).toNat / 2]?.getD 0#32 := by
        have h1 := (hlr (te - 1) (by omega)).1
        have h2 : (s.trl[te - 1]?.getD 0#32).toNat = lit.toNat := by
          rw [List.getElem?_eq_getElem (by rw [hlen.trl_len]; omega), Option.getD_some, hlit_eq]
        rw [h2] at h1 ⊢
        rw [← h1, List.getElem?_eq_getElem (by rw [hllv]; exact hv_lt), Option.getD_some]
      let lv := st.lvl[lit.toNat / 2]'(by rw [hllv]; exact hv_lt)
      have hle_eq : (BitVec.ofNat 64 lv.toNat).ule target_lvl =
          decide (lv.toNat ≤ target_lvl.toNat) := by
        simpa [bv_ofNat_toNat_eq target_lvl] using
          bv_ule_eq (a := lv.toNat) (b := target_lvl.toNat) (by have := lv.isLt; omega) htgt_lt
      rw [bv32_zext64_eq, hle_eq]
      simp only [decide_eq_true_eq, decide_eq_false_iff_not]
      refine ⟨fun hle => ?_, fun hgt => ?_⟩
      · refine hB (BitVec.ofNat 64 te, ()) ml ⟨te, st, rfl,
          ⟨hte_le, hd1, hd2, hll, hnc, hte_st, hpr, hcl, hfu, hcf, htc, htl, hmrk, htrl, htmp,
            hwh, hcls, hwn, hlpool, hvl, hllv, hrsl, hvdom, hvt, hvf, hlr, hpopped⟩, ?_, hml⟩
        intro i hi
        have hm := hcore.trail_mono i (te - 1) (by omega) (by omega)
        dsimp only [lv] at hle; rw [← hlvl_st_eq] at hm; omega
      · have hnlit_lt : (lit.toNat ^^^ 1) < 2 * c.mv := litNeg_lt_two_mul hlit_lt
        rw [bv32_zext64_eq, trunc32_8_zero]
        obtain ⟨ok1, hm1⟩ := store_arena_vals (i := lit.toNat) 0#8 (by rw [hvl]; exact hlit_lt) hml
        refine ⟨ok1, ?_⟩
        rw [bv32_zext64_eq, bv32_xor_1]
        obtain ⟨ok2, hm2⟩ := store_arena_vals (i := lit.toNat ^^^ 1) 0#8
          (by simp [hvl]; exact hnlit_lt) hm1
        refine ⟨ok2, ?_⟩
        obtain ⟨ok3, hm3⟩ := store_arena_lvl (i := lit.toNat / 2) 0#32
          (by simp [hllv]; exact hv_lt) hm2
        refine ⟨ok3, ?_⟩
        obtain ⟨ok4, hm4⟩ := store_arena_rsns (i := lit.toNat / 2) 0xFFFFFFFF#32
          (by simp [hrsl]; exact hv_lt) hm3
        refine ⟨ok4, ?_⟩
        have htr_te : (s.trl[te - 1]?.getD 0#32).toNat = lit.toNat := by
          rw [List.getElem?_eq_getElem (by rw [hlen.trl_len]; omega), Option.getD_some, hlit_eq]
        have hnot_pre : ∀ i < te - 1, (s.trl[i]?.getD 0#32).toNat / 2 ≠ lit.toNat / 2 := by
          intro i hi heq
          have := hcore.trail_vars_nodup i (te - 1) (by omega) (by omega)
            (by rw [htr_te]; exact heq)
          omega
        let st' : ArenaState :=
          { st with
            vals := (st.vals.set lit.toNat 0#8).set (lit.toNat ^^^ 1) 0#8
            lvl := st.lvl.set (lit.toNat / 2) 0#32
            rsns := st.rsns.set (lit.toNat / 2) 0xFFFFFFFF#32 }
        refine ih (te - 1) _ _ (by omega) ⟨te - 1, st', rfl, rfl,
          ⟨by omega, hd1, hd2, hll, hnc, hte_st, hpr, hcl, hfu, hcf, htc, htl, hmrk, htrl, htmp,
            hwh, hcls, hwn, hlpool, by simp [st', hvl], by simp [st', hllv], by simp [st', hrsl],
            ?_, ?_, ?_, ?_, ?_⟩, hm4⟩
        · intro l hl
          dsimp only [st']
          by_cases h1 : l = lit.toNat ^^^ 1
          · subst h1
            rw [List.getElem?_set_self (by simp [hvl]; exact hnlit_lt)]; exact Or.inl rfl
          · rw [List.getElem?_set_ne (Ne.symm h1)]
            by_cases h2 : l = lit.toNat
            · subst h2
              rw [List.getElem?_set_self (by rw [hvl]; exact hlit_lt)]; exact Or.inl rfl
            · rw [List.getElem?_set_ne (Ne.symm h2)]; exact hvdom l hl
        · intro l hl
          dsimp only [st']
          by_cases h1 : l = lit.toNat ^^^ 1
          · subst h1
            rw [List.getElem?_set_self (by simp [hvl]; exact hnlit_lt), Option.getD_some]
            refine ⟨(fun hc => by cases hc), fun ⟨i, hi, heq⟩ => ?_⟩
            exact absurd (by rw [heq]; exact litVar_litNeg _) (hnot_pre i hi)
          · rw [List.getElem?_set_ne (Ne.symm h1)]
            by_cases h2 : l = lit.toNat
            · subst h2
              rw [List.getElem?_set_self (by rw [hvl]; exact hlit_lt), Option.getD_some]
              refine ⟨(fun hc => by cases hc), fun ⟨i, hi, heq⟩ => ?_⟩
              exact absurd (by rw [heq]) (hnot_pre i hi)
            · rw [List.getElem?_set_ne (Ne.symm h2), hvt l hl]
              refine ⟨fun ⟨i, hi, heq⟩ => ⟨i, ?_, heq⟩, fun ⟨i, hi, heq⟩ => ⟨i, by omega, heq⟩⟩
              by_cases hie : i = te - 1
              · subst hie; rw [htr_te] at heq; exact absurd heq.symm h2
              · omega
        · intro l hl
          dsimp only [st']
          by_cases h1 : l = lit.toNat ^^^ 1
          · subst h1
            rw [List.getElem?_set_self (by simp [hvl]; exact hnlit_lt), Option.getD_some]
            refine ⟨(fun hc => by cases hc), fun ⟨i, hi, heq⟩ => ?_⟩
            exact absurd (by
              rw [heq]; have h := litNeg_litNeg lit.toNat; unfold litNeg at h; rw [h])
              (hnot_pre i hi)
          · rw [List.getElem?_set_ne (Ne.symm h1)]
            by_cases h2 : l = lit.toNat
            · subst h2
              rw [List.getElem?_set_self (by rw [hvl]; exact hlit_lt), Option.getD_some]
              refine ⟨(fun hc => by cases hc), fun ⟨i, hi, heq⟩ => ?_⟩
              exact absurd (by rw [heq]; exact litVar_litNeg _) (hnot_pre i hi)
            · rw [List.getElem?_set_ne (Ne.symm h2), hvf l hl]
              refine ⟨fun ⟨i, hi, heq⟩ => ⟨i, ?_, heq⟩, fun ⟨i, hi, heq⟩ => ⟨i, by omega, heq⟩⟩
              by_cases hie : i = te - 1
              · subst hie; rw [htr_te] at heq
                have : l = lit.toNat ^^^ 1 := by
                  have h := congrArg litNeg heq
                  have h' : litNeg (l ^^^ 1) = l := litNeg_litNeg l
                  rw [h'] at h; exact h.symm
                exact absurd this h1
              · omega
        · intro i hi
          have hnv := hnot_pre i hi
          dsimp only [st']
          refine ⟨?_, ?_⟩
          · rw [List.getElem?_set_ne (Ne.symm hnv)]; exact (hlr i (by omega)).1
          · rw [List.getElem?_set_ne (Ne.symm hnv)]; exact (hlr i (by omega)).2
        · intro i hi1 hi2
          by_cases hie : i = te - 1
          · subst hie; dsimp only [lv] at hgt; rw [← hlvl_st_eq]; omega
          · exact hpopped i (by omega) hi2
    · have hte0 : te = 0 := by omega
      subst hte0
      exact hB (0#64, ()) ml ⟨0, st, rfl,
        ⟨hte_le, hd1, hd2, hll, hnc, hte_st, hpr, hcl, hfu, hcf, htc, htl, hmrk, htrl, htmp,
          hwh, hcls, hwn, hlpool, hvl, hllv, hrsl, hvdom, hvt, hvf, hlr, hpopped⟩,
        fun _ h => by omega, hml⟩
  · intro B L _ hL; wp_unfold
    refine hL s.trail_end _ m ⟨s.trail_end, s, rfl, rfl,
      ⟨Nat.le_refl _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        rfl, rfl, rfl, hlen.vals_len, hlen.lvl_len, hlen.rsns_len,
        hcore.vals_domain, hcore.vals_true_iff, hcore.vals_false_iff,
        fun _ _ => ⟨rfl, rfl⟩, fun _ h1 h2 => by omega⟩, hm⟩

/-- Specification of `kissat_zero_tables(h)`. -/
def kissatZeroTablesSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : ArenaCfg) (s : ArenaState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (ArenaMem c s ⋆ R) m ∧
    let s' : ArenaState :=
      { s with
        vals := List.replicate (2 * c.mv) 0#8
        wh := List.replicate (2 * c.mv) 0xFFFFFFFF#32
        mrk := List.replicate c.mv 0#8
        lvl := List.replicate c.mv 0#32
        rsns := List.replicate c.mv 0xFFFFFFFF#32
        tmp := List.replicate c.mv 0#32 }
    ∀ m', (ArenaMem c s' ⋆ R) m' → Q () m'

theorem kissat_zero_tables_wp (Γ : Env) :
    ∀ args m Q X, kissatZeroTablesSpec args m Q X →
      Func.wp Γ kissat_zero_tables_body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  unfold Func.wp kissat_zero_tables_body; wp_unfold
  have hmv := c.hmv; unfold dimacsBound at hmv
  refine ⟨_, load_arena_mv hm, _, load_arena_values hm, _, load_arena_watch_head hm, ?_⟩
  rw [bv_shl_sext1]
  refine wp_loop_group
    (fun r (iv, ()) ml => ∃ i vals' wh',
      i ≤ 2 * c.mv ∧ r = 2 * c.mv - i ∧ iv = BitVec.ofNat 64 i ∧
      vals'.length = 2 * c.mv ∧ wh'.length = 2 * c.mv ∧
      (∀ k < i, vals'[k]? = some 0#8 ∧ wh'[k]? = some 0xFFFFFFFF#32) ∧
      (ArenaMem c { s with vals := vals', wh := wh' } ⋆ R) ml) ?_ ?_
  · rintro L r ⟨iv, ⟨⟩⟩ ml ih ⟨i, vals', wh', hile, rfl, rfl, hvl, hwl, hzero, hml⟩
    wp_unfold
    rw [bv_ult_eq (by omega) (by omega)]
    simp only [decide_eq_true_eq, decide_eq_false_iff_not]
    refine ⟨fun hilt => ?_, fun hige => ?_⟩
    · rw [trunc32_8_zero]
      obtain ⟨ok1, hm1⟩ := store_arena_vals 0#8 (by simp [hvl]; exact hilt) hml
      refine ⟨ok1, ?_⟩
      rw [bv64_mul4_nat]
      obtain ⟨ok2, hm2⟩ := store_arena_wh 0xFFFFFFFF#32 (by simp [hwl]; exact hilt) hm1
      refine ⟨ok2, ?_⟩
      rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, bv_add_ofNat]
      refine ih (2 * c.mv - (i + 1)) _ _ (by omega)
        ⟨i + 1, vals'.set i 0#8, wh'.set i 0xFFFFFFFF#32, by omega, rfl, rfl,
          by simp [hvl], by simp [hwl], ?_, hm2⟩
      intro k hk
      by_cases hki : k = i
      · subst k; simp [List.getElem?_set_self (by omega : i < vals'.length),
          List.getElem?_set_self (by omega : i < wh'.length)]
      · rw [List.getElem?_set_ne (Ne.symm hki), List.getElem?_set_ne (Ne.symm hki)]
        exact hzero k (by omega)
    · have hieq : i = 2 * c.mv := by omega
      subst hieq
      have hvals_eq : vals' = List.replicate (2 * c.mv) 0#8 :=
        List.ext_getElem (by simp [hvl]) fun k hk1 _ => by
          have := (hzero k (by omega)).1
          rw [List.getElem?_eq_getElem hk1, Option.some.injEq] at this; simpa using this
      have hwh_eq : wh' = List.replicate (2 * c.mv) 0xFFFFFFFF#32 :=
        List.ext_getElem (by simp [hwl]) fun k hk1 _ => by
          have := (hzero k (by omega)).2
          rw [List.getElem?_eq_getElem hk1, Option.some.injEq] at this; simpa using this
      rw [hvals_eq, hwh_eq] at hml
      let s1 : ArenaState :=
        { s with vals := List.replicate (2 * c.mv) 0#8,
                 wh := List.replicate (2 * c.mv) 0xFFFFFFFF#32 }
      refine ⟨_, load_arena_mark hml, _, load_arena_level hml, _, load_arena_reason hml,
        _, load_arena_tmp_lits hml, ?_⟩
      refine wp_loop_group
        (fun r2 (vv, ()) m2 => ∃ v mrk' lvl' rsns' tmp',
          v ≤ c.mv ∧ r2 = c.mv - v ∧ vv = BitVec.ofNat 64 v ∧
          mrk'.length = c.mv ∧ lvl'.length = c.mv ∧ rsns'.length = c.mv ∧ tmp'.length = c.mv ∧
          (∀ k < v, mrk'[k]? = some 0#8 ∧ lvl'[k]? = some 0#32 ∧
            rsns'[k]? = some 0xFFFFFFFF#32 ∧ tmp'[k]? = some 0#32) ∧
          (ArenaMem c { s1 with mrk := mrk', lvl := lvl', rsns := rsns', tmp := tmp' } ⋆ R) m2)
        ?_ ?_
      · rintro L2 r2 ⟨vv, ⟨⟩⟩ m2 ih2
          ⟨v, mrk', lvl', rsns', tmp', hvle, rfl, rfl, hmkl, hlvll, hrsl, htmpl, hz2, hm2⟩
        wp_unfold
        rw [bv_ult_eq (by omega) (by omega)]
        simp only [decide_eq_true_eq, decide_eq_false_iff_not]
        refine ⟨fun hvlt => ?_, fun hvge => ?_⟩
        · rw [trunc32_8_zero]
          obtain ⟨ok1, hm1⟩ := store_arena_mrk 0#8 (by simp [hmkl]; exact hvlt) hm2
          refine ⟨ok1, ?_⟩
          rw [bv64_mul4_nat]
          obtain ⟨ok2, hm2'⟩ := store_arena_lvl 0#32 (by simp [hlvll]; exact hvlt) hm1
          refine ⟨ok2, ?_⟩
          obtain ⟨ok3, hm3⟩ := store_arena_rsns 0xFFFFFFFF#32 (by simp [hrsl]; exact hvlt) hm2'
          refine ⟨ok3, ?_⟩
          obtain ⟨ok4, hm4⟩ := store_arena_tmp 0#32 (by simp [htmpl]; exact hvlt) hm3
          refine ⟨ok4, ?_⟩
          rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, bv_add_ofNat]
          refine ih2 (c.mv - (v + 1)) _ _ (by omega)
            ⟨v + 1, mrk'.set v 0#8, lvl'.set v 0#32, rsns'.set v 0xFFFFFFFF#32, tmp'.set v 0#32,
              by omega, rfl, rfl, by simp [hmkl], by simp [hlvll], by simp [hrsl], by simp [htmpl],
              ?_, hm4⟩
          intro k hk
          by_cases hkv : k = v
          · subst k
            simp [List.getElem?_set_self (by omega : v < mrk'.length),
              List.getElem?_set_self (by omega : v < lvl'.length),
              List.getElem?_set_self (by omega : v < rsns'.length),
              List.getElem?_set_self (by omega : v < tmp'.length)]
          · rw [List.getElem?_set_ne (Ne.symm hkv), List.getElem?_set_ne (Ne.symm hkv),
              List.getElem?_set_ne (Ne.symm hkv), List.getElem?_set_ne (Ne.symm hkv)]
            exact hz2 k (by omega)
        · have hveq : v = c.mv := by omega
          subst hveq
          have hm_eq : mrk' = List.replicate c.mv 0#8 :=
            List.ext_getElem (by simp [hmkl]) fun k hk1 _ => by
              have := (hz2 k (by omega)).1
              rw [List.getElem?_eq_getElem hk1, Option.some.injEq] at this; simpa using this
          have hl_eq : lvl' = List.replicate c.mv 0#32 :=
            List.ext_getElem (by simp [hlvll]) fun k hk1 _ => by
              have := (hz2 k (by omega)).2.1
              rw [List.getElem?_eq_getElem hk1, Option.some.injEq] at this; simpa using this
          have hr_eq : rsns' = List.replicate c.mv 0xFFFFFFFF#32 :=
            List.ext_getElem (by simp [hrsl]) fun k hk1 _ => by
              have := (hz2 k (by omega)).2.2.1
              rw [List.getElem?_eq_getElem hk1, Option.some.injEq] at this; simpa using this
          have ht_eq : tmp' = List.replicate c.mv 0#32 :=
            List.ext_getElem (by simp [htmpl]) fun k hk1 _ => by
              have := (hz2 k (by omega)).2.2.2
              rw [List.getElem?_eq_getElem hk1, Option.some.injEq] at this; simpa using this
          rw [hm_eq, hl_eq, hr_eq, ht_eq] at hm2
          exact hQ m2 hm2
      · intro L2 hL2; wp_unfold
        exact hL2 c.mv _ _ ⟨0, s.mrk, s.lvl, s.rsns, s.tmp, Nat.zero_le _, by simp, rfl,
          hlen.mrk_len, hlen.lvl_len, hlen.rsns_len, hlen.tmp_len_arr, fun _ h => by omega, hml⟩
  · intro L hL; wp_unfold
    exact hL (2 * c.mv) _ m ⟨0, s.vals, s.wh, Nat.zero_le _, by simp, rfl,
      hlen.vals_len, hlen.wh_len, fun _ h => by omega, hm⟩

end LeanQbe.T.Examples.Kissat
