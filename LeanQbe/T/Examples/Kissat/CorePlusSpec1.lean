module

public import LeanQbe.T.Examples.Kissat.CorePlusArena
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Core+` Modular Invariants & Minimization / Unit-Witness Helpers (`Stage 2`)

Builds on `CorePlusArena` to define:
1. Clause projections (`clauseOff`, `clauseSize`, `clauseLits`) and structured invariants
   (`ClausesInv`, `CorePlusCoreInv` / `TrailInv`, `MarksClear`, `MinMarkInv`, `CorePlusInv`),
   keeping heuristic fields (`HeurState`) out of soundness obligations.
2. Invariant preservation & minimization soundness lemmas (`assign_preserves_core`,
   `addClause_preserves_core`, `swapClause_preserves_core`, `minMarkInv_*`,
   `entails_of_minMarkInv`).
3. Unit-witness trace predicates (`UnitSatTrace`, `UnitUnsatTrace`) and pure DIMACS/CNF helpers
   for non-vacuity and `Func.wp` proofs (`CorePlusSpec` holds per-fn contracts & `Env.ofTable`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.CorePlus

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test

/-! ## 1. Clause projections and solver invariants -/

/-- Starting offset in `s.lpool` of clause `cid`. -/
def clauseOff (s : CorePlusState) (cid : Nat) : Nat :=
  (s.cls[4 * cid]?.getD 0#32).toNat

/-- Literal count of clause `cid`. -/
def clauseSize (s : CorePlusState) (cid : Nat) : Nat :=
  (s.cls[4 * cid + 1]?.getD 0#32).toNat

/-- Literal list of clause `cid` as 0-based Kissat `Nat` literals. -/
def clauseLits (s : CorePlusState) (cid : Nat) : List Nat :=
  ((s.lpool.drop (clauseOff s cid)).take (clauseSize s cid)).map BitVec.toNat

theorem mem_clauseLits_iff {s : CorePlusState} {cid l : Nat}
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
size `≥ 2`, literals `< 2 * mv`, semantically entailed by `F0`. -/
structure ClausesInv (c : CorePlusCfg) (F0 : CNF Nat) (s : CorePlusState) : Prop where
  bounds : ∀ cid < s.num_clauses,
    2 ≤ clauseSize s cid ∧ clauseOff s cid + clauseSize s cid ≤ s.lit_len
  disjoint : ∀ cid1 cid2, cid1 < cid2 → cid2 < s.num_clauses →
    clauseOff s cid1 + clauseSize s cid1 ≤ clauseOff s cid2
  lits_lt : ∀ cid < s.num_clauses, ∀ l ∈ clauseLits s cid, l < 2 * c.mv
  entails : ∀ cid < s.num_clauses, F0.EntailsClause (cnfClause (clauseLits s cid))

/-- Mark-agnostic core CDCL trail & reason invariant (independent of `HeurState`). -/
structure CorePlusCoreInv (c : CorePlusCfg) (F0 : CNF Nat) (s : CorePlusState) : Prop where
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

/-- Alias highlighting trail soundness focus. -/
abbrev TrailInv := CorePlusCoreInv

/-- All entries of `s.mrk[0 ..< c.mv)` are zero. -/
def MarksClear (c : CorePlusCfg) (s : CorePlusState) : Prop :=
  ∀ v < c.mv, s.mrk[v]?.getD 0#8 = 0#8

/-- Iterative minimization mark invariant for `kissat_minimize_lit` / `kissat_minimize_clause`:
1. Marks stay in `{0#8, 2#8, 4#8}` (`UNSEEN`, `REMOVABLE`, `POISONED`).
2. When `min_clr_full = 0#64`, every nonzero mark in `0..mv` is logged in `min_clr[0..min_clr_len)`.
3. Every `REMOVABLE`-marked trail variable either keeps its falsified literal in `keep` or has
   its reason clause justified strictly earlier on the trail by `lvl = 0` or `REMOVABLE`. -/
structure MinMarkInv (c : CorePlusCfg) (s : CorePlusState) (keep : List Nat) : Prop where
  mrk_dom : ∀ v < c.mv,
    s.mrk[v]?.getD 0#8 = 0#8 ∨ s.mrk[v]?.getD 0#8 = 2#8 ∨ s.mrk[v]?.getD 0#8 = 4#8
  clr_cov : s.min_clr_full = 0#64 → ∀ v < c.mv, s.mrk[v]?.getD 0#8 ≠ 0#8 →
    ∃ k < s.min_clr_len, (s.min_clr[k]?.getD 0#32).toNat = v
  rem_sound : ∀ idx < s.trail_end,
    let p := (s.trl[idx]?.getD 0#32).toNat
    let v := p / 2
    s.mrk[v]?.getD 0#8 = 2#8 →
    (p ^^^ 1) ∈ keep ∨
      let rsn := s.rsns[v]?.getD 0xFFFFFFFF#32
      rsn ≠ 0xFFFFFFFF#32 ∧ rsn.toNat < s.num_clauses ∧
      ∀ q ∈ clauseLits s rsn.toNat,
        q = p ∨
        ∃ k < idx,
          (s.trl[k]?.getD 0#32).toNat = q ^^^ 1 ∧
          ((s.lvl[q / 2]?.getD 0#32).toNat = 0 ∨ s.mrk[q / 2]?.getD 0#8 = 2#8)

/-- Full CDCL solver invariant (`CorePlusCoreInv` + `MarksClear`). -/
structure CorePlusInv (c : CorePlusCfg) (F0 : CNF Nat) (s : CorePlusState) : Prop where
  core : CorePlusCoreInv c F0 s
  marks : MarksClear c s

/-! ## 2. Invariant preservation and minimization soundness lemmas -/

theorem HeurState.LengthsOk.with_vals {c : CorePlusCfg} (h : HeurState)
    {hp' ps' : List (BitVec 32)} {sc' : List (BitVec 64)}
    {ph' : List (BitVec 8)} {hl' : Nat}
    (h1 : hp'.length = c.mv) (h2 : ps'.length = c.mv)
    (h3 : sc'.length = c.mv) (h4 : ph'.length = c.mv) (h5 : hl' ≤ c.mv) :
    ({ h with heap := hp', pos := ps', score := sc', phases := ph',
              heap_len := hl' } : HeurState).LengthsOk c :=
  ⟨h1, h2, h3, h4, h5⟩

theorem CorePlusState.LengthsOk.with_heur {c : CorePlusCfg} {s : CorePlusState}
    (hlen : s.LengthsOk c) {heur' : HeurState} (hok : heur'.LengthsOk c) :
    ({ s with heur := heur' } : CorePlusState).LengthsOk c :=
  { hlen with heur_ok := hok }

theorem CorePlusCoreInv.mono {c : CorePlusCfg} {F0 F1 : CNF Nat} {s : CorePlusState}
    (hF : F1.Entails F0) (h : CorePlusCoreInv c F0 s) : CorePlusCoreInv c F1 s :=
  { h with
    clauses := { h.clauses with
      entails := fun cid hcid => CNF.entails_clause_trans hF (h.clauses.entails cid hcid) }
    level0_sound := fun i hi hl0 => CNF.entails_clause_trans hF (h.level0_sound i hi hl0) }

theorem CorePlusInv.mono {c : CorePlusCfg} {F0 F1 : CNF Nat} {s : CorePlusState}
    (hF : F1.Entails F0) (h : CorePlusInv c F0 s) : CorePlusInv c F1 s :=
  ⟨h.core.mono hF, h.marks⟩

theorem CorePlusCoreInv.with_heur {c : CorePlusCfg} {F0 : CNF Nat} {s : CorePlusState}
    (h : CorePlusCoreInv c F0 s) {heur' : HeurState} (hok : heur'.LengthsOk c) :
    CorePlusCoreInv c F0 { s with heur := heur' } :=
  { h with
    lengths := h.lengths.with_heur hok
    clauses := { h.clauses with bounds := h.clauses.bounds } }

theorem CorePlusInv.with_heur {c : CorePlusCfg} {F0 : CNF Nat} {s : CorePlusState}
    (h : CorePlusInv c F0 s) {heur' : HeurState} (hok : heur'.LengthsOk c) :
    CorePlusInv c F0 { s with heur := heur' } :=
  ⟨h.core.with_heur hok, h.marks⟩

theorem CorePlusCoreInv.with_d {c : CorePlusCfg} {F0 : CNF Nat} {s : CorePlusState}
    (h : CorePlusCoreInv c F0 s) (cur' val' : BitVec 64) :
    CorePlusCoreInv c F0 { s with d_cur := cur', d_val := val' } :=
  { h with
    lengths := { h.lengths with vals_len := h.lengths.vals_len }
    clauses := { h.clauses with bounds := h.clauses.bounds } }

theorem CorePlusInv.with_d {c : CorePlusCfg} {F0 : CNF Nat} {s : CorePlusState}
    (h : CorePlusInv c F0 s) (cur' val' : BitVec 64) :
    CorePlusInv c F0 { s with d_cur := cur', d_val := val' } :=
  ⟨h.core.with_d cur' val', h.marks⟩

theorem CorePlusCoreInv.vals_zero_iff {c : CorePlusCfg} {F0 : CNF Nat} {s : CorePlusState}
    (h : CorePlusCoreInv c F0 s) {l : Nat} (hl : l < 2 * c.mv) :
    s.vals[l]?.getD 0#8 = 0#8 ↔ ∀ i < s.trail_end, (s.trl[i]?.getD 0#32).toNat / 2 ≠ l / 2 := by
  constructor
  · intro hz i hi hvar
    rcases (litVar_eq_iff _ l).mp hvar with h1 | h2
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

theorem CorePlusCoreInv.trail_end_lt_of_unassigned {c : CorePlusCfg} {F0 : CNF Nat}
    {s : CorePlusState} (h : CorePlusCoreInv c F0 s) {l : Nat} (hl : l < 2 * c.mv)
    (hun : s.vals[l]?.getD 0#8 = 0#8) : s.trail_end < c.mv := by
  have hmiss := (h.vals_zero_iff hl).mp hun
  exact inj_lt_of_missing (fun i => (s.trl[i]?.getD 0#32).toNat / 2)
    (fun i j hi hj heq => h.trail_vars_nodup i j hi hj heq)
    (fun i hi => by have := h.trail_lits_lt i hi; omega)
    (by omega : l / 2 < c.mv) hmiss

theorem CorePlusCoreInv.level0_unsat_of_conflict {c : CorePlusCfg} {F0 : CNF Nat}
    {s : CorePlusState} (h : CorePlusCoreInv c F0 s) (hl0 : s.cur_level = 0)
    {cid : Nat} (hcid : cid < s.num_clauses)
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

theorem CorePlusCoreInv.falsified_lit_unique {c : CorePlusCfg} {F0 : CNF Nat}
    {s : CorePlusState} (h : CorePlusCoreInv c F0 s) {l1 l2 : Nat}
    (hl1 : l1 < 2 * c.mv) (hl2 : l2 < 2 * c.mv) (hv : l1 / 2 = l2 / 2)
    (hf1 : s.vals[l1]?.getD 0#8 = 0xFF#8) (hf2 : s.vals[l2]?.getD 0#8 = 0xFF#8) :
    l1 = l2 := by
  obtain ⟨i1, hi1, he1⟩ := (h.vals_false_iff l1 hl1).mp hf1
  obtain ⟨i2, hi2, he2⟩ := (h.vals_false_iff l2 hl2).mp hf2
  have hi : i1 = i2 := h.trail_vars_nodup i1 i2 hi1 hi2 (by
    rw [he1, he2]
    have h1 := litVar_litNeg l1; have h2 := litVar_litNeg l2
    unfold litVar litNeg at h1 h2; omega)
  subst hi
  have hx : litNeg l1 = litNeg l2 := he1.symm.trans he2
  simpa using congrArg litNeg hx

/-- Pushing an unassigned literal onto the trail preserves `CorePlusCoreInv`. -/
theorem assign_preserves_core {c : CorePlusCfg} {F0 : CNF Nat} {s : CorePlusState}
    (hinv : CorePlusCoreInv c F0 s) {lit rsn : BitVec 32} {phases' : List (BitVec 8)}
    (hlit : lit.toNat < 2 * c.mv) (hph : phases'.length = c.mv)
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
    let s' : CorePlusState :=
      { s with
        vals := (s.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8
        lvl := s.lvl.set v (BitVec.ofNat 32 s.cur_level)
        rsns := s.rsns.set v rsn
        trl := s.trl.set s.trail_end lit
        trail_end := s.trail_end + 1
        heur := { s.heur with phases := phases' } }
    CorePlusCoreInv c F0 s' := by
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
    · subst h1; dsimp only [s']; simp only [↓reduceIte]
      rw [List.getElem?_set_self (by simp [hlen.vals_len]; exact hnlit_lt)]; rfl
    · dsimp only [s']; simp only [h1, ↓reduceIte]
      rw [List.getElem?_set_ne (Ne.symm h1)]
      by_cases h2 : l = lit.toNat
      · subst h2; simp only [↓reduceIte]
        rw [List.getElem?_set_self (by rw [hlen.vals_len]; exact hlit)]; rfl
      · simp only [h2, ↓reduceIte]; rw [List.getElem?_set_ne (Ne.symm h2)]
  have hs'_te : s'.trail_end = s.trail_end + 1 := rfl
  have hs'_cl : s'.cur_level = s.cur_level := rfl
  have hs'_nc : s'.num_clauses = s.num_clauses := rfl
  have hheur' : s'.heur.LengthsOk c :=
    { hlen.heur_ok with phases_len := hph }
  have hlen' : s'.LengthsOk c :=
    { hlen with
      vals_len := by simp [s', hlen.vals_len]
      lvl_len := by simp [s', hlen.lvl_len]
      rsns_len := by simp [s', hlen.rsns_len]
      trl_len := by simp [s', hlen.trl_len]
      trail_end_le := by dsimp [s']; omega
      propagated_le := by dsimp [s']; have := hlen.propagated_le; omega
      heur_ok := hheur' }
  refine ⟨hlen', ⟨hinv.clauses.bounds, hinv.clauses.disjoint, hinv.clauses.lits_lt,
      hinv.clauses.entails⟩, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
  · intro i hi; rw [hs'_te] at hi; rw [hs'_cl, htrl_get i hi]
    by_cases hie : i = s.trail_end
    · simp only [hie, ↓reduceIte]; rw [hlvl_get v (by omega)]; simp
    · simp only [hie, ↓reduceIte]
      have hilt : i < s.trail_end := by omega
      rw [hlvl_get _ (by have := hinv.trail_lits_lt i hilt; omega)]
      simp only [hnot_var i hilt, ↓reduceIte]; exact hinv.lvl_le i hilt
  · intro i j hij hj; rw [hs'_te] at hj; rw [htrl_get i (by omega), htrl_get j hj]
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
  · intro i hi hli; rw [hs'_te] at hi; rw [htrl_get i hi] at hli ⊢
    by_cases hie : i = s.trail_end
    · simp only [hie, ↓reduceIte] at hli ⊢
      rw [hlvl_get v (by omega)] at hli; simp only [↓reduceIte] at hli; exact hl0 hli
    · simp only [hie, ↓reduceIte] at hli ⊢
      have hilt : i < s.trail_end := by omega
      rw [hlvl_get _ (by have := hinv.trail_lits_lt i hilt; omega)] at hli
      simp only [hnot_var i hilt, ↓reduceIte] at hli; exact hinv.level0_sound i hilt hli
  · intro idx hidx; rw [hs'_te] at hidx; dsimp only; rw [htrl_get idx hidx]
    by_cases hie : idx = s.trail_end
    · simp only [hie, ↓reduceIte]
      have hr : s'.rsns[v]?.getD 0xFFFFFFFF#32 = rsn := by
        dsimp only [s']; rw [List.getElem?_set_self (by rw [hlen.rsns_len]; omega)]; rfl
      rw [hr]; intro hne
      obtain ⟨hrc, hall⟩ := hrsn hne
      refine ⟨by rw [hs'_nc]; exact hrc, fun q hq => ?_⟩
      have hq' : q ∈ clauseLits s rsn.toNat := by
        simpa [clauseLits, clauseOff, clauseSize, s'] using hq
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
        simpa [clauseLits, clauseOff, clauseSize, s'] using hq
      exact (hall q hq').elim Or.inl fun ⟨k, hk, hkeq⟩ => Or.inr ⟨k, hk, by
        rw [htrl_get k (by omega)]; simp [show k ≠ s.trail_end by omega, hkeq]⟩

/-- Helper state update after appending one clause in `kissat_add_clause`. -/
def addClauseState (s : CorePlusState) (len : Nat)
    (lpool' cls' wh' wn' : List (BitVec 32)) : CorePlusState :=
  { s with
    lit_len := s.lit_len + len
    num_clauses := s.num_clauses + 1
    lpool := lpool', cls := cls', wh := wh', wn := wn' }

/-- Appending an entailed clause of length `≥ 2` preserves `CorePlusCoreInv`. -/
theorem addClause_preserves_core {c : CorePlusCfg} {F0 : CNF Nat} {s : CorePlusState}
    {len : Nat} {lpool' cls' wh' wn' : List (BitVec 32)}
    (hinv : CorePlusCoreInv c F0 s)
    (hlen' : (addClauseState s len lpool' cls' wh' wn').LengthsOk c)
    (hge2 : 2 ≤ len)
    (hlits_lt : ∀ l ∈ (s.tmp.take len).map BitVec.toNat, l < 2 * c.mv)
    (hent : F0.EntailsClause (cnfClause ((s.tmp.take len).map BitVec.toNat)))
    (hold_meta : ∀ cid < s.num_clauses,
      clauseOff (addClauseState s len lpool' cls' wh' wn') cid = clauseOff s cid ∧
      clauseSize (addClauseState s len lpool' cls' wh' wn') cid = clauseSize s cid)
    (hold_lpool : ∀ k < s.lit_len, lpool'[k]? = s.lpool[k]?)
    (hoff_new : clauseOff (addClauseState s len lpool' cls' wh' wn') s.num_clauses = s.lit_len)
    (hsz_new : clauseSize (addClauseState s len lpool' cls' wh' wn') s.num_clauses = len)
    (hlits_new : clauseLits (addClauseState s len lpool' cls' wh' wn') s.num_clauses =
      (s.tmp.take len).map BitVec.toNat) :
    CorePlusCoreInv c F0 (addClauseState s len lpool' cls' wh' wn') := by
  let s' := addClauseState s len lpool' cls' wh' wn'
  have hold_lits : ∀ cid < s.num_clauses, clauseLits s' cid = clauseLits s cid := by
    intro cid hcid
    obtain ⟨ho, hs⟩ := hold_meta cid hcid
    have hbd := (hinv.clauses.bounds cid hcid).2
    have hl1 := hinv.lengths.lpool_len
    have hl2 : lpool'.length = c.lcap := hlen'.lpool_len
    have hll_le := hinv.lengths.lit_len_le
    unfold clauseLits; rw [ho, hs]
    apply List.ext_getElem
    · dsimp only [s', addClauseState]; simp [hl1, hl2]
    · intro k hk1 _
      simp only [s', addClauseState, List.getElem_map, List.getElem_take, List.getElem_drop]
      have hklt : clauseOff s cid + k < s.lit_len := by
        dsimp only [s', addClauseState] at hk1
        simp only [List.length_map, List.length_take, List.length_drop, hl2] at hk1; omega
      have heq := hold_lpool (clauseOff s cid + k) hklt
      rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at heq
      exact congrArg BitVec.toNat (Option.some.inj heq)
  refine ⟨hlen', ⟨?_, ?_, ?_, ?_⟩, hinv.cur_level_le, hinv.trail_lits_lt, hinv.trail_vars_nodup,
    hinv.vals_domain, hinv.vals_true_iff, hinv.vals_false_iff, hinv.lvl_le, hinv.trail_mono,
    hinv.levels_inhabited, hinv.level0_sound, ?_⟩
  · intro cid hcid
    rcases Nat.lt_succ_iff_lt_or_eq.mp hcid with hlt | rfl
    · obtain ⟨ho, hs⟩ := hold_meta cid hlt
      have hbd := hinv.clauses.bounds cid hlt
      dsimp only [s', addClauseState] at ho hs ⊢; rw [ho, hs]; omega
    · dsimp only [s', addClauseState] at hoff_new hsz_new ⊢; rw [hoff_new, hsz_new]; omega
  · intro c1 c2 h12 h2
    rcases Nat.lt_succ_iff_lt_or_eq.mp h2 with h2lt | rfl
    · obtain ⟨ho1, hs1⟩ := hold_meta c1 (by omega)
      obtain ⟨ho2, _⟩ := hold_meta c2 h2lt
      dsimp only [s', addClauseState] at ho1 hs1 ho2 ⊢
      rw [ho1, hs1, ho2]; exact hinv.clauses.disjoint c1 c2 h12 h2lt
    · obtain ⟨ho1, hs1⟩ := hold_meta c1 h12
      dsimp only [s', addClauseState] at ho1 hs1 hoff_new ⊢; rw [ho1, hs1, hoff_new]
      exact (hinv.clauses.bounds c1 h12).2
  · intro cid hcid
    rcases Nat.lt_succ_iff_lt_or_eq.mp hcid with hlt | rfl
    · rw [hold_lits cid hlt]; exact hinv.clauses.lits_lt cid hlt
    · dsimp only [s', addClauseState] at hlits_new ⊢; rw [hlits_new]; exact hlits_lt
  · intro cid hcid
    rcases Nat.lt_succ_iff_lt_or_eq.mp hcid with hlt | rfl
    · rw [hold_lits cid hlt]; exact hinv.clauses.entails cid hlt
    · dsimp only [s', addClauseState] at hlits_new ⊢; rw [hlits_new]; exact hent
  · intro idx hidx; dsimp only [s', addClauseState]; intro hne
    obtain ⟨hrc, hall⟩ := hinv.reason_inv idx hidx hne
    refine ⟨by omega, fun q hq => ?_⟩
    change q ∈ clauseLits s' _ at hq
    rw [hold_lits _ hrc] at hq
    exact hall q hq

/-- Swapping two literals inside clause `cid` preserves `CorePlusCoreInv`. -/
theorem swapClause_preserves_core {c : CorePlusCfg} {F0 : CNF Nat} {s : CorePlusState}
    (hinv : CorePlusCoreInv c F0 s) {cid k1 k2 : Nat} {srch : BitVec 32}
    {wh' wn' : List (BitVec 32)} (hcid : cid < s.num_clauses)
    (hk1 : k1 < clauseSize s cid) (hk2 : k2 < clauseSize s cid)
    (hwl : wh'.length = 2 * c.mv) (hwnl : wn'.length = 2 * c.max_c) :
    let off := clauseOff s cid
    let hlen := hinv.lengths
    have hbd : off + clauseSize s cid ≤ s.lpool.length := by
      have := (hinv.clauses.bounds cid hcid).2; have := hlen.lit_len_le; have := hlen.lpool_len
      omega
    let l1 := s.lpool[off + k1]'(by omega)
    let l2 := s.lpool[off + k2]'(by omega)
    let s' : CorePlusState :=
      { s with
        cls := s.cls.set (4 * cid + 2) srch
        lpool := (s.lpool.set (off + k1) l2).set (off + k2) l1
        wh := wh', wn := wn' }
    CorePlusCoreInv c F0 s' := by
  intro off hlen hbd l1 l2 s'
  have hmc := hlen.num_clauses_le
  have hoff_eq : ∀ id, clauseOff s' id = clauseOff s id := fun id => by
    unfold clauseOff s'
    rw [List.getElem?_set_ne (by omega : 4 * cid + 2 ≠ 4 * id)]
  have hsz_eq : ∀ id, clauseSize s' id = clauseSize s id := fun id => by
    unfold clauseSize s'
    rw [List.getElem?_set_ne (by omega : 4 * cid + 2 ≠ 4 * id + 1)]
  have hlen' : s'.LengthsOk c :=
    { hlen with
      wh_len := hwl, cls_len := by simp [s', hlen.cls_len],
      wn_len := hwnl, lpool_len := by simp [s', hlen.lpool_len] }
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

/-- Initial zeroed state produced by `kissat_init_state` satisfies `CorePlusInv`. -/
theorem corePlusInv_init {c : CorePlusCfg} {s : CorePlusState} (hlen : s.LengthsOk c)
    (hnc : s.num_clauses = 0) (hte : s.trail_end = 0) (hcl : s.cur_level = 0)
    (hvals : s.vals = List.replicate (2 * c.mv) 0#8)
    (hmrk : s.mrk = List.replicate c.mv 0#8) :
    CorePlusInv c (shiftDownCnf CNF.empty) s := by
  refine ⟨⟨hlen,
    ⟨fun _ h => (by rw [hnc] at h; cases h),
     fun _ _ _ h => (by rw [hnc] at h; cases h),
     fun _ h => (by rw [hnc] at h; cases h),
     fun _ h => (by rw [hnc] at h; cases h)⟩,
    by rw [hte, hcl]; exact Nat.le_refl _,
    fun _ h => (by rw [hte] at h; cases h),
    fun _ _ h => (by rw [hte] at h; cases h),
    fun l hl => (by rw [hvals]; simp [hl]),
    fun l hl => (by rw [hvals, hte]; simp [hl]),
    fun l hl => (by rw [hvals, hte]; simp [hl]),
    fun _ h => (by rw [hte] at h; cases h),
    fun _ _ _ h => (by rw [hte] at h; cases h),
    fun _ _ h2 => (by rw [hcl] at h2; omega),
    fun _ h => (by rw [hte] at h; cases h),
    fun _ h => (by rw [hte] at h; cases h)⟩,
    fun v hv => (by rw [hmrk]; simp [hv])⟩

theorem minMarkInv_init {c : CorePlusCfg} {F0 : CNF Nat} {s : CorePlusState}
    (hcore : CorePlusCoreInv c F0 s) (hmc : MarksClear c s) (keep : List Nat) :
    MinMarkInv c s keep :=
  ⟨fun v hv => Or.inl (hmc v hv),
   fun _ v hv hnz => absurd (hmc v hv) hnz,
   fun idx hi h => by
     have hv : (s.trl[idx]?.getD 0#32).toNat / 2 < c.mv := by
       have := hcore.trail_lits_lt idx hi; omega
     have := hmc _ hv
     rw [h] at this; cases this⟩

private theorem trail_xor_var_lt {c : CorePlusCfg} {F0 : CNF Nat} {s : CorePlusState}
    (hcore : CorePlusCoreInv c F0 s) {k q : Nat} (hk : k < s.trail_end)
    (hkeq : (s.trl[k]?.getD 0#32).toNat = q ^^^ 1) : q / 2 < c.mv := by
  have hlt := hcore.trail_lits_lt k hk
  have hql : (q ^^^ 1) / 2 = q / 2 := litVar_litNeg q
  rw [hkeq, ← hql] at *
  omega

/-- State update performed by `kissat_min_mark(h, v, tag)` when `mrk[v] = 0`. -/
def minMarkState (c : CorePlusCfg) (s : CorePlusState) (v : Nat) (tag : BitVec 8) :
    CorePlusState :=
  let mclr' := if s.min_clr_len < c.mv then s.min_clr.set s.min_clr_len (BitVec.ofNat 32 v)
               else s.min_clr
  let mcl' := if s.min_clr_len < c.mv then s.min_clr_len + 1 else s.min_clr_len
  let mcf' := if s.min_clr_len < c.mv then s.min_clr_full else 1#64
  { s with mrk := s.mrk.set v tag, min_clr := mclr', min_clr_len := mcl', min_clr_full := mcf' }

private theorem clr_cov_mark_step {c : CorePlusCfg} {s : CorePlusState}
    (hcov : s.min_clr_full = 0#64 → ∀ w < c.mv, s.mrk[w]?.getD 0#8 ≠ 0#8 →
      ∃ k < s.min_clr_len, (s.min_clr[k]?.getD 0#32).toNat = w)
    {v : Nat} (hv : v < c.mv) (hmcll : s.min_clr.length = c.mv)
    (tag : BitVec 8) :
    let s' := minMarkState c s v tag
    s'.min_clr_full = 0#64 → ∀ w < c.mv, s'.mrk[w]?.getD 0#8 ≠ 0#8 →
      ∃ k < s'.min_clr_len, (s'.min_clr[k]?.getD 0#32).toNat = w := by
  dsimp only [minMarkState]
  intro hmcf w hw hnz
  by_cases hlt : s.min_clr_len < c.mv
  · simp only [hlt, ↓reduceIte] at hmcf hnz ⊢
    by_cases hweq : w = v
    · subst w
      refine ⟨s.min_clr_len, by omega, ?_⟩
      rw [List.getElem?_set_self (by omega), Option.getD_some,
        bv32_ofNat_toNat (by have := c.hmv; unfold dimacsBound at this; omega)]
    · have hnz' : s.mrk[w]?.getD 0#8 ≠ 0#8 := by
        simpa [List.getElem?_set_ne (Ne.symm hweq)] using hnz
      obtain ⟨k, hk, hkeq⟩ := hcov hmcf w hw hnz'
      refine ⟨k, by omega, ?_⟩
      rw [List.getElem?_set_ne (by omega)]; exact hkeq
  · simp only [hlt, ↓reduceIte] at hmcf; cases hmcf

theorem minMarkInv_poison {c : CorePlusCfg} {F0 : CNF Nat} {s : CorePlusState} {keep : List Nat}
    (hcore : CorePlusCoreInv c F0 s) (hmin : MinMarkInv c s keep)
    {v : Nat} (hv : v < c.mv) (hz : s.mrk[v]?.getD 0#8 = 0#8) :
    MinMarkInv c (minMarkState c s v 4#8) keep := by
  let s' := minMarkState c s v 4#8; change MinMarkInv c s' keep
  have hlen := hcore.lengths
  have hmono : ∀ w < c.mv, s'.mrk[w]?.getD 0#8 = 2#8 ↔ s.mrk[w]?.getD 0#8 = 2#8 := by
    intro w _
    by_cases hweq : w = v
    · subst w; rw [show s'.mrk[v]?.getD 0#8 = 4#8 by
        simp [s', minMarkState, List.getElem?_set_self (by rw [hlen.mrk_len]; omega)], hz]; decide
    · simp [s', minMarkState, List.getElem?_set_ne (Ne.symm hweq)]
  refine ⟨fun w hw => ?_, clr_cov_mark_step hmin.clr_cov hv hlen.min_clr_len_arr 4#8,
    fun idx hi h2 => ?_⟩
  · by_cases hweq : w = v
    · subst w; right; right
      simp [s', minMarkState, List.getElem?_set_self (by rw [hlen.mrk_len]; omega)]
    · simp only [s', minMarkState, List.getElem?_set_ne (Ne.symm hweq)]; exact hmin.mrk_dom w hw
  · have hvw : (s.trl[idx]?.getD 0#32).toNat / 2 < c.mv := by
      have := hcore.trail_lits_lt idx hi; omega
    have h2' : s.mrk[(s.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#8 = 2#8 := (hmono _ hvw).mp h2
    rcases hmin.rem_sound idx hi h2' with hin | ⟨hne, hrc, hall⟩
    · exact Or.inl hin
    · refine Or.inr ⟨hne, hrc, fun q hq => ?_⟩
      rcases hall q hq with rfl | ⟨k, hk, hkeq, hdep⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨k, hk, hkeq, hdep.elim Or.inl fun hk2 =>
          Or.inr ((hmono _ (trail_xor_var_lt hcore (Nat.lt_trans hk hi) hkeq)).mpr hk2)⟩

theorem minMarkInv_mark_keep {c : CorePlusCfg} {F0 : CNF Nat} {s : CorePlusState}
    {keep : List Nat} (hcore : CorePlusCoreInv c F0 s) (hmin : MinMarkInv c s keep)
    {l : Nat} (hl : l < 2 * c.mv) (hkeep : l ∈ keep) (hfals : s.vals[l]?.getD 0#8 = 0xFF#8)
    (hz : s.mrk[l / 2]?.getD 0#8 = 0#8) :
    MinMarkInv c (minMarkState c s (l / 2) 2#8) keep := by
  let v := l / 2
  let s' := minMarkState c s v 2#8; change MinMarkInv c s' keep
  have hlen := hcore.lengths
  have hv : v < c.mv := by omega
  have hmono : ∀ w < c.mv, s.mrk[w]?.getD 0#8 = 2#8 → s'.mrk[w]?.getD 0#8 = 2#8 := by
    intro w _ hw2
    by_cases hweq : w = v
    · subst w; rw [hz] at hw2; cases hw2
    · simp [s', minMarkState, List.getElem?_set_ne (Ne.symm hweq), hw2]
  refine ⟨fun w hw => ?_, clr_cov_mark_step hmin.clr_cov hv hlen.min_clr_len_arr 2#8,
    fun idx hi h2 => ?_⟩
  · by_cases hweq : w = v
    · subst w; right; left
      simp [s', minMarkState, List.getElem?_set_self (by rw [hlen.mrk_len]; omega)]
    · simp only [s', minMarkState, List.getElem?_set_ne (Ne.symm hweq)]; exact hmin.mrk_dom w hw
  · have hi' : idx < s.trail_end := hi
    by_cases hveq : (s.trl[idx]?.getD 0#32).toNat / 2 = v
    · obtain ⟨k, hk, hkeq⟩ := (hcore.vals_false_iff l hl).mp hfals
      have hk_idx : k = idx := hcore.trail_vars_nodup k idx hk hi' (by
        rw [hkeq, show (l ^^^ 1) / 2 = v from litVar_litNeg l, hveq])
      subst hk_idx
      have hpeq : (s.trl[k]?.getD 0#32).toNat ^^^ 1 = l := by
        rw [hkeq]; exact litNeg_litNeg l
      exact Or.inl (by dsimp only [s', minMarkState]; rwa [hpeq])
    · have h2' : s.mrk[(s.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#8 = 2#8 := by
        simpa [s', minMarkState, List.getElem?_set_ne (Ne.symm hveq)] using h2
      rcases hmin.rem_sound idx hi' h2' with hin | ⟨hne, hrc, hall⟩
      · exact Or.inl hin
      · refine Or.inr ⟨hne, hrc, fun q hq => ?_⟩
        rcases hall q hq with rfl | ⟨k, hk, hkeq, hdep⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨k, hk, hkeq, hdep.elim Or.inl fun hk2 =>
            Or.inr (hmono _ (trail_xor_var_lt hcore (Nat.lt_trans hk hi') hkeq) hk2)⟩

theorem minMarkInv_mark_rem {c : CorePlusCfg} {F0 : CNF Nat} {s : CorePlusState}
    {keep : List Nat} (hcore : CorePlusCoreInv c F0 s) (hmin : MinMarkInv c s keep)
    {idx0 : Nat} (hi0 : idx0 < s.trail_end)
    (hz : s.mrk[(s.trl[idx0]?.getD 0#32).toNat / 2]?.getD 0#8 = 0#8)
    (hrsn : let p0 := (s.trl[idx0]?.getD 0#32).toNat
      let rsn := s.rsns[p0 / 2]?.getD 0xFFFFFFFF#32
      rsn ≠ 0xFFFFFFFF#32 ∧ rsn.toNat < s.num_clauses ∧
      ∀ q ∈ clauseLits s rsn.toNat,
        q = p0 ∨ ∃ k < idx0, (s.trl[k]?.getD 0#32).toNat = q ^^^ 1 ∧
          ((s.lvl[q / 2]?.getD 0#32).toNat = 0 ∨ s.mrk[q / 2]?.getD 0#8 = 2#8)) :
    MinMarkInv c (minMarkState c s ((s.trl[idx0]?.getD 0#32).toNat / 2) 2#8) keep := by
  let v := (s.trl[idx0]?.getD 0#32).toNat / 2
  let s' := minMarkState c s v 2#8; change MinMarkInv c s' keep
  have hlen := hcore.lengths
  have hv : v < c.mv := by have := hcore.trail_lits_lt idx0 hi0; omega
  have hmono : ∀ w < c.mv, s.mrk[w]?.getD 0#8 = 2#8 → s'.mrk[w]?.getD 0#8 = 2#8 := by
    intro w _ hw2
    by_cases hweq : w = v
    · subst w; rw [hz] at hw2; cases hw2
    · simp [s', minMarkState, List.getElem?_set_ne (Ne.symm hweq), hw2]
  refine ⟨fun w hw => ?_, clr_cov_mark_step hmin.clr_cov hv hlen.min_clr_len_arr 2#8,
    fun idx hi h2 => ?_⟩
  · by_cases hweq : w = v
    · subst w; right; left
      simp [s', minMarkState, List.getElem?_set_self (by rw [hlen.mrk_len]; omega)]
    · simp only [s', minMarkState, List.getElem?_set_ne (Ne.symm hweq)]; exact hmin.mrk_dom w hw
  · have hi' : idx < s.trail_end := hi
    by_cases hveq : (s.trl[idx]?.getD 0#32).toNat / 2 = v
    · have hidx : idx = idx0 := hcore.trail_vars_nodup idx idx0 hi' hi0 hveq
      subst hidx
      obtain ⟨hne, hrc, hall⟩ := hrsn
      refine Or.inr ⟨hne, hrc, fun q hq => ?_⟩
      rcases hall q hq with rfl | ⟨k, hk, hkeq, hdep⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨k, hk, hkeq, hdep.elim Or.inl fun hk2 =>
          Or.inr (hmono _ (trail_xor_var_lt hcore (Nat.lt_trans hk hi0) hkeq) hk2)⟩
    · have h2' : s.mrk[(s.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#8 = 2#8 := by
        simpa [s', minMarkState, List.getElem?_set_ne (Ne.symm hveq)] using h2
      rcases hmin.rem_sound idx hi' h2' with hin | ⟨hne, hrc, hall⟩
      · exact Or.inl hin
      · refine Or.inr ⟨hne, hrc, fun q hq => ?_⟩
        rcases hall q hq with rfl | ⟨k, hk, hkeq, hdep⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨k, hk, hkeq, hdep.elim Or.inl fun hk2 =>
            Or.inr (hmono _ (trail_xor_var_lt hcore (Nat.lt_trans hk hi') hkeq) hk2)⟩

theorem minMarkInv_drop {c : CorePlusCfg} {F0 : CNF Nat} {s : CorePlusState}
    {keep keep' : List Nat} (hcore : CorePlusCoreInv c F0 s) (hmin : MinMarkInv c s keep)
    {root_lit : Nat} (hsub : ∀ l ∈ keep, l = root_lit ∨ l ∈ keep')
    {idx0 : Nat} (hi0 : idx0 < s.trail_end)
    (hroot : (s.trl[idx0]?.getD 0#32).toNat = root_lit ^^^ 1)
    (hrsn : let p0 := root_lit ^^^ 1
      let rsn := s.rsns[p0 / 2]?.getD 0xFFFFFFFF#32
      rsn ≠ 0xFFFFFFFF#32 ∧ rsn.toNat < s.num_clauses ∧
      ∀ q ∈ clauseLits s rsn.toNat,
        q = p0 ∨ ∃ k < idx0, (s.trl[k]?.getD 0#32).toNat = q ^^^ 1 ∧
          ((s.lvl[q / 2]?.getD 0#32).toNat = 0 ∨ s.mrk[q / 2]?.getD 0#8 = 2#8)) :
    MinMarkInv c s keep' := by
  refine ⟨hmin.mrk_dom, hmin.clr_cov, fun idx hi h2 => ?_⟩
  rcases hmin.rem_sound idx hi h2 with hin | hok
  · rcases hsub _ hin with heq | hin'
    · have hv_eq : (s.trl[idx]?.getD 0#32).toNat / 2 = (s.trl[idx0]?.getD 0#32).toNat / 2 := by
        rw [hroot]
        have h1 : ((s.trl[idx]?.getD 0#32).toNat ^^^ 1) / 2 =
            (s.trl[idx]?.getD 0#32).toNat / 2 := litVar_litNeg _
        have h2' : (root_lit ^^^ 1) / 2 = root_lit / 2 := litVar_litNeg _
        rw [← h1, heq, h2']
      have hidx : idx = idx0 := hcore.trail_vars_nodup idx idx0 hi hi0 hv_eq
      subst hidx; rw [hroot]; exact Or.inr hrsn
    · exact Or.inl hin'
  · exact Or.inr hok

private theorem trail_lit_false_strong {c : CorePlusCfg} {F0 : CNF Nat} {s : CorePlusState}
    {keep : List Nat} (hcore : CorePlusCoreInv c F0 s) (hmin : MinMarkInv c s keep)
    (α : Nat → Bool) (hα : F0.Sat α)
    (hkeep_false : ∀ l ∈ keep, α (litVar l) ≠ !(litSign l)) :
    ∀ i < s.trail_end,
      let p := (s.trl[i]?.getD 0#32).toNat
      (s.lvl[p / 2]?.getD 0#32).toNat = 0 ∨ s.mrk[p / 2]?.getD 0#8 = 2#8 →
      α (litVar p) = !(litSign p) := by
  intro i hi p hcond
  rcases hcond with hl0 | hrem
  · exact (sat_cnfClause_singleton α p).mp
      (CNF.entails_clause_def.mp (hcore.level0_sound i hi hl0) α hα)
  · rcases hmin.rem_sound i hi hrem with hin | ⟨_, hrc, hall⟩
    · have hf := hkeep_false _ hin
      have hv : litVar (p ^^^ 1) = litVar p := litVar_litNeg p
      have hs : litSign (p ^^^ 1) = !(litSign p) := litSign_litNeg p
      rw [hv, hs] at hf; cases h1 : α (litVar p) <;> cases h2 : litSign p <;> simp_all
    · have hcl_sat := CNF.entails_clause_def.mp (hcore.clauses.entails _ hrc) α hα
      obtain ⟨q, hq, hqsat⟩ := (clause_sat_cnfClause_iff α _).mp hcl_sat
      rcases hall q hq with rfl | ⟨k, hk, hkeq, hkcond⟩
      · exact hqsat
      · have hkq : (s.trl[k]?.getD 0#32).toNat / 2 = q / 2 := by rw [hkeq]; exact litVar_litNeg q
        have hkf := trail_lit_false_strong hcore hmin α hα hkeep_false k
          (Nat.lt_trans hk hi) (by rw [hkq]; exact hkcond)
        have hv : litVar (q ^^^ 1) = litVar q := litVar_litNeg q
        have hs : litSign (q ^^^ 1) = !(litSign q) := litSign_litNeg q
        rw [hkeq, hv, hs] at hkf
        cases h1 : α (litVar q) <;> cases h2 : litSign q <;> simp_all
termination_by i => i

/-- Soundness of clause minimization via `MinMarkInv`: if every literal of `orig` is falsified
and either kept in `keep` or marked `REMOVABLE` (`2#8`), then `F0` still entails `keep`. -/
theorem entails_of_minMarkInv {c : CorePlusCfg} {F0 : CNF Nat} {s : CorePlusState}
    {orig keep : List Nat} (hcore : CorePlusCoreInv c F0 s) (hmin : MinMarkInv c s keep)
    (horig : F0.EntailsClause (cnfClause orig))
    (hspec : ∀ l ∈ orig, l < 2 * c.mv ∧ s.vals[l]?.getD 0#8 = 0xFF#8 ∧
      (l ∈ keep ∨ s.mrk[l / 2]?.getD 0#8 = 2#8)) :
    F0.EntailsClause (cnfClause keep) := by
  rw [CNF.entails_clause_def] at horig ⊢
  intro α hα
  by_cases hsat : (keep.any fun l => α (litVar l) == !(litSign l)) = true
  · obtain ⟨l, hl, hlt⟩ := List.any_eq_true.mp hsat
    exact (clause_sat_cnfClause_iff α keep).mpr ⟨l, hl, beq_iff_eq.mp hlt⟩
  · exfalso
    have hkeep_false : ∀ l ∈ keep, α (litVar l) ≠ !(litSign l) := fun l hl heq =>
      hsat (List.any_eq_true.mpr ⟨l, hl, beq_iff_eq.mpr heq⟩)
    obtain ⟨l, hl, hlsat⟩ := (clause_sat_cnfClause_iff α orig).mp (horig α hα)
    obtain ⟨hlt, hfals, hkm⟩ := hspec l hl
    rcases hkm with hin | hmrk
    · exact hkeep_false l hin hlsat
    · obtain ⟨i, hi, hieq⟩ := (hcore.vals_false_iff l hlt).mp hfals
      have hvar : (s.trl[i]?.getD 0#32).toNat / 2 = l / 2 := by
        rw [hieq]; exact litVar_litNeg l
      have htf := trail_lit_false_strong hcore hmin α hα hkeep_false i hi
        (Or.inr (by rw [hvar]; exact hmrk))
      have hv : litVar (l ^^^ 1) = litVar l := litVar_litNeg l
      have hs : litSign (l ^^^ 1) = !(litSign l) := litSign_litNeg l
      rw [hieq, hv, hs, hlsat] at htf
      cases hls : litSign l <;> simp_all

/-! ## 3. Unit-witness traces and pure DIMACS / CNF helpers -/

theorem kissatLitToDimacsLiteral_inj {l1 l2 : Nat}
    (h : kissatLitToDimacsLiteral l1 = kissatLitToDimacsLiteral l2) : l1 = l2 := by
  unfold kissatLitToDimacsLiteral litVar litSign at h
  simp only [Prod.mk.injEq, Bool.not_inj_iff] at h
  rcases h with ⟨hv, hs⟩
  rcases Nat.mod_two_eq_zero_or_one l1 with h1 | h1 <;>
    rcases Nat.mod_two_eq_zero_or_one l2 with h2 | h2 <;> simp [h1, h2] at hs <;> omega

/-- Deterministic unit-only SAT trace (all clauses are unit-assigning and non-conflicting). -/
inductive UnitSatTrace (mv : Nat) : List (BitVec 8) → Nat → List UInt8 → Nat →
    List (BitVec 8) → Nat → Prop where
  | done {vals te bs} :
      (skipWsComments bs).isEmpty = true →
      UnitSatTrace mv vals te bs 0 vals te
  | step {vals te bs l rest k vals' te'} :
      l < 2 * mv →
      parseClause mv bs = some (CNF.Clause.ofLiterals [kissatLitToDimacsLiteral l], rest) →
      vals[l]?.getD 0#8 = 0#8 →
      UnitSatTrace mv ((vals.set l 1#8).set (l ^^^ 1) 0xFF#8) (te + 1) rest k vals' te' →
      UnitSatTrace mv vals te bs (k + 1) vals' te'

/-- Deterministic unit-only UNSAT trace (unit prefix ending in a unit conflict, valid tail). -/
inductive UnitUnsatTrace (mv : Nat) : List (BitVec 8) → List UInt8 → Nat → Prop where
  | conflict {vals bs l rest k} :
      l < 2 * mv →
      parseClause mv bs = some (CNF.Clause.ofLiterals [kissatLitToDimacsLiteral l], rest) →
      vals[l]?.getD 0#8 = 0xFF#8 →
      (∃ cnf, parseClauses mv k CNF.empty rest = some cnf) →
      UnitUnsatTrace mv vals bs (k + 1)
  | step {vals bs l rest k} :
      l < 2 * mv →
      parseClause mv bs = some (CNF.Clause.ofLiterals [kissatLitToDimacsLiteral l], rest) →
      vals[l]?.getD 0#8 = 0#8 →
      UnitUnsatTrace mv ((vals.set l 1#8).set (l ^^^ 1) 0xFF#8) rest k →
      UnitUnsatTrace mv vals bs (k + 1)

theorem parseClauses_some_of_acc {mv k : Nat} {bs : List UInt8}
    {acc1 acc2 cnf1 : CNF Nat}
    (h : parseClauses mv k acc1 bs = some cnf1) :
    ∃ cnf2, parseClauses mv k acc2 bs = some cnf2 := by
  induction k generalizing bs acc1 acc2 with
  | zero =>
    simp only [parseClauses] at h ⊢
    split at h
    · exact ⟨acc2, by simp_all⟩
    · cases h
  | succ k ih =>
    simp only [parseClauses] at h ⊢
    cases hpc : parseClause mv bs with
    | none => rw [hpc] at h; cases h
    | some p =>
      rcases p with ⟨cl, rest⟩
      rw [hpc] at h
      exact ih h

theorem cnf_unsat_add {F : CNF Nat} {cl : CNF.Clause Nat}
    (hu : F.Unsat) : (F.add cl).Unsat := by
  rw [CNF.unsat_iff_not_sat] at hu ⊢
  intro α hα; exact hu α (CNF.sat_add.mp hα).2

end LeanQbe.T.Examples.Kissat.CorePlus
