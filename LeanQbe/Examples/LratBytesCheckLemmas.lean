module

public import LeanQbe.Examples.LratBytesSpec
import all Kraken.Mem
import all Kraken.Separation

/-!
# Verification of `lbCheckPrf`, `lratCheckBytes`, and `checkPrfPure` soundness

Proves:
1. Pure LRAT proof soundness (`checkPrfAux_sound_of`, `runLratCheckBytes_sound_of`).
2. `lbCheckPrf_correct_of`: total-correctness `Func.spec` of `lbCheckPrf` against `lbCheckPrfSpec`.
3. `lratCheckBytes_exact_of`: total-correctness `Func.spec` of `lratCheckBytes` against
   `lratCheckBytesExactSpec`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.LratBytes

open Std Std.ExtHashMap Std.Sat
open Std.Tactic.BVDecide.LRAT.Internal
open Kraken.Bedrock2.Test
open LeanQbe.LratRup

/-! ## 1. Pure stream-length, fuel-invariance, and literal-validity lemmas -/

private theorem or_lt_two_pow {a b k : Nat} (ha : a < 2 ^ k) (hb : b < 2 ^ k) :
    (a ||| b) < 2 ^ k := by
  have hor : (BitVec.ofNat k a ||| BitVec.ofNat k b).toNat < 2 ^ k := BitVec.isLt _
  simpa [BitVec.toNat_or, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using hor

private theorem readLeb128Aux_props {fuel acc sh : Nat} {bs : List UInt8} {u : Nat}
    {bs' : List UInt8} (hacc : acc < 2 ^ 28) (hsh7 : sh % 7 = 0) (hsh : sh < 28)
    (h : readLeb128Aux fuel acc sh bs = some (u, bs')) :
    u < 2 ^ 28 ∧ bs'.length < bs.length ∧ bs' = bs.drop (bs.length - bs'.length) := by
  induction fuel generalizing acc sh bs with
  | zero => simp [readLeb128Aux] at h
  | succ fuel ih =>
    cases bs with
    | nil => simp [readLeb128Aux] at h
    | cons b rest =>
      simp only [readLeb128Aux] at h
      have hsh21 : sh ≤ 21 := by omega
      have hlo : ((b.toNat &&& 127) <<< sh) < 2 ^ 28 := by
        have h127 : b.toNat &&& 127 ≤ 127 := by
          have : b.toNat &&& 127 = b.toNat % 128 := Nat.and_two_pow_sub_one_eq_mod b.toNat 7
          omega
        rw [Nat.shiftLeft_eq]
        have hpow : 2 ^ sh ≤ 2 ^ 21 := Nat.pow_le_pow_right (by decide) hsh21
        have hmul := Nat.mul_le_mul h127 hpow
        omega
      have hacc2 : (acc ||| ((b.toNat &&& 127) <<< sh)) < 2 ^ 28 := or_lt_two_pow hacc hlo
      split at h
      · split at h
        · rename_i hlt28
          obtain ⟨hu, hlen, hdrop⟩ := ih hacc2 (by omega) hlt28 h
          refine ⟨hu, by simp; omega, ?_⟩
          have hd : (b :: rest).length - bs'.length = (rest.length - bs'.length) + 1 := by
            simp; omega
          rw [hd, List.drop_succ_cons]
          exact hdrop
        · simp at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        exact ⟨hacc2, by simp, by simp⟩

private theorem readLeb128Pure_props {bs : List UInt8} {u : Nat} {bs' : List UInt8}
    (h : readLeb128Pure bs = some (u, bs')) :
    u < 2 ^ 28 ∧ bs'.length < bs.length ∧ bs' = bs.drop (bs.length - bs'.length) :=
  readLeb128Aux_props (by decide) rfl (by decide) h

private theorem drop_trans_len {full bs' : List UInt8} {idx : Nat} (hidx : idx ≤ full.length)
    (h : bs' = (full.drop idx).drop ((full.drop idx).length - bs'.length))
    (hlen : bs'.length ≤ (full.drop idx).length) :
    bs' = full.drop (full.length - bs'.length) ∧ full.length - bs'.length ≤ full.length := by
  have hfl : (full.drop idx).length = full.length - idx := List.length_drop
  rw [List.drop_drop] at h
  have heq : idx + ((full.drop idx).length - bs'.length) = full.length - bs'.length := by omega
  rw [heq] at h
  exact ⟨h, by omega⟩

private theorem readAddLitsAux_lt {fuel mv poolRem : Nat} {acc : List Val} {bs : List UInt8}
    {clits : List Val} {poolRem' : Nat} {bs' : List UInt8}
    (h : readAddLitsAux fuel mv poolRem acc bs = some (clits, poolRem', bs')) :
    bs'.length < bs.length := by
  induction fuel generalizing poolRem acc bs with
  | zero => simp [readAddLitsAux] at h
  | succ fuel ih =>
    simp only [readAddLitsAux] at h
    split at h
    · simp at h
    · split at h
      · simp at h
      · rename_i bs1 heq
        obtain ⟨_, hlt1, _⟩ := readLeb128Pure_props heq
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨_, _, rfl⟩ := h
        exact hlt1
      · rename_i u bs1 _ heq
        obtain ⟨_, hlt1, _⟩ := readLeb128Pure_props heq
        split at h
        · simp at h
        · have hlt2 := ih h
          omega

private theorem readAddLitsPure_lt {mv poolRem : Nat} {bs : List UInt8}
    {clits : List Val} {poolRem' : Nat} {bs' : List UInt8}
    (h : readAddLitsPure mv poolRem bs = some (clits, poolRem', bs')) :
    bs'.length < bs.length :=
  readAddLitsAux_lt h

private theorem consumeHintsAux_lt {fuel id : Nat} {table : List (Option (List Val))}
    {bs bs' : List UInt8} (h : consumeHintsAux fuel id table bs = some bs') :
    bs'.length < bs.length := by
  induction fuel generalizing bs with
  | zero => simp [consumeHintsAux] at h
  | succ fuel ih =>
    simp only [consumeHintsAux] at h
    split at h
    · simp at h
    · rename_i bs1 heq
      obtain ⟨_, hlt1, _⟩ := readLeb128Pure_props heq
      simp only [Option.some.injEq] at h; subst h; exact hlt1
    · rename_i u bs1 _ heq
      obtain ⟨_, hlt1, _⟩ := readLeb128Pure_props heq
      split at h
      · simp at h
      · split at h
        · split at h
          · have hlt2 := ih h; omega
          · simp at h
        · simp at h

private theorem rupPhase2Aux_lt {fuel mv id : Nat} {table : List (Option (List Val))}
    {vals : List Val} {tl : Nat} {bs bs' : List UInt8}
    (h : rupPhase2Aux fuel mv id table vals tl bs = some bs') :
    bs'.length < bs.length := by
  induction fuel generalizing vals tl bs with
  | zero => simp [rupPhase2Aux] at h
  | succ fuel ih =>
    simp only [rupPhase2Aux] at h
    split at h
    · simp at h
    · simp at h
    · rename_i u bs1 _ heq
      obtain ⟨_, hlt1, _⟩ := readLeb128Pure_props heq
      split at h
      · simp at h
      · split at h
        · split at h
          · split at h
            · simp at h
            · split at h
              · have hlt2 := ih h; omega
              · have hlt2 := consumeHintsAux_lt h; omega
          · simp at h
        · simp at h

private theorem rupCheckPure_lt {mv id : Nat} {clits : List Val}
    {table : List (Option (List Val))} {bs bs' : List UInt8}
    (h : rupCheckPure mv id clits table bs = some bs') :
    bs'.length < bs.length := by
  unfold rupCheckPure at h
  split at h
  · simp at h
  · exact consumeHintsAux_lt h
  · exact rupPhase2Aux_lt h

private theorem delLoopAux_props {fuel cap : Nat} {table : List (Option (List Val))}
    {bs : List UInt8} {table' : List (Option (List Val))} {bs' : List UInt8}
    (h : delLoopAux fuel cap table bs = some (table', bs')) :
    bs'.length < bs.length ∧ bs' = bs.drop (bs.length - bs'.length) := by
  induction fuel generalizing table bs with
  | zero => simp [delLoopAux] at h
  | succ fuel ih =>
    simp only [delLoopAux] at h
    split at h
    · simp at h
    · rename_i bs1 heq
      obtain ⟨_, hlt1, hdrop1⟩ := readLeb128Pure_props heq
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hlt1, hdrop1⟩
    · rename_i u bs1 _ heq
      obtain ⟨_, hlt1, hdrop1⟩ := readLeb128Pure_props heq
      split at h
      · simp at h
      · split at h
        · simp at h
        · split at h
          · obtain ⟨hlt2, hdrop2⟩ := ih h
            refine ⟨by omega, ?_⟩
            rw [hdrop1] at hdrop2
            exact (drop_trans_len (by omega) hdrop2 (by rw [← hdrop1]; omega)).1
          · simp at h

private theorem delLoopAux_fuel_irrel {f1 f2 cap : Nat} {table : List (Option (List Val))}
    {bs : List UInt8} (hf1 : bs.length < f1) (hf2 : bs.length < f2) :
    delLoopAux f1 cap table bs = delLoopAux f2 cap table bs := by
  induction f1 generalizing f2 table bs with
  | zero => omega
  | succ f1 ih =>
    cases f2 with
    | zero => omega
    | succ f2 =>
      simp only [delLoopAux]
      split
      · rfl
      · rfl
      · rename_i u bs1 _ heq
        obtain ⟨_, hlt1, _⟩ := readLeb128Pure_props heq
        split
        · rfl
        · split
          · rfl
          · split
            · exact ih (by omega) (by omega)
            · rfl

private theorem checkPrfAux_fuel_irrel {f1 f2 mv nc poolRem : Nat}
    {table : List (Option (List Val))} {bs : List UInt8}
    (hf1 : bs.length < f1) (hf2 : bs.length < f2) :
    checkPrfAux f1 mv nc poolRem table bs = checkPrfAux f2 mv nc poolRem table bs := by
  induction f1 generalizing f2 poolRem table bs with
  | zero => omega
  | succ f1 ih =>
    cases f2 with
    | zero => omega
    | succ f2 =>
      cases bs with
      | nil => simp [checkPrfAux]
      | cons tag bs1 =>
        have hbs1 : bs1.length < f1 ∧ bs1.length < f2 := by simp at hf1 hf2; omega
        simp only [checkPrfAux]
        split
        · split
          · rfl
          · rename_i uid bs2 heq1
            obtain ⟨_, hlt1, _⟩ := readLeb128Pure_props heq1
            split
            · rfl
            · split
              · rfl
              · split
                · split
                  · rfl
                  · rename_i clits poolRem' bs3 heq2
                    have hlt2 := readAddLitsPure_lt heq2
                    split
                    · rfl
                    · rename_i bs4 heq3
                      have hlt3 := rupCheckPure_lt heq3
                      split
                      · rfl
                      · exact ih (by omega) (by omega)
                · rfl
        · split
          · split
            · rfl
            · rename_i table' bs2 heqd
              obtain ⟨hltd, _⟩ := delLoopAux_props heqd
              exact ih (by omega) (by omega)
          · rfl

private theorem decodeZigZag_valid {u mv : Nat} (hu : u < 2 ^ 28) (hv0 : 1 ≤ u / 2)
    (hvm : u / 2 ≤ mv) (hmv : mv < dimacsBound) :
    IsValidLit mv (decodeZigZag u) := by
  unfold dimacsBound at hmv
  have hpos_valid : IsValidLit mv (BitVec.ofNat 64 (u / 2)) := by
    unfold IsValidLit bvAbs IsInt32
    grind
  unfold decodeZigZag
  split
  · exact isValidLit_neg hpos_valid
  · exact hpos_valid

private theorem readAddLitsAux_valid {fuel mv poolRem : Nat} {acc : List Val} {bs : List UInt8}
    {clits : List Val} {poolRem' : Nat} {bs' : List UInt8}
    (hmv : mv < dimacsBound) (hacc : ∀ x ∈ acc, IsValidLit mv x)
    (h : readAddLitsAux fuel mv poolRem acc bs = some (clits, poolRem', bs')) :
    ∀ x ∈ clits, IsValidLit mv x := by
  induction fuel generalizing poolRem acc bs with
  | zero => simp [readAddLitsAux] at h
  | succ fuel ih =>
    simp only [readAddLitsAux] at h
    split at h
    · simp at h
    · split at h
      · simp at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, _, _⟩ := h
        intro x hx
        exact hacc x (List.mem_reverse.mp hx)
      · rename_i u bs1 _ heq
        obtain ⟨hu, _, _⟩ := readLeb128Pure_props heq
        split at h
        · simp at h
        · rename_i hgood
          simp only [Bool.not_eq_true, Bool.or_eq_false_iff, beq_eq_false_iff_ne,
            decide_eq_false_iff_not] at hgood
          have hv_valid := decodeZigZag_valid hu (by omega) (by omega) hmv
          refine ih ?_ h
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hx'
          · exact hv_valid
          · exact hacc x hx'

private theorem readAddLitsPure_valid {mv poolRem : Nat} {bs : List UInt8}
    {clits : List Val} {poolRem' : Nat} {bs' : List UInt8}
    (hmv : mv < dimacsBound)
    (h : readAddLitsPure mv poolRem bs = some (clits, poolRem', bs')) :
    ∀ x ∈ clits, IsValidLit mv x :=
  readAddLitsAux_valid hmv (by simp) h

/-! ## 2. Pure LRAT proof soundness (`checkPrfAux_sound_of`, `runLratCheckBytes_sound_of`) -/

/-- Every active clause in `table` has valid literals in `1..mv` and is entailed by `F`. -/
abbrev TableSound (mv : Nat) (F : CNF Nat) (table : List (Option (List Val))) : Prop :=
  ∀ (i : Nat) (lits : List Val), table[i]? = some (some lits) →
    (∀ x ∈ lits, IsValidLit mv x) ∧ CNF.EntailsClause F (toClause lits)

private theorem entailsClause_add_mono {F : CNF Nat} {c d : CNF.Clause Nat}
    (h : CNF.EntailsClause F d) : CNF.EntailsClause (F.add c) d := by
  rw [CNF.entails_clause_def] at h ⊢
  intro a ha
  rw [CNF.sat_def, CNF.eval_add, Bool.and_eq_true] at ha
  exact h a ((CNF.sat_def a F).mpr ha.2)

private theorem entailsClause_add_self (F : CNF Nat) (c : CNF.Clause Nat) :
    CNF.EntailsClause (F.add c) c := by
  rw [CNF.entails_clause_def]
  intro a ha
  rw [CNF.sat_def, CNF.eval_add, Bool.and_eq_true] at ha
  exact (CNF.Clause.sat_def a c).mpr ha.1

private theorem foldl_add_entails {clauses : List (List Val)} {F : CNF Nat} {c : CNF.Clause Nat}
    (hc : CNF.EntailsClause F c) :
    CNF.EntailsClause (clauses.foldl (fun acc lits => acc.add (toClause lits)) F) c := by
  induction clauses generalizing F with
  | nil => exact hc
  | cons hd tl ih => exact ih (entailsClause_add_mono hc)

private theorem foldl_mem_entails {clauses : List (List Val)} {F : CNF Nat} {lits : List Val}
    (hmem : lits ∈ clauses) :
    CNF.EntailsClause (clauses.foldl (fun acc ls => acc.add (toClause ls)) F) (toClause lits) := by
  induction clauses generalizing F with
  | nil => nomatch hmem
  | cons hd tl ih =>
    rcases List.mem_cons.mp hmem with rfl | htl
    · exact @foldl_add_entails tl (F.add (toClause lits)) (toClause lits)
        (entailsClause_add_self F (toClause lits))
    · exact ih htl

theorem initClauseTable_sound {mv cap : Nat} {clauses : List (List Val)}
    (hvalid : ∀ cl ∈ clauses, ∀ x ∈ cl, IsValidLit mv x) :
    TableSound mv (clauses.foldl (fun acc lits => acc.add (toClause lits)) CNF.empty)
      (initClauseTable cap clauses) := by
  intro i lits hget
  unfold initClauseTable at hget
  cases i with
  | zero => simp at hget
  | succ j =>
    simp only [List.cons_append, List.getElem?_cons_succ] at hget
    by_cases hj : j < (clauses.map some).length
    · rw [List.getElem?_append_left hj, List.getElem?_eq_getElem hj, List.getElem_map] at hget
      simp only [Option.some.injEq] at hget
      subst hget
      have hj' : j < clauses.length := by simpa using hj
      have hmem := List.getElem_mem hj'
      exact ⟨hvalid _ hmem, foldl_mem_entails hmem⟩
    · rw [List.getElem?_append_right (Nat.le_of_not_lt hj)] at hget
      rw [List.getElem?_replicate] at hget
      split at hget <;> simp at hget

private theorem delLoopAux_sound {fuel cap mv : Nat} {F : CNF Nat}
    {table table' : List (Option (List Val))} {bs bs' : List UInt8}
    (ht : TableSound mv F table)
    (h : delLoopAux fuel cap table bs = some (table', bs')) :
    TableSound mv F table' := by
  induction fuel generalizing table bs with
  | zero => simp [delLoopAux] at h
  | succ fuel ih =>
    simp only [delLoopAux] at h
    split at h
    · simp at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, _⟩ := h; exact ht
    · split at h
      · simp at h
      · split at h
        · simp at h
        · split at h
          · refine ih ?_ h
            intro i lits hi
            rw [List.getElem?_set] at hi
            split at hi
            · simp at hi
            · exact ht i lits hi
          · simp at h

private theorem unsat_of_entails_empty {cnf₀ F : CNF Nat}
    (hent : cnf₀.Entails F) (hemp : CNF.EntailsClause F (toClause [])) :
    cnf₀.Unsat := by
  rw [CNF.unsat_iff_not_sat]
  intro a ha
  have hF : F.Sat a := (CNF.entails_def cnf₀ F).mp hent a ha
  have hc : (toClause []).Sat a := CNF.entails_clause_def.mp hemp a hF
  rw [CNF.Clause.sat_def] at hc
  have hev : CNF.Clause.eval a (toClause []) = false := by
    have hem : toClause [] = CNF.Clause.empty := CNF.Clause.ext (by simp [toClause])
    rw [hem]
    exact CNF.Clause.eval_empty a
  rw [hev] at hc
  cases hc

/-- Pure soundness of `checkPrfAux` given RUP step soundness `hrup_sound`. -/
theorem checkPrfAux_sound_of
    (hrup_sound : ∀ {mv id : Nat} {clits : List Val} {table : List (Option (List Val))}
      {bs bs' : List UInt8} {F : CNF Nat},
      mv < dimacsBound →
      (∀ x ∈ clits, IsValidLit mv x) →
      (∀ aid < id, ∀ alits, table[aid]? = some (some alits) →
        (∀ x ∈ alits, IsValidLit mv x) ∧ CNF.EntailsClause F (toClause alits)) →
      rupCheckPure mv id clits table bs = some bs' →
      CNF.EntailsClause F (toClause clits))
    {fuel mv nc poolRem : Nat} {table : List (Option (List Val))} {bs : List UInt8}
    {cnf₀ F : CNF Nat}
    (hmv : mv < dimacsBound)
    (hent : cnf₀.Entails F)
    (htable : TableSound mv F table)
    (hchk : checkPrfAux fuel mv nc poolRem table bs = true) :
    cnf₀.Unsat := by
  induction fuel generalizing poolRem table bs F with
  | zero => simp [checkPrfAux] at hchk
  | succ fuel ih =>
    cases bs with
    | nil => simp [checkPrfAux] at hchk
    | cons tag bs1 =>
      simp only [checkPrfAux] at hchk
      split at hchk
      · split at hchk
        · simp at hchk
        · rename_i uid bs2 heq_uid
          split at hchk
          · simp at hchk
          · split at hchk
            · simp at hchk
            · split at hchk
              · split at hchk
                · simp at hchk
                · rename_i clits poolRem' bs3 hread
                  have hclits := readAddLitsPure_valid hmv hread
                  split at hchk
                  · simp at hchk
                  · rename_i bs4 hrup
                    have hent_cl : CNF.EntailsClause F (toClause clits) :=
                      hrup_sound hmv hclits (fun aid _ alits hget => htable aid alits hget) hrup
                    split at hchk
                    · rename_i hemp
                      have hnil : clits = [] := List.isEmpty_iff.mp hemp
                      subst hnil
                      exact unsat_of_entails_empty hent hent_cl
                    · let F' := F.add (toClause clits)
                      have hent' : cnf₀.Entails F' := by
                        refine CNF.entails_trans hent ?_
                        rw [CNF.entails_add_iff]
                        exact ⟨CNF.entails_refl F, hent_cl⟩
                      have htable' : TableSound mv F' (table.set (uid / 2) (some clits)) := by
                        intro i lits hi
                        rw [List.getElem?_set] at hi
                        split at hi
                        · split at hi
                          · simp only [Option.some.injEq] at hi
                            subst hi
                            exact ⟨hclits, entailsClause_add_self F (toClause clits)⟩
                          · simp at hi
                        · obtain ⟨hv, he⟩ := htable i lits hi
                          exact ⟨hv, entailsClause_add_mono he⟩
                      exact ih hent' htable' hchk
              · simp at hchk
      · split at hchk
        · split at hchk
          · simp at hchk
          · rename_i table' bs2 hdel
            exact ih hent (delLoopAux_sound htable hdel) hchk
        · simp at hchk

private theorem parseDigitsAux_lt {acc : Nat} {bs : List UInt8} {n : Nat} {rest : List UInt8}
    (hacc : acc < dimacsBound) (h : parseDigitsAux acc bs = some (n, rest)) :
    n < dimacsBound := by
  induction bs generalizing acc with
  | nil =>
    simp [parseDigitsAux] at h
    obtain ⟨rfl, _⟩ := h
    exact hacc
  | cons b bs ih =>
    simp only [parseDigitsAux] at h
    split at h
    · split at h
      · rename_i hlt
        exact ih hlt h
      · simp at h
    · split at h
      · simp at h
        obtain ⟨rfl, _⟩ := h
        exact hacc
      · simp at h

private theorem parseNat_lt {bs : List UInt8} {n : Nat} {rest : List UInt8}
    (h : parseNat bs = some (n, rest)) : n < dimacsBound := by
  cases bs with
  | nil => simp [parseNat] at h
  | cons b bs =>
    simp only [parseNat] at h
    split at h
    · rename_i hd
      have hb : b.toNat - 48 < dimacsBound := by
        unfold isDimacsDigit at hd
        have := b.toNat_lt
        unfold dimacsBound
        omega
      exact parseDigitsAux_lt hb h
    · simp at h

theorem parseHeader_bounds {bs : List UInt8} {mv nc : Nat} {rest : List UInt8}
    (h : parseHeader bs = some (mv, nc, rest)) : mv < dimacsBound ∧ nc < dimacsBound := by
  unfold parseHeader at h
  simp only [bind, Option.bind] at h
  split at h
  · split at h
    · cases h
    · dsimp only at h
      split at h
      · rename_i bs3 _
        cases h2 : skipWs1 bs3 with
        | none => simp [h2] at h
        | some bs4 =>
          simp only [h2] at h
          cases hmv : parseNat bs4 with
          | none => simp [hmv] at h
          | some p1 =>
            rcases p1 with ⟨mv', bs5⟩
            simp only [hmv] at h
            cases h3 : skipWs1 bs5 with
            | none => simp [h3] at h
            | some bs6 =>
              simp only [h3] at h
              cases hnc : parseNat bs6 with
              | none => simp [hnc] at h
              | some p2 =>
                rcases p2 with ⟨nc', bs7⟩
                simp only [hnc, Option.some.injEq, Prod.mk.injEq] at h
                rcases h with ⟨rfl, rfl, rfl⟩
                exact ⟨parseNat_lt hmv, parseNat_lt hnc⟩
      · cases h
  · cases h

/-- Pure soundness of `runLratCheckBytes` given `parseBodyPure_sound` and `rupCheckPure_sound`. -/
theorem runLratCheckBytes_sound_of
    (hbody_sound : ∀ {cnfBytes bodyRest : List UInt8} {mv nc poolInts poolRem' : Nat}
      {clauses : List (List Val)},
      parseHeader cnfBytes = some (mv, nc, bodyRest) →
      mv < dimacsBound →
      parseBodyPure mv nc poolInts [] bodyRest = some (clauses, poolRem') →
      parseDimacs cnfBytes =
        some (clauses.foldl (fun c lits => c.add (toClause lits)) CNF.empty) ∧
      clauses.length = nc ∧
      (∀ cl ∈ clauses, ∀ x ∈ cl, IsValidLit mv x))
    (hrup_sound : ∀ {mv id : Nat} {clits : List Val} {table : List (Option (List Val))}
      {bs bs' : List UInt8} {F : CNF Nat},
      mv < dimacsBound →
      (∀ x ∈ clits, IsValidLit mv x) →
      (∀ aid < id, ∀ alits, table[aid]? = some (some alits) →
        (∀ x ∈ alits, IsValidLit mv x) ∧ CNF.EntailsClause F (toClause alits)) →
      rupCheckPure mv id clits table bs = some bs' →
      CNF.EntailsClause F (toClause clits))
    {cnfBytes prfBytes : List UInt8} {work_len : Nat}
    (hrun : runLratCheckBytes cnfBytes prfBytes work_len = true) :
    ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat := by
  unfold runLratCheckBytes at hrun
  split at hrun
  · simp at hrun
  · split at hrun
    · simp at hrun
    · rename_i mv nc bodyRest hhdr
      have hmv := (parseHeader_bounds hhdr).1
      dsimp only at hrun
      split at hrun
      · simp at hrun
      · let fixed := 80 + ((mv + 8) / 8) * 8 + ((4 * (mv + 1) + 7) / 8) * 8
        let rem := work_len - fixed
        let c_half := rem / 16
        let want := nc + prfBytes.length % 268435456 + 32
        let cap := if c_half < want then c_half else want
        change (if cap ≤ nc then false else
          match parseBodyPure mv nc ((rem - 8 * cap) / 4) [] bodyRest with
          | none => false
          | some (clauses, pool_ints') =>
            checkPrfPure mv nc pool_ints' (initClauseTable cap clauses) prfBytes) = true at hrun
        split at hrun
        · simp at hrun
        · split at hrun
          · simp at hrun
          · rename_i clauses pool_ints' hbody
            obtain ⟨hdimacs, _, hcl_valid⟩ := hbody_sound hhdr hmv hbody
            let cnf₀ := clauses.foldl (fun c lits => c.add (toClause lits)) CNF.empty
            have hunsat : cnf₀.Unsat :=
              checkPrfAux_sound_of hrup_sound hmv (CNF.entails_refl cnf₀)
                (initClauseTable_sound hcl_valid) hrun
            exact ⟨cnf₀, hdimacs, hunsat⟩

/-! ## 3. WP lemma for `readLeb128` -/

private theorem check_readLeb128_spec {Γ : Env} {Q : Post} {X : XPost} {fail : Cont}
    {base : Val} {bs : List UInt8} {idx0 : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    {done : Val → Val → Expr Val Cont}
    (hbound : base.toNat + bs.length < 2 ^ 64)
    (hidx0 : idx0 ≤ bs.length)
    (hm : (Eq (bs.At base) ⋆ R) m)
    (hfail : readLeb128Pure (bs.drop idx0) = none → fail [] m)
    (hdone : ∀ (u : Nat) (bs' : List UInt8),
      readLeb128Pure (bs.drop idx0) = some (u, bs') →
      u < 2 ^ 28 →
      bs' = bs.drop (bs.length - bs'.length) →
      bs.length - bs'.length ≤ bs.length →
      idx0 < bs.length - bs'.length →
      wp Γ Q X (done (BitVec.ofNat 64 u) (base + BitVec.ofNat 64 (bs.length - bs'.length))) [] [] m) :
    wp Γ Q X (readLeb128 fail (base + BitVec.ofNat 64 idx0) (base + BitVec.ofNat 64 bs.length) done) [] [] m := by
  unfold readLeb128
  apply wp_join (fun as m' => ∃ (u : Nat) (bs' : List UInt8),
    as = [BitVec.ofNat 64 u, base + BitVec.ofNat 64 (bs.length - bs'.length)] ∧
    m' = m ∧
    readLeb128Pure (bs.drop idx0) = some (u, bs') ∧
    u < 2 ^ 28 ∧
    bs' = bs.drop (bs.length - bs'.length) ∧
    bs.length - bs'.length ≤ bs.length ∧
    idx0 < bs.length - bs'.length)
  · rintro _ _ ⟨u, bs', rfl, rfl, hpure, hu, hdrop, hle, hgt⟩
    wp_unfold
    exact hdone u bs' hpure hu hdrop hle hgt
  intro Jdone hJdone
  apply wp_loop (fun r as m' => ∃ (k idx acc : Nat),
    k < 4 ∧ r = 4 - k ∧
    idx = idx0 + k ∧ idx ≤ bs.length ∧
    acc < 2 ^ 28 ∧
    m' = m ∧
    as = [base + BitVec.ofNat 64 idx, BitVec.ofNat 64 acc, BitVec.ofNat 64 (7 * k)] ∧
    readLeb128Pure (bs.drop idx0) = readLeb128Aux (4 - k) acc (7 * k) (bs.drop idx))
  · rintro Jleb r as m' ⟨k, idx, acc, hk4, rfl, hidx_eq, hidx_le, hacc, rfl, rfl, heq_pure⟩ ih
    have hfuel : 4 - k = (3 - k) + 1 := by omega
    wp_unfold
    refine ⟨fun heof => ?_, fun hneof => ?_⟩
    · have hidx_end : idx = bs.length := by
        have := congrArg (fun x => (x - base).toNat) heof
        simp [BitVec.add_comm base, Nat.mod_eq_of_lt (by omega : idx < 2 ^ 64),
          Nat.mod_eq_of_lt (by omega : bs.length < 2 ^ 64)] at this
        omega
      subst hidx_end
      apply hfail
      rw [heq_pure, hfuel, List.drop_length]
      rfl
    · have hidx_lt : idx < bs.length := by
        rcases Nat.eq_or_lt_of_le hidx_le with rfl | h
        · exact absurd rfl hneof
        · exact h
      have hld := loadub_At hidx_lt (by omega) hm
      refine ⟨_, hld, ?_⟩
      have hdrop_cons : bs.drop idx = bs[idx] :: bs.drop (idx + 1) :=
        List.drop_eq_getElem_cons hidx_lt
      have hb_lt : bs[idx].toNat < 256 := bs[idx].toNat_lt
      let lo_nat := bs[idx].toNat &&& 127
      have hlo_le : lo_nat ≤ 127 := by
        have : bs[idx].toNat &&& 127 = bs[idx].toNat % 128 :=
          Nat.and_two_pow_sub_one_eq_mod bs[idx].toNat 7
        dsimp [lo_nat]; omega
      have hlo_bv : BitVec.ofNat 64 bs[idx].toNat &&& (127 : Val) = BitVec.ofNat 64 lo_nat := by
        apply BitVec.eq_of_toNat_eq
        simp [lo_nat, BitVec.toNat_and, Nat.mod_eq_of_lt (by omega : bs[idx].toNat < 2 ^ 64)]
      have hsh_lt : lo_nat <<< (7 * k) < 2 ^ 28 := by
        rw [Nat.shiftLeft_eq]
        have hpow : 2 ^ (7 * k) ≤ 2 ^ 21 := Nat.pow_le_pow_right (by decide) (by omega)
        have hmul := Nat.mul_le_mul hlo_le hpow
        omega
      have hsl_bv : BitVec.ofNat 64 lo_nat <<< ((BitVec.ofNat 64 (7 * k)).toNat % 64) =
          BitVec.ofNat 64 (lo_nat <<< (7 * k)) := by
        have hmod : (BitVec.ofNat 64 (7 * k)).toNat % 64 = 7 * k := by
          simp [Nat.mod_eq_of_lt (by omega : 7 * k < 2 ^ 64),
            Nat.mod_eq_of_lt (by omega : 7 * k < 64)]
        rw [hmod]
        apply BitVec.eq_of_toNat_eq
        simp [BitVec.toNat_shiftLeft, Nat.mod_eq_of_lt (by omega : lo_nat < 2 ^ 64),
          Nat.mod_eq_of_lt (by omega : lo_nat <<< (7 * k) < 2 ^ 64)]
      let acc2 := acc ||| (lo_nat <<< (7 * k))
      have hacc2_lt : acc2 < 2 ^ 28 := or_lt_two_pow hacc hsh_lt
      have hacc2_bv : BitVec.ofNat 64 acc ||| BitVec.ofNat 64 (lo_nat <<< (7 * k)) =
          BitVec.ofNat 64 acc2 := by
        apply BitVec.eq_of_toNat_eq
        simp [acc2, BitVec.toNat_or, Nat.mod_eq_of_lt (by omega : acc < 2 ^ 64),
          Nat.mod_eq_of_lt (by omega : lo_nat <<< (7 * k) < 2 ^ 64)]
      have hhi_bv : (BitVec.ofNat 64 bs[idx].toNat &&& (128 : Val) ≠ (0 : Val)) ↔
          ((bs[idx].toNat &&& 128) != 0) = true := by
        rw [bne_iff_ne]
        constructor
        · intro hne heq0
          apply hne
          apply BitVec.eq_of_toNat_eq
          simp [BitVec.toNat_and, Nat.mod_eq_of_lt (by omega : bs[idx].toNat < 2 ^ 64), heq0]
        · intro hne heq0
          apply hne
          have := congrArg BitVec.toNat heq0
          simpa [BitVec.toNat_and, Nat.mod_eq_of_lt (by omega : bs[idx].toNat < 2 ^ 64)] using this
      have hp1 : base + BitVec.ofNat 64 idx + (1 : Val) = base + BitVec.ofNat 64 (idx + 1) := by
        apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]; omega
      rw [hlo_bv, hsl_bv, hacc2_bv, hp1]
      refine ⟨fun hmore => ?_, fun hnmore => ?_⟩
      · have hmore' : ((bs[idx].toNat &&& 128) != 0) = true := hhi_bv.mp hmore
        have hsh2 : BitVec.ofNat 64 (7 * k) + (7 : Val) = BitVec.ofNat 64 (7 * (k + 1)) := by
          apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]; omega
        rw [hsh2]
        have hult28 : (BitVec.ofNat 64 (7 * (k + 1))).ult (28 : Val) = true ↔ 7 * (k + 1) < 28 := by
          simp [BitVec.ult, Nat.mod_eq_of_lt (by omega : 7 * (k + 1) < 2 ^ 64)]
        refine ⟨fun hoksh => ?_, fun hbadsh => ?_⟩
        · have hk_next : 7 * (k + 1) < 28 := hult28.mp hoksh
          refine ih (4 - (k + 1)) _ _ (by omega)
            ⟨k + 1, idx + 1, acc2, by omega, rfl, by omega, hidx_lt, hacc2_lt, rfl, rfl, ?_⟩
          rw [heq_pure, hfuel, hdrop_cons]
          have h3k : 3 - k = 4 - (k + 1) := by omega
          have h7 : 7 * k + 7 = 7 * (k + 1) := by omega
          simp only [readLeb128Aux, hmore', ↓reduceIte, h7, hk_next, acc2, lo_nat, h3k]
        · have hk_bad : ¬ (7 * (k + 1) < 28) := by
            intro h; rw [hult28.mpr h] at hbadsh; cases hbadsh
          apply hfail
          rw [heq_pure, hfuel, hdrop_cons]
          have h7 : 7 * k + 7 = 7 * (k + 1) := by omega
          simp only [readLeb128Aux, hmore', ↓reduceIte, h7, hk_bad]
      · have hnmore' : ((bs[idx].toNat &&& 128) != 0) = false := by
          cases hb : (bs[idx].toNat &&& 128) != 0
          · rfl
          · exact absurd (hhi_bv.mpr hb) hnmore
        let bs' := bs.drop (idx + 1)
        have hpure_eq : readLeb128Pure (bs.drop idx0) = some (acc2, bs') := by
          rw [heq_pure, hfuel, hdrop_cons]
          simp [readLeb128Aux, hnmore', acc2, lo_nat, bs']
        have hbs'_len : bs.length - bs'.length = idx + 1 := by
          simp [bs', List.length_drop]; omega
        refine hJdone _ _ ⟨acc2, bs', ?_, rfl, hpure_eq, hacc2_lt, ?_, by omega, by omega⟩
        · rw [hbs'_len]
        · rw [hbs'_len]
  · intro Jleb hJleb
    wp_unfold
    exact hJleb 4 _ _ ⟨0, idx0, 0, by decide, rfl, by omega, hidx0, by decide, rfl, rfl, rfl⟩

/-! ## 4. `WorkState` accessors and verification of `lbCheckPrf` -/

private theorem workState_collapse {B R : Mem 64 → Prop} {c : WorkCfg}
    {poolUsed poolRem : Nat} {cur : Val} {ptrs : List Val} {table : List (Option (List Val))}
    {PoolUsed : Mem 64 → Prop} {m : Mem 64}
    (hm : (B ⋆ WorkState c poolUsed poolRem cur ptrs table PoolUsed ⋆ R) m) :
    (B ⋆ region c.hdr c.activeBytes ⋆ R) m :=
  sep_mono2 (sep_mono2 (fun _ h => h) fun _ => WorkState.to_region) (fun _ h => h) m hm

private theorem workState_tableRel {B R : Mem 64 → Prop} {c : WorkCfg}
    {poolUsed poolRem : Nat} {cur : Val} {ptrs : List Val} {table : List (Option (List Val))}
    {PoolUsed : Mem 64 → Prop} {m : Mem 64}
    (hm : (B ⋆ WorkState c poolUsed poolRem cur ptrs table PoolUsed ⋆ R) m) :
    TableRel c.mv c.cap ptrs table PoolUsed := by
  obtain ⟨_, _, _, _, ⟨_, _, _, _, _, ⟨_, htr, _, _⟩⟩, _⟩ := hm
  exact htr

private theorem workState_load_hdr {B R : Mem 64 → Prop} {c : WorkCfg}
    {poolUsed poolRem : Nat} {cur a : Val} {ptrs : List Val} {table : List (Option (List Val))}
    {PoolUsed : Mem 64 → Prop} {m : Mem 64} (i : Nat) (hi : i < 10)
    (ha : a = c.hdr + BitVec.ofNat 64 (8 * i))
    (hm : (B ⋆ WorkState c poolUsed poolRem cur ptrs table PoolUsed ⋆ R) m) :
    loadVal m .l .l true a =
      some ((c.hdrWords (c.pbase + BitVec.ofNat 64 (4 * poolUsed)) cur)[i]'(by
        simpa [WorkCfg.hdrWords] using hi)) := by
  subst ha
  obtain ⟨f_bw, f_r, hu1, hd1, ⟨f_b, f_w, hu2, hd2, hb, ⟨_, _, _, hwm⟩⟩, hr⟩ := hm
  dsimp only at hwm
  let pcur := c.pbase + BitVec.ofNat 64 (4 * poolUsed)
  have hfocus : (word8Array c.hdr (c.hdrWords pcur cur) ⋆
      (B ⋆ (byte1Array c.vb (assignBytes c.mv Assignment.empty) ⋆
        region (c.vb + BitVec.ofNat 64 (c.mv + 1)) (c.vBytes - (c.mv + 1)) ⋆
        region c.tb c.tRaw ⋆
        region c.tlim (c.tBytes - c.tRaw) ⋆
        word8Array c.cb ptrs ⋆
        PoolUsed ⋆
        region pcur (4 * poolRem)) ⋆ R)) m := by
    have hfull : (B ⋆ (word8Array c.hdr (c.hdrWords pcur cur) ⋆
        (byte1Array c.vb (assignBytes c.mv Assignment.empty) ⋆
          region (c.vb + BitVec.ofNat 64 (c.mv + 1)) (c.vBytes - (c.mv + 1)) ⋆
          region c.tb c.tRaw ⋆
          region c.tlim (c.tBytes - c.tRaw) ⋆
          word8Array c.cb ptrs ⋆
          PoolUsed ⋆
          region pcur (4 * poolRem))) ⋆ R) m :=
      ⟨f_bw, f_r, hu1, hd1, ⟨f_b, f_w, hu2, hd2, hb, sep_cast hwm (by dsimp [pcur]; ac_rfl)⟩, hr⟩
    exact sep_cast hfull (by ac_rfl)
  exact loadl_word8Array (by simpa [WorkCfg.hdrWords] using hi) hfocus

private theorem workState_store_cur {B R : Mem 64 → Prop} {c : WorkCfg}
    {poolUsed poolRem : Nat} {cur cur' : Val} {ptrs : List Val} {table : List (Option (List Val))}
    {PoolUsed : Mem 64 → Prop} {m : Mem 64}
    (hm : (B ⋆ WorkState c poolUsed poolRem cur ptrs table PoolUsed ⋆ R) m) :
    storeOk m .l (c.hdr + 72) ∧
      (B ⋆ WorkState c poolUsed poolRem cur' ptrs table PoolUsed ⋆ R)
        (storeMem m .l (c.hdr + 72) cur') := by
  obtain ⟨f_bw, f_r, hu1, hd1, ⟨f_b, f_w, hu2, hd2, hb, ⟨hsum, htr, hpu, hwm⟩⟩, hr⟩ := hm
  dsimp only at hwm
  let pcur := c.pbase + BitVec.ofNat 64 (4 * poolUsed)
  let WRest := byte1Array c.vb (assignBytes c.mv Assignment.empty) ⋆
    region (c.vb + BitVec.ofNat 64 (c.mv + 1)) (c.vBytes - (c.mv + 1)) ⋆
    region c.tb c.tRaw ⋆
    region c.tlim (c.tBytes - c.tRaw) ⋆
    word8Array c.cb ptrs ⋆
    PoolUsed ⋆
    region pcur (4 * poolRem)
  have hfocus : (word8Array c.hdr (c.hdrWords pcur cur) ⋆ (B ⋆ WRest ⋆ R)) m := by
    have hfull : (B ⋆ (word8Array c.hdr (c.hdrWords pcur cur) ⋆ WRest) ⋆ R) m :=
      ⟨f_bw, f_r, hu1, hd1, ⟨f_b, f_w, hu2, hd2, hb,
        sep_cast hwm (by dsimp [WRest, pcur]; ac_rfl)⟩, hr⟩
    exact sep_cast hfull (by ac_rfl)
  have h72 : c.hdr + (72 : Val) = c.hdr + BitVec.ofNat 64 (8 * 9) := rfl
  rw [h72]
  obtain ⟨hok, hm1⟩ := storel_word8Array (i := 9) cur' (by simp [WorkCfg.hdrWords]) hfocus
  have hset : (c.hdrWords pcur cur).set 9 cur' = c.hdrWords pcur cur' := rfl
  rw [hset] at hm1
  have hm2 : (B ⋆ (word8Array c.hdr (c.hdrWords pcur cur') ⋆ WRest) ⋆ R)
      (storeMem m .l (c.hdr + BitVec.ofNat 64 (8 * 9)) cur') :=
    sep_cast hm1 (by ac_rfl)
  obtain ⟨g_bw, g_r, gu1, gd1, ⟨g_b, g_w, gu2, gd2, gb, gwm⟩, gr⟩ := hm2
  refine ⟨hok, g_bw, g_r, gu1, gd1, ⟨g_b, g_w, gu2, gd2, gb, ⟨hsum, htr, hpu, ?_⟩⟩, gr⟩
  dsimp only
  exact sep_cast gwm (by dsimp [WRest, pcur]; ac_rfl)

private theorem workState_load_cb {B R : Mem 64 → Prop} {c : WorkCfg}
    {poolUsed poolRem : Nat} {cur : Val} {ptrs : List Val} {table : List (Option (List Val))}
    {PoolUsed : Mem 64 → Prop} {m : Mem 64} {i : Nat} (hi : i < c.cap)
    (hm : (B ⋆ WorkState c poolUsed poolRem cur ptrs table PoolUsed ⋆ R) m) :
    ∃ (hplen : ptrs.length = c.cap) (htlen : table.length = c.cap),
      loadVal m .l .l true (c.cb + BitVec.ofNat 64 (8 * i)) = some (ptrs[i]'(hplen ▸ hi)) ∧
      (match table[i]'(htlen ▸ hi) with
       | none => ptrs[i]'(hplen ▸ hi) = 0
       | some lits =>
         ptrs[i]'(hplen ▸ hi) ≠ 0 ∧
         (∀ x ∈ lits, IsValidLit c.mv x) ∧
         (∃ R_l, PoolUsed = (ZeroTermInts (ptrs[i]'(hplen ▸ hi)) lits ⋆ R_l))) := by
  obtain ⟨f_bw, f_r, hu1, hd1, ⟨f_b, f_w, hu2, hd2, hb, ⟨_, ⟨hplen, htlen, hrel⟩, _, hwm⟩⟩, hr⟩ := hm
  dsimp only at hwm
  let pcur := c.pbase + BitVec.ofNat 64 (4 * poolUsed)
  let WOther := word8Array c.hdr (c.hdrWords pcur cur) ⋆
    byte1Array c.vb (assignBytes c.mv Assignment.empty) ⋆
    region (c.vb + BitVec.ofNat 64 (c.mv + 1)) (c.vBytes - (c.mv + 1)) ⋆
    region c.tb c.tRaw ⋆
    region c.tlim (c.tBytes - c.tRaw) ⋆
    PoolUsed ⋆
    region pcur (4 * poolRem)
  have hfocus : (word8Array c.cb ptrs ⋆ (B ⋆ WOther ⋆ R)) m := by
    have hfull : (B ⋆ (word8Array c.cb ptrs ⋆ WOther) ⋆ R) m :=
      ⟨f_bw, f_r, hu1, hd1, ⟨f_b, f_w, hu2, hd2, hb,
        sep_cast hwm (by dsimp [WOther, pcur]; ac_rfl)⟩, hr⟩
    exact sep_cast hfull (by ac_rfl)
  exact ⟨hplen, htlen, loadl_word8Array (hplen ▸ hi) hfocus, hrel i hi⟩

private theorem workState_store_cb {B R : Mem 64 → Prop} {c : WorkCfg}
    {poolUsed poolRem : Nat} {cur v : Val} {ptrs : List Val} {table table' : List (Option (List Val))}
    {PoolUsed : Mem 64 → Prop} {m : Mem 64} {i : Nat} (hi : i < c.cap)
    (htr' : TableRel c.mv c.cap (ptrs.set i v) table' PoolUsed)
    (hm : (B ⋆ WorkState c poolUsed poolRem cur ptrs table PoolUsed ⋆ R) m) :
    storeOk m .l (c.cb + BitVec.ofNat 64 (8 * i)) ∧
      (B ⋆ WorkState c poolUsed poolRem cur (ptrs.set i v) table' PoolUsed ⋆ R)
        (storeMem m .l (c.cb + BitVec.ofNat 64 (8 * i)) v) := by
  obtain ⟨f_bw, f_r, hu1, hd1, ⟨f_b, f_w, hu2, hd2, hb, ⟨hsum, ⟨hplen, _, _⟩, hpu, hwm⟩⟩, hr⟩ := hm
  dsimp only at hwm
  let pcur := c.pbase + BitVec.ofNat 64 (4 * poolUsed)
  let WOther := word8Array c.hdr (c.hdrWords pcur cur) ⋆
    byte1Array c.vb (assignBytes c.mv Assignment.empty) ⋆
    region (c.vb + BitVec.ofNat 64 (c.mv + 1)) (c.vBytes - (c.mv + 1)) ⋆
    region c.tb c.tRaw ⋆
    region c.tlim (c.tBytes - c.tRaw) ⋆
    PoolUsed ⋆
    region pcur (4 * poolRem)
  have hfocus : (word8Array c.cb ptrs ⋆ (B ⋆ WOther ⋆ R)) m := by
    have hfull : (B ⋆ (word8Array c.cb ptrs ⋆ WOther) ⋆ R) m :=
      ⟨f_bw, f_r, hu1, hd1, ⟨f_b, f_w, hu2, hd2, hb,
        sep_cast hwm (by dsimp [WOther, pcur]; ac_rfl)⟩, hr⟩
    exact sep_cast hfull (by ac_rfl)
  obtain ⟨hok, hm1⟩ := storel_word8Array v (hplen ▸ hi) hfocus
  have hm2 : (B ⋆ (word8Array c.cb (ptrs.set i v) ⋆ WOther) ⋆ R)
      (storeMem m .l (c.cb + BitVec.ofNat 64 (8 * i)) v) :=
    sep_cast hm1 (by ac_rfl)
  obtain ⟨g_bw, g_r, gu1, gd1, ⟨g_b, g_w, gu2, gd2, gb, gwm⟩, gr⟩ := hm2
  refine ⟨hok, g_bw, g_r, gu1, gd1, ⟨g_b, g_w, gu2, gd2, gb, ⟨hsum, htr', hpu, ?_⟩⟩, gr⟩
  dsimp only
  exact sep_cast gwm (by dsimp [WOther, pcur]; ac_rfl)

private theorem tableRel_set_none {mv cap : Nat} {ptrs : List Val}
    {table : List (Option (List Val))} {PoolUsed : Mem 64 → Prop} {did : Nat}
    (htr : TableRel mv cap ptrs table PoolUsed) :
    TableRel mv cap (ptrs.set did 0) (table.set did none) PoolUsed := by
  obtain ⟨hplen, htlen, hrel⟩ := htr
  refine ⟨by simp [hplen], by simp [htlen], fun i hi => ?_⟩
  by_cases heq : did = i
  · subst heq
    simp
  · simp only [List.getElem_set_ne heq]
    exact hrel i hi

private theorem tableRel_set_some {mv cap : Nat} {ptrs : List Val}
    {table : List (Option (List Val))} {PoolUsed : Mem 64 → Prop}
    {id : Nat} {c_ptr : Val} {clits : List Val}
    (hc_ptr : c_ptr ≠ 0) (hclits : ∀ x ∈ clits, IsValidLit mv x)
    (hpool : ∃ R_c, PoolUsed = (ZeroTermInts c_ptr clits ⋆ R_c))
    (htr : TableRel mv cap ptrs table PoolUsed) :
    TableRel mv cap (ptrs.set id c_ptr) (table.set id (some clits)) PoolUsed := by
  obtain ⟨hplen, htlen, hrel⟩ := htr
  refine ⟨by simp [hplen], by simp [htlen], fun i hi => ?_⟩
  by_cases heq : id = i
  · subst heq
    simp only [List.getElem_set_self]
    exact ⟨hc_ptr, hclits, hpool⟩
  · simp only [List.getElem_set_ne heq]
    exact hrel i hi

/-- Verification of `lbCheckPrf` against `lbCheckPrfSpec`, parameterized by `Γ` providing
`lbReadAddLitsSpec` and `lbRupCheckSpec`. -/
theorem lbCheckPrf_correct_of (Γ : Env)
    (hReadAddLits : ∀ args m Q X, lbReadAddLitsSpec args m Q X → Γ "lb_read_add_lits" args m Q X)
    (hRupCheck : ∀ args m Q X, lbRupCheckSpec args m Q X → Γ "lb_rup_check" args m Q X) :
    ∀ args m Q X, lbCheckPrfSpec args m Q X → Func.spec Γ lbCheckPrf args m Q X := by
  rintro _ m0 Q X ⟨c, prf_ptr, prfBytes, poolUsed0, poolRem0, ptrs0, table0, PoolUsed0, R,
    rfl, hprf_fit, hm0, hQ⟩
  unfold lbCheckPrf Func.spec
  have hcap_bound : c.cap < 2 ^ 64 := by have := c.hfit; omega
  have hnc_bound : c.nc < 2 ^ 64 := by have := c.hnc; unfold dimacsBound at this; omega
  wp_unfold
  refine ⟨_, workState_load_hdr 1 (by decide) rfl hm0,
    _, workState_load_hdr 2 (by decide) rfl hm0,
    _, workState_load_hdr 6 (by decide) rfl hm0, ?_⟩
  simp only [WorkCfg.hdrWords, List.getElem_cons_succ, List.getElem_cons_zero]
  -- `@fail` join point
  apply wp_join (fun as m' => as = [] ∧
    checkPrfPure c.mv c.nc poolRem0 table0 prfBytes = false ∧
    (Eq (prfBytes.At prf_ptr) ⋆ region c.hdr c.activeBytes ⋆ R) m')
  · rintro _ m' ⟨rfl, hfalse, hm'⟩
    wp_unfold
    exact hQ 0 m' (by simp [hfalse]) hm'
  intro Jfail hJfail
  -- `@rec_loop`
  apply wp_loop (fun r as m => ∃ idx poolUsed poolRem ptrs table PoolUsed,
    as = [] ∧
    idx ≤ prfBytes.length ∧
    r = prfBytes.length - idx ∧
    checkPrfPure c.mv c.nc poolRem0 table0 prfBytes =
      checkPrfAux ((prfBytes.drop idx).length + 1) c.mv c.nc poolRem table (prfBytes.drop idx) ∧
    (Eq (prfBytes.At prf_ptr) ⋆
      WorkState c poolUsed poolRem (prf_ptr + BitVec.ofNat 64 idx) ptrs table PoolUsed ⋆ R) m)
  · rintro Jrec r as m ⟨idx, poolUsed, poolRem, ptrs, table, PoolUsed,
      rfl, hidx, rfl, hpure, hm⟩ ih
    have hlen_cap : table.length = c.cap := (workState_tableRel hm).2.1
    wp_unfold
    refine ⟨_, workState_load_hdr 9 (by decide) rfl hm, ?_⟩
    simp only [WorkCfg.hdrWords, List.getElem_cons_succ, List.getElem_cons_zero]
    refine ⟨fun heof => ?_, fun hneof => ?_⟩
    · have hidx_end : idx = prfBytes.length := by
        have := congrArg (fun x => (x - prf_ptr).toNat) heof
        simp [BitVec.add_comm prf_ptr, Nat.mod_eq_of_lt (by omega : idx < 2 ^ 64),
          Nat.mod_eq_of_lt (by omega : prfBytes.length < 2 ^ 64)] at this
        omega
      subst hidx_end
      refine hJfail _ _ ⟨rfl, ?_, workState_collapse hm⟩
      rw [hpure, List.drop_length]
      rfl
    · have hidx_lt : idx < prfBytes.length := by
        rcases Nat.eq_or_lt_of_le hidx with rfl | h
        · exact absurd rfl hneof
        · exact h
      have hm_prf : (Eq (prfBytes.At prf_ptr) ⋆
          (WorkState c poolUsed poolRem (prf_ptr + BitVec.ofNat 64 idx) ptrs table PoolUsed ⋆ R)) m :=
        sep_cast hm (by ac_rfl)
      have hld_tag := loadub_At hidx_lt (by omega) hm_prf
      refine ⟨_, hld_tag, ?_⟩
      let tag := prfBytes[idx]
      let bs1 := prfBytes.drop (idx + 1)
      have hdrop_idx : prfBytes.drop idx = tag :: bs1 := List.drop_eq_getElem_cons hidx_lt
      have hcur1 : prf_ptr + BitVec.ofNat 64 idx + (1 : Val) = prf_ptr + BitVec.ofNat 64 (idx + 1) := by
        apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]; omega
      rw [hcur1]
      have his_a_iff : (BitVec.ofNat 64 tag.toNat = (97 : Val)) ↔ (tag == 97) = true := by grind
      refine ⟨fun his_a => ?_, fun hnot_a => ?_⟩
      · -- `'a'` record
        have htag97 : (tag == 97) = true := his_a_iff.mp his_a
        refine check_readLeb128_spec hprf_fit hidx_lt hm_prf
          (fun hleb_none => hJfail _ _ ⟨rfl, by
            rw [hpure, hdrop_idx]
            simp [checkPrfAux, htag97, bs1, hleb_none], workState_collapse hm⟩)
          fun uid bs2 hleb_uid huid_lt hbs2_drop hidx2_le hidx2_gt => ?_
        let idx2 := prfBytes.length - bs2.length
        wp_unfold
        have hodd_iff : (BitVec.ofNat 64 uid &&& (1 : Val) ≠ (0 : Val)) ↔ (uid % 2 != 0) = true := by
          rw [bne_iff_ne]
          have hand1 : uid &&& 1 = uid % 2 := Nat.and_two_pow_sub_one_eq_mod uid 1
          constructor
          · intro hne heq0
            apply hne
            apply BitVec.eq_of_toNat_eq
            simp [BitVec.toNat_and, Nat.mod_eq_of_lt (by omega : uid < 2 ^ 64), hand1, heq0]
          · intro hne heq0
            apply hne
            have := congrArg BitVec.toNat heq0
            simpa [BitVec.toNat_and, Nat.mod_eq_of_lt (by omega : uid < 2 ^ 64), hand1] using this
        refine ⟨fun hodd => hJfail _ _ ⟨rfl, by
            have ho := hodd_iff.mp hodd
            rw [hpure, hdrop_idx]
            simp [checkPrfAux, htag97, bs1, hleb_uid, ho], workState_collapse hm⟩,
          fun heven => ?_⟩
        have heven' : (uid % 2 != 0) = false := by
          cases hb : uid % 2 != 0
          · rfl
          · exact absurd (hodd_iff.mpr hb) heven
        let id := uid / 2
        have hid_bv : BitVec.ofNat 64 uid >>> (1 : Nat) = BitVec.ofNat 64 id := by
          apply BitVec.eq_of_toNat_eq
          simp [id, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
            Nat.mod_eq_of_lt (by omega : uid < 2 ^ 64), Nat.mod_eq_of_lt (by omega : uid / 2 < 2 ^ 64)]
        rw [hid_bv]
        have hgt_nc_iff : (BitVec.ofNat 64 c.nc).ult (BitVec.ofNat 64 id) = true ↔ c.nc < id := by
          simp [BitVec.ult, Nat.mod_eq_of_lt hnc_bound, Nat.mod_eq_of_lt (by omega : id < 2 ^ 64)]
        refine ⟨fun hgt_nc => ?_, fun hle_nc => ?_⟩
        · have hnc_lt_id : c.nc < id := hgt_nc_iff.mp hgt_nc
          have hlt_cap_iff : (BitVec.ofNat 64 id).ult (BitVec.ofNat 64 c.cap) = true ↔ id < c.cap := by
            simp [BitVec.ult, Nat.mod_eq_of_lt (by omega : id < 2 ^ 64), Nat.mod_eq_of_lt hcap_bound]
          refine ⟨fun hlt_cap => ?_, fun hge_cap => ?_⟩
          · have hid_lt_cap : id < c.cap := hlt_cap_iff.mp hlt_cap
            have hid_toNat : (BitVec.ofNat 64 id).toNat = id :=
              Nat.mod_eq_of_lt (by omega : id < 2 ^ 64)
            rw [hid_toNat]
            obtain ⟨hplen, htlen, hld_slot, hslot_rel⟩ := workState_load_cb hid_lt_cap hm
            refine ⟨_, hld_slot, fun hused => ?_, fun hunused => ?_⟩
            · -- Slot is non-zero, so `table[id]` cannot be `none`
              refine hJfail _ _ ⟨rfl, ?_, workState_collapse hm⟩
              rw [hpure, hdrop_idx]
              cases hti : table[id]'(htlen ▸ hid_lt_cap) with
              | none =>
                rw [hti] at hslot_rel
                exact absurd hslot_rel hused
              | some lits =>
                simp [checkPrfAux, htag97, bs1, hleb_uid, heven', hlen_cap, hnc_lt_id, hid_lt_cap,
                  id, hti]
            · -- Slot is zero, so `table[id] = none`
              have hptr0 : ptrs[id]'(hplen ▸ hid_lt_cap) = 0 := Classical.not_not.mp hunused
              have hti_none : table[id]'(htlen ▸ hid_lt_cap) = none := by
                cases hti : table[id]'(htlen ▸ hid_lt_cap) with
                | none => rfl
                | some lits =>
                  rw [hti] at hslot_rel
                  exact absurd hptr0 hslot_rel.1
              obtain ⟨hok_cur2, hm_cur2⟩ := workState_store_cur (cur' := prf_ptr + BitVec.ofNat 64 idx2) hm
              refine ⟨hok_cur2, _, workState_load_hdr 8 (by decide) rfl hm_cur2, ?_⟩
              simp only [WorkCfg.hdrWords, List.getElem_cons_succ, List.getElem_cons_zero]
              -- Call `lb_read_add_lits`
              let c_ptr := c.pbase + BitVec.ofNat 64 (4 * poolUsed)
              simp only [wp, List.map, Arg.val, true_and]
              let P_read : Post := fun rs m1 => ∃ r, rs = [r] ∧
                (match readAddLitsPure c.mv poolRem (prfBytes.drop idx2) with
                 | none =>
                   r = 0 ∧ (Eq (prfBytes.At prf_ptr) ⋆ region c.hdr c.activeBytes ⋆ R) m1
                 | some (clits, poolRem', bs3) =>
                   let idx3 := prfBytes.length - bs3.length
                   r = (if clits.isEmpty then 2 else 1) ∧
                   bs3 = prfBytes.drop idx3 ∧ idx3 ≤ prfBytes.length ∧
                   clits.length + 1 + poolRem' = poolRem ∧
                   c_ptr ≠ 0 ∧
                   (∀ x ∈ clits, IsValidLit c.mv x) ∧
                   (Eq (prfBytes.At prf_ptr) ⋆
                     WorkState c (poolUsed + (clits.length + 1)) poolRem'
                       (prf_ptr + BitVec.ofNat 64 idx3)
                       ptrs table (PoolUsed ⋆ ZeroTermInts c_ptr clits) ⋆ R) m1)
              refine ⟨P_read, fun _ _ _ => False,
                hReadAddLits _ _ _ _ ⟨c, prf_ptr, prfBytes, idx2, poolUsed, poolRem,
                  ptrs, table, PoolUsed, R, rfl, hprf_fit, hidx2_le, hm_cur2,
                  fun r m1 hr => ⟨r, rfl, hr⟩⟩,
                ?_, fun _ _ _ h => h.elim⟩
              rintro _ m1 ⟨lstat, rfl, hread_res⟩
              wp_unfold
              cases hread_eq : readAddLitsPure c.mv poolRem (prfBytes.drop idx2) with
              | none =>
                rw [hread_eq] at hread_res
                obtain ⟨rfl, hm1_reg⟩ := hread_res
                refine ⟨fun h => absurd rfl h, fun _ => hJfail _ _ ⟨rfl, ?_, hm1_reg⟩⟩
                rw [hpure, hdrop_idx]
                rw [← hbs2_drop] at hread_eq
                simp [checkPrfAux, htag97, bs1, hleb_uid, heven', hlen_cap, hnc_lt_id, hid_lt_cap,
                  id, hti_none, hread_eq]
              | some val3 =>
                rcases val3 with ⟨clits, poolRem', bs3⟩
                rw [hread_eq] at hread_res
                obtain ⟨hlstat, hbs3_drop, hidx3_le, _, hc_ptr_nz, hclits_v, hm1⟩ := hread_res
                let idx3 := prfBytes.length - bs3.length
                have hlstat_nz : lstat ≠ 0 := by
                  rw [hlstat]; split <;> decide
                refine ⟨fun _ => ?_, fun h0 => absurd (Classical.not_not.mp h0) hlstat_nz⟩
                -- Call `lb_rup_check`
                simp only [wp, List.map, Arg.val, true_and]
                let PoolUsed1 := PoolUsed ⋆ ZeroTermInts c_ptr clits
                let P_rup : Post := fun rs m2 => ∃ r, rs = [r] ∧
                  (match rupCheckPure c.mv id clits table (prfBytes.drop idx3) with
                   | none =>
                     r = 0 ∧ (Eq (prfBytes.At prf_ptr) ⋆ region c.hdr c.activeBytes ⋆ R) m2
                   | some bs4 =>
                     let idx4 := prfBytes.length - bs4.length
                     r = 1 ∧ bs4 = prfBytes.drop idx4 ∧ idx4 ≤ prfBytes.length ∧
                     (Eq (prfBytes.At prf_ptr) ⋆
                       WorkState c (poolUsed + (clits.length + 1)) poolRem'
                         (prf_ptr + BitVec.ofNat 64 idx4)
                         ptrs table PoolUsed1 ⋆ R) m2)
                refine ⟨P_rup, fun _ _ _ => False,
                  hRupCheck _ _ _ _ ⟨c, id, c_ptr, prf_ptr, prfBytes, idx3,
                    poolUsed + (clits.length + 1), poolRem', clits, ptrs, table, PoolUsed1, R,
                    rfl, hid_lt_cap, hprf_fit, hidx3_le, hclits_v,
                    ⟨PoolUsed, sep_comm PoolUsed (ZeroTermInts c_ptr clits)⟩, hm1,
                    fun r m2 hr => ⟨r, rfl, hr⟩⟩,
                  ?_, fun _ _ _ h => h.elim⟩
                rintro _ m2 ⟨rok, rfl, hrup_res⟩
                wp_unfold
                cases hrup_eq : rupCheckPure c.mv id clits table (prfBytes.drop idx3) with
                | none =>
                  rw [hrup_eq] at hrup_res
                  obtain ⟨rfl, hm2_reg⟩ := hrup_res
                  refine ⟨fun h => absurd rfl h, fun _ => hJfail _ _ ⟨rfl, ?_, hm2_reg⟩⟩
                  rw [hpure, hdrop_idx]
                  rw [← hbs2_drop] at hread_eq
                  rw [← hbs3_drop] at hrup_eq
                  simp [checkPrfAux, htag97, bs1, hleb_uid, heven', hlen_cap, hnc_lt_id, hid_lt_cap,
                    id, hti_none, hread_eq, hrup_eq]
                | some bs4 =>
                  rw [hrup_eq] at hrup_res
                  obtain ⟨rfl, hbs4_drop, hidx4_le, hm2⟩ := hrup_res
                  let idx4 := prfBytes.length - bs4.length
                  refine ⟨fun _ => ?_, fun h0 => absurd (Classical.not_not.mp h0) (by decide)⟩
                  have hlstat2_iff : (lstat = (2 : Val)) ↔ clits.isEmpty = true := by
                    rw [hlstat]; cases clits.isEmpty <;> decide
                  refine ⟨fun hemp => ?_, fun hnemp => ?_⟩
                  · have hemp' : clits.isEmpty = true := hlstat2_iff.mp hemp
                    refine hQ 1 m2 ?_ (workState_collapse hm2)
                    have htrue : checkPrfPure c.mv c.nc poolRem0 table0 prfBytes = true := by
                      rw [hpure, hdrop_idx]
                      rw [← hbs2_drop] at hread_eq
                      rw [← hbs3_drop] at hrup_eq
                      simp [checkPrfAux, htag97, bs1, hleb_uid, heven', hlen_cap, hnc_lt_id, hid_lt_cap,
                        id, hti_none, hread_eq, hrup_eq, hemp']
                    simp [htrue]
                  · have hnemp' : clits.isEmpty = false := by
                      cases hb : clits.isEmpty
                      · rfl
                      · exact absurd (hlstat2_iff.mpr hb) hnemp
                    have htr_new := tableRel_set_some (id := id) hc_ptr_nz hclits_v
                      ⟨PoolUsed, sep_comm PoolUsed (ZeroTermInts c_ptr clits)⟩
                      (workState_tableRel hm2)
                    obtain ⟨hok_cb, hm3⟩ := workState_store_cb hid_lt_cap htr_new hm2
                    refine ⟨hok_cb, ?_⟩
                    have hlt2 := readAddLitsPure_lt hread_eq
                    have hlt3 := rupCheckPure_lt hrup_eq
                    have hbs3_lt : bs3.length < bs2.length := by
                      have : (prfBytes.drop idx2).length = bs2.length := by rw [← hbs2_drop]
                      omega
                    have hbs4_lt : bs4.length < bs3.length := by
                      have : (prfBytes.drop idx3).length = bs3.length := by rw [← hbs3_drop]
                      omega
                    have hidx4_gt : idx < idx4 := by
                      dsimp [idx4, idx2] at hidx2_gt ⊢; omega
                    refine ih (prfBytes.length - idx4) _ _ (by omega)
                      ⟨idx4, poolUsed + (clits.length + 1), poolRem',
                        ptrs.set id c_ptr, table.set id (some clits), PoolUsed1,
                        rfl, hidx4_le, rfl, ?_, hm3⟩
                    rw [hpure, hdrop_idx]
                    rw [← hbs2_drop] at hread_eq
                    rw [← hbs3_drop] at hrup_eq
                    have hstep_aux : checkPrfAux ((tag :: bs1).length + 1) c.mv c.nc poolRem table (tag :: bs1) =
                        checkPrfAux (bs1.length + 1) c.mv c.nc poolRem' (table.set id (some clits)) bs4 := by
                      simp [checkPrfAux, htag97, bs1, hleb_uid, heven', hlen_cap, hnc_lt_id, hid_lt_cap,
                        id, hti_none, hread_eq, hrup_eq, hnemp']
                    rw [hstep_aux, ← hbs4_drop]
                    exact checkPrfAux_fuel_irrel
                      (by have : bs1.length = prfBytes.length - (idx + 1) := List.length_drop; omega)
                      (by omega)
          · have hid_ge_cap : ¬ (id < c.cap) := by
              intro h; rw [hlt_cap_iff.mpr h] at hge_cap; cases hge_cap
            refine hJfail _ _ ⟨rfl, ?_, workState_collapse hm⟩
            rw [hpure, hdrop_idx]
            simp [checkPrfAux, htag97, bs1, hleb_uid, heven', hlen_cap, hnc_lt_id, hid_ge_cap, id]
        · have hid_le_nc : ¬ (c.nc < id) := by
            intro h; rw [hgt_nc_iff.mpr h] at hle_nc; cases hle_nc
          refine hJfail _ _ ⟨rfl, ?_, workState_collapse hm⟩
          rw [hpure, hdrop_idx]
          simp [checkPrfAux, htag97, bs1, hleb_uid, heven', hid_le_nc, id]
      · -- Not `'a'`: check `'d'` (`100`)
        have htag_not97 : (tag == 97) = false := by
          cases hb : tag == 97
          · rfl
          · exact absurd (his_a_iff.mpr hb) hnot_a
        have his_d_iff : (BitVec.ofNat 64 tag.toNat = (100 : Val)) ↔ (tag == 100) = true := by grind
        refine ⟨fun his_d => ?_, fun hnot_d => ?_⟩
        · have htag100 : (tag == 100) = true := his_d_iff.mp his_d
          -- `@del_loop`
          apply wp_loop (fun dr das dm => ∃ didx dptrs dtable,
            das = [prf_ptr + BitVec.ofNat 64 didx] ∧
            idx + 1 ≤ didx ∧ didx ≤ prfBytes.length ∧
            dr = prfBytes.length - didx ∧
            delLoopAux (bs1.length + 1) c.cap table bs1 =
              delLoopAux ((prfBytes.drop didx).length + 1) c.cap dtable (prfBytes.drop didx) ∧
            (Eq (prfBytes.At prf_ptr) ⋆
              WorkState c poolUsed poolRem (prf_ptr + BitVec.ofNat 64 idx) dptrs dtable PoolUsed ⋆ R) dm)
          · rintro Jdel dr das dm ⟨didx, dptrs, dtable, rfl, hdidx_lo, hdidx_hi, rfl, hdel_eq, hdm⟩ ih_del
            wp_unfold
            have hdm_prf : (Eq (prfBytes.At prf_ptr) ⋆
                (WorkState c poolUsed poolRem (prf_ptr + BitVec.ofNat 64 idx) dptrs dtable PoolUsed ⋆ R)) dm :=
              sep_cast hdm (by ac_rfl)
            refine check_readLeb128_spec hprf_fit hdidx_hi hdm_prf
              (fun hleb_none => hJfail _ _ ⟨rfl, by
                rw [hpure, hdrop_idx]
                have hdn : delLoopAux (bs1.length + 1) c.cap table bs1 = none := by
                  rw [hdel_eq]; simp [delLoopAux, hleb_none]
                simp only [checkPrfAux, htag_not97, htag100, hlen_cap, ↓reduceIte, Bool.false_eq_true]
                rw [hdn], workState_collapse hdm⟩)
              fun u bs_d hleb_u hu_lt hbsd_drop hdidx2_le hdidx2_gt => ?_
            let didx2 := prfBytes.length - bs_d.length
            wp_unfold
            have huz_iff : (BitVec.ofNat 64 u = (0 : Val)) ↔ u = 0 := by grind
            refine ⟨fun huz => ?_, fun hnuz => ?_⟩
            · have hu0 : u = 0 := huz_iff.mp huz
              subst hu0
              obtain ⟨hok_dcur, hdm_cur⟩ := workState_store_cur (cur' := prf_ptr + BitVec.ofNat 64 didx2) hdm
              refine ⟨hok_dcur, ?_⟩
              have hdel_done : delLoopAux (bs1.length + 1) c.cap table bs1 = some (dtable, bs_d) := by
                rw [hdel_eq]; simp [delLoopAux, hleb_u]
              refine ih (prfBytes.length - didx2) _ _ (by omega)
                ⟨didx2, poolUsed, poolRem, dptrs, dtable, PoolUsed, rfl, hdidx2_le, rfl, ?_, hdm_cur⟩
              rw [hpure, hdrop_idx]
              have hstep_d : checkPrfAux ((tag :: bs1).length + 1) c.mv c.nc poolRem table (tag :: bs1) =
                  checkPrfAux (bs1.length + 1) c.mv c.nc poolRem dtable bs_d := by
                simp only [checkPrfAux, htag_not97, htag100, hlen_cap, ↓reduceIte, Bool.false_eq_true]
                rw [hdel_done]
                rfl
              rw [hstep_d, ← hbsd_drop]
              exact checkPrfAux_fuel_irrel
                (by have : bs1.length = prfBytes.length - (idx + 1) := List.length_drop; omega)
                (by omega)
            · have hu_ne0 : u ≠ 0 := fun h => hnuz (huz_iff.mpr h)
              cases u with
              | zero => exact absurd rfl hu_ne0
              | succ u1 =>
                let u := u1 + 1
                have hdodd_iff : (BitVec.ofNat 64 u &&& (1 : Val) ≠ (0 : Val)) ↔ (u % 2 != 0) = true := by
                  rw [bne_iff_ne]
                  have hand1 : u &&& 1 = u % 2 := Nat.and_two_pow_sub_one_eq_mod u 1
                  constructor
                  · intro hne heq0
                    apply hne
                    apply BitVec.eq_of_toNat_eq
                    simp [BitVec.toNat_and, Nat.mod_eq_of_lt (by omega : u < 2 ^ 64), hand1, heq0]
                  · intro hne heq0
                    apply hne
                    have := congrArg BitVec.toNat heq0
                    simpa [BitVec.toNat_and, Nat.mod_eq_of_lt (by omega : u < 2 ^ 64), hand1] using this
                refine ⟨fun hdodd => hJfail _ _ ⟨rfl, by
                    have ho := hdodd_iff.mp hdodd
                    have hdn : delLoopAux (bs1.length + 1) c.cap table bs1 = none := by
                      rw [hdel_eq]; simp [delLoopAux, hleb_u, ho, u]
                    rw [hpure, hdrop_idx]
                    simp only [checkPrfAux, htag_not97, htag100, hlen_cap, ↓reduceIte, Bool.false_eq_true]
                    rw [hdn], workState_collapse hdm⟩,
                  fun hdeven => ?_⟩
                have hdeven' : (u % 2 != 0) = false := by
                  cases hb : u % 2 != 0
                  · rfl
                  · exact absurd (hdodd_iff.mpr hb) hdeven
                let did := u / 2
                have hdid_bv : BitVec.ofNat 64 u >>> (1 : Nat) = BitVec.ofNat 64 did := by
                  apply BitVec.eq_of_toNat_eq
                  simp [did, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
                    Nat.mod_eq_of_lt (by omega : u < 2 ^ 64), Nat.mod_eq_of_lt (by omega : u / 2 < 2 ^ 64)]
                rw [hdid_bv]
                have hdz_iff : (BitVec.ofNat 64 did = (0 : Val)) ↔ (did == 0) = true := by grind
                refine ⟨fun hdz => hJfail _ _ ⟨rfl, by
                    have hz0 := hdz_iff.mp hdz
                    have hdn : delLoopAux (bs1.length + 1) c.cap table bs1 = none := by
                      rw [hdel_eq]; simp [delLoopAux, hleb_u, hdeven', did, hz0, u]
                    rw [hpure, hdrop_idx]
                    simp only [checkPrfAux, htag_not97, htag100, hlen_cap, ↓reduceIte, Bool.false_eq_true]
                    rw [hdn], workState_collapse hdm⟩,
                  fun hdnz => ?_⟩
                have hdid_nz : (did == 0) = false := by
                  cases hb : did == 0
                  · rfl
                  · exact absurd (hdz_iff.mpr hb) hdnz
                have hdlt_cap_iff : (BitVec.ofNat 64 did).ult (BitVec.ofNat 64 c.cap) = true ↔ did < c.cap := by
                  simp [BitVec.ult, Nat.mod_eq_of_lt (by omega : did < 2 ^ 64), Nat.mod_eq_of_lt hcap_bound]
                refine ⟨fun hdlt_cap => ?_, fun hdge_cap => ?_⟩
                · have hdid_lt_cap : did < c.cap := hdlt_cap_iff.mp hdlt_cap
                  have hdid_toNat : (BitVec.ofNat 64 did).toNat = did :=
                    Nat.mod_eq_of_lt (by omega : did < 2 ^ 64)
                  rw [hdid_toNat]
                  obtain ⟨hdplen, hdtlen, hdld_slot, hdslot_rel⟩ := workState_load_cb hdid_lt_cap hdm
                  refine ⟨_, hdld_slot, fun hdact => ?_, fun hdinact => ?_⟩
                  · -- Active clause: `dtable[did] = some lits`
                    have hdti_some : ∃ lits, dtable[did]'(hdtlen ▸ hdid_lt_cap) = some lits := by
                      cases hti : dtable[did]'(hdtlen ▸ hdid_lt_cap) with
                      | none =>
                        rw [hti] at hdslot_rel
                        exact absurd hdslot_rel hdact
                      | some lits => exact ⟨lits, rfl⟩
                    obtain ⟨dlits, hdti_eq⟩ := hdti_some
                    have hdtr_new := tableRel_set_none (did := did) (workState_tableRel hdm)
                    obtain ⟨hok_dcb, hdm2⟩ := workState_store_cb hdid_lt_cap hdtr_new hdm
                    refine ⟨hok_dcb, ?_⟩
                    refine ih_del (prfBytes.length - didx2) _ _ (by omega)
                      ⟨didx2, dptrs.set did 0, dtable.set did none, rfl,
                        by omega, hdidx2_le, rfl, ?_, hdm2⟩
                    rw [hdel_eq]
                    have hdget_eq : dtable[did]? = some (some dlits) := by
                      rw [List.getElem?_eq_getElem (hdtlen ▸ hdid_lt_cap), hdti_eq]
                    have hstep_del : delLoopAux ((prfBytes.drop didx).length + 1) c.cap dtable (prfBytes.drop didx) =
                        delLoopAux (prfBytes.drop didx).length c.cap (dtable.set did none) bs_d := by
                      simp [delLoopAux, hleb_u, hdeven', did, hdid_nz, hdid_lt_cap, hdget_eq, u]
                    rw [hstep_del, ← hbsd_drop]
                    exact delLoopAux_fuel_irrel
                      (by have : bs_d.length = prfBytes.length - didx2 := by
                            rw [hbsd_drop, List.length_drop]
                          have : (prfBytes.drop didx).length = prfBytes.length - didx := List.length_drop
                          omega)
                      (by omega)
                  · -- Inactive (`0`): fails
                    have hdptr0 : dptrs[did]'(hdplen ▸ hdid_lt_cap) = 0 := Classical.not_not.mp hdinact
                    have hdti_none : dtable[did]'(hdtlen ▸ hdid_lt_cap) = none := by
                      cases hti : dtable[did]'(hdtlen ▸ hdid_lt_cap) with
                      | none => rfl
                      | some lits =>
                        rw [hti] at hdslot_rel
                        exact absurd hdptr0 hdslot_rel.1
                    have hdget_none : dtable[did]? = some none := by
                      rw [List.getElem?_eq_getElem (hdtlen ▸ hdid_lt_cap), hdti_none]
                    refine hJfail _ _ ⟨rfl, ?_, workState_collapse hdm⟩
                    have hdn : delLoopAux (bs1.length + 1) c.cap table bs1 = none := by
                      rw [hdel_eq]
                      simp [delLoopAux, hleb_u, hdeven', did, hdid_nz, hdid_lt_cap, hdget_none, u]
                    rw [hpure, hdrop_idx]
                    simp only [checkPrfAux, htag_not97, htag100, hlen_cap, ↓reduceIte, Bool.false_eq_true]
                    rw [hdn]
                · have hdid_ge_cap : ¬ (did < c.cap) := by
                    intro h; rw [hdlt_cap_iff.mpr h] at hdge_cap; cases hdge_cap
                  refine hJfail _ _ ⟨rfl, ?_, workState_collapse hdm⟩
                  have hdn : delLoopAux (bs1.length + 1) c.cap table bs1 = none := by
                    rw [hdel_eq]
                    simp [delLoopAux, hleb_u, hdeven', did, hdid_nz, hdid_ge_cap, u]
                  rw [hpure, hdrop_idx]
                  simp only [checkPrfAux, htag_not97, htag100, hlen_cap, ↓reduceIte, Bool.false_eq_true]
                  rw [hdn]
          · intro Jdel hJdel
            wp_unfold
            exact hJdel (prfBytes.length - (idx + 1)) _ _
              ⟨idx + 1, ptrs, table, rfl, Nat.le_refl _, hidx_lt, rfl, rfl, hm⟩
        · have htag_not100 : (tag == 100) = false := by
            cases hb : tag == 100
            · rfl
            · exact absurd (his_d_iff.mpr hb) hnot_d
          refine hJfail _ _ ⟨rfl, ?_, workState_collapse hm⟩
          rw [hpure, hdrop_idx]
          simp [checkPrfAux, htag_not97, htag_not100]
  · intro Jrec hJrec
    wp_unfold
    refine hJrec prfBytes.length _ _
      ⟨0, poolUsed0, poolRem0, ptrs0, table0, PoolUsed0, rfl, Nat.zero_le _, by simp, rfl, ?_⟩
    simpa using hm0

/-! ## 5. Verification of `lratCheckBytes` against `lratCheckBytesExactSpec` -/

private theorem bv_align8 {x : Nat} (hx : x < 2 ^ 64) :
    BitVec.ofNat 64 x &&& (-8 : Val) = BitVec.ofNat 64 ((x / 8) * 8) := by
  have hdiv : (BitVec.ofNat 64 x >>> (3 : Nat)) <<< (3 : Nat) = BitVec.ofNat 64 ((x / 8) * 8) := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hx,
      Nat.mod_eq_of_lt (by omega : x / 8 * 8 < 2 ^ 64)]
    omega
  rw [← hdiv]
  grind

private theorem bv_align4 {x : Nat} (hx : x < 2 ^ 64) :
    BitVec.ofNat 64 x &&& (-4 : Val) = BitVec.ofNat 64 ((x / 4) * 4) := by
  have hdiv : (BitVec.ofNat 64 x >>> (2 : Nat)) <<< (2 : Nat) = BitVec.ofNat 64 ((x / 4) * 4) := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
      Nat.shiftLeft_eq, Nat.mod_eq_of_lt hx,
      Nat.mod_eq_of_lt (by omega : x / 4 * 4 < 2 ^ 64)]
  rw [← hdiv]
  grind

private theorem replicate_zero_set {xs : List Val} {i : Nat} (hi : i < xs.length) :
    (List.replicate i 0 ++ xs.drop i).set i 0 =
      List.replicate (i + 1) 0 ++ xs.drop (i + 1) := by
  apply List.ext_getElem
  · simp; omega
  · intro k hk1 hk2
    by_cases hki : k < i
    · rw [List.getElem_set_ne (by omega), List.getElem_append_left (by simp [hki]),
          List.getElem_append_left (by simp; omega)]
      simp
    · by_cases heq : k = i
      · subst heq
        rw [List.getElem_set_self, List.getElem_append_left (by simp)]
        simp
      · rw [List.getElem_set_ne (by omega),
            List.getElem_append_right (by simp; omega),
            List.getElem_append_right (by simp; omega)]
        simp only [List.length_replicate, List.getElem_drop]
        congr 1
        omega

private theorem tableRel_init (mv cap : Nat) :
    TableRel mv cap (List.replicate cap 0) (List.replicate cap none) emp :=
  ⟨by simp, by simp, fun _ _ => by simp⟩

private theorem split_workspace (c : WorkCfg) (work_len : Nat)
    (hlen : c.activeBytes ≤ work_len)
    (hwfit : c.hdr.toNat + work_len < 2 ^ 64)
    {R_rest : Mem 64 → Prop} {hdrInit : List Val} {m : Mem 64}
    (hm : (word8Array c.hdr hdrInit ⋆ region (c.hdr + 80) (work_len - 80) ⋆ R_rest) m) :
    ∃ (vs0 cs0 : List Val),
      vs0.length = c.mv + 1 ∧
      cs0.length = c.cap ∧
      (byte1Array c.vb vs0 ⋆
        word8Array c.cb cs0 ⋆
        word8Array c.hdr hdrInit ⋆
        (region (c.vb + BitVec.ofNat 64 (c.mv + 1)) (c.vBytes - (c.mv + 1)) ⋆
          region c.tb c.tRaw ⋆
          region c.tlim (c.tBytes - c.tRaw) ⋆
          region c.pbase (4 * c.poolInts)) ⋆
        region (c.hdr + BitVec.ofNat 64 c.activeBytes) (work_len - c.activeBytes) ⋆ R_rest) m := by
  have hfit := c.hfit
  have hmv := c.hmv
  unfold dimacsBound at hmv
  have hact80 : 80 ≤ c.activeBytes := by unfold WorkCfg.activeBytes; omega
  have he_tail : region (c.hdr + 80) (work_len - 80) =
      (region c.vb (c.activeBytes - 80) ⋆
        region (c.hdr + BitVec.ofNat 64 c.activeBytes) (work_len - c.activeBytes)) := by
    have hsum : work_len - 80 = (c.activeBytes - 80) + (work_len - c.activeBytes) := by omega
    have hvb_eq : c.hdr + (80 : Val) = c.vb := rfl
    have hptr : c.vb + BitVec.ofNat 64 (c.activeBytes - 80) =
        c.hdr + BitVec.ofNat 64 c.activeBytes := by
      apply BitVec.eq_of_toNat_eq
      unfold WorkCfg.vb WorkCfg.activeBytes WorkCfg.vBytes WorkCfg.tBytes WorkCfg.tRaw at *
      simp [BitVec.toNat_add]; omega
    rw [hsum, hvb_eq, region_split (by
      unfold WorkCfg.vb WorkCfg.activeBytes WorkCfg.vBytes WorkCfg.tBytes WorkCfg.tRaw at *
      simp; omega), hptr]
  have he_vtcb : region c.vb (c.activeBytes - 80) =
      (region c.vb c.vBytes ⋆ region c.tb (c.tBytes + (8 * c.cap + 4 * c.poolInts))) := by
    have : c.activeBytes - 80 = c.vBytes + (c.tBytes + (8 * c.cap + 4 * c.poolInts)) := by
      unfold WorkCfg.activeBytes; omega
    rw [this, region_split (by
      unfold WorkCfg.vb WorkCfg.vBytes WorkCfg.tBytes WorkCfg.tRaw at *
      simp; omega)]
    rfl
  have he_v : region c.vb c.vBytes =
      (region c.vb (c.mv + 1) ⋆
        region (c.vb + BitVec.ofNat 64 (c.mv + 1)) (c.vBytes - (c.mv + 1))) := by
    have : c.vBytes = (c.mv + 1) + (c.vBytes - (c.mv + 1)) := by unfold WorkCfg.vBytes; omega
    conv => lhs; rw [this, region_split (by
      unfold WorkCfg.vb WorkCfg.vBytes WorkCfg.tBytes WorkCfg.tRaw at *
      simp; omega)]
  have he_tcb : region c.tb (c.tBytes + (8 * c.cap + 4 * c.poolInts)) =
      (region c.tb c.tBytes ⋆ region c.cb (8 * c.cap + 4 * c.poolInts)) := by
    rw [region_split (by
      unfold WorkCfg.tb WorkCfg.vb WorkCfg.vBytes WorkCfg.tBytes WorkCfg.tRaw at *
      simp; omega)]
    rfl
  have he_t : region c.tb c.tBytes =
      (region c.tb c.tRaw ⋆ region c.tlim (c.tBytes - c.tRaw)) := by
    have : c.tBytes = c.tRaw + (c.tBytes - c.tRaw) := by unfold WorkCfg.tBytes; omega
    conv => lhs; rw [this, region_split (by
      unfold WorkCfg.tb WorkCfg.vb WorkCfg.vBytes WorkCfg.tBytes WorkCfg.tRaw at *
      simp; omega)]
    rfl
  have he_cb : region c.cb (8 * c.cap + 4 * c.poolInts) =
      (region c.cb (8 * c.cap) ⋆ region c.pbase (4 * c.poolInts)) := by
    rw [region_split (by
      unfold WorkCfg.cb WorkCfg.tb WorkCfg.vb WorkCfg.vBytes WorkCfg.tBytes WorkCfg.tRaw at *
      simp; omega)]
    rfl
  rw [he_tail, he_vtcb, he_v, he_tcb, he_t, he_cb] at hm
  have hm_ord : (region c.vb (c.mv + 1) ⋆ region c.cb (8 * c.cap) ⋆
      (word8Array c.hdr hdrInit ⋆
        (region (c.vb + BitVec.ofNat 64 (c.mv + 1)) (c.vBytes - (c.mv + 1)) ⋆
          region c.tb c.tRaw ⋆
          region c.tlim (c.tBytes - c.tRaw) ⋆
          region c.pbase (4 * c.poolInts)) ⋆
        region (c.hdr + BitVec.ofNat 64 c.activeBytes) (work_len - c.activeBytes) ⋆ R_rest)) m :=
    sep_cast hm (by ac_rfl)
  obtain ⟨f_vc, f_rem, hu1, hd1, ⟨f_v, f_c, hu2, hd2, hrv, hrc⟩, hrem⟩ := hm_ord
  obtain ⟨vs0, hvs0, hbv⟩ := region_to_byte1Array (c.mv + 1) (by omega) hrv
  obtain ⟨cs0, hcs0, hbc⟩ := region_to_word8Array c.cap
    (by unfold WorkCfg.vBytes WorkCfg.tBytes WorkCfg.tRaw at *; omega) hrc
  refine ⟨vs0, cs0, hvs0, hcs0, ?_⟩
  have h1 : (byte1Array c.vb vs0 ⋆ word8Array c.cb cs0 ⋆
      (word8Array c.hdr hdrInit ⋆
        (region (c.vb + BitVec.ofNat 64 (c.mv + 1)) (c.vBytes - (c.mv + 1)) ⋆
          region c.tb c.tRaw ⋆
          region c.tlim (c.tBytes - c.tRaw) ⋆
          region c.pbase (4 * c.poolInts)) ⋆
        region (c.hdr + BitVec.ofNat 64 c.activeBytes) (work_len - c.activeBytes) ⋆ R_rest)) m :=
    ⟨f_vc, f_rem, hu1, hd1, ⟨f_v, f_c, hu2, hd2, hbv, hbc⟩, hrem⟩
  exact sep_cast h1 (by ac_rfl)

private theorem merge_workspace_tail (c : WorkCfg) (work_len : Nat)
    (hlen : c.activeBytes ≤ work_len)
    (hwfit : c.hdr.toNat + work_len < 2 ^ 64) :
    (region c.hdr c.activeBytes ⋆
      region (c.hdr + BitVec.ofNat 64 c.activeBytes) (work_len - c.activeBytes)) =
    region c.hdr work_len := by
  have : work_len = c.activeBytes + (work_len - c.activeBytes) := by omega
  conv => rhs; rw [this, region_split (by omega)]

private theorem runLratCheckBytes_of_header {cnfBytes prfBytes bodyRest : List UInt8}
    {work_len mv nc : Nat}
    (h128 : ¬ (work_len < 128))
    (hhdr : parseHeader cnfBytes = some (mv, nc, bodyRest)) :
    runLratCheckBytes cnfBytes prfBytes work_len =
      let v_bytes := ((mv + 8) / 8) * 8
      let t_raw := 4 * (mv + 1)
      let t_bytes := ((t_raw + 7) / 8) * 8
      let fixed := 80 + v_bytes + t_bytes
      if work_len < fixed then false
      else
        let rem := work_len - fixed
        let c_half := rem / 16
        let p_cap := prfBytes.length % 268435456
        let want := nc + p_cap + 32
        let cap := if c_half < want then c_half else want
        if cap ≤ nc then false
        else
          let cb_bytes := 8 * cap
          let pool_rem := rem - cb_bytes
          let pool_ints := pool_rem / 4
          match parseBodyPure mv nc pool_ints [] bodyRest with
          | none => false
          | some (clauses, pool_ints') =>
            checkPrfPure mv nc pool_ints' (initClauseTable cap clauses) prfBytes := by
  unfold runLratCheckBytes
  simp only [h128, hhdr, ↓reduceIte]
  rfl

/-- Verification of `lratCheckBytes` against `lratCheckBytesExactSpec`, parameterized by `Γ`
providing `lbParseDimacsHeaderSpec`, `lbParseDimacsBodySpec`, and `lbCheckPrfSpec`. -/
theorem lratCheckBytes_exact_of (Γ : Env)
    (hParseHeader : ∀ args m Q X,
      lbParseDimacsHeaderSpec args m Q X → Γ "lb_parse_dimacs_header" args m Q X)
    (hParseBody : ∀ args m Q X,
      lbParseDimacsBodySpec args m Q X → Γ "lb_parse_dimacs_body" args m Q X)
    (hCheckPrf : ∀ args m Q X,
      lbCheckPrfSpec args m Q X → Γ "lb_check_prf" args m Q X) :
    ∀ args m Q X, lratCheckBytesExactSpec args m Q X → Func.spec Γ lratCheckBytes args m Q X := by
  rintro _ m0 Q X ⟨cnf_ptr, prf_ptr, work_ptr, cnfBytes, prfBytes, work_len, R_mem,
    rfl, hcnf_fit, hprf_fit, hwork_fit, hm0, hQ⟩
  unfold lratCheckBytes Func.spec
  wp_unfold
  have hsmall_iff : (BitVec.ofNat 64 work_len).ult (128 : Val) = true ↔ work_len < 128 := by
    simp [BitVec.ult, Nat.mod_eq_of_lt (by omega : work_len < 2 ^ 64)]
  refine ⟨fun hsmall => ?_, fun hge128 => ?_⟩
  · have hlt128 : work_len < 128 := hsmall_iff.mp hsmall
    exact hQ 0 m0 (by simp [runLratCheckBytes, hlt128]) hm0
  · have hnot_lt128 : ¬ (work_len < 128) := fun h => by
      rw [hsmall_iff.mpr h] at hge128; cases hge128
    have hsplit80 : region work_ptr work_len =
        (region work_ptr 80 ⋆ region (work_ptr + 80) (work_len - 80)) := by
      have : work_len = 80 + (work_len - 80) := by omega
      conv => lhs; rw [this, region_split (by omega)]
      rfl
    let R80 := region (work_ptr + 80) (work_len - 80) ⋆ Eq (prfBytes.At prf_ptr) ⋆ R_mem
    have hm0_hdr : (Eq (cnfBytes.At cnf_ptr) ⋆ region work_ptr 80 ⋆ R80) m0 := by
      have hm_tmp := hm0
      rw [hsplit80] at hm_tmp
      exact sep_cast hm_tmp (by dsimp [R80]; ac_rfl)
    -- Call `lb_parse_dimacs_header`
    simp only [wp, List.map, Arg.val, true_and]
    let P_hdr : Post := fun rs m1 => ∃ r, rs = [r] ∧
      (match parseHeader cnfBytes with
       | none =>
         r = 0 ∧ (Eq (cnfBytes.At cnf_ptr) ⋆ region work_ptr 80 ⋆ R80) m1
       | some (mv, nc, rest) =>
         r = 1 ∧ mv < dimacsBound ∧ nc < dimacsBound ∧
         rest = cnfBytes.drop (cnfBytes.length - rest.length) ∧
         rest.length ≤ cnfBytes.length ∧
         ∃ w2 w3 w4 w5 w6 w7 w8 : Val,
           (Eq (cnfBytes.At cnf_ptr) ⋆
             word8Array work_ptr
               [BitVec.ofNat 64 mv, BitVec.ofNat 64 nc, w2, w3, w4, w5, w6, w7, w8,
                cnf_ptr + BitVec.ofNat 64 (cnfBytes.length - rest.length)] ⋆ R80) m1)
    refine ⟨P_hdr, fun _ _ _ => False,
      hParseHeader _ _ _ _ ⟨cnf_ptr, work_ptr, cnfBytes, R80, rfl, hcnf_fit, by omega, hm0_hdr,
        fun r m1 hr => ⟨r, rfl, hr⟩⟩,
      ?_, fun _ _ _ h => h.elim⟩
    rintro _ m1 ⟨hok, rfl, hhdr_res⟩
    wp_unfold
    cases hhdr_eq : parseHeader cnfBytes with
    | none =>
      rw [hhdr_eq] at hhdr_res
      obtain ⟨rfl, hm1_reg⟩ := hhdr_res
      refine ⟨fun h => absurd rfl h, fun _ => ?_⟩
      have hm1_full : ((Eq (cnfBytes.At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆
          region work_ptr work_len) ⋆ R_mem) m1 := by
        have h1 : (Eq (cnfBytes.At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆
            (region work_ptr 80 ⋆ region (work_ptr + 80) (work_len - 80)) ⋆ R_mem) m1 :=
          sep_cast hm1_reg (by dsimp [R80]; ac_rfl)
        rw [← hsplit80] at h1
        exact sep_cast h1 (by ac_rfl)
      exact hQ 0 m1 (by simp [runLratCheckBytes, hnot_lt128, hhdr_eq]) hm1_full
    | some val_hdr =>
      rcases val_hdr with ⟨mv, nc, bodyRest⟩
      rw [hhdr_eq] at hhdr_res
      obtain ⟨rfl, hmv, hnc, hbody_drop, hbody_le, w2, w3, w4, w5, w6, w7, w8, hm1⟩ := hhdr_res
      refine ⟨fun _ => ?_, fun h0 => absurd (Classical.not_not.mp h0) (by decide)⟩
      let idx0 := cnfBytes.length - bodyRest.length
      let cur0 := cnf_ptr + BitVec.ofNat 64 idx0
      let hdrInit : List Val :=
        [BitVec.ofNat 64 mv, BitVec.ofNat 64 nc, w2, w3, w4, w5, w6, w7, w8, cur0]
      have hm1_focus : (word8Array work_ptr hdrInit ⋆
          (Eq (cnfBytes.At cnf_ptr) ⋆ R80)) m1 :=
        sep_cast hm1 (by dsimp [hdrInit, cur0, idx0]; ac_rfl)
      have hld_mv : loadVal m1 .l .l true work_ptr = some (BitVec.ofNat 64 mv) := by
        have h0 : work_ptr = work_ptr + BitVec.ofNat 64 (8 * 0) := by simp
        rw [h0]
        exact loadl_word8Array (i := 0) (by simp [hdrInit]) hm1_focus
      have hld_nc : loadVal m1 .l .l true (work_ptr + 8) = some (BitVec.ofNat 64 nc) := by
        have h1 : work_ptr + (8 : Val) = work_ptr + BitVec.ofNat 64 (8 * 1) := rfl
        rw [h1]
        exact loadl_word8Array (i := 1) (by simp [hdrInit]) hm1_focus
      refine ⟨_, hld_mv, _, hld_nc, ?_⟩
      -- Collapse helper when returning `0` early after `lb_parse_dimacs_header`
      have hcollapse_init : ((Eq (cnfBytes.At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆
          region work_ptr work_len) ⋆ R_mem) m1 := by
        have hr80 : ∀ f, word8Array work_ptr hdrInit f → region work_ptr 80 f := fun f hf => by
          have := word8Array_to_region (by simp [hdrInit]) hf
          simpa [hdrInit] using this
        have h1 : (region work_ptr 80 ⋆ (Eq (cnfBytes.At cnf_ptr) ⋆ R80)) m1 :=
          sep_mono hr80 hm1_focus
        have h2 : (Eq (cnfBytes.At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆
            (region work_ptr 80 ⋆ region (work_ptr + 80) (work_len - 80)) ⋆ R_mem) m1 :=
          sep_cast h1 (by dsimp [R80]; ac_rfl)
        rw [← hsplit80] at h2
        exact sep_cast h2 (by ac_rfl)
      -- Evaluate layout BitVec arithmetic
      have hmv_lt : mv < 2 ^ 28 := hmv
      have hnc_lt : nc < 2 ^ 28 := hnc
      let v_bytes := ((mv + 8) / 8) * 8
      let t_raw := 4 * (mv + 1)
      let t_bytes := ((t_raw + 7) / 8) * 8
      let fixed := 80 + v_bytes + t_bytes
      have hbv_mv1 : BitVec.ofNat 64 mv + (1 : Val) = BitVec.ofNat 64 (mv + 1) := by
        apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]
      have hbv_mv8 : BitVec.ofNat 64 mv + (8 : Val) = BitVec.ofNat 64 (mv + 8) := by
        apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]
      have hbv_vb : BitVec.ofNat 64 (mv + 8) &&& (-8 : Val) = BitVec.ofNat 64 v_bytes :=
        bv_align8 (by omega)
      have hbv_traw : (BitVec.ofNat 64 (mv + 1)) <<< (2 : Nat) = BitVec.ofNat 64 t_raw := by
        apply BitVec.eq_of_toNat_eq
        simp [t_raw, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
          Nat.mod_eq_of_lt (by omega : mv + 1 < 2 ^ 64),
          Nat.mod_eq_of_lt (by omega : (mv + 1) * 4 < 2 ^ 64)]
        omega
      have hbv_tpad : BitVec.ofNat 64 t_raw + (7 : Val) = BitVec.ofNat 64 (t_raw + 7) := by
        apply BitVec.eq_of_toNat_eq; simp [t_raw, BitVec.toNat_add]
      have hbv_tb : BitVec.ofNat 64 (t_raw + 7) &&& (-8 : Val) = BitVec.ofNat 64 t_bytes :=
        bv_align8 (by dsimp [t_raw]; omega)
      have hbv_vt : BitVec.ofNat 64 v_bytes + BitVec.ofNat 64 t_bytes =
          BitVec.ofNat 64 (v_bytes + t_bytes) := by
        apply BitVec.eq_of_toNat_eq
        simp [v_bytes, t_bytes, t_raw, BitVec.toNat_add]
      have hbv_fixed : (80 : Val) + BitVec.ofNat 64 (v_bytes + t_bytes) =
          BitVec.ofNat 64 fixed := by
        apply BitVec.eq_of_toNat_eq
        simp [fixed, v_bytes, t_bytes, t_raw, BitVec.toNat_add]; omega
      rw [hbv_mv1, hbv_mv8, hbv_vb, hbv_traw, hbv_tpad, hbv_tb, hbv_vt, hbv_fixed]
      have hnofit_iff : (BitVec.ofNat 64 work_len).ult (BitVec.ofNat 64 fixed) = true ↔
          work_len < fixed := by
        simp [BitVec.ult, Nat.mod_eq_of_lt (by omega : work_len < 2 ^ 64),
          Nat.mod_eq_of_lt (by dsimp [fixed, v_bytes, t_bytes, t_raw]; omega : fixed < 2 ^ 64)]
      refine ⟨fun hnofit => ?_, fun hfit_fixed => ?_⟩
      · have hlt_fixed : work_len < fixed := hnofit_iff.mp hnofit
        refine hQ 0 m1 ?_ hcollapse_init
        rw [runLratCheckBytes_of_header hnot_lt128 hhdr_eq]
        dsimp only [fixed, v_bytes, t_bytes, t_raw] at hlt_fixed
        simp only [hlt_fixed, ↓reduceIte]
        rfl
      · have hnot_lt_fixed : ¬ (work_len < fixed) := fun h => by
          rw [hnofit_iff.mpr h] at hfit_fixed; cases hfit_fixed
        let rem := work_len - fixed
        let c_half := rem / 16
        let p_cap := prfBytes.length % 268435456
        let want := nc + p_cap + 32
        let cap := if c_half < want then c_half else want
        have hbv_rem : BitVec.ofNat 64 work_len - BitVec.ofNat 64 fixed = BitVec.ofNat 64 rem := by
          apply BitVec.eq_of_toNat_eq
          have hfixed_lt : fixed < 2 ^ 64 := by dsimp [fixed, v_bytes, t_bytes, t_raw]; omega
          simp [rem, BitVec.toNat_sub, Nat.mod_eq_of_lt (by omega : work_len < 2 ^ 64),
            Nat.mod_eq_of_lt hfixed_lt]
          omega
        have hbv_chalf : (BitVec.ofNat 64 rem) >>> (4 : Nat) = BitVec.ofNat 64 c_half := by
          apply BitVec.eq_of_toNat_eq
          simp [c_half, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
            Nat.mod_eq_of_lt (by omega : rem < 2 ^ 64),
            Nat.mod_eq_of_lt (by omega : rem / 16 < 2 ^ 64)]
        have hbv_pcap : BitVec.ofNat 64 prfBytes.length &&& (268435455 : Val) =
            BitVec.ofNat 64 p_cap := by
          apply BitVec.eq_of_toNat_eq
          have hand28 : prfBytes.length &&& 268435455 = prfBytes.length % 268435456 :=
            Nat.and_two_pow_sub_one_eq_mod prfBytes.length 28
          simp [p_cap, BitVec.toNat_and, Nat.mod_eq_of_lt (by omega : prfBytes.length < 2 ^ 64),
            hand28, Nat.mod_eq_of_lt (by omega : prfBytes.length % 268435456 < 2 ^ 64)]
        have hbv_w1 : BitVec.ofNat 64 nc + BitVec.ofNat 64 p_cap = BitVec.ofNat 64 (nc + p_cap) := by
          apply BitVec.eq_of_toNat_eq
          simp [p_cap, BitVec.toNat_add]
        have hbv_want : BitVec.ofNat 64 (nc + p_cap) + (32 : Val) = BitVec.ofNat 64 want := by
          apply BitVec.eq_of_toNat_eq
          simp [want, p_cap, BitVec.toNat_add]
        rw [hbv_rem, hbv_chalf, hbv_pcap, hbv_w1, hbv_want]
        -- `@got_cap(%cap)`
        apply wp_join (fun as m' => as = [BitVec.ofNat 64 cap] ∧ m' = m1)
        · rintro _ m_cap ⟨rfl, hm_cap_eq⟩
          subst m_cap
          wp_unfold
          have hcap_le_chalf : cap ≤ c_half := by dsimp [cap]; split <;> omega
          have hcap_lt64 : cap < 2 ^ 64 := by dsimp [c_half, rem] at hcap_le_chalf; omega
          have hbadcap_iff : (BitVec.ofNat 64 cap).ule (BitVec.ofNat 64 nc) = true ↔ cap ≤ nc := by
            simp [BitVec.ule, Nat.mod_eq_of_lt hcap_lt64,
              Nat.mod_eq_of_lt (by omega : nc < 2 ^ 64)]
          refine ⟨fun hbadcap => ?_, fun hgoodcap => ?_⟩
          · have hcap_le_nc : cap ≤ nc := hbadcap_iff.mp hbadcap
            refine hQ 0 m1 ?_ hcollapse_init
            rw [runLratCheckBytes_of_header hnot_lt128 hhdr_eq]
            dsimp only [cap, c_half, want, p_cap, rem, fixed, v_bytes, t_bytes, t_raw] at hnot_lt_fixed hcap_le_nc
            simp only [hnot_lt_fixed, hcap_le_nc, ↓reduceIte]
            rfl
          · have hnot_cap_le_nc : ¬ (cap ≤ nc) := fun h => by
              rw [hbadcap_iff.mpr h] at hgoodcap; cases hgoodcap
            have hnc_cap : nc < cap := by omega
            let cb_bytes := 8 * cap
            let pool_rem := rem - cb_bytes
            let pool_ints := pool_rem / 4
            have hcb_le_rem : cb_bytes ≤ rem := by dsimp [cb_bytes, c_half] at *; omega
            have hact_le : 80 + v_bytes + t_bytes + 8 * cap + 4 * pool_ints ≤ work_len := by
              dsimp [pool_ints, pool_rem, cb_bytes, rem]; omega
            let c : WorkCfg := {
              hdr := work_ptr
              mv := mv
              nc := nc
              cap := cap
              poolInts := pool_ints
              hmv := hmv
              hnc := hnc
              hnc_cap := hnc_cap
              hfit := by dsimp [v_bytes, t_bytes, t_raw] at hact_le; omega
            }
            have hc_act_le : c.activeBytes ≤ work_len := hact_le
            have hcap_toNat : (BitVec.ofNat 64 cap).toNat = cap := Nat.mod_eq_of_lt hcap_lt64
            have hbv_pool_rem : BitVec.ofNat 64 rem - BitVec.ofNat 64 (8 * cap) =
                BitVec.ofNat 64 pool_rem := by
              apply BitVec.eq_of_toNat_eq
              simp [pool_rem, cb_bytes, BitVec.toNat_sub,
                Nat.mod_eq_of_lt (by omega : rem < 2 ^ 64),
                Nat.mod_eq_of_lt (by omega : 8 * cap < 2 ^ 64)]
              omega
            have hbv_pool_bytes : BitVec.ofNat 64 pool_rem &&& (-4 : Val) =
                BitVec.ofNat 64 (4 * pool_ints) := by
              rw [bv_align4 (by omega)]
              congr 1; dsimp [pool_ints]; omega
            rw [hcap_toNat, hbv_pool_rem, hbv_pool_bytes]
            -- Split workspace into `vs0`, `cs0`, `hdrInit`, rest of `WorkState`, and tail
            have hm1_ws_in : (word8Array c.hdr hdrInit ⋆
                region (c.hdr + 80) (work_len - 80) ⋆
                (Eq (cnfBytes.At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆ R_mem)) m1 :=
              sep_cast hm1 (by dsimp [c, R80, hdrInit, cur0, idx0]; ac_rfl)
            obtain ⟨vs0, cs0, hvs0, hcs0, hm1_split⟩ :=
              split_workspace c work_len hc_act_le hwork_fit hm1_ws_in
            let WMid := region (c.vb + BitVec.ofNat 64 (c.mv + 1)) (c.vBytes - (c.mv + 1)) ⋆
              region c.tb c.tRaw ⋆
              region c.tlim (c.tBytes - c.tRaw) ⋆
              region c.pbase (4 * c.poolInts)
            let RTail := region (c.hdr + BitVec.ofNat 64 c.activeBytes) (work_len - c.activeBytes)
            let RRest := Eq (cnfBytes.At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆ R_mem
            -- `@zv_done()`
            apply wp_join (fun as m_zv => as = [] ∧
              (word8Array c.cb cs0 ⋆
                byte1Array c.vb (List.replicate (c.mv + 1) 0) ⋆
                word8Array c.hdr hdrInit ⋆ WMid ⋆ RTail ⋆ RRest) m_zv)
            · rintro _ m_zv ⟨rfl, hm_zv⟩
              -- `@zcb_done()`
              apply wp_join (fun as m_zcb => as = [] ∧
                (word8Array c.hdr hdrInit ⋆
                  byte1Array c.vb (List.replicate (c.mv + 1) 0) ⋆
                  word8Array c.cb (List.replicate c.cap 0) ⋆
                  WMid ⋆ RTail ⋆ RRest) m_zcb)
              · rintro _ m_zcb ⟨rfl, hm_zcb⟩
                wp_unfold
                -- 7 header stores (`+16 .. +64`)
                let TailZ := byte1Array c.vb (List.replicate (c.mv + 1) 0) ⋆
                  word8Array c.cb (List.replicate c.cap 0) ⋆
                  WMid ⋆ RTail ⋆ RRest
                have hm_s0 : (word8Array c.hdr hdrInit ⋆ TailZ) m_zcb :=
                  sep_cast hm_zcb (by dsimp [TailZ]; ac_rfl)
                have hp16 : work_ptr + (16 : Val) = c.hdr + BitVec.ofNat 64 (8 * 2) := rfl
                have hp24 : work_ptr + (24 : Val) = c.hdr + BitVec.ofNat 64 (8 * 3) := rfl
                have hp32 : work_ptr + (32 : Val) = c.hdr + BitVec.ofNat 64 (8 * 4) := rfl
                have hp40 : work_ptr + (40 : Val) = c.hdr + BitVec.ofNat 64 (8 * 5) := rfl
                have hp48 : work_ptr + (48 : Val) = c.hdr + BitVec.ofNat 64 (8 * 6) := rfl
                have hp56 : work_ptr + (56 : Val) = c.hdr + BitVec.ofNat 64 (8 * 7) := rfl
                have hp64 : work_ptr + (64 : Val) = c.hdr + BitVec.ofNat 64 (8 * 8) := rfl
                rw [hp16, hp24, hp32, hp40, hp48, hp56, hp64]
                obtain ⟨hok2, hm_s2⟩ := storel_word8Array (i := 2) (BitVec.ofNat 64 c.cap)
                  (by simp [hdrInit]) hm_s0
                obtain ⟨hok3, hm_s3⟩ := storel_word8Array (i := 3) c.vb
                  (by simp [hdrInit]) hm_s2
                obtain ⟨hok4, hm_s4⟩ := storel_word8Array (i := 4) c.tb
                  (by simp [hdrInit]) hm_s3
                obtain ⟨hok5, hm_s5⟩ := storel_word8Array (i := 5) c.tlim
                  (by simp [hdrInit]) hm_s4
                obtain ⟨hok6, hm_s6⟩ := storel_word8Array (i := 6) c.cb
                  (by simp [hdrInit]) hm_s5
                obtain ⟨hok7, hm_s7⟩ := storel_word8Array (i := 7) c.plim
                  (by simp [hdrInit]) hm_s6
                obtain ⟨hok8, hm_s8⟩ := storel_word8Array (i := 8) c.pbase
                  (by simp [hdrInit]) hm_s7
                refine ⟨hok2, hok3, hok4, hok5, hok6, hok7, hok8, ?_⟩
                let m_hdr := storeMem (storeMem (storeMem (storeMem (storeMem (storeMem
                  (storeMem m_zcb .l (c.hdr + BitVec.ofNat 64 (8 * 2)) (BitVec.ofNat 64 c.cap))
                  .l (c.hdr + BitVec.ofNat 64 (8 * 3)) c.vb)
                  .l (c.hdr + BitVec.ofNat 64 (8 * 4)) c.tb)
                  .l (c.hdr + BitVec.ofNat 64 (8 * 5)) c.tlim)
                  .l (c.hdr + BitVec.ofNat 64 (8 * 6)) c.cb)
                  .l (c.hdr + BitVec.ofNat 64 (8 * 7)) c.plim)
                  .l (c.hdr + BitVec.ofNat 64 (8 * 8)) c.pbase
                have hhdr_eq_words : (((((((hdrInit.set 2 (BitVec.ofNat 64 c.cap)).set 3 c.vb).set
                    4 c.tb).set 5 c.tlim).set 6 c.cb).set 7 c.plim).set 8 c.pbase) =
                    c.hdrWords (c.pbase + BitVec.ofNat 64 (4 * 0)) cur0 := by
                  simp [hdrInit, WorkCfg.hdrWords, c]
                rw [hhdr_eq_words] at hm_s8
                -- Assemble `WorkState c 0 c.poolInts cur0 (replicate cap 0) (replicate cap none) emp`
                let RBody := RTail ⋆ Eq (prfBytes.At prf_ptr) ⋆ R_mem
                have hm_ws0 : (Eq (cnfBytes.At cnf_ptr) ⋆
                    WorkState c 0 c.poolInts cur0
                      (List.replicate c.cap 0) (List.replicate c.cap none) emp ⋆ RBody) m_hdr := by
                  have hm_reord : (Eq (cnfBytes.At cnf_ptr) ⋆
                      (word8Array c.hdr (c.hdrWords (c.pbase + BitVec.ofNat 64 (4 * 0)) cur0) ⋆
                        byte1Array c.vb (assignBytes c.mv Assignment.empty) ⋆
                        region (c.vb + BitVec.ofNat 64 (c.mv + 1)) (c.vBytes - (c.mv + 1)) ⋆
                        region c.tb c.tRaw ⋆
                        region c.tlim (c.tBytes - c.tRaw) ⋆
                        word8Array c.cb (List.replicate c.cap 0) ⋆
                        emp ⋆
                        region (c.pbase + BitVec.ofNat 64 (4 * 0)) (4 * c.poolInts)) ⋆
                      RBody) m_hdr := by
                    have hvb_emp : List.replicate (c.mv + 1) (0 : Val) =
                        assignBytes c.mv Assignment.empty := (assignBytes_empty c.mv).symm
                    have hp0 : c.pbase + BitVec.ofNat 64 (4 * 0) = c.pbase := by simp
                    have hm_tmp : (word8Array c.hdr (c.hdrWords (c.pbase + BitVec.ofNat 64 (4 * 0)) cur0) ⋆
                        TailZ) m_hdr := hm_s8
                    dsimp only [TailZ, WMid, RRest] at hm_tmp
                    rw [hvb_emp, ← sep_emp (region c.pbase (4 * c.poolInts))] at hm_tmp
                    conv at hm_tmp =>
                      pattern (region c.pbase (4 * c.poolInts))
                      rw [← hp0]
                    exact sep_cast hm_tmp (by dsimp [RBody]; ac_rfl)
                  obtain ⟨f_cw, f_rb, hu1, hd1, ⟨f_c, f_w, hu2, hd2, hc_mem, hw_mem⟩, hrb⟩ := hm_reord
                  refine ⟨f_cw, f_rb, hu1, hd1, ⟨f_c, f_w, hu2, hd2, hc_mem,
                    ⟨by omega, tableRel_init c.mv c.cap,
                      fun f hf => by simpa [region_zero] using hf, hw_mem⟩⟩, hrb⟩
                -- Call `lb_parse_dimacs_body`
                simp only [wp, List.map, Arg.val, true_and]
                let P_body : Post := fun rs m_b => ∃ r, rs = [r] ∧
                  (match parseBodyPure c.mv c.nc c.poolInts [] (cnfBytes.drop idx0) with
                   | none =>
                     r = 0 ∧ (Eq (cnfBytes.At cnf_ptr) ⋆ region c.hdr c.activeBytes ⋆ RBody) m_b
                   | some (clauses, poolRem') =>
                     r = 1 ∧ clauses.length = c.nc ∧ poolRem' ≤ c.poolInts ∧
                     ∃ (ptrs : List Val) (PoolUsed : Mem 64 → Prop),
                       (Eq (cnfBytes.At cnf_ptr) ⋆
                         WorkState c (c.poolInts - poolRem') poolRem'
                           cur0 ptrs (initClauseTable c.cap clauses) PoolUsed ⋆ RBody) m_b)
                refine ⟨P_body, fun _ _ _ => False,
                  hParseBody _ _ _ _ ⟨c, cnf_ptr, cnfBytes, idx0, RBody,
                    rfl, hcnf_fit, by dsimp [idx0]; omega, hm_ws0,
                    fun r m_b hr => ⟨r, rfl, hr⟩⟩,
                  ?_, fun _ _ _ h => h.elim⟩
                rintro _ m_b ⟨bok, rfl, hbody_res⟩
                wp_unfold
                cases hbody_eq : parseBodyPure c.mv c.nc c.poolInts [] (cnfBytes.drop idx0) with
                | none =>
                  rw [hbody_eq] at hbody_res
                  obtain ⟨rfl, hm_b_reg⟩ := hbody_res
                  refine ⟨fun h => absurd rfl h, fun _ => ?_⟩
                  have hm_b_full : ((Eq (cnfBytes.At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆
                      region work_ptr work_len) ⋆ R_mem) m_b := by
                    have h1 : (Eq (cnfBytes.At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆
                        (region c.hdr c.activeBytes ⋆ RTail) ⋆ R_mem) m_b :=
                      sep_cast hm_b_reg (by dsimp [RBody]; ac_rfl)
                    dsimp only [RTail] at h1
                    rw [merge_workspace_tail c work_len hc_act_le hwork_fit] at h1
                    exact sep_cast h1 (by dsimp [c])
                  have hbody_eq' : parseBodyPure mv nc pool_ints [] bodyRest = none := by
                    simpa [c, idx0, ← hbody_drop] using hbody_eq
                  refine hQ 0 m_b ?_ hm_b_full
                  rw [runLratCheckBytes_of_header hnot_lt128 hhdr_eq]
                  dsimp only [pool_ints, pool_rem, cb_bytes, cap, c_half, want, p_cap, rem,
                    fixed, v_bytes, t_bytes, t_raw] at hnot_lt_fixed hnot_cap_le_nc hbody_eq'
                  simp only [hnot_lt_fixed, hnot_cap_le_nc, hbody_eq', ↓reduceIte]
                  rfl
                | some val_body =>
                  rcases val_body with ⟨clauses, poolRem'⟩
                  rw [hbody_eq] at hbody_res
                  obtain ⟨rfl, _, _, ptrs, PoolUsed, hm_b⟩ := hbody_res
                  refine ⟨fun _ => ?_, fun h0 => absurd (Classical.not_not.mp h0) (by decide)⟩
                  -- Store `prf_ptr` at `work_ptr + 72` (`c.hdr + 72`)
                  obtain ⟨hok72, hm_b2⟩ := workState_store_cur (cur' := prf_ptr) hm_b
                  refine ⟨hok72, ?_⟩
                  let m_prf_in := storeMem m_b .l (c.hdr + 72) prf_ptr
                  let RPrf := RTail ⋆ Eq (cnfBytes.At cnf_ptr) ⋆ R_mem
                  have hm_prf_ws : (Eq (prfBytes.At prf_ptr) ⋆
                      WorkState c (c.poolInts - poolRem') poolRem' prf_ptr
                        ptrs (initClauseTable c.cap clauses) PoolUsed ⋆ RPrf) m_prf_in :=
                    sep_cast hm_b2 (by dsimp [RBody, RPrf]; ac_rfl)
                  -- Call `lb_check_prf`
                  simp only [wp, List.map, Arg.val, true_and]
                  let P_prf : Post := fun rs m_fin => ∃ r, rs = [r] ∧
                    r = (if checkPrfPure c.mv c.nc poolRem' (initClauseTable c.cap clauses) prfBytes
                         then 1 else 0) ∧
                    (Eq (prfBytes.At prf_ptr) ⋆ region c.hdr c.activeBytes ⋆ RPrf) m_fin
                  refine ⟨P_prf, fun _ _ _ => False,
                    hCheckPrf _ _ _ _ ⟨c, prf_ptr, prfBytes, c.poolInts - poolRem', poolRem',
                      ptrs, initClauseTable c.cap clauses, PoolUsed, RPrf,
                      rfl, hprf_fit, hm_prf_ws,
                      fun r m_fin hr hm_fin => ⟨r, rfl, hr, hm_fin⟩⟩,
                    ?_, fun _ _ _ h => h.elim⟩
                  rintro _ m_fin ⟨pok, rfl, hpok, hm_fin⟩
                  wp_unfold
                  have hm_fin_full : ((Eq (cnfBytes.At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆
                      region work_ptr work_len) ⋆ R_mem) m_fin := by
                    have h1 : (Eq (cnfBytes.At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆
                        (region c.hdr c.activeBytes ⋆ RTail) ⋆ R_mem) m_fin :=
                      sep_cast hm_fin (by dsimp [RPrf]; ac_rfl)
                    dsimp only [RTail] at h1
                    rw [merge_workspace_tail c work_len hc_act_le hwork_fit] at h1
                    exact sep_cast h1 (by dsimp [c])
                  have hbody_eq' : parseBodyPure mv nc pool_ints [] bodyRest =
                      some (clauses, poolRem') := by
                    simpa [c, idx0, ← hbody_drop] using hbody_eq
                  refine hQ pok m_fin ?_ hm_fin_full
                  rw [hpok, runLratCheckBytes_of_header hnot_lt128 hhdr_eq]
                  dsimp only [c, pool_ints, pool_rem, cb_bytes, cap, c_half, want, p_cap, rem,
                    fixed, v_bytes, t_bytes, t_raw] at hnot_lt_fixed hnot_cap_le_nc hbody_eq' ⊢
                  simp only [hnot_lt_fixed, hnot_cap_le_nc, hbody_eq', ↓reduceIte]
              · -- `@zcb(%j)` loop
                intro Jzcb_done hJzcb_done
                let RestZcb := byte1Array c.vb (List.replicate (c.mv + 1) 0) ⋆
                  word8Array c.hdr hdrInit ⋆ WMid ⋆ RTail ⋆ RRest
                apply wp_loop (fun r as m => ∃ j,
                  as = [BitVec.ofNat 64 j] ∧
                  j ≤ c.cap ∧
                  r = c.cap - j ∧
                  (word8Array c.cb (List.replicate j 0 ++ cs0.drop j) ⋆ RestZcb) m)
                · rintro Jzcb r as m ⟨j, rfl, hj_le, rfl, hm_j⟩ ih_zcb
                  wp_unfold
                  have hccap_lt : c.cap < 2 ^ 64 := hcap_lt64
                  have hj_lt_iff : (BitVec.ofNat 64 j).ult (BitVec.ofNat 64 c.cap) = true ↔ j < c.cap := by
                    simp [BitVec.ult, Nat.mod_eq_of_lt (by omega : j < 2 ^ 64),
                      Nat.mod_eq_of_lt hccap_lt]
                  refine ⟨fun hjlt => ?_, fun hjge => ?_⟩
                  · have hj_lt : j < c.cap := hj_lt_iff.mp hjlt
                    have hj_toNat : (BitVec.ofNat 64 j).toNat = j :=
                      Nat.mod_eq_of_lt (by omega : j < 2 ^ 64)
                    rw [hj_toNat]
                    obtain ⟨hok_j, hm_j'⟩ := storel_word8Array (i := j) 0
                      (by simp [hcs0]; omega) hm_j
                    rw [replicate_zero_set (hcs0 ▸ hj_lt)] at hm_j'
                    have hj2 : BitVec.ofNat 64 j + (1 : Val) = BitVec.ofNat 64 (j + 1) := by
                      apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]
                    rw [hj2]
                    exact ⟨hok_j, ih_zcb (c.cap - (j + 1)) _ _ (by omega)
                      ⟨j + 1, rfl, by omega, rfl, hm_j'⟩⟩
                  · have hj_eq : j = c.cap := by
                      rcases Nat.eq_or_lt_of_le hj_le with rfl | h
                      · rfl
                      · rw [hj_lt_iff.mpr h] at hjge; cases hjge
                    subst hj_eq
                    have hdone_cs : List.replicate c.cap (0 : Val) ++ cs0.drop c.cap =
                        List.replicate c.cap 0 := by
                      rw [List.drop_of_length_le (by omega), List.append_nil]
                    rw [hdone_cs] at hm_j
                    exact hJzcb_done _ _ ⟨rfl, sep_cast hm_j (by dsimp [RestZcb]; ac_rfl)⟩
                · intro Jzcb hJzcb
                  wp_unfold
                  refine hJzcb c.cap _ _ ⟨0, rfl, Nat.zero_le _, by simp, ?_⟩
                  have hm_zv' : (word8Array c.cb (List.replicate 0 0 ++ cs0.drop 0) ⋆
                      byte1Array c.vb (List.replicate (c.mv + 1) 0) ⋆
                      word8Array c.hdr hdrInit ⋆ WMid ⋆ RTail ⋆ RRest) m_zv := by
                    simpa using hm_zv
                  exact sep_cast hm_zv' (by dsimp [RestZcb]; ac_rfl)
            · -- `@zv(%i)` loop
              intro Jzv_done hJzv_done
              let RestZv := word8Array c.cb cs0 ⋆ word8Array c.hdr hdrInit ⋆ WMid ⋆ RTail ⋆ RRest
              apply wp_loop (fun r as m => ∃ i,
                as = [BitVec.ofNat 64 i] ∧
                i ≤ c.mv + 1 ∧
                r = (c.mv + 1) - i ∧
                (byte1Array c.vb (List.replicate i 0 ++ vs0.drop i) ⋆ RestZv) m)
              · rintro Jzv r as m ⟨i, rfl, hi_le, rfl, hm_i⟩ ih_zv
                wp_unfold
                have hcmv_lt : c.mv < 2 ^ 28 := hmv_lt
                have hi_ule_iff : (BitVec.ofNat 64 i).ule (BitVec.ofNat 64 c.mv) = true ↔ i ≤ c.mv := by
                  simp [BitVec.ule, Nat.mod_eq_of_lt (by omega : i < 2 ^ 64),
                    Nat.mod_eq_of_lt (by omega : c.mv < 2 ^ 64)]
                refine ⟨fun hi_ule => ?_, fun hi_gt => ?_⟩
                · have hi_le_mv : i ≤ c.mv := hi_ule_iff.mp hi_ule
                  have hi_lt : i < c.mv + 1 := by omega
                  obtain ⟨hok_i, hm_i'⟩ := storeb_byte1Array (i := i) 0
                    (by simp [hvs0]; omega) hm_i
                  rw [replicate_zero_set (hvs0 ▸ hi_lt)] at hm_i'
                  have hi2 : BitVec.ofNat 64 i + (1 : Val) = BitVec.ofNat 64 (i + 1) := by
                    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]
                  rw [hi2]
                  exact ⟨hok_i, ih_zv ((c.mv + 1) - (i + 1)) _ _ (by omega)
                    ⟨i + 1, rfl, by omega, rfl, hm_i'⟩⟩
                · have hi_eq : i = c.mv + 1 := by
                    by_cases h : i ≤ c.mv
                    · rw [hi_ule_iff.mpr h] at hi_gt; cases hi_gt
                    · omega
                  subst hi_eq
                  have hdone_vs : List.replicate (c.mv + 1) (0 : Val) ++ vs0.drop (c.mv + 1) =
                      List.replicate (c.mv + 1) 0 := by
                    rw [List.drop_of_length_le (by omega), List.append_nil]
                  rw [hdone_vs] at hm_i
                  exact hJzv_done _ _ ⟨rfl, sep_cast hm_i (by dsimp [RestZv]; ac_rfl)⟩
              · intro Jzv hJzv
                wp_unfold
                refine hJzv (c.mv + 1) _ _ ⟨0, rfl, Nat.zero_le _, by simp, ?_⟩
                have hm1_split' : (byte1Array c.vb (List.replicate 0 0 ++ vs0.drop 0) ⋆
                    word8Array c.cb cs0 ⋆ word8Array c.hdr hdrInit ⋆ WMid ⋆
                    RTail ⋆ RRest) m1 := by
                  simpa [WMid, RTail, RRest] using hm1_split
                exact sep_cast hm1_split' (by dsimp [RestZv]; ac_rfl)
        · -- Entry to `@got_cap`: `%use_half =w cultl %c_half, %want; jnz %use_half, @got_cap(%c_half), @got_cap(%want)`
          intro Jgot_cap hJgot_cap
          wp_unfold
          have huse_iff : (BitVec.ofNat 64 c_half).ult (BitVec.ofNat 64 want) = true ↔ c_half < want := by
            simp [BitVec.ult, Nat.mod_eq_of_lt (by dsimp [c_half, rem]; omega : c_half < 2 ^ 64),
              Nat.mod_eq_of_lt (by dsimp [want, p_cap]; omega : want < 2 ^ 64)]
          refine ⟨fun huse => ?_, fun hnuse => ?_⟩
          · have hlt_w : c_half < want := huse_iff.mp huse
            exact hJgot_cap _ _ ⟨by simp [cap, hlt_w], rfl⟩
          · have hge_w : ¬ (c_half < want) := fun h => by
              rw [huse_iff.mpr h] at hnuse; cases hnuse
            exact hJgot_cap _ _ ⟨by simp [cap, hge_w], rfl⟩

end LeanQbe.LratBytes
