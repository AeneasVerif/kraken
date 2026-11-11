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
open ProofUtil

/-! ## 1. Pure stream-length, fuel-invariance, and literal-validity lemmas -/

private theorem readLeb128Pure_props {bs : List UInt8} {u : Nat} {bs' : List UInt8}
    (h : readLeb128Pure bs = some (u, bs')) :
    u < 2 ^ 28 ∧ bs'.length < bs.length ∧ bs' = bs.drop (bs.length - bs'.length) := by
  obtain ⟨hu, hlt, k, _, hkle, rfl⟩ := readLeb128Pure_some h
  rw [List.length_drop]
  exact ⟨hu, by omega, by congr 1; omega⟩

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
          have hv_valid := isValidLit_decodeZigZag hu (by omega) (by omega) hmv
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
                exact ⟨parseNat_lt_bound hmv, parseNat_lt_bound hnc⟩
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

/-! ## 3. `WorkState` accessors and verification of `lbCheckPrf` -/

private theorem workState_collapse {B R : Mem 64 → Prop} {c : WorkCfg}
    {poolUsed poolRem : Nat} {cur : Val} {ptrs : List Val} {table : List (Option (List Val))}
    {PoolUsed : Mem 64 → Prop} {m : Mem 64}
    (hm : (B ⋆ WorkState c poolUsed poolRem cur ptrs table PoolUsed ⋆ R) m) :
    (B ⋆ region c.hdr c.activeBytes ⋆ R) m :=
  sep_mono2 (sep_mono2 (fun _ h => h) fun _ => WorkState.to_region) (fun _ h => h) m hm

private abbrev wsCbRest (c : WorkCfg) (poolUsed poolRem : Nat) (cur : Val)
    (PoolUsed B R : Mem 64 → Prop) : Mem 64 → Prop :=
  word8Array c.hdr (c.hdrWords (c.pbase + BitVec.ofNat 64 (4 * poolUsed)) cur) ⋆
  byte1Array c.vb (assignBytes c.mv Assignment.empty) ⋆
  region (c.vb + BitVec.ofNat 64 (c.mv + 1)) (c.vBytes - (c.mv + 1)) ⋆
  region c.tb c.tRaw ⋆ region c.tlim (c.tBytes - c.tRaw) ⋆
  PoolUsed ⋆ region (c.pbase + BitVec.ofNat 64 (4 * poolUsed)) (4 * poolRem) ⋆ B ⋆ R

private theorem workState_tableRel {B R : Mem 64 → Prop} {c : WorkCfg}
    {poolUsed poolRem : Nat} {cur : Val} {ptrs : List Val} {table : List (Option (List Val))}
    {PoolUsed : Mem 64 → Prop} {m : Mem 64}
    (hm : (B ⋆ WorkState c poolUsed poolRem cur ptrs table PoolUsed ⋆ R) m) :
    TableRel c.mv c.cap ptrs table PoolUsed :=
  (workState_sep.mp (sep_ac hm : (WorkState c poolUsed poolRem cur ptrs table PoolUsed ⋆ (B ⋆ R)) m)).2.1

private theorem workState_load_hdr {B R : Mem 64 → Prop} {c : WorkCfg}
    {poolUsed poolRem : Nat} {cur a : Val} {ptrs : List Val} {table : List (Option (List Val))}
    {PoolUsed : Mem 64 → Prop} {m : Mem 64} (i : Nat) (hi : i < 10)
    (ha : a = c.hdr + BitVec.ofNat 64 (8 * i))
    (hm : (B ⋆ WorkState c poolUsed poolRem cur ptrs table PoolUsed ⋆ R) m) :
    loadVal m .l .l true a =
      some ((c.hdrWords (c.pbase + BitVec.ofNat 64 (4 * poolUsed)) cur)[i]'(by
        simpa [WorkCfg.hdrWords] using hi)) := by
  obtain ⟨_, _, _, hwm⟩ := workState_sep.mp
    (sep_ac hm : (WorkState c poolUsed poolRem cur ptrs table PoolUsed ⋆ (B ⋆ R)) m)
  simp only [sep_assoc] at hwm
  exact loadl_hdr i hi hwm ha

private theorem workState_store_cur {B R : Mem 64 → Prop} {c : WorkCfg}
    {poolUsed poolRem : Nat} {cur cur' : Val} {ptrs : List Val} {table : List (Option (List Val))}
    {PoolUsed : Mem 64 → Prop} {m : Mem 64}
    (hm : (B ⋆ WorkState c poolUsed poolRem cur ptrs table PoolUsed ⋆ R) m) :
    storeOk m .l (c.hdr + 72) ∧
      (B ⋆ WorkState c poolUsed poolRem cur' ptrs table PoolUsed ⋆ R)
        (storeMem m .l (c.hdr + 72) cur') := by
  obtain ⟨hsum, htr, hpu, hwm⟩ := workState_sep.mp
    (sep_ac hm : (WorkState c poolUsed poolRem cur ptrs table PoolUsed ⋆ (B ⋆ R)) m)
  simp only [sep_assoc] at hwm
  rw [show c.hdr + (72 : Val) = c.hdr + BitVec.ofNat 64 (8 * 9) from rfl]
  obtain ⟨hok, hm1⟩ := storel_word8Array (i := 9) cur' (by simp [WorkCfg.hdrWords]) hwm
  have hset : (c.hdrWords (c.pbase + BitVec.ofNat 64 (4 * poolUsed)) cur).set 9 cur' =
      c.hdrWords (c.pbase + BitVec.ofNat 64 (4 * poolUsed)) cur' := rfl
  rw [hset] at hm1
  exact ⟨hok, sep_ac (workState_sep.mpr ⟨hsum, htr, hpu, by simp only [sep_assoc]; exact hm1⟩)⟩

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
  obtain ⟨_, ⟨hplen, htlen, hrel⟩, _, hwm⟩ := workState_sep.mp
    (sep_ac hm : (WorkState c poolUsed poolRem cur ptrs table PoolUsed ⋆ (B ⋆ R)) m)
  have hwm_cb : (word8Array c.cb ptrs ⋆ wsCbRest c poolUsed poolRem cur PoolUsed B R) m := by
    dsimp only [wsCbRest]; exact sep_ac hwm
  exact ⟨hplen, htlen, loadl_word8Array (hplen ▸ hi) hwm_cb, hrel i hi⟩

private theorem workState_store_cb {B R : Mem 64 → Prop} {c : WorkCfg}
    {poolUsed poolRem : Nat} {cur v : Val} {ptrs : List Val} {table table' : List (Option (List Val))}
    {PoolUsed : Mem 64 → Prop} {m : Mem 64} {i : Nat} (hi : i < c.cap)
    (htr' : TableRel c.mv c.cap (ptrs.set i v) table' PoolUsed)
    (hm : (B ⋆ WorkState c poolUsed poolRem cur ptrs table PoolUsed ⋆ R) m) :
    storeOk m .l (c.cb + BitVec.ofNat 64 (8 * i)) ∧
      (B ⋆ WorkState c poolUsed poolRem cur (ptrs.set i v) table' PoolUsed ⋆ R)
        (storeMem m .l (c.cb + BitVec.ofNat 64 (8 * i)) v) := by
  obtain ⟨hsum, ⟨hplen, _, _⟩, hpu, hwm⟩ := workState_sep.mp
    (sep_ac hm : (WorkState c poolUsed poolRem cur ptrs table PoolUsed ⋆ (B ⋆ R)) m)
  have hwm_cb : (word8Array c.cb ptrs ⋆ wsCbRest c poolUsed poolRem cur PoolUsed B R) m := by
    dsimp only [wsCbRest]; exact sep_ac hwm
  obtain ⟨hok, hm1⟩ := storel_word8Array v (hplen ▸ hi) hwm_cb
  dsimp only [wsCbRest] at hm1
  have hm1_ws : ((word8Array c.hdr (c.hdrWords (c.pbase + BitVec.ofNat 64 (4 * poolUsed)) cur) ⋆
      byte1Array c.vb (assignBytes c.mv Assignment.empty) ⋆
      region (c.vb + BitVec.ofNat 64 (c.mv + 1)) (c.vBytes - (c.mv + 1)) ⋆
      region c.tb c.tRaw ⋆ region c.tlim (c.tBytes - c.tRaw) ⋆
      word8Array c.cb (ptrs.set i v) ⋆
      PoolUsed ⋆ region (c.pbase + BitVec.ofNat 64 (4 * poolUsed)) (4 * poolRem)) ⋆
      (B ⋆ R)) (storeMem m .l (c.cb + BitVec.ofNat 64 (8 * i)) v) := sep_ac hm1
  exact ⟨hok, sep_ac (workState_sep.mpr ⟨hsum, htr', hpu, hm1_ws⟩)⟩

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
    refine cursor_eof_branch hidx (by omega)
      (fun hidx_end => by
        subst hidx_end
        refine hJfail _ _ ⟨rfl, ?_, workState_collapse hm⟩
        rw [hpure, List.drop_length]; rfl)
      (fun hidx_lt => by
        have hm_prf : (Eq (prfBytes.At prf_ptr) ⋆
            (WorkState c poolUsed poolRem (prf_ptr + BitVec.ofNat 64 idx) ptrs table PoolUsed ⋆ R)) m :=
          sep_cast hm (by ac_rfl)
        refine ⟨_, loadub_At hidx_lt (by omega) hm_prf, ?_⟩
        let tag := prfBytes[idx]
        let bs1 := prfBytes.drop (idx + 1)
        have hdrop_idx : prfBytes.drop idx = tag :: bs1 := List.drop_eq_getElem_cons hidx_lt
        rw [ptr_step_1]
        have his_a_iff : (BitVec.ofNat 64 tag.toNat = (97 : Val)) ↔ (tag == 97) = true := by
          rw [show (97 : Val) = BitVec.ofNat 64 (97 : UInt8).toNat from rfl, bv64_u8_eq, beq_iff_eq]
        refine ⟨fun his_a => ?_, fun hnot_a => ?_⟩
        · -- `'a'` record
          have htag97 : (tag == 97) = true := his_a_iff.mp his_a
          refine readLeb128_spec hprf_fit (by omega) rfl rfl hm_prf
            (fun hleb_none => hJfail _ _ ⟨rfl, by
              rw [hpure, hdrop_idx]
              simp [checkPrfAux, htag97, bs1, hleb_none], workState_collapse hm⟩)
            fun uid bs2 hleb_uid huid_lt _ hbs2_drop hidx2_gt => ?_
          let idx2 := prfBytes.length - bs2.length
          have hidx2_le : idx2 ≤ prfBytes.length := Nat.sub_le _ _
          wp_unfold
          refine bv_odd_branch (by omega : uid < 2 ^ 64)
            (fun ho => hJfail _ _ ⟨rfl, by
              rw [hpure, hdrop_idx]
              simp [checkPrfAux, htag97, bs1, hleb_uid, ho], workState_collapse hm⟩)
            (fun heven' => ?_)
          let id := uid / 2
          rw [bv_shr_one (by omega : uid < 2 ^ 64)]
          refine ult_branch hnc_bound (by omega : id < 2 ^ 64)
            (fun hnc_lt_id => ?_) (fun hid_le_nc => ?_)
          · refine ult_branch (by omega : id < 2 ^ 64) hcap_bound
              (fun hid_lt_cap => ?_) (fun hid_ge_cap => ?_)
            · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : id < 2 ^ 64)]
              obtain ⟨hplen, htlen, hld_slot, hslot_rel⟩ := workState_load_cb hid_lt_cap hm
              refine ⟨_, hld_slot, fun hused => ?_, fun hunused => ?_⟩
              · refine hJfail _ _ ⟨rfl, ?_, workState_collapse hm⟩
                rw [hpure, hdrop_idx]
                cases hti : table[id]'(htlen ▸ hid_lt_cap) with
                | none => rw [hti] at hslot_rel; exact absurd hslot_rel hused
                | some lits =>
                  simp [checkPrfAux, htag97, bs1, hleb_uid, heven', hlen_cap, hnc_lt_id, hid_lt_cap,
                    id, hti]
              · have hptr0 : ptrs[id]'(hplen ▸ hid_lt_cap) = 0 := Classical.not_not.mp hunused
                have hti_none : table[id]'(htlen ▸ hid_lt_cap) = none := by
                  cases hti : table[id]'(htlen ▸ hid_lt_cap) with
                  | none => rfl
                  | some lits => rw [hti] at hslot_rel; exact absurd hptr0 hslot_rel.1
                obtain ⟨hok_cur2, hm_cur2⟩ := workState_store_cur (cur' := prf_ptr + BitVec.ofNat 64 idx2) hm
                refine ⟨hok_cur2, _, workState_load_hdr 8 (by decide) rfl hm_cur2, ?_⟩
                simp only [WorkCfg.hdrWords, List.getElem_cons_succ, List.getElem_cons_zero]
                let c_ptr := c.pbase + BitVec.ofNat 64 (4 * poolUsed)
                refine wp_call_ret1 _
                  (hReadAddLits _ _ _ _ ⟨c, prf_ptr, prfBytes, idx2, poolUsed, poolRem,
                    ptrs, table, PoolUsed, R, rfl, hprf_fit, hidx2_le, hm_cur2,
                    fun r m1 hr => ⟨r, rfl, hr⟩⟩) ?_
                rintro lstat m1 hread_res
                wp_unfold
                cases hread_eq : readAddLitsPure c.mv poolRem (prfBytes.drop idx2) with
                | none =>
                  rw [hread_eq] at hread_res
                  obtain ⟨rfl, hm1_reg⟩ := hread_res
                  refine ⟨fun h => absurd rfl h, fun _ => hJfail _ _ ⟨rfl, ?_, hm1_reg⟩⟩
                  rw [hpure, hdrop_idx, ← hbs2_drop] at *
                  simp [checkPrfAux, htag97, bs1, hleb_uid, heven', hlen_cap, hnc_lt_id, hid_lt_cap,
                    id, hti_none, hread_eq]
                | some val3 =>
                  rcases val3 with ⟨clits, poolRem', bs3⟩
                  rw [hread_eq] at hread_res
                  obtain ⟨hlstat, hbs3_drop, hidx3_le, _, hc_ptr_nz, hclits_v, hm1⟩ := hread_res
                  let idx3 := prfBytes.length - bs3.length
                  have hlstat_nz : lstat ≠ 0 := by rw [hlstat]; split <;> decide
                  refine ⟨fun _ => ?_, fun h0 => absurd (Classical.not_not.mp h0) hlstat_nz⟩
                  let PoolUsed1 := PoolUsed ⋆ ZeroTermInts c_ptr clits
                  refine wp_call_ret1 _
                    (hRupCheck _ _ _ _ ⟨c, id, c_ptr, prf_ptr, prfBytes, idx3,
                      poolUsed + (clits.length + 1), poolRem', clits, ptrs, table, PoolUsed1, R,
                      rfl, hid_lt_cap, hprf_fit, hidx3_le, hclits_v,
                      ⟨PoolUsed, sep_comm PoolUsed (ZeroTermInts c_ptr clits)⟩, hm1,
                      fun r m2 hr => ⟨r, rfl, hr⟩⟩) ?_
                  rintro rok m2 hrup_res
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
                      have hidx4_gt : idx < idx4 := by dsimp [idx4, idx2] at hidx2_gt ⊢; omega
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
            · refine hJfail _ _ ⟨rfl, ?_, workState_collapse hm⟩
              rw [hpure, hdrop_idx]
              simp [checkPrfAux, htag97, bs1, hleb_uid, heven', hlen_cap, hnc_lt_id, hid_ge_cap]
          · refine hJfail _ _ ⟨rfl, ?_, workState_collapse hm⟩
            rw [hpure, hdrop_idx]
            simp [checkPrfAux, htag97, bs1, hleb_uid, heven', hid_le_nc]
        · -- Not `'a'`: check `'d'` (`100`)
          have htag_not97 : (tag == 97) = false := beq_false_of_ne (fun h => hnot_a (his_a_iff.mpr (beq_iff_eq.mpr h)))
          have his_d_iff : (BitVec.ofNat 64 tag.toNat = (100 : Val)) ↔ (tag == 100) = true := by
            rw [show (100 : Val) = BitVec.ofNat 64 (100 : UInt8).toNat from rfl, bv64_u8_eq, beq_iff_eq]
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
              refine readLeb128_spec hprf_fit hdidx_hi rfl rfl hdm_prf
                (fun hleb_none => hJfail _ _ ⟨rfl, by
                  rw [hpure, hdrop_idx]
                  have hdn : delLoopAux (bs1.length + 1) c.cap table bs1 = none := by
                    rw [hdel_eq]; simp [delLoopAux, hleb_none]
                  simp only [checkPrfAux, htag_not97, htag100, hlen_cap, ↓reduceIte, Bool.false_eq_true]
                  rw [hdn], workState_collapse hdm⟩)
                fun u bs_d hleb_u hu_lt _ hbsd_drop hdidx2_gt => ?_
              let didx2 := prfBytes.length - bs_d.length
              have hdidx2_le : didx2 ≤ prfBytes.length := Nat.sub_le _ _
              wp_unfold
              refine bv_eq_zero_branch (by omega : u < 2 ^ 64)
                (fun hu0 => by
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
                    rw [hdel_done]; rfl
                  rw [hstep_d, ← hbsd_drop]
                  exact checkPrfAux_fuel_irrel
                    (by have : bs1.length = prfBytes.length - (idx + 1) := List.length_drop; omega)
                    (by omega))
                (fun hu_ne0 => by
                  cases u with
                  | zero => exact absurd rfl hu_ne0
                  | succ u1 =>
                    let u := u1 + 1
                    refine bv_odd_branch (by omega : u < 2 ^ 64)
                      (fun ho => hJfail _ _ ⟨rfl, by
                        have hdn : delLoopAux (bs1.length + 1) c.cap table bs1 = none := by
                          rw [hdel_eq]; simp [delLoopAux, hleb_u, ho]
                        rw [hpure, hdrop_idx]
                        simp only [checkPrfAux, htag_not97, htag100, hlen_cap, ↓reduceIte, Bool.false_eq_true]
                        rw [hdn], workState_collapse hdm⟩)
                      (fun hdeven' => ?_)
                    let did := u / 2
                    rw [bv_shr_one (by omega : u < 2 ^ 64)]
                    refine bv_eq_zero_branch (by omega : did < 2 ^ 64)
                      (fun hdid0 => hJfail _ _ ⟨rfl, by
                        have hdn : delLoopAux (bs1.length + 1) c.cap table bs1 = none := by
                          rw [hdel_eq]; simp [delLoopAux, hleb_u, hdeven', hdid0, u]
                        rw [hpure, hdrop_idx]
                        simp only [checkPrfAux, htag_not97, htag100, hlen_cap, ↓reduceIte, Bool.false_eq_true]
                        rw [hdn], workState_collapse hdm⟩)
                      (fun hdid_nz' => ?_)
                    have hdid_nz : (did == 0) = false := beq_false_of_ne hdid_nz'
                    refine ult_branch (by omega : did < 2 ^ 64) hcap_bound
                      (fun hdid_lt_cap => ?_) (fun hdid_ge_cap => ?_)
                    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : did < 2 ^ 64)]
                      obtain ⟨hdplen, hdtlen, hdld_slot, hdslot_rel⟩ := workState_load_cb hdid_lt_cap hdm
                      refine ⟨_, hdld_slot, fun hdact => ?_, fun hdinact => ?_⟩
                      · obtain ⟨dlits, hdti_eq⟩ : ∃ lits, dtable[did]'(hdtlen ▸ hdid_lt_cap) = some lits := by
                          cases hti : dtable[did]'(hdtlen ▸ hdid_lt_cap) with
                          | none => rw [hti] at hdslot_rel; exact absurd hdslot_rel hdact
                          | some lits => exact ⟨lits, rfl⟩
                        have hdtr_new := tableRel_set_none (did := did) (workState_tableRel hdm)
                        obtain ⟨hok_dcb, hdm2⟩ := workState_store_cb hdid_lt_cap hdtr_new hdm
                        refine ⟨hok_dcb, ih_del (prfBytes.length - didx2) _ _ (by omega)
                          ⟨didx2, dptrs.set did 0, dtable.set did none, rfl,
                            by omega, hdidx2_le, rfl, ?_, hdm2⟩⟩
                        rw [hdel_eq]
                        have hdget_eq : dtable[did]? = some (some dlits) := by
                          rw [List.getElem?_eq_getElem (hdtlen ▸ hdid_lt_cap), hdti_eq]
                        have hstep_del : delLoopAux ((prfBytes.drop didx).length + 1) c.cap dtable (prfBytes.drop didx) =
                            delLoopAux (prfBytes.drop didx).length c.cap (dtable.set did none) bs_d := by
                          simp [delLoopAux, hleb_u, hdeven', did, hdid_nz, hdid_lt_cap, hdget_eq, u]
                        rw [hstep_del, ← hbsd_drop]
                        exact delLoopAux_fuel_irrel
                          (by have : bs_d.length = prfBytes.length - didx2 := by rw [hbsd_drop, List.length_drop]
                              have : (prfBytes.drop didx).length = prfBytes.length - didx := List.length_drop
                              omega)
                          (by omega)
                      · have hdptr0 : dptrs[did]'(hdplen ▸ hdid_lt_cap) = 0 := Classical.not_not.mp hdinact
                        have hdti_none : dtable[did]'(hdtlen ▸ hdid_lt_cap) = none := by
                          cases hti : dtable[did]'(hdtlen ▸ hdid_lt_cap) with
                          | none => rfl
                          | some lits => rw [hti] at hdslot_rel; exact absurd hdptr0 hdslot_rel.1
                        have hdget_none : dtable[did]? = some none := by
                          rw [List.getElem?_eq_getElem (hdtlen ▸ hdid_lt_cap), hdti_none]
                        refine hJfail _ _ ⟨rfl, ?_, workState_collapse hdm⟩
                        have hdn : delLoopAux (bs1.length + 1) c.cap table bs1 = none := by
                          rw [hdel_eq]
                          simp [delLoopAux, hleb_u, hdeven', did, hdid_nz, hdid_lt_cap, hdget_none, u]
                        rw [hpure, hdrop_idx]
                        simp only [checkPrfAux, htag_not97, htag100, hlen_cap, ↓reduceIte, Bool.false_eq_true]
                        rw [hdn]
                    · refine hJfail _ _ ⟨rfl, ?_, workState_collapse hdm⟩
                      have hdn : delLoopAux (bs1.length + 1) c.cap table bs1 = none := by
                        rw [hdel_eq]
                        simp [delLoopAux, hleb_u, hdeven', did, hdid_nz, hdid_ge_cap, u]
                      rw [hpure, hdrop_idx]
                      simp only [checkPrfAux, htag_not97, htag100, hlen_cap, ↓reduceIte, Bool.false_eq_true]
                      rw [hdn])
            · intro Jdel hJdel
              wp_unfold
              exact hJdel (prfBytes.length - (idx + 1)) _ _
                ⟨idx + 1, ptrs, table, rfl, Nat.le_refl _, hidx_lt, rfl, rfl, hm⟩
          · have htag_not100 : (tag == 100) = false := beq_false_of_ne (fun h => hnot_d (his_d_iff.mpr (beq_iff_eq.mpr h)))
            refine hJfail _ _ ⟨rfl, ?_, workState_collapse hm⟩
            rw [hpure, hdrop_idx]
            simp [checkPrfAux, htag_not97, htag_not100])
  · intro Jrec hJrec
    wp_unfold
    refine hJrec prfBytes.length _ _
      ⟨0, poolUsed0, poolRem0, ptrs0, table0, PoolUsed0, rfl, Nat.zero_le _, by simp, rfl, ?_⟩
    simpa using hm0

/-! ## 4. Verification of `lratCheckBytes` against `lratCheckBytesExactSpec` -/

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
  have hfit := c.fit_active; have hmv := c.hmv
  unfold dimacsBound at hmv; unfold WorkCfg.activeBytes at hfit
  have hact_le : 80 ≤ c.activeBytes := by unfold WorkCfg.activeBytes; omega
  have hvb_le : c.mv + 1 ≤ c.vBytes := by unfold WorkCfg.vBytes; omega
  have htb_le : c.tRaw ≤ c.tBytes := by unfold WorkCfg.tBytes WorkCfg.tRaw; omega
  have hact_fit : c.activeBytes ≤ 2 ^ 64 := by unfold WorkCfg.activeBytes at hlen ⊢; omega
  have hv_fit : c.vBytes ≤ 2 ^ 64 := by omega
  have ht_fit : c.tBytes ≤ 2 ^ 64 := by omega
  have hcb_fit : 8 * c.cap + 4 * c.poolInts ≤ 2 ^ 64 := by omega
  have htc_fit : c.tBytes + (8 * c.cap + 4 * c.poolInts) ≤ 2 ^ 64 := by omega
  have hptr : c.vb + BitVec.ofNat 64 (c.activeBytes - 80) = c.hdr + BitVec.ofNat 64 c.activeBytes := by
    apply BitVec.eq_of_toNat_eq
    unfold WorkCfg.vb WorkCfg.activeBytes WorkCfg.vBytes WorkCfg.tBytes WorkCfg.tRaw at *
    simp [BitVec.toNat_add]; omega
  rw [show c.hdr + (80 : Val) = c.vb from rfl,
    ← region_merge_eq (a := c.vb) (n1 := c.activeBytes - 80) (n2 := work_len - c.activeBytes)
      (n := work_len - 80) (by omega) (by omega), hptr,
    ← region_merge_eq (a := c.vb) (n1 := c.vBytes) (n2 := c.tBytes + (8 * c.cap + 4 * c.poolInts))
      (n := c.activeBytes - 80) (by unfold WorkCfg.activeBytes; omega) (by omega),
    ← region_merge_eq (a := c.vb) (n1 := c.mv + 1) (n2 := c.vBytes - (c.mv + 1))
      (n := c.vBytes) (by omega) hv_fit,
    show c.vb + BitVec.ofNat 64 c.vBytes = c.tb from rfl,
    ← region_merge_eq (a := c.tb) (n1 := c.tBytes) (n2 := 8 * c.cap + 4 * c.poolInts)
      (n := c.tBytes + (8 * c.cap + 4 * c.poolInts)) rfl htc_fit,
    ← region_merge_eq (a := c.tb) (n1 := c.tRaw) (n2 := c.tBytes - c.tRaw)
      (n := c.tBytes) (by omega) ht_fit,
    show c.tb + BitVec.ofNat 64 c.tRaw = c.tlim from rfl,
    show c.tb + BitVec.ofNat 64 c.tBytes = c.cb from rfl,
    ← region_merge_eq (a := c.cb) (n1 := 8 * c.cap) (n2 := 4 * c.poolInts)
      (n := 8 * c.cap + 4 * c.poolInts) rfl hcb_fit,
    show c.cb + BitVec.ofNat 64 (8 * c.cap) = c.pbase from rfl] at hm
  have hm_ord : (region c.vb (c.mv + 1) ⋆ region c.cb (8 * c.cap) ⋆
      (word8Array c.hdr hdrInit ⋆
        (region (c.vb + BitVec.ofNat 64 (c.mv + 1)) (c.vBytes - (c.mv + 1)) ⋆
          region c.tb c.tRaw ⋆ region c.tlim (c.tBytes - c.tRaw) ⋆ region c.pbase (4 * c.poolInts)) ⋆
        region (c.hdr + BitVec.ofNat 64 c.activeBytes) (work_len - c.activeBytes) ⋆ R_rest)) m :=
    sep_ac hm
  obtain ⟨f_vc, f_rem, hu1, hd1, ⟨f_v, f_c, hu2, hd2, hrv, hrc⟩, hrem⟩ := hm_ord
  obtain ⟨vs0, hvs0, hbv⟩ := region_to_byte1Array (c.mv + 1) (by omega) hrv
  obtain ⟨cs0, hcs0, hbc⟩ := region_to_word8Array c.cap (by omega) hrc
  exact ⟨vs0, cs0, hvs0, hcs0, sep_ac (show (byte1Array c.vb vs0 ⋆ word8Array c.cb cs0 ⋆ _) m from
    ⟨f_vc, f_rem, hu1, hd1, ⟨f_v, f_c, hu2, hd2, hbv, hbc⟩, hrem⟩)⟩

private theorem merge_workspace_tail (c : WorkCfg) (work_len : Nat)
    (hlen : c.activeBytes ≤ work_len)
    (hwfit : c.hdr.toNat + work_len < 2 ^ 64) :
    (region c.hdr c.activeBytes ⋆
      region (c.hdr + BitVec.ofNat 64 c.activeBytes) (work_len - c.activeBytes)) =
    region c.hdr work_len :=
  region_merge_eq (by omega) (by omega)

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
  refine ult_branch (a := work_len) (b := 128) (by omega) (by decide)
    (fun hlt128 => hQ 0 m0 (by simp [runLratCheckBytes, hlt128]) hm0)
    (fun hnot_lt128 => by
      have hsplit80 : region work_ptr work_len =
          (region work_ptr 80 ⋆ region (work_ptr + 80) (work_len - 80)) := by
        have : work_len = 80 + (work_len - 80) := by omega
        conv => lhs; rw [this, region_split (by omega)]
        rfl
      let R80 := region (work_ptr + 80) (work_len - 80) ⋆ Eq (prfBytes.At prf_ptr) ⋆ R_mem
      have hm0_hdr : (Eq (cnfBytes.At cnf_ptr) ⋆ region work_ptr 80 ⋆ R80) m0 := by
        have hm_tmp := hm0; rw [hsplit80] at hm_tmp
        exact sep_cast hm_tmp (by dsimp [R80]; ac_rfl)
      refine wp_call_ret1 _
        (hParseHeader _ _ _ _ ⟨cnf_ptr, work_ptr, cnfBytes, R80, rfl, hcnf_fit, by omega, hm0_hdr,
          fun r m1 hr => ⟨r, rfl, hr⟩⟩) ?_
      rintro hok m1 hhdr_res
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
        have hm1_focus : (word8Array work_ptr hdrInit ⋆ (Eq (cnfBytes.At cnf_ptr) ⋆ R80)) m1 :=
          sep_cast hm1 (by dsimp [hdrInit, cur0, idx0]; ac_rfl)
        have hld_mv : loadVal m1 .l .l true work_ptr = some (BitVec.ofNat 64 mv) := by
          rw [show work_ptr = work_ptr + BitVec.ofNat 64 (8 * 0) by simp]
          exact loadl_word8Array (i := 0) (by simp [hdrInit]) hm1_focus
        have hld_nc : loadVal m1 .l .l true (work_ptr + 8) = some (BitVec.ofNat 64 nc) :=
          loadl_word8Array (i := 1) (by simp [hdrInit]) hm1_focus
        refine ⟨_, hld_mv, _, hld_nc, ?_⟩
        have hcollapse_init : ((Eq (cnfBytes.At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆
            region work_ptr work_len) ⋆ R_mem) m1 := by
          have hr80 : ∀ f, word8Array work_ptr hdrInit f → region work_ptr 80 f := fun f hf => by
            simpa [hdrInit] using word8Array_to_region (by simp [hdrInit]) hf
          have h2 : (Eq (cnfBytes.At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆
              (region work_ptr 80 ⋆ region (work_ptr + 80) (work_len - 80)) ⋆ R_mem) m1 :=
            sep_cast (sep_mono hr80 hm1_focus) (by dsimp [R80]; ac_rfl)
          rw [← hsplit80] at h2
          exact sep_cast h2 (by ac_rfl)
        have hmv_lt : mv < 2 ^ 28 := hmv
        have hnc_lt : nc < 2 ^ 28 := hnc
        let v_bytes := ((mv + 8) / 8) * 8
        let t_raw := 4 * (mv + 1)
        let t_bytes := ((t_raw + 7) / 8) * 8
        let fixed := 80 + v_bytes + t_bytes
        have hbv_traw : (BitVec.ofNat 64 (mv + 1)) <<< (2 : Nat) = BitVec.ofNat 64 t_raw := by
          rw [bv_shl_ofNat (by omega) (by decide), show (mv + 1) <<< 2 = t_raw by simp [t_raw, Nat.shiftLeft_eq]; omega]
        rw [show BitVec.ofNat 64 mv + (1 : Val) = BitVec.ofNat 64 (mv + 1) from bv_add_ofNat mv 1,
          show BitVec.ofNat 64 mv + (8 : Val) = BitVec.ofNat 64 (mv + 8) from bv_add_ofNat mv 8,
          show (-8 : Val) = -(BitVec.ofNat 64 (2 ^ 3)) from rfl, bv_align_pow2 (by decide) (by omega),
          hbv_traw,
          show BitVec.ofNat 64 t_raw + (7 : Val) = BitVec.ofNat 64 (t_raw + 7) from bv_add_ofNat t_raw 7,
          bv_align_pow2 (by decide) (by dsimp [t_raw]; omega),
          bv_add_ofNat v_bytes t_bytes,
          show (80 : Val) + BitVec.ofNat 64 (v_bytes + t_bytes) = BitVec.ofNat 64 fixed from
            by rw [show (80 : Val) = BitVec.ofNat 64 80 from rfl, bv_add_ofNat]; congr 1; omega]
        refine ult_branch (by omega : work_len < 2 ^ 64)
          (by dsimp [fixed, v_bytes, t_bytes, t_raw]; omega : fixed < 2 ^ 64)
          (fun hlt_fixed => by
            refine hQ 0 m1 ?_ hcollapse_init
            rw [runLratCheckBytes_of_header hnot_lt128 hhdr_eq]
            dsimp only [fixed, v_bytes, t_bytes, t_raw] at hlt_fixed
            simp only [hlt_fixed, ↓reduceIte]; rfl)
          (fun hnot_lt_fixed => by
            let rem := work_len - fixed
            let c_half := rem / 16
            let p_cap := prfBytes.length % 268435456
            let want := nc + p_cap + 32
            let cap := if c_half < want then c_half else want
            have hbv_chalf : (BitVec.ofNat 64 rem) >>> (4 : Nat) = BitVec.ofNat 64 c_half := by
              rw [bv_shr_ofNat (by omega) (by decide), Nat.shiftRight_eq_div_pow]
            rw [bv_sub_ofNat (by omega) (by omega), hbv_chalf,
              show (268435455 : Val) = BitVec.ofNat 64 (2 ^ 28 - 1) from rfl,
              bv_and_pow2_sub_one (k := 28) (by omega),
              bv_add_ofNat nc p_cap,
              show BitVec.ofNat 64 (nc + p_cap) + (32 : Val) = BitVec.ofNat 64 want from
                bv_add_ofNat (nc + p_cap) 32]
            apply wp_join (fun as m' => as = [BitVec.ofNat 64 cap] ∧ m' = m1)
            · rintro _ m_cap ⟨rfl, hm_cap_eq⟩
              subst m_cap
              wp_unfold
              have hcap_le_chalf : cap ≤ c_half := by dsimp [cap]; split <;> omega
              have hcap_lt64 : cap < 2 ^ 64 := by dsimp [c_half, rem] at hcap_le_chalf; omega
              refine ule_branch hcap_lt64 (by omega : nc < 2 ^ 64)
                (fun hcap_le_nc => by
                  refine hQ 0 m1 ?_ hcollapse_init
                  rw [runLratCheckBytes_of_header hnot_lt128 hhdr_eq]
                  dsimp only [cap, c_half, want, p_cap, rem, fixed, v_bytes, t_bytes, t_raw] at hnot_lt_fixed hcap_le_nc
                  simp only [hnot_lt_fixed, hcap_le_nc, ↓reduceIte]; rfl)
                (fun hnot_cap_le_nc => by
                  have hnc_cap : nc < cap := by omega
                  let cb_bytes := 8 * cap
                  let pool_rem := rem - cb_bytes
                  let pool_ints := pool_rem / 4
                  have hcb_le_rem : cb_bytes ≤ rem := by dsimp [cb_bytes, c_half] at *; omega
                  have hact_le : 80 + v_bytes + t_bytes + 8 * cap + 4 * pool_ints ≤ work_len := by
                    dsimp [pool_ints, pool_rem, cb_bytes, rem]; omega
                  let c : WorkCfg := {
                    hdr := work_ptr, mv := mv, nc := nc, cap := cap, poolInts := pool_ints,
                    hmv := hmv, hnc := hnc, hnc_cap := hnc_cap,
                    hfit := by dsimp [v_bytes, t_bytes, t_raw] at hact_le; omega
                  }
                  have hc_act_le : c.activeBytes ≤ work_len := hact_le
                  have hbv_pool_bytes : BitVec.ofNat 64 pool_rem &&& (-4 : Val) =
                      BitVec.ofNat 64 (4 * pool_ints) := by
                    rw [show (-4 : Val) = -(BitVec.ofNat 64 (2 ^ 2)) from rfl,
                      bv_align_pow2 (by decide) (by omega)]
                    congr 1; dsimp [pool_ints]; omega
                  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcap_lt64,
                    bv_sub_ofNat hcb_le_rem (by omega), hbv_pool_bytes]
                  have hm1_ws_in : (word8Array c.hdr hdrInit ⋆
                      region (c.hdr + 80) (work_len - 80) ⋆
                      (Eq (cnfBytes.At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆ R_mem)) m1 :=
                    sep_cast hm1 (by dsimp [c, R80, hdrInit, cur0, idx0]; ac_rfl)
                  obtain ⟨vs0, cs0, hvs0, hcs0, hm1_split⟩ :=
                    split_workspace c work_len hc_act_le hwork_fit hm1_ws_in
                  let WMid := region (c.vb + BitVec.ofNat 64 (c.mv + 1)) (c.vBytes - (c.mv + 1)) ⋆
                    region c.tb c.tRaw ⋆ region c.tlim (c.tBytes - c.tRaw) ⋆
                    region c.pbase (4 * c.poolInts)
                  let RTail := region (c.hdr + BitVec.ofNat 64 c.activeBytes) (work_len - c.activeBytes)
                  let RRest := Eq (cnfBytes.At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆ R_mem
                  -- `@zv_done()`
                  apply wp_join (fun as m_zv => as = [] ∧
                    (word8Array c.cb cs0 ⋆ byte1Array c.vb (List.replicate (c.mv + 1) 0) ⋆
                      word8Array c.hdr hdrInit ⋆ WMid ⋆ RTail ⋆ RRest) m_zv)
                  · rintro _ m_zv ⟨rfl, hm_zv⟩
                    -- `@zcb_done()`
                    apply wp_join (fun as m_zcb => as = [] ∧
                      (word8Array c.hdr hdrInit ⋆ byte1Array c.vb (List.replicate (c.mv + 1) 0) ⋆
                        word8Array c.cb (List.replicate c.cap 0) ⋆ WMid ⋆ RTail ⋆ RRest) m_zcb)
                    · rintro _ m_zcb ⟨rfl, hm_zcb⟩
                      wp_unfold
                      let TailZ := byte1Array c.vb (List.replicate (c.mv + 1) 0) ⋆
                        word8Array c.cb (List.replicate c.cap 0) ⋆ WMid ⋆ RTail ⋆ RRest
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
                      obtain ⟨hok2, hm_s2⟩ := storel_word8Array (i := 2) (BitVec.ofNat 64 c.cap) (by simp [hdrInit]) hm_s0
                      obtain ⟨hok3, hm_s3⟩ := storel_word8Array (i := 3) c.vb (by simp [hdrInit]) hm_s2
                      obtain ⟨hok4, hm_s4⟩ := storel_word8Array (i := 4) c.tb (by simp [hdrInit]) hm_s3
                      obtain ⟨hok5, hm_s5⟩ := storel_word8Array (i := 5) c.tlim (by simp [hdrInit]) hm_s4
                      obtain ⟨hok6, hm_s6⟩ := storel_word8Array (i := 6) c.cb (by simp [hdrInit]) hm_s5
                      obtain ⟨hok7, hm_s7⟩ := storel_word8Array (i := 7) c.plim (by simp [hdrInit]) hm_s6
                      obtain ⟨hok8, hm_s8⟩ := storel_word8Array (i := 8) c.pbase (by simp [hdrInit]) hm_s7
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
                      let RBody := RTail ⋆ Eq (prfBytes.At prf_ptr) ⋆ R_mem
                      have hm_ws0 : (Eq (cnfBytes.At cnf_ptr) ⋆
                          WorkState c 0 c.poolInts cur0
                            (List.replicate c.cap 0) (List.replicate c.cap none) emp ⋆ RBody) m_hdr := by
                        have hm_tmp : (word8Array c.hdr (c.hdrWords (c.pbase + BitVec.ofNat 64 (4 * 0)) cur0) ⋆
                            TailZ) m_hdr := hm_s8
                        dsimp only [TailZ, WMid, RRest] at hm_tmp
                        rw [← assignBytes_empty c.mv, ← sep_emp (region c.pbase (4 * c.poolInts))] at hm_tmp
                        conv at hm_tmp =>
                          pattern (region c.pbase (4 * c.poolInts))
                          rw [show c.pbase = c.pbase + BitVec.ofNat 64 (4 * 0) from
                            (BitVec.add_zero c.pbase).symm]
                        have hm_ws0' : (WorkState c 0 c.poolInts cur0
                            (List.replicate c.cap 0) (List.replicate c.cap none) emp ⋆
                            (Eq (cnfBytes.At cnf_ptr) ⋆ RBody)) m_hdr :=
                          workState_sep.mpr ⟨Nat.zero_add _, tableRel_init c.mv c.cap,
                            fun f hf => by simpa [region_zero] using hf,
                            sep_cast hm_tmp (by dsimp [RBody]; ac_rfl)⟩
                        exact sep_cast hm_ws0' (by ac_rfl)
                      refine wp_call_ret1 _
                        (hParseBody _ _ _ _ ⟨c, cnf_ptr, cnfBytes, idx0, RBody,
                          rfl, hcnf_fit, by dsimp [idx0]; omega, hm_ws0,
                          fun r m_b hr => ⟨r, rfl, hr⟩⟩) ?_
                      rintro bok m_b hbody_res
                      wp_unfold
                      cases hbody_eq : parseBodyPure c.mv c.nc c.poolInts [] (cnfBytes.drop idx0) with
                      | none =>
                        rw [hbody_eq] at hbody_res
                        obtain ⟨rfl, hm_b_reg⟩ := hbody_res
                        refine ⟨fun h => absurd rfl h, fun _ => ?_⟩
                        have hm_b_full : ((Eq (cnfBytes.At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆
                            region work_ptr work_len) ⋆ R_mem) m_b := by
                          have h1 : (Eq (cnfBytes.At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆
                              (region c.hdr c.activeBytes ⋆ RTail) ⋆ R_mem) m_b := by
                            dsimp only [RBody] at hm_b_reg; exact sep_ac hm_b_reg
                          dsimp only [RTail] at h1
                          rw [merge_workspace_tail c work_len hc_act_le hwork_fit] at h1
                          exact h1
                        have hbody_eq' : parseBodyPure mv nc pool_ints [] bodyRest = none := by
                          simpa [c, idx0, ← hbody_drop] using hbody_eq
                        refine hQ 0 m_b ?_ hm_b_full
                        rw [runLratCheckBytes_of_header hnot_lt128 hhdr_eq]
                        dsimp only [pool_ints, pool_rem, cb_bytes, cap, c_half, want, p_cap, rem,
                          fixed, v_bytes, t_bytes, t_raw] at hnot_lt_fixed hnot_cap_le_nc hbody_eq'
                        simp only [hnot_lt_fixed, hnot_cap_le_nc, hbody_eq', ↓reduceIte]; rfl
                      | some val_body =>
                        rcases val_body with ⟨clauses, poolRem'⟩
                        rw [hbody_eq] at hbody_res
                        obtain ⟨rfl, _, _, ptrs, PoolUsed, hm_b⟩ := hbody_res
                        refine ⟨fun _ => ?_, fun h0 => absurd (Classical.not_not.mp h0) (by decide)⟩
                        obtain ⟨hok72, hm_b2⟩ := workState_store_cur (cur' := prf_ptr) hm_b
                        refine ⟨hok72, ?_⟩
                        let RPrf := RTail ⋆ Eq (cnfBytes.At cnf_ptr) ⋆ R_mem
                        have hm_prf_ws : (Eq (prfBytes.At prf_ptr) ⋆
                            WorkState c (c.poolInts - poolRem') poolRem' prf_ptr
                              ptrs (initClauseTable c.cap clauses) PoolUsed ⋆ RPrf)
                            (storeMem m_b .l (c.hdr + 72) prf_ptr) :=
                          sep_cast hm_b2 (by dsimp [RBody, RPrf]; ac_rfl)
                        refine wp_call_ret1
                          (fun r m_fin =>
                            r = (if checkPrfPure c.mv c.nc poolRem' (initClauseTable c.cap clauses) prfBytes = true
                              then 1 else 0) ∧
                            (Eq (prfBytes.At prf_ptr) ⋆ region c.hdr c.activeBytes ⋆ RPrf) m_fin)
                          (hCheckPrf _ _ _ _ ⟨c, prf_ptr, prfBytes, c.poolInts - poolRem', poolRem',
                            ptrs, initClauseTable c.cap clauses, PoolUsed, RPrf,
                            rfl, hprf_fit, hm_prf_ws,
                            fun r m_fin hr hm_fin => ⟨r, rfl, hr, hm_fin⟩⟩) ?_
                        rintro pok m_fin ⟨hpok, hm_fin⟩
                        wp_unfold
                        have hm_fin_full : ((Eq (cnfBytes.At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆
                            region work_ptr work_len) ⋆ R_mem) m_fin := by
                          have h1 : (Eq (cnfBytes.At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆
                              (region c.hdr c.activeBytes ⋆ RTail) ⋆ R_mem) m_fin := by
                            dsimp only [RPrf] at hm_fin; exact sep_ac hm_fin
                          dsimp only [RTail] at h1
                          rw [merge_workspace_tail c work_len hc_act_le hwork_fit] at h1
                          exact h1
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
                        as = [BitVec.ofNat 64 j] ∧ j ≤ c.cap ∧ r = c.cap - j ∧
                        (word8Array c.cb (List.replicate j 0 ++ cs0.drop j) ⋆ RestZcb) m)
                      · rintro Jzcb r as m ⟨j, rfl, hj_le, rfl, hm_j⟩ ih_zcb
                        wp_unfold
                        have hc_cap : c.cap = cap := rfl
                        refine ult_branch (by rw [hc_cap] at hj_le; omega : j < 2 ^ 64) hcap_lt64
                          (fun hj_lt => by
                            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by rw [hc_cap] at hj_le; omega : j < 2 ^ 64)]
                            obtain ⟨hok_j, hm_j'⟩ := storel_word8Array (i := j) 0 (by simp [hcs0]; dsimp [c]; omega) hm_j
                            rw [replicate_zero_set (hcs0 ▸ (by dsimp [c]; exact hj_lt))] at hm_j'
                            rw [show work_ptr + (80 : Val) + BitVec.ofNat 64 ((mv + 8) / 2 ^ 3 * 2 ^ 3) +
                                  BitVec.ofNat 64 ((t_raw + 7) / 2 ^ 3 * 2 ^ 3) = c.cb from rfl,
                              show BitVec.ofNat 64 j + (1 : Val) = BitVec.ofNat 64 (j + 1) from bv_add_ofNat j 1]
                            exact ⟨hok_j, ih_zcb (c.cap - (j + 1)) _ _ (by dsimp [c]; omega)
                              ⟨j + 1, rfl, by dsimp [c]; omega, rfl, hm_j'⟩⟩)
                          (fun hj_ge => by
                            obtain rfl : j = c.cap := by dsimp only [c] at hj_le ⊢; omega
                            rw [List.drop_of_length_le (by omega), List.append_nil] at hm_j
                            exact hJzcb_done _ _ ⟨rfl, sep_cast hm_j (by dsimp [RestZcb]; ac_rfl)⟩)
                      · intro Jzcb hJzcb
                        wp_unfold
                        exact hJzcb c.cap _ _ ⟨0, rfl, Nat.zero_le _, by simp,
                          sep_cast (by simpa using hm_zv) (by dsimp [RestZcb]; ac_rfl)⟩
                  · -- `@zv(%i)` loop
                    intro Jzv_done hJzv_done
                    let RestZv := word8Array c.cb cs0 ⋆ word8Array c.hdr hdrInit ⋆ WMid ⋆ RTail ⋆ RRest
                    apply wp_loop (fun r as m => ∃ i,
                      as = [BitVec.ofNat 64 i] ∧ i ≤ c.mv + 1 ∧ r = (c.mv + 1) - i ∧
                      (byte1Array c.vb (List.replicate i 0 ++ vs0.drop i) ⋆ RestZv) m)
                    · rintro Jzv r as m ⟨i, rfl, hi_le, rfl, hm_i⟩ ih_zv
                      wp_unfold
                      have hc_mv : c.mv = mv := rfl
                      refine ule_branch (by rw [hc_mv] at hi_le; omega : i < 2 ^ 64) (by omega : mv < 2 ^ 64)
                        (fun hi_le_mv => by
                          obtain ⟨hok_i, hm_i'⟩ := storeb_byte1Array (i := i) 0 (by simp [hvs0, hc_mv]; omega) hm_i
                          rw [replicate_zero_set (hvs0 ▸ (by rw [hc_mv]; omega : i < c.mv + 1))] at hm_i'
                          rw [show work_ptr + (80 : Val) = c.vb from rfl,
                            show BitVec.ofNat 64 i + (1 : Val) = BitVec.ofNat 64 (i + 1) from bv_add_ofNat i 1]
                          exact ⟨hok_i, ih_zv ((c.mv + 1) - (i + 1)) _ _ (by dsimp [c]; omega)
                            ⟨i + 1, rfl, by dsimp [c]; omega, rfl, hm_i'⟩⟩)
                        (fun hi_gt => by
                          obtain rfl : i = c.mv + 1 := by dsimp only [c] at hi_le ⊢; omega
                          rw [List.drop_of_length_le (by omega), List.append_nil] at hm_i
                          exact hJzv_done _ _ ⟨rfl, sep_cast hm_i (by dsimp [RestZv]; ac_rfl)⟩)
                    · intro Jzv hJzv
                      wp_unfold
                      have hm1_split' : (byte1Array c.vb (List.replicate 0 0 ++ vs0.drop 0) ⋆
                          word8Array c.cb cs0 ⋆ word8Array c.hdr hdrInit ⋆ WMid ⋆
                          RTail ⋆ RRest) m1 := by simpa [WMid, RTail, RRest] using hm1_split
                      exact hJzv (c.mv + 1) _ _ ⟨0, rfl, Nat.zero_le _, by simp,
                        sep_cast hm1_split' (by dsimp [RestZv]; ac_rfl)⟩)
            · intro Jgot_cap hJgot_cap
              wp_unfold
              refine ult_branch (by dsimp [c_half, rem]; omega : c_half < 2 ^ 64)
                (by dsimp [want, p_cap]; omega : want < 2 ^ 64)
                (fun hlt_w => hJgot_cap _ _ ⟨by simp [cap, hlt_w], rfl⟩)
                (fun hge_w => hJgot_cap _ _ ⟨by simp [cap, hge_w], rfl⟩)))

end LeanQbe.LratBytes
