module

public import LeanQbe.T.Examples.LratBytesSpec
import LeanQbe.T.Logic.C0HeadStep
meta import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.ProofKit
meta import LeanQbe.T.Logic.ProofKit
import all Kraken.Separation

/-!
# Verification of `lbCheckPrf`, `lratCheckBytes`, and `checkPrfPure` soundness in `LeanQbe.T`

Proves:
1. Pure LRAT proof soundness (`checkPrfAux_sound_of`, `runLratCheckBytes_sound_of`).
2. `lbCheckPrf_correct_of`: total-correctness `Func.spec` of `lbCheckPrf` against `lbCheckPrfSpec`.
3. `lratCheckBytes_exact_of`: total-correctness `Func.spec` of `lratCheckBytes` against
   `lratCheckBytesExactSpec`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.LratBytes

open Std Std.ExtHashMap Std.Sat
open Std.Tactic.BVDecide.LRAT.Internal
open Kraken.Bedrock2.Test
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.ProofKit
open LeanQbe.T.C0HeadStep

@[local bv_c0] private theorem list_length_nil {α : Type _} : ([] : List α).length = 0 := rfl
@[local bv_c0] private theorem list_length_cons {α : Type _} (x : α) (xs : List α) :
    (x :: xs).length = xs.length + 1 := List.length_cons
@[local bv_c0] private theorem list_length_set {α : Type _} (xs : List α) (i : Nat) (v : α) :
    (xs.set i v).length = xs.length := List.length_set
@[local bv_c0] private theorem hdrWords_length (c : WorkCfg) (pcur cur : BitVec 64) :
    (c.hdrWords pcur cur).length = 10 := rfl
@[local bv_c0] private theorem bv_c0_dimacsBound : dimacsBound = 2 ^ 28 := rfl
@[local bv_c0] private theorem bv_c0_and_one (u : Nat) :
    BitVec.ofNat 64 u &&& 1#64 = BitVec.ofNat 64 (u % 2) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_and, Nat.and_one_is_mod, Nat.mod_mod_of_dvd _ (by decide : 2 ∣ 2 ^ 64)]
@[local bv_c0 high] private theorem bv_c0_ofNat_and_1 (u : Nat) :
    BitVec.ofNat 64 u &&& (1 : BitVec 64) = BitVec.ofNat 64 (u % 2) := bv_c0_and_one u
@[local bv_c0 high] private theorem bv_c0_toNat_and_1 (x : BitVec 64) :
    (x &&& (1 : BitVec 64)).toNat = x.toNat % 2 := bv_c0_toNat_and_one_64 x

@[local c0_load] private theorem c0_load_word8Array_zero {a : BitVec 64}
    {xs : List (BitVec 64)} {R : Mem 64 → Prop} {m : Mem 64}
    (h : (word8Array a xs ⋆ R) m) (hi : 0 < xs.length) : loadVal m i64 a = some (xs[0]'hi) := by
  simpa using load_word8Array (i := 0) hi h

@[local c0_load] private theorem c0_load_word8Array_off {a off : BitVec 64}
    {xs : List (BitVec 64)} {R : Mem 64 → Prop} {m : Mem 64} (h : (word8Array a xs ⋆ R) m)
    (hdiv : off.toNat % 8 = 0) (hi : off.toNat / 8 < xs.length) :
    loadVal m i64 (a + off) = some (xs[off.toNat / 8]'hi) := by
  have heq : BitVec.ofNat 64 (8 * (off.toNat / 8)) = off := by c0_bv_omega
  simpa [heq] using load_word8Array (i := off.toNat / 8) hi h

@[local c0_store] private theorem c0_store_word8Array_off {a off v : BitVec 64}
    {vs : List (BitVec 64)} {F : Mem 64 → Prop} {m : Mem 64}
    (hoff : off.toNat % 8 = 0) (hi : off.toNat / 8 < vs.length) (hm : (word8Array a vs ⋆ F) m) :
    storeOk m i64 (a + off) ∧
      (word8Array a (vs.set (off.toNat / 8) v) ⋆ F) (storeMem m i64 (a + off) v) := by
  have hmem : a + BitVec.ofNat 64 (8 * (off.toNat / 8)) = a + off := by congr 1; c0_bv_omega
  simpa [hmem] using store_word8Array (i := off.toNat / 8) v hi hm

@[local c0_store] private theorem c0_store_byte1Array_off {a off : BitVec 64} (v : BitVec 8)
    {vs : List (BitVec 64)} {F : Mem 64 → Prop} {m : Mem 64}
    (hi : off.toNat < vs.length) (hm : (byte1Array a vs ⋆ F) m) :
    storeOk m i8 (a + off) ∧
      (byte1Array a (vs.set off.toNat (v.setWidth 64)) ⋆ F) (storeMem m i8 (a + off) v) := by
  have hmem : a + BitVec.ofNat 64 off.toNat = a + off := by congr 1; c0_bv_omega
  simpa [hmem] using store_byte1Array (i := off.toNat) v hi hm

/-! ## 1. Pure stream-length, fuel-invariance, and literal-validity lemmas -/

private theorem readLeb128Pure_props {bs : List UInt8} {u : Nat} {bs' : List UInt8}
    (h : readLeb128Pure bs = some (u, bs')) :
    u < 2 ^ 28 ∧ bs'.length < bs.length ∧ bs' = bs.drop (bs.length - bs'.length) := by
  obtain ⟨hu, hlt, k, _, hkle, rfl⟩ := readLeb128Pure_some h; grind

private theorem drop_trans_len {full bs' : List UInt8} {idx : Nat} (hidx : idx ≤ full.length)
    (h : bs' = (full.drop idx).drop ((full.drop idx).length - bs'.length))
    (hlen : bs'.length ≤ (full.drop idx).length) :
    bs' = full.drop (full.length - bs'.length) ∧ full.length - bs'.length ≤ full.length := by
  have hfl : (full.drop idx).length = full.length - idx := List.length_drop
  rw [List.drop_drop] at h; grind

private theorem runLratCheckBytes_lt128 {cnfBytes prfBytes : List UInt8} {work_len : Nat}
    (h : work_len < 128) : runLratCheckBytes cnfBytes prfBytes work_len = false := by
  unfold runLratCheckBytes; simp only [h, ↓reduceIte]
private theorem runLratCheckBytes_hdr_none {cnfBytes prfBytes : List UInt8} {work_len : Nat}
    (h128 : ¬ (work_len < 128)) (hhdr : parseHeader cnfBytes = none) :
    runLratCheckBytes cnfBytes prfBytes work_len = false := by
  unfold runLratCheckBytes; simp only [h128, ↓reduceIte, hhdr]

private theorem readAddLitsAux_lt {fuel mv poolRem : Nat} {acc : List (BitVec 64)}
    {bs : List UInt8} {clits : List (BitVec 64)} {poolRem' : Nat} {bs' : List UInt8}
    (h : readAddLitsAux fuel mv poolRem acc bs = some (clits, poolRem', bs')) :
    bs'.length < bs.length := by
  induction fuel generalizing poolRem acc bs with
  | zero => rw [readAddLitsAux.eq_1] at h; nomatch h
  | succ fuel ih =>
    rw [readAddLitsAux.eq_2] at h; split at h; · nomatch h
    split at h
    · nomatch h
    · cases h; exact (readLeb128Pure_props ‹readLeb128Pure bs = some _›).2.1
    · have hlt1 := (readLeb128Pure_props ‹readLeb128Pure bs = some _›).2.1
      dsimp only at h; split at h; · nomatch h
      exact Nat.lt_trans (ih h) hlt1

private theorem readAddLitsPure_lt {mv poolRem : Nat} {bs : List UInt8}
    {clits : List (BitVec 64)} {poolRem' : Nat} {bs' : List UInt8}
    (h : readAddLitsPure mv poolRem bs = some (clits, poolRem', bs')) :
    bs'.length < bs.length := readAddLitsAux_lt h

private theorem consumeHintsAux_lt {fuel id : Nat} {table : List (Option (List (BitVec 64)))}
    {bs bs' : List UInt8} (h : consumeHintsAux fuel id table bs = some bs') :
    bs'.length < bs.length := by
  induction fuel generalizing bs with
  | zero => rw [consumeHintsAux.eq_1] at h; nomatch h
  | succ fuel ih =>
    rcases hleb : readLeb128Pure bs with _ | ⟨_ | u_pred, bs1⟩ <;>
      rw [consumeHintsAux.eq_2, hleb] at h
    · nomatch h
    · cases h; exact (readLeb128Pure_props hleb).2.1
    · dsimp only at h; have hlt1 := (readLeb128Pure_props hleb).2.1
      by_cases hodd : ((u_pred + 1) % 2 != 0) = true <;> simp only [hodd, ↓reduceIte] at h
      · cases h
      · by_cases haid : (u_pred + 1) / 2 < id <;> simp only [haid, ↓reduceIte] at h
        · rcases htbl : table[(u_pred + 1) / 2]? with _ | _ | alits <;>
            rw [htbl] at h <;> first | cases h | exact Nat.lt_trans (ih h) hlt1
        · cases h

private theorem rupPhase2Aux_lt {fuel mv id : Nat} {table : List (Option (List (BitVec 64)))}
    {vals : List (BitVec 64)} {tl : Nat} {bs bs' : List UInt8}
    (h : rupPhase2Aux fuel mv id table vals tl bs = some bs') : bs'.length < bs.length := by
  induction fuel generalizing vals tl bs with
  | zero => rw [rupPhase2Aux.eq_1] at h; nomatch h
  | succ fuel ih =>
    rcases hleb : readLeb128Pure bs with _ | ⟨_ | u_pred, bs1⟩ <;>
      rw [rupPhase2Aux.eq_2, hleb] at h
    · nomatch h
    · nomatch h
    · dsimp only at h; have hlt1 := (readLeb128Pure_props hleb).2.1
      by_cases hodd : ((u_pred + 1) % 2 != 0) = true <;> simp only [hodd, ↓reduceIte] at h
      · cases h
      · by_cases haid : (u_pred + 1) / 2 < id <;> simp only [haid, ↓reduceIte] at h
        · rcases htbl : table[(u_pred + 1) / 2]? with _ | _ | alits <;>
            rw [htbl] at h <;> first | cases h | dsimp only at h
          rcases hin : rupInnerPure mv alits 0 vals tl with _ | ⟨unit, vals', tl'⟩ <;>
            rw [hin] at h <;> first | cases h | dsimp only at h
          by_cases hu : (unit != 0) = true <;> simp only [hu, ↓reduceIte] at h
          · exact Nat.lt_trans (ih h) hlt1
          · exact Nat.lt_trans (consumeHintsAux_lt h) hlt1
        · cases h

private theorem rupCheckPure_lt {mv id : Nat} {clits : List (BitVec 64)}
    {table : List (Option (List (BitVec 64)))} {bs bs' : List UInt8}
    (h : rupCheckPure mv id clits table bs = some bs') : bs'.length < bs.length := by
  unfold rupCheckPure at h
  cases hp : rupPhase1Pure mv clits (List.replicate (mv + 1) 0) 0 <;> rw [hp] at h
  · nomatch h
  · exact consumeHintsAux_lt h
  · exact rupPhase2Aux_lt h

private theorem delLoopAux_props {fuel cap : Nat} {table : List (Option (List (BitVec 64)))}
    {bs : List UInt8} {table' : List (Option (List (BitVec 64)))} {bs' : List UInt8}
    (h : delLoopAux fuel cap table bs = some (table', bs')) :
    bs'.length < bs.length ∧ bs' = bs.drop (bs.length - bs'.length) := by
  induction fuel generalizing table bs with
  | zero => rw [delLoopAux.eq_1] at h; nomatch h
  | succ fuel ih =>
    rcases hleb : readLeb128Pure bs with _ | ⟨_ | u_pred, bs1⟩ <;>
      rw [delLoopAux.eq_2, hleb] at h
    · nomatch h
    · cases h; exact (readLeb128Pure_props hleb).2
    · dsimp only at h; obtain ⟨_, hlt1, hdrop1⟩ := readLeb128Pure_props hleb
      by_cases hodd : ((u_pred + 1) % 2 != 0) = true <;> simp only [hodd, ↓reduceIte] at h
      · cases h
      · by_cases hbad : ((u_pred + 1) / 2 == 0 || !decide ((u_pred + 1) / 2 < cap)) = true <;>
          simp only [hbad, ↓reduceIte] at h
        · cases h
        · rcases htbl : table[(u_pred + 1) / 2]? with _ | _ | alits <;>
            rw [htbl] at h <;> first | cases h | dsimp only at h
          obtain ⟨hlt2, hdrop2⟩ := ih h
          rw [hdrop1] at hdrop2
          exact ⟨by omega, (drop_trans_len (by omega) hdrop2 (by rw [← hdrop1]; omega)).1⟩

private theorem delLoopAux_fuel_irrel {f1 f2 cap : Nat} {table : List (Option (List (BitVec 64)))}
    {bs : List UInt8} (hf1 : bs.length < f1) (hf2 : bs.length < f2) :
    delLoopAux f1 cap table bs = delLoopAux f2 cap table bs := by
  induction f1 generalizing f2 table bs with
  | zero => omega
  | succ f1 ih =>
    cases f2 with
    | zero => omega
    | succ f2 =>
      rcases heq : readLeb128Pure bs with _ | ⟨_ | u_pred, bs1⟩ <;>
        rw [delLoopAux.eq_2, delLoopAux.eq_2, heq]
      · rfl
      · dsimp only; have hlt1 := (readLeb128Pure_props heq).2.1
        by_cases hodd : ((u_pred + 1) % 2 != 0) = true <;>
          simp only [hodd, Bool.false_eq_true, ↓reduceIte]
        by_cases hbad : ((u_pred + 1) / 2 == 0 || !decide ((u_pred + 1) / 2 < cap)) = true <;>
          simp only [hbad, Bool.false_eq_true, ↓reduceIte]
        rcases table[(u_pred + 1) / 2]? with _ | _ | _ <;>
          first | rfl | exact ih (by omega) (by omega)

private theorem checkPrfAux_fuel_irrel {f1 f2 mv nc poolRem : Nat}
    {table : List (Option (List (BitVec 64)))} {bs : List UInt8}
    (hf1 : bs.length < f1) (hf2 : bs.length < f2) :
    checkPrfAux f1 mv nc poolRem table bs = checkPrfAux f2 mv nc poolRem table bs := by
  induction f1 generalizing f2 poolRem table bs with
  | zero => omega
  | succ f1 ih =>
    cases f2 with
    | zero => omega
    | succ f2 =>
      cases bs with
      | nil => rw [checkPrfAux.eq_2, checkPrfAux.eq_2] <;> omega
      | cons tag bs1 =>
        have hbs1 : bs1.length < f1 ∧ bs1.length < f2 := by simp at hf1 hf2; omega
        rw [checkPrfAux.eq_3, checkPrfAux.eq_3]
        by_cases h97 : (tag == 97) = true <;> simp only [h97, Bool.false_eq_true, ↓reduceIte]
        · rcases heq1 : readLeb128Pure bs1 with _ | ⟨uid, bs2⟩; · rfl
          dsimp only; have hlt1 := (readLeb128Pure_props heq1).2.1
          split; · rfl
          split; · rfl
          rcases table[uid / 2]? with _ | _ | _ <;> try rfl
          dsimp only; rcases heq2 : readAddLitsPure mv poolRem bs2 with _ | ⟨clits, poolRem', bs3⟩
          · rfl
          dsimp only; have hlt2 := readAddLitsPure_lt heq2
          rcases heq3 : rupCheckPure mv (uid / 2) clits table bs3 with _ | bs4; · rfl
          dsimp only; have hlt3 := rupCheckPure_lt heq3
          split <;> first | rfl | exact ih (by omega) (by omega)
        · by_cases h100 : (tag == 100) = true <;>
            simp only [h100, Bool.false_eq_true, ↓reduceIte]
          rcases heqd : delLoopAux (bs1.length + 1) table.length table bs1 with _ | ⟨table', bs2⟩
          · rfl
          dsimp only; obtain ⟨hltd, _⟩ := delLoopAux_props heqd; exact ih (by omega) (by omega)

private theorem readAddLitsAux_valid {fuel mv poolRem : Nat} {acc : List (BitVec 64)}
    {bs : List UInt8} {clits : List (BitVec 64)} {poolRem' : Nat} {bs' : List UInt8}
    (hmv : mv < dimacsBound) (hacc : ∀ x ∈ acc, IsValidLit mv x)
    (h : readAddLitsAux fuel mv poolRem acc bs = some (clits, poolRem', bs')) :
    ∀ x ∈ clits, IsValidLit mv x := by
  induction fuel generalizing poolRem acc bs with
  | zero => rw [readAddLitsAux.eq_1] at h; nomatch h
  | succ fuel ih =>
    cases hpool : (poolRem == 0)
    · rcases heq : readLeb128Pure bs with _ | ⟨_ | u_pred, bs1⟩ <;>
        simp only [readAddLitsAux.eq_2, hpool, heq, Bool.false_eq_true, ↓reduceIte] at h
      · nomatch h
      · obtain ⟨rfl, _, _⟩ := Option.some.inj h; exact fun x hx => hacc x (List.mem_reverse.mp hx)
      · obtain ⟨hu, _, _⟩ := readLeb128Pure_props heq
        cases hbad : ((u_pred + 1) / 2 == 0 || mv < (u_pred + 1) / 2)
        · rw [hbad] at h; simp only [Bool.false_eq_true, ↓reduceIte] at h
          simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, decide_eq_false_iff_not] at hbad
          have hv_valid := isValidLit_decodeZigZag hu (by omega) (by omega) hmv
          exact ih (fun x hx => by
            rcases List.mem_cons.mp hx with rfl | hx; exact hv_valid; exact hacc x hx) h
        · rw [hbad] at h; nomatch h
    · rw [readAddLitsAux.eq_2, hpool] at h; nomatch h

private theorem readAddLitsPure_valid {mv poolRem : Nat} {bs : List UInt8}
    {clits : List (BitVec 64)} {poolRem' : Nat} {bs' : List UInt8}
    (hmv : mv < dimacsBound) (h : readAddLitsPure mv poolRem bs = some (clits, poolRem', bs')) :
    ∀ x ∈ clits, IsValidLit mv x := readAddLitsAux_valid hmv (by simp) h

/-! ## 2. Pure LRAT proof soundness (`checkPrfAux_sound_of`, `runLratCheckBytes_sound_of`) -/

private abbrev TableSound (mv : Nat) (F : CNF Nat)
    (table : List (Option (List (BitVec 64)))) : Prop :=
  ∀ (i : Nat) (lits : List (BitVec 64)), table[i]? = some (some lits) →
    (∀ x ∈ lits, IsValidLit mv x) ∧ CNF.EntailsClause F (toClause lits)

private theorem entailsClause_add_mono {F : CNF Nat} {c d : CNF.Clause Nat}
    (h : CNF.EntailsClause F d) : CNF.EntailsClause (F.add c) d := by
  rw [CNF.entails_clause_def] at h ⊢; intro a ha
  rw [CNF.sat_def, CNF.eval_add, Bool.and_eq_true] at ha; exact h a ((CNF.sat_def a F).mpr ha.2)

private theorem entailsClause_add_self (F : CNF Nat) (c : CNF.Clause Nat) :
    CNF.EntailsClause (F.add c) c := by
  rw [CNF.entails_clause_def]; intro a ha
  rw [CNF.sat_def, CNF.eval_add, Bool.and_eq_true] at ha
  exact (CNF.Clause.sat_def a c).mpr ha.1

private theorem foldl_add_entails {clauses : List (List (BitVec 64))} {F : CNF Nat}
    {c : CNF.Clause Nat} (hc : CNF.EntailsClause F c) :
    CNF.EntailsClause (clauses.foldl (fun acc lits => acc.add (toClause lits)) F) c := by
  induction clauses generalizing F with
  | nil => exact hc
  | cons _ _ ih => exact ih (entailsClause_add_mono hc)

private theorem foldl_mem_entails {clauses : List (List (BitVec 64))} {F : CNF Nat}
    {lits : List (BitVec 64)} (hmem : lits ∈ clauses) :
    CNF.EntailsClause (clauses.foldl (fun acc ls => acc.add (toClause ls)) F) (toClause lits) := by
  induction clauses generalizing F with
  | nil => nomatch hmem
  | cons hd tl ih =>
    rcases List.mem_cons.mp hmem with rfl | htl
    · exact @foldl_add_entails tl (F.add (toClause lits)) (toClause lits)
        (entailsClause_add_self F (toClause lits))
    · exact ih htl

private theorem tableSound_set_none {mv : Nat} {F : CNF Nat}
    {table : List (Option (List (BitVec 64)))} (ht : TableSound mv F table) (did : Nat) :
    TableSound mv F (table.set did none) := by
  intro i lits hi
  by_cases h : i = did
  · subst h; by_cases hlt : i < table.length <;> simp_all
  · rw [List.getElem?_set_ne (Ne.symm h)] at hi; exact ht i lits hi

private theorem tableSound_set_some {mv : Nat} {F : CNF Nat}
    {table : List (Option (List (BitVec 64)))} (ht : TableSound mv F table) (id : Nat)
    {clits : List (BitVec 64)} (hval : ∀ x ∈ clits, IsValidLit mv x)
    (hent : CNF.EntailsClause F (toClause clits)) :
    TableSound mv F (table.set id (some clits)) := by
  intro i lits hi
  by_cases h : i = id
  · subst h; by_cases hlt : i < table.length
    · rw [List.getElem?_set_self hlt] at hi; cases hi; exact ⟨hval, hent⟩
    · rw [List.getElem?_eq_none (by rw [List.length_set]; omega)] at hi; nomatch hi
  · rw [List.getElem?_set_ne (Ne.symm h)] at hi; exact ht i lits hi

private theorem initClauseTable_sound {mv cap : Nat} {clauses : List (List (BitVec 64))}
    (hvalid : ∀ cl ∈ clauses, ∀ x ∈ cl, IsValidLit mv x) :
    TableSound mv (clauses.foldl (fun acc lits => acc.add (toClause lits)) CNF.empty)
      (initClauseTable cap clauses) := by
  intro i lits hget; unfold initClauseTable at hget
  cases i with
  | zero => simp at hget
  | succ j =>
    simp only [List.cons_append, List.getElem?_cons_succ] at hget
    by_cases hj : j < (clauses.map some).length
    · rw [List.getElem?_append_left hj, List.getElem?_eq_getElem hj, List.getElem_map] at hget
      simp only [Option.some.injEq] at hget; subst hget
      have hj' : j < clauses.length := by simpa using hj
      exact ⟨hvalid _ (List.getElem_mem hj'), foldl_mem_entails (List.getElem_mem hj')⟩
    · grind

private theorem delLoopAux_sound {fuel cap mv : Nat} {F : CNF Nat}
    {table table' : List (Option (List (BitVec 64)))} {bs bs' : List UInt8}
    (ht : TableSound mv F table) (h : delLoopAux fuel cap table bs = some (table', bs')) :
    TableSound mv F table' := by
  induction fuel generalizing table bs with
  | zero => rw [delLoopAux.eq_1] at h; nomatch h
  | succ fuel ih =>
    rw [delLoopAux.eq_2] at h; split at h; · contradiction
    · cases h; exact ht
    · split at h <;> try contradiction
      dsimp only at h; split at h <;> try contradiction
      split at h <;> try contradiction
      exact ih (tableSound_set_none ht _) h

private theorem unsat_of_entails_empty {cnf₀ F : CNF Nat}
    (hent : cnf₀.Entails F) (hemp : CNF.EntailsClause F (toClause [])) : cnf₀.Unsat := by
  rw [CNF.unsat_iff_not_sat]; intro a ha
  have hc : (toClause []).Sat a :=
    CNF.entails_clause_def.mp hemp a ((CNF.entails_def cnf₀ F).mp hent a ha)
  rw [CNF.Clause.sat_def] at hc
  have hev : CNF.Clause.eval a (toClause []) = false := by
    rw [show toClause [] = CNF.Clause.empty from CNF.Clause.ext (by simp [toClause])]
    exact CNF.Clause.eval_empty a
  grind

abbrev RupSoundHyp : Prop :=
  ∀ {mv id : Nat} {clits : List (BitVec 64)}
    {table : List (Option (List (BitVec 64)))} {bs bs' : List UInt8} {F : CNF Nat},
    mv < dimacsBound → (∀ x ∈ clits, IsValidLit mv x) →
    (∀ aid < id, ∀ alits, table[aid]? = some (some alits) →
      (∀ x ∈ alits, IsValidLit mv x) ∧ CNF.EntailsClause F (toClause alits)) →
    rupCheckPure mv id clits table bs = some bs' → CNF.EntailsClause F (toClause clits)

private theorem checkPrfAux_sound_of (hrup_sound : RupSoundHyp)
    {fuel mv nc poolRem : Nat} {table : List (Option (List (BitVec 64)))} {bs : List UInt8}
    {cnf₀ F : CNF Nat} (hmv : mv < dimacsBound) (hent : cnf₀.Entails F)
    (htable : TableSound mv F table) (hchk : checkPrfAux fuel mv nc poolRem table bs = true) :
    cnf₀.Unsat := by
  induction fuel generalizing poolRem table bs F with
  | zero => rw [checkPrfAux.eq_1] at hchk; cases hchk
  | succ fuel ih =>
    cases bs with
    | nil => simp [checkPrfAux] at hchk
    | cons tag bs1 =>
      rw [checkPrfAux.eq_3] at hchk
      by_cases h97 : (tag == 97) = true <;> simp only [h97, Bool.false_eq_true, ↓reduceIte] at hchk
      · rcases heq_uid : readLeb128Pure bs1 with _ | ⟨uid, bs2⟩; · rw [heq_uid] at hchk; cases hchk
        rw [heq_uid] at hchk; dsimp only at hchk
        split at hchk; · cases hchk
        split at hchk; · cases hchk
        rcases htbl : table[uid / 2]? with _ | _ | _ <;> rw [htbl] at hchk <;>
          first | cases hchk | dsimp only at hchk
        rcases hread : readAddLitsPure mv poolRem bs2 with _ | ⟨clits, poolRem', bs3⟩
        · rw [hread] at hchk; cases hchk
        rw [hread] at hchk; dsimp only at hchk
        have hclits := readAddLitsPure_valid hmv hread
        rcases hrup : rupCheckPure mv (uid / 2) clits table bs3 with _ | bs4
        · rw [hrup] at hchk; cases hchk
        rw [hrup] at hchk; dsimp only at hchk
        have hent_cl := hrup_sound hmv hclits (fun aid _ alits hget => htable aid alits hget) hrup
        by_cases hemp : clits.isEmpty = true <;>
          simp only [hemp, Bool.false_eq_true, ↓reduceIte] at hchk
        · exact unsat_of_entails_empty hent (List.isEmpty_iff.mp hemp ▸ hent_cl)
        · exact ih hent (tableSound_set_some htable (uid / 2) hclits hent_cl) hchk
      · by_cases h100 : (tag == 100) = true <;>
          simp only [h100, Bool.false_eq_true, ↓reduceIte] at hchk
        rcases hdel : delLoopAux (bs1.length + 1) table.length table bs1 with _ | ⟨table', bs2⟩
        · rw [hdel] at hchk; cases hchk
        rw [hdel] at hchk; dsimp only at hchk; exact ih hent (delLoopAux_sound htable hdel) hchk

private theorem parseHeader_bounds {bs : List UInt8} {mv nc : Nat} {rest : List UInt8}
    (h : parseHeader bs = some (mv, nc, rest)) : mv < dimacsBound ∧ nc < dimacsBound := by
  unfold parseHeader at h; simp only [bind, Option.bind] at h
  split at h <;> try cases h
  rcases h2 : skipWs1 _ with _ | bs2 <;> rw [h2] at h; · cases h
  dsimp only at h; split at h <;> try cases h
  rcases h3 : skipWs1 _ with _ | bs4 <;> rw [h3] at h; · cases h
  dsimp only at h; rcases hmv : parseNat bs4 with _ | ⟨mv', bs5⟩ <;> rw [hmv] at h; · cases h
  dsimp only at h; rcases h4 : skipWs1 bs5 with _ | bs6 <;> rw [h4] at h; · cases h
  dsimp only at h; rcases hnc : parseNat bs6 with _ | ⟨nc', bs7⟩ <;> rw [hnc] at h; · cases h
  rcases h with ⟨rfl, rfl, rfl⟩; exact ⟨parseNat_lt_bound hmv, parseNat_lt_bound hnc⟩

/-- Pure soundness of `runLratCheckBytes` given `parseBodyPure_sound` and `rupCheckPure_sound`. -/
theorem runLratCheckBytes_sound_of
    (hbody_sound : ∀ {cnfBytes bodyRest : List UInt8} {mv nc poolInts poolRem' : Nat}
      {clauses : List (List (BitVec 64))},
      parseHeader cnfBytes = some (mv, nc, bodyRest) → mv < dimacsBound →
      parseBodyPure mv nc poolInts [] bodyRest = some (clauses, poolRem') →
      parseDimacs cnfBytes =
        some (clauses.foldl (fun c lits => c.add (toClause lits)) CNF.empty) ∧
      clauses.length = nc ∧ (∀ cl ∈ clauses, ∀ x ∈ cl, IsValidLit mv x))
    (hrup_sound : RupSoundHyp) {cnfBytes prfBytes : List UInt8} {work_len : Nat}
    (hrun : runLratCheckBytes cnfBytes prfBytes work_len = true) :
    ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat := by
  unfold runLratCheckBytes at hrun; split at hrun; · cases hrun
  rcases hhdr : parseHeader cnfBytes with _ | ⟨mv, nc, bodyRest⟩; · rw [hhdr] at hrun; cases hrun
  rw [hhdr] at hrun; dsimp only at hrun; have hmv := (parseHeader_bounds hhdr).1
  by_cases hlt_f : work_len < 80 + (mv + 8) / 8 * 8 + (4 * (mv + 1) + 7) / 8 * 8 <;>
    simp only [hlt_f, ↓reduceIte] at hrun; · cases hrun
  by_cases hcap :
      ((if (work_len - (80 + (mv + 8) / 8 * 8 + (4 * (mv + 1) + 7) / 8 * 8)) / 16 <
            nc + prfBytes.length % 268435456 + 32 then
          (work_len - (80 + (mv + 8) / 8 * 8 + (4 * (mv + 1) + 7) / 8 * 8)) / 16
        else nc + prfBytes.length % 268435456 + 32) ≤ nc) <;>
    simp only [hcap, ↓reduceIte] at hrun; · cases hrun
  rcases hbody : parseBodyPure mv nc _ [] bodyRest with _ | ⟨clauses, pool_ints'⟩ <;>
    rw [hbody] at hrun; · cases hrun
  dsimp only at hrun
  obtain ⟨hdimacs, _, hcl_valid⟩ := hbody_sound hhdr hmv hbody
  exact ⟨_, hdimacs, checkPrfAux_sound_of hrup_sound hmv (CNF.entails_refl _)
    (initClauseTable_sound hcl_valid) hrun⟩

/-! ## 3. `WorkState` accessors and verification of `lbCheckPrf` -/

private theorem workState_collapse {B R : Mem 64 → Prop} {c : WorkCfg} {poolUsed poolRem : Nat}
    {cur : BitVec 64} {ptrs : List (BitVec 64)} {table : List (Option (List (BitVec 64)))}
    {PoolUsed : Mem 64 → Prop} {m : Mem 64}
    (hm : (B ⋆ WorkState c poolUsed poolRem cur ptrs table PoolUsed ⋆ R) m) :
    (B ⋆ region c.hdr c.activeBytes ⋆ R) m :=
  sep_mono2 (sep_mono2 (fun _ h => h) fun _ => WorkState.to_region) (fun _ h => h) m hm

private abbrev wsCbRest (c : WorkCfg) (poolUsed poolRem : Nat) (cur : BitVec 64)
    (PoolUsed B R : Mem 64 → Prop) : Mem 64 → Prop :=
  word8Array c.hdr (c.hdrWords (c.pbase + BitVec.ofNat 64 (4 * poolUsed)) cur) ⋆
  byte1Array c.vb (assignBytes c.mv Assignment.empty) ⋆
  region (c.vb + BitVec.ofNat 64 (c.mv + 1)) (c.vBytes - (c.mv + 1)) ⋆
  region c.tb c.tRaw ⋆ region c.tlim (c.tBytes - c.tRaw) ⋆
  PoolUsed ⋆ region (c.pbase + BitVec.ofNat 64 (4 * poolUsed)) (4 * poolRem) ⋆ B ⋆ R

private theorem workState_tableRel {B R : Mem 64 → Prop} {c : WorkCfg} {poolUsed poolRem : Nat}
    {cur : BitVec 64} {ptrs : List (BitVec 64)} {table : List (Option (List (BitVec 64)))}
    {PoolUsed : Mem 64 → Prop} {m : Mem 64}
    (hm : (B ⋆ WorkState c poolUsed poolRem cur ptrs table PoolUsed ⋆ R) m) :
    TableRel c.mv c.cap ptrs table PoolUsed :=
  (workState_sep.mp (sep_ac hm :
    (WorkState c poolUsed poolRem cur ptrs table PoolUsed ⋆ (B ⋆ R)) m)).2.1

private theorem workState_load_hdr {F : Mem 64 → Prop} {c : WorkCfg} {poolUsed poolRem : Nat}
    {cur : BitVec 64} {ptrs : List (BitVec 64)} {table : List (Option (List (BitVec 64)))}
    {PoolUsed : Mem 64 → Prop} {m : Mem 64} (i : Nat) (hi : i < 10)
    (hm : (WorkState c poolUsed poolRem cur ptrs table PoolUsed ⋆ F) m) :
    loadVal m i64 (c.hdr + BitVec.ofNat 64 (8 * i)) =
      some ((c.hdrWords (c.pbase + BitVec.ofNat 64 (4 * poolUsed)) cur)[i]'
        (by simpa [WorkCfg.hdrWords] using hi)) :=
  loadl_hdr i hi (by simpa only [sep_assoc] using (workState_sep.mp hm).2.2.2) rfl

@[local c0_load] private theorem c0_load_ws_8 {F c poolUsed poolRem cur ptrs table PoolUsed m}
    (hm : (WorkState c poolUsed poolRem cur ptrs table PoolUsed ⋆ F) m) :
    loadVal m i64 (c.hdr + 8) = some (BitVec.ofNat 64 c.nc) := workState_load_hdr 1 (by decide) hm
@[local c0_load] private theorem c0_load_ws_16 {F c poolUsed poolRem cur ptrs table PoolUsed m}
    (hm : (WorkState c poolUsed poolRem cur ptrs table PoolUsed ⋆ F) m) :
    loadVal m i64 (c.hdr + 16) = some (BitVec.ofNat 64 c.cap) := workState_load_hdr 2 (by decide) hm
@[local c0_load] private theorem c0_load_ws_48 {F c poolUsed poolRem cur ptrs table PoolUsed m}
    (hm : (WorkState c poolUsed poolRem cur ptrs table PoolUsed ⋆ F) m) :
    loadVal m i64 (c.hdr + 48) = some c.cb := workState_load_hdr 6 (by decide) hm
@[local c0_load] private theorem c0_load_ws_64 {F c poolUsed poolRem cur ptrs table PoolUsed m}
    (hm : (WorkState c poolUsed poolRem cur ptrs table PoolUsed ⋆ F) m) :
    loadVal m i64 (c.hdr + 64) = some (c.pbase + BitVec.ofNat 64 (4 * poolUsed)) :=
  workState_load_hdr 8 (by decide) hm
@[local c0_load] private theorem c0_load_ws_72 {F c poolUsed poolRem cur ptrs table PoolUsed m}
    (hm : (WorkState c poolUsed poolRem cur ptrs table PoolUsed ⋆ F) m) :
    loadVal m i64 (c.hdr + 72) = some cur := workState_load_hdr 9 (by decide) hm

@[local c0_store] private theorem c0_store_ws_72 {F c poolUsed poolRem cur cur' ptrs table
    PoolUsed m} (hm : (WorkState c poolUsed poolRem cur ptrs table PoolUsed ⋆ F) m) :
    storeOk m i64 (c.hdr + 72) ∧
      (WorkState c poolUsed poolRem cur' ptrs table PoolUsed ⋆ F)
        (storeMem m i64 (c.hdr + 72) cur') := by
  obtain ⟨hsum, htr, hpu, hwm⟩ := workState_sep.mp hm
  simp only [sep_assoc] at hwm
  rw [show c.hdr + (72 : BitVec 64) = c.hdr + BitVec.ofNat 64 (8 * 9) from rfl]
  obtain ⟨hok, hm1⟩ := store_word8Array (i := 9) cur' (by simp [WorkCfg.hdrWords]) hwm
  have hset : (c.hdrWords (c.pbase + BitVec.ofNat 64 (4 * poolUsed)) cur).set 9 cur' =
      c.hdrWords (c.pbase + BitVec.ofNat 64 (4 * poolUsed)) cur' := rfl
  rw [hset] at hm1
  exact ⟨hok, workState_sep.mpr ⟨hsum, htr, hpu, by simp only [sep_assoc]; exact hm1⟩⟩

private theorem ws_cb_lookup {B R : Mem 64 → Prop} {c : WorkCfg} {poolUsed poolRem : Nat}
    {cur : BitVec 64} {ptrs : List (BitVec 64)} {table : List (Option (List (BitVec 64)))}
    {PoolUsed : Mem 64 → Prop} {m : Mem 64} {i : Nat} (hi : i < c.cap)
    (hm : (B ⋆ WorkState c poolUsed poolRem cur ptrs table PoolUsed ⋆ R) m) :
    ∃ v, loadVal m i64 (c.cb + BitVec.ofNat 64 (8 * i)) = some v ∧
      ((v ≠ 0 → ∃ lits, table[i]? = some (some lits)) ∧ (v = 0 → table[i]? = some none)) := by
  obtain ⟨_, ⟨hplen, htlen, hrel⟩, _, hwm⟩ := workState_sep.mp
    (sep_ac hm : (WorkState c poolUsed poolRem cur ptrs table PoolUsed ⋆ (B ⋆ R)) m)
  refine ⟨_, load_word8Array (hplen ▸ hi)
    (show (word8Array c.cb ptrs ⋆ wsCbRest c poolUsed poolRem cur PoolUsed B R) m by
      dsimp only [wsCbRest]; exact sep_ac hwm), ?_⟩
  have hri := hrel i hi
  have hget : table[i]? = some (table[i]'(htlen ▸ hi)) := List.getElem?_eq_getElem _
  cases hti : table[i]'(htlen ▸ hi) <;> rw [hti] at hri hget
  · exact ⟨fun h => absurd hri h, fun _ => hget⟩
  · exact ⟨fun _ => ⟨_, hget⟩, fun h => absurd h hri.1⟩

private theorem workState_store_cb {B R : Mem 64 → Prop} {c : WorkCfg} {poolUsed poolRem : Nat}
    {cur v : BitVec 64} {ptrs : List (BitVec 64)} {table table' : List (Option (List (BitVec 64)))}
    {PoolUsed : Mem 64 → Prop} {m : Mem 64} {i : Nat} (hi : i < c.cap)
    (htr' : TableRel c.mv c.cap (ptrs.set i v) table' PoolUsed)
    (hm : (B ⋆ WorkState c poolUsed poolRem cur ptrs table PoolUsed ⋆ R) m) :
    storeOk m i64 (c.cb + BitVec.ofNat 64 (8 * i)) ∧
      (B ⋆ WorkState c poolUsed poolRem cur (ptrs.set i v) table' PoolUsed ⋆ R)
        (storeMem m i64 (c.cb + BitVec.ofNat 64 (8 * i)) v) := by
  obtain ⟨hsum, ⟨hplen, _, _⟩, hpu, hwm⟩ := workState_sep.mp
    (sep_ac hm : (WorkState c poolUsed poolRem cur ptrs table PoolUsed ⋆ (B ⋆ R)) m)
  obtain ⟨hok, hm1⟩ := store_word8Array v (hplen ▸ hi)
    (show (word8Array c.cb ptrs ⋆ wsCbRest c poolUsed poolRem cur PoolUsed B R) m by
      dsimp only [wsCbRest]; exact sep_ac hwm)
  dsimp only [wsCbRest] at hm1
  exact ⟨hok, sep_ac (workState_sep.mpr ⟨hsum, htr', hpu, sep_ac hm1⟩ :
    (WorkState c poolUsed poolRem cur (ptrs.set i v) table' PoolUsed ⋆ (B ⋆ R)) _)⟩

private theorem tableRel_set_none {mv cap : Nat} {ptrs : List (BitVec 64)}
    {table : List (Option (List (BitVec 64)))} {PoolUsed : Mem 64 → Prop} {did : Nat}
    (htr : TableRel mv cap ptrs table PoolUsed) :
    TableRel mv cap (ptrs.set did 0) (table.set did none) PoolUsed := by
  obtain ⟨hplen, htlen, hrel⟩ := htr
  refine ⟨by simp [hplen], by simp [htlen], fun i hi => ?_⟩; grind

private theorem tableRel_set_some {mv cap : Nat} {ptrs : List (BitVec 64)}
    {table : List (Option (List (BitVec 64)))} {PoolUsed : Mem 64 → Prop}
    {id : Nat} {c_ptr : BitVec 64} {clits : List (BitVec 64)}
    (hc_ptr : c_ptr ≠ 0) (hclits : ∀ x ∈ clits, IsValidLit mv x)
    (hpool : ∃ R_c, PoolUsed = (ZeroTermInts c_ptr clits ⋆ R_c))
    (htr : TableRel mv cap ptrs table PoolUsed) :
    TableRel mv cap (ptrs.set id c_ptr) (table.set id (some clits)) PoolUsed := by
  obtain ⟨hplen, htlen, hrel⟩ := htr
  refine ⟨by simp [hplen], by simp [htlen], fun i hi => ?_⟩; grind

private theorem apply_jfail {J : Cont []} {P : Mem 64 → Prop} {m : Mem 64}
    (hJ : ∀ m, P m → J () m) (hp : P m) : J () m := hJ m hp

private structure CheckRecSt where
  idx : Nat
  poolUsed : Nat
  poolRem : Nat
  ptrs : List (BitVec 64)
  table : List (Option (List (BitVec 64)))
  PoolUsed : Mem 64 → Prop

private structure DelLoopSt where
  didx : Nat
  dptrs : List (BitVec 64)
  dtable : List (Option (List (BitVec 64)))

local macro "fail_leaf" : tactic =>
  `(tactic| ((try refine ⟨fun h => absurd rfl h, fun _ => ?_⟩);
             apply apply_jfail ‹_›;
             refine ⟨by
               simp +zetaDelta [*, -List.getElem_cons_drop, -List.length_drop,
                 -bne_iff_ne, -getElem?_pos, checkPrfAux]
               try simp +zetaDelta [*, -List.getElem_cons_drop, -List.length_drop,
                 -bne_iff_ne, -getElem?_pos, delLoopAux],
              by first | assumption | exact workState_collapse ‹_›⟩))

/-- Verification of `lbCheckPrf` against `lbCheckPrfSpec`, parameterized by `Γ` providing
`lbReadAddLitsSpec` and `lbRupCheckSpec`. -/
theorem lbCheckPrf_correct_of (Γ : Env)
    (hReadAddLits : ∀ args m Q X,
      lbReadAddLitsSpec args m Q X → Γ "lb_read_add_lits" [i64, i64] [i64] args m Q X)
    (hRupCheck : ∀ args m Q X,
      lbRupCheckSpec args m Q X → Γ "lb_rup_check" [i64, i64, i64, i64] [i64] args m Q X) :
    ∀ args m Q X, lbCheckPrfSpec args m Q X → Func.spec Γ lbCheckPrf args m Q X := by
  rintro _ m0 Q X ⟨c, prf_ptr, prfBytes, poolUsed0, poolRem0, ptrs0, table0, PoolUsed0, R,
    rfl, hprf_fit, hm0, hQ⟩
  unfold lbCheckPrf Func.spec Func.wp
  have hcap_bound : c.cap < 2 ^ 64 := by have := c.hfit; omega
  have hnc_bound : c.nc < 2 ^ 64 := by have := c.hnc; c0_bv_omega
  c0_hsteps_nogrp
  refine wp_join0 (fun m' =>
    checkPrfPure c.mv c.nc poolRem0 table0 prfBytes = false ∧
    (Eq (prfBytes.At prf_ptr) ⋆ region c.hdr c.activeBytes ⋆ R) m')
    (fun _ m' ⟨hfalse, hm'⟩ => by c0_hstraight; exact hQ 0 m' (by simp [hfalse]) hm') ?_
  intro Jfail hJfail
  refine wp_while_state0 (fun st : CheckRecSt => prfBytes.length - st.idx)
    (fun st m => st.idx ≤ prfBytes.length ∧
      checkPrfPure c.mv c.nc poolRem0 table0 prfBytes =
        checkPrfAux ((prfBytes.drop st.idx).length + 1) c.mv c.nc st.poolRem st.table
          (prfBytes.drop st.idx) ∧
      (Eq (prfBytes.At prf_ptr) ⋆
        WorkState c st.poolUsed st.poolRem (prf_ptr + BitVec.ofNat 64 st.idx)
          st.ptrs st.table st.PoolUsed ⋆ R) m)
    (fun Jrec hJrec => by
      c0_hstraight
      exact hJrec ⟨0, poolUsed0, poolRem0, ptrs0, table0, PoolUsed0⟩ m0
        ⟨Nat.zero_le _, rfl, by simpa using hm0⟩)
    (fun Jrec ⟨idx, poolUsed, poolRem, ptrs, table, PoolUsed⟩ m hst ih => by
      obtain ⟨hidx, hpure, hm⟩ := hst; dsimp only at hidx hpure hm
      have hlen_cap : table.length = c.cap := (workState_tableRel hm).2.1
      c0_hstraight; c0_hsplit
      · have hidx_end : idx = prfBytes.length := by c0_bv_omega
        subst hidx_end; c0_hstraight
        exact hJfail m ⟨by rw [hpure, List.drop_length]; rfl, workState_collapse hm⟩
      · have hidx_lt : idx < prfBytes.length := by c0_bv_omega
        have hm_prf : (Eq (prfBytes.At prf_ptr) ⋆
            (WorkState c poolUsed poolRem (prf_ptr + BitVec.ofNat 64 idx) ptrs table PoolUsed ⋆
              R)) m := sep_cast hm (by ac_rfl)
        refine head_wp_load rfl (loadu8_At hidx_lt (by omega) hm_prf) ?_
        c0_hstraight; rw [setWidth64_ofNat8, ptr_step_1]
        let tag := prfBytes[idx]; let bs1 := prfBytes.drop (idx + 1)
        have hdrop_idx : prfBytes.drop idx = tag :: bs1 := List.drop_eq_getElem_cons hidx_lt
        c0_hsplit
        · have htag97 : (tag == 97) = true := beq_iff_eq.mpr (bv64_u8_eq.mp (by simpa using hc))
          clear hc; c0_hstraight
          refine readLeb128_spec hprf_fit (by omega) rfl rfl hm_prf
            (fun hleb_none => by c0_hstraight; fail_leaf)
            fun uid bs2 hleb_uid huid_lt _ hbs2_drop hidx2_gt => ?_
          rw [eq_comm] at hbs2_drop
          let idx2 := prfBytes.length - bs2.length
          have hidx2_le : idx2 ≤ prfBytes.length := Nat.sub_le _ _
          c0_guard_exit
          · have hodd : (uid % 2 != 0) = true := bne_iff_ne.mpr (by c0_bv_omega [*]); fail_leaf
          · have hid_le_nc : ¬ c.nc < uid / 2 := (by c0_bv_omega [*]); fail_leaf
          · have hid_ge_cap : ¬ uid / 2 < c.cap := (by c0_bv_omega [*]); fail_leaf
          · let id := uid / 2
            have heven' : (uid % 2 != 0) = false := by
              have : uid % 2 = 0 := (by c0_bv_omega [*]); simp [this]
            have hnc_lt_id : c.nc < id := by dsimp [id]; c0_bv_omega [*]
            have hid_lt_cap : id < c.cap := by dsimp [id]; c0_bv_omega [*]
            have hid_bv : (BitVec.ofNat 64 uid >>> 1) = BitVec.ofNat 64 id := by
              dsimp [id]; c0_bv_omega [*]
            rw [show ((BitVec.ofNat 64 uid >>> 1) <<< 3) = BitVec.ofNat 64 (8 * id) by
              dsimp [id]; c0_bv_omega [*]]
            obtain ⟨v_cb, hload_cb, hcb_nz, hcb_z⟩ := ws_cb_lookup hid_lt_cap hm
            refine head_wp_load rfl hload_cb ?_
            c0_hsplit
            · obtain ⟨_, _⟩ := hcb_nz (by simpa using hc); c0_hstraight; fail_leaf
            · have hti_none := hcb_z (by simpa using hc)
              c0_hstraight
              let c_ptr := c.pbase + BitVec.ofNat 64 (4 * poolUsed)
              refine wp_call_ret1 _ _ _
                (hReadAddLits _ _ _ _ ⟨c, prf_ptr, prfBytes, idx2, poolUsed, poolRem,
                  ptrs, table, PoolUsed, R, rfl, hprf_fit, hidx2_le, sep_ac hm,
                  fun r m1 hr => hr⟩) ?_
              rintro lstat m1 hread_res; c0_hstraight; rw [hbs2_drop] at hread_res
              cases hread_eq : readAddLitsPure c.mv poolRem bs2 with
              | none =>
                rw [hread_eq] at hread_res; obtain ⟨rfl, hm1_reg⟩ := hread_res
                c0_hstep; c0_hstraight; fail_leaf
              | some val3 =>
                rcases val3 with ⟨clits, poolRem', bs3⟩
                rw [hread_eq] at hread_res
                obtain ⟨hlstat, hbs3_drop, hidx3_le, _, hc_ptr_nz, hclits_v, hm1⟩ := hread_res
                rw [eq_comm] at hbs3_drop; let idx3 := prfBytes.length - bs3.length
                have hlstat_nz : lstat ≠ 0 := by rw [hlstat]; split <;> decide
                c0_guard_exit (exit := by exfalso; exact hlstat_nz (by simpa using hc))
                clear hc; let PoolUsed1 := PoolUsed ⋆ ZeroTermInts c_ptr clits
                rw [hid_bv]
                refine wp_call_ret1 _ _ _
                  (hRupCheck _ _ _ _ ⟨c, id, c_ptr, prf_ptr, prfBytes, idx3,
                    poolUsed + (clits.length + 1), poolRem', clits, ptrs, table, PoolUsed1, R,
                    rfl, hid_lt_cap, hprf_fit, hidx3_le, hclits_v,
                    ⟨PoolUsed, sep_comm PoolUsed (ZeroTermInts c_ptr clits)⟩, hm1,
                    fun r m2 hr => hr⟩) ?_
                rintro rok m2 hrup_res; c0_hstraight; rw [hbs3_drop] at hrup_res
                cases hrup_eq : rupCheckPure c.mv id clits table bs3 with
                | none =>
                  rw [hrup_eq] at hrup_res; obtain ⟨rfl, hm2_reg⟩ := hrup_res
                  c0_hstep; c0_hstraight; fail_leaf
                | some bs4 =>
                  rw [hrup_eq] at hrup_res
                  obtain ⟨rfl, hbs4_drop, hidx4_le, hm2⟩ := hrup_res
                  let idx4 := prfBytes.length - bs4.length
                  c0_hstep; c0_hstraight
                  have hlstat2_iff : (lstat = (2 : BitVec 64)) ↔ clits.isEmpty = true := by
                    rw [hlstat]; cases clits.isEmpty <;> decide
                  have hbnd : (!(c.nc < uid / 2) || !(uid / 2 < table.length)) = false := by
                    dsimp only [id] at hnc_lt_id hid_lt_cap
                    simp only [hnc_lt_id, hlen_cap ▸ hid_lt_cap, decide_true, Bool.not_true,
                      Bool.false_or]
                  c0_hsplit
                  · c0_hstraight
                    have hemp' : clits.isEmpty = true := hlstat2_iff.mp (by simpa using hc)
                    refine hQ 1 m2 ?_ (workState_collapse hm2)
                    have htrue : checkPrfPure c.mv c.nc poolRem0 table0 prfBytes = true := by
                      rw [hpure, hdrop_idx, checkPrfAux.eq_3]
                      dsimp only [tag, bs1] at htag97 ⊢; dsimp only [id] at hti_none hrup_eq
                      simp only [htag97, ↓reduceIte, hleb_uid, heven', Bool.false_eq_true, hbnd,
                        hti_none, hread_eq, hrup_eq, hemp']
                    simp [htrue]
                  · have hnemp' : clits.isEmpty = false := by
                      cases hb : clits.isEmpty
                      · rfl
                      · exact absurd (hlstat2_iff.mpr hb) (by simpa using hc)
                    have htr_new := tableRel_set_some (id := id) hc_ptr_nz hclits_v
                      ⟨PoolUsed, sep_comm PoolUsed (ZeroTermInts c_ptr clits)⟩
                      (workState_tableRel hm2)
                    obtain ⟨hok_cb, hm3⟩ := workState_store_cb hid_lt_cap htr_new hm2
                    refine ⟨hok_cb, ?_⟩; c0_hstraight
                    have hbs3_lt := readAddLitsPure_lt hread_eq
                    have hbs4_lt := rupCheckPure_lt hrup_eq
                    have hidx4_gt : idx < idx4 := by dsimp [idx4, idx2] at hidx2_gt ⊢; omega
                    refine ih ⟨idx4, poolUsed + (clits.length + 1), poolRem',
                      ptrs.set id c_ptr, table.set id (some clits), PoolUsed1⟩ _
                      (by dsimp; omega) ⟨hidx4_le, ?_, hm3⟩
                    rw [hpure, hdrop_idx, checkPrfAux.eq_3]
                    dsimp only [tag, bs1] at htag97 ⊢; dsimp only [id] at hti_none hrup_eq
                    simp only [htag97, ↓reduceIte, hleb_uid, heven', Bool.false_eq_true, hbnd,
                      hti_none, hread_eq, hrup_eq, hnemp']
                    rw [show prfBytes.drop idx4 = bs4 from hbs4_drop.symm]
                    refine checkPrfAux_fuel_irrel (by simp; omega) (by omega)
        · have htag_not97 : (tag == 97) = false :=
            beq_false_of_ne (fun h => hc (by simpa using bv64_u8_eq.mpr h))
          clear hc; c0_hstraight; c0_hsplit
          · have htag100 : (tag == 100) = true := beq_iff_eq.mpr (bv64_u8_eq.mp (by simpa using hc))
            clear hc; c0_hsteps_nogrp
            refine wp_while_state1 (fun st : DelLoopSt => prf_ptr + BitVec.ofNat 64 st.didx)
              (fun st : DelLoopSt => prfBytes.length - st.didx)
              (fun st dm => idx + 1 ≤ st.didx ∧ st.didx ≤ prfBytes.length ∧
                delLoopAux (bs1.length + 1) c.cap table bs1 =
                  delLoopAux ((prfBytes.drop st.didx).length + 1) c.cap st.dtable
                    (prfBytes.drop st.didx) ∧
                (Eq (prfBytes.At prf_ptr) ⋆
                  WorkState c poolUsed poolRem (prf_ptr + BitVec.ofNat 64 idx)
                    st.dptrs st.dtable PoolUsed ⋆ R) dm)
              (fun Jdel hJdel => by
                c0_hstraight
                exact hJdel ⟨idx + 1, ptrs, table⟩ m ⟨Nat.le_refl _, hidx_lt, rfl, hm⟩)
              (fun Jdel ⟨didx, dptrs, dtable⟩ dm ⟨hdidx_lo, hdidx_hi, hdel_eq, hdm⟩ ih_del => by
                dsimp only at hdidx_lo hdidx_hi hdel_eq hdm; c0_hstraight
                have hdm_prf : (Eq (prfBytes.At prf_ptr) ⋆
                    (WorkState c poolUsed poolRem (prf_ptr + BitVec.ofNat 64 idx)
                      dptrs dtable PoolUsed ⋆ R)) dm := sep_cast hdm (by ac_rfl)
                refine readLeb128_spec hprf_fit hdidx_hi rfl rfl hdm_prf
                  (fun hleb_none => by c0_hstraight; fail_leaf)
                  fun u bs_d hleb_u hu_lt _ hbsd_drop hdidx2_gt => ?_
                rw [eq_comm] at hbsd_drop
                let didx2 := prfBytes.length - bs_d.length
                have hdidx2_le : didx2 ≤ prfBytes.length := Nat.sub_le _ _
                c0_hsplit
                · have hu0 : u = 0 := by c0_bv_omega
                  subst hu0; c0_hstraight
                  have hdel_done :
                      delLoopAux (bs1.length + 1) c.cap table bs1 = some (dtable, bs_d) := by
                    rw [hdel_eq, delLoopAux.eq_2, hleb_u]; rfl
                  refine ih ⟨didx2, poolUsed, poolRem, dptrs, dtable, PoolUsed⟩ _
                    (by dsimp; omega) ⟨hdidx2_le, ?_, sep_ac ‹_›⟩
                  rw [hpure, hdrop_idx, checkPrfAux.eq_3]
                  dsimp only [tag] at htag_not97 htag100 ⊢
                  simp only [htag_not97, htag100, Bool.false_eq_true, ↓reduceIte,
                    hlen_cap, hdel_done]
                  rw [show prfBytes.drop didx2 = bs_d from hbsd_drop]
                  have hbs_d_len : bs_d.length = prfBytes.length - didx2 := by
                    rw [← hbsd_drop, List.length_drop]
                  have hbl : bs1.length = prfBytes.length - (idx + 1) := List.length_drop
                  have hlt_d : bs_d.length < (prfBytes.drop didx).length := ‹_›
                  rw [List.length_drop] at hlt_d
                  refine checkPrfAux_fuel_irrel
                    (by simp only [List.length_cons]; rw [hbl]; omega)
                    (by rw [← hbsd_drop, List.length_drop]; omega)
                · have hu_ne0 : u ≠ 0 := by c0_bv_omega
                  c0_guard_exit
                  · have ho : (u % 2 != 0) = true := bne_iff_ne.mpr (by c0_bv_omega [*]); fail_leaf
                  · have hdid0 : u / 2 = 0 := (by c0_bv_omega [*]); fail_leaf
                  · have hdid_ge_cap : ¬ u / 2 < c.cap := (by c0_bv_omega [*]); fail_leaf
                  · let did := u / 2
                    have hdeven' : (u % 2 != 0) = false := by
                      have : u % 2 = 0 := (by c0_bv_omega [*]); simp [this]
                    have hdid_nz' : did ≠ 0 := by dsimp [did]; c0_bv_omega [*]
                    have hdid_nz : (did == 0) = false := beq_false_of_ne hdid_nz'
                    have hdid_lt_cap : did < c.cap := by dsimp [did]; c0_bv_omega [*]
                    have hdid_bv : (BitVec.ofNat 64 u >>> 1) = BitVec.ofNat 64 did := by
                      dsimp [did]; c0_bv_omega [*]
                    rw [show ((BitVec.ofNat 64 u >>> 1) <<< 3) = BitVec.ofNat 64 (8 * did) by
                      dsimp [did]; c0_bv_omega [*]]
                    obtain ⟨v_cb, hload_cb, hcb_nz, hcb_z⟩ := ws_cb_lookup hdid_lt_cap hdm
                    refine head_wp_load rfl hload_cb ?_
                    c0_hsplit
                    · obtain ⟨dlits, hdget_eq⟩ := hcb_nz (by simpa using hc)
                      have hdtr_new := tableRel_set_none (did := did) (workState_tableRel hdm)
                      obtain ⟨hok_dcb, hdm2⟩ := workState_store_cb hdid_lt_cap hdtr_new hdm
                      refine ⟨hok_dcb, ?_⟩; c0_hstraight
                      have hdec : prfBytes.length - didx2 < prfBytes.length - didx := by
                        dsimp [didx2]; omega
                      refine ih_del ⟨didx2, dptrs.set did 0, dtable.set did none⟩ _
                        hdec ⟨by dsimp only [didx2]; omega, hdidx2_le, ?_, hdm2⟩
                      rcases u with _ | u1
                      · exact absurd rfl hu_ne0
                      · rw [hdel_eq, delLoopAux.eq_2, hleb_u]
                        dsimp only [did] at hdid_nz hdid_lt_cap hdget_eq ⊢
                        simp only [hdeven', hdid_nz, hdid_lt_cap, decide_true, Bool.false_or,
                          Bool.not_true, Bool.false_eq_true, ↓reduceIte, hdget_eq]
                        rw [show prfBytes.drop didx2 = bs_d from hbsd_drop]
                        exact delLoopAux_fuel_irrel (by assumption) (by omega)
                    · have _ := hcb_z (by simpa using hc); c0_hstraight; fail_leaf)
          · have htag_not100 : (tag == 100) = false :=
              beq_false_of_ne (fun h => hc (by simpa using bv64_u8_eq.mpr h))
            c0_hstraight; fail_leaf)

/-! ## 4. Verification of `lratCheckBytes` against `lratCheckBytesExactSpec` -/

private theorem replicate_zero_set {xs : List (BitVec 64)} {i : Nat} (hi : i < xs.length) :
    (List.replicate i 0 ++ xs.drop i).set i 0 =
      List.replicate (i + 1) 0 ++ xs.drop (i + 1) := by
  apply List.ext_getElem; · simp; omega
  · grind

private theorem tableRel_init (mv cap : Nat) :
    TableRel mv cap (List.replicate cap 0) (List.replicate cap none) emp :=
  ⟨by simp, by simp, fun _ _ => by simp⟩

private theorem split_workspace (c : WorkCfg) (work_len : Nat)
    (hlen : c.activeBytes ≤ work_len) (hwfit : c.hdr.toNat + work_len < 2 ^ 64)
    {R_rest : Mem 64 → Prop} {hdrInit : List (BitVec 64)} {m : Mem 64}
    (hm : (word8Array c.hdr hdrInit ⋆ region (c.hdr + 80) (work_len - 80) ⋆ R_rest) m) :
    ∃ (vs0 cs0 : List (BitVec 64)), vs0.length = c.mv + 1 ∧ cs0.length = c.cap ∧
      (byte1Array c.vb vs0 ⋆ word8Array c.cb cs0 ⋆ word8Array c.hdr hdrInit ⋆
        (region (c.vb + BitVec.ofNat 64 (c.mv + 1)) (c.vBytes - (c.mv + 1)) ⋆
          region c.tb c.tRaw ⋆ region c.tlim (c.tBytes - c.tRaw) ⋆
          region c.pbase (4 * c.poolInts)) ⋆
        region (c.hdr + BitVec.ofNat 64 c.activeBytes) (work_len - c.activeBytes) ⋆ R_rest) m := by
  have hfit := c.fit_active; have hmv := c.hmv; unfold dimacsBound at hmv
  unfold WorkCfg.activeBytes at hfit
  have hvb_le : c.mv + 1 ≤ c.vBytes := by unfold WorkCfg.vBytes; omega
  have htb_le : c.tRaw ≤ c.tBytes := by unfold WorkCfg.tBytes WorkCfg.tRaw; omega
  have hptr : c.vb + BitVec.ofNat 64 (c.activeBytes - 80) =
      c.hdr + BitVec.ofNat 64 c.activeBytes := by
    apply BitVec.eq_of_toNat_eq
    unfold WorkCfg.vb WorkCfg.activeBytes WorkCfg.vBytes WorkCfg.tBytes WorkCfg.tRaw at *
    simp [BitVec.toNat_add]; omega
  rw [show c.hdr + (80 : BitVec 64) = c.vb from rfl,
    ← region_merge_eq (a := c.vb) (n1 := c.activeBytes - 80) (n2 := work_len - c.activeBytes)
      (n := work_len - 80) (by unfold WorkCfg.activeBytes at hlen ⊢; omega) (by omega), hptr,
    ← region_merge_eq (a := c.vb) (n1 := c.vBytes) (n2 := c.tBytes + (8 * c.cap + 4 * c.poolInts))
      (n := c.activeBytes - 80) (by unfold WorkCfg.activeBytes; omega) (by omega),
    ← region_merge_eq (a := c.vb) (n1 := c.mv + 1) (n2 := c.vBytes - (c.mv + 1))
      (n := c.vBytes) (by omega) (by omega),
    show c.vb + BitVec.ofNat 64 c.vBytes = c.tb from rfl,
    ← region_merge_eq (a := c.tb) (n1 := c.tBytes) (n2 := 8 * c.cap + 4 * c.poolInts)
      (n := c.tBytes + (8 * c.cap + 4 * c.poolInts)) rfl (by omega),
    ← region_merge_eq (a := c.tb) (n1 := c.tRaw) (n2 := c.tBytes - c.tRaw)
      (n := c.tBytes) (by omega) (by omega),
    show c.tb + BitVec.ofNat 64 c.tRaw = c.tlim from rfl,
    show c.tb + BitVec.ofNat 64 c.tBytes = c.cb from rfl,
    ← region_merge_eq (a := c.cb) (n1 := 8 * c.cap) (n2 := 4 * c.poolInts)
      (n := 8 * c.cap + 4 * c.poolInts) rfl (by omega),
    show c.cb + BitVec.ofNat 64 (8 * c.cap) = c.pbase from rfl] at hm
  obtain ⟨f_vc, f_rem, hu1, hd1, ⟨f_v, f_c, hu2, hd2, hrv, hrc⟩, hrem⟩ :=
    (sep_ac hm : (region c.vb (c.mv + 1) ⋆ region c.cb (8 * c.cap) ⋆
      (word8Array c.hdr hdrInit ⋆
        (region (c.vb + BitVec.ofNat 64 (c.mv + 1)) (c.vBytes - (c.mv + 1)) ⋆
          region c.tb c.tRaw ⋆ region c.tlim (c.tBytes - c.tRaw) ⋆
          region c.pbase (4 * c.poolInts)) ⋆
        region (c.hdr + BitVec.ofNat 64 c.activeBytes) (work_len - c.activeBytes) ⋆ R_rest)) m)
  obtain ⟨vs0, hvs0, hbv⟩ := region_to_byte1Array (c.mv + 1) (by omega) hrv
  obtain ⟨cs0, hcs0, hbc⟩ := region_to_word8Array c.cap (by omega) hrc
  exact ⟨vs0, cs0, hvs0, hcs0, sep_ac (show (byte1Array c.vb vs0 ⋆ word8Array c.cb cs0 ⋆ _) m from
    ⟨f_vc, f_rem, hu1, hd1, ⟨f_v, f_c, hu2, hd2, hbv, hbc⟩, hrem⟩)⟩

private theorem merge_ws_tail (c : WorkCfg) (work_len : Nat)
    (hlen : c.activeBytes ≤ work_len) (hwfit : c.hdr.toNat + work_len < 2 ^ 64)
    {cnf_ptr prf_ptr : BitVec 64} {cnfBytes prfBytes : List UInt8}
    {R_mem : Mem 64 → Prop} {m : Mem 64}
    (hm : (Eq (cnfBytes.At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆
      (region c.hdr c.activeBytes ⋆
        region (c.hdr + BitVec.ofNat 64 c.activeBytes) (work_len - c.activeBytes)) ⋆
      R_mem) m) :
    ((Eq (cnfBytes.At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆ region c.hdr work_len) ⋆ R_mem) m := by
  rw [region_merge_eq (n1 := c.activeBytes) (n2 := work_len - c.activeBytes) (n := work_len)
    (by omega) (by omega)] at hm
  exact sep_cast hm (by ac_rfl)

private theorem region80_eq {p : BitVec 64} {n : Nat} (hn : 80 ≤ n) (hf : p.toNat + n < 2 ^ 64) :
    region p n = (region p 80 ⋆ region (p + 80) (n - 80)) := by
  conv => lhs; rw [show n = 80 + (n - 80) from by omega, region_split (by omega)]
  rfl

private theorem collapse_hdr80 {cnf_ptr prf_ptr work_ptr : BitVec 64}
    {cnfBytes prfBytes : List UInt8} {work_len : Nat} (hw : 80 ≤ work_len)
    (hwfit : work_ptr.toNat + work_len < 2 ^ 64) {R_mem : Mem 64 → Prop} {m : Mem 64}
    (hm : (region work_ptr 80 ⋆ Eq (cnfBytes.At cnf_ptr) ⋆
      region (work_ptr + 80) (work_len - 80) ⋆ Eq (prfBytes.At prf_ptr) ⋆ R_mem) m) :
    ((Eq (cnfBytes.At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆ region work_ptr work_len) ⋆
      R_mem) m := by
  have h1 : (Eq (cnfBytes.At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆
      (region work_ptr 80 ⋆ region (work_ptr + 80) (work_len - 80)) ⋆ R_mem) m := sep_ac hm
  rw [← region80_eq hw hwfit] at h1; exact sep_cast h1 (by ac_rfl)

private theorem runLratCheckBytes_of_header {cnfBytes prfBytes bodyRest : List UInt8}
    {work_len mv nc : Nat} (h128 : ¬ (work_len < 128))
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
  unfold runLratCheckBytes; simp only [h128, ↓reduceIte, hhdr]; rfl

/-- Verification of `lratCheckBytes` against `lratCheckBytesExactSpec`, parameterized by `Γ`
providing `lbParseDimacsHeaderSpec`, `lbParseDimacsBodySpec`, and `lbCheckPrfSpec`. -/
theorem lratCheckBytes_exact_of (Γ : Env)
    (hParseHeader : ∀ args m Q X,
      lbParseDimacsHeaderSpec args m Q X →
      Γ "lb_parse_dimacs_header" [i64, i64, i64] [i64] args m Q X)
    (hParseBody : ∀ args m Q X,
      lbParseDimacsBodySpec args m Q X →
      Γ "lb_parse_dimacs_body" [i64, i64] [i64] args m Q X)
    (hCheckPrf : ∀ args m Q X,
      lbCheckPrfSpec args m Q X →
      Γ "lb_check_prf" [i64, i64] [i64] args m Q X) :
    ∀ args m Q X, lratCheckBytesExactSpec args m Q X → Func.spec Γ lratCheckBytes args m Q X := by
  rintro _ m0 Q X ⟨cnf_ptr, prf_ptr, work_ptr, cnfBytes, prfBytes, work_len, R_mem,
    rfl, hcnf_fit, hprf_fit, hwork_fit, hm0, hQ⟩
  unfold lratCheckBytes Func.spec Func.wp
  c0_hstraight; c0_hsplit
  · have hlt128 : work_len < 128 := by c0_bv_omega
    c0_hstraight; exact hQ 0 m0 (by simp [runLratCheckBytes_lt128 hlt128]) hm0
  · have hnot_lt128 : ¬ work_len < 128 := by c0_bv_omega
    c0_hstraight
    let R80 := region (work_ptr + 80) (work_len - 80) ⋆ Eq (prfBytes.At prf_ptr) ⋆ R_mem
    have hm0_hdr : (Eq (cnfBytes.At cnf_ptr) ⋆ region work_ptr 80 ⋆ R80) m0 := by
      have hm_tmp := hm0; rw [region80_eq (by omega) hwork_fit] at hm_tmp
      exact sep_cast hm_tmp (by dsimp [R80]; ac_rfl)
    refine wp_call_ret1 _ _ _
      (hParseHeader _ _ _ _ ⟨cnf_ptr, work_ptr, cnfBytes, R80, rfl, hcnf_fit, by omega, hm0_hdr,
        fun r m1 hr => hr⟩) ?_
    rintro hok m1 hhdr_res; c0_hstraight
    cases hhdr_eq : parseHeader cnfBytes with
    | none =>
      rw [hhdr_eq] at hhdr_res; obtain ⟨rfl, hm1_reg⟩ := hhdr_res
      c0_hstep; c0_hstraight
      exact hQ 0 m1 (by simp [runLratCheckBytes_hdr_none hnot_lt128 hhdr_eq])
        (collapse_hdr80 (by omega) hwork_fit (by dsimp [R80] at hm1_reg; exact sep_ac hm1_reg))
    | some val_hdr =>
      rcases val_hdr with ⟨mv, nc, bodyRest⟩
      rw [hhdr_eq] at hhdr_res
      obtain ⟨rfl, hmv, hnc, hbody_drop, hbody_le, w2, w3, w4, w5, w6, w7, w8, hm1⟩ := hhdr_res
      c0_hstep
      let idx0 := cnfBytes.length - bodyRest.length
      let cur0 := cnf_ptr + BitVec.ofNat 64 idx0
      let hdrInit : List (BitVec 64) :=
        [BitVec.ofNat 64 mv, BitVec.ofNat 64 nc, w2, w3, w4, w5, w6, w7, w8, cur0]
      have hm1_focus : (word8Array work_ptr hdrInit ⋆ (Eq (cnfBytes.At cnf_ptr) ⋆ R80)) m1 :=
        sep_cast hm1 (by dsimp [hdrInit, cur0, idx0]; ac_rfl)
      have hm1_reg : (region work_ptr 80 ⋆ (Eq (cnfBytes.At cnf_ptr) ⋆ R80)) m1 :=
        sep_mono (fun f (hf : word8Array work_ptr hdrInit f) =>
          by simpa [hdrInit] using word8Array_to_region (by simp [hdrInit]) hf) hm1_focus
      have hcollapse_init : ((Eq (cnfBytes.At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆
          region work_ptr work_len) ⋆ R_mem) m1 := by
        dsimp only [R80] at hm1_reg; exact collapse_hdr80 (by omega) hwork_fit (sep_ac hm1_reg)
      dsimp only [hdrInit] at hm1_focus
      c0_hstraight
      simp only [List.getElem_cons_zero, List.getElem_cons_succ, BitVec.reduceToNat, Nat.reduceDiv]
      have hmv_lt : mv < 2 ^ 28 := hmv; have hnc_lt : nc < 2 ^ 28 := hnc
      let v_bytes := ((mv + 8) / 8) * 8; let t_raw := 4 * (mv + 1)
      let t_bytes := ((t_raw + 7) / 8) * 8; let fixed := 80 + v_bytes + t_bytes
      have hfix64 : fixed < 2 ^ 64 := by dsimp [fixed, v_bytes, t_bytes, t_raw]; omega
      rw [show (BitVec.ofNat 64 mv + 1) <<< (OfNat.ofNat 2 : Nat) = BitVec.ofNat 64 t_raw by
          c0_bv_omega,
        show (BitVec.ofNat 64 mv + (8 : BitVec 64) &&& (-8 : BitVec 64)) =
            BitVec.ofNat 64 v_bytes by
          rw [show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, bv_add_ofNat mv 8,
            show (-8#64 : BitVec 64) = -(BitVec.ofNat 64 (2 ^ 3)) from rfl,
            bv_align_pow2 (by decide) (by omega)],
        show (BitVec.ofNat 64 t_raw + (7 : BitVec 64) &&& (-8 : BitVec 64)) =
            BitVec.ofNat 64 t_bytes by
          rw [show (7 : BitVec 64) = BitVec.ofNat 64 7 from rfl, bv_add_ofNat t_raw 7,
            show (-8 : BitVec 64) = -(BitVec.ofNat 64 (2 ^ 3)) from rfl,
            bv_align_pow2 (by decide) (by dsimp [t_raw]; omega)],
        show (80 : BitVec 64) + (BitVec.ofNat 64 v_bytes + BitVec.ofNat 64 t_bytes) =
            BitVec.ofNat 64 fixed by
          rw [bv_add_ofNat v_bytes t_bytes,
            show (80 : BitVec 64) = BitVec.ofNat 64 80 from rfl, bv_add_ofNat]; congr 1; omega]
      c0_hsplit
      · have hlt_fixed : work_len < fixed := by
          rwa [Nat.mod_eq_of_lt (by omega : work_len < 2 ^ 64), Nat.mod_eq_of_lt hfix64] at hc
        c0_hstraight; refine hQ 0 m1 ?_ hcollapse_init
        rw [runLratCheckBytes_of_header hnot_lt128 hhdr_eq]; dsimp only
        dsimp only [fixed, v_bytes, t_bytes, t_raw] at hlt_fixed
        simp only [hlt_fixed, ↓reduceIte]; rfl
      · have hnot_lt_fixed : ¬ work_len < fixed := by
          rwa [Nat.mod_eq_of_lt (by omega : work_len < 2 ^ 64), Nat.mod_eq_of_lt hfix64] at hc
        c0_hstraight
        let rem := work_len - fixed; let c_half := rem / 16
        let p_cap := prfBytes.length % 268435456; let want := nc + p_cap + 32
        let cap := if c_half < want then c_half else want
        rw [bv_sub_ofNat (by omega) (by omega),
          show (BitVec.ofNat 64 prfBytes.length &&& (268435455 : BitVec 64)) =
              BitVec.ofNat 64 p_cap by
            rw [show (268435455 : BitVec 64) = BitVec.ofNat 64 (2 ^ 28 - 1) from rfl,
              bv_and_pow2_sub_one (k := 28) (by omega)],
          show (BitVec.ofNat 64 rem) >>> (4 : Nat) = BitVec.ofNat 64 c_half by
            rw [bv_shr_ofNat (by omega) (by decide), Nat.shiftRight_eq_div_pow],
          bv_add_ofNat nc p_cap,
          show BitVec.ofNat 64 (nc + p_cap) + (32 : BitVec 64) = BitVec.ofNat 64 want from
            bv_add_ofNat (nc + p_cap) 32]
        refine wp_join_group (fun (cap_v, ()) m' => cap_v = BitVec.ofNat 64 cap ∧ m' = m1) ?_ ?_
        · rintro _ ⟨cap_v, ⟨⟩⟩ m_cap ⟨rfl, hm_cap_eq⟩
          subst m_cap; c0_hstraight
          have hcap_le_chalf : cap ≤ c_half := by dsimp [cap]; split <;> omega
          have hcap_lt64 : cap < 2 ^ 64 := by dsimp [c_half, rem] at hcap_le_chalf; omega
          c0_hsplit
          · have hcap_le_nc : cap ≤ nc := by
              rwa [Nat.mod_eq_of_lt hcap_lt64, Nat.mod_eq_of_lt (by omega : nc < 2 ^ 64)] at hc
            c0_hstraight; refine hQ 0 m1 ?_ hcollapse_init
            rw [runLratCheckBytes_of_header hnot_lt128 hhdr_eq]; dsimp only
            dsimp only [cap, c_half, want, p_cap, rem, fixed, v_bytes, t_bytes,
              t_raw] at hnot_lt_fixed hcap_le_nc
            simp only [hnot_lt_fixed, hcap_le_nc, ↓reduceIte]; rfl
          · have hnot_cap_le_nc : ¬ cap ≤ nc := by
              rwa [Nat.mod_eq_of_lt hcap_lt64, Nat.mod_eq_of_lt (by omega : nc < 2 ^ 64)] at hc
            have hnc_cap : nc < cap := by omega
            c0_hstraight
            let cb_bytes := 8 * cap; let pool_rem := rem - cb_bytes; let pool_ints := pool_rem / 4
            have hcb_le_rem : cb_bytes ≤ rem := by dsimp [cb_bytes, c_half] at *; omega
            have hact_le : 80 + v_bytes + t_bytes + 8 * cap + 4 * pool_ints ≤ work_len := by
              dsimp [pool_ints, pool_rem, cb_bytes, rem]; omega
            let c : WorkCfg := {
              hdr := work_ptr, mv := mv, nc := nc, cap := cap, poolInts := pool_ints,
              hmv := hmv, hnc := hnc, hnc_cap := hnc_cap,
              hfit := by dsimp [v_bytes, t_bytes, t_raw] at hact_le; omega
            }
            have hc_act_le : c.activeBytes ≤ work_len := hact_le
            rw [show BitVec.ofNat 64 cap <<< 3 = BitVec.ofNat 64 cb_bytes by
                rw [bv_shl_ofNat (by omega) (by decide)]
                congr 1; dsimp [cb_bytes]; simp [Nat.shiftLeft_eq]; omega,
              show (BitVec.ofNat 64 rem - BitVec.ofNat 64 cb_bytes) &&& (-4 : BitVec 64) =
                  BitVec.ofNat 64 (4 * pool_ints) by
                rw [bv_sub_ofNat hcb_le_rem (by omega),
                  show (-4 : BitVec 64) = -(BitVec.ofNat 64 (2 ^ 2)) from rfl,
                  bv_align_pow2 (by decide) (by omega)]; congr 1; dsimp [pool_ints]; omega]
            clear hfix64 hcb_le_rem hcap_le_chalf hc hm0 hm0_hdr hm1_focus
              hcollapse_init hmv_lt hnc_lt
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
            refine wp_join0 (fun m_zv =>
              (word8Array c.cb cs0 ⋆ byte1Array c.vb (List.replicate (c.mv + 1) 0) ⋆
                word8Array c.hdr hdrInit ⋆ WMid ⋆ RTail ⋆ RRest) m_zv) ?_ ?_
            · intro _ m_zv hm_zv
              refine wp_join0 (fun m_zcb =>
                (word8Array c.hdr hdrInit ⋆ byte1Array c.vb (List.replicate (c.mv + 1) 0) ⋆
                  word8Array c.cb (List.replicate c.cap 0) ⋆ WMid ⋆ RTail ⋆ RRest) m_zcb) ?_ ?_
              · intro _ m_zcb hm_zcb
                let TailZ := byte1Array c.vb (List.replicate (c.mv + 1) 0) ⋆
                  word8Array c.cb (List.replicate c.cap 0) ⋆ WMid ⋆ RTail ⋆ RRest
                have hm_s0 : (word8Array work_ptr hdrInit ⋆ TailZ) m_zcb :=
                  sep_cast hm_zcb (by dsimp [TailZ, c]; ac_rfl)
                dsimp only [hdrInit] at hm_s0
                c0_hsteps_nogrp
                simp only [List.set_cons_zero, List.set_cons_succ, BitVec.reduceToNat,
                  Nat.reduceDiv] at hm
                let RBody := RTail ⋆ Eq (prfBytes.At prf_ptr) ⋆ R_mem
                have hm_ws0 : (Eq (cnfBytes.At cnf_ptr) ⋆
                    WorkState c 0 c.poolInts cur0
                      (List.replicate c.cap 0) (List.replicate c.cap none) emp ⋆
                    RBody) m := by
                  have hm_tmp : (word8Array c.hdr (c.hdrWords c.pbase cur0) ⋆ TailZ) m := hm
                  dsimp only [TailZ, WMid, RRest] at hm_tmp
                  rw [← assignBytes_empty c.mv, ← sep_emp (region c.pbase (4 * c.poolInts)),
                    show c.pbase = c.pbase + BitVec.ofNat 64 (4 * 0) from
                      (BitVec.add_zero c.pbase).symm] at hm_tmp
                  exact sep_cast (workState_sep.mpr ⟨Nat.zero_add _, tableRel_init c.mv c.cap,
                    fun f hf => by simpa [region_zero] using hf,
                    sep_cast hm_tmp (by dsimp [RBody]; ac_rfl)⟩ :
                    (WorkState c 0 c.poolInts cur0 (List.replicate c.cap 0)
                      (List.replicate c.cap none) emp ⋆ (Eq (cnfBytes.At cnf_ptr) ⋆ RBody)) m)
                    (by ac_rfl)
                refine wp_call_ret1 _ _ _ (hParseBody _ _ _ _ ⟨c, cnf_ptr, cnfBytes, idx0, RBody,
                    rfl, hcnf_fit, by dsimp [idx0]; omega, hm_ws0, fun r m_b hr => hr⟩) ?_
                rintro bok m_b hbody_res; c0_hstraight
                cases hbody_eq : parseBodyPure c.mv c.nc c.poolInts [] (cnfBytes.drop idx0) with
                | none =>
                  rw [hbody_eq] at hbody_res; obtain ⟨rfl, hm_b_reg⟩ := hbody_res
                  c0_hstep; c0_hstraight
                  have hbody_eq' : parseBodyPure mv nc pool_ints [] bodyRest = none := by
                    dsimp only [c, idx0] at hbody_eq; rwa [← hbody_drop] at hbody_eq
                  refine hQ 0 m_b ?_ (merge_ws_tail c work_len hc_act_le hwork_fit
                    (by dsimp only [RBody, RTail] at hm_b_reg; exact sep_ac hm_b_reg))
                  rw [runLratCheckBytes_of_header hnot_lt128 hhdr_eq]; dsimp only
                  dsimp only [pool_ints, pool_rem, cb_bytes, cap, c_half, want, p_cap, rem,
                    fixed, v_bytes, t_bytes, t_raw] at hnot_lt_fixed hnot_cap_le_nc hbody_eq'
                  simp only [hnot_lt_fixed, hnot_cap_le_nc, hbody_eq', ↓reduceIte]; rfl
                | some val_b =>
                  rcases val_b with ⟨clauses, poolRem'⟩
                  rw [hbody_eq] at hbody_res; obtain ⟨rfl, _, _, ptrs, PoolUsed, hm_b⟩ := hbody_res
                  c0_hstep; c0_hstraight
                  obtain ⟨hok72, hm_b2⟩ := c0_store_ws_72 (cur' := prf_ptr)
                    (sep_ac hm_b : (WorkState c (c.poolInts - poolRem') poolRem' _ ptrs
                      (initClauseTable c.cap clauses) PoolUsed ⋆
                      (Eq (cnfBytes.At cnf_ptr) ⋆ RBody)) m_b)
                  refine ⟨hok72, ?_⟩
                  let RPrf := RTail ⋆ Eq (cnfBytes.At cnf_ptr) ⋆ R_mem
                  have hm_prf_ws : (Eq (prfBytes.At prf_ptr) ⋆
                      WorkState c (c.poolInts - poolRem') poolRem' prf_ptr
                        ptrs (initClauseTable c.cap clauses) PoolUsed ⋆ RPrf)
                      (storeMem m_b i64 (c.hdr + 72) prf_ptr) :=
                    sep_cast hm_b2 (by dsimp [RBody, RPrf]; ac_rfl)
                  refine wp_call_ret1 _ _ (fun r m_fin =>
                      r = (if checkPrfPure c.mv c.nc poolRem'
                        (initClauseTable c.cap clauses) prfBytes = true then 1 else 0) ∧
                      (Eq (prfBytes.At prf_ptr) ⋆ region c.hdr c.activeBytes ⋆ RPrf) m_fin)
                    (hCheckPrf _ _ _ _ ⟨c, prf_ptr, prfBytes, c.poolInts - poolRem', poolRem',
                      ptrs, initClauseTable c.cap clauses, PoolUsed, RPrf, rfl, hprf_fit,
                      hm_prf_ws, fun r m_fin hr hm_fin => ⟨hr, hm_fin⟩⟩) ?_
                  rintro pok m_fin ⟨hpok, hm_fin⟩; c0_hstraight
                  have hbody_eq' : parseBodyPure mv nc pool_ints [] bodyRest =
                      some (clauses, poolRem') := by
                    dsimp only [c, idx0] at hbody_eq; rwa [← hbody_drop] at hbody_eq
                  refine hQ pok m_fin ?_ (merge_ws_tail c work_len hc_act_le hwork_fit
                    (by dsimp only [RPrf, RTail] at hm_fin; exact sep_ac hm_fin))
                  rw [hpok, runLratCheckBytes_of_header hnot_lt128 hhdr_eq]; dsimp only
                  dsimp only [c, pool_ints, pool_rem, cb_bytes, cap, c_half, want, p_cap, rem,
                    fixed, v_bytes, t_bytes, t_raw] at hnot_lt_fixed hnot_cap_le_nc hbody_eq' ⊢
                  simp only [hnot_lt_fixed, hnot_cap_le_nc, hbody_eq', ↓reduceIte]
              · intro Jzcb_done hJzcb_done
                let RestZcb := byte1Array c.vb (List.replicate (c.mv + 1) 0) ⋆
                  word8Array c.hdr hdrInit ⋆ WMid ⋆ RTail ⋆ RRest
                refine wp_while_state1 (fun j => BitVec.ofNat 64 j) (fun j => c.cap - j)
                  (fun j m => j ≤ c.cap ∧
                    (word8Array c.cb (List.replicate j 0 ++ cs0.drop j) ⋆ RestZcb) m)
                  (fun J hJ => by c0_hstraight; exact hJ 0 _ ⟨Nat.zero_le _,
                    sep_cast (by simpa using hm_zv) (by dsimp [RestZcb]; ac_rfl)⟩)
                  (fun J j m ⟨hj_le, hm_j⟩ ih_zcb => by
                    c0_hstraight
                    have hjl64 : j < 2 ^ 64 := by
                      have : c.cap = cap := rfl; rw [this] at hj_le; omega
                    c0_hsplit
                    · have hj_lt : j < c.cap := by
                        rwa [Nat.mod_eq_of_lt hjl64, Nat.mod_eq_of_lt (by exact hcap_lt64)] at hc
                      obtain ⟨hok_j, hm_j''⟩ := store_word8Array (i := j) 0
                        (by simp [hcs0]; omega) (hm_j : (word8Array c.cb _ ⋆ RestZcb) m)
                      rw [replicate_zero_set (hcs0 ▸ hj_lt)] at hm_j''; c0_hstep; c0_hstep
                      rw [show work_ptr + (80 : BitVec 64) + BitVec.ofNat 64 v_bytes +
                            BitVec.ofNat 64 t_bytes = c.cb from rfl,
                        show c.cb + BitVec.ofNat 64 j <<< (OfNat.ofNat 3 : Nat) =
                            c.cb + BitVec.ofNat 64 (8 * j) from by
                          congr 1; rw [bv_shl_ofNat hjl64 (by decide)]
                          congr 1; simp [Nat.shiftLeft_eq]; omega]
                      refine ⟨hok_j, ?_⟩; c0_hstraight; dsimp only
                      rw [show BitVec.ofNat 64 j + (1 : BitVec 64) = BitVec.ofNat 64 (j + 1) from
                        bv_add_ofNat j 1]
                      exact ih_zcb (j + 1) _ (by omega) ⟨by omega, hm_j''⟩
                    · have hj_eq : j = c.cap := by
                        rw [Nat.mod_eq_of_lt hjl64, Nat.mod_eq_of_lt (by exact hcap_lt64)] at hc
                        exact Nat.le_antisymm hj_le (Nat.not_lt.mp hc)
                      subst hj_eq; rw [List.drop_of_length_le (by omega), List.append_nil] at hm_j
                      c0_hstraight; exact hJzcb_done _ (sep_cast hm_j (by dsimp [RestZcb]; ac_rfl)))
            · intro Jzv_done hJzv_done
              let RestZv := word8Array c.cb cs0 ⋆ word8Array c.hdr hdrInit ⋆ WMid ⋆ RTail ⋆ RRest
              refine wp_while_state1 (fun i => BitVec.ofNat 64 i) (fun i => (c.mv + 1) - i)
                (fun i m => i ≤ c.mv + 1 ∧
                  (byte1Array c.vb (List.replicate i 0 ++ vs0.drop i) ⋆ RestZv) m)
                (fun J hJ => by
                  c0_hstraight; exact hJ 0 _ ⟨Nat.zero_le _, by
                    simpa [WMid, RTail, RRest] using
                      sep_cast hm1_split (by dsimp [RestZv, WMid, RTail, RRest]; ac_rfl)⟩)
                (fun J i m ⟨hi_le, hm_i⟩ ih_zv => by
                  c0_hstraight
                  have hil64 : i < 2 ^ 64 := by have : c.mv = mv := rfl; rw [this] at hi_le; omega
                  c0_hsplit
                  · have hi_le_mv : i ≤ c.mv := by c0_bv_omega [hil64, c.hmv]
                    obtain ⟨hok_i, hm_i'⟩ := store_byte1Array (i := i) 0#8
                      (by simp [hvs0]; omega) hm_i
                    rw [show (0#8).setWidth 64 = (0 : BitVec 64) from rfl,
                      replicate_zero_set (hvs0 ▸ (by omega : i < c.mv + 1))] at hm_i'
                    c0_hstep; rw [show work_ptr + (80 : BitVec 64) = c.vb from rfl]
                    refine ⟨hok_i, ?_⟩; c0_hstraight; dsimp only
                    rw [show BitVec.ofNat 64 i + (1 : BitVec 64) = BitVec.ofNat 64 (i + 1) from
                      bv_add_ofNat i 1]
                    exact ih_zv (i + 1) _ (by omega) ⟨by omega, hm_i'⟩
                  · have hi_eq : i = c.mv + 1 := by
                      dsimp only [c] at hi_le ⊢; c0_bv_omega [hi_le, hil64, hmv]
                    subst hi_eq; rw [List.drop_of_length_le (by omega), List.append_nil] at hm_i
                    c0_hstraight; exact hJzv_done _ (sep_cast hm_i (by dsimp [RestZv]; ac_rfl)))
        · intro Jgot_cap hJgot_cap; c0_hstraight; c0_hsplit
          · exact hJgot_cap _ _ ⟨by simp [cap, show c_half < want by
              rwa [Nat.mod_eq_of_lt (by dsimp [c_half, rem]; omega : c_half < 2 ^ 64),
                Nat.mod_eq_of_lt (by dsimp [want, p_cap]; omega : want < 2 ^ 64)] at hc], rfl⟩
          · exact hJgot_cap _ _ ⟨by simp [cap, show ¬ c_half < want by
              rwa [Nat.mod_eq_of_lt (by dsimp [c_half, rem]; omega : c_half < 2 ^ 64),
                Nat.mod_eq_of_lt (by dsimp [want, p_cap]; omega : want < 2 ^ 64)] at hc], rfl⟩

end LeanQbe.T.Examples.LratBytes
