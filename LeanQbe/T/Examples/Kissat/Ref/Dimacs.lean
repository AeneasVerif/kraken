/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Ref.Trail

/-!
# Pure Lean ASCII DIMACS CNF Specification and Kissat 0-Based Shift Bridges

Pure Lean specification (`Std.Sat.CNF Nat`, zero `Kraken.Mem` or C0 imports):

1. Exact pure specification of standard ASCII DIMACS CNF (`parseHeader`, `parseClause`,
   `parseDimacs`), extensionally identical to `LeanQbe.T.Examples.LratBytes.parseDimacs` /
   `parseHeader` (zero `Kraken.*` imports; bridged via extensional equality or re-export).
2. 1-based to 0-based CNF shift (`shiftDownClause`, `shiftDownCnf`, `CnfVarsPos`,
   `shiftDownCnf_unsat`), propositional entailment/resolution bridges (`entails_of_mem_or_false`,
   `entails_resolve_to`), and `List.Nodup` pigeonhole bounds.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Ref

open Std.Sat

/-! ## 1. Pure specification of ASCII DIMACS CNF (`parseDimacs`) -/

/-- Standard ASCII whitespace (`' '`, `'\t'`, `'\n'`, `'\v'`, `'\f'`, `'\r'`). -/
@[expose] def isDimacsWs (b : UInt8) : Bool :=
  b == 32 || (9 ≤ b && b ≤ 13)

/-- ASCII decimal digit `'0'..'9'`. -/
@[expose] def isDimacsDigit (b : UInt8) : Bool :=
  48 ≤ b && b ≤ 57

/-- Upper bound (`2^28`) on DIMACS header counts and variable indices. -/
@[expose] def dimacsBound : Nat := 2 ^ 28

/-- Two-state structural scanner (`inComment = true` inside `'c' .. '\n'`) skipping ASCII
whitespace and `'c'` comment lines. -/
@[expose] def skipWsCommentsAux : Bool → List UInt8 → List UInt8
  | true, [] => []
  | true, 10 :: bs => skipWsCommentsAux false bs
  | true, _ :: bs => skipWsCommentsAux true bs
  | false, [] => []
  | false, b :: bs =>
    if isDimacsWs b then skipWsCommentsAux false bs
    else if b == 99 then skipWsCommentsAux true bs
    else b :: bs

/-- Skip ASCII whitespace and `'c'` (`99`) comment lines. -/
@[expose] def skipWsComments (bs : List UInt8) : List UInt8 :=
  skipWsCommentsAux false bs

/-- Skip zero or more whitespace bytes. -/
@[expose] def skipWs : List UInt8 → List UInt8
  | [] => []
  | b :: bs => if isDimacsWs b then skipWs bs else b :: bs

/-- Require at least one whitespace byte and skip any following whitespace. -/
@[expose] def skipWs1 : List UInt8 → Option (List UInt8)
  | [] => none
  | b :: bs => if isDimacsWs b then some (skipWs bs) else none

/-- Accumulate remaining digits of an unsigned decimal integer `< 2^28`, terminated by ws or EOF. -/
@[expose] def parseDigitsAux (acc : Nat) : List UInt8 → Option (Nat × List UInt8)
  | [] => some (acc, [])
  | b :: bs =>
    if isDimacsDigit b then
      let acc' := acc * 10 + (b.toNat - 48)
      if acc' < dimacsBound then parseDigitsAux acc' bs else none
    else if isDimacsWs b then
      some (acc, b :: bs)
    else
      none

/-- Parse a non-empty unsigned decimal integer `< 2^28`, terminated by whitespace or EOF. -/
@[expose] def parseNat : List UInt8 → Option (Nat × List UInt8)
  | [] => none
  | b :: bs =>
    if isDimacsDigit b then parseDigitsAux (b.toNat - 48) bs else none

/-- Parse leading comments/whitespace and the `p cnf <max_var> <num_clauses>` header. -/
@[expose] def parseHeader (bs : List UInt8) : Option (Nat × Nat × List UInt8) := do
  match skipWsComments bs with
  | 112 :: bs1 =>
    let bs2 ← skipWs1 bs1
    match bs2 with
    | 99 :: 110 :: 102 :: bs3 =>
      let bs4 ← skipWs1 bs3
      let (mv, bs5) ← parseNat bs4
      let bs6 ← skipWs1 bs5
      let (nc, bs7) ← parseNat bs6
      some (mv, nc, bs7)
    | _ => none
  | _ => none

/-- Structural helper for `parseClause`: each literal consumes ≥ 1 byte, so `bs.length + 1` steps
suffice for any input `bs` without truncation. -/
@[expose] def parseClauseAux : Nat → Nat → List (Literal Nat) → List UInt8 →
    Option (CNF.Clause Nat × List UInt8)
  | 0, _, _, _ => none
  | fuel + 1, mv, acc, bs =>
    match skipWsComments bs with
    | [] => none
    | 45 :: rest =>
      match parseNat rest with
      | some (v, rest') =>
        if 1 ≤ v && v ≤ mv then parseClauseAux fuel mv ((v, false) :: acc) rest' else none
      | none => none
    | b :: rest =>
      match parseNat (b :: rest) with
      | some (0, rest') => some (CNF.Clause.ofLiterals acc.reverse, rest')
      | some (v, rest') =>
        if 1 ≤ v && v ≤ mv then parseClauseAux fuel mv ((v, true) :: acc) rest' else none
      | none => none

/-- Parse one `0`-terminated clause of signed decimal literals with variables in `1..mv`. -/
@[expose] def parseClause (mv : Nat) (bs : List UInt8) : Option (CNF.Clause Nat × List UInt8) :=
  parseClauseAux (bs.length + 1) mv [] bs

/-- Parse `k` `0`-terminated clauses and require only whitespace/comments until EOF. -/
@[expose] def parseClauses (mv : Nat) : Nat → CNF Nat → List UInt8 → Option (CNF Nat)
  | 0, cnf, bs => if (skipWsComments bs).isEmpty then some cnf else none
  | k + 1, cnf, bs => do
    let (cl, bs') ← parseClause mv bs
    parseClauses mv k (cnf.add cl) bs'

/-- Total pure specification of standard ASCII DIMACS CNF. -/
@[expose] def parseDimacs (bs : List UInt8) : Option (CNF Nat) := do
  let (mv, nc, rest) ← parseHeader bs
  parseClauses mv nc CNF.empty rest


/-! ## 2. Semantic entailment bridges on top of `Ref.Base` -/

theorem entails_of_mem_or_false {F0 : CNF Nat} {c1 c2 : List Nat}
    (h1 : F0.EntailsClause (cnfClause c1))
    (hsub : ∀ l ∈ c1, l ∈ c2 ∨ F0.EntailsClause (cnfClause [litNeg l])) :
    F0.EntailsClause (cnfClause c2) := by
  rw [CNF.entails_clause_def] at h1 ⊢
  intro α hα
  obtain ⟨l, hl, hsat⟩ := (clause_sat_cnfClause_iff α c1).mp (h1 α hα)
  rcases hsub l hl with hin | hfalse
  · exact (clause_sat_cnfClause_iff α c2).mpr ⟨l, hin, hsat⟩
  · have hneg := CNF.entails_clause_def.mp hfalse α hα
    exact absurd ((sat_cnfClause_singleton α l).mpr hsat) ((sat_cnfClause_litNeg_iff α l).mp hneg)

theorem entails_resolve_to {F0 : CNF Nat} {p : Nat} {c1 c2 c3 : List Nat}
    (h1 : F0.EntailsClause (cnfClause c1))
    (h2 : F0.EntailsClause (cnfClause c2))
    (hs1 : ∀ l ∈ c1, l = p ∨ l ∈ c3 ∨ F0.EntailsClause (cnfClause [litNeg l]))
    (hs2 : ∀ l ∈ c2, l = litNeg p ∨ l ∈ c3 ∨ F0.EntailsClause (cnfClause [litNeg l])) :
    F0.EntailsClause (cnfClause c3) := by
  refine entails_of_mem_or_false (entails_resolve (p := p) h1 h2) fun l hl => ?_
  unfold resolveOn at hl
  rcases List.mem_append.mp hl with hl1 | hl2
  · rw [List.mem_filter, bne_iff_ne] at hl1
    rcases hs1 l hl1.1 with rfl | hin | hf
    · exact absurd rfl hl1.2
    · exact Or.inl hin
    · exact Or.inr hf
  · rw [List.mem_filter, bne_iff_ne] at hl2
    rcases hs2 l hl2.1 with rfl | hin | hf
    · exact absurd rfl hl2.2
    · exact Or.inl hin
    · exact Or.inr hf

end LeanQbe.T.Examples.Kissat.Ref
