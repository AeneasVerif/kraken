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
   `parseDimacs`), definitionally identical to `LeanQbe.T.Examples.LratBytes.parseDimacs`.
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


/-! ## 2. `shiftDownCnf`, semantic entailment bridges, and pigeonhole bounds -/

/-- Convert a 0-based Kissat internal literal (`2*(v-1)` / `2*(v-1)+1`) into the 1-based
`Std.Sat.Literal Nat` used by `parseDimacs`. -/
@[expose, inline] def kissatLitToDimacsLiteral (l : Nat) : Literal Nat :=
  (litVar l + 1, !(litSign l))

/-- Shift a 1-based DIMACS clause (`v ≥ 1`) down to 0-based Kissat variables (`v ↦ v - 1`). -/
@[expose] def shiftDownClause (cl : CNF.Clause Nat) : CNF.Clause Nat :=
  CNF.Clause.ofLiterals (cl.literals.map fun (v, p) => (v - 1, p))

/-- Shift a 1-based DIMACS `CNF Nat` down to 0-based Kissat variables. -/
@[expose] def shiftDownCnf (cnf : CNF Nat) : CNF Nat :=
  ⟨cnf.clauses.map shiftDownClause⟩

/-- Every variable occurring in `cnf` is positive (`1`-based DIMACS convention). -/
@[expose] def CnfVarsPos (cnf : CNF Nat) : Prop :=
  ∀ cl ∈ cnf, ∀ lit ∈ cl.literals, 1 ≤ lit.1

theorem cnfVarsPos_empty : CnfVarsPos (CNF.empty : CNF Nat) := by
  intro cl hcl
  simp [CNF.empty, CNF.Internal.mem_iff] at hcl

theorem cnfVarsPos_add {cnf : CNF Nat} {cl : CNF.Clause Nat}
    (h1 : CnfVarsPos cnf) (h2 : ∀ lit ∈ cl.literals, 1 ≤ lit.1) :
    CnfVarsPos (cnf.add cl) := by
  intro c hc
  rcases CNF.mem_add.mp hc with rfl | hc'
  · exact h2
  · exact h1 c hc'

theorem shiftDownClause_sat_of_sat {cl : CNF.Clause Nat} {α : Nat → Bool}
    (hpos : ∀ lit ∈ cl.literals, 1 ≤ lit.1) (hsat : cl.Sat α) :
    (shiftDownClause cl).Sat (fun v => α (v + 1)) := by
  rw [CNF.Clause.sat_iff_exists_mem_eq] at hsat ⊢
  obtain ⟨⟨v, p⟩, hmem, heq⟩ := hsat
  have hmem' : (v, p) ∈ cl.literals := CNF.Clause.mem_literals_iff.mpr hmem
  have hv1 : 1 ≤ v := hpos (v, p) hmem'
  refine ⟨(v - 1, p), ?_, ?_⟩
  · rw [← CNF.Clause.mem_literals_iff, shiftDownClause, CNF.Clause.literals_ofLiterals]
    exact List.mem_map.mpr ⟨(v, p), hmem', rfl⟩
  · simpa [Nat.sub_add_cancel hv1] using heq

theorem shiftDownCnf_unsat {cnf : CNF Nat} (hpos : CnfVarsPos cnf)
    (hu : (shiftDownCnf cnf).Unsat) : cnf.Unsat := by
  rw [CNF.unsat_iff_not_sat] at hu ⊢
  intro α hα
  apply hu (fun v => α (v + 1))
  rw [CNF.sat_iff_all_mem_sat] at hα ⊢
  intro cl' hcl'
  rw [CNF.Internal.mem_iff, shiftDownCnf, Array.mem_map] at hcl'
  obtain ⟨cl, hcl, rfl⟩ := hcl'
  have hmem : cl ∈ cnf := CNF.Internal.mem_iff.mpr hcl
  exact shiftDownClause_sat_of_sat (hpos cl hmem) (hα cl hmem)

theorem shiftDownCnf_add (cnf : CNF Nat) (cl : CNF.Clause Nat) :
    shiftDownCnf (cnf.add cl) = (shiftDownCnf cnf).add (shiftDownClause cl) := by
  simp [shiftDownCnf, CNF.add]

theorem shiftDownCnf_entails_add (cnf : CNF Nat) (cl : CNF.Clause Nat) :
    (shiftDownCnf (cnf.add cl)).Entails (shiftDownCnf cnf) := by
  rw [shiftDownCnf_add, CNF.entails_def]
  intro α hα
  exact (CNF.sat_add.mp hα).2

theorem shiftDownCnf_entails_added (cnf : CNF Nat) (cl : CNF.Clause Nat) :
    (shiftDownCnf (cnf.add cl)).EntailsClause (shiftDownClause cl) := by
  rw [shiftDownCnf_add, CNF.entails_clause_def]
  intro α hα
  exact (CNF.sat_add.mp hα).1

theorem shiftDownClause_kissatLits (lits : List Nat) :
    shiftDownClause (CNF.Clause.ofLiterals (lits.map kissatLitToDimacsLiteral)) =
      cnfClause lits := by
  apply CNF.Clause.ext
  simp [shiftDownClause, cnfClause, kissatLitToDimacsLiteral, litToLiteral, Function.comp_def]

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

theorem nodup_map_of_inj {α β : Type} {f : α → β} :
    ∀ {xs : List α}, xs.Nodup → (∀ a ∈ xs, ∀ b ∈ xs, f a = f b → a = b) → (xs.map f).Nodup
  | [], _, _ => by simp
  | x :: xs, hnd, hinj => by
    rw [List.nodup_cons] at hnd
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hmem => ?_, nodup_map_of_inj hnd.2 fun a ha b hb =>
      hinj a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb)⟩
    obtain ⟨y, hy, heq⟩ := List.mem_map.mp hmem
    have hxy := hinj y (List.mem_cons_of_mem _ hy) x List.mem_cons_self heq
    exact hnd.1 (hxy ▸ hy)

/-- Pigeonhole bound for `List.Nodup` elements in `0 ..< n`. -/
theorem nodup_length_le_of_lt :
    ∀ (n : Nat) (xs : List Nat), xs.Nodup → (∀ x ∈ xs, x < n) → xs.length ≤ n
  | 0, xs, _, hlt => by
    cases xs with
    | nil => simp
    | cons x _ => have := hlt x (by simp); omega
  | n + 1, xs, hnd, hlt => by
    have hnd' : (xs.erase n).Nodup := hnd.erase n
    have hlt' : ∀ y ∈ xs.erase n, y < n := by
      intro y hy
      have hne : y ≠ n := by
        intro heq; subst heq
        exact (List.Nodup.not_mem_erase hnd) hy
      have hyx : y ∈ xs := List.mem_of_mem_erase hy
      have := hlt y hyx; omega
    have hle := nodup_length_le_of_lt n (xs.erase n) hnd' hlt'
    have hlen : xs.length ≤ (xs.erase n).length + 1 := by
      by_cases hmem : n ∈ xs
      · rw [List.length_erase_of_mem hmem]; have := List.length_pos_of_mem hmem; omega
      · rw [List.erase_of_not_mem hmem]; omega
    omega

theorem nodup_lt_of_missing {n v : Nat} {xs : List Nat}
    (hnd : xs.Nodup) (hlt : ∀ x ∈ xs, x < n) (hv : v < n) (hnot : v ∉ xs) :
    xs.length < n := by
  have h := nodup_length_le_of_lt n (v :: xs) (List.nodup_cons.mpr ⟨hnot, hnd⟩)
    (fun x hx => (List.mem_cons.mp hx).elim (fun h => h ▸ hv) (hlt x))
  simp only [List.length_cons] at h
  omega

/-- Injection from `{0..k-1}` into `{0..n-1}` missing a point `v < n` forces `k < n`. -/
theorem inj_lt_of_missing {k n v : Nat} (f : Nat → Nat)
    (hinj : ∀ i j, i < k → j < k → f i = f j → i = j)
    (hlt : ∀ i < k, f i < n) (hv : v < n) (hmiss : ∀ i < k, f i ≠ v) : k < n := by
  let xs := (List.range k).map f
  have hlen : xs.length = k := by simp [xs]
  have hnd : xs.Nodup :=
    nodup_map_of_inj List.nodup_range fun i hi j hj heq =>
      hinj i j (List.mem_range.mp hi) (List.mem_range.mp hj) heq
  have hmem : ∀ x ∈ xs, x < n := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    exact hlt i (List.mem_range.mp hi)
  have hnot : v ∉ xs := by
    intro hx
    obtain ⟨i, hi, heq⟩ := List.mem_map.mp hx
    exact hmiss i (List.mem_range.mp hi) heq
  rw [← hlen]
  exact nodup_lt_of_missing hnd hmem hv hnot

/-- Surjection from `{0..k-1}` onto `{1..L}` implies `L ≤ k`. -/
theorem le_of_surj_range1 {L k : Nat} (g : Nat → Nat)
    (hsurj : ∀ x, 1 ≤ x → x ≤ L → ∃ i < k, g i = x) : L ≤ k := by
  let ys := (List.range L).map (fun x => x + 1)
  have hsub : ∀ y ∈ ys, ∃ i < k, g i = y := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    have hxlt := List.mem_range.mp hx
    exact hsurj (x + 1) (by omega) (by omega)
  have hnd : ys.Nodup := nodup_map_of_inj List.nodup_range fun a _ b _ h => by omega
  have hlen := nodup_length_le_of_lt k
    (ys.map fun y => (List.range k).findIdx (fun i => g i == y))
    (nodup_map_of_inj hnd fun a ha b hb heq => by
      obtain ⟨ia, hia, hga⟩ := hsub a ha
      obtain ⟨ib, hib, hgb⟩ := hsub b hb
      have hfa : (List.range k).findIdx (fun i => g i == a) < (List.range k).length :=
        List.findIdx_lt_length.mpr ⟨ia, List.mem_range.mpr hia, by simp [hga]⟩
      have hfb : (List.range k).findIdx (fun i => g i == b) < (List.range k).length :=
        List.findIdx_lt_length.mpr ⟨ib, List.mem_range.mpr hib, by simp [hgb]⟩
      have hpa := List.findIdx_getElem (xs := List.range k) (p := fun i => g i == a) (w := hfa)
      have hpb := List.findIdx_getElem (xs := List.range k) (p := fun i => g i == b) (w := hfb)
      simp only [List.getElem_range, beq_iff_eq] at hpa hpb
      rw [heq] at hpa
      exact hpa.symm.trans hpb)
    (by
      intro idx hidx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hidx
      obtain ⟨i, hi, hgi⟩ := hsub y hy
      have hlt : (List.range k).findIdx (fun j => g j == y) < (List.range k).length :=
        List.findIdx_lt_length.mpr ⟨i, List.mem_range.mpr hi, by simp [hgi]⟩
      rwa [List.length_range] at hlt)
  simpa [ys] using hlen


end LeanQbe.T.Examples.Kissat.Ref
