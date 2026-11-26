module

public import Std.Sat.CNF
public import LeanQbe.T.Examples.Bitblast.Ref.Aig
public import LeanQbe.T.Examples.LratBytes
public import LeanQbe.T.Examples.LratBytesDimacsLemmas

/-!
# Pure Backward-Sweep COI, Per-Clause `tseitin_sound`, and DIMACS Bridge (`Bitblast.Ref.Tseitin`)

Defines:
- `coiMark`: single backward sweep `g.nodes.size - 1 .. 0` (no DFS, no stack)
- `litToDimacs`, `andClauses`, `iteClauses`, `tseitinClauses`, `tseitin`
- `tseitin_sound`: `(tseitin g marks root).Unsat -> ∀ ρ, g.evalLit ρ root = false`
- `tseitin_sound_of_clauses`: general per-clause soundness for any definitional clause list
- `validDimacs_tseitin` and `parseDimacs_encodeDimacs_tseitin` (`<= std3`, `0` axioms)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Bitblast.Ref.Tseitin

open Std.Sat
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Bitblast.Ref

/-! ## 1. DIMACS Literal & Clause Construction -/

/-- Convert an AIG literal `l = 2 * node + neg` to a 1-based DIMACS literal
`(node + 1, !neg)`. -/
@[expose] def litToDimacs (l : UInt32) : Literal Nat :=
  ((l >>> 1).toNat + 1, (l &&& 1) == 0)

/-- Three Tseitin definitional clauses for AND gate `outNode ↔ (lhs ∧ rhs)`. -/
@[expose] def andClauses (outNode : Nat) (lhs rhs : UInt32) : List (CNF.Clause Nat) :=
  let o := outNode + 1
  let l := litToDimacs lhs
  let r := litToDimacs rhs
  [ CNF.Clause.ofLiterals [(o, false), (l.1, l.2)],
    CNF.Clause.ofLiterals [(o, false), (r.1, r.2)],
    CNF.Clause.ofLiterals [(o, true), (l.1, !l.2), (r.1, !r.2)] ]

/-- Four Tseitin definitional clauses for ITE gate `outNode ↔ (cond ? ifT : ifF)`. -/
@[expose] def iteClauses (outNode : Nat) (cond ifT ifF : UInt32) : List (CNF.Clause Nat) :=
  let o := outNode + 1
  let c := litToDimacs cond
  let t := litToDimacs ifT
  let f := litToDimacs ifF
  [ CNF.Clause.ofLiterals [(c.1, !c.2), (t.1, !t.2), (o, true)],
    CNF.Clause.ofLiterals [(c.1, !c.2), (t.1, t.2), (o, false)],
    CNF.Clause.ofLiterals [(c.1, c.2), (f.1, !f.2), (o, true)],
    CNF.Clause.ofLiterals [(c.1, c.2), (f.1, f.2), (o, false)] ]

/-! ## 2. Backward-Sweep COI Marking and CNF Generation -/

/-- Backward-sweep cone-of-influence marking over AIG gates `k - 1 .. 0`. -/
@[expose] def coiMarkLoop (g : Aig) : Nat → Array Bool → Array Bool
  | 0, marks => marks
  | k + 1, marks =>
    let marks' :=
      if h : k < g.nodes.size then
        if marks.getD (g.A + 1 + k) false then
          let gate := g.nodes[k]
          let m1 := marks.setIfInBounds (gate.1 >>> 1).toNat true
          m1.setIfInBounds (gate.2 >>> 1).toNat true
        else
          marks
      else
        marks
    coiMarkLoop g k marks'

/-- Mark all AIG nodes reachable from `root` in a single linear backward sweep. -/
@[expose] def coiMark (g : Aig) (root : UInt32) : Array Bool :=
  let sz := g.A + 1 + g.nodes.size
  let marks0 := (Array.replicate sz false).setIfInBounds (root >>> 1).toNat true
  coiMarkLoop g g.nodes.size marks0

/-- Forward emission of Tseitin AND clauses for marked AIG gates `0 .. g.nodes.size - 1`. -/
@[expose] def tseitinClauses (g : Aig) (marks : Array Bool) : List (CNF.Clause Nat) :=
  (List.range g.nodes.size).flatMap fun i =>
    if h : i < g.nodes.size then
      if marks.getD (g.A + 1 + i) false then
        let gate := g.nodes[i]
        andClauses (g.A + 1 + i) gate.1 gate.2
      else []
    else []

/-- Complete Tseitin CNF for `(g, marks, root)`.
When `root = 0` (constant `false`), emits a single empty clause `[⊥]`. -/
@[expose] def tseitin (g : Aig) (marks : Array Bool) (root : UInt32) : CNF Nat :=
  if root == 0 then
    CNF.empty.add CNF.Clause.empty
  else
    ((tseitinClauses g marks).foldl CNF.add CNF.empty).add
      (CNF.Clause.ofLiterals [litToDimacs root])

/-! ## 3. Per-Clause Soundness (`tseitin_sound`) -/

/-- Canonical satisfying assignment of all definitional clauses induced by AIG evaluation
under atom assignment `ρ`: DIMACS variable `v ≥ 1` evaluates to `g.evalNode ρ (v - 1)`. -/
@[expose] def nodeEvalAssign (g : Aig) (ρ : Nat → Bool) : Nat → Bool :=
  fun v => g.evalNode ρ (v - 1)

private theorem litToDimacs_eval (g : Aig) (ρ : Nat → Bool) (l : UInt32) :
    (nodeEvalAssign g ρ (litToDimacs l).1 == (litToDimacs l).2) = g.evalLit ρ l := by
  simp only [nodeEvalAssign, litToDimacs, Nat.add_sub_cancel, Aig.evalLit]
  have hne : ((l &&& 1) != 0) = !((l &&& 1) == 0) := by rfl
  rw [hne]
  cases g.evalNode ρ (l >>> 1).toNat <;> cases ((l &&& 1) == 0) <;> rfl

private theorem litToDimacs_neg_eval (g : Aig) (ρ : Nat → Bool) (l : UInt32) :
    (nodeEvalAssign g ρ (litToDimacs l).1 == !(litToDimacs l).2) = !(g.evalLit ρ l) := by
  rw [← litToDimacs_eval g ρ l]
  cases nodeEvalAssign g ρ (litToDimacs l).1 <;> cases (litToDimacs l).2 <;> decide

private theorem clause_sat_of_mem_eval {α : Type} {a : α → Bool} {ls : List (Literal α)}
    (h : ls.any (fun p => a p.1 == p.2) = true) :
    CNF.Clause.Sat a (CNF.Clause.ofLiterals ls) := by
  obtain ⟨p, hp, heq⟩ := List.any_eq_true.mp h
  have hmem : p ∈ CNF.Clause.ofLiterals ls :=
    CNF.Clause.mem_literals_iff.mp (by rw [CNF.Clause.literals_ofLiterals]; exact hp)
  exact CNF.Clause.sat_of_mem_of_eq hmem (beq_iff_eq.mp heq)

theorem andClauses_sat {g : Aig} (hwf : g.Wf) (ρ : Nat → Bool) {i : Nat}
    (hi : i < g.nodes.size) :
    ∀ cl ∈ andClauses (g.A + 1 + i) g.nodes[i].1 g.nodes[i].2,
      CNF.Clause.Sat (nodeEvalAssign g ρ) cl := by
  intro cl hcl
  have hgate := Aig.evalNode_gate hwf ρ hi
  have ho : nodeEvalAssign g ρ (g.A + 1 + i + 1) =
      (g.evalLit ρ g.nodes[i].1 && g.evalLit ρ g.nodes[i].2) := by
    simp only [nodeEvalAssign, Nat.add_sub_cancel]; exact hgate
  have hl := litToDimacs_eval g ρ g.nodes[i].1
  have hr := litToDimacs_eval g ρ g.nodes[i].2
  have hln := litToDimacs_neg_eval g ρ g.nodes[i].1
  have hrn := litToDimacs_neg_eval g ρ g.nodes[i].2
  unfold andClauses at hcl
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hcl
  rcases hcl with rfl | rfl | rfl
  · refine clause_sat_of_mem_eval ?_
    simp only [List.any_cons, List.any_nil, Bool.or_false, ho, hl]
    cases g.evalLit ρ g.nodes[i].1 <;> cases g.evalLit ρ g.nodes[i].2 <;> decide
  · refine clause_sat_of_mem_eval ?_
    simp only [List.any_cons, List.any_nil, Bool.or_false, ho, hr]
    cases g.evalLit ρ g.nodes[i].1 <;> cases g.evalLit ρ g.nodes[i].2 <;> decide
  · refine clause_sat_of_mem_eval ?_
    simp only [List.any_cons, List.any_nil, Bool.or_false, ho, hln, hrn]
    cases g.evalLit ρ g.nodes[i].1 <;> cases g.evalLit ρ g.nodes[i].2 <;> decide

theorem iteClauses_sat (g : Aig) (ρ : Nat → Bool) (outNode : Nat) (cond ifT ifF : UInt32)
    (hdef : g.evalNode ρ outNode =
      bif g.evalLit ρ cond then g.evalLit ρ ifT else g.evalLit ρ ifF) :
    ∀ cl ∈ iteClauses outNode cond ifT ifF,
      CNF.Clause.Sat (nodeEvalAssign g ρ) cl := by
  intro cl hcl
  have ho : nodeEvalAssign g ρ (outNode + 1) =
      (bif g.evalLit ρ cond then g.evalLit ρ ifT else g.evalLit ρ ifF) := by
    simp only [nodeEvalAssign, Nat.add_sub_cancel]; exact hdef
  have hc := litToDimacs_eval g ρ cond
  have hcn := litToDimacs_neg_eval g ρ cond
  have ht := litToDimacs_eval g ρ ifT
  have htn := litToDimacs_neg_eval g ρ ifT
  have hf := litToDimacs_eval g ρ ifF
  have hfn := litToDimacs_neg_eval g ρ ifF
  unfold iteClauses at hcl
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hcl
  rcases hcl with rfl | rfl | rfl | rfl <;> refine clause_sat_of_mem_eval ?_ <;>
    simp only [List.any_cons, List.any_nil, Bool.or_false, ho, hc, hcn, ht, htn, hf, hfn] <;>
    cases g.evalLit ρ cond <;> cases g.evalLit ρ ifT <;> cases g.evalLit ρ ifF <;> decide

private theorem foldl_cnf_sat {α : Type} {a : α → Bool} {cls : List (CNF.Clause α)} {init : CNF α}
    (hinit : CNF.Sat a init) (hcls : ∀ cl ∈ cls, CNF.Clause.Sat a cl) :
    CNF.Sat a (cls.foldl CNF.add init) := by
  induction cls generalizing init with
  | nil => exact hinit
  | cons cl cls ih =>
    simp only [List.foldl_cons]
    exact ih (CNF.sat_add.mpr ⟨hcls cl (by simp), hinit⟩)
      (fun c hc => hcls c (by simp [hc]))

/-- General per-clause Tseitin soundness: if `nodeEvalAssign g ρ` satisfies every clause in
`clauses`, then unsatisfiability of `clauses + [root]` implies `g.evalLit ρ root = false`. -/
theorem tseitin_sound_of_clauses (g : Aig) (clauses : List (CNF.Clause Nat)) (root : UInt32)
    (hdef : ∀ ρ, ∀ cl ∈ clauses, CNF.Clause.Sat (nodeEvalAssign g ρ) cl)
    (hunsat : ((clauses.foldl CNF.add CNF.empty).add
      (CNF.Clause.ofLiterals [litToDimacs root])).Unsat) :
    ∀ ρ, g.evalLit ρ root = false := by
  intro ρ
  cases hroot : g.evalLit ρ root
  · rfl
  · exfalso
    have hunit :
        CNF.Clause.Sat (nodeEvalAssign g ρ) (CNF.Clause.ofLiterals [litToDimacs root]) := by
      refine clause_sat_of_mem_eval ?_
      simp [litToDimacs_eval, hroot]
    have hsat : CNF.Sat (nodeEvalAssign g ρ)
        ((clauses.foldl CNF.add CNF.empty).add (CNF.Clause.ofLiterals [litToDimacs root])) :=
      CNF.sat_add.mpr ⟨hunit, foldl_cnf_sat CNF.sat_empty (hdef ρ)⟩
    exact (CNF.unsat_iff_not_sat.mp hunsat (nodeEvalAssign g ρ)) hsat

/-- Main Tseitin soundness theorem:
`(tseitin g marks root).Unsat → ∀ ρ, g.evalLit ρ root = false`. -/
theorem tseitin_sound (g : Aig) (hwf : g.Wf) (marks : Array Bool) (root : UInt32)
    (hunsat : (tseitin g marks root).Unsat) :
    ∀ ρ, g.evalLit ρ root = false := by
  unfold tseitin at hunsat
  by_cases h0 : root == 0
  · have hr : root = 0 := beq_iff_eq.mp h0
    subst hr
    intro ρ
    exact Aig.evalLit_zero g ρ
  · simp only [h0, Bool.false_eq_true, ↓reduceIte] at hunsat
    refine tseitin_sound_of_clauses g (tseitinClauses g marks) root (fun ρ cl hcl => ?_) hunsat
    unfold tseitinClauses at hcl
    rw [List.mem_flatMap] at hcl
    rcases hcl with ⟨i, hi_mem, hcl_i⟩
    rw [List.mem_range] at hi_mem
    simp only [hi_mem, ↓reduceDIte] at hcl_i
    split at hcl_i
    · exact andClauses_sat hwf ρ hi_mem cl hcl_i
    · cases hcl_i

/-! ## 4. `ValidDimacsCnf` and `parseDimacs_encodeDimacs` Bridge -/

private theorem foldl_cnf_clauses_toList (cls : List (CNF.Clause Nat)) (init : CNF Nat) :
    (cls.foldl CNF.add init).clauses.toList = init.clauses.toList ++ cls := by
  induction cls generalizing init with
  | nil => simp
  | cons cl cls ih => simp [CNF.add, ih]

private theorem mem_foldl_lit_max_le {ls : List (Literal Nat)} {bound : Nat}
    (h : ∀ l ∈ ls, l.1 ≤ bound) (m0 : Nat) (hm0 : m0 ≤ bound) :
    ls.foldl (fun m' l => Nat.max m' l.1) m0 ≤ bound := by
  induction ls generalizing m0 with
  | nil => exact hm0
  | cons l ls ih =>
    simp only [List.foldl_cons]
    exact ih (fun x hx => h x (by simp [hx])) _ (Nat.max_le.mpr ⟨hm0, h l (by simp)⟩)

private theorem cnfMaxVar_le_of_all {cnf : CNF Nat} {bound : Nat}
    (h : ∀ cl ∈ cnf.clauses.toList, ∀ l ∈ cl.literals, l.1 ≤ bound) :
    cnfMaxVar cnf ≤ bound := by
  unfold cnfMaxVar
  rw [← Array.foldl_toList]
  suffices ∀ (cls : List (CNF.Clause Nat)) (m0 : Nat),
      m0 ≤ bound → (∀ cl ∈ cls, ∀ l ∈ cl.literals, l.1 ≤ bound) →
      cls.foldl (fun m cl => cl.literals.foldl (fun m' l => Nat.max m' l.1) m) m0 ≤ bound from
    this cnf.clauses.toList 0 (Nat.zero_le _) h
  intro cls
  induction cls with
  | nil => intro m0 hm0 _; exact hm0
  | cons cl cls ih =>
    intro m0 hm0 hcls
    simp only [List.foldl_cons]
    exact ih _ (mem_foldl_lit_max_le (hcls cl (by simp)) m0 hm0)
      (fun c hc => hcls c (by simp [hc]))

private theorem litToDimacs_bounds {l : UInt32} {N : Nat} (hl : (l >>> 1).toNat < N) :
    1 ≤ (litToDimacs l).1 ∧ (litToDimacs l).1 ≤ N := by
  simp only [litToDimacs]
  omega

private theorem tseitinClauses_length_le (g : Aig) (marks : Array Bool) :
    (tseitinClauses g marks).length ≤ 3 * g.nodes.size := by
  unfold tseitinClauses
  have hsub : ∀ i ∈ List.range g.nodes.size,
      (if h : i < g.nodes.size then
        if marks.getD (g.A + 1 + i) false then
          andClauses (g.A + 1 + i) g.nodes[i].1 g.nodes[i].2
        else []
      else []).length ≤ 3 := by
    intro i hi
    rw [List.mem_range] at hi
    simp only [hi, ↓reduceDIte]
    split <;> simp [andClauses]
  have hsum : ∀ (xs : List Nat) (f : Nat → List (CNF.Clause Nat)),
      (∀ x ∈ xs, (f x).length ≤ 3) → (xs.flatMap f).length ≤ 3 * xs.length := by
    intro xs f hf
    induction xs with
    | nil => simp
    | cons x xs ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      have hx := hf x (by simp)
      have hxs := ih (fun y hy => hf y (by simp [hy]))
      omega
  simpa [List.length_range] using hsum (List.range g.nodes.size) _ hsub

private theorem tseitinClauses_lit_bounds {g : Aig} (hwf : g.Wf) (marks : Array Bool) :
    ∀ cl ∈ tseitinClauses g marks, ∀ l ∈ cl.literals,
      1 ≤ l.1 ∧ l.1 ≤ g.A + 1 + g.nodes.size := by
  intro cl hcl l hl
  unfold tseitinClauses at hcl
  rw [List.mem_flatMap] at hcl
  rcases hcl with ⟨i, hi_mem, hcl_i⟩
  rw [List.mem_range] at hi_mem
  simp only [hi_mem, ↓reduceDIte] at hcl_i
  split at hcl_i
  · have h1 := (hwf i hi_mem).1
    have h2 := (hwf i hi_mem).2
    have hl1 := litToDimacs_bounds (N := g.A + 1 + g.nodes.size)
      (by omega : (g.nodes[i].1 >>> 1).toNat < _)
    have hl2 := litToDimacs_bounds (N := g.A + 1 + g.nodes.size)
      (by omega : (g.nodes[i].2 >>> 1).toNat < _)
    unfold andClauses at hcl_i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hcl_i
    rcases hcl_i with rfl | rfl | rfl <;> simp only [CNF.Clause.literals_ofLiterals] at hl <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl <;>
      rcases hl with rfl | rfl | rfl <;> omega
  · cases hcl_i

/-- `ValidDimacsCnf` holds for `tseitin g marks root` whenever the AIG and root fit below
`dimacsBound` (`2^28`). -/
theorem validDimacs_tseitin {g : Aig} (hwf : g.Wf) (marks : Array Bool) {root : UInt32}
    (hroot : (root >>> 1).toNat < g.A + 1 + g.nodes.size)
    (hvar : g.A + 1 + g.nodes.size < dimacsBound)
    (hcls : 3 * g.nodes.size + 1 < dimacsBound) :
    ValidDimacsCnf (tseitin g marks root) := by
  unfold tseitin
  by_cases h0 : root == 0
  · simp only [h0, ↓reduceIte]
    refine ⟨?_, ?_, ?_⟩
    · have hle : cnfMaxVar (CNF.empty.add CNF.Clause.empty) ≤ 0 := by
        apply cnfMaxVar_le_of_all
        intro cl hcl l hl
        simp only [CNF.add, CNF.empty, Array.toList_push, List.nil_append,
          List.mem_singleton] at hcl
        subst hcl
        simp at hl
      have : 0 < dimacsBound := by decide
      omega
    · simp [CNF.add, CNF.empty]; decide
    · intro cl hcl l hl
      simp only [CNF.add, CNF.empty, Array.toList_push, List.nil_append,
        List.mem_singleton] at hcl
      subst hcl
      simp at hl
  · simp only [h0, Bool.false_eq_true, ↓reduceIte]
    have hlist : (((tseitinClauses g marks).foldl CNF.add CNF.empty).add
        (CNF.Clause.ofLiterals [litToDimacs root])).clauses.toList =
        tseitinClauses g marks ++ [CNF.Clause.ofLiterals [litToDimacs root]] := by
      simp [CNF.add, CNF.empty, foldl_cnf_clauses_toList]
    have hlit_all : ∀ cl ∈ (((tseitinClauses g marks).foldl CNF.add CNF.empty).add
        (CNF.Clause.ofLiterals [litToDimacs root])).clauses.toList,
        ∀ l ∈ cl.literals, 1 ≤ l.1 ∧ l.1 ≤ g.A + 1 + g.nodes.size := by
      intro cl hcl l hl
      rw [hlist, List.mem_append] at hcl
      rcases hcl with hcl | hcl
      · exact tseitinClauses_lit_bounds hwf marks cl hcl l hl
      · rw [List.mem_singleton] at hcl
        subst hcl
        simp only [CNF.Clause.literals_ofLiterals, List.mem_singleton] at hl
        subst hl
        exact litToDimacs_bounds hroot
    refine ⟨?_, ?_, fun cl hcl l hl => (hlit_all cl hcl l hl).1⟩
    · have := cnfMaxVar_le_of_all (fun cl hcl l hl => (hlit_all cl hcl l hl).2)
      omega
    · have hsz : (((tseitinClauses g marks).foldl CNF.add CNF.empty).add
          (CNF.Clause.ofLiterals [litToDimacs root])).clauses.size =
          (tseitinClauses g marks).length + 1 := by
        rw [← Array.length_toList, hlist, List.length_append, List.length_singleton]
      have hlen := tseitinClauses_length_le g marks
      omega

/-- Exact DIMACS round-trip bridge into `LratBytes.parseDimacs_encodeDimacs`. -/
theorem parseDimacs_encodeDimacs_tseitin {g : Aig} (hwf : g.Wf) (marks : Array Bool)
    {root : UInt32} (hroot : (root >>> 1).toNat < g.A + 1 + g.nodes.size)
    (hvar : g.A + 1 + g.nodes.size < dimacsBound)
    (hcls : 3 * g.nodes.size + 1 < dimacsBound) :
    parseDimacs (encodeDimacs (tseitin g marks root)) = some (tseitin g marks root) :=
  parseDimacs_encodeDimacs (validDimacs_tseitin hwf marks hroot hvar hcls)

end LeanQbe.T.Examples.Bitblast.Ref.Tseitin
