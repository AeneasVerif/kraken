/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Ref.Trail

/-!
# Pure Lean Layer-A Soundness Theory for Equivalence / SCC Literal Substitution

Pure Lean (`CNF Nat`, zero `Kraken.Mem` or C0 imports) soundness theory for Kissat's
`substitute.c` (binary implication graph SCC equivalence detection, representative literal
substitution, tautology elimination, and model reconstruction):

1. **Assignment evaluation & tautology helpers**: `evalLitVal`, `clauseEvalVal`, `cnfEvalVal`,
   `substUpdate`, `clauseIsTaut`, `VarFreshIn`, `VarFreshCnf`, and `CNF Nat ↔ List (List Nat)`
   round-trip lemmas.
2. **Single-step representative substitution (`EquivEntailed`, `substCnf`, `substExtend`)**:
   if `F ⊨ (v ↔ l)`, substituting `l` for positive `v` and `¬l` for negative `v` across `F`
   (dropping tautologies) preserves `Unsat` (`subst_unsat_sound`), reconstructs SAT models
   explicitly via `α[v ↦ α.eval l]` (`subst_sat_reconstruct`), preserves equisatisfiability
   (`subst_equisat`), and eliminates `v` when `litVar l ≠ v` (`subst_var_elim`).
3. **Multi-step substitution trace / witness stack (`SubstTrace`, `substTraceApply`,
   `substExtendTrace`)**: compositional UNSAT preservation (`substTrace_unsat`), explicit SAT
   model reconstruction (`substTrace_sat`), and equisatisfiability (`substTrace_equisat`).
4. **Binary implication graph & simultaneous SCC substitution (`BinReach`, `substMapCnf`,
   `substMapExtend`)**: SCC equivalence (`binReach_scc_equiv`), same-SCC contradiction
   (`binReach_contra_unsat`), failed-literal unit detection (`binReach_failed_unit`),
   simultaneous representative substitution (`substMap_unsat_sound`, `substMap_sat_recon`),
   and executable `Array Bool` model reconstruction bridges (`substTraceExtendArr_sound`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Ref

open Std.Sat

/-! ## 1. Single-step equivalence substitution and model reconstruction -/

/-- Formula `f` entails the literal equivalence `v ↔ l`, represented by the two binary
implication clauses `[¬v, l]` (`v → l`) and `[v, ¬l]` (`l → v`). -/
@[expose] def EquivEntailed (f : CNF Nat) (v l : Nat) : Prop :=
  f.EntailsClause (cnfClause [mkLit v false, l]) ∧
  f.EntailsClause (cnfClause [mkLit v true, litNeg l])

/-- Apply literal map `f` to clause `c`, deduplicating and dropping tautologies (`none`). -/
@[expose] def mapClauseTaut (f : Nat → Nat) (c : List Nat) : Option (List Nat) :=
  let c' := dedupLits (c.map f)
  if clauseIsTaut c' then none else some c'

/-- Substitute `l` for positive occurrences of `v` and `¬l` for negative occurrences of `v`. -/
@[expose, inline] def substLit (v l x : Nat) : Nat :=
  if litVar x == v then
    if litSign x then litNeg l else l
  else
    x

/-- Substitute `(v ↦ l)` into clause `c`, deduplicating and dropping tautologies (`none`). -/
abbrev substClause (v l : Nat) (c : List Nat) : Option (List Nat) :=
  mapClauseTaut (substLit v l) c

/-- Apply single-variable substitution `(v ↦ l)` across a list of clauses, dropping tautologies. -/
@[expose] def substClauses (v l : Nat) (cs : List (List Nat)) : List (List Nat) :=
  cs.filterMap (substClause v l)

/-- Apply single-variable substitution `(v ↦ l)` across a `CNF Nat`, dropping tautologies. -/
@[expose] def substCnf (v l : Nat) (f : CNF Nat) : CNF Nat :=
  cnfOfClauses (substClauses v l (clausesOfCnf f))

/-- Explicit SAT model reconstruction for substitution `(v ↦ l)`: `α' = α[v ↦ α.eval l]`. -/
@[expose, inline] def substExtend (v l : Nat) (α : Nat → Bool) : Nat → Bool :=
  substUpdate α v (evalLitVal α l)

/-! ## 2. Multi-step substitution trace and witness stack composition -/

/-- One recorded literal substitution `(var ↦ repr)` on the substitution witness stack. -/
structure SubstEntry where
  var : Nat
  repr : Nat
  deriving Repr, DecidableEq, Inhabited

/-- Ordered sequence of substitution steps `[e₁, e₂, ..., eₖ]` applied left-to-right. -/
abbrev SubstTrace := List SubstEntry

/-- Apply a substitution trace left-to-right to a clause list. -/
@[expose] def substTraceApplyClauses : SubstTrace → List (List Nat) → List (List Nat)
  | [], cs => cs
  | e :: rest, cs => substTraceApplyClauses rest (substClauses e.var e.repr cs)

/-- Apply a substitution trace left-to-right to a formula `f`. -/
@[expose] def substTraceApply : SubstTrace → CNF Nat → CNF Nat
  | [], f => f
  | e :: rest, f => substTraceApply rest (substCnf e.var e.repr f)

/-- Validity of a substitution trace against `f`: each step `(v ↦ l)` is entailed by the
current transformed formula (with `litVar l ≠ v`). -/
@[expose] def SubstTraceValid : CNF Nat → SubstTrace → Prop
  | _, [] => True
  | f, e :: rest =>
    litVar e.repr ≠ e.var ∧
    EquivEntailed f e.var e.repr ∧
    SubstTraceValid (substCnf e.var e.repr f) rest

/-- Reconstruct a model of `f` from a model `α` of `substTraceApply tr f` by unwinding the
substitution stack right-to-left (`foldr`). -/
@[expose] def substExtendTrace (tr : SubstTrace) (α : Nat → Bool) : Nat → Bool :=
  tr.foldr (fun e acc => substExtend e.var e.repr acc) α

/-! ## 4. Binary implication graph, SCC reachability, and simultaneous representative maps -/

/-- Binary implication edge `a → b` entailed by `f` (equivalently `f ⊨ [¬a, b]`). -/
@[expose] def BinEdge (f : CNF Nat) (a b : Nat) : Prop :=
  f.EntailsClause (cnfClause [litNeg a, b])

/-- Reflexive-transitive reachability `a →* b` in the binary implication graph of `f`. -/
inductive BinReach (f : CNF Nat) : Nat → Nat → Prop where
  | refl (a : Nat) : BinReach f a a
  | step {a b c : Nat} : BinEdge f a b → BinReach f b c → BinReach f a c

/-- Simultaneous polarity-respecting representative map lifted from variables (`Nat → Nat`)
to literals (`Nat → Nat`). -/
@[expose, inline] def substMapLit (m : Nat → Nat) (x : Nat) : Nat :=
  if litSign x then litNeg (m (litVar x)) else m (litVar x)

/-- Apply simultaneous representative map `m` to clause `c`, dropping tautologies. -/
abbrev substMapClause (m : Nat → Nat) (c : List Nat) : Option (List Nat) :=
  mapClauseTaut (substMapLit m) c

/-- Apply simultaneous representative map `m` across a clause list, dropping tautologies. -/
@[expose] def substMapClauses (m : Nat → Nat) (cs : List (List Nat)) : List (List Nat) :=
  cs.filterMap (substMapClause m)

/-- Apply simultaneous representative map `m` across a `CNF Nat`, dropping tautologies. -/
@[expose] def substMapCnf (m : Nat → Nat) (f : CNF Nat) : CNF Nat :=
  cnfOfClauses (substMapClauses m (clausesOfCnf f))

/-- Simultaneous SAT model reconstruction for a representative map `m`:
`α'(v) = α.eval (m v)`. -/
@[expose, inline] def substMapExtend (m : Nat → Nat) (α : Nat → Bool) : Nat → Bool :=
  fun v => evalLitVal α (m v)

/-! ## 5. Executable `Array Bool` model reconstruction bridge -/

/-- Executable single-step model update on `Array Bool` (`σ[v ↦ evalLit σ l]`). -/
@[expose] def substExtendArr (v l : Nat) (σ : Array Bool) : Array Bool :=
  arraySetPad σ v (evalLit σ l) false

/-- Executable trace model reconstruction on `Array Bool`. -/
@[expose] def substTraceExtendArr (tr : SubstTrace) (σ : Array Bool) : Array Bool :=
  tr.foldr (fun e acc => substExtendArr e.var e.repr acc) σ

/-- Executable representative table lookup (`tbl[v]?.getD (mkLit v true)`). -/
@[expose] def reprOfTable (tbl : Array Nat) (v : Nat) : Nat :=
  tbl[v]?.getD (mkLit v true)

/-- Executable simultaneous SCC model reconstruction on `Array Bool`. -/
@[expose] def substTableExtendArr (tbl : Array Nat) (σ : Array Bool) : Array Bool :=
  Array.ofFn (n := Nat.max σ.size tbl.size) fun i => evalLit σ (reprOfTable tbl i.val)

/-- Executable check that a binary implication edge `a → b` appears directly in `cs`. -/
@[expose] def hasBinEdge (cs : List (List Nat)) (a b : Nat) : Bool :=
  cs.contains [litNeg a, b] || cs.contains [b, litNeg a]

/-- Executable check that `a :: rest` is a valid binary implication chain ending at `b`. -/
@[expose] def checkBinPath (cs : List (List Nat)) : Nat → List Nat → Nat → Bool
  | a, [], b => a == b
  | a, next :: rest, b => hasBinEdge cs a next && checkBinPath cs next rest b

end LeanQbe.T.Examples.Kissat.Ref
