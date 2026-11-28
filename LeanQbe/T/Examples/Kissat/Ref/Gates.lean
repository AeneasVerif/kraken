/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Ref.Substitute

/-!
# Pure Lean Layer-A Soundness Theory for BCE and Gate-Restricted BVE

Pure Lean (`CNF Nat`, zero `Kraken.Mem` or C0 imports) soundness theory for Kissat's
`gates.c`, `definition.c`, `eliminate.c`, and BCE passes:

1. **Blocked Clause Elimination (`BCE`) & `BceReconStack`**:
   if `l ∈ C` and every clause `D ∈ F` containing `¬l` has tautological resolvent
   `(C \ {l}) ∪ (D \ {¬l})`, removing `C` preserves equisatisfiability with explicit
   flip-if-falsified witness reconstruction (`extendBce`), composing over `BceReconStack`
   (`bceStack_unsat_sound`, `bceStack_sat_recon`, `bceStack_equisat`).
2. **Gate-Restricted BVE (`gates.c`, `eliminate.c`, `definition.c`)**:
   partitioning `P` / `N` around pivot `v` into gate clauses (`P_g`, `N_g`) and non-gate clauses
   (`P_ng`, `N_ng`), skipping `P_ng × N_ng` and resolving only `P_g × N` and `P × N_g` preserves
   `Unsat` (`gateBve_unsat_sound`) unconditionally and reconstructs SAT models (`extendGateBve`)
   under non-gate resolvent entailment (`gateBve_sat_recon`), semantic/functional gates
   (`gateFunc_bve_sat`, `gateFunc_bve_equisat`), or blocked non-gate resolvents
   (`gateBlocked_bve_sat`). Includes `GateFunctional` proofs for Kissat's `Equiv`, `AND`, `ITE`,
   `XOR`, and core-UNSAT `definition.c` gates.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Ref

open Std.Sat

/-! ## 1. Blocked Clause Elimination (`BCE`) and `BceReconStack` -/

/-- Set literal `l` to `true` in assignment `α` by updating `litVar l ↦ !(litSign l)`. -/
@[expose, inline] def setLitTrue (l : Nat) (α : Nat → Bool) : Nat → Bool :=
  substUpdate α (litVar l) (!(litSign l))

/-- Explicit flip-if-falsified BCE witness reconstruction: if `α` already satisfies `c`, return
`α` unchanged; otherwise flip `litVar l` so that `l` becomes `true`. -/
@[expose] def extendBce (l : Nat) (c : List Nat) (α : Nat → Bool) : Nat → Bool :=
  if clauseEvalVal α c then α else setLitTrue l α

/-- Clause `c` is blocked on literal `l` with respect to clause set `cs`: `l ∈ c`, and every
clause `d ∈ cs` containing `¬l` produces a tautological resolvent `resolveOn l c d`. -/
@[expose] def IsBlockedOn (cs : List (List Nat)) (c : List Nat) (l : Nat) : Prop :=
  l ∈ c ∧ ∀ d ∈ cs, litNeg l ∈ d → clauseIsTaut (resolveOn l c d) = true

/-- Executable Boolean checker for `IsBlockedOn`. -/
@[expose] def isBlockedOnBool (cs : List (List Nat)) (c : List Nat) (l : Nat) : Bool :=
  c.contains l && cs.all (fun d => !d.contains (litNeg l) || clauseIsTaut (resolveOn l c d))

/-- Witness entry for one eliminated blocked clause on the reconstruction stack. -/
structure BceReconEntry where
  lit : Nat
  clause : List Nat
  deriving Repr, DecidableEq, Inhabited

/-- Composable reconstruction stack for iterated Blocked Clause Elimination. -/
abbrev BceReconStack := List BceReconEntry

/-- Apply a BCE elimination stack left-to-right to a clause list. -/
@[expose] def bceApplyStack : BceReconStack → List (List Nat) → List (List Nat)
  | [], cs => cs
  | e :: rest, cs => bceApplyStack rest (cs.erase e.clause)

/-- Validity of a BCE elimination stack: every popped clause is blocked on its witness literal
with respect to the remaining clauses. -/
@[expose] def BceStackValid : List (List Nat) → BceReconStack → Prop
  | _, [] => True
  | cs, e :: rest =>
    e.clause ∈ cs ∧
    IsBlockedOn (cs.erase e.clause) e.clause e.lit ∧
    BceStackValid (cs.erase e.clause) rest

/-- Unwind a `BceReconStack` right-to-left (`foldr`) to reconstruct a model of the original CNF. -/
@[expose] def extendBceStack (st : BceReconStack) (α : Nat → Bool) : Nat → Bool :=
  st.foldr (fun e acc => extendBce e.lit e.clause acc) α

/-! ## 2. Gate-Restricted BVE (`gates.c`, `eliminate.c`, `definition.c`) -/

/-- Partition of a clause database around pivot variable `v` into positive/negative gate clauses
(`posGate`, `negGate`), positive/negative non-gate clauses (`posNonGate`, `negNonGate`), and
pivot-free remainder clauses (`rest`). -/
structure GatePartition where
  posGate : List (List Nat)
  posNonGate : List (List Nat)
  negGate : List (List Nat)
  negNonGate : List (List Nat)
  rest : List (List Nat)
  deriving Repr, DecidableEq, Inhabited

@[expose] def GatePartition.posClauses (gp : GatePartition) : List (List Nat) :=
  gp.posGate ++ gp.posNonGate

@[expose] def GatePartition.negClauses (gp : GatePartition) : List (List Nat) :=
  gp.negGate ++ gp.negNonGate

@[expose] def GatePartition.gateClauses (gp : GatePartition) : List (List Nat) :=
  gp.posGate ++ gp.negGate

@[expose] def GatePartition.allClauses (gp : GatePartition) : List (List Nat) :=
  gp.posGate ++ gp.posNonGate ++ gp.negGate ++ gp.negNonGate ++ gp.rest

/-- Partition validity around pivot variable `v`. -/
@[expose] def GatePartValid (v : Nat) (gp : GatePartition) : Prop :=
  (∀ c ∈ gp.posClauses, mkLit v true ∈ c) ∧
  (∀ d ∈ gp.negClauses, mkLit v false ∈ d) ∧
  (∀ r ∈ gp.rest, ∀ x ∈ r, litVar x ≠ v)

/-- Executable partitioning of `cs` around variable `v` using gate classifier `isGate`. -/
@[expose]
def partitionOnVar (v : Nat) (isGate : List Nat → Bool) (cs : List (List Nat)) : GatePartition :=
  let p := mkLit v true
  let np := mkLit v false
  let pos := cs.filter (fun c => c.contains p)
  let neg := cs.filter (fun c => !c.contains p && c.contains np)
  let rest := cs.filter (fun c => !c.contains p && !c.contains np)
  { posGate := pos.filter isGate
    posNonGate := pos.filter (fun c => !isGate c)
    negGate := neg.filter isGate
    negNonGate := neg.filter (fun c => !isGate c)
    rest := rest }

/-- All non-tautological deduplicated resolvents on pivot literal `p` across `as × bs`. -/
@[expose] def nonTautResolvents (p : Nat) (as bs : List (List Nat)) : List (List Nat) :=
  as.flatMap fun c => bs.filterMap fun d =>
    let r := dedupLits (resolveOn p c d)
    if clauseIsTaut r then none else some r

/-- Gate-restricted BVE output clauses: retains `rest` and resolves ONLY `posGate × negClauses`
and `posNonGate × negGate` (skipping `posNonGate × negNonGate`). -/
@[expose] def gateBveClauses (v : Nat) (gp : GatePartition) : List (List Nat) :=
  let p := mkLit v true
  gp.rest ++
    nonTautResolvents p gp.posGate gp.negClauses ++
    nonTautResolvents p gp.posNonGate gp.negGate

/-- Full BVE output clauses (for comparison and blocked-resolvent composition). -/
@[expose] def fullBveClauses (v : Nat) (gp : GatePartition) : List (List Nat) :=
  gateBveClauses v gp ++ nonTautResolvents (mkLit v true) gp.posNonGate gp.negNonGate

/-- Explicit SAT model reconstruction for gate-restricted (and full) BVE: assign `v := false`
if `α[v ↦ false]` satisfies all positive clauses `posClauses`, otherwise assign `v := true`. -/
@[expose]
def extendGateBve (v : Nat) (posClauses : List (List Nat)) (α : Nat → Bool) : Nat → Bool :=
  if posClauses.all (clauseEvalVal (substUpdate α v false)) then
    substUpdate α v false
  else
    substUpdate α v true

/-- Non-gate resolvent entailment condition: every non-tautological resolvent of `posNonGate`
with `negNonGate` is already entailed by `gateBveClauses v gp`. -/
@[expose] def GateNonGateEntailed (v : Nat) (gp : GatePartition) : Prop :=
  ∀ c ∈ gp.posNonGate, ∀ d ∈ gp.negNonGate,
    let r := dedupLits (resolveOn (mkLit v true) c d)
    clauseIsTaut r = false →
    (cnfOfClauses (gateBveClauses v gp)).EntailsClause (cnfClause r)

/-- Semantic / functional gate definition (`gates.c`, `definition.c`): no assignment to variables
other than `v` can simultaneously satisfy `posGate` with `v = false` and `negGate` with
`v = true`. -/
@[expose] def GateFunctional (v : Nat) (posGate negGate : List (List Nat)) : Prop :=
  ∀ α : Nat → Bool,
    ¬ ((cnfOfClauses posGate).Sat (substUpdate α v false) ∧
       (cnfOfClauses negGate).Sat (substUpdate α v true))

end LeanQbe.T.Examples.Kissat.Ref
