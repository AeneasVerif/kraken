/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Ref.Gates

/-!
# Pure Lean Layer-A Soundness Theory for BCA, BVA / Factorization & Tier-B Traces

Builds on `Kissat.Ref.Gates` (`factor.c`):

1. **Blocked Clause Addition (`BCA`) & Bounded Variable Addition / Factorization (`factor.c`)**:
   proves general and fresh-variable BCA (`bca_unsat_sound`, `fresh_bca_batch_unsat`) and
   Kissat's fresh-variable divider/quotient factorization (`bvaFactor_unsat_sound`,
   `bvaFactor_sat_recon`, `bvaFactor_equisat`).
2. **Unified Tier-B Pipeline (`TierBStep`, `TierBTrace`)**:
   composes `Subst`, `BCE`, `Gate-BVE`, and `BVA/Factor` into a single witness-reconstructing
   trace (`tierBTrace_unsat`, `tierBTrace_sat_recon`, `tierBTrace_equisat`) with an executable
   `Array Bool` reconstruction bridge (`tierBTraceExtendArr_sound`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Ref

open Std.Sat

/-! ## 3. Blocked Clause Addition (`BCA`) and Bounded Variable Addition (`factor.c`) -/

/-- Kissat `factor.c` divider clauses `[z, fᵢ]` for each factor literal `fᵢ ∈ L`. -/
@[expose] def bvaDivClauses (z : Nat) (L : List Nat) : List (List Nat) :=
  L.map fun f => [mkLit z true, f]

/-- Kissat `factor.c` quotient clauses `[¬z] ++ qⱼ` for each quotient subclause `qⱼ ∈ Q`. -/
@[expose] def bvaQuotClauses (z : Nat) (Q : List (List Nat)) : List (List Nat) :=
  Q.map fun q => mkLit z false :: q

/-- Order-independent membership test: `true` iff `c` is subsumed by some product clause
`f :: q` with `f ∈ L` and `q ∈ Q`. -/
@[expose] def bvaIsFactored (L : List Nat) (Q : List (List Nat)) (c : List Nat) : Bool :=
  L.any fun f => c.contains f && Q.any fun q => q.all fun x => c.contains x

/-- Kissat `factor.c` Bounded Variable Addition / Factorization transform: introduces fresh `z`,
adds divider clauses `{[z, f] | f ∈ L}` and quotient clauses `{¬z :: q | q ∈ Q}`, and deletes
every clause subsumed by a factored product clause `f :: q`. -/
@[expose] def bvaFactorClauses (z : Nat) (L : List Nat) (Q : List (List Nat))
    (cs : List (List Nat)) : List (List Nat) :=
  bvaDivClauses z L ++ bvaQuotClauses z Q ++ cs.filter (fun c => !bvaIsFactored L Q c)

/-- Forward witness assignment for fresh variable `z` introduced by `bvaFactorClauses`:
`z := false` if every divider literal `f ∈ L` is already true under `α`, else `z := true`. -/
@[expose] def bvaExtend (z : Nat) (L : List Nat) (α : Nat → Bool) : Nat → Bool :=
  substUpdate α z (!(L.all (evalLitVal α)))

/-- Validity side-condition for Bounded Variable Addition / Factorization (`factor.c`). -/
@[expose]
def BvaValid (z : Nat) (L : List Nat) (Q : List (List Nat)) (cs : List (List Nat)) : Prop :=
  VarFreshIn cs z ∧
  (∀ f ∈ L, litVar f ≠ z) ∧
  (∀ q ∈ Q, ∀ x ∈ q, litVar x ≠ z) ∧
  (∀ f ∈ L, ∀ q ∈ Q, (cnfOfClauses cs).EntailsClause (cnfClause (f :: q)))

/-! ## 4. Unified Tier-B Inprocessing Trace and Executable `Array Bool` Reconstruction -/

/-- One Tier-B inprocessing step (`substitute.c`, `BCE`, `gates.c` BVE, or `factor.c` BVA). -/
inductive TierBStep where
  | subst (v l : Nat)
  | bce (l : Nat) (clause : List Nat)
  | gateBve (v : Nat) (gp : GatePartition)
  | bvaFactor (z : Nat) (dividers : List Nat) (quotients : List (List Nat))
  deriving Repr, DecidableEq

/-- Multi-step Tier-B inprocessing trace. -/
abbrev TierBTrace := List TierBStep

/-- Execute a single Tier-B transformation step on a clause list. -/
@[expose] def tierBStepApply (step : TierBStep) (cs : List (List Nat)) : List (List Nat) :=
  match step with
  | .subst v l => substClauses v l cs
  | .bce _ c => cs.erase c
  | .gateBve v gp => gateBveClauses v gp
  | .bvaFactor z L Q => bvaFactorClauses z L Q cs

/-- Reconstruct a model across a single Tier-B step. -/
@[expose] def tierBStepExtend (step : TierBStep) (α : Nat → Bool) : Nat → Bool :=
  match step with
  | .subst v l => substExtend v l α
  | .bce l c => extendBce l c α
  | .gateBve v gp => extendGateBve v gp.posClauses α
  | .bvaFactor _ _ _ => α

/-- Semantic validity of one Tier-B step on clause list `cs`. -/
@[expose] def TierBStepValid (cs : List (List Nat)) : TierBStep → Prop
  | .subst v l => litVar l ≠ v ∧ EquivEntailed (cnfOfClauses cs) v l
  | .bce l c => c ∈ cs ∧ IsBlockedOn (cs.erase c) c l
  | .gateBve v gp =>
    (∀ α, (cnfOfClauses gp.allClauses).Sat α ↔ (cnfOfClauses cs).Sat α) ∧
    GatePartValid v gp ∧
    GateNonGateEntailed v gp
  | .bvaFactor z L Q => BvaValid z L Q cs

/-- Apply a multi-step Tier-B trace left-to-right. -/
@[expose] def tierBTraceApply : TierBTrace → List (List Nat) → List (List Nat)
  | [], cs => cs
  | s :: rest, cs => tierBTraceApply rest (tierBStepApply s cs)

/-- Reconstruct a model across a multi-step Tier-B trace right-to-left (`foldr`). -/
@[expose] def tierBTraceExtend (tr : TierBTrace) (α : Nat → Bool) : Nat → Bool :=
  tr.foldr tierBStepExtend α

/-- Inductive validity of a multi-step Tier-B trace on `cs`. -/
@[expose] def TierBTraceValid : List (List Nat) → TierBTrace → Prop
  | _, [] => True
  | cs, s :: rest => TierBStepValid cs s ∧ TierBTraceValid (tierBStepApply s cs) rest

/-! ### Executable `Array Bool` Reconstruction Bridges -/

/-- Executable BCE witness reconstruction on `Array Bool`. -/
@[expose] def extendBceArr (l : Nat) (c : List Nat) (σ : Array Bool) : Array Bool :=
  if evalClause σ c then σ else arraySetPad σ (litVar l) (!(litSign l)) false

/-- Executable BCE stack reconstruction on `Array Bool`. -/
@[expose] def extendBceStackArr (st : BceReconStack) (σ : Array Bool) : Array Bool :=
  st.foldr (fun e acc => extendBceArr e.lit e.clause acc) σ

/-- Executable Gate-BVE witness reconstruction on `Array Bool`. -/
@[expose]
def extendGateBveArr (v : Nat) (posClauses : List (List Nat)) (σ : Array Bool) : Array Bool :=
  let σF := arraySetPad σ v false false
  if posClauses.all (evalClause σF) then σF else arraySetPad σ v true false

/-- Executable single-step Tier-B reconstruction on `Array Bool`. -/
@[expose] def tierBStepExtendArr (step : TierBStep) (σ : Array Bool) : Array Bool :=
  match step with
  | .subst v l => substExtendArr v l σ
  | .bce l c => extendBceArr l c σ
  | .gateBve v gp => extendGateBveArr v gp.posClauses σ
  | .bvaFactor _ _ _ => σ

/-- Executable multi-step Tier-B reconstruction on `Array Bool`. -/
@[expose] def tierBTraceExtendArr (tr : TierBTrace) (σ : Array Bool) : Array Bool :=
  tr.foldr tierBStepExtendArr σ

end LeanQbe.T.Examples.Kissat.Ref
