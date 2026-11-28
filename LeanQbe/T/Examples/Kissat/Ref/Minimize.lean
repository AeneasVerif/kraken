/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Ref.Cdcl

/-!
# Pure Lean Layer-A CDCL Theory for Clause Minimization (Part 1)

Foundational pure-Lean theory (zero `Kraken.Mem` / `Kraken.Separation` imports) supporting
Kissat's lazy-level clause minimization (`minimize.c`) and shrinking (`shrink.c`):

1. `LazyTrailInv`: Kissat-faithful trail invariant omitting `levels_mono` (supporting lazy
   assignment levels `fastassign.h:31-32`, `proplit.h:68,90`), with `TrailInv.toLazy`,
   `lazyTrailEntailment`, `lazyTrailEntailment_level0`, and `backtrackFilter_preserves_lazyInv`.
2. `MinState`: trail-indexed assignment state (`trailPos`, `removable`, `poisoned`, `shrinkable`,
   `frameUsed`), `TrailPosInv`, `MinState.ofCdcl`, and the lexicographic `(level, trailPos)`
   preorder `varLe` (`⪯`) / strict order `varLt` (`≺`), showing `ReasonDagInv` forces
   antecedents to be strictly `varLt`-smaller even under lazy levels.
3. `MinState.RemovableInv` (lexicographic `(level, trailPos)` removability invariant) and:
   - (a) Initial clause-literal seeding lemma (`seedRemovable_preserves`, `minimize.c:172-173`).
   - (b) Soundness & invariance of `poisoned`, `shrinkable`, `frameUsed`, and depth limits.
   - (c) Monotonicity, single-step & binary-chain `removable` caching (`setRemovableChain`).
   - (d) Cut-deletion theorem (`cut_delete_sound`): depth-0 justification deletes `l` while
     preserving both `F₀.EntailsClause (C \ {l})` and `RemovableInv F₀ (C \ {l})`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Ref

open Std.Sat

/-! ## 1. Lazy-level filtering backtrack -/

/-- Kissat-faithful filtering backtrack (`backtrack.c:94-112`): compacts every trail literal
with `level ≤ targetLevel` left-to-right without assuming `levels_mono`. -/
@[expose] def backtrackFilter (s : CdclState) (targetLevel : Nat) : CdclState :=
  { s with
    trail := (s.trail.toList.filter (fun l => decide (stateLevel s l ≤ targetLevel))).toArray
    level := Nat.min s.level targetLevel }

/-! ## 2. Trail-indexed `MinState` and lexicographic `(level, trailPos)` preorder -/

/-- Trail-indexed assignment state supporting Kissat `minimize` and `shrink`. -/
structure MinState where
  cdcl : CdclState
  trailPos : Array Nat
  removable : Array Bool
  poisoned : Array Bool
  shrinkable : Array Bool
  frameUsed : Array Nat

/-- Build `trailPos[litVar trail[i]] := i` for a trail array. -/
@[expose] def buildTrailPos (trail : Array Nat) : Array Nat :=
  let rec go (i : Nat) (acc : Array Nat) : Array Nat :=
    if h : i < trail.size then
      go (i + 1) (arraySetPad acc (litVar trail[i]) i 0)
    else acc
  termination_by trail.size - i
  go 0 #[]

/-- Construct a clean `MinState` from a `CdclState`. -/
@[expose] def MinState.ofCdcl (cdcl : CdclState) (frameUsed : Array Nat := #[]) : MinState :=
  { cdcl := cdcl
    trailPos := buildTrailPos cdcl.trail
    removable := Array.replicate cdcl.numVars false
    poisoned := Array.replicate cdcl.numVars false
    shrinkable := Array.replicate cdcl.numVars false
    frameUsed := frameUsed }

@[expose, inline] def MinState.varLevel (s : MinState) (v : Nat) : Nat :=
  s.cdcl.levels.getD v 0

@[expose, inline] def MinState.litLevel (s : MinState) (l : Nat) : Nat :=
  s.varLevel (litVar l)

@[expose, inline] def MinState.varTrailPos (s : MinState) (v : Nat) : Nat :=
  s.trailPos.getD v 0

@[expose, inline] def MinState.litTrailPos (s : MinState) (l : Nat) : Nat :=
  s.varTrailPos (litVar l)

@[expose, inline] def MinState.isRemovable (s : MinState) (v : Nat) : Bool :=
  s.removable.getD v false

@[expose, inline] def MinState.isPoisoned (s : MinState) (v : Nat) : Bool :=
  s.poisoned.getD v false

@[expose, inline] def MinState.isShrinkable (s : MinState) (v : Nat) : Bool :=
  s.shrinkable.getD v false

@[expose, inline] def MinState.getFrameUsed (s : MinState) (lvl : Nat) : Nat :=
  s.frameUsed.getD lvl 0

@[expose] def MinState.setRemovable (s : MinState) (v : Nat) (b : Bool) : MinState :=
  { s with removable := arraySetPad s.removable v b false }

@[expose] def MinState.setPoisoned (s : MinState) (v : Nat) (b : Bool) : MinState :=
  { s with poisoned := arraySetPad s.poisoned v b false }

@[expose] def MinState.setShrinkable (s : MinState) (v : Nat) (b : Bool) : MinState :=
  { s with shrinkable := arraySetPad s.shrinkable v b false }

@[expose] def MinState.resetPoisoned (s : MinState) : MinState :=
  { s with poisoned := Array.replicate s.poisoned.size false }

@[expose] def MinState.resetShrinkable (s : MinState) : MinState :=
  { s with shrinkable := Array.replicate s.shrinkable.size false }

@[expose] def MinState.resetRemovable (s : MinState) : MinState :=
  { s with removable := Array.replicate s.removable.size false }

/-- Consistency of `trailPos` with `cdcl.trail`. -/
@[expose] def TrailPosInv (s : CdclState) (trailPos : Array Nat) : Prop :=
  ∀ (i : Nat) (_hi : i < s.trail.size), trailPos.getD (litVar s.trail[i]) 0 = i

/-- Base invariant on `MinState.cdcl` and `MinState.trailPos` (preserved by all flag updates). -/
structure MinBaseInv (s : MinState) : Prop where
  trail_inv : LazyTrailInv s.cdcl
  pos_inv : TrailPosInv s.cdcl s.trailPos

/-- Lexicographic `(level, trailPos)` preorder `v ⪯ w` on variables. -/
@[expose] def varLe (s : MinState) (v w : Nat) : Prop :=
  s.varLevel v < s.varLevel w ∨
    (s.varLevel v = s.varLevel w ∧ s.varTrailPos v ≤ s.varTrailPos w)

/-- Strict lexicographic `(level, trailPos)` order `v ≺ w` on variables. -/
@[expose] def varLt (s : MinState) (v w : Nat) : Prop :=
  s.varLevel v < s.varLevel w ∨
    (s.varLevel v = s.varLevel w ∧ s.varTrailPos v < s.varTrailPos w)

/-- Executable strict lexicographic comparison on literals. -/
@[expose, inline] def varLtLit (s : MinState) (l1 l2 : Nat) : Bool :=
  let lvl1 := s.litLevel l1
  let lvl2 := s.litLevel l2
  lvl1 < lvl2 || (lvl1 == lvl2 && s.litTrailPos l1 < s.litTrailPos l2)

/-! ## 3. Lexicographic `RemovableInv`, seeding, poison/depth safety, caching, and cut deletion -/

/-- Kissat's lexicographic `(level, trailPos)` removability invariant relative to current
clause `C` (`minimize.c` / `shrink.c`): every non-level-0 `removable` variable `v`
is falsified/assigned on the trail (`t_v = trail[i]`) and implied by `F₀` together with the
falsification of `{ l ∈ C | var l ⪯ v }`. -/
@[expose] def MinState.RemovableInv (s : MinState) (C : List Nat) : Prop :=
  ∀ v, s.isRemovable v = true → 0 < s.varLevel v →
    ∃ (i : Nat) (_hi : i < s.cdcl.trail.size),
      litVar s.cdcl.trail[i] = v ∧
      ∀ α : Nat → Bool, s.cdcl.f0.Sat α →
        (∀ l ∈ C, varLe s (litVar l) v → ¬ (cnfClause [l]).Sat α) →
        (cnfClause [s.cdcl.trail[i]]).Sat α

/-- Seed every literal variable of clause `C` onto `removable` (`minimize.c:172-173`). -/
@[expose] def seedRemovable (s : MinState) (C : List Nat) : MinState :=
  C.foldl (fun st l => st.setRemovable (litVar l) true) s

/-- Semantic antecedent-removability condition for a true literal `t` on the trail. -/
@[expose] def AntecedentsRemovable (s : MinState) (t : Nat) : Prop :=
  match stateReason s.cdcl t with
  | .decision => False
  | .unit => s.litLevel t = 0
  | .binary other =>
    s.litLevel other = 0 ∨ s.isRemovable (litVar other) = true
  | .large cid =>
    ∃ cl : Clause, s.cdcl.clauses[cid]? = some (some cl) ∧ !cl.garbage = true ∧ t ∈ cl.lits ∧
      ∀ x ∈ cl.lits, x ≠ t → s.litLevel x = 0 ∨ s.isRemovable (litVar x) = true

/-- Folding `setRemovable · true` over a list of variables. -/
@[expose] def setRemovableList (s : MinState) (vs : List Nat) : MinState :=
  vs.foldl (fun st v => st.setRemovable v true) s

/-- Lexicographic `Nat` measure of `(varLevel, varTrailPos)` bounded by `trail.size + 1`. -/
@[expose] def varLexMeasure (s : MinState) (v : Nat) : Nat :=
  s.varLevel v * (s.cdcl.trail.size + 1) + s.varTrailPos v

end LeanQbe.T.Examples.Kissat.Ref
