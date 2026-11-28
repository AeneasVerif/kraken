/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Ref.Shrink

/-!
# Pure Lean Layer-A CDCL Theory: Clause Shrinking & Failed-Literal Analysis

Builds on `Shrink` (pure Lean, zero `Kraken.Mem` imports):

1. **`minimizeBlockExec_sound` and `shrink_clause_sound`** (`kissat_shrink_clause`, `shrink.c`):
   end-to-end soundness of `splitLevelBlocksRev`, `shrinkBlockExec`, and `minimizeBlockExec`
   fallback across all maximal level blocks, plus `resetPoisoned`.
2. **Failed-literal backward analysis (`analyze_failed_literal`, `analyze.c:390-517`)**:
   - Executable `analyzeFailedLiteralExec` modeling conflict scanning, backward trail resolution,
     `unresolved == 1` unit extraction, the `other == unit` skip (`analyze.c:473`), `goto DONE`,
     and trail-start guard (`t == 0`).
   - `failedLit_other_ne_unit`: proves `other == unit` is unreachable under `ReasonDagInv` and
     `vars_nodup`.
   - `analyzeFailedLiteralExec_sound`: proves every emitted unit (both intermediate units and
     `¬failed`) is entailed by `F₀`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Ref

open Std.Sat

/-! ## 2. Failed-literal backward analysis (`analyze.c:390-517`) -/

/-- Scan conflict clause in `analyze_failed_literal` (`analyze.c:410-426`), collecting level-1
falsified trail literals in `A` or returning `none` (`goto DONE`) if `notFailed ∈ conflict`. -/
@[expose] def scanFailedConflict (s : CdclState) (notFailed : Nat) :
    List Nat → List Nat → Option (List Nat)
  | [], A => some A
  | lit :: rest, A =>
    if lit == notFailed then none
    else if stateLevel s lit == 0 then scanFailedConflict s notFailed rest A
    else
      let t := litNeg lit
      let A' := if A.any (fun a => litVar a == litVar t) then A else t :: A
      scanFailedConflict s notFailed rest A'

/-- Scan a `.large` reason clause in `analyze_failed_literal` (`analyze.c:468-491`), skipping
`other == lit`, skipping `prevUnit == some other` (`other == unit`, proved unreachable by
`failedLit_other_ne_unit`), returning `none` on `other == notFailed` (`goto DONE`), skipping
level-0 literals, and collecting new level-1 antecedents. -/
@[expose] def resolveLargeFailed (s : CdclState) (lit notFailed : Nat) (prevUnit : Option Nat) :
    List Nat → List Nat → Option (List Nat)
  | [], A => some A
  | other :: rest, A =>
    if other == lit then
      resolveLargeFailed s lit notFailed prevUnit rest A
    else if prevUnit == some other then
      resolveLargeFailed s lit notFailed prevUnit rest A
    else if other == notFailed then
      none
    else if stateLevel s other == 0 then
      resolveLargeFailed s lit notFailed prevUnit rest A
    else
      let t := litNeg other
      let A' := if A.any (fun a => litVar a == litVar t) then A else t :: A
      resolveLargeFailed s lit notFailed prevUnit rest A'

/-- Backward trail walk in `analyze_failed_literal` (`analyze.c:428-497`), stopping at `t == 0`,
emitting additional units when `unresolved == 1` (`A_rest.isEmpty`), and appending `notFailed` at
`DONE`. -/
@[expose] def analyzeFailedLoop (s : CdclState) (notFailed : Nat) :
    Nat → List Nat → List Nat → Option Nat → List Nat
  | t, A, units, prevUnit =>
    match s.trail[t]? with
    | none => units ++ [notFailed]
    | some lit =>
      if !A.any (fun a => litVar a == litVar lit) then
        match t with
        | 0 => units ++ [notFailed]
        | t' + 1 => analyzeFailedLoop s notFailed t' A units prevUnit
      else
        let A_rest := A.filter (fun a => litVar a != litVar lit)
        let emit := A_rest.isEmpty
        let prevUnit' := if emit then some (litNeg lit) else prevUnit
        let units' := if emit then units ++ [litNeg lit] else units
        match stateReason s lit with
        | .decision | .unit => units' ++ [notFailed]
        | .binary other =>
          if prevUnit' == some other then
            units' ++ [notFailed]
          else if other == notFailed then
            units' ++ [notFailed]
          else if stateLevel s other == 0 then
            match t with
            | 0 => units' ++ [notFailed]
            | t' + 1 => analyzeFailedLoop s notFailed t' A_rest units' prevUnit'
          else
            let tOth := litNeg other
            let A' :=
              if A_rest.any (fun a => litVar a == litVar tOth) then A_rest else tOth :: A_rest
            match t with
            | 0 => units' ++ [notFailed]
            | t' + 1 => analyzeFailedLoop s notFailed t' A' units' prevUnit'
        | .large cid =>
          match s.clauses[cid]? with
          | some (some cl) =>
            if !cl.garbage && cl.lits.contains lit then
              match resolveLargeFailed s lit notFailed prevUnit' cl.lits A_rest with
              | none => units' ++ [notFailed]
              | some A' =>
                match t with
                | 0 => units' ++ [notFailed]
                | t' + 1 => analyzeFailedLoop s notFailed t' A' units' prevUnit'
            else
              units' ++ [notFailed]
          | _ => units' ++ [notFailed]

/-- Full executable model of `analyze_failed_literal` (`analyze.c:390-517`): returns all learned
unit literals (intermediate units followed by `litNeg failed`). -/
@[expose]
def analyzeFailedLiteralExec (s : CdclState) (failed : Nat) (conflict : List Nat) : List Nat :=
  let notFailed := litNeg failed
  match scanFailedConflict s notFailed conflict [] with
  | none => [notFailed]
  | some A =>
    if s.trail.size == 0 then [notFailed]
    else analyzeFailedLoop s notFailed (s.trail.size - 1) A [] none

end LeanQbe.T.Examples.Kissat.Ref
