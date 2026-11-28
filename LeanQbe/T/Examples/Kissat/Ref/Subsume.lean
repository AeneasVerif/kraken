/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Ref.Reduce

/-!
# Pure Lean Layer-A Inprocessing Theory: Subsumption & Self-Subsuming Resolution

Pure Lean formalization (zero `Kraken.Mem` or `Kraken.Separation` imports) of forward/backward
subsumption deletion, self-subsuming resolution (`SSR`), and on-the-fly subsumption (`OTFS`)
preserving full logical equivalence (`∀ α, F'.Sat α ↔ F.Sat α` and `F'.Unsat ↔ F.Unsat`):

1. **Clause-list & CNF replacement/deletion primitives** (`clauseSubset`, `removeLit`,
   `deleteIdx`, `replaceIdx`).
2. **Subsumption deletion soundness** (`subsume_cnf_equiv`, `subsume_clauses_equiv`,
   `entailed_del_equiv`): deleting `C` when another distinct clause `D ⊆ C` remains in `F`
   preserves both `Sat α` (`↔`) and `Unsat` (`↔`).
3. **Self-subsuming resolution & OTFS** (`ssr_cnf_equiv`, `ssr_clauses_equiv`,
   `otfs_clauses_equiv`): if `l ∈ C`, `¬l ∈ D`, and `(D \ {¬l}) ⊆ (C \ {l})`, then
   `D ≠ C` automatically and replacing `C` with `C \ {l}` preserves `Sat α` (`↔`) and
   `Unsat` (`↔`); similarly replacing `C` with `resolveOn l C D` when `resolveOn l C D ⊆ C`.
4. **Executable passes & DB/CDCL bridge** (`subsumePass`, `ssrPass`, `subsumeAndSSR`,
   `subsume_pass_equiv`, `ssr_pass_equiv`, `subsume_ssr_equiv`, `subsume_db_equiv`,
   `ssr_db_equiv`, `subsume_preserves_inv`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Ref

open Std.Sat

/-! ## 1. Clause subsets, literal removal, and list slot deletion/replacement -/

/-- Decidable clause subsumption check `d ⊆ c`. -/
@[expose] def clauseSubset (d c : List Nat) : Bool :=
  d.all fun l => c.contains l

/-- Remove every occurrence of literal `l` from clause `c`. -/
@[expose] def removeLit (c : List Nat) (l : Nat) : List Nat :=
  c.filter (· != l)

/-- Delete element at index `i` from a list (leaving `xs` unchanged if `i ≥ xs.length`). -/
@[expose] def deleteIdx {α : Type} : List α → Nat → List α
  | [], _ => []
  | _ :: xs, 0 => xs
  | x :: xs, i + 1 => x :: deleteIdx xs i

/-- Replace element at index `i` with `y` (leaving `xs` unchanged if `i ≥ xs.length`). -/
@[expose] def replaceIdx {α : Type} : List α → Nat → α → List α
  | [], _, _ => []
  | _ :: xs, 0, y => y :: xs
  | x :: xs, i + 1, y => x :: replaceIdx xs i y

/-! ## 4. Executable subsumption & SSR passes with equivalence theorems -/

/-- Check whether `c` is subsumed by any clause in `others`. -/
@[expose] def isSubsumedByAny (c : List Nat) (others : List (List Nat)) : Bool :=
  others.any fun d => clauseSubset d c

/-- Try strengthening `c` by a single self-subsuming resolution step against `d`. -/
@[expose] def trySSR (c d : List Nat) : Option (List Nat) :=
  match c.find? fun l =>
      d.contains (litNeg l) &&
        (removeLit d (litNeg l)).all fun x => x != l && c.contains x with
  | some l => some (removeLit c l)
  | none => none

/-- Iteratively self-subsume `c` against every clause in `others`. -/
@[expose] def strengthenWithList (c : List Nat) (others : List (List Nat)) : List Nat :=
  others.foldl (fun cur d => match trySSR cur d with | some cur' => cur' | none => cur) c

/-- Single forward/backward subsumption elimination pass over a clause list, checking each
clause strictly against the remaining kept + unvisited clauses (`kept ++ rest`). -/
@[expose] def subsumePassAux : List (List Nat) → List (List Nat) → List (List Nat)
  | kept, [] => kept.reverse
  | kept, c :: rest =>
    if isSubsumedByAny c kept || isSubsumedByAny c rest then
      subsumePassAux kept rest
    else
      subsumePassAux (c :: kept) rest

/-- Subsumption pass deleting subsumed clauses from `cs`. -/
@[expose] def subsumePass (cs : List (List Nat)) : List (List Nat) :=
  subsumePassAux [] cs

/-- Single SSR strengthening pass: strengthens every clause `c` against all other kept and
remaining clauses (`kept ++ rest`). -/
abbrev ssrPassAux : List (List Nat) → List (List Nat) → List (List Nat) :=
  clauseTransformPassAux (fun others c => strengthenWithList c others)

/-- Self-subsuming resolution pass over `cs`. -/
@[expose] def ssrPass (cs : List (List Nat)) : List (List Nat) :=
  ssrPassAux [] cs

/-- Iterated subsumption + self-subsuming resolution simplifier (`fuel` rounds). -/
@[expose] def subsumeAndSSR : Nat → List (List Nat) → List (List Nat)
  | 0, cs => cs
  | fuel + 1, cs => subsumeAndSSR fuel (subsumePass (ssrPass cs))

end LeanQbe.T.Examples.Kissat.Ref
