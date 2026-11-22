module

public import LeanQbe.T.Notation
public import LeanQbe.T.Module
public import LeanQbe.T.Logic.Mem
public import LeanQbe.T.Examples.UnionFindProg

/-!
# Union-Find (Disjoint Set Union) in `LeanQbe.T` (`T4`)

Typed-IR counterpart of `LeanQbe/Examples/UnionFind.lean`:
* `find` — iterative root lookup with path halving (`findK` loop).
* `union` — merges the trees containing two elements, calling `find`.
* `unionInline` — merges two elements with two inlined `findK` loops.
* `Forest`, `uf`, `merge`, `findSpec`, `unionSpec`, `ufFns`, `ufEnv` — separation-logic
  specification and closed module environment.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.UnionFind

open Std.ExtHashMap

/-- Parent lookup in the parent array (defaulting to `0` out of bounds). -/
def pa (parent : List (BitVec 64)) (i : BitVec 64) : BitVec 64 :=
  parent.getD i.toNat 0

/-- Representation invariant of a disjoint-set forest in a `n`-element `parent` array:
`rep` sends every element in `[0, n)` to its canonical root, and `rank` decreases along
non-root parent edges (ensuring loop termination without exposing `rank` in the public spec). -/
structure Forest (n : Nat) (parent : List (BitVec 64))
    (rep : BitVec 64 → BitVec 64) (rank : BitVec 64 → Nat) : Prop where
  len : parent.length = n
  closed : ∀ i : BitVec 64, i.toNat < n → (pa parent i).toNat < n
  rep_lt : ∀ i : BitVec 64, i.toNat < n → (rep i).toNat < n
  rep_root : ∀ i : BitVec 64, i.toNat < n → pa parent (rep i) = rep i
  root_rep : ∀ i : BitVec 64, i.toNat < n → pa parent i = i → rep i = i
  rep_pa : ∀ i : BitVec 64, i.toNat < n → rep (pa parent i) = rep i
  rank_lt : ∀ i : BitVec 64, i.toNat < n → pa parent i ≠ i → rank (pa parent i) < rank i

/-- Separation-logic predicate: valid forest of size `n` implementing `rep` at base `p`. -/
def uf (p : BitVec 64) (n : Nat) (rep : BitVec 64 → BitVec 64) : Mem 64 → Prop :=
  fun m => ∃ parent rank, Forest n parent rep rank ∧ array64 p parent m

/-- Abstract merge of the components of `x` and `y`: sends `x`'s class to `y`'s root. -/
def merge (rep : BitVec 64 → BitVec 64) (x y : BitVec 64) : BitVec 64 → BitVec 64 :=
  fun i => if rep i = rep x then rep y else rep i

/-- Public specification of `find(p, x)`. -/
def findSpec : Spec [i64, i64] [i64] := fun (p, x, ()) m Q _ =>
  ∃ n rep R, (uf p n rep ⋆ R) m ∧ x.toNat < n ∧
    ∀ m', (uf p n rep ⋆ R) m' → Q (rep x, ()) m'

/-- Public specification of `union(p, x, y)` and `unionInline(p, x, y)`. -/
def unionSpec : Spec [i64, i64, i64] [] := fun (p, x, y, ()) m Q _ =>
  ∃ n rep R, (uf p n rep ⋆ R) m ∧ x.toNat < n ∧ y.toNat < n ∧
    ∀ m', (uf p n (merge rep x y) ⋆ R) m' → Q () m'

/-- Closed union-find `Module` (`externs := []`, `exits := []`). -/
def ufModule : Module where
  fns := ufFns
  externs := []
  exits := []

/-- Closed module specification environment for `ufModule`. -/
def ufEnv : Env
  | "find", [.bits 64, .bits 64], [.bits 64] => findSpec
  | "union", [.bits 64, .bits 64, .bits 64], [] => unionSpec
  | "unionInline", [.bits 64, .bits 64, .bits 64], [] => unionSpec
  | _, _, _ => fun _ _ _ _ => False

end LeanQbe.T.Examples.UnionFind
