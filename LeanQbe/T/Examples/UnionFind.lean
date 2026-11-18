module

public import LeanQbe.T.Notation
public import LeanQbe.T.Logic.Mem

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

/-- Reusable path-halving `find` loop fragment: finds root of `x` in `p` and passes it to `k`. -/
def findK {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} (p x : V i64)
    (k : V i64 → Expr V L rs) : Expr V L rs :=
  tqbe {
    loop @lp(%y:l = %x) {
      %off:l = shl %y, 3
      %a:l = add %p, %off
      %py:l = load %a
      %done:b = ceql %py, %y
      jnz %done, { ⟨k y⟩ }, {
        %poff:l = shl %py, 3
        %pa:l = add %p, %poff
        %ppy:l = load %pa
        store %ppy, %a
        continue @lp(%ppy)
      }
    }
  }

/-- `find(p, x)`: find the canonical representative of `x` with path halving. -/
def find : Func [i64, i64] [i64] :=
  tqbe(%p:l, %x:l) -> l {
    %r:l <- findK(%p, %x)
    ret %r
  }

/-- `union(p, x, y)`: merge the sets containing `x` and `y` via calls to `$find`. -/
def union : Func [i64, i64, i64] [] :=
  tqbe(%p:l, %x:l, %y:l) -> () {
    %rx:l = call $find(%p, %x)
    %ry:l = call $find(%p, %y)
    %same:b = ceql %rx, %ry
    jnz %same, {
      ret
    }, {
      %off:l = shl %rx, 3
      %a:l = add %p, %off
      store %ry, %a
      ret
    }
  }

/-- `unionInline(p, x, y)`: single-function union with two inlined `findK` loops. -/
def unionInline : Func [i64, i64, i64] [] :=
  tqbe(%p:l, %x:l, %y:l) -> () {
    %rx:l <- findK(%p, %x)
    %ry:l <- findK(%p, %y)
    %same:b = ceql %rx, %ry
    jnz %same, {
      ret
    }, {
      %off:l = shl %rx, 3
      %a:l = add %p, %off
      store %ry, %a
      ret
    }
  }

/-- Public specification of `find(p, x)`. -/
def findSpec : Spec [i64, i64] [i64] := fun (p, x, ()) m Q _ =>
  ∃ n rep R, (uf p n rep ⋆ R) m ∧ x.toNat < n ∧
    ∀ m', (uf p n rep ⋆ R) m' → Q (rep x, ()) m'

/-- Public specification of `union(p, x, y)` and `unionInline(p, x, y)`. -/
def unionSpec : Spec [i64, i64, i64] [] := fun (p, x, y, ()) m Q _ =>
  ∃ n rep R, (uf p n rep ⋆ R) m ∧ x.toNat < n ∧ y.toNat < n ∧
    ∀ m', (uf p n (merge rep x y) ⋆ R) m' → Q () m'

/-- The closed union-find module. -/
def ufFns : List Fn :=
  [ ⟨"find", [i64, i64], [i64], find⟩
  , ⟨"union", [i64, i64, i64], [], union⟩
  , ⟨"unionInline", [i64, i64, i64], [], unionInline⟩ ]

/-- Closed module specification environment for `ufFns`. -/
def ufEnv : Env
  | "find", [.bits 64, .bits 64], [.bits 64] => findSpec
  | "union", [.bits 64, .bits 64, .bits 64], [] => unionSpec
  | "unionInline", [.bits 64, .bits 64, .bits 64], [] => unionSpec
  | _, _, _ => fun _ _ _ _ => False

end LeanQbe.T.Examples.UnionFind
