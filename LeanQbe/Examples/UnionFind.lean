module

public import LeanQbe.Notation
public import LeanQbe.Logic.Mem

/-!
# Union-find on an array of 64-bit parent indices (plan step 2c, decision D14)

The structure is an array of `n` words at address `p`: `p[i]` is the parent of `i`, and roots are
their own parent. `find` uses path halving (`p[x] := p[p[x]]; x := p[x]`) in a loop made of a join
point, with no recursion (decision D6). `union` links the root of `x` under the root of `y`.

The functional model is the partition itself, given by its canonical representative `rep : Val → Val`
(`i` and `j` are in one class iff `rep i = rep j`). `uf p n rep` says the array at `p` is some forest
whose roots are exactly the representatives `rep`. Proofs are in `UnionFindLemmas.lean`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.UnionFind

open Std.ExtHashMap

/-! ## Programs -/

/-- `find` with path halving, as a Lean macro in continuation-passing style: `k r` runs with the
representative `r` of `x`. -/
def findK {V L : Type} (p x : V) (k : V → Expr V L) : Expr V L := qbe {
  @loop(%x) {
    %o =l shl %x, 3
    %a =l add %p, %o
    %px =l loadl %a
    %c =w ceql %px, %x
    jnz %c, { ⟨k x⟩ }, {
      %o2 =l shl %px, 3
      %a2 =l add %p, %o2
      %gp =l loadl %a2
      storel %gp, %a
      jmp @loop(%gp)
    }
  }
  jmp @loop(%x)
}

/-- `function l $find(l %p, l %x)`. -/
def find : Func := fun _ _ => qbe(%p, %x) {
  %r <- findK(%p, %x)
  ret %r
}

/-- `function $union(l %p, l %x, l %y)`, calling `$find`. -/
def union : Func := fun _ _ => qbe(%p, %x, %y) {
  %rx =l call $find(%p, %x)
  %ry =l call $find(%p, %y)
  %c =w ceql %rx, %ry
  jnz %c, { ret }, {
    %o =l shl %rx, 3
    %a =l add %p, %o
    storel %ry, %a
    ret
  }
}

/-- `union` with `find` inlined twice by the macro. -/
def unionInline : Func := fun _ _ => qbe(%p, %x, %y) {
  %rx <- findK(%p, %x)
  %ry <- findK(%p, %y)
  %c =w ceql %rx, %ry
  jnz %c, { ret }, {
    %o =l shl %rx, 3
    %a =l add %p, %o
    storel %ry, %a
    ret
  }
}

/-! ## Functional model -/

/-- The parent of `i` in the array contents `parent`. -/
def pa (parent : List Val) (i : Val) : Val := parent.getD i.toNat 0

/-- `parent` is a forest on `[0, n)` whose roots are the representatives `rep`. `rank` strictly
decreases towards the roots; it is a ghost, the termination measure of `find`. -/
structure Forest (n : Nat) (parent : List Val) (rep : Val → Val) (rank : Val → Nat) : Prop where
  len : parent.length = n
  closed : ∀ i : Val, i.toNat < n → (pa parent i).toNat < n
  rep_lt : ∀ i : Val, i.toNat < n → (rep i).toNat < n
  rep_root : ∀ i : Val, i.toNat < n → pa parent (rep i) = rep i
  root_rep : ∀ i : Val, i.toNat < n → pa parent i = i → rep i = i
  rep_pa : ∀ i : Val, i.toNat < n → rep (pa parent i) = rep i
  rank_lt : ∀ i : Val, i.toNat < n → pa parent i ≠ i → rank (pa parent i) < rank i

/-- A union-find structure at `p` on the elements `[0, n)`, representing the partition `rep`. -/
def uf (p : Val) (n : Nat) (rep : Val → Val) : Mem 64 → Prop :=
  fun m => ∃ parent, ∃ rank, Forest n parent rep rank ∧ array64 p parent m

/-- The partition after merging the classes of `x` and `y`. -/
def merge (rep : Val → Val) (x y : Val) : Val → Val :=
  fun i => if rep i = rep x then rep y else rep i

/-! ## Contracts -/

/-- `find(p, x)` returns the representative of `x` and keeps the partition. -/
def findSpec : Spec := fun args m Q _ =>
  ∃ p x n rep R, args = [p, x] ∧ (uf p n rep ⋆ R) m ∧ x.toNat < n ∧
    ∀ m', (uf p n rep ⋆ R) m' → Q [rep x] m'

/-- `union(p, x, y)` merges the classes of `x` and `y`. -/
def unionSpec : Spec := fun args m Q _ =>
  ∃ p x y n rep R, args = [p, x, y] ∧ (uf p n rep ⋆ R) m ∧ x.toNat < n ∧ y.toNat < n ∧
    ∀ m', (uf p n (merge rep x y) ⋆ R) m' → Q [] m'

def findFn : Fn := ⟨"find", find⟩
def unionFn : Fn := ⟨"union", union⟩
def unionInlineFn : Fn := ⟨"unionInline", unionInline⟩

/-- The union-find module (`find`, `union` calling `find` twice, and `unionInline`). -/
def ufFns : List Fn := [findFn, unionFn, unionInlineFn]

/-- Environment mapping `"find"` to `findSpec` and `"union"` / `"unionInline"` to `unionSpec`. -/
def ufEnv : Env := fun g => if g = "find" then findSpec else unionSpec

end LeanQbe.UnionFind
