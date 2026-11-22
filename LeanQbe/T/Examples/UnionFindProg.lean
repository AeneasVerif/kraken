module

public import LeanQbe.T.Notation

/-!
# Pure AST Definitions for Union-Find (`UnionFindProg`)
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.UnionFind

open LeanQbe.T

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

/-- The closed union-find function list. -/
def ufFns : List Fn :=
  [ ⟨"find", [i64, i64], [i64], find⟩
  , ⟨"union", [i64, i64, i64], [], union⟩
  , ⟨"unionInline", [i64, i64, i64], [], unionInline⟩ ]

end LeanQbe.T.Examples.UnionFind
