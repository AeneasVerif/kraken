module

public import LeanQbe.Notation

/-!
# The RUP check of lrat-trim, in QBE notation (plan step 7, pulled forward)

A port of `br_check_clause_non_strictly_by_propagation` from Kraken's
`Kraken/Bedrock2/Test/LratTrim.lean`, the function whose Bedrock2 proof is
`LratTrimRupProof.lean`. It is the same algorithm on the same memory layout, written as QBE IL would
be written:

* mutable locals become join-point parameters (`@p1(%l, %te, %sla)`), and Bedrock2's `checked` flag
  plus `lit = 0` / `aid = 0` loop exits become direct jumps to the continuations `@finish`, `@phase2`,
  `@fail`;
* `(load4(l) << 32) .>> 32` is `loadsw`, the sign-extending byte load is `loadsb`;
* `lit .< 0 ? -lit : lit` and the conditional negation `if lit .< 0 { val = -val }` are branch-free:
  with `s = lit sar 63`, `abs lit = (lit xor s) - s` and `neg-if val = (val xor s) - s`;
* `interact lrat_fail(code, id, aid, 0, 0)` is `exit $lrat_fail(…)` (decision D5), after flushing the
  register-resident state, as the original does.

The Bedrock2 `%❰…❱` inline helpers are Lean macros (CPS functions), each with its own `wp` lemma in
`LratRupLemmas.lean`.

Kernel state at `%st` (64-bit fields): `+16` literals_begin, `+24` values_begin, `+40` trail_begin,
`+48` trail_end, `+144` stat_resolved, `+152` stat_lit_assigned.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.LratRup

/-- `inline_assigned_literal`: `idx = |lit|`, `val = values[idx]` negated if `lit < 0`. -/
def assignedLit {V L : Type} (vb lit : V) (k : V → V → Expr V L) : Expr V L := qbe {
  %s =l sar %lit, 63
  %x =l xor %lit, %s
  %idx =l sub %x, %s
  %pa =l add %vb, %idx
  %b =l loadsb %pa
  %y =l xor %b, %s
  %val =l sub %y, %s
  ⟨k idx val⟩
}

/-- `inline_assign_literal`: `values[idx] = sign(lit)`, push `lit` on the trail. -/
def assignLit {V L : Type} (vb te sla lit idx : V) (k : V → V → Expr V L) : Expr V L := qbe {
  %s =l sar %lit, 63
  %sg =l or %s, 1
  %pa =l add %vb, %idx
  storeb %sg, %pa
  storew %lit, %te
  %te2 =l add %te, 4
  %sla2 =l add %sla, 1
  ⟨k te2 sla2⟩
}

/-- `flush_prop_state`: write the register-resident state back to the kernel state. -/
def flush {V L : Type} (st te sr sla : V) (k : Expr V L) : Expr V L := qbe {
  %p48 =l add %st, 48
  storel %te, %p48
  %p144 =l add %st, 144
  storel %sr, %p144
  %p152 =l add %st, 152
  storel %sla, %p152
  ⟨k⟩
}

/-- `inline_backtrack`: clear `values[|t|]` for every literal `t` on the trail. -/
def backtrack {V L : Type} (vb tb te : V) (k : Expr V L) : Expr V L := qbe {
  @bt(%t) {
    %c =w ceql %t, %te
    jnz %c, { ⟨k⟩ }, {
      %tlit =l loadsw %t
      %s =l sar %tlit, 63
      %x =l xor %tlit, %s
      %idx =l sub %x, %s
      %pa =l add %vb, %idx
      storeb 0, %pa
      %t2 =l add %t, 4
      jmp @bt(%t2)
    }
  }
  jmp @bt(%tb)
}

/-- Phase 1: assign the negation of every literal of the clause, or find it tautological. -/
def phase1 {V L : Type} (finish phase2 : L) (vb lits te0 sr sla0 : V) : Expr V L := qbe {
  @p1(%l, %te, %sla) {
    %lit =l loadsw %l
    jnz %lit, {
      %idx, %val <- assignedLit(%vb, %lit)
      %l2 =l add %l, 4
      %vneg =w csltl %val, 0
      jnz %vneg, @p1(%l2, %te, %sla), {
        %vpos =w csltl 0, %val
        jnz %vpos, @finish(%te, %sr, %sla), {
          %nlit =l sub 0, %lit
          %te2, %sla2 <- assignLit(%vb, %te, %sla, %nlit, %idx)
          jmp @p1(%l2, %te2, %sla2)
        }
      }
    }, @phase2(%te, %sla)
  }
  jmp @p1(%lits, %te0, %sla0)
}

/-- Phase 2, inner loop: unit propagation over the literals of one antecedent clause. -/
def inner {V L : Type} (fail done : L) (vb aid als te0 sr sla0 : V) : Expr V L := qbe {
  @lp(%l, %unit, %te, %sla) {
    %lit =l loadsw %l
    jnz %lit, {
      %idx, %val <- assignedLit(%vb, %lit)
      %l2 =l add %l, 4
      %vneg =w csltl %val, 0
      jnz %vneg, {
        %nlit =l sub 0, %lit
        %c =w ceql %unit, %nlit
        jnz %c, @fail(2, %aid, %te, %sr, %sla), @lp(%l2, %unit, %te, %sla)
      }, {
        @setunit() {
          %vz =w ceql %val, 0
          jnz %vz, {
            %te2, %sla2 <- assignLit(%vb, %te, %sla, %lit, %idx)
            jmp @lp(%l2, %lit, %te2, %sla2)
          }, @lp(%l2, %lit, %te, %sla)
        }
        jnz %unit, {
          %eq =w ceql %unit, %lit
          jnz %eq, @setunit, @fail(2, %aid, %te, %sr, %sla)
        }, @setunit
      }
    }, @done(%unit, %te, %sla)
  }
  jmp @lp(%als, 0, %te0, %sla0)
}

/-- Phase 2, outer loop: propagate each antecedent until a conflict (success) or the end (failure). -/
def phase2 {V L : Type} (fail finish : L) (lb vb ants te0 sr0 sla0 : V) : Expr V L := qbe {
  @outer(%a, %te, %sr, %sla) {
    %aid =l loadsw %a
    jnz %aid, {
      %neg =w csltl %aid, 0
      jnz %neg, @fail(1, %aid, %te, %sr, %sla), {
        %off =l shl %aid, 3
        %pp =l add %lb, %off
        %als =l loadl %pp
        %sr2 =l add %sr, 1
        @idone(%unit, %te2, %sla2) {
          jnz %unit, {
            %a2 =l add %a, 4
            jmp @outer(%a2, %te2, %sr2, %sla2)
          }, @finish(%te2, %sr2, %sla2)
        }
        ⟨inner fail idone vb aid als te sr2 sla⟩
      }
    }, @fail(3, 0, %te, %sr, %sla)
  }
  jmp @outer(%ants, %te0, %sr0, %sla0)
}

/-- `br_check_clause_non_strictly_by_propagation(st, id, literals, antecedents)`. -/
def checkRup : Func := fun _ _ => qbe(%st, %id, %literals, %antecedents) {
  %p16 =l add %st, 16
  %lb =l loadl %p16
  %p24 =l add %st, 24
  %vb =l loadl %p24
  %p40 =l add %st, 40
  %tb =l loadl %p40
  %p48 =l add %st, 48
  %te0 =l loadl %p48
  %p144 =l add %st, 144
  %sr0 =l loadl %p144
  %sr1 =l add %sr0, 1
  %p152 =l add %st, 152
  %sla0 =l loadl %p152
  @fail(%code, %aid, %te, %sr, %sla) {
    use flush(%st, %te, %sr, %sla)
    exit $lrat_fail(%code, %id, %aid, 0, 0)
  }
  {
    @finish(%te, %sr, %sla) {
      use backtrack(%vb, %tb, %te)
      use flush(%st, %tb, %sr, %sla)
      ret
    }
    {
      @ph2(%te, %sla) {
        ⟨phase2 fail finish lb vb antecedents te sr1 sla⟩
      }
      ⟨phase1 finish ph2 vb literals te0 sr1 sla0⟩
    }
  }
}

end LeanQbe.LratRup
