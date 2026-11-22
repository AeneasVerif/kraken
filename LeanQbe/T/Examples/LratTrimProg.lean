module

public import LeanQbe.T.Notation

/-!
# Pure AST Definitions for `lrat-trim` Kernel (`LratTrimProg`)
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.LratTrim

open LeanQbe.T
/-! ## RUP Propagation (`br_check_clause_non_strictly_by_propagation`) -/

/-- `inline_assigned_literal`: `idx = |lit|`, `val = values[idx]` negated if `lit < 0`. -/
def assignedLit {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (vb lit : V i64) (k : V i64 → V i64 → Expr V L rs) : Expr V L rs := tqbe {
  %s:l = sar %lit, 63
  %x:l = xor %lit, %s
  %idx:l = sub %x, %s
  %pa:l = add %vb, %idx
  %b8:i8 = load %pa
  %b:l = sext %b8
  %y:l = xor %b, %s
  %val:l = sub %y, %s
  ⟨k idx val⟩
}

/-- `inline_assign_literal`: `values[idx] = sign(lit)`, push `lit` onto trail. -/
def assignLit {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (vb te sla lit idx : V i64) (k : V i64 → V i64 → Expr V L rs) : Expr V L rs := tqbe {
  %s:l = sar %lit, 63
  %sg:l = or %s, 1
  %sg8:i8 = trunc %sg
  %pa:l = add %vb, %idx
  store %sg8, %pa
  %lit32:w = trunc %lit
  store %lit32, %te
  %te2:l = add %te, 4
  %sla2:l = add %sla, 1
  ⟨k te2 sla2⟩
}

/-- `flush_prop_state`: write register-resident trail end and stats back to kernel state. -/
def flush {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (st te sr sla : V i64) (k : Expr V L rs) : Expr V L rs := tqbe {
  %p48:l = add %st, 48
  store %te, %p48
  %p144:l = add %st, 144
  store %sr, %p144
  %p152:l = add %st, 152
  store %sla, %p152
  ⟨k⟩
}

/-- `inline_backtrack`: clear `values[|t|]` for every literal `t` on `[tb, te)`. -/
def backtrack {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (vb tb te : V i64) (k : Expr V L rs) : Expr V L rs := tqbe {
  @bt(%t:l) {
    %c:b = ceql %t, %te
    jnz %c, { ⟨k⟩ }, {
      %tlit32:w = load %t
      %tlit:l = sext %tlit32
      %s:l = sar %tlit, 63
      %x:l = xor %tlit, %s
      %idx:l = sub %x, %s
      %pa:l = add %vb, %idx
      store 0:i8, %pa
      %t2:l = add %t, 4
      jmp @bt(%t2)
    }
  }
  jmp @bt(%tb)
}

/-- Phase 1: assign negation of every clause literal, or jump to `finish` if tautological. -/
def rupPhase1 {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (finish : L [i64, i64, i64]) (phase2 : L [i64, i64])
    (vb lits te0 sr sla0 : V i64) : Expr V L rs := tqbe {
  @p1(%l:l, %te:l, %sla:l) {
    %lit32:w = load %l
    %lit_nz:b = cnew %lit32, 0
    jnz %lit_nz, {
      %lit:l = sext %lit32
      %idx:l, %val:l <- assignedLit(%vb, %lit)
      %l2:l = add %l, 4
      %vneg:b = csltl %val, 0
      jnz %vneg, @p1(%l2, %te, %sla), {
        %vpos:b = csltl 0, %val
        jnz %vpos, @finish(%te, %sr, %sla), {
          %nlit:l = sub 0, %lit
          %te2:l, %sla2:l <- assignLit(%vb, %te, %sla, %nlit, %idx)
          jmp @p1(%l2, %te2, %sla2)
        }
      }
    }, @phase2(%te, %sla)
  }
  jmp @p1(%lits, %te0, %sla0)
}

/-- Phase 2 inner loop: unit propagation over literals of one antecedent clause. -/
def rupInner {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (fail : L [i64, i64, i64, i64, i64]) (done : L [i64, i64, i64])
    (vb aid als te0 sr sla0 : V i64) : Expr V L rs := tqbe {
  @lp(%l:l, %unit:l, %te:l, %sla:l) {
    %lit32:w = load %l
    %lit_nz:b = cnew %lit32, 0
    jnz %lit_nz, {
      %lit:l = sext %lit32
      %idx:l, %val:l <- assignedLit(%vb, %lit)
      %l2:l = add %l, 4
      %vneg:b = csltl %val, 0
      jnz %vneg, {
        %nlit:l = sub 0, %lit
        %c:b = ceql %unit, %nlit
        jnz %c, @fail(2, %aid, %te, %sr, %sla), @lp(%l2, %unit, %te, %sla)
      }, {
        @setunit() {
          %vz:b = ceql %val, 0
          jnz %vz, {
            %te2:l, %sla2:l <- assignLit(%vb, %te, %sla, %lit, %idx)
            jmp @lp(%l2, %lit, %te2, %sla2)
          }, @lp(%l2, %lit, %te, %sla)
        }
        %unit_nz:b = cnel %unit, 0
        jnz %unit_nz, {
          %eq:b = ceql %unit, %lit
          jnz %eq, @setunit, @fail(2, %aid, %te, %sr, %sla)
        }, @setunit
      }
    }, @done(%unit, %te, %sla)
  }
  jmp @lp(%als, 0, %te0, %sla0)
}

/-- Phase 2 outer loop: propagate each antecedent until conflict (`finish`) or error (`fail`). -/
def rupPhase2 {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (fail : L [i64, i64, i64, i64, i64]) (finish : L [i64, i64, i64])
    (lb vb ants te0 sr0 sla0 : V i64) : Expr V L rs := tqbe {
  @outer(%a:l, %te:l, %sr:l, %sla:l) {
    %aid32:w = load %a
    %aid_nz:b = cnew %aid32, 0
    jnz %aid_nz, {
      %aid:l = sext %aid32
      %neg:b = csltl %aid, 0
      jnz %neg, @fail(1, %aid, %te, %sr, %sla), {
        %off:l = shl %aid, 3
        %pp:l = add %lb, %off
        %als:l = load %pp
        %sr2:l = add %sr, 1
        @idone(%unit:l, %te2:l, %sla2:l) {
          %unit_nz:b = cnel %unit, 0
          jnz %unit_nz, {
            %a2:l = add %a, 4
            jmp @outer(%a2, %te2, %sr2, %sla2)
          }, @finish(%te2, %sr2, %sla2)
        }
        ⟨rupInner fail idone vb aid als te sr2 sla⟩
      }
    }, @fail(3, 0, %te, %sr, %sla)
  }
  jmp @outer(%ants, %te0, %sr0, %sla0)
}

/-- `br_check_clause_non_strictly_by_propagation(st, id, literals, antecedents)`. -/
def checkRup : Func [i64, i64, i64, i64] [] :=
  tqbe(%st:l, %id:l, %literals:l, %antecedents:l) -> () {
    %p16:l = add %st, 16
    %lb:l = load %p16
    %p24:l = add %st, 24
    %vb:l = load %p24
    %p40:l = add %st, 40
    %tb:l = load %p40
    %p48:l = add %st, 48
    %te0:l = load %p48
    %p144:l = add %st, 144
    %sr0:l = load %p144
    %sr1:l = add %sr0, 1
    %p152:l = add %st, 152
    %sla0:l = load %p152
    @fail(%code:l, %aid:l, %te:l, %sr:l, %sla:l) {
      use flush(%st, %te, %sr, %sla)
      exit $lrat_fail(%code, %id, %aid, 0:l, 0:l)
    }
    {
      @finish(%te:l, %sr:l, %sla:l) {
        use backtrack(%vb, %tb, %te)
        use flush(%st, %tb, %sr, %sla)
        ret
      }
      {
        @ph2(%te:l, %sla:l) {
          ⟨rupPhase2 fail finish lb vb antecedents te sr1 sla⟩
        }
        ⟨rupPhase1 finish ph2 vb literals te0 sr1 sla0⟩
      }
    }
  }

/-! ## Strict Resolution Check (`br_check_clause_strictly_by_resolution`) -/

/-- Loop 1: every antecedent id must be positive; finds the `0` terminator. -/
def strictScan {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (id : V i64) (scanned : L [i64]) (ants : V i64) : Expr V L rs := tqbe {
  @scan(%a:l) {
    %aid32:w = load %a
    %aid_nz:b = cnew %aid32, 0
    jnz %aid_nz, {
      %aid:l = sext %aid32
      %neg:b = csltl %aid, 0
      jnz %neg, { exit $lrat_fail(1:l, %id, %aid, 0:l, 0:l) }, {
        %a2:l = add %a, 4
        jmp @scan(%a2)
      }
    }, @scanned(%a)
  }
  jmp @scan(%ants)
}

/-- Loop 2 inner: resolve the literals of one antecedent into the marks array. -/
def strictInner {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (st id aid mb sr : V i64) (done : L [i64, i64]) (als rsize0 : V i64) : Expr V L rs := tqbe {
  @lp(%l:l, %unit:l, %rsize:l) {
    %lit32:w = load %l
    %lit_nz:b = cnew %lit32, 0
    jnz %lit_nz, {
      %lit:l = sext %lit32
      %s:l = sar %lit, 63
      %x:l = xor %lit, %s
      %idx:l = sub %x, %s
      %m:l = add %mb, %idx
      %mark8:i8 = load %m
      %mark:l = sext %mark8
      %l2:l = add %l, 4
      %mz:b = ceql %mark, 0
      jnz %mz, {
        %sg:l = or %s, 1
        %sg8:i8 = trunc %sg
        store %sg8, %m
        %r2:l = add %rsize, 1
        jmp @lp(%l2, %unit, %r2)
      }, {
        %y:l = xor %mark, %s
        %mk:l = sub %y, %s
        %pos:b = csltl 0, %mk
        jnz %pos, @lp(%l2, %unit, %rsize), {
          %unit_nz:b = cnel %unit, 0
          jnz %unit_nz, {
            %p144:l = add %st, 144
            store %sr, %p144
            exit $lrat_fail(4:l, %id, %unit, %lit, %aid)
          }, @lp(%l2, %lit, %rsize)
        }
      }
    }, @done(%unit, %rsize)
  }
  jmp @lp(%als, 0, %rsize0)
}

/-- Loop 2 outer: resolve antecedents from last to first. -/
def strictOuter {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (st id lb mb ants : V i64) (resolved : L [i64, i64, Ty.bool])
    (a0 sr0 : V i64) : Expr V L rs := tqbe {
  @outer(%a:l, %sr:l, %rsize:l, %first:b) {
    %c:b = ceql %a, %ants
    jnz %c, @resolved(%sr, %rsize, %first), {
      %a2:l = sub %a, 4
      %aid32:w = load %a2
      %aid:l = sext %aid32
      %off:l = shl %aid, 3
      %pp:l = add %lb, %off
      %als:l = load %pp
      %sr2:l = add %sr, 1
      @idone(%unit:l, %rsize2:l) {
        %unit_nz:b = cnel %unit, 0
        jnz %first, {
          jnz %unit_nz, {
            %p144:l = add %st, 144
            store %sr2, %p144
            %nu:l = sub 0, %unit
            exit $lrat_fail(4:l, %id, %nu, %unit, %aid)
          }, @outer(%a2, %sr2, %rsize2, false)
        }, {
          jnz %unit_nz, {
            %s:l = sar %unit, 63
            %x:l = xor %unit, %s
            %idx:l = sub %x, %s
            %m:l = add %mb, %idx
            store 0:i8, %m
            %r3:l = sub %rsize2, 1
            jmp @outer(%a2, %sr2, %r3, %first)
          }, {
            %p144:l = add %st, 144
            store %sr2, %p144
            exit $lrat_fail(5:l, %id, %aid, 0:l, 0:l)
          }
        }
      }
      ⟨strictInner st id aid mb sr2 idone als rsize⟩
    }
  }
  jmp @outer(%a0, %sr0, 0, true)
}

/-- Loop 3: verify the resolvent matches `lits` and clear marks. -/
def strictFinal {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (id mb : V i64) (checked : L [i64]) (lits rsize0 : V i64) : Expr V L rs := tqbe {
  @l3(%l:l, %rsize:l) {
    %lit32:w = load %l
    %lit_nz:b = cnew %lit32, 0
    jnz %lit_nz, {
      %lit:l = sext %lit32
      %s:l = sar %lit, 63
      %x:l = xor %lit, %s
      %idx:l = sub %x, %s
      %m:l = add %mb, %idx
      %mark8:i8 = load %m
      %mark:l = sext %mark8
      %mz:b = ceql %mark, 0
      jnz %mz, { exit $lrat_fail(6:l, %id, %lit, 0:l, 0:l) }, {
        %y:l = xor %mark, %s
        %mk:l = sub %y, %s
        %neg:b = csltl %mk, 0
        jnz %neg, { exit $lrat_fail(7:l, %id, %lit, 0:l, 0:l) }, {
          store 0:i8, %m
          %r2:l = sub %rsize, 1
          %l2:l = add %l, 4
          jmp @l3(%l2, %r2)
        }
      }
    }, @checked(%rsize)
  }
  jmp @l3(%lits, %rsize0)
}

/-- `br_check_clause_strictly_by_resolution(st, id, literals, antecedents)`. -/
def strictCheck : Func [i64, i64, i64, i64] [] :=
  tqbe(%st:l, %id:l, %literals:l, %antecedents:l) -> () {
    @scanned(%aend:l) {
      %p16:l = add %st, 16
      %lb:l = load %p16
      %p32:l = add %st, 32
      %mb:l = load %p32
      %p144:l = add %st, 144
      %sr0:l = load %p144
      @resolved(%sr:l, %rsize:l, %first:b) {
        store %sr, %p144
        jnz %first, { exit $lrat_fail(3:l, %id, 0:l, 0:l, 0:l) }, {
          @checked(%rs:l) {
            %nz:b = cnel %rs, 0
            jnz %nz, { exit $lrat_fail(8:l, %id, %rs, 0:l, 0:l) }, { ret }
          }
          ⟨strictFinal id mb checked literals rsize⟩
        }
      }
      ⟨strictOuter st id lb mb antecedents resolved aend sr0⟩
    }
    ⟨strictScan id scanned antecedents⟩
  }

/-! ## `br_check_clause` and `br_check_proof` -/

/-- `br_check_clause(st, id, literals, antecedents)`: count the check, then dispatch. -/
def checkClause : Func [i64, i64, i64, i64] [] :=
  tqbe(%st:l, %id:l, %literals:l, %antecedents:l) -> () {
    %p128:l = add %st, 128
    %t:l = load %p128
    %t1:l = add %t, 1
    store %t1, %p128
    %l0_32:w = load %literals
    @cont() {
      %p80:l = add %st, 80
      %strict:l = load %p80
      %sc:b = cnel %strict, 0
      jnz %sc, {
        call $br_check_clause_strictly_by_resolution(%st, %id, %literals, %antecedents)
        ret
      }, {
        call $br_check_clause_non_strictly_by_propagation(%st, %id, %literals, %antecedents)
        ret
      }
    }
    %e:b = ceqw %l0_32, 0
    jnz %e, {
      %p136:l = add %st, 136
      %c:l = load %p136
      %c1:l = add %c, 1
      store %c1, %p136
      jmp @cont
    }, @cont
  }

/-- `br_check_proof(st)`: check every used proof step from `first_proof_id` to `empty_clause`. -/
def checkProof : Func [i64] [] :=
  tqbe(%st:l) -> () {
    %p96:l = add %st, 96
    %checking:l = load %p96
    %p104:l = add %st, 104
    %forward:l = load %p104
    %p64:l = add %st, 64
    %empty32:w = load %p64
    %empty:l = sext %empty32
    %empty_nz:b = cnew %empty32, 0
    %p72:l = add %st, 72
    %fst32:w = load %p72
    %fst:l = sext %fst32
    %fst_nz:b = cnew %fst32, 0
    %c1:b = cnel %checking, 0
    jnz %c1, {
      %c2:b = ceql %forward, 0
      jnz %c2, {
        jnz %empty_nz, {
          jnz %fst_nz, {
            %p88:l = add %st, 88
            %trimming:l = load %p88
            %ub:l = load %st
            %p16:l = add %st, 16
            %lb:l = load %p16
            %p8:l = add %st, 8
            %ab:l = load %p8
            @loop(%id:l) {
              %gt:b = csltl %empty, %id
              jnz %gt, { ret }, {
                @next() {
                  %id2:l = add %id, 1
                  jmp @loop(%id2)
                }
                {
                  @check(%used:b) {
                    jnz %used, {
                      %o8:l = shl %id, 3
                      %pl:l = add %lb, %o8
                      %l:l = load %pl
                      %pa:l = add %ab, %o8
                      %a:l = load %pa
                      call $br_check_clause(%st, %id, %l, %a)
                      jmp @next
                    }, @next
                  }
                  %tz:b = cnel %trimming, 0
                  jnz %tz, {
                    %o4:l = shl %id, 2
                    %pu:l = add %ub, %o4
                    %u32:w = load %pu
                    %u_nz:b = cnew %u32, 0
                    jmp @check(%u_nz)
                  }, @check(true)
                }
              }
            }
            jmp @loop(%fst)
          }, { ret }
        }, { ret }
      }, { ret }
    }, { ret }
  }

/-! ## `br_trim_proof` -/

/-- `inline_mark_used(id, used_where)`: returns `(was_used, is_orig, tcnf, tprf)`. -/
def markUsed {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (ub fst id usedWhere tcnf tprf : V i64)
    (k : V Ty.bool → V Ty.bool → V i64 → V i64 → Expr V L rs) : Expr V L rs := tqbe {
  %o:l = shl %id, 2
  %w:l = add %ub, %o
  %before32:w = load %w
  %before:l = sext %before32
  %before_nz:b = cnew %before32, 0
  @mdone(%wu:b, %io:b, %c:l, %p:l) {
    ⟨k wu io c p⟩
  }
  {
    %lt:b = csltl %before, %usedWhere
    jnz %lt, {
      %uw32:w = trunc %usedWhere
      store %uw32, %w
      jnz %before_nz, @mdone(true, false, %tcnf, %tprf), {
        %z:b = ceql %fst, 0
        %lt2:b = csltl %id, %fst
        %orig:b = or %z, %lt2
        jnz %orig, {
          %c1:l = add %tcnf, 1
          jmp @mdone(false, %orig, %c1, %tprf)
        }, {
          %p1:l = add %tprf, 1
          jmp @mdone(false, %orig, %tcnf, %p1)
        }
      }
    }, @mdone(true, false, %tcnf, %tprf)
  }
}

/-- Inner loop of `br_trim_proof`: mark every antecedent of step `id`, pushing newly used proof
steps onto the worklist. -/
def trimInner {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (ub fst id : V i64) (done : L [i64, i64, i64])
    (p0 we0 tc0 tp0 : V i64) : Expr V L rs := tqbe {
  @ip(%p:l, %we:l, %tc:l, %tp:l) {
    %raw32:w = load %p
    %raw:l = sext %raw32
    %s:l = sar %raw, 63
    %x:l = xor %raw, %s
    %other:l = sub %x, %s
    %other_nz:b = cnel %other, 0
    jnz %other_nz, {
      %wu:b, %io:b, %tc2:l, %tp2:l <- markUsed(%ub, %fst, %other, %id, %tc, %tp)
      %p2:l = add %p, 4
      @nx(%we2:l) {
        jmp @ip(%p2, %we2, %tc2, %tp2)
      }
      {
        jnz %wu, @nx(%we), {
          jnz %io, @nx(%we), {
            %other32:w = trunc %other
            store %other32, %we
            %we3:l = add %we, 4
            jmp @nx(%we3)
          }
        }
      }
    }, @done(%we, %tc, %tp)
  }
  jmp @ip(%p0, %we0, %tc0, %tp0)
}

/-- `br_trim_proof(st)`: mark all proof steps that the empty clause depends on. -/
def trimProof : Func [i64] [] :=
  tqbe(%st:l) -> () {
    %p88:l = add %st, 88
    %trimming:l = load %p88
    %t:b = cnel %trimming, 0
    jnz %t, {
      %p64:l = add %st, 64
      %empty32:w = load %p64
      %empty:l = sext %empty32
      %empty_nz:b = cnew %empty32, 0
      jnz %empty_nz, {
        %ub:l = load %st
        %p8:l = add %st, 8
        %ab:l = load %p8
        %p56:l = add %st, 56
        %wb:l = load %p56
        %p72:l = add %st, 72
        %fst32:w = load %p72
        %fst:l = sext %fst32
        %p112:l = add %st, 112
        %tcnf0:l = load %p112
        %p120:l = add %st, 120
        %tprf0:l = load %p120
        %wu0:b, %io0:b, %tc1:l, %tp1:l <- markUsed(%ub, %fst, %empty, %empty, %tcnf0, %tprf0)
        @work(%we0:l) {
          @fin(%tc:l, %tp:l) {
            store %tc, %p112
            store %tp, %p120
            ret
          }
          {
            @wl(%we:l, %tc:l, %tp:l) {
              %done:b = ceql %we, %wb
              jnz %done, @fin(%tc, %tp), {
                %we2:l = sub %we, 4
                %id32:w = load %we2
                %id:l = sext %id32
                %o8:l = shl %id, 3
                %pp:l = add %ab, %o8
                %p:l = load %pp
                @idone(%we3:l, %tc3:l, %tp3:l) {
                  jmp @wl(%we3, %tc3, %tp3)
                }
                ⟨trimInner ub fst id idone p we2 tc tp⟩
              }
            }
            jmp @wl(%we0, %tc1, %tp1)
          }
        }
        %z:b = ceql %fst, 0
        %lt:b = csltl %empty, %fst
        %orig:b = or %z, %lt
        jnz %orig, @work(%wb), {
          store %empty32, %wb
          %we1:l = add %wb, 4
          jmp @work(%we1)
        }
      }, { ret }
    }, { ret }
  }

/-! ## Module Export -/

/-- The `lrat-trim` kernel functions in callee-first order, matching C symbol names. -/
def lratTrimFns : List Fn :=
  [ { name := "br_check_clause_non_strictly_by_propagation",
      as := [i64, i64, i64, i64], rs := [], body := checkRup }
  , { name := "br_check_clause_strictly_by_resolution",
      as := [i64, i64, i64, i64], rs := [], body := strictCheck }
  , { name := "br_check_clause", as := [i64, i64, i64, i64], rs := [], body := checkClause }
  , { name := "br_check_proof", as := [i64], rs := [], body := checkProof }
  , { name := "br_trim_proof", as := [i64], rs := [], body := trimProof }
  ]

end LeanQbe.T.Examples.LratTrim
