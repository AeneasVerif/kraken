module

public import LeanQbe.Notation
public import LeanQbe.Examples.LratRup
public import Kraken.Bedrock2.Test.LratTrimCheckProof

/-!
# The rest of the lrat-trim kernel, in QBE notation

Ports of the remaining functions of Kraken's `Kraken/Bedrock2/Test/LratTrim.lean`:

| Bedrock2 | here |
|---|---|
| `br_check_clause_strictly_by_resolution` | `strictCheck` (`strictScan`, `strictOuter`, `strictInner`, `strictFinal`) |
| `br_check_clause` | `checkClause` (calls one of the two checks) |
| `br_check_proof` | `checkProof` (calls `br_check_clause` per used proof step) |
| `br_trim_proof`, `inline_mark_used` | `trimProof`, `markUsed`, `trimInner` |
| `br_check_clause_non_strictly_by_propagation` | `LratRup.checkRup` |

The translation follows `LratRup.lean`. Mutable locals become join-point parameters, flags that only
exit a loop become jumps, `x .< 0 ? -x : x` is `(x xor s) - s` with `s = x sar 63`, and
`(load4 p << 32) .>> 32` is `loadsw`. `interact lrat_fail(…)` becomes `exit $lrat_fail(…)`.

A 64-bit field or counter used as a condition is compared with `cnel x, 0` first, because QBE's `jnz`
tests only the low 32 bits. Values that are sign-extended 32-bit (literals, clause ids, `loadsw`
results) and 0/1 flags are used directly.

Functions are called by their C names, so that the compiled module links with the C harness and with
`lrat_fail`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.LratTrim

/-! ## `br_check_clause_strictly_by_resolution` -/

/-- Loop 1: every antecedent id must be positive; ends at the 0 terminator. -/
def strictScan {V L : Type} (id : V) (scanned : L) (ants : V) : Expr V L := qbe {
  @scan(%a) {
    %aid =l loadsw %a
    jnz %aid, {
      %neg =w csltl %aid, 0
      jnz %neg, { exit $lrat_fail(1, %id, %aid, 0, 0) }, {
        %a2 =l add %a, 4
        jmp @scan(%a2)
      }
    }, @scanned(%a)
  }
  jmp @scan(%ants)
}

/-- Loop 2, inner: resolve the literals of one antecedent into the marks array. -/
def strictInner {V L : Type} (st id aid mb sr : V) (done : L) (als rsize0 : V) : Expr V L := qbe {
  @lp(%l, %unit, %rsize) {
    %lit =l loadsw %l
    jnz %lit, {
      %s =l sar %lit, 63
      %x =l xor %lit, %s
      %idx =l sub %x, %s
      %m =l add %mb, %idx
      %mark =l loadsb %m
      %l2 =l add %l, 4
      %mz =w ceql %mark, 0
      jnz %mz, {
        %sg =l or %s, 1
        storeb %sg, %m
        %r2 =l add %rsize, 1
        jmp @lp(%l2, %unit, %r2)
      }, {
        %y =l xor %mark, %s
        %mk =l sub %y, %s
        %pos =w csltl 0, %mk
        jnz %pos, @lp(%l2, %unit, %rsize), {
          jnz %unit, {
            %p144 =l add %st, 144
            storel %sr, %p144
            exit $lrat_fail(4, %id, %unit, %lit, %aid)
          }, @lp(%l2, %lit, %rsize)
        }
      }
    }, @done(%unit, %rsize)
  }
  jmp @lp(%als, 0, %rsize0)
}

/-- Loop 2, outer: the antecedents from last to first; the first one resolved must have no
clashing literal, every later one exactly one. -/
def strictOuter {V L : Type} (st id lb mb ants : V) (resolved : L) (a0 sr0 : V) : Expr V L := qbe {
  @outer(%a, %sr, %rsize, %first) {
    %c =w ceql %a, %ants
    jnz %c, @resolved(%sr, %rsize, %first), {
      %a2 =l sub %a, 4
      %aid =l loadsw %a2
      %off =l shl %aid, 3
      %pp =l add %lb, %off
      %als =l loadl %pp
      %sr2 =l add %sr, 1
      @idone(%unit, %rsize2) {
        jnz %first, {
          jnz %unit, {
            %p144 =l add %st, 144
            storel %sr2, %p144
            %nu =l sub 0, %unit
            exit $lrat_fail(4, %id, %nu, %unit, %aid)
          }, @outer(%a2, %sr2, %rsize2, 0)
        }, {
          jnz %unit, {
            %s =l sar %unit, 63
            %x =l xor %unit, %s
            %idx =l sub %x, %s
            %m =l add %mb, %idx
            storeb 0, %m
            %r3 =l sub %rsize2, 1
            jmp @outer(%a2, %sr2, %r3, %first)
          }, {
            %p144 =l add %st, 144
            storel %sr2, %p144
            exit $lrat_fail(5, %id, %aid, 0, 0)
          }
        }
      }
      ⟨strictInner st id aid mb sr2 idone als rsize⟩
    }
  }
  jmp @outer(%a0, %sr0, 0, 1)
}

/-- Loop 3: the resolvent must be exactly the clause; clears the marks. -/
def strictFinal {V L : Type} (id mb : V) (checked : L) (lits rsize0 : V) : Expr V L := qbe {
  @l3(%l, %rsize) {
    %lit =l loadsw %l
    jnz %lit, {
      %s =l sar %lit, 63
      %x =l xor %lit, %s
      %idx =l sub %x, %s
      %m =l add %mb, %idx
      %mark =l loadsb %m
      %mz =w ceql %mark, 0
      jnz %mz, { exit $lrat_fail(6, %id, %lit, 0, 0) }, {
        %y =l xor %mark, %s
        %mk =l sub %y, %s
        %neg =w csltl %mk, 0
        jnz %neg, { exit $lrat_fail(7, %id, %lit, 0, 0) }, {
          storeb 0, %m
          %r2 =l sub %rsize, 1
          %l2 =l add %l, 4
          jmp @l3(%l2, %r2)
        }
      }
    }, @checked(%rsize)
  }
  jmp @l3(%lits, %rsize0)
}

/-- `br_check_clause_strictly_by_resolution(st, id, literals, antecedents)`. -/
def strictCheck : Func := fun _ _ => qbe(%st, %id, %literals, %antecedents) {
  @scanned(%aend) {
    %p16 =l add %st, 16
    %lb =l loadl %p16
    %p32 =l add %st, 32
    %mb =l loadl %p32
    %p144 =l add %st, 144
    %sr0 =l loadl %p144
    @resolved(%sr, %rsize, %first) {
      storel %sr, %p144
      jnz %first, { exit $lrat_fail(3, %id, 0, 0, 0) }, {
        @checked(%rs) {
          %nz =w cnel %rs, 0
          jnz %nz, { exit $lrat_fail(8, %id, %rs, 0, 0) }, { ret }
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
def checkClause : Func := fun _ _ => qbe(%st, %id, %literals, %antecedents) {
  %p128 =l add %st, 128
  %t =l loadl %p128
  %t1 =l add %t, 1
  storel %t1, %p128
  %l0 =l loaduw %literals
  @cont() {
    %p80 =l add %st, 80
    %strict =l loadl %p80
    %sc =w cnel %strict, 0
    jnz %sc, {
      call $br_check_clause_strictly_by_resolution(%st, %id, %literals, %antecedents)
      ret
    }, {
      call $br_check_clause_non_strictly_by_propagation(%st, %id, %literals, %antecedents)
      ret
    }
  }
  %e =w ceql %l0, 0
  jnz %e, {
    %p136 =l add %st, 136
    %c =l loadl %p136
    %c1 =l add %c, 1
    storel %c1, %p136
    jmp @cont
  }, @cont
}

/-- `br_check_proof(st)`: check every used proof step from `first_proof_id` to `empty_clause`. -/
def checkProof : Func := fun _ _ => qbe(%st) {
  %p96 =l add %st, 96
  %checking =l loadl %p96
  %p104 =l add %st, 104
  %forward =l loadl %p104
  %p64 =l add %st, 64
  %empty =l loadsw %p64
  %p72 =l add %st, 72
  %fst =l loadsw %p72
  %c1 =w cnel %checking, 0
  jnz %c1, {
    %c2 =w ceql %forward, 0
    jnz %c2, {
      jnz %empty, {
        jnz %fst, {
          %p88 =l add %st, 88
          %trimming =l loadl %p88
          %ub =l loadl %st
          %p16 =l add %st, 16
          %lb =l loadl %p16
          %p8 =l add %st, 8
          %ab =l loadl %p8
          @loop(%id) {
            %gt =w csltl %empty, %id
            jnz %gt, { ret }, {
              @next() {
                %id2 =l add %id, 1
                jmp @loop(%id2)
              }
              {
                @check(%used) {
                  jnz %used, {
                    %o8 =l shl %id, 3
                    %pl =l add %lb, %o8
                    %l =l loadl %pl
                    %pa =l add %ab, %o8
                    %a =l loadl %pa
                    call $br_check_clause(%st, %id, %l, %a)
                    jmp @next
                  }, @next
                }
                %tz =w cnel %trimming, 0
                jnz %tz, {
                  %o4 =l shl %id, 2
                  %pu =l add %ub, %o4
                  %u =l loadsw %pu
                  jmp @check(%u)
                }, @check(-1)
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

/-- `inline_mark_used(id, used_where)`: returns `was_used`, `is_orig` and the two counters. -/
def markUsed {V L : Type} (ub fst id usedWhere tcnf tprf : V) (k : V → V → V → V → Expr V L) :
    Expr V L := qbe {
  %o =l shl %id, 2
  %w =l add %ub, %o
  %before =l loadsw %w
  @mdone(%wu, %io, %c, %p) {
    ⟨k wu io c p⟩
  }
  {
    %lt =w csltl %before, %usedWhere
    jnz %lt, {
      storew %usedWhere, %w
      jnz %before, @mdone(1, 0, %tcnf, %tprf), {
        %z =w ceql %fst, 0
        %lt2 =w csltl %id, %fst
        %orig =w or %z, %lt2
        jnz %orig, {
          %c1 =l add %tcnf, 1
          jmp @mdone(0, %orig, %c1, %tprf)
        }, {
          %p1 =l add %tprf, 1
          jmp @mdone(0, %orig, %tcnf, %p1)
        }
      }
    }, @mdone(1, 0, %tcnf, %tprf)
  }
}

/-- The inner loop of `br_trim_proof`: mark every antecedent of step `id`, pushing the newly used
proof steps on the work list. -/
def trimInner {V L : Type} (ub fst id : V) (done : L) (p0 we0 tc0 tp0 : V) : Expr V L := qbe {
  @ip(%p, %we, %tc, %tp) {
    %raw =l loadsw %p
    %s =l sar %raw, 63
    %x =l xor %raw, %s
    %other =l sub %x, %s
    jnz %other, {
      %wu, %io, %tc2, %tp2 <- markUsed(%ub, %fst, %other, %id, %tc, %tp)
      %p2 =l add %p, 4
      @nx(%we2) {
        jmp @ip(%p2, %we2, %tc2, %tp2)
      }
      {
        jnz %wu, @nx(%we), {
          jnz %io, @nx(%we), {
            storew %other, %we
            %we3 =l add %we, 4
            jmp @nx(%we3)
          }
        }
      }
    }, @done(%we, %tc, %tp)
  }
  jmp @ip(%p0, %we0, %tc0, %tp0)
}

/-- `br_trim_proof(st)`: mark the proof steps the empty clause depends on. -/
def trimProof : Func := fun _ _ => qbe(%st) {
  %p88 =l add %st, 88
  %trimming =l loadl %p88
  %t =w cnel %trimming, 0
  jnz %t, {
    %p64 =l add %st, 64
    %empty =l loadsw %p64
    jnz %empty, {
      %ub =l loadl %st
      %p8 =l add %st, 8
      %ab =l loadl %p8
      %p56 =l add %st, 56
      %wb =l loadl %p56
      %p72 =l add %st, 72
      %fst =l loadsw %p72
      %p112 =l add %st, 112
      %tcnf0 =l loadl %p112
      %p120 =l add %st, 120
      %tprf0 =l loadl %p120
      %wu0, %io0, %tc1, %tp1 <- markUsed(%ub, %fst, %empty, %empty, %tcnf0, %tprf0)
      @start(%we0) {
        @fin(%tc, %tp) {
          storel %tc, %p112
          storel %tp, %p120
          ret
        }
        {
          @wl(%we, %tc, %tp) {
            %done =w ceql %we, %wb
            jnz %done, @fin(%tc, %tp), {
              %we2 =l sub %we, 4
              %id =l loadsw %we2
              %o8 =l shl %id, 3
              %pp =l add %ab, %o8
              %p =l loadl %pp
              @idone(%we3, %tc3, %tp3) {
                jmp @wl(%we3, %tc3, %tp3)
              }
              ⟨trimInner ub fst id idone p we2 tc tp⟩
            }
          }
          jmp @wl(%we0, %tc1, %tp1)
        }
      }
      %z =w ceql %fst, 0
      %lt =w csltl %empty, %fst
      %orig =w or %z, %lt
      jnz %orig, @start(%wb), {
        storew %empty, %wb
        %we1 =l add %wb, 4
        jmp @start(%we1)
      }
    }, { ret }
  }, { ret }
}

/-- The kernel as named functions, as QBE's `function $name(...)` definitions. -/
def lratTrimFns : List Fn :=
  [⟨"br_check_clause_non_strictly_by_propagation", LratRup.checkRup⟩,
   ⟨"br_check_clause_strictly_by_resolution", strictCheck⟩,
   ⟨"br_check_clause", checkClause⟩,
   ⟨"br_check_proof", checkProof⟩,
   ⟨"br_trim_proof", trimProof⟩]

/-! ## Contracts

Each contract is the corresponding Kraken theorem turned into a `Spec`, over the imported Bedrock2
model. The theorem's hypotheses become the caller's `∃ … ∧`, its `post` becomes the return
postcondition, and `lratFailExt` becomes "the exit postcondition accepts every exit to `lrat_fail`".
The Bedrock2 `e.lookup f = some …` hypotheses for callees become hypotheses on `Γ` in the correctness
theorems.
-/

open Std.Sat Std.Tactic.BVDecide.LRAT.Internal Kraken.Bedrock2.Test

/-- `call_br_check_clause_strictly_by_resolution` (`LratTrimStrictProof.lean`). -/
def strictSpec : Spec := fun args m Q X =>
  ∃ (st id lits_ptr ant_ptr : Val) (max_var n : Nat) (f : CNF Nat) (k : KernelFields)
    (clause_lits ants : List Val) (R_ro : Mem 64 → Prop),
    args = [st, id, lits_ptr, ant_ptr] ∧
    max_var < n ∧ n < 2 ^ 64 ∧ 4 * ants.length < 2 ^ 64 ∧
    (∀ x ∈ ants, IsInt32 x ∧ x ≠ 0) ∧
    (∀ aid ∈ ants, aid.slt 0 = false → ValidAntecedent max_var f k.literals_begin R_ro aid) ∧
    (∀ x ∈ clause_lits, IsValidLit max_var x) ∧
    (byte1Array k.marks_begin (List.replicate n 0) ⋆ (kernelState st k ⋆ R_ro)) m ∧
    (∃ R', R_ro = (ZeroTermInts ant_ptr ants ⋆ R')) ∧
    (∃ R', R_ro = (ZeroTermInts lits_ptr clause_lits ⋆ R')) ∧
    (CNF.EntailsClause f (toClause clause_lits) → ∀ m',
      (byte1Array k.marks_begin (List.replicate n 0) ⋆
        (kernelState st { k with stat_resolved := k.stat_resolved + BitVec.ofNat 64 ants.length } ⋆
          R_ro)) m' → Q [] m') ∧
    (∀ as m', X "lrat_fail" as m')

/-- `call_br_check_clause_rup` (`LratTrimCheckProof.lean`): `br_check_clause` with `strict = 0`. -/
def checkClauseRupSpec : Spec := fun args m Q X =>
  ∃ (st id literals antecedents : Val) (max_var : Nat) (k : KernelFields)
    (lits aids lit_ptrs trail_free0 : List Val) (s : State) (P_ro : Mem 64 → Prop),
    args = [st, id, literals, antecedents] ∧
    k.strict = 0 ∧
    k.trail_end = k.trail_begin ∧
    ClauseTable max_var k.literals_begin lit_ptrs s.formula P_ro ∧
    (∃ R_lits, P_ro = (ZeroTermInts literals lits ⋆ R_lits)) ∧
    (∃ R_aids, P_ro = (ZeroTermInts antecedents aids ⋆ R_aids)) ∧
    (∀ x ∈ lits, IsValidLit max_var x) ∧
    (∀ aid ∈ aids, IsInt32 aid ∧ aid ≠ 0 ∧
      (aid.slt 0 = false → ∃ h : aid.toNat < lit_ptrs.length, lit_ptrs[aid.toNat] ≠ 0)) ∧
    lits.length + aids.length ≤ trail_free0.length ∧
    4 * trail_free0.length < 2 ^ 64 ∧
    ((byte1Array k.values_begin (assignBytes max_var Assignment.empty) ⋆
        int4Array k.trail_begin trail_free0) ⋆ (kernelState st k ⋆ P_ro)) m ∧
    (∀ m' (stat_resolved stat_lit_assigned : Val) (trail_all : List Val),
      trail_all.length = trail_free0.length →
      ((byte1Array k.values_begin (assignBytes max_var Assignment.empty) ⋆
          int4Array k.trail_begin trail_all) ⋆
        (kernelState st
          { (k.bumpCheckStats ((lits ++ [0])[0]'(by simp))) with
            trail_end := k.trail_begin, stat_resolved, stat_lit_assigned } ⋆ P_ro)) m' →
      CNF.EntailsClause s.toCNF (toClause lits) → Q [] m') ∧
    (∀ as m', X "lrat_fail" as m')

/-- `call_br_check_clause_strict` (`LratTrimCheckProof.lean`): `br_check_clause` with `strict ≠ 0`. -/
def checkClauseStrictSpec : Spec := fun args m Q X =>
  ∃ (st id literals antecedents : Val) (max_var n : Nat) (f : CNF Nat) (k : KernelFields)
    (clause_lits ants : List Val) (P_ro : Mem 64 → Prop),
    args = [st, id, literals, antecedents] ∧
    k.strict ≠ 0 ∧
    max_var < n ∧ n < 2 ^ 64 ∧ 4 * ants.length < 2 ^ 64 ∧
    (∀ x ∈ ants, IsInt32 x ∧ x ≠ 0) ∧
    (∀ aid ∈ ants, aid.slt 0 = false → ValidAntecedent max_var f k.literals_begin P_ro aid) ∧
    (∀ x ∈ clause_lits, IsValidLit max_var x) ∧
    (byte1Array k.marks_begin (List.replicate n 0) ⋆ (kernelState st k ⋆ P_ro)) m ∧
    (∃ R', P_ro = (ZeroTermInts antecedents ants ⋆ R')) ∧
    (∃ R', P_ro = (ZeroTermInts literals clause_lits ⋆ R')) ∧
    (CNF.EntailsClause f (toClause clause_lits) → ∀ m',
      (byte1Array k.marks_begin (List.replicate n 0) ⋆
        (kernelState st
          { (k.bumpCheckStats ((clause_lits ++ [0])[0]'(by simp))) with
            stat_resolved := k.stat_resolved + BitVec.ofNat 64 ants.length } ⋆ P_ro)) m' →
      Q [] m') ∧
    (∀ as m', X "lrat_fail" as m')

/-- The hypotheses of `call_br_check_proof_full` (`LratTrimCheckProof.lean`), with the same names. -/
structure CheckProofPre (max_var n : Nat) (st : Val) (k₀ : KernelFields)
    (usedWords litsPtrs antePtrs trail_free0 : List Val) (cnf₀ : CNF Nat)
    (clauses : List (CNF.Clause Nat)) (litsTable anteTable : List (List Val))
    (P_ro : Mem 64 → Prop) (m₀ : Mem 64) : Prop where
  hchecking : k₀.checking ≠ 0
  hforward : k₀.forward = 0
  hfst_pos : 0 < k₀.first_proof_id.toNat
  hfst_le : k₀.first_proof_id.toNat ≤ k₀.empty_clause.toNat
  hemp_lt : k₀.empty_clause.toNat + 1 < 2 ^ 31
  hused_len : k₀.empty_clause.toNat < usedWords.length
  hused_int32 : ∀ i (hi : i < usedWords.length), IsInt32 usedWords[i]
  hlits_len : k₀.empty_clause.toNat < litsPtrs.length
  hante_len : k₀.empty_clause.toNat < antePtrs.length
  hempty_used : isStepUsed k₀.trimming usedWords k₀.empty_clause.toNat = true
  hempty_clause : clauseAt clauses k₀.empty_clause.toNat = .empty
  hP_arrays : ∃ R_arr, P_ro = (int4Array k₀.used_begin usedWords ⋆
    (word8Array k₀.literals_begin litsPtrs ⋆ (word8Array k₀.antecedents_begin antePtrs ⋆ R_arr)))
  hrup_case : k₀.strict = 0 →
    k₀.trail_end = k₀.trail_begin ∧
    4 * trail_free0.length < 2 ^ 64 ∧
    (m₀ =⋆ (byte1Array k₀.values_begin (assignBytes max_var Assignment.empty) ⋆
        int4Array k₀.trail_begin trail_free0) ⋆
      (kernelState st k₀ ⋆ P_ro)) ∧
    (∀ (id : Val) (_hid_lo : k₀.first_proof_id.toNat ≤ id.toNat)
        (hid_hi : id.toNat ≤ k₀.empty_clause.toNat),
      isStepUsed k₀.trimming usedWords id.toNat = true →
      let lits := litsTable.getD id.toNat []
      let aids := anteTable.getD id.toNat []
      let s := stateAt cnf₀ k₀.first_proof_id.toNat k₀.trimming usedWords clauses
        (id.toNat - k₀.first_proof_id.toNat)
      clauseAt clauses id.toNat = toClause lits ∧
      ClauseTable max_var k₀.literals_begin (litsPtrs.take id.toNat) s.formula P_ro ∧
      (∃ R_lits, P_ro = (ZeroTermInts (litsPtrs[id.toNat]'(Nat.lt_of_le_of_lt hid_hi hlits_len)) lits ⋆
        R_lits)) ∧
      (∃ R_aids, P_ro = (ZeroTermInts (antePtrs[id.toNat]'(Nat.lt_of_le_of_lt hid_hi hante_len)) aids ⋆
        R_aids)) ∧
      (∀ x ∈ lits, IsValidLit max_var x) ∧
      (∀ aid ∈ aids, IsInt32 aid ∧ aid ≠ 0 ∧
        (aid.slt 0 = false →
          ∃ h : aid.toNat < (litsPtrs.take id.toNat).length, (litsPtrs.take id.toNat)[aid.toNat] ≠ 0)) ∧
      lits.length + aids.length ≤ trail_free0.length)
  hstrict_case : k₀.strict ≠ 0 →
    max_var < n ∧
    n < 2 ^ 64 ∧
    (m₀ =⋆ byte1Array k₀.marks_begin (List.replicate n 0) ⋆ (kernelState st k₀ ⋆ P_ro)) ∧
    (∀ (id : Val) (_hid_lo : k₀.first_proof_id.toNat ≤ id.toNat)
        (hid_hi : id.toNat ≤ k₀.empty_clause.toNat),
      isStepUsed k₀.trimming usedWords id.toNat = true →
      let lits := litsTable.getD id.toNat []
      let ants := anteTable.getD id.toNat []
      let s := stateAt cnf₀ k₀.first_proof_id.toNat k₀.trimming usedWords clauses
        (id.toNat - k₀.first_proof_id.toNat)
      clauseAt clauses id.toNat = toClause lits ∧
      4 * ants.length < 2 ^ 64 ∧
      (∀ x ∈ ants, IsInt32 x ∧ x ≠ 0) ∧
      (∀ aid ∈ ants, aid.slt 0 = false →
        ValidAntecedent max_var s.toCNF k₀.literals_begin P_ro aid) ∧
      (∀ x ∈ lits, IsValidLit max_var x) ∧
      (∃ R_lits, P_ro = (ZeroTermInts (litsPtrs[id.toNat]'(Nat.lt_of_le_of_lt hid_hi hlits_len)) lits ⋆
        R_lits)) ∧
      (∃ R_ants, P_ro = (ZeroTermInts (antePtrs[id.toNat]'(Nat.lt_of_le_of_lt hid_hi hante_len)) ants ⋆
        R_ants)))

/-- `call_br_check_proof_full`: if `br_check_proof(st)` returns, the formula is unsatisfiable. -/
def checkProofSpec : Spec := fun args m Q X =>
  ∃ (max_var n : Nat) (st : Val) (k₀ : KernelFields)
    (usedWords litsPtrs antePtrs trail_free0 : List Val) (cnf₀ : CNF Nat)
    (clauses : List (CNF.Clause Nat)) (litsTable anteTable : List (List Val))
    (P_ro : Mem 64 → Prop),
    args = [st] ∧
    CheckProofPre max_var n st k₀ usedWords litsPtrs antePtrs trail_free0 cnf₀ clauses litsTable
      anteTable P_ro m ∧
    (∀ m', (∃ k', FullMemInv max_var n trail_free0.length st k₀ P_ro k' m') → cnf₀.Unsat → Q [] m') ∧
    (∀ as m', X "lrat_fail" as m')

end LeanQbe.LratTrim
