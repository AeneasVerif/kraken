module

public import LeanQbe.T.Notation
public import LeanQbe.T.Module
public import LeanQbe.T.Logic.Mem
public import Std.Sat.CNF

/-!
# End-to-end untrusted-bytes LRAT proof checker in `LeanQbe.T` (`lrat_check_bytes`)

Typed-IR port of the untrusted-bytes LRAT proof checker (`T16` / `K1a`, self-contained per `G5`):
verifies unsatisfiability of a CNF formula given as raw ASCII DIMACS bytes (`cnf_ptr`, `cnf_len`)
against a certificate in standard Binary LRAT format (`prf_ptr`, `prf_len`), using a caller-supplied
uninitialized scratch buffer (`work_ptr`, `work_len`) and returning `1` only if `cnfBytes` is valid
DIMACS for a genuinely unsatisfiable `CNF Nat` (and `0` on any malformed input, invalid proof step,
non-conflict, or insufficient scratch space).

All six functions in `lratBytesFns` take at most 6 `i64` arguments, have `exits = []`, and return a
single `i64` word, assembled in callees-first order as `lratBytesModule : LeanQbe.T.Module`.

## Scratch header layout at `hdr = work_ptr` (10 × 8 = 80 bytes)

* `+0`:  `mv`   (`max_var < 2^28`)
* `+8`:  `nc`   (`num_clauses < 2^28`)
* `+16`: `cap`  (number of 8-byte entries in `clause_ptr`, `nc < cap`)
* `+24`: `vb`   (`values_begin`, `mv + 1` bytes, zero-initialized)
* `+32`: `tb`   (`trail_begin`, `mv + 1` 4-byte ints)
* `+40`: `tlim` (`trail_lim = tb + 4 * (mv + 1)`)
* `+48`: `cb`   (`clause_ptr_begin`, `cap` 8-byte pointers, zero-initialized)
* `+56`: `plim` (`pool_lim`, 4-byte aligned end of literal pool)
* `+64`: `pcur` (`pool_cur`, current 4-byte aligned write cursor in literal pool)
* `+72`: `cur`  (current stream cursor in `cnfBytes` or `prfBytes`)
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.LratBytes

open Std.Sat
open Std.ExtHashMap
open LeanQbe.T

/-! ## Pure specification of ASCII DIMACS CNF (`parseDimacs`) and encoders -/

/-- Standard ASCII whitespace (`' '`, `'\t'`, `'\n'`, `'\v'`, `'\f'`, `'\r'`). -/
def isDimacsWs (b : UInt8) : Bool :=
  b == 32 || (9 ≤ b && b ≤ 13)

/-- ASCII decimal digit `'0'..'9'`. -/
def isDimacsDigit (b : UInt8) : Bool :=
  48 ≤ b && b ≤ 57

/-- Upper bound (`2^28`) on DIMACS header counts and variable indices. -/
def dimacsBound : Nat := 2 ^ 28

/-- Two-state structural scanner (`inComment = true` inside `'c' .. '\n'`) skipping ASCII
whitespace and `'c'` comment lines. -/
def skipWsCommentsAux : Bool → List UInt8 → List UInt8
  | true, [] => []
  | true, 10 :: bs => skipWsCommentsAux false bs
  | true, _ :: bs => skipWsCommentsAux true bs
  | false, [] => []
  | false, b :: bs =>
    if isDimacsWs b then skipWsCommentsAux false bs
    else if b == 99 then skipWsCommentsAux true bs
    else b :: bs

/-- Skip ASCII whitespace and `'c'` (`99`) comment lines. -/
def skipWsComments (bs : List UInt8) : List UInt8 :=
  skipWsCommentsAux false bs

/-- Skip zero or more whitespace bytes. -/
def skipWs : List UInt8 → List UInt8
  | [] => []
  | b :: bs => if isDimacsWs b then skipWs bs else b :: bs

/-- Require at least one whitespace byte and skip any following whitespace. -/
def skipWs1 : List UInt8 → Option (List UInt8)
  | [] => none
  | b :: bs => if isDimacsWs b then some (skipWs bs) else none

/-- Accumulate remaining digits of an unsigned decimal integer `< 2^28`, terminated by ws or EOF. -/
def parseDigitsAux (acc : Nat) : List UInt8 → Option (Nat × List UInt8)
  | [] => some (acc, [])
  | b :: bs =>
    if isDimacsDigit b then
      let acc' := acc * 10 + (b.toNat - 48)
      if acc' < dimacsBound then parseDigitsAux acc' bs else none
    else if isDimacsWs b then
      some (acc, b :: bs)
    else
      none

/-- Parse a non-empty unsigned decimal integer `< 2^28`, terminated by whitespace or EOF. -/
def parseNat : List UInt8 → Option (Nat × List UInt8)
  | [] => none
  | b :: bs =>
    if isDimacsDigit b then parseDigitsAux (b.toNat - 48) bs else none

/-- Parse leading comments/whitespace and the `p cnf <max_var> <num_clauses>` header. -/
def parseHeader (bs : List UInt8) : Option (Nat × Nat × List UInt8) := do
  match skipWsComments bs with
  | 112 :: bs1 =>
    let bs2 ← skipWs1 bs1
    match bs2 with
    | 99 :: 110 :: 102 :: bs3 =>
      let bs4 ← skipWs1 bs3
      let (mv, bs5) ← parseNat bs4
      let bs6 ← skipWs1 bs5
      let (nc, bs7) ← parseNat bs6
      some (mv, nc, bs7)
    | _ => none
  | _ => none

/-- Structural helper for `parseClause`: each literal consumes ≥ 1 byte, so `bs.length + 1` steps
suffice for any input `bs` without truncation. -/
def parseClauseAux : Nat → Nat → List (Literal Nat) → List UInt8 →
    Option (CNF.Clause Nat × List UInt8)
  | 0, _, _, _ => none
  | fuel + 1, mv, acc, bs =>
    match skipWsComments bs with
    | [] => none
    | 45 :: rest =>
      match parseNat rest with
      | some (v, rest') =>
        if 1 ≤ v && v ≤ mv then parseClauseAux fuel mv ((v, false) :: acc) rest' else none
      | none => none
    | b :: rest =>
      match parseNat (b :: rest) with
      | some (0, rest') => some (CNF.Clause.ofLiterals acc.reverse, rest')
      | some (v, rest') =>
        if 1 ≤ v && v ≤ mv then parseClauseAux fuel mv ((v, true) :: acc) rest' else none
      | none => none

/-- Parse one `0`-terminated clause of signed decimal literals with variables in `1..mv`. -/
def parseClause (mv : Nat) (bs : List UInt8) : Option (CNF.Clause Nat × List UInt8) :=
  parseClauseAux (bs.length + 1) mv [] bs

/-- Parse `k` `0`-terminated clauses and require only whitespace/comments until EOF. -/
def parseClauses (mv : Nat) : Nat → CNF Nat → List UInt8 → Option (CNF Nat)
  | 0, cnf, bs => if (skipWsComments bs).isEmpty then some cnf else none
  | k + 1, cnf, bs => do
    let (cl, bs') ← parseClause mv bs
    parseClauses mv k (cnf.add cl) bs'

/-- Total pure specification of standard ASCII DIMACS CNF. -/
def parseDimacs (bs : List UInt8) : Option (CNF Nat) := do
  let (mv, nc, rest) ← parseHeader bs
  parseClauses mv nc CNF.empty rest

/-! ### DIMACS and Binary LRAT encoders (for callers and concrete test witnesses) -/

def natToBytesAux : Nat → Nat → List UInt8 → List UInt8
  | 0, _, acc => acc
  | fuel + 1, n, acc =>
    let d : UInt8 := (48 + n % 10).toUInt8
    if n < 10 then d :: acc
    else natToBytesAux fuel (n / 10) (d :: acc)

/-- Decimal ASCII encoding of `n`. -/
def natToBytes (n : Nat) : List UInt8 :=
  natToBytesAux (n + 1) n []

def encodeDimacsLit (l : Literal Nat) : List UInt8 :=
  (if l.2 then [] else [45]) ++ natToBytes l.1 ++ [32]

def encodeDimacsClause (cl : CNF.Clause Nat) : List UInt8 :=
  (cl.literals.flatMap encodeDimacsLit) ++ [48, 10]

def cnfMaxVar (cnf : CNF Nat) : Nat :=
  cnf.clauses.foldl (fun m cl => cl.literals.foldl (fun m' l => Nat.max m' l.1) m) 0

/-- Canonical ASCII DIMACS encoding of a `CNF Nat`. -/
def encodeDimacs (cnf : CNF Nat) : List UInt8 :=
  [112, 32, 99, 110, 102, 32] ++
    natToBytes (cnfMaxVar cnf) ++ [32] ++
    natToBytes cnf.clauses.size ++ [10] ++
    (cnf.clauses.toList.flatMap encodeDimacsClause)

def encodeLeb128Aux : Nat → Nat → List UInt8
  | 0, _ => []
  | fuel + 1, n =>
    if n < 128 then [n.toUInt8]
    else (n % 128 + 128).toUInt8 :: encodeLeb128Aux fuel (n / 128)

/-- Unsigned LEB128 encoding of `n`. -/
def encodeLeb128 (n : Nat) : List UInt8 :=
  encodeLeb128Aux (n + 1) n

/-- Binary LRAT zig-zag + LEB128 encoding of a signed literal (`2 * |lit| + sign`). -/
def encodeLratLit (lit : Int) : List UInt8 :=
  if lit == 0 then [0]
  else if lit > 0 then encodeLeb128 (2 * lit.natAbs)
  else encodeLeb128 (2 * lit.natAbs + 1)

/-- A step in a Binary LRAT proof: `'a'` (addition with RUP hints) or `'d'` (clause deletion). -/
inductive LratStep
  | add (id : Nat) (lits : List Int) (hints : List Nat)
  | del (ids : List Nat)
  deriving Repr, DecidableEq

def encodeLratStep : LratStep → List UInt8
  | .add id lits hints =>
    [0x61] ++ encodeLeb128 (2 * id) ++
      (lits.flatMap encodeLratLit) ++ [0] ++
      (hints.flatMap (fun aid => encodeLeb128 (2 * aid))) ++ [0]
  | .del ids =>
    [0x64] ++ (ids.flatMap (fun did => encodeLeb128 (2 * did))) ++ [0]

/-- Encode a list of LRAT steps into standard Binary LRAT bytes. -/
def encodeLrat (steps : List LratStep) : List UInt8 :=
  steps.flatMap encodeLratStep

/-! ## `LeanQbe.T` implementation of `lrat_check_bytes` -/

/-- `ws = true` iff byte `b` (`0..255`) is ASCII whitespace (`32` or `9..13`), else `false`. -/
def isWsByte {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} (b : V i64)
    (k : V .bool → Expr V L rs) : Expr V L rs := tqbe {
  %sp:b = ceql %b, 32
  %t:l = sub %b, 9
  %ctl:b = cultl %t, 5
  %ws:b = or %sp, %ctl
  ⟨k ws⟩
}

/-- Advance `cur` past ASCII whitespace and `'c' .. '\n'` comments up to `cend`. -/
def skipWsCommentsQbe {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} (cur cend : V i64)
    (done : V i64 → Expr V L rs) : Expr V L rs := tqbe {
  @done_swc(%res:l) {
    ⟨done res⟩
  }
  {
    @swc(%p:l) {
      %eof:b = ceql %p, %cend
      jnz %eof, @done_swc(%p), {
        %b8:i8 = load %p
        %b:l = zext %b8
        %p1:l = add %p, 1
        %ws:b <- isWsByte(%b)
        jnz %ws, @swc(%p1), {
          %isc:b = ceql %b, 99
          jnz %isc, {
            @skl(%q:l) {
              %qeof:b = ceql %q, %cend
              jnz %qeof, @done_swc(%q), {
                %c8:i8 = load %q
                %c:l = zext %c8
                %q1:l = add %q, 1
                %isnl:b = ceql %c, 10
                jnz %isnl, @swc(%q1), @skl(%q1)
              }
            }
            jmp @skl(%p1)
          }, @done_swc(%p)
        }
      }
    }
    jmp @swc(%cur)
  }
}

/-- Require ≥ 1 whitespace byte at `cur`, then skip any remaining whitespace up to `cend`. -/
def skipWs1Qbe {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} (fail : L [])
    (cur cend : V i64) (done : V i64 → Expr V L rs) : Expr V L rs := tqbe {
  %eof0:b = ceql %cur, %cend
  jnz %eof0, @fail, {
    %b08:i8 = load %cur
    %b0:l = zext %b08
    %ws0:b <- isWsByte(%b0)
    jnz %ws0, {
      @done_sw(%res:l) {
        ⟨done res⟩
      }
      {
        @sw(%p:l) {
          %eof:b = ceql %p, %cend
          jnz %eof, @done_sw(%p), {
            %b8:i8 = load %p
            %b:l = zext %b8
            %ws:b <- isWsByte(%b)
            jnz %ws, {
              %p1:l = add %p, 1
              jmp @sw(%p1)
            }, @done_sw(%p)
          }
        }
        %cur1:l = add %cur, 1
        jmp @sw(%cur1)
      }
    }, @fail
  }
}

/-- Read an unsigned decimal integer `< 2^28` (`268435456`), terminated by whitespace or `cend`. -/
def readDimacsNat {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} (fail : L [])
    (cur cend : V i64) (done : V i64 → V i64 → Expr V L rs) : Expr V L rs := tqbe {
  %eof0:b = ceql %cur, %cend
  jnz %eof0, @fail, {
    %b08:i8 = load %cur
    %b0:l = zext %b08
    %d0:l = sub %b0, 48
    %ok0:b = cultl %d0, 10
    jnz %ok0, {
      @done_nat(%val:l, %res:l) {
        ⟨done val res⟩
      }
      {
        @pdig(%p:l, %acc:l) {
          %eof:b = ceql %p, %cend
          jnz %eof, @done_nat(%acc, %p), {
            %b8:i8 = load %p
            %b:l = zext %b8
            %d:l = sub %b, 48
            %isd:b = cultl %d, 10
            jnz %isd, {
              %a10:l = mul %acc, 10
              %acc2:l = add %a10, %d
              %okb:b = cultl %acc2, 268435456
              jnz %okb, {
                %p1:l = add %p, 1
                jmp @pdig(%p1, %acc2)
              }, @fail
            }, {
              %ws:b <- isWsByte(%b)
              jnz %ws, @done_nat(%acc, %p), @fail
            }
          }
        }
        %cur1:l = add %cur, 1
        jmp @pdig(%cur1, %d0)
      }
    }, @fail
  }
}

/-- Read 1..4 bytes of unsigned LEB128 (`u < 2^28`) from `[cur, pend)`, jumping to `fail` on EOF or 5+ bytes. -/
def readLeb128 {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} (fail : L [])
    (cur pend : V i64) (done : V i64 → V i64 → Expr V L rs) : Expr V L rs := tqbe {
  @done_leb(%u:l, %res:l) {
    ⟨done u res⟩
  }
  {
    @leb(%p:l, %acc:l, %sh:l) {
      %eof:b = ceql %p, %pend
      jnz %eof, @fail, {
        %b8:i8 = load %p
        %b:l = zext %b8
        %p1:l = add %p, 1
        %lo:l = and %b, 127
        %sl:l = shl %lo, %sh
        %acc2:l = or %acc, %sl
        %hi:l = and %b, 128
        %more:b = cnel %hi, 0
        jnz %more, {
          %sh2:l = add %sh, 7
          %oksh:b = cultl %sh2, 28
          jnz %oksh, @leb(%p1, %acc2, %sh2), @fail
        }, @done_leb(%acc2, %p1)
      }
    }
    jmp @leb(%cur, 0, 0)
  }
}

/-- Lookup `idx = |lit|` and `val = evalAssignedLit values[idx] lit`. -/
def assignedLit {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} (vb lit : V i64)
    (k : V i64 → V i64 → Expr V L rs) : Expr V L rs := tqbe {
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

/-- Bounds-checked trail push + assignment (`values[idx] := sign(lit)`). -/
def assignLitChecked {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} (fail : L [])
    (vb tlim te lit idx : V i64) (k : V i64 → Expr V L rs) : Expr V L rs := tqbe {
  %full:b = ceql %te, %tlim
  jnz %full, @fail, {
    %s:l = sar %lit, 63
    %sg:l = or %s, 1
    %sg8:i8 = trunc %sg
    %pa:l = add %vb, %idx
    store %sg8, %pa
    %lit32:w = trunc %lit
    store %lit32, %te
    %te2:l = add %te, 4
    ⟨k te2⟩
  }
}

/-- Clear `values[|t|]` for every literal `t` in `[tb, te)`. -/
def backtrack {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} (vb tb te : V i64)
    (k : Expr V L rs) : Expr V L rs := tqbe {
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

/-- Parse `p cnf <mv> <nc>`, storing `mv` at `hdr+0`, `nc` at `hdr+8`, and body cursor at `hdr+72`. -/
def lbParseDimacsHeader : Func [i64, i64, i64] [i64] :=
  tqbe(%cnf_ptr:l, %cnf_end:l, %hdr:l) -> l {
    @fail() {
      ret 0
    }
    {
      %cur1:l <- skipWsCommentsQbe(%cnf_ptr, %cnf_end)
      %eof1:b = ceql %cur1, %cnf_end
      jnz %eof1, @fail, {
        %bp8:i8 = load %cur1
        %bp:l = zext %bp8
        %isp:b = ceql %bp, 112
        jnz %isp, {
          %p_after:l = add %cur1, 1
          %cur2:l <- skipWs1Qbe(@fail, %p_after, %cnf_end)
          %eofc0:b = ceql %cur2, %cnf_end
          jnz %eofc0, @fail, {
            %bc8:i8 = load %cur2
            %bc:l = zext %bc8
            %isc:b = ceql %bc, 99
            jnz %isc, {
              %c1:l = add %cur2, 1
              %eofc1:b = ceql %c1, %cnf_end
              jnz %eofc1, @fail, {
                %bn8:i8 = load %c1
                %bn:l = zext %bn8
                %isn:b = ceql %bn, 110
                jnz %isn, {
                  %c2:l = add %cur2, 2
                  %eofc2:b = ceql %c2, %cnf_end
                  jnz %eofc2, @fail, {
                    %bf8:i8 = load %c2
                    %bf:l = zext %bf8
                    %isf:b = ceql %bf, 102
                    jnz %isf, {
                      %c3:l = add %cur2, 3
                      %cur3:l <- skipWs1Qbe(@fail, %c3, %cnf_end)
                      %mv:l, %cur4:l <- readDimacsNat(@fail, %cur3, %cnf_end)
                      %cur5:l <- skipWs1Qbe(@fail, %cur4, %cnf_end)
                      %nc:l, %cur6:l <- readDimacsNat(@fail, %cur5, %cnf_end)
                      store %mv, %hdr
                      %p8:l = add %hdr, 8
                      store %nc, %p8
                      %p72:l = add %hdr, 72
                      store %cur6, %p72
                      ret 1
                    }, @fail
                  }
                }, @fail
              }
            }, @fail
          }
        }, @fail
      }
    }
  }

/-- Parse `nc` `0`-terminated DIMACS clauses into the pool and populate `clause_ptr[1..nc]`. -/
def lbParseDimacsBody : Func [i64, i64] [i64] :=
  tqbe(%cnf_end:l, %hdr:l) -> l {
    %mv:l = load %hdr
    %p8:l = add %hdr, 8
    %nc:l = load %p8
    %p48:l = add %hdr, 48
    %cb:l = load %p48
    %p56:l = add %hdr, 56
    %plim:l = load %p56
    %p64:l = add %hdr, 64
    %pcur0:l = load %p64
    %p72:l = add %hdr, 72
    %cur0:l = load %p72
    @fail() {
      ret 0
    }
    {
      @cl_loop(%cid:l, %cur:l, %pcur:l) {
        %done_cls:b = cultl %nc, %cid
        jnz %done_cls, {
          %end_cur:l <- skipWsCommentsQbe(%cur, %cnf_end)
          %at_eof:b = ceql %end_cur, %cnf_end
          jnz %at_eof, {
            store %pcur, %p64
            ret 1
          }, @fail
        }, {
          @lit_loop(%lcur:l, %wcur:l) {
            %cur1:l <- skipWsCommentsQbe(%lcur, %cnf_end)
            %eof:b = ceql %cur1, %cnf_end
            jnz %eof, @fail, {
              %full:b = ceql %wcur, %plim
              jnz %full, @fail, {
                %b8:i8 = load %cur1
                %b:l = zext %b8
                %is_neg:b = ceql %b, 45
                jnz %is_neg, {
                  %after_m:l = add %cur1, 1
                  %v:l, %cur2:l <- readDimacsNat(@fail, %after_m, %cnf_end)
                  %vz:b = ceql %v, 0
                  jnz %vz, @fail, {
                    %vbig:b = cultl %mv, %v
                    jnz %vbig, @fail, {
                      %nlit:l = sub 0, %v
                      %nlit32:w = trunc %nlit
                      store %nlit32, %wcur
                      %wcur2:l = add %wcur, 4
                      jmp @lit_loop(%cur2, %wcur2)
                    }
                  }
                }, {
                  %v:l, %cur2:l <- readDimacsNat(@fail, %cur1, %cnf_end)
                  %vz:b = ceql %v, 0
                  jnz %vz, {
                    store 0:w, %wcur
                    %wcur2:l = add %wcur, 4
                    %off:l = shl %cid, 3
                    %slot:l = add %cb, %off
                    store %pcur, %slot
                    %cid2:l = add %cid, 1
                    jmp @cl_loop(%cid2, %cur2, %wcur2)
                  }, {
                    %vbig:b = cultl %mv, %v
                    jnz %vbig, @fail, {
                      %v32:w = trunc %v
                      store %v32, %wcur
                      %wcur2:l = add %wcur, 4
                      jmp @lit_loop(%cur2, %wcur2)
                    }
                  }
                }
              }
            }
          }
          jmp @lit_loop(%cur, %pcur)
        }
      }
      jmp @cl_loop(1, %cur0, %pcur0)
    }
  }

/-- Decode the `0`-terminated zig-zag LEB128 literal list of an `'a'` step into the pool.
Returns `0` on error, `1` on non-empty clause, `2` on empty clause `[]`. -/
def lbReadAddLits : Func [i64, i64] [i64] :=
  tqbe(%hdr:l, %prf_end:l) -> l {
    %mv:l = load %hdr
    %p56:l = add %hdr, 56
    %plim:l = load %p56
    %p64:l = add %hdr, 64
    %pcur0:l = load %p64
    %p72:l = add %hdr, 72
    %cur0:l = load %p72
    @fail() {
      ret 0
    }
    {
      @rd_loop(%cur:l, %wcur:l) {
        %full:b = ceql %wcur, %plim
        jnz %full, @fail, {
          %u:l, %cur2:l <- readLeb128(@fail, %cur, %prf_end)
          %uz:b = ceql %u, 0
          jnz %uz, {
            store 0:w, %wcur
            %wcur2:l = add %wcur, 4
            store %wcur2, %p64
            store %cur2, %p72
            %is_emp:b = ceql %wcur, %pcur0
            jnz %is_emp, { ret 2 }, { ret 1 }
          }, {
            %v:l = shr %u, 1
            %vz:b = ceql %v, 0
            jnz %vz, @fail, {
              %vbig:b = cultl %mv, %v
              jnz %vbig, @fail, {
                %sbit:l = and %u, 1
                %mask:l = sub 0, %sbit
                %x:l = xor %v, %mask
                %lit:l = sub %x, %mask
                %lit32:w = trunc %lit
                store %lit32, %wcur
                %wcur2:l = add %wcur, 4
                jmp @rd_loop(%cur2, %wcur2)
              }
            }
          }
        }
      }
      jmp @rd_loop(%cur0, %pcur0)
    }
  }

/-- Phase 1 of RUP: negate literals at `c_ptr` into `values`/`trail`, or jump to `taut` on tautology. -/
def rupPhase1 {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (fail : L []) (taut ph2 : L [i64, i64]) (vb tlim c_ptr tb cur0 : V i64) : Expr V L rs := tqbe {
  @p1(%l:l, %te:l) {
    %lit32:w = load %l
    %lit_nz:b = cnew %lit32, 0
    jnz %lit_nz, {
      %lit:l = sext %lit32
      %idx:l, %val:l <- assignedLit(%vb, %lit)
      %l2:l = add %l, 4
      %vneg:b = csltl %val, 0
      jnz %vneg, @p1(%l2, %te), {
        %vpos:b = csltl 0, %val
        jnz %vpos, @taut(%cur0, %te), {
          %nlit:l = sub 0, %lit
          %te2:l <- assignLitChecked(@fail, %vb, %tlim, %te, %nlit, %idx)
          jmp @p1(%l2, %te2)
        }
      }
    }, @ph2(%cur0, %te)
  }
  jmp @p1(%c_ptr, %tb)
}

/-- Phase 2 inner loop: unit-propagate over `0`-terminated antecedent literals at `als`. -/
def rupInner {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (fail : L []) (done : L [i64, i64]) (vb tlim als te0 : V i64) : Expr V L rs := tqbe {
  @lp(%l:l, %unit:l, %te:l) {
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
        jnz %c, @fail, @lp(%l2, %unit, %te)
      }, {
        @setunit() {
          %vz:b = ceql %val, 0
          jnz %vz, {
            %te2:l <- assignLitChecked(@fail, %vb, %tlim, %te, %lit, %idx)
            jmp @lp(%l2, %lit, %te2)
          }, @lp(%l2, %lit, %te)
        }
        %unit_nz:b = cnel %unit, 0
        jnz %unit_nz, {
          %eq:b = ceql %unit, %lit
          jnz %eq, @setunit, @fail
        }, @setunit
      }
    }, @done(%unit, %te)
  }
  jmp @lp(%als, 0, %te0)
}

/-- Run RUP check for candidate clause at `c_ptr` (with clause ID `id`), streaming hints from `hdr+72`.
On success, consumes the hint `0`-terminator, backtracks `values` to empty, updates `hdr+72`, and returns `1`. -/
def lbRupCheck : Func [i64, i64, i64, i64] [i64] :=
  tqbe(%hdr:l, %id:l, %c_ptr:l, %prf_end:l) -> l {
    %p24:l = add %hdr, 24
    %vb:l = load %p24
    %p32:l = add %hdr, 32
    %tb:l = load %p32
    %p40:l = add %hdr, 40
    %tlim:l = load %p40
    %p48:l = add %hdr, 48
    %cb:l = load %p48
    %p72:l = add %hdr, 72
    %cur0:l = load %p72
    @fail() {
      ret 0
    }
    {
      @consume(%ccur:l, %cte:l) {
        @cloop(%p:l) {
          %u:l, %p2:l <- readLeb128(@fail, %p, %prf_end)
          %uz:b = ceql %u, 0
          jnz %uz, {
            use backtrack(%vb, %tb, %cte)
            store %p2, %p72
            ret 1
          }, {
            %odd:l = and %u, 1
            %is_odd:b = cnel %odd, 0
            jnz %is_odd, @fail, {
              %aid:l = shr %u, 1
              %lt_id:b = cultl %aid, %id
              jnz %lt_id, {
                %off:l = shl %aid, 3
                %slot:l = add %cb, %off
                %als:l = load %slot
                %act:b = cnel %als, 0
                jnz %act, @cloop(%p2), @fail
              }, @fail
            }
          }
        }
        jmp @cloop(%ccur)
      }
      {
        @ph2(%hcur:l, %hte:l) {
          @outer(%p:l, %t:l) {
            %u:l, %p2:l <- readLeb128(@fail, %p, %prf_end)
            %uz:b = ceql %u, 0
            jnz %uz, @fail, {
              %odd:l = and %u, 1
              %is_odd:b = cnel %odd, 0
              jnz %is_odd, @fail, {
                %aid:l = shr %u, 1
                %lt_id:b = cultl %aid, %id
                jnz %lt_id, {
                  %off:l = shl %aid, 3
                  %slot:l = add %cb, %off
                  %als:l = load %slot
                  %act:b = cnel %als, 0
                  jnz %act, {
                    @idone(%unit:l, %t2:l) {
                      %unit_nz:b = cnel %unit, 0
                      jnz %unit_nz, @outer(%p2, %t2), @consume(%p2, %t2)
                    }
                    ⟨rupInner fail idone vb tlim als t⟩
                  }, @fail
                }, @fail
              }
            }
          }
          jmp @outer(%hcur, %hte)
        }
        ⟨rupPhase1 fail consume ph2 vb tlim c_ptr tb cur0⟩
      }
    }
  }

/-- Process Binary LRAT records (`'a'` and `'d'`) from `hdr+72` up to `prf_end`.
Returns `1` as soon as an `'a'` step derives the empty clause `[]`, or `0` on any error or EOF. -/
def lbCheckPrf : Func [i64, i64] [i64] :=
  tqbe(%hdr:l, %prf_end:l) -> l {
    %p8:l = add %hdr, 8
    %nc:l = load %p8
    %p16:l = add %hdr, 16
    %cap:l = load %p16
    %p48:l = add %hdr, 48
    %cb:l = load %p48
    %p64:l = add %hdr, 64
    %p72:l = add %hdr, 72
    @fail() {
      ret 0
    }
    {
      @rec_loop() {
        %cur:l = load %p72
        %eof:b = ceql %cur, %prf_end
        jnz %eof, @fail, {
          %tag8:i8 = load %cur
          %tag:l = zext %tag8
          %cur1:l = add %cur, 1
          %is_a:b = ceql %tag, 97
          jnz %is_a, {
            %uid:l, %cur2:l <- readLeb128(@fail, %cur1, %prf_end)
            %odd:l = and %uid, 1
            %is_odd:b = cnel %odd, 0
            jnz %is_odd, @fail, {
              %id:l = shr %uid, 1
              %gt_nc:b = cultl %nc, %id
              jnz %gt_nc, {
                %lt_cap:b = cultl %id, %cap
                jnz %lt_cap, {
                  %off:l = shl %id, 3
                  %slot:l = add %cb, %off
                  %old:l = load %slot
                  %used:b = cnel %old, 0
                  jnz %used, @fail, {
                    store %cur2, %p72
                    %c_ptr:l = load %p64
                    %lstat:l = call $lb_read_add_lits(%hdr, %prf_end)
                    %lok:b = cnel %lstat, 0
                    jnz %lok, {
                      %rok:l = call $lb_rup_check(%hdr, %id, %c_ptr, %prf_end)
                      %rok_nz:b = cnel %rok, 0
                      jnz %rok_nz, {
                        %is_emp:b = ceql %lstat, 2
                        jnz %is_emp, { ret 1 }, {
                          store %c_ptr, %slot
                          jmp @rec_loop
                        }
                      }, @fail
                    }, @fail
                  }
                }, @fail
              }, @fail
            }
          }, {
            %is_d:b = ceql %tag, 100
            jnz %is_d, {
              @del_loop(%dcur:l) {
                %u:l, %dcur2:l <- readLeb128(@fail, %dcur, %prf_end)
                %uz:b = ceql %u, 0
                jnz %uz, {
                  store %dcur2, %p72
                  jmp @rec_loop
                }, {
                  %odd:l = and %u, 1
                  %is_odd:b = cnel %odd, 0
                  jnz %is_odd, @fail, {
                    %did:l = shr %u, 1
                    %dz:b = ceql %did, 0
                    jnz %dz, @fail, {
                      %lt_cap:b = cultl %did, %cap
                      jnz %lt_cap, {
                        %off:l = shl %did, 3
                        %slot:l = add %cb, %off
                        %old:l = load %slot
                        %act:b = cnel %old, 0
                        jnz %act, {
                          store 0:l, %slot
                          jmp @del_loop(%dcur2)
                        }, @fail
                      }, @fail
                    }
                  }
                }
              }
              jmp @del_loop(%cur1)
            }, @fail
          }
        }
      }
      jmp @rec_loop
    }
  }

/-- Top-level entry point:
`lrat_check_bytes(cnf_ptr, cnf_len, prf_ptr, prf_len, work_ptr, work_len) -> 0 | 1`. -/
def lratCheckBytes : Func [i64, i64, i64, i64, i64, i64] [i64] :=
  tqbe(%cnf_ptr:l, %cnf_len:l, %prf_ptr:l, %prf_len:l, %work_ptr:l, %work_len:l) -> l {
    %small:b = cultl %work_len, 128
    jnz %small, { ret 0 }, {
      %cnf_end:l = add %cnf_ptr, %cnf_len
      %prf_end:l = add %prf_ptr, %prf_len
      %hok:l = call $lb_parse_dimacs_header(%cnf_ptr, %cnf_end, %work_ptr)
      %hok_nz:b = cnel %hok, 0
      jnz %hok_nz, {
        %mv:l = load %work_ptr
        %p8:l = add %work_ptr, 8
        %nc:l = load %p8
        %mv1:l = add %mv, 1
        %mv8:l = add %mv, 8
        %v_bytes:l = and %mv8, -8
        %t_raw:l = shl %mv1, 2
        %t_pad:l = add %t_raw, 7
        %t_bytes:l = and %t_pad, -8
        %vt:l = add %v_bytes, %t_bytes
        %fixed:l = add 80, %vt
        %no_fit:b = cultl %work_len, %fixed
        jnz %no_fit, { ret 0 }, {
          %rem:l = sub %work_len, %fixed
          %c_half:l = shr %rem, 4
          %p_cap:l = and %prf_len, 268435455
          %w1:l = add %nc, %p_cap
          %want:l = add %w1, 32
          @got_cap(%cap:l) {
            %bad_cap:b = culel %cap, %nc
            jnz %bad_cap, { ret 0 }, {
              %vb:l = add %work_ptr, 80
              %tb:l = add %vb, %v_bytes
              %tlim:l = add %tb, %t_raw
              %cb:l = add %tb, %t_bytes
              %cb_bytes:l = shl %cap, 3
              %pbase:l = add %cb, %cb_bytes
              %pool_rem:l = sub %rem, %cb_bytes
              %pool_bytes:l = and %pool_rem, -4
              %plim:l = add %pbase, %pool_bytes
              @zv_done() {
                @zcb_done() {
                  %p16:l = add %work_ptr, 16
                  store %cap, %p16
                  %p24:l = add %work_ptr, 24
                  store %vb, %p24
                  %p32:l = add %work_ptr, 32
                  store %tb, %p32
                  %p40:l = add %work_ptr, 40
                  store %tlim, %p40
                  %p48:l = add %work_ptr, 48
                  store %cb, %p48
                  %p56:l = add %work_ptr, 56
                  store %plim, %p56
                  %p64:l = add %work_ptr, 64
                  store %pbase, %p64
                  %bok:l = call $lb_parse_dimacs_body(%cnf_end, %work_ptr)
                  %bok_nz:b = cnel %bok, 0
                  jnz %bok_nz, {
                    %p72:l = add %work_ptr, 72
                    store %prf_ptr, %p72
                    %pok:l = call $lb_check_prf(%work_ptr, %prf_end)
                    ret %pok
                  }, { ret 0 }
                }
                {
                  @zcb(%j:l) {
                    %ltc:b = cultl %j, %cap
                    jnz %ltc, {
                      %joff:l = shl %j, 3
                      %jslot:l = add %cb, %joff
                      store 0:l, %jslot
                      %j2:l = add %j, 1
                      jmp @zcb(%j2)
                    }, @zcb_done
                  }
                  jmp @zcb(0)
                }
              }
              {
                @zv(%i:l) {
                  %lem:b = culel %i, %mv
                  jnz %lem, {
                    %vp:l = add %vb, %i
                    store 0:i8, %vp
                    %i2:l = add %i, 1
                    jmp @zv(%i2)
                  }, @zv_done
                }
                jmp @zv(0)
              }
            }
          }
          %use_half:b = cultl %c_half, %want
          jnz %use_half, @got_cap(%c_half), @got_cap(%want)
        }
      }, { ret 0 }
    }
  }

/-- The acyclic 6-function list (callees first, `lrat_check_bytes` last). -/
def lratBytesFns : List Fn :=
  [ ⟨"lb_parse_dimacs_header", [i64, i64, i64], [i64], lbParseDimacsHeader⟩,
    ⟨"lb_parse_dimacs_body", [i64, i64], [i64], lbParseDimacsBody⟩,
    ⟨"lb_read_add_lits", [i64, i64], [i64], lbReadAddLits⟩,
    ⟨"lb_rup_check", [i64, i64, i64, i64], [i64], lbRupCheck⟩,
    ⟨"lb_check_prf", [i64, i64], [i64], lbCheckPrf⟩,
    ⟨"lrat_check_bytes", [i64, i64, i64, i64, i64, i64], [i64], lratCheckBytes⟩ ]

/-- Acyclic `LeanQbe.T.Module` packaging all 6 functions (`externs = []`, `exits = []`). -/
def lratBytesModule : LeanQbe.T.Module :=
  { fns := lratBytesFns, externs := [], exits := [] }

/-! ## Top-level contract and concrete test instances -/

/-- Top-level source contract for `lrat_check_bytes(cnf_ptr, cnf_len, prf_ptr, prf_len, work_ptr, work_len)`:
assumes zero structural properties of `cnfBytes`, `prfBytes`, or `work`, leaves `cnfBytes` and `prfBytes`
untouched and `work` as `region work_ptr work_len`, returns `0` or `1` (with `exits = []`, so `X` is
unconstrained and can be instantiated to `False`), and returns `1` only when `parseDimacs cnfBytes`
succeeds on an unsatisfiable `CNF Nat`. -/
def lratCheckBytesSpec : Spec [i64, i64, i64, i64, i64, i64] [i64] := fun args m Q _ =>
  ∃ (cnf_ptr prf_ptr work_ptr : BitVec 64) (cnfBytes prfBytes : List UInt8) (work_len : Nat)
    (R_mem : Mem 64 → Prop),
    args = (cnf_ptr, BitVec.ofNat 64 cnfBytes.length,
            prf_ptr, BitVec.ofNat 64 prfBytes.length,
            work_ptr, BitVec.ofNat 64 work_len, ()) ∧
    cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧
    prf_ptr.toNat + prfBytes.length < 2 ^ 64 ∧
    work_ptr.toNat + work_len < 2 ^ 64 ∧
    ((Eq (cnfBytes.At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆ region work_ptr work_len) ⋆ R_mem) m ∧
    ∀ (r : BitVec 64) (m' : Mem 64),
      (r = 0 ∨ r = 1) →
      (r = 1 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) →
      ((Eq (cnfBytes.At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆ region work_ptr work_len) ⋆ R_mem) m' →
      Q (r, ()) m'

/-- Unsatisfiable 2-clause formula `(x₁) ∧ (¬x₁)` for concrete accepting non-vacuity. -/
def nvBytesCnf : CNF Nat :=
  (CNF.empty.add (CNF.Clause.ofLiterals [(1, true)])).add (CNF.Clause.ofLiterals [(1, false)])

/-- Concrete ASCII DIMACS bytes `"p cnf 1 2\n1 0\n-1 0\n"` (19 bytes). -/
def nvDimacsBytes : List UInt8 :=
  encodeDimacs nvBytesCnf

/-- Concrete 3-step Binary LRAT proof exercising both `'a'` and `'d'` (15 bytes):
1. `'a'` ID 3 `[1]` from hint `[1]`,
2. `'d'` delete ID 1,
3. `'a'` ID 4 `[]` (empty clause) from hints `[3, 2]`. -/
def nvLratAcceptBytes : List UInt8 :=
  encodeLrat [.add 3 [1] [1], .del [1], .add 4 [] [3, 2]]

/-- Concrete invalid Binary LRAT proof (5 bytes): attempts to derive `[]` from `[1]` alone (non-conflict). -/
def nvLratRejectBytes : List UInt8 :=
  encodeLrat [.add 3 [] [1]]

end LeanQbe.T.Examples.LratBytes
