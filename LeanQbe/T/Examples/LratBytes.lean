module

public import LeanQbe.T.Notation
public import LeanQbe.T.Module
public import LeanQbe.T.Logic.Mem
public import Std.Sat.CNF
public import LeanQbe.T.Examples.LratBytesProg

/-!
# End-to-end untrusted-bytes LRAT proof checker in `LeanQbe.T` (`lrat_check_bytes`)

Self-contained typed-IR untrusted-bytes LRAT proof checker:
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

/-- ASCII space `' '` (`32 : UInt8`). -/
abbrev asciiSpace : UInt8 := ' '.toNat.toUInt8

/-- ASCII newline `'\n'` (`10 : UInt8`). -/
abbrev asciiNewline : UInt8 := '\n'.toNat.toUInt8

/-- ASCII minus `'-'` (`45 : UInt8`). -/
abbrev asciiMinus : UInt8 := '-'.toNat.toUInt8

/-- ASCII digit zero `'0'` (`48 : UInt8`). -/
abbrev asciiZero : UInt8 := '0'.toNat.toUInt8

/-- ASCII `'p'` (`112 : UInt8`). -/
abbrev asciiP : UInt8 := 'p'.toNat.toUInt8

/-- ASCII `'c'` (`99 : UInt8`). -/
abbrev asciiC : UInt8 := 'c'.toNat.toUInt8

/-- ASCII `'n'` (`110 : UInt8`). -/
abbrev asciiN : UInt8 := 'n'.toNat.toUInt8

/-- ASCII `'f'` (`102 : UInt8`). -/
abbrev asciiF : UInt8 := 'f'.toNat.toUInt8

/-- DIMACS problem header prefix `"p cnf "` (`[112, 32, 99, 110, 102, 32] : List UInt8`). -/
abbrev dimacsHeaderPrefix : List UInt8 :=
  [asciiP, asciiSpace, asciiC, asciiN, asciiF, asciiSpace]

/-- Structural helper for decimal ASCII integer encoding `natToBytes`.
Recursively emits decimal digits of `n` in base 10 into accumulator `acc`.
Terminates via `fuel = n + 1`: since `n / 10 < n` for all `n > 0`
(and `n = 0` terminates in 1 step), `n + 1` steps strictly exceed the number of decimal digits
`⌊log₁₀(n)⌋ + 1` for any `n : Nat`.
Emits no leading zeros for `n > 0`, and produces `['0']` (`[asciiZero]`) for `n = 0`. -/
def natToBytesAux : Nat → Nat → List UInt8 → List UInt8
  | 0, _, acc => acc
  | fuel + 1, n, acc =>
    let d : UInt8 := (asciiZero.toNat + n % 10).toUInt8
    if n < 10 then d :: acc
    else natToBytesAux fuel (n / 10) (d :: acc)

/-- Decimal ASCII representation of `n : Nat`
(e.g. `0` ↦ `"0"` / `[48]`, `42` ↦ `"42"` / `[52, 50]`).
Always supplies `fuel = n + 1` to `natToBytesAux`, guaranteeing termination without digit
truncation and without leading zeros for `n > 0`. -/
def natToBytes (n : Nat) : List UInt8 :=
  natToBytesAux (n + 1) n []

/-- Encode a single `Std.Sat.Literal Nat = Nat × Bool` as standard DIMACS ASCII bytes with
trailing space:
- `(v, true)`  ↦ `"<v> "`  (positive literal: variable `v` in decimal ASCII followed by `' '`)
- `(v, false)` ↦ `"-<v> "` (negative literal: `'-'` followed by variable `v` in decimal ASCII
  and `' '`)
Polarity convention: `l.2 = true` indicates positive polarity (no minus sign),
while `l.2 = false` indicates negated literal (prefixed with `asciiMinus = '-'`). -/
def encodeDimacsLit (l : Literal Nat) : List UInt8 :=
  (if l.2 then [] else [asciiMinus]) ++ natToBytes l.1 ++ [asciiSpace]

/-- Encode a `CNF.Clause Nat` as standard DIMACS ASCII clause bytes terminated with `"0\n"`:
`<lit₁> <lit₂> ... <litₖ> 0\n`
Empty clause `CNF.Clause.ofLiterals []` encodes as `"0\n"` (`[asciiZero, asciiNewline]`). -/
def encodeDimacsClause (cl : CNF.Clause Nat) : List UInt8 :=
  (cl.literals.flatMap encodeDimacsLit) ++ [asciiZero, asciiNewline]

/-- Compute the maximum variable index appearing across all literals in `cnf`.
Returns `0` if `cnf` contains no literals (e.g. empty CNF or only empty clauses). -/
def cnfMaxVar (cnf : CNF Nat) : Nat :=
  cnf.clauses.foldl (fun m cl => cl.literals.foldl (fun m' l => Nat.max m' l.1) m) 0

/-- Canonical ASCII DIMACS encoding of a `CNF Nat` into standard DIMACS CNF format bytes.
Exact byte layout:
```text
p cnf <maxVar> <numClauses>\n
<clause_1_lit_1> ... <clause_1_lit_k> 0\n
...
<clause_m_lit_1> ... <clause_m_lit_j> 0\n
```
Header prefix `"p cnf "`
(`dimacsHeaderPrefix = [asciiP, asciiSpace, asciiC, asciiN, asciiF, asciiSpace]`),
followed by `<maxVar>` in decimal ASCII, space (`asciiSpace`), `<numClauses>`
(`cnf.clauses.size`) in decimal ASCII, newline (`asciiNewline`), and all encoded clauses
in sequence. -/
def encodeDimacs (cnf : CNF Nat) : List UInt8 :=
  dimacsHeaderPrefix ++
    natToBytes (cnfMaxVar cnf) ++ [asciiSpace] ++
    natToBytes cnf.clauses.size ++ [asciiNewline] ++
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

/-- Acyclic `LeanQbe.T.Module` packaging all 6 functions (`externs = []`, `exits = []`). -/
def lratBytesModule : LeanQbe.T.Module :=
  { fns := lratBytesFns, externs := [], exits := [] }

/-! ## Top-level contract and concrete test instances -/

/-- Top-level source contract for
`lrat_check_bytes(cnf_ptr, cnf_len, prf_ptr, prf_len, work_ptr, work_len)`:
assumes zero structural properties of `cnfBytes`, `prfBytes`, or `work`,
leaves `cnfBytes` and `prfBytes`
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
      ((Eq (cnfBytes.At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆
        region work_ptr work_len) ⋆ R_mem) m' →
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

/-- Concrete invalid Binary LRAT proof (5 bytes): attempts to derive `[]` from `[1]` alone
(non-conflict). -/
def nvLratRejectBytes : List UInt8 :=
  encodeLrat [.add 3 [] [1]]

end LeanQbe.T.Examples.LratBytes
