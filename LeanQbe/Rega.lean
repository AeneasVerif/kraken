module

public import LeanQbe.IL
public import LeanQbe.Abi

/-!
# Lowering from PHOAS to target directives (QBE `rega.c`, plus the parts of `emit.c` that place code)

`lower` is the verified exit of the compiler (plan section 2.2, decision D9). It is one structural
recursion over the IL term instantiated at `V := Nat` (names) and `L := Nat` (label numbers).

Its state is the next fresh name `nv`, the next fresh label `nl`, and a *symbolic register file*
`R : List (Arg Nat × Reg)`: `(.var x, r) ∈ R` means "register `r` holds the value of name `x`",
`(.imm c, r) ∈ R` means "register `r` holds `c`". A relation, not a map: a value may sit in several
registers (needed for `jump l(x, x)`), and a register may hold several names (after a move).

Hints come from an untrusted oracle (`Live`, `Spill`): a destination register per name, and an
entry map per label. The lowering never trusts them:

* an operand is read from `R`; if it is not there, compilation fails;
* writing a register removes every entry for it (and every snippet removes the scratch registers);
* at `jump ℓ(args)` / `ret vs`, an untrusted parallel-move pass computes moves, `lower` executes them
  symbolically, and then checks that `R` contains every entry the target expects;
* a block body is lowered from exactly its entry map.

So the correctness proof (`RegaLemmas.lean`) has no liveness, interference or dominance argument.

Code layout: `rest ++ [label ℓ] ++ body` for a block, `jnz c ℓ ++ else ++ [label ℓ] ++ then` for a
conditional; every lowered term ends in a jump or return, so nothing falls through.

Not yet: calls, exits, stack slots (plan step 3).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe
namespace Rega

variable {I : Isa}

/-- The symbolic register file: which registers hold which names or constants. -/
abbrev SymRegs (I : Isa) := List (Arg Nat × I.Reg)

/-- Hint: where a join point expects its live values and its parameters. -/
structure Entry (I : Isa) where
  live : SymRegs I
  ploc : List I.Reg

/-- Untrusted allocation hints. Names and labels are numbered in the order `lower` meets them. -/
structure Hints (I : Isa) where
  dest : Nat → Option I.Reg
  entry : Nat → Entry I

/-- Lowering state. `PL`: registers of the parameters still to be bound; `pend`: labels declared and
not yet defined by a `block` (mirrors the `acc` argument of `wp`). -/
structure St (I : Isa) where
  nv : Nat
  nl : Nat
  R : SymRegs I
  PL : List I.Reg
  pend : List Nat

/-- Result: code, next fresh name, next fresh label. -/
abbrev Res (I : Isa) := Except String (List I.Directive × Nat × Nat)

/-- Decimal digits of `n`, prepended to `acc`. (`Nat.toDigits` does not reduce by `rfl` in modules.) -/
def natDigits : Nat → Nat → List Char → List Char
  | 0, _, acc => acc
  | fuel + 1, n, acc =>
    let acc := Char.ofNat (48 + n % 10) :: acc
    if n < 10 then acc else natDigits fuel (n / 10) acc

/-- Assembly name of label number `n` in function `fn`. -/
def lname (fn : String) (n : Nat) : String := fn ++ ".L" ++ String.ofList (natDigits (n + 1) n [])

/-- A register holding name `x`, if any. -/
def lookup (R : SymRegs I) (x : Nat) : Option I.Reg :=
  (R.find? (fun p => p.1 == .var x)).map (·.2)

/-- An operand as a snippet operand: a variable must be in a non-scratch register. -/
def argReg (R : SymRegs I) : Arg Nat → Option (Arg I.Reg)
  | .var x =>
    match lookup R x with
    | some r => if r ∈ I.scratch then none else some (.var r)
    | none => none
  | .imm c => some (.imm c)

def opRegs (R : SymRegs I) : Op Nat → Option (Op I.Reg)
  | .bin k o a b =>
    match argReg R a, argReg R b with
    | some a, some b => some (.bin k o a b)
    | _, _ => none
  | .cmp k o a b =>
    match argReg R a, argReg R b with
    | some a, some b => some (.cmp k o a b)
    | _, _ => none
  | .ext k s sg a =>
    match argReg R a with
    | some a => some (.ext k s sg a)
    | none => none
  | .copy k a =>
    match argReg R a with
    | some a => some (.copy k a)
    | none => none

/-- After a snippet that wrote `d` (if any) and the scratch registers. -/
def clob (d : Option I.Reg) (R : SymRegs I) : SymRegs I :=
  R.filter (fun p => decide (some p.2 ≠ d) && decide (p.2 ∉ I.scratch))

/-- Name `x` (fresh) now lives in `r`. Stale entries for `x` (from a bad hint) are dropped. -/
def bindN (x : Nat) (r : I.Reg) (R : SymRegs I) : SymRegs I :=
  (.var x, r) :: R.filter (fun p => p.1 != .var x)

/-- A move `rd := src`. -/
abbrev Move (I : Isa) := I.Reg × Arg I.Reg

def Move.code : Move I → List I.Directive
  | (d, .var s) => I.mov d s
  | (d, .imm c) => I.movi d c

/-- Symbolic effect of a move. -/
def movSym : Move I → SymRegs I → SymRegs I
  | (d, .var s), R =>
    if d = s then R else
      (R.filter (fun p => decide (p.2 = s))).map (fun p => (p.1, d)) ++
        R.filter (fun p => decide (p.2 ≠ d))
  | (d, .imm c), R => (.imm c, d) :: clob (some d) R

/-- Execute moves symbolically; every destination must be allocatable or scratch (a scratch
register may hold a temporary that breaks a cycle). -/
def execMoves : List (Move I) → SymRegs I → Option (SymRegs I)
  | [], R => some R
  | mv :: mvs, R =>
    if mv.1 ∈ I.allocatable ∨ mv.1 ∈ I.scratch then execMoves mvs (movSym mv R) else none

def movesCode : List (Move I) → List I.Directive
  | [] => []
  | mv :: mvs => mv.code ++ movesCode mvs

/-! ### Untrusted parallel moves -/

/-- Source operand for target content `a` in `R`. -/
def srcOf (R : SymRegs I) : Arg Nat → Option (Arg I.Reg)
  | .imm c => some (.imm c)
  | .var x => (lookup R x).map .var

/-- Writing `d` would destroy the only copy of a value some other pending target still needs. -/
def blocked (R : SymRegs I) (pending : SymRegs I) (d : I.Reg) : Bool :=
  pending.any fun (a, d') =>
    decide (d' ≠ d) &&
    match a with
    | .var y => R.all (fun p => p.1 != .var y || decide (p.2 = d)) && R.any (fun p => p.1 == .var y)
    | .imm _ => false

/-- Sequentialise the moves into `tgts`. Untrusted: `lower` checks the outcome. Register-to-register
moves go first, in an order that never overwrites the last copy of a value still needed; a cycle is
broken by copying one register into a free scratch register; constants are loaded last. -/
def pmoveAux : Nat → SymRegs I → SymRegs I → List (Move I) → List (Move I)
  | 0, _, _, acc => acc.reverse
  | fuel + 1, R, pending, acc =>
    match pending.filter (fun t => decide (t ∉ R)) with
    | [] => acc.reverse
    | pend =>
      let isVar : Arg Nat × I.Reg → Bool := fun t => match t.1 with | .var _ => true | .imm _ => false
      let step (a : Arg Nat) (d : I.Reg) : List (Move I) :=
        match srcOf R a with
        | some src => pmoveAux fuel (movSym (d, src) R) pend ((d, src) :: acc)
        | none => acc.reverse
      match pend.find? (fun t => isVar t && !blocked R pend t.2) with
      | some (a, d) => step a d
      | none =>
        match pend.find? isVar with
        | some (_, d) =>
          match I.scratch.find? (fun t => !blocked R pend t) with
          | some tmp => pmoveAux fuel (movSym (tmp, .var d) R) pend ((tmp, .var d) :: acc)
          | none => acc.reverse
        | none =>
          match pend.head? with
          | some (a, d) => step a d
          | none => acc.reverse

def pmove (R : SymRegs I) (tgts : SymRegs I) : List (Move I) :=
  pmoveAux (2 * tgts.length + 2) R tgts []

/-- Move into `tgts`, then check that every target holds. Returns the move code. -/
def shuffle (R : SymRegs I) (tgts : SymRegs I) : Option (List I.Directive) :=
  let mv := pmove R tgts
  match execMoves mv R with
  | some R' => if tgts.all (fun t => decide (t ∈ R')) then some (movesCode mv) else none
  | none => none

def prepend (pre : List I.Directive) : Res I → Res I
  | .ok (c, nv, nl) => .ok (pre ++ c, nv, nl)
  | .error e => .error e

/-! ### The lowering -/

/-- Lower a term. `fn` prefixes label names. -/
def lower (h : Hints I) (fn : String) : Expr Nat Nat → St I → Res I
  | .param f, st =>
    match st.PL with
    | [] => .error "param: no register left"
    | r :: PL => lower h fn (f st.nv) ⟨st.nv + 1, st.nl, bindN st.nv r st.R, PL, []⟩
  | .let_ op k, st =>
    match h.dest st.nv, opRegs st.R op with
    | some d, some o =>
      if d ∈ I.allocatable then
        match I.op o d with
        | some c =>
          prepend c (lower h fn (k st.nv)
            ⟨st.nv + 1, st.nl, bindN st.nv d (clob (some d) st.R), [], []⟩)
        | none => .error "let: no snippet"
      else .error "let: destination not allocatable"
    | _, _ => .error "let: operand or destination missing"
  | .load cl sz sg a k, st =>
    match h.dest st.nv, argReg st.R a with
    | some d, some a' =>
      if d ∈ I.allocatable then
        match I.load cl sz sg d a' with
        | some c =>
          prepend c (lower h fn (k st.nv)
            ⟨st.nv + 1, st.nl, bindN st.nv d (clob (some d) st.R), [], []⟩)
        | none => .error "load: no snippet"
      else .error "load: destination not allocatable"
    | _, _ => .error "load: operand or destination missing"
  | .store sz v a k, st =>
    match argReg st.R v, argReg st.R a with
    | some v', some a' =>
      match I.store sz v' a' with
      | some c => prepend c (lower h fn k ⟨st.nv, st.nl, clob none st.R, [], []⟩)
      | none => .error "store: no snippet"
    | _, _ => .error "store: operand missing"
  | .call _ _ _, _ => .error "call: not yet"
  | .jnz (.imm c) t e, st =>
    if Truthy c then lower h fn t ⟨st.nv, st.nl, st.R, [], []⟩
    else lower h fn e ⟨st.nv, st.nl, st.R, [], []⟩
  | .jnz (.var x) t e, st =>
    match argReg st.R (.var x) with
    | some (.var rc) =>
      match lower h fn e ⟨st.nv, st.nl + 1, clob none st.R, [], []⟩ with
      | .ok (ce, nv1, nl1) =>
        prepend (I.jnz rc (lname fn st.nl) ++ ce ++ [I.label (lname fn st.nl)])
          (lower h fn t ⟨nv1, nl1, clob none st.R, [], []⟩)
      | .error err => .error err
    | _ => .error "jnz: operand missing"
  | .jump j as, st =>
    let E := h.entry j
    let tgts := E.live ++ as.zip E.ploc
    if as.length = E.ploc.length ∧ tgts.all (fun t => decide (t.2 ∉ I.scratch)) then
      match shuffle st.R tgts with
      | some c => .ok (c ++ I.jmp (lname fn j), st.nv, st.nl)
      | none => .error "jump: entry map not met"
    else .error "jump: arity or scratch register in entry map"
  | .ret vs, st =>
    if vs.length ≤ I.retRegs.length then
      match shuffle st.R (vs.zip I.retRegs) with
      | some c => .ok (c ++ I.ret, st.nv, st.nl)
      | none => .error "ret: results not placed"
    else .error "ret: too many results"
  | .exit _ _, _ => .error "exit: not yet"
  | .hlt, st => .ok ([], st.nv, st.nl)
  | .label f, st => lower h fn (f st.nl) ⟨st.nv, st.nl + 1, st.R, st.PL, st.pend ++ [st.nl]⟩
  | .block b rest, st =>
    match st.pend with
    | [] => .error "block: no pending label"
    | ℓ :: pend =>
      match lower h fn rest ⟨st.nv, st.nl, st.R, st.PL, pend⟩ with
      | .ok (cr, nv1, nl1) =>
        prepend (cr ++ [I.label (lname fn ℓ)])
          (lower h fn b ⟨nv1, nl1, (h.entry ℓ).live, (h.entry ℓ).ploc, []⟩)
      | .error err => .error err

/-- Initial state of a function body: parameters in the argument registers. -/
def St.init (I : Isa) : St I := ⟨0, 0, [], I.argRegs, []⟩

/-- Lower a function: its label, then its body. -/
def lowerFn (h : Hints I) (f : Fn) : Except String (List I.Directive) :=
  match lower h f.name (f.body Nat Nat) (St.init I) with
  | .ok (c, _, _) => .ok (I.label f.name :: c)
  | .error e => .error e

end Rega
end LeanQbe
