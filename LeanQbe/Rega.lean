module

public import LeanQbe.IL
public import LeanQbe.Abi

/-!
# Lowering from PHOAS to target directives (QBE `rega.c`, plus the parts of `emit.c` that place code)

`lower` is the verified exit of the compiler (plan section 2.2, decision D9). It is one structural
recursion over the IL term instantiated at `V := Nat` (names) and `L := Nat` (label numbers).

Its state is the next fresh name `nv`, the next fresh label `nl`, the next instruction number `ip`,
and a *symbolic location file* `R : List (Arg Nat × Loc)`: `(.var x, l) ∈ R` means "location `l`
(a register or a spill slot of the frame) holds the value of name `x`", `(.imm c, l) ∈ R` means "`l`
holds `c`". A relation, not a map: a value may sit in several locations, a location may hold several
names.

Hints come from an untrusted oracle (`Live`, `Spill`): a destination register per name, an entry map
per label, moves (spills, reloads, copies) before each instruction, and the number of spill slots.
The lowering never trusts them:

* an operand is read from a register in `R`; if it is not there, compilation fails;
* writing a location removes every entry for it (and every snippet removes the scratch registers);
* moves are executed symbolically and their destinations must be allocatable registers, scratch
  registers or slots of the frame;
* at `jump ℓ(args)`, `ret`, `call` and `exit`, an untrusted parallel-move pass computes moves, `lower`
  executes them symbolically and checks that `R` contains every entry the target expects;
* a block body is lowered from exactly its entry map; after a `call` only slot entries survive.

So the correctness proof (`RegaLemmas.lean`) has no liveness, interference or dominance argument.

Frame: every function starts with `prologue ns` and leaves through `epilogue ns` (then `ret` or
`tailJmp`). Code layout: `rest ++ [label ℓ] ++ body` for a block, `jnz c ℓ ++ else ++ [label ℓ] ++
then` for a conditional; every lowered term ends in a jump, return or exit, so nothing falls
through.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe
namespace Rega

variable {I : Isa}

/-- A location: a register, or spill slot `i` of the current frame. -/
inductive Loc (I : Isa) where
  | reg (r : I.Reg)
  | slot (i : Nat)

instance : DecidableEq (Loc I) := fun a b =>
  match a, b with
  | .reg r, .reg r' =>
    if h : r = r' then .isTrue (h ▸ rfl) else .isFalse (by intro e; cases e; exact h rfl)
  | .slot i, .slot j =>
    if h : i = j then .isTrue (h ▸ rfl) else .isFalse (by intro e; cases e; exact h rfl)
  | .reg _, .slot _ => .isFalse (by intro e; cases e)
  | .slot _, .reg _ => .isFalse (by intro e; cases e)

/-- The symbolic location file: which locations hold which names or constants. -/
abbrev SymRegs (I : Isa) := List (Arg Nat × Loc I)

/-- Hint: where a join point expects its live values (registers or slots) and its parameters
(registers). -/
structure Entry (I : Isa) where
  live : SymRegs I
  ploc : List I.Reg

/-- A move. -/
inductive Move (I : Isa) where
  /-- `d := s` -/
  | mov (d s : I.Reg)
  /-- `d := c` -/
  | movi (d : I.Reg) (c : Val)
  /-- `d := slot i` (reload) -/
  | ld (d : I.Reg) (i : Nat)
  /-- `slot i := s` (spill) -/
  | st (i : Nat) (s : I.Reg)

/-- Untrusted allocation hints. Names, labels and instructions are numbered in the order `lower`
meets them. -/
structure Hints (I : Isa) where
  dest : Nat → Option I.Reg
  entry : Nat → Entry I
  /-- Moves before instruction number `ip`. -/
  pre : Nat → List (Move I)
  /-- Spill slots of the frame. -/
  nslots : Nat

/-- Lowering state. `PL`: registers of the parameters still to be bound; `pend`: labels declared and
not yet defined by a `block` (mirrors the `acc` argument of `wp`). -/
structure St (I : Isa) where
  nv : Nat
  nl : Nat
  ip : Nat
  R : SymRegs I
  PL : List I.Reg
  pend : List Nat

/-- Result: code, next fresh name, next fresh label, next instruction number. -/
abbrev Res (I : Isa) := Except String (List I.Directive × Nat × Nat × Nat)

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
  R.findSome? fun p =>
    if p.1 == .var x then (match p.2 with | .reg r => some r | .slot _ => none) else none

/-- A location holding name `x`, if any (registers first). -/
def lookupLoc (R : SymRegs I) (x : Nat) : Option (Loc I) :=
  match lookup R x with
  | some r => some (.reg r)
  | none => (R.find? (fun p => p.1 == .var x)).map (·.2)

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

/-- Is this entry kept when register `d` (if any) and the scratch registers are written? -/
def keepAfter (d : Option I.Reg) : Loc I → Bool
  | .reg r => decide (some r ≠ d) && decide (r ∉ I.scratch)
  | .slot _ => true

/-- After a snippet that wrote `d` (if any) and the scratch registers. -/
def clob (d : Option I.Reg) (R : SymRegs I) : SymRegs I := R.filter (fun p => keepAfter d p.2)

/-- After a call: only slot entries survive (no callee-saved register is allocatable). -/
def slotsOnly (R : SymRegs I) : SymRegs I :=
  R.filter fun p => match p.2 with | .slot _ => true | .reg _ => false

/-- Name `x` (fresh) now lives in `r`. Stale entries for `x` (from a bad hint) are dropped. -/
def bindN (x : Nat) (r : I.Reg) (R : SymRegs I) : SymRegs I :=
  (.var x, .reg r) :: R.filter (fun p => p.1 != .var x)

/-- The entries of location `l`, copied to location `d`. -/
def copyTo (l d : Loc I) (R : SymRegs I) : SymRegs I :=
  (R.filter (fun p => decide (p.2 = l))).map (fun p => (p.1, d))

def Move.code : Move I → List I.Directive
  | .mov d s => I.mov d s
  | .movi d c => I.movi d c
  | .ld d i => I.slotLd d i
  | .st i s => I.slotSt i s

/-- Symbolic effect of a move. -/
def movSym : Move I → SymRegs I → SymRegs I
  | .mov d s, R =>
    if d = s then R else copyTo (.reg s) (.reg d) R ++ R.filter (fun p => decide (p.2 ≠ .reg d))
  | .movi d c, R => (.imm c, .reg d) :: clob (some d) R
  | .ld d i, R => copyTo (.slot i) (.reg d) R ++ clob (some d) R
  | .st i s, R =>
    clob none (copyTo (.reg s) (.slot i) R ++ R.filter (fun p => decide (p.2 ≠ .slot i)))

/-- Is a move allowed (in a frame of `ns` slots)? -/
def Move.ok (ns : Nat) : Move I → Bool
  | .mov d _ | .movi d _ => decide (d ∈ I.allocatable ∨ d ∈ I.scratch)
  | .ld d i => decide (d ∈ I.allocatable ∨ d ∈ I.scratch) && decide (i < ns)
  | .st i s => decide (s ∉ I.scratch) && decide (i < ns)

/-- Execute moves symbolically. -/
def execMoves (ns : Nat) : List (Move I) → SymRegs I → Option (SymRegs I)
  | [], R => some R
  | mv :: mvs, R => if mv.ok ns then execMoves ns mvs (movSym mv R) else none

def movesCode : List (Move I) → List I.Directive
  | [] => []
  | mv :: mvs => mv.code ++ movesCode mvs

/-! ### Untrusted parallel moves -/

/-- A move that puts the value `a` (found through `R`) into location `d`. -/
def moveFor (R : SymRegs I) (a : Arg Nat) : Loc I → Option (Move I)
  | .reg d =>
    match a with
    | .imm c => some (.movi d c)
    | .var x =>
      match lookupLoc R x with
      | some (.reg r) => some (.mov d r)
      | some (.slot i) => some (.ld d i)
      | none => none
  | .slot i =>
    match a with
    | .imm _ => none
    | .var x =>
      match lookup R x with
      | some r => if r ∈ I.scratch then none else some (.st i r)
      | none => none

/-- Writing `d` would destroy the only copy of a value some other pending target still needs. -/
def blocked (R : SymRegs I) (pending : SymRegs I) (d : Loc I) : Bool :=
  pending.any fun (a, d') =>
    decide (d' ≠ d) &&
    match a with
    | .var y => R.all (fun p => p.1 != .var y || decide (p.2 = d)) && R.any (fun p => p.1 == .var y)
    | .imm _ => false

/-- Sequentialise the moves into `tgts`. Untrusted: `lower` checks the outcome. Moves from locations
go first, in an order that never overwrites the last copy of a value still needed; a register cycle
is broken by copying one register into a free scratch register; constants are loaded last. -/
def pmoveAux : Nat → SymRegs I → SymRegs I → List (Move I) → List (Move I)
  | 0, _, _, acc => acc.reverse
  | fuel + 1, R, pending, acc =>
    match pending.filter (fun t => decide (t ∉ R)) with
    | [] => acc.reverse
    | pend =>
      let isVar : Arg Nat × Loc I → Bool := fun t => match t.1 with | .var _ => true | .imm _ => false
      let step (a : Arg Nat) (d : Loc I) : List (Move I) :=
        match moveFor R a d with
        | some mv => pmoveAux fuel (movSym mv R) pend (mv :: acc)
        | none => acc.reverse
      match pend.find? (fun t => isVar t && !blocked R pend t.2) with
      | some (a, d) => step a d
      | none =>
        match pend.find? (fun t => isVar t && match t.2 with | .reg _ => true | .slot _ => false) with
        | some (_, .reg d) =>
          match I.scratch.find? (fun t => !blocked R pend (.reg t)) with
          | some tmp => pmoveAux fuel (movSym (.mov tmp d) R) pend (.mov tmp d :: acc)
          | none => acc.reverse
        | _ =>
          match pend.head? with
          | some (a, d) => step a d
          | none => acc.reverse

def pmove (R : SymRegs I) (tgts : SymRegs I) : List (Move I) :=
  pmoveAux (2 * tgts.length + 2) R tgts []

/-- Move into `tgts`, then check that every target holds. Returns the move code and the new file. -/
def shuffle (ns : Nat) (R : SymRegs I) (tgts : SymRegs I) : Option (List I.Directive × SymRegs I) :=
  let mv := pmove R tgts
  match execMoves ns mv R with
  | some R' => if tgts.all (fun t => decide (t ∈ R')) then some (movesCode mv, R') else none
  | none => none

def prepend (pre : List I.Directive) : Res I → Res I
  | .ok (c, nv, nl, ip) => .ok (pre ++ c, nv, nl, ip)
  | .error e => .error e

/-- The registers of `regs` paired with the values `as` (targets of a shuffle). -/
def tgtsIn (as : List (Arg Nat)) (regs : List I.Reg) : SymRegs I :=
  as.zip (regs.map .reg)

/-! ### The lowering -/

/-- What a function may call and exit to. -/
structure Ext where
  callees : List String
  exits : List String

/-- Lower a term. `fn` prefixes label names. -/
def lower (h : Hints I) (E : Ext) (fn : String) : Expr Nat Nat → St I → Res I
  | .param f, st =>
    match st.PL with
    | [] => .error "param: no register left"
    | r :: PL => lower h E fn (f st.nv) ⟨st.nv + 1, st.nl, st.ip, bindN st.nv r st.R, PL, []⟩
  | .let_ op k, st =>
    match execMoves h.nslots (h.pre st.ip) st.R with
    | none => .error "let: bad moves"
    | some R =>
      match h.dest st.nv, opRegs R op with
      | some d, some o =>
        if d ∈ I.allocatable then
          match I.op o d with
          | some c =>
            prepend (movesCode (h.pre st.ip) ++ c) (lower h E fn (k st.nv)
              ⟨st.nv + 1, st.nl, st.ip + 1, bindN st.nv d (clob (some d) R), [], []⟩)
          | none => .error "let: no snippet"
        else .error "let: destination not allocatable"
      | _, _ => .error "let: operand or destination missing"
  | .load cl sz sg a k, st =>
    match execMoves h.nslots (h.pre st.ip) st.R with
    | none => .error "load: bad moves"
    | some R =>
      match h.dest st.nv, argReg R a with
      | some d, some a' =>
        if d ∈ I.allocatable then
          match I.load cl sz sg d a' with
          | some c =>
            prepend (movesCode (h.pre st.ip) ++ c) (lower h E fn (k st.nv)
              ⟨st.nv + 1, st.nl, st.ip + 1, bindN st.nv d (clob (some d) R), [], []⟩)
          | none => .error "load: no snippet"
        else .error "load: destination not allocatable"
      | _, _ => .error "load: operand or destination missing"
  | .store sz v a k, st =>
    match execMoves h.nslots (h.pre st.ip) st.R with
    | none => .error "store: bad moves"
    | some R =>
      match argReg R v, argReg R a with
      | some v', some a' =>
        match I.store sz v' a' with
        | some c =>
          prepend (movesCode (h.pre st.ip) ++ c)
            (lower h E fn k ⟨st.nv, st.nl, st.ip + 1, clob none R, [], []⟩)
        | none => .error "store: no snippet"
      | _, _ => .error "store: operand missing"
  | .call g as k, st =>
    match execMoves h.nslots (h.pre st.ip) st.R with
    | none => .error "call: bad moves"
    | some R =>
      if g ∈ E.callees ∧ as.length ≤ I.argRegs.length then
        match shuffle h.nslots R (tgtsIn as I.argRegs) with
        | some (c, R') =>
          prepend (movesCode (h.pre st.ip) ++ c ++ I.call g)
            (lower h E fn k ⟨st.nv, st.nl, st.ip + 1, slotsOnly R', I.retRegs, []⟩)
        | none => .error "call: arguments not placed"
      else .error "call: callee not allowed or too many arguments"
  | .jnz (.imm c) t e, st =>
    match execMoves h.nslots (h.pre st.ip) st.R with
    | none => .error "jnz: bad moves"
    | some R =>
      prepend (movesCode (h.pre st.ip))
        (if Truthy c then lower h E fn t ⟨st.nv, st.nl, st.ip + 1, R, [], []⟩
         else lower h E fn e ⟨st.nv, st.nl, st.ip + 1, R, [], []⟩)
  | .jnz (.var x) t e, st =>
    match execMoves h.nslots (h.pre st.ip) st.R with
    | none => .error "jnz: bad moves"
    | some R =>
      match argReg R (.var x) with
      | some (.var rc) =>
        match lower h E fn e ⟨st.nv, st.nl + 1, st.ip + 1, clob none R, [], []⟩ with
        | .ok (ce, nv1, nl1, ip1) =>
          prepend (movesCode (h.pre st.ip) ++ I.jnz rc (lname fn st.nl) ++ ce ++
              [I.label (lname fn st.nl)])
            (lower h E fn t ⟨nv1, nl1, ip1, clob none R, [], []⟩)
        | .error err => .error err
      | _ => .error "jnz: operand missing"
  | .jump j as, st =>
    match execMoves h.nslots (h.pre st.ip) st.R with
    | none => .error "jump: bad moves"
    | some R =>
      let En := h.entry j
      let tgts := En.live ++ tgtsIn as En.ploc
      if as.length = En.ploc.length ∧
          tgts.all (fun t => match t.2 with | .reg r => decide (r ∉ I.scratch) | .slot _ => true) then
        match shuffle h.nslots R tgts with
        | some (c, _) => .ok (movesCode (h.pre st.ip) ++ c ++ I.jmp (lname fn j), st.nv, st.nl,
            st.ip + 1)
        | none => .error "jump: entry map not met"
      else .error "jump: arity or scratch register in entry map"
  | .ret vs, st =>
    match execMoves h.nslots (h.pre st.ip) st.R with
    | none => .error "ret: bad moves"
    | some R =>
      if vs.length ≤ I.retRegs.length then
        match shuffle h.nslots R (tgtsIn vs I.retRegs) with
        | some (c, _) =>
          .ok (movesCode (h.pre st.ip) ++ c ++ I.epilogue h.nslots ++ I.ret, st.nv, st.nl,
            st.ip + 1)
        | none => .error "ret: results not placed"
      else .error "ret: too many results"
  | .exit g as, st =>
    match execMoves h.nslots (h.pre st.ip) st.R with
    | none => .error "exit: bad moves"
    | some R =>
      if g ∈ E.exits ∧ as.length ≤ I.argRegs.length then
        match shuffle h.nslots R (tgtsIn as I.argRegs) with
        | some (c, _) =>
          .ok (movesCode (h.pre st.ip) ++ c ++ I.epilogue h.nslots ++ I.tailJmp g, st.nv, st.nl,
            st.ip + 1)
        | none => .error "exit: arguments not placed"
      else .error "exit: target not allowed or too many arguments"
  | .hlt, st => .ok ([], st.nv, st.nl, st.ip + 1)
  | .label f, st =>
    lower h E fn (f st.nl) ⟨st.nv, st.nl + 1, st.ip, st.R, st.PL, st.pend ++ [st.nl]⟩
  | .block b rest, st =>
    match st.pend with
    | [] => .error "block: no pending label"
    | ℓ :: pend =>
      match lower h E fn rest ⟨st.nv, st.nl, st.ip, st.R, st.PL, pend⟩ with
      | .ok (cr, nv1, nl1, ip1) =>
        prepend (cr ++ [I.label (lname fn ℓ)])
          (lower h E fn b ⟨nv1, nl1, ip1, (h.entry ℓ).live, (h.entry ℓ).ploc, []⟩)
      | .error err => .error err

/-- Initial state of a function body: parameters in the argument registers. -/
def St.init (I : Isa) : St I := ⟨0, 0, 0, [], I.argRegs, []⟩

/-- Lower a function: its label, the prologue, then its body. -/
def lowerFn (h : Hints I) (E : Ext) (f : Fn) : Except String (List I.Directive) :=
  match lower h E f.name (f.body Nat Nat) (St.init I) with
  | .ok (c, _, _, _) => .ok (I.label f.name :: (I.prologue h.nslots ++ c))
  | .error e => .error e

end Rega
end LeanQbe
