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

/-- The symbolic location file: which locations hold which names or constants. -/
abbrev SymRegs (I : Isa) := List (Arg Nat × Loc I)

def locEq (a b : Loc I) : Bool :=
  match a, b with
  | .reg r, .reg r' => r == r'
  | .slot i, .slot j => i == j
  | _, _ => false

def argNatEq (a b : Arg Nat) : Bool :=
  match a, b with
  | .var x, .var y => x == y
  | .imm c, .imm d => c == d
  | _, _ => false

def symRegMem (t : Arg Nat × Loc I) (R : SymRegs I) : Bool :=
  R.any fun p => argNatEq p.1 t.1 && locEq p.2 t.2

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
  /-- Callee-saved registers preserved in extra frame slots `nslots .. nslots + saved.length - 1`. -/
  saved : List I.Reg := []

/-- Total number of 8-byte frame slots (spill slots plus callee-saved register slots). -/
def Hints.totalSlots (h : Hints I) : Nat := h.nslots + h.saved.length

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
    if argNatEq p.1 (.var x) then (match p.2 with | .reg r => some r | .slot _ => none) else none

/-- A location holding name `x`, if any (registers first). -/
def lookupLoc (R : SymRegs I) (x : Nat) : Option (Loc I) :=
  match lookup R x with
  | some r => some (.reg r)
  | none => (R.find? (fun p => argNatEq p.1 (.var x))).map (·.2)

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

/-- After a call: slot entries and saved callee-saved registers survive. -/
def afterCall (saved : List I.Reg) (R : SymRegs I) : SymRegs I :=
  R.filter fun p => match p.2 with | .slot _ => true | .reg r => decide (r ∈ saved)

/-- Name `x` (fresh) now lives in `r`. Stale entries for `x` (from a bad hint) are dropped. -/
def bindN (x : Nat) (r : I.Reg) (R : SymRegs I) : SymRegs I :=
  (.var x, .reg r) :: R.filter (fun p => !argNatEq p.1 (.var x))

/-- The entries of location `l`, copied to location `d`. -/
def copyTo (l d : Loc I) (R : SymRegs I) : SymRegs I :=
  (R.filter (fun p => locEq p.2 l)).map (fun p => (p.1, d))

def Move.code : Move I → List I.Directive
  | .mov d s => I.mov d s
  | .movi d c => I.movi d c
  | .ld d i => I.slotLd d i
  | .st i s => I.slotSt i s

/-- Symbolic effect of a move. -/
def movSym : Move I → SymRegs I → SymRegs I
  | .mov d s, R =>
    if d = s then R else copyTo (.reg s) (.reg d) R ++ R.filter (fun p => !locEq p.2 (.reg d))
  | .movi d c, R => (.imm c, .reg d) :: clob (some d) R
  | .ld d i, R => copyTo (.slot i) (.reg d) R ++ clob (some d) R
  | .st i s, R =>
    clob none (copyTo (.reg s) (.slot i) R ++ R.filter (fun p => !locEq p.2 (.slot i)))

/-- Is a move allowed (in a frame of `ns` spill slots and `saved` callee-saved registers)? -/
def Move.ok (ns : Nat) (saved : List I.Reg := []) : Move I → Bool
  | .mov d _ | .movi d _ => decide (d ∈ I.allocatable ∨ d ∈ saved ∨ d ∈ I.scratch)
  | .ld d i => decide (d ∈ I.allocatable ∨ d ∈ saved ∨ d ∈ I.scratch) && decide (i < ns)
  | .st i s => decide (s ∉ I.scratch) && decide (i < ns)

/-- Execute moves symbolically. -/
def execMoves (ns : Nat) (saved : List I.Reg := []) :
    List (Move I) → SymRegs I → Option (SymRegs I)
  | [], R => some R
  | mv :: mvs, R => if mv.ok ns saved then execMoves ns saved mvs (movSym mv R) else none

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
    !locEq d' d &&
    match a with
    | .var y =>
      R.all (fun p => !argNatEq p.1 (.var y) || locEq p.2 d) &&
        R.any (fun p => argNatEq p.1 (.var y))
    | .imm _ => false

/-- Sequentialise the moves into `tgts`. Untrusted: `lower` checks the outcome. Moves from locations
go first, in an order that never overwrites the last copy of a value still needed; a register cycle
is broken by copying one register into a free scratch register; constants are loaded last. -/
def pmoveAux : Nat → SymRegs I → SymRegs I → List (Move I) → List (Move I)
  | 0, _, _, acc => acc.reverse
  | fuel + 1, R, pending, acc =>
    match pending.filter (fun t => !symRegMem t R) with
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
def shuffle (ns : Nat) (saved : List I.Reg := []) (R : SymRegs I) (tgts : SymRegs I) :
    Option (List I.Directive × SymRegs I) :=
  let mv := pmove R tgts
  match execMoves ns saved mv R with
  | some R' => if tgts.all (fun t => symRegMem t R') then some (movesCode mv, R') else none
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

/-- Save callee-saved registers into slots `[base .. base + rs.length - 1]`. -/
def saveCs {I : Isa} (base : Nat) : List I.Reg → List I.Directive
  | [] => []
  | r :: rs => I.slotSt base r ++ saveCs (base + 1) rs

/-- Restore callee-saved registers from slots `[base .. base + rs.length - 1]`. -/
def restoreCs {I : Isa} (base : Nat) : List I.Reg → List I.Directive
  | [] => []
  | r :: rs => I.slotLd r base ++ restoreCs (base + 1) rs

/-- Negation of a comparison operator (`a o.neg b ↔ ¬ (a o b)`). -/
def _root_.LeanQbe.CmpOp.neg : CmpOp → CmpOp
  | .eq => .ne | .ne => .eq
  | .sle => .sgt | .slt => .sge | .sge => .slt | .sgt => .sle
  | .ule => .ugt | .ult => .uge | .uge => .ult | .ugt => .ule

/-- Execute pre-moves at `st.ip`, requiring `st.pend` to be empty. -/
def stepPre (h : Hints I) (st : St I) : Option (SymRegs I) :=
  if st.pend.isEmpty then execMoves h.nslots h.saved (h.pre st.ip) st.R else none

/-- If `e` is `.jump j as` and needs no moves from `R`, return `some j`. -/
def zeroMoveJump? (h : Hints I) (R : SymRegs I) : Expr Nat Nat → Option Nat
  | .jump j as =>
    let En := h.entry j
    let tgts := En.live ++ tgtsIn as En.ploc
    if as.length == En.ploc.length &&
        tgts.all (fun t => symRegMem t R &&
          match t.2 with | .reg r => decide (r ∉ I.scratch) | .slot _ => true)
    then some j else none
  | _ => none

/-- Label jumped to at the end of a straight-line sequence, if any. -/
def endsWithJump? : Expr Nat Nat → Option Nat
  | .jump j _ => some j
  | .let_ _ k | .load _ _ _ _ k | .param k => endsWithJump? (k 0)
  | .store _ _ _ k | .call _ _ k => endsWithJump? k
  | _ => none

/-- Untrusted branch layout choice `(inv, tgt?)`:
`inv = true` negates the branch condition and swaps the roles of `t` and `e`;
`tgt? = some j` threads a zero-move jump directly into the conditional branch. -/
def jnzMode (h : Hints I) (R : SymRegs I) (t e : Expr Nat Nat) (ft : Option Nat) :
    Bool × Option Nat :=
  match zeroMoveJump? h R t, zeroMoveJump? h R e with
  | some jt, some je => if ft == some jt then (true, some je) else (false, some jt)
  | some jt, none => (false, some jt)
  | none, some je => (true, some je)
  | none, none => (ft.isSome && endsWithJump? e == ft && endsWithJump? t != ft, none)

/-- Fused comparison state `(xf, cls, co, a', b')` from a preceding dest-less `let_ (.cmp ...)`. -/
abbrev Fused (I : Isa) := Option (Nat × Cls × CmpOp × Arg I.Reg × Arg I.Reg)

/-- Resolve the branch condition of `.jnz (.var x)`, either from `fused` or by testing `x ≠ 0`. -/
def jnzCond (h : Hints I) (x : Nat) (st : St I) :
    Fused I → Option (List I.Directive × SymRegs I × Cls × CmpOp × Arg I.Reg × Arg I.Reg)
  | some (xf, cls, co, a', b') =>
    if x == xf && (h.pre st.ip).isEmpty && st.pend.isEmpty then
      some ([], st.R, cls, co, a', b')
    else none
  | none =>
    match stepPre h st with
    | some R =>
      match argReg R (.var x) with
      | some (.var rc) => some (movesCode (h.pre st.ip), R, .w, .ne, .var rc, .imm 0)
      | _ => none
    | none => none

/-- Assemble one orientation of `jnz`, checking that a threaded jump lowered to `[]`. -/
def finishJnzBranch (I : Isa) (fn : String) (nl : Nat) (tgt? : Option Nat)
    (b_taken : Expr Nat Nat) (br c_ft c_taken : List I.Directive) (nv2 nl2 ip2 : Nat) : Res I :=
  match tgt? with
  | some j =>
    match b_taken with
    | .jump j' _ =>
      if j' == j && c_taken.isEmpty then .ok (br ++ c_ft, nv2, nl2, ip2)
      else .error "jnz: bad jump thread"
    | _ => .error "jnz: not a jump"
  | none =>
    .ok (br ++ c_ft ++ [I.label (lname fn nl)] ++ c_taken, nv2, nl2, ip2)

/-- Assemble the lowered branches of `jnz` according to `inv`. -/
def finishJnz (I : Isa) (fn : String) (nl : Nat) (inv : Bool) (tgt? : Option Nat)
    (t e : Expr Nat Nat) (br ce ct : List I.Directive) (nv2 nl2 ip2 : Nat) : Res I :=
  if inv then finishJnzBranch I fn nl tgt? e br ct ce nv2 nl2 ip2
  else finishJnzBranch I fn nl tgt? t br ce ct nv2 nl2 ip2

/-- Lower a term. `fn` prefixes label names.
`ft` is the optional label of the immediately following block, so a trailing `jump` to `ft` falls
through. `fused` carries `(xf, cls, co, a', b')` when a preceding `cmp` fuses into `jnz`. -/
def lower (h : Hints I) (E : Ext) (fn : String) :
    Expr Nat Nat → St I → (ft : Option Nat := none) → (fused : Fused I := none) → Res I
  | .param f, st, ft, none =>
    match st.PL, st.pend with
    | r :: PL, [] => lower h E fn (f st.nv) ⟨st.nv + 1, st.nl, st.ip, bindN st.nv r st.R, PL, []⟩ ft
    | _, _ => .error "param: no register left or pending label"
  | .let_ op k, st, ft, none =>
    match stepPre h st with
    | some R =>
      match h.dest st.nv, opRegs R op with
      | some d, some o =>
        if d ∈ I.allocatable ∨ d ∈ h.saved then
          match I.op o d with
          | some c =>
            prepend (movesCode (h.pre st.ip) ++ c) (lower h E fn (k st.nv)
              ⟨st.nv + 1, st.nl, st.ip + 1, bindN st.nv d (clob (some d) R), [], []⟩ ft)
          | none => .error "let: no snippet"
        else .error "let: destination not allocatable"
      | none, some (.cmp cls co a' b') =>
        prepend (movesCode (h.pre st.ip)) (lower h E fn (k st.nv)
          ⟨st.nv + 1, st.nl, st.ip + 1, R.filter (fun p => !argNatEq p.1 (.var st.nv)), [], []⟩
          ft (some (st.nv, cls, co, a', b')))
      | _, _ => .error "let: operand or destination missing"
    | none => .error "let: bad moves"
  | .load cl sz sg a k, st, ft, none =>
    match stepPre h st with
    | some R =>
      match h.dest st.nv, argReg R a with
      | some d, some a' =>
        if d ∈ I.allocatable ∨ d ∈ h.saved then
          match I.load cl sz sg d a' with
          | some c =>
            prepend (movesCode (h.pre st.ip) ++ c) (lower h E fn (k st.nv)
              ⟨st.nv + 1, st.nl, st.ip + 1, bindN st.nv d (clob (some d) R), [], []⟩ ft)
          | none => .error "load: no snippet"
        else .error "load: destination not allocatable"
      | _, _ => .error "load: operand or destination missing"
    | none => .error "load: bad moves"
  | .store sz v a k, st, ft, none =>
    match stepPre h st with
    | some R =>
      match argReg R v, argReg R a with
      | some v', some a' =>
        match I.store sz v' a' with
        | some c =>
          prepend (movesCode (h.pre st.ip) ++ c)
            (lower h E fn k ⟨st.nv, st.nl, st.ip + 1, clob none R, [], []⟩ ft)
        | none => .error "store: no snippet"
      | _, _ => .error "store: operand missing"
    | none => .error "store: bad moves"
  | .call g as k, st, ft, none =>
    match stepPre h st with
    | some R =>
      if g ∈ E.callees ∧ as.length ≤ I.argRegs.length then
        match shuffle h.nslots h.saved R (tgtsIn as I.argRegs) with
        | some (c, R') =>
          prepend (movesCode (h.pre st.ip) ++ c ++ I.call g)
            (lower h E fn k ⟨st.nv, st.nl, st.ip + 1, afterCall h.saved R', I.retRegs, []⟩ ft)
        | none => .error "call: arguments not placed"
      else .error "call: callee not allowed or too many arguments"
    | none => .error "call: bad moves"
  | .jnz (.imm c) t e, st, ft, none =>
    match stepPre h st with
    | some R =>
      prepend (movesCode (h.pre st.ip))
        (if Truthy c then lower h E fn t ⟨st.nv, st.nl, st.ip + 1, R, [], []⟩ ft
         else lower h E fn e ⟨st.nv, st.nl, st.ip + 1, R, [], []⟩ ft)
    | none => .error "jnz: bad moves"
  | .jnz (.var x) t e, st, ft, fused =>
    match jnzCond h x st fused with
    | none => .error "jnz: bad condition"
    | some (mvs, R, cls, co, a', b') =>
      let R' := clob none R
      let (inv, tgt?) := jnzMode h R' t e ft
      let lbl := tgt?.getD st.nl
      let ft_taken := match tgt? with | some j => some j | none => ft
      let ft_ft := match tgt? with | some _ => ft | none => some st.nl
      match I.jnzCmp cls (if inv then co.neg else co) a' b' (lname fn lbl) with
      | none => .error "jnz: no snippet"
      | some br =>
        match lower h E fn e ⟨st.nv, st.nl + 1, st.ip + 1, R', [], []⟩
            (if inv then ft_taken else ft_ft) with
        | .ok (ce, nv1, nl1, ip1) =>
          match lower h E fn t ⟨nv1, nl1, ip1, R', [], []⟩
              (if inv then ft_ft else ft_taken) with
          | .ok (ct, nv2, nl2, ip2) =>
            prepend mvs (finishJnz I fn st.nl inv tgt? t e br ce ct nv2 nl2 ip2)
          | .error err => .error err
        | .error err => .error err
  | .jump j as, st, ft, none =>
    match stepPre h st with
    | some R =>
      let En := h.entry j
      let tgts := En.live ++ tgtsIn as En.ploc
      if as.length = En.ploc.length ∧
          tgts.all (fun t => match t.2 with | .reg r => decide (r ∉ I.scratch) | .slot _ => true) then
        match shuffle h.nslots h.saved R tgts with
        | some (c, _) =>
          let jc := if ft == some j then [] else I.jmp (lname fn j)
          .ok (movesCode (h.pre st.ip) ++ c ++ jc, st.nv, st.nl, st.ip + 1)
        | none => .error "jump: entry map not met"
      else .error "jump: arity or scratch register in entry map"
    | none => .error "jump: bad moves"
  | .ret vs, st, _, none =>
    match stepPre h st with
    | some R =>
      if vs.length ≤ I.retRegs.length then
        match shuffle h.nslots h.saved R (tgtsIn vs I.retRegs) with
        | some (c, _) =>
          .ok (movesCode (h.pre st.ip) ++ c ++ restoreCs h.nslots h.saved ++
            I.epilogue h.totalSlots ++ I.ret, st.nv, st.nl, st.ip + 1)
        | none => .error "ret: results not placed"
      else .error "ret: too many results"
    | none => .error "ret: bad moves"
  | .exit g as, st, _, none =>
    match stepPre h st with
    | some R =>
      if g ∈ E.exits ∧ as.length ≤ I.argRegs.length then
        match shuffle h.nslots h.saved R (tgtsIn as I.argRegs) with
        | some (c, _) =>
          .ok (movesCode (h.pre st.ip) ++ c ++ restoreCs h.nslots h.saved ++
            I.epilogue h.totalSlots ++ I.tailJmp g, st.nv, st.nl, st.ip + 1)
        | none => .error "exit: arguments not placed"
      else .error "exit: target not allowed or too many arguments"
    | none => .error "exit: bad moves"
  | .hlt, st, _, none =>
    if st.pend.isEmpty then .ok ([], st.nv, st.nl, st.ip + 1) else .error "hlt: pending label"
  | .label f, st, ft, none =>
    lower h E fn (f st.nl) ⟨st.nv, st.nl + 1, st.ip, st.R, st.PL, st.pend ++ [st.nl]⟩ ft
  | .block b rest, st, ft, none =>
    match st.pend with
    | [] => .error "block: no pending label"
    | ℓ :: pend =>
      match lower h E fn rest ⟨st.nv, st.nl, st.ip, st.R, st.PL, pend⟩ (some ℓ) with
      | .ok (cr, nv1, nl1, ip1) =>
        prepend (cr ++ [I.label (lname fn ℓ)])
          (lower h E fn b ⟨nv1, nl1, ip1, (h.entry ℓ).live, (h.entry ℓ).ploc, []⟩ ft)
      | .error err => .error err
  | _, _, _, some _ => .error "unexpected fused cmp"

/-- Initial state of a function body: parameters in the argument registers. -/
def St.init (I : Isa) : St I := ⟨0, 0, 0, [], I.argRegs, []⟩

/-- Lower a function: its label, the prologue (plus saving callee-saved regs), then its body. -/
def lowerFn (h : Hints I) (E : Ext) (f : Fn) : Except String (List I.Directive) :=
  if h.saved.Nodup ∧ h.saved.all (fun r => decide (r ∈ I.calleeSaved)) then
    match lower h E f.name (f.body Nat Nat) (St.init I) with
    | .ok (c, _, _, _) =>
      .ok (I.label f.name :: (I.prologue h.totalSlots ++ saveCs h.nslots h.saved ++ c))
    | .error e => .error e
  else .error "callee-saved list invalid"

end Rega
end LeanQbe
