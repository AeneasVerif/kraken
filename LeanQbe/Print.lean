module

public import LeanQbe.IL

/-!
# Printing to QBE IL text

Prints a function at `V := Nat`, `L := Nat` as QBE IL that stock QBE accepts, as a second opinion on
the operation semantics (plan section 2.5, step 3) and later as a baseline. Not trusted, not verified.

Translation of the constructs QBE does not have:

* Every value has class `l`. An operation of class `w` is printed at class `w` into a temporary, then
  zero-extended with `extuw`, which is exactly our semantics (decision D3).
* Join-point parameters: block `ℓ` reads its `i`-th parameter from the temporary `%L{ℓ}_p{i}`, and
  `jump ℓ(args)` assigns those temporaries first. QBE accepts temporaries defined more than once and
  builds SSA itself. Arguments never mention `%L…` temporaries (block bodies copy them into fresh
  `%v…` first), so the assignments are a correct parallel move.
* `jnz c` branches get fresh blocks `@j{n}`, and tests `%c{n} =w cnew c, 0` (see `go`). The entry
  block is `@start`.
* `exit $f(args)` is `call $f(args)` followed by `hlt`.
* At most one result: `ret` and the continuation of `call` with more than one value are rejected,
  as are junk shapes (`param` in the middle of a body, `block` with no pending label).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.Print

structure St where
  /-- next variable name -/
  nv : Nat := 0
  /-- next label name -/
  nl : Nat := 0
  /-- next `jnz` block name -/
  nj : Nat := 0
  /-- labels declared and not yet defined, oldest first -/
  acc : List Nat := []
  /-- arity of `ret`, once seen -/
  retArity : Option Nat := none
  out : Array String := #[]

abbrev M := StateT St (Except String)

def emit (s : String) : M Unit := modify fun st => { st with out := st.out.push s }
def ins (s : String) : M Unit := emit ("\t" ++ s)

def freshVar : M Nat := modifyGet fun st => (st.nv, { st with nv := st.nv + 1 })
def freshJ : M Nat := modifyGet fun st => (st.nj, { st with nj := st.nj + 1 })

def var (n : Nat) : String := s!"%v{n}"
def lbl (n : Nat) : String := s!"@L{n}"
def blockParam (l i : Nat) : String := s!"%L{l}_p{i}"

def arg : Arg Nat → String
  | .var v => var v
  | .imm c => toString c.toInt

def args (as : List (Arg Nat)) : String := ", ".intercalate (as.map fun a => "l " ++ arg a)

def loadName (s : Sz) (sg : Bool) : String :=
  match s, sg with
  | .b, true => "loadsb" | .b, false => "loadub"
  | .h, true => "loadsh" | .h, false => "loaduh"
  | .w, true => "loadsw" | .w, false => "loaduw"
  | .l, _ => "loadl"

def extName (s : Sz) (sg : Bool) : String :=
  match s, sg with
  | .b, true => "extsb" | .b, false => "extub"
  | .h, true => "extsh" | .h, false => "extuh"
  | .w, true => "extsw" | .w, false => "extuw"
  | .l, _ => "copy"

/-- Print `%v{x} = op`. A class-`w` operation is computed into a temporary and zero-extended:
`bin` at class `w` (QBE's 32-bit operation), `ext` at class `l` (QBE has no `extsw` at class `w`), and
`copy` at class `w` is `extuw` itself. Comparisons yield `0`/`1` and are printed at class `l`. -/
def letOp (x : Nat) : Op Nat → M Unit
  | .bin .l o a b => ins s!"{var x} =l {o.name} {arg a}, {arg b}"
  | .bin .w o a b => do
    ins s!"{var x}_w =w {o.name} {arg a}, {arg b}"
    ins s!"{var x} =l extuw {var x}_w"
  | .cmp k o a b => ins s!"{var x} =l c{o.name}{k.name} {arg a}, {arg b}"
  | .ext .l s sg a => ins s!"{var x} =l {extName s sg} {arg a}"
  | .ext .w s sg a => do
    ins s!"{var x}_l =l {extName s sg} {arg a}"
    ins s!"{var x} =l extuw {var x}_l"
  | .copy .l a => ins s!"{var x} =l copy {arg a}"
  | .copy .w a => ins s!"{var x} =l extuw {arg a}"

def setRet (n : Nat) : M Unit := do
  if n > 1 then throw s!"ret with {n} results: stock QBE returns at most one value"
  let st ← get
  match st.retArity with
  | none => set { st with retArity := some n }
  | some n' => if n ≠ n' then throw s!"ret arities {n'} and {n} in one function" else pure ()

/-- What the leading `param`s of the term being printed bind. -/
inductive Mode
  /-- nothing: a `param` here is junk -/
  | body
  /-- the parameters of the block of label `l`, starting with the `i`-th -/
  | blk (l i : Nat)
  /-- the result of `call $f(args)`, not printed yet -/
  | call (f : Sym) (as : List (Arg Nat))
  /-- a second result of the call to `f`: rejected -/
  | afterCall (f : Sym)

/-- Before an instruction that is not a `param`: print a pending result-less call. -/
def flush : Mode → M Unit
  | .call f as => ins s!"call ${f}({args as})"
  | _ => pure ()

/-- Print a body. -/
def go (mode : Mode) : Expr Nat Nat → M Unit
  | .param f => do
    match mode with
    | .body => throw "param in the middle of a body"
    | .afterCall g => throw s!"call ${g} with more than one result"
    | .blk l i =>
      let x ← freshVar
      ins s!"{var x} =l copy {blockParam l i}"
      go (.blk l (i + 1)) (f x)
    | .call g as =>
      let x ← freshVar
      ins s!"{var x} =l call ${g}({args as})"
      go (.afterCall g) (f x)
  | .let_ op k => do
    flush mode
    let x ← freshVar
    letOp x op
    go .body (k x)
  | .load c s sg a k => do
    flush mode
    let x ← freshVar
    match c with
    | .l => ins s!"{var x} =l {loadName s sg} {arg a}"
    | .w => do
      ins s!"{var x}_l =l {loadName s sg} {arg a}"
      ins s!"{var x} =l extuw {var x}_l"
    go .body (k x)
  | .store s v a k => do
    flush mode
    ins s!"store{s.name} {arg v}, {arg a}"
    go .body k
  | .call f as k => do
    flush mode
    go (.call f as) k
  | .jnz c t e => do
    flush mode
    let jt ← freshJ
    let je ← freshJ
    -- `jnz` tests the low 32 bits (`Truthy`), but stock QBE on amd64 reuses the flags of a 64-bit
    -- operation that defined `c` in the same block; an explicit `cnew` makes every target agree.
    ins s!"%c{jt} =w cnew {arg c}, 0"
    ins s!"jnz %c{jt}, @j{jt}, @j{je}"
    emit s!"@j{jt}"
    go .body t
    emit s!"@j{je}"
    go .body e
  | .jump j as => do
    flush mode
    let mut i := 0
    for a in as do
      ins s!"{blockParam j i} =l copy {arg a}"
      i := i + 1
    ins s!"jmp {lbl j}"
  | .ret vs => do
    flush mode
    setRet vs.length
    match vs with
    | [] => ins "ret"
    | v :: _ => ins s!"ret {arg v}"
  | .exit f as => do
    flush mode
    ins s!"call ${f}({args as})"
    ins "hlt"
  | .hlt => do
    flush mode
    ins "hlt"
  | .label f => do
    flush mode
    let l ← modifyGet fun st => (st.nl, { st with nl := st.nl + 1, acc := st.acc ++ [st.nl] })
    go .body (f l)
  | .block b rest => do
    flush mode
    let st ← get
    match st.acc with
    | [] => throw "block with no pending label"
    | l :: acc' =>
      set { st with acc := acc' }
      go .body rest
      modify fun st => { st with acc := [] }
      emit (lbl l)
      go (.blk l 0) b

/-- Function parameters: the leading `param`s of the body. -/
def goParams (ps : Array Nat) : Expr Nat Nat → M (Array Nat)
  | .param f => do
    let x ← freshVar
    goParams (ps.push x) (f x)
  | e => do
    go .body e
    return ps

/-- QBE IL text of one function, exported under its name. -/
def fn (f : Fn) : Except String String := do
  let (ps, st) ← (goParams #[] (f.body Nat Nat)).run { out := #["@start"] }
  let ret := match st.retArity with
    | some 1 => "l "
    | _ => ""
  let params := ", ".intercalate (ps.toList.map fun x => "l " ++ var x)
  return s!"export function {ret}${f.name}({params}) \{\n" ++ "\n".intercalate st.out.toList ++ "\n}\n"

/-- QBE IL text of several functions. -/
def module (fs : List Fn) : Except String String := do
  let ts ← fs.mapM fn
  return "\n".intercalate ts

end LeanQbe.Print
