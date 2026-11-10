module

public import LeanQbe.Flat

/-!
# Parsing QBE IL text (integer subset) into the PHOAS term

Untrusted front end, so that QBE's own `test/*.ssa` programs can be fed through our pipeline and
compared. It produces a `Flat` term and the function `fun V L => denote V L flat [] 0 [] 0`, whose `Wf`
is `denote_wf` (no per-program proof).

Supported: `function` definitions with `w`/`l` parameters and result; instructions on temporaries of
class `w`/`l`: the binary operations, comparisons, `ext*`, `copy`, `load*`, `store*`, `call $f(…)` with
zero or one result; `phi`; `jmp`, `jnz`, `ret`, `hlt`, fall-through between blocks; non-SSA input
(a temporary assigned several times). `$sym` operands become calls to an external
`addrFn sym` (the IL has no symbol operands). Not supported (an error naming the construct): `alloc*`,
floating point, aggregates, varargs, `neg`, thread-local data. `data` definitions are skipped, so a test
whose code uses its own data fails to link rather than to parse.

Translation (D4: join points instead of phis): every block becomes a join point of one mutually recursive
group, whose parameters are *all* the temporaries of the function, in a fixed order. A jump passes the
current value of every temporary, except that the target's `phi`s pick the value for this predecessor.
The entry jumps to the first block with the function parameters and `0` for the other temporaries.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.Parse

inductive Tok
  | tmp (s : String)   -- %x
  | lbl (s : String)   -- @x
  | glo (s : String)   -- $x
  | id (s : String)    -- function, w, add, …
  | num (i : Int)
  | str (s : String)
  | sym (c : Char)     -- ( ) { } , = : + …
  | nl
  deriving Repr, BEq, Inhabited

def isIdChar (c : Char) : Bool := c.isAlphanum || c == '_' || c == '.'

partial def lexIdent (cs : List Char) (acc : String) : String × List Char :=
  match cs with
  | c :: cs' => if isIdChar c then lexIdent cs' (acc.push c) else (acc, cs)
  | [] => (acc, [])

partial def lexNum (cs : List Char) (acc : Nat) : Nat × List Char :=
  match cs with
  | c :: cs' => if c.isDigit then lexNum cs' (acc * 10 + (c.toNat - '0'.toNat)) else (acc, cs)
  | [] => (acc, [])

partial def lexStr (cs : List Char) (acc : String) : String × List Char :=
  match cs with
  | '"' :: cs' => (acc, cs')
  | '\\' :: c :: cs' => lexStr cs' ((acc.push '\\').push c)
  | c :: cs' => lexStr cs' (acc.push c)
  | [] => (acc, [])

partial def lex (cs : List Char) (acc : Array Tok) : Except String (Array Tok) :=
  match cs with
  | [] => .ok acc
  | '#' :: cs' => lex (cs'.dropWhile (· != '\n')) acc
  | '\n' :: cs' => lex cs' (acc.push .nl)
  | '%' :: cs' => let (s, r) := lexIdent cs' ""; lex r (acc.push (.tmp s))
  | '@' :: cs' => let (s, r) := lexIdent cs' ""; lex r (acc.push (.lbl s))
  | '$' :: cs' => let (s, r) := lexIdent cs' ""; lex r (acc.push (.glo s))
  | '"' :: cs' => let (s, r) := lexStr cs' ""; lex r (acc.push (.str s))
  | '-' :: c :: cs' =>
    if c.isDigit then let (n, r) := lexNum (c :: cs') 0; lex r (acc.push (.num (-(n : Int))))
    else lex (c :: cs') (acc.push (.sym '-'))
  | c :: cs' =>
    if c == ' ' || c == '\t' || c == '\r' then lex cs' acc
    else if c.isDigit then let (n, r) := lexNum (c :: cs') 0; lex r (acc.push (.num n))
    else if c.isAlpha || c == '_' then let (s, r) := lexIdent (c :: cs') ""; lex r (acc.push (.id s))
    else lex cs' (acc.push (.sym c))

/-! ## Abstract syntax -/

/-- An operand: a temporary or an integer constant. -/
inductive POp
  | tmp (s : String)
  | imm (v : Val)
  /-- `$s`: the address of a global, obtained by calling `addrFn s` (see `addrFn`). -/
  | glo (s : String)
  deriving Repr, Inhabited, BEq

inductive PIns
  | assign (x : String) (k : Cls) (op : String) (args : List POp)
  | call (x : Option String) (f : String) (args : List POp)
  | store (sz : Sz) (v a : POp)
  deriving Repr, Inhabited

inductive PJmp
  | jmp (l : String)
  | jnz (c : POp) (t e : String)
  | ret (v : Option POp)
  | hlt
  | fall
  deriving Repr, Inhabited

structure PBlk where
  label : String
  phis : List (String × List (String × POp)) := []
  ins : Array PIns := #[]
  jmp : PJmp := .fall
  deriving Repr, Inhabited

structure PFn where
  name : String
  params : List String
  blocks : Array PBlk
  deriving Repr, Inhabited

/-! ## Parser (recursive descent over tokens; newlines separate statements) -/

abbrev P := StateT (List Tok) (Except String)

def peek : P (Option Tok) := do return (← get).head?
def next : P Tok := do
  match ← get with
  | t :: ts => set ts; return t
  | [] => throw "unexpected end of input"
def skipNl : P Unit := modify fun ts => ts.dropWhile (· == .nl)
def expectSym (c : Char) : P Unit := do
  match ← next with
  | .sym c' => if c == c' then pure () else throw s!"expected '{c}', got '{c'}'"
  | t => throw s!"expected '{c}', got {repr t}"
def trySym (c : Char) : P Bool := do
  match ← peek with
  | some (.sym c') => if c == c' then do let _ ← next; return true else return false
  | _ => return false

def cls (s : String) : Except String Cls :=
  match s with
  | "w" => .ok .w
  | "l" => .ok .l
  | _ => .error s!"unsupported class {s} (integer subset: w, l)"

def operand : P POp := do
  match ← next with
  | .tmp s => return .tmp s
  | .num i => return .imm (BitVec.ofInt 64 i)
  | .glo s => return .glo s
  | t => throw s!"expected an operand, got {repr t}"

partial def operands (acc : Array POp) : P (List POp) := do
  match ← peek with
  | some .nl | some (.sym '}') | none => return acc.toList
  | _ =>
    let o ← operand
    if ← trySym ',' then operands (acc.push o) else return (acc.push o).toList

/-- `(k a, k b, …)` in calls. -/
partial def callArgs (acc : Array POp) : P (List POp) := do
  if ← trySym ')' then return acc.toList
  match ← next with
  | .id k =>
    let _ ← liftM (m := Except String) (cls k)
    let o ← operand
    let _ ← trySym ','
    callArgs (acc.push o)
  | t => throw s!"unsupported call argument {repr t}"

partial def phiArgs (acc : Array (String × POp)) : P (List (String × POp)) := do
  match ← peek with
  | some (.lbl l) =>
    let _ ← next
    let o ← operand
    let _ ← trySym ','
    phiArgs (acc.push (l, o))
  | _ => return acc.toList

def storeSz (s : String) : Option Sz :=
  match s with
  | "storeb" => some .b | "storeh" => some .h | "storew" => some .w | "storel" => some .l
  | _ => none

/-- Parse statements of a function body until `}`. -/
partial def body (blks : Array PBlk) (cur : Option PBlk) : P (Array PBlk) := do
  skipNl
  let close (b : Option PBlk) : Array PBlk := match b with | some b => blks.push b | none => blks
  match ← next with
  | .sym '}' => return close cur
  | .lbl l => body (close cur) (some { label := l })
  | t =>
    let some b := cur | throw "instruction before the first label"
    match b.jmp with
    | .fall => pure ()
    | _ => throw s!"instruction after a jump in @{b.label} (QBE needs a label here)"
    match t with
    | .tmp x =>
      expectSym '='
      let .id k ← next | throw "expected a class after '='"
      let k' ← liftM (m := Except String) (cls k)
      match ← next with
      | .id "phi" =>
        let as ← phiArgs #[]
        body blks (some { b with phis := b.phis ++ [(x, as)] })
      | .id "call" =>
        let .glo f ← next | throw "expected $function after call"
        expectSym '('
        let as ← callArgs #[]
        body blks (some { b with ins := b.ins.push (.call (some x) f as) })
      | .id op =>
        let as ← operands #[]
        body blks (some { b with ins := b.ins.push (.assign x k' op as) })
      | t => throw s!"expected an operation, got {repr t}"
    | .id "call" =>
      let .glo f ← next | throw "expected $function after call"
      expectSym '('
      let as ← callArgs #[]
      body blks (some { b with ins := b.ins.push (.call none f as) })
    | .id "jmp" =>
      let .lbl l ← next | throw "expected @label after jmp"
      body blks (some { b with jmp := .jmp l })
    | .id "jnz" =>
      let c ← operand
      expectSym ','
      let .lbl t ← next | throw "expected @label in jnz"
      expectSym ','
      let .lbl e ← next | throw "expected @label in jnz"
      body blks (some { b with jmp := .jnz c t e })
    | .id "ret" =>
      match ← peek with
      | some .nl | some (.sym '}') => body blks (some { b with jmp := .ret none })
      | _ => let o ← operand; body blks (some { b with jmp := .ret (some o) })
    | .id "hlt" => body blks (some { b with jmp := .hlt })
    | .id s =>
      match storeSz s with
      | some sz =>
        let v ← operand
        expectSym ','
        let a ← operand
        body blks (some { b with ins := b.ins.push (.store sz v a) })
      | none => throw s!"unsupported statement {s}"
    | t => throw s!"unexpected {repr t}"

partial def params (acc : Array String) : P (List String) := do
  if ← trySym ')' then return acc.toList
  match ← next with
  | .id k =>
    let _ ← liftM (m := Except String) (cls k)
    let .tmp x ← next | throw "expected %param"
    let _ ← trySym ','
    params (acc.push x)
  | t => throw s!"unsupported parameter {repr t}"

/-- Skip a `data` or `type` definition (up to its closing brace). -/
partial def skipDef (depth : Nat) : P Unit := do
  match ← next with
  | .sym '{' => skipDef (depth + 1)
  | .sym '}' => if depth ≤ 1 then pure () else skipDef (depth - 1)
  | _ => skipDef depth

partial def file (acc : Array PFn) : P (Array PFn) := do
  skipNl
  match ← peek with
  | none => return acc
  | some (.id "export") => let _ ← next; file acc
  | some (.id "data") | some (.id "type") => skipDef 0; file acc
  | some (.id "function") =>
    let _ ← next
    -- optional result class
    let t ← next
    let name ← match t with
      | .glo f => pure f
      | .id k => do
        let _ ← liftM (m := Except String) (cls k)
        let .glo f ← next | throw "expected $name"
        pure f
      | t => throw s!"unsupported function header {repr t}"
    expectSym '('
    let ps ← params #[]
    skipNl
    expectSym '{'
    let blks ← body #[] none
    file (acc.push { name, params := ps, blocks := blks })
  | some t => throw s!"unexpected top-level {repr t}"

/-! ## Translation to `Flat` -/

structure Env where
  /-- temporary ↦ operand (level or constant) -/
  vals : List (String × Arg Nat)
  /-- next value level -/
  nv : Nat

def Env.get (e : Env) (x : String) : Except String (Arg Nat) :=
  match e.vals.lookup x with
  | some a => .ok a
  | none => .error s!"unknown temporary %{x}"

def Env.op (e : Env) : POp → Except String (Arg Nat)
  | .tmp x => e.get x
  | .imm v => .ok (.imm v)
  | .glo s => e.get ("$" ++ s)

/-- The address of global `$s` is the result of calling this function (the IL has no symbol
operands); the test driver links a C definition `void *addrFn_s(void) { return &s; }`. -/
def addrFn (s : String) : String := "leanqbe_addr_" ++ s

def globalsOf (ops : List POp) : List String :=
  (ops.filterMap fun | .glo s => some s | _ => none).eraseDups

/-- Bind the globals of `ops` (by calls to `addrFn`) before `k`. -/
def withGlobals (ops : List POp) (e : Env) (k : Env → Except String Flat) : Except String Flat :=
  let rec go (gs : List String) (e : Env) : Except String Flat :=
    match gs with
    | [] => k e
    | g :: gs =>
      if (e.vals.lookup ("$" ++ g)).isSome then go gs e
      else do
        let e' : Env := { vals := ("$" ++ g, .var e.nv) :: e.vals, nv := e.nv + 1 }
        return .call (addrFn g) [] (.param (← go gs e'))
  go (globalsOf ops) e

def binOp (s : String) : Option BinOp :=
  match s with
  | "add" => some .add | "sub" => some .sub | "mul" => some .mul | "div" => some .div
  | "rem" => some .rem | "udiv" => some .udiv | "urem" => some .urem | "and" => some .and
  | "or" => some .or | "xor" => some .xor | "sar" => some .sar | "shr" => some .shr
  | "shl" => some .shl | _ => none

def cmpOp (s : String) : Option CmpOp :=
  match s with
  | "eq" => some .eq | "ne" => some .ne | "sle" => some .sle | "slt" => some .slt
  | "sge" => some .sge | "sgt" => some .sgt | "ule" => some .ule | "ult" => some .ult
  | "uge" => some .uge | "ugt" => some .ugt | _ => none

def szOf (c : Char) : Option Sz :=
  match c with
  | 'b' => some .b | 'h' => some .h | 'w' => some .w | 'l' => some .l | _ => none

/-- `%x =k op args` as an operation or a load. -/
def lowerAssign (k : Cls) (op : String) (as : List (Arg Nat)) :
    Except String (Sum (Op Nat) (Cls × Sz × Bool × Arg Nat)) := do
  let two : Except String (Arg Nat × Arg Nat) := match as with
    | [a, b] => .ok (a, b) | _ => .error s!"{op} takes two operands"
  let one : Except String (Arg Nat) := match as with
    | [a] => .ok a | _ => .error s!"{op} takes one operand"
  if let some o := binOp op then
    let (a, b) ← two; return .inl (.bin k o a b)
  if op == "copy" then
    return .inl (.copy k (← one))
  match op.toList with
  | ['e', 'x', 't', sg, c] =>
    let some s := szOf c | throw s!"unsupported {op}"
    unless sg == 's' || sg == 'u' do throw s!"unsupported {op}"
    return .inl (.ext k s (sg == 's') (← one))
  | 'l' :: 'o' :: 'a' :: 'd' :: rest =>
    let (sg, c) ← match rest with
      | [c] => pure (true, c)
      | ['s', c] => pure (true, c)
      | ['u', c] => pure (false, c)
      | _ => throw s!"unsupported {op}"
    let some s := szOf c | throw s!"unsupported {op}"
    return .inr (k, s, sg, ← one)
  | 'c' :: rest =>
    let some kc := rest.getLast? | throw s!"unsupported {op}"
    let some o := cmpOp (String.ofList rest.dropLast) | throw s!"unsupported {op}"
    let kk ← cls (String.singleton kc)
    let (a, b) ← two
    return .inl (.cmp kk o a b)
  | _ => throw s!"unsupported operation {op}"

/-- The body of a block, from its environment: instructions, then the terminator. -/
def lowerBlock (temps : List String) (lbls : List String) (blks : Array PBlk) (i : Nat) (b : PBlk)
    (e : Env) : Except String Flat := do
  let labelOf (l : String) : Except String Nat :=
    match lbls.idxOf? l with
    | some j => .ok j
    | none => .error s!"unknown label @{l}"
  let phiOps (l : String) : List POp :=
    match lbls.idxOf? l with
    | some j => blks[j]!.phis.filterMap fun (_, ins) => ins.lookup b.label
    | none => []
  let jumpTo (e : Env) (l : String) : Except String Flat := do
    let j ← labelOf l
    let tgt := blks[j]!
    let args ← temps.mapM fun t =>
      match tgt.phis.lookup t with
      | some ins =>
        match ins.lookup b.label with
        | some o => e.op o
        | none => .error s!"phi for %{t} in @{l} has no entry for @{b.label}"
      | none => e.get t
    return .jump j args
  -- instructions, innermost last: build a list of "wrappers" then fold
  let rec go (ins : List PIns) (e : Env) : Except String Flat := do
    match ins with
    | [] =>
      let jops : List POp := match b.jmp with
        | .jnz c t f => c :: (phiOps t ++ phiOps f)
        | .jmp l => phiOps l
        | .fall => (match lbls[i + 1]? with | some l => phiOps l | none => [])
        | .ret (some o) => [o]
        | _ => []
      withGlobals jops e fun e =>
      match b.jmp with
      | .jmp l => jumpTo e l
      | .jnz c t f => return .jnz (← e.op c) (← jumpTo e t) (← jumpTo e f)
      | .ret none => return .ret []
      | .ret (some o) => return .ret [← e.op o]
      | .hlt => return .hlt
      | .fall =>
        match lbls[i + 1]? with
        | some l => jumpTo e l
        | none => throw s!"last block @{b.label} falls off the function"
    | .assign x k op as :: rest =>
      withGlobals as e fun e => do
      let as ← as.mapM e.op
      let e' : Env := { vals := (x, .var e.nv) :: e.vals, nv := e.nv + 1 }
      match ← lowerAssign k op as with
      | .inl o => return .let_ o (← go rest e')
      | .inr (c, s, sg, a) => return .load c s sg a (← go rest e')
    | .call x f as :: rest =>
      withGlobals as e fun e => do
      let as ← as.mapM e.op
      match x with
      | some x =>
        let e' : Env := { vals := (x, .var e.nv) :: e.vals, nv := e.nv + 1 }
        return .call f as (.param (← go rest e'))
      | none => return .call f as (← go rest e)
    | .store sz v a :: rest =>
      withGlobals [v, a] e fun e => do
      return .store sz (← e.op v) (← e.op a) (← go rest e)
  go b.ins.toList e

/-- Temporaries referenced by an operand list. -/
def opsTmps (ops : List POp) : List String :=
  ops.filterMap fun | .tmp x => some x | _ => none

/-- Temporaries defined in a block (excluding phis). -/
def blkDefs (b : PBlk) : List String :=
  b.ins.toList.filterMap fun
    | .assign x .. => some x | .call (some x) .. => some x | _ => none

/-- Temporaries used in a block (instructions, terminator, and outgoing phi operands). -/
def blkUses (blks : Array PBlk) (b : PBlk) : List String :=
  let insU := b.ins.toList.flatMap fun
    | .assign _ _ _ as => opsTmps as
    | .call _ _ as => opsTmps as
    | .store _ v a => opsTmps [v, a]
  let jmpU := match b.jmp with
    | .jnz c _ _ => opsTmps [c]
    | .ret (some o) => opsTmps [o]
    | _ => []
  let phiU := blks.toList.flatMap fun tgt =>
    tgt.phis.filterMap (fun (_, ins) => ins.lookup b.label) |> opsTmps
  insU ++ jmpU ++ phiU

def lowerFn (f : PFn) : Except String Flat := do
  let p := f.params.length
  let allPhiDefs := f.blocks.toList.flatMap fun b => b.phis.map (·.1)
  let allInsDefs := f.blocks.toList.flatMap blkDefs
  let allDefs := allPhiDefs ++ allInsDefs
  -- A temporary needs to be carried as a block parameter iff it is not a (single-assigned) function
  -- parameter and is either a phi, assigned more than once, or used outside the block that defines it.
  let isCross (t : String) : Bool :=
    let defCount := (if f.params.contains t then 1 else 0) + (allDefs.filter (· == t)).length
    if defCount > 1 || allPhiDefs.contains t then true
    else if f.params.contains t then false
    else
      f.blocks.toList.any fun b =>
        !(blkDefs b).contains t && (blkUses f.blocks b).contains t
  let temps := (f.params ++ allDefs).eraseDups.filter isCross
  let T := temps.length
  let lbls := f.blocks.toList.map (·.label)
  if lbls.isEmpty then throw s!"function ${f.name} has no blocks"
  let paramBindings := f.params.zipIdx.map fun (t, j) => (t, Arg.var j)
  let crossBindings := temps.zipIdx.map fun (t, j) => (t, Arg.var (p + j))
  let blockEnv : Env := { vals := crossBindings ++ paramBindings, nv := p + T }
  let bodies ← (f.blocks.toList.zipIdx).mapM fun (b, i) => lowerBlock temps lbls f.blocks i b blockEnv
  let blocks := bodies.map fun bd => (List.range T).foldr (fun _ acc => Flat.param acc) bd
  let entryArgs := temps.map fun t =>
    match paramBindings.lookup t with
    | some a => a
    | none => .imm 0
  let group := blocks.foldr (fun b acc => Flat.block b acc) (Flat.jump 0 entryArgs)
  let labelled := lbls.foldr (fun _ acc => Flat.label acc) group
  return (List.range p).foldr (fun _ acc => Flat.param acc) labelled

/-- Parse a QBE IL file into functions (name, first-order term). -/
def parseFlat (src : String) : Except String (List (String × Flat)) := do
  let toks ← lex src.toList #[]
  let (fns, _) ← (file #[]).run toks.toList
  fns.toList.mapM fun f => do return (f.name, ← lowerFn f)

/-- One parsed function as our `Fn` (its `Wf` is `denote_wf`). -/
def toFn (f : String × Flat) : Fn := { name := f.1, body := fun V L => denote V L f.2 [] 0 [] 0 }

end LeanQbe.Parse
