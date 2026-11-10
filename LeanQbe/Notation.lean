module

public import LeanQbe.IL
public meta import Lean.Elab.Term

/-!
# QBE-flavoured notation for the IL

`qbe(%a, %b) { … }` is a function (its parameters, then its body) and `qbe { … }` a code fragment;
both elaborate to the PHOAS term `Expr V L` (for any `V L`, taken from the expected type). The syntax
follows QBE's IL text (`qbe/doc/il.txt`):

```
%x =l add %a, %b          %c =w ceql %x, 0         %v =l loadl %p        storel %v, %p
%r =l call $f(%a, 1)      call $g(%a)              exit $abort(%a)       hlt
jmp @loop(%x)             jnz %c, @t, @f(%y)       jnz %c, { … }, { … }  ret %x, %y
@loop(%x, %y) { … }       -- a join point; consecutive ones form one mutually recursive group
%r <- f(%a, %b)           -- a Lean function as a macro: `f a b fun r => …`
⟨e⟩                       -- splice a Lean term: `Arg V` as an operand, `Expr V L` as a tail
```

Differences from QBE's text, all forced by the PHOAS encoding (D1, D4):

* Blocks do not fall through. A function body is one block; branches are `jnz` with two targets, each a
  jump `@l(args)` or an inline block `{ … }`.
* Join points have parameters instead of `phi`s, and are scoped: `@l(%x) { body }` is visible in every
  block of its group and in the statements after the group, which are the group's entry.
* Labels and values are Lean binders, so shadowing follows Lean's scoping and a misspelt name is an
  elaboration error.
-/

set_option autoImplicit false

public section

namespace LeanQbe.Notation

open Lean

declare_syntax_cat qbe_arg
declare_syntax_cat qbe_param
declare_syntax_cat qbe_sym
declare_syntax_cat qbe_target
declare_syntax_cat qbe_stmt

/-- An operand: `%x`, a numeral, or `⟨t⟩` with `t : Arg V`. -/
syntax "%" noWs ident : qbe_arg
syntax num : qbe_arg
syntax "-" noWs num : qbe_arg
syntax "⟨" term "⟩" : qbe_arg

/-- A bound name `%x`. -/
syntax "%" noWs ident : qbe_param

/-- A global symbol `$f`. -/
syntax "$" noWs ident : qbe_sym

/-- A `jnz` target: a jump, or an inline block. -/
syntax "@" noWs ident ("(" qbe_arg,* ")")? : qbe_target
syntax "{" qbe_stmt* "}" : qbe_target

/-- `%x =k op a, b` (also `load…`, `call $f(…)`). -/
syntax "%" noWs ident " =" noWs ident ident qbe_arg,* : qbe_stmt
syntax "%" noWs ident " =" noWs ident "call " qbe_sym "(" qbe_arg,* ")" : qbe_stmt
/-- `store{l,w,h,b} v, a`. -/
syntax ident qbe_arg ", " qbe_arg : qbe_stmt
/-- A call without results. -/
syntax "call " qbe_sym "(" qbe_arg,* ")" : qbe_stmt
syntax "exit " qbe_sym "(" qbe_arg,* ")" : qbe_stmt
syntax "jmp " "@" noWs ident ("(" qbe_arg,* ")")? : qbe_stmt
syntax "jnz " qbe_arg ", " qbe_target ", " qbe_target : qbe_stmt
syntax "ret" (ppSpace qbe_arg),* : qbe_stmt
syntax "hlt" : qbe_stmt
/-- A join point. Consecutive ones form one group. -/
syntax "@" noWs ident "(" qbe_param,* ")" " {" qbe_stmt* "}" : qbe_stmt
/-- A Lean function as a macro, in continuation-passing style. -/
syntax "%" noWs ident " <- " ident "(" qbe_param,* ")" : qbe_stmt
/-- Splice a Lean term of type `Expr V L` as the tail. -/
syntax "⟨" term "⟩" : qbe_stmt

meta def expandArg : TSyntax `qbe_arg → MacroM Term
  | `(qbe_arg| %$x:ident) => `(LeanQbe.Arg.var $x)
  | `(qbe_arg| $n:num) => `(LeanQbe.Arg.imm $n)
  | `(qbe_arg| -$n:num) => `(LeanQbe.Arg.imm (-$n))
  | `(qbe_arg| ⟨$t⟩) => pure t
  | _ => Macro.throwUnsupported

meta def expandArgs (as : Syntax.TSepArray `qbe_arg ",") : MacroM Term := do
  let as ← as.getElems.mapM expandArg
  `([$as,*])

meta def paramIdent : TSyntax `qbe_param → MacroM Ident
  | `(qbe_param| %$x:ident) => pure x
  | _ => Macro.throwUnsupported

/-- `$f` parses as a pseudo-antiquotation node (`"$" [] f []`) outside quotations, so take the
identifier wherever it is. -/
meta def symName (s : TSyntax `qbe_sym) : MacroM Term := do
  let some f := s.raw.getArgs.find? (·.isIdent) | Macro.throwErrorAt s "qbe: expected $symbol"
  pure (Syntax.mkStrLit f.getId.toString)

meta def params (xs : Array (TSyntax `qbe_param)) (body : Term) : MacroM Term := do
  (← xs.mapM paramIdent).foldrM (fun x b => `(LeanQbe.Expr.param fun $x => $b)) body

meta def expandCls (k : Ident) : MacroM Term :=
  match k.getId with
  | `l => `(LeanQbe.Cls.l)
  | `w => `(LeanQbe.Cls.w)
  | _ => Macro.throwErrorAt k "qbe: expected class l or w"

meta def szOf : Char → Option Name
  | 'b' => some `b | 'h' => some `h | 'w' => some `w | 'l' => some `l | _ => none

meta def binOps : List String :=
  ["add", "sub", "mul", "div", "rem", "udiv", "urem", "and", "or", "xor", "sar", "shr", "shl"]

meta def cmpOps : List String := ["eq", "ne", "sle", "slt", "sge", "sgt", "ule", "ult", "uge", "ugt"]

/-- The binding statement `%x =k op args` with continuation `body`. -/
meta def expandLet (x k op : Ident) (args : Array Term) (body : Term) : MacroM Term := do
  let cls ← expandCls k
  let name := op.getId.toString
  let arity (n : Nat) : MacroM Unit :=
    unless args.size = n do Macro.throwErrorAt op s!"qbe: {name} takes {n} operand(s)"
  if binOps.contains name then
    arity 2
    `(LeanQbe.Expr.let_ (LeanQbe.Op.bin $cls $(mkIdent (`LeanQbe.BinOp ++ .mkSimple name))
        $(args[0]!) $(args[1]!)) fun $x => $body)
  else if name == "copy" then
    arity 1
    `(LeanQbe.Expr.let_ (LeanQbe.Op.copy $cls $(args[0]!)) fun $x => $body)
  else
    let unknown {α : Type} : MacroM α := Macro.throwErrorAt op s!"qbe: unknown operation {name}"
    match name.toList with
    | ['e', 'x', 't', sg, c] =>
      -- extsb extub extsh extuh extsw extuw
      let some sz := szOf c | unknown
      unless sg == 's' || sg == 'u' do unknown
      arity 1
      `(LeanQbe.Expr.let_ (LeanQbe.Op.ext $cls $(mkIdent (`LeanQbe.Sz ++ sz))
          $(quote (sg == 's')) $(args[0]!)) fun $x => $body)
    | 'l' :: 'o' :: 'a' :: 'd' :: rest =>
      -- loadl loadw (= loadsw) loadsw loaduw loadsh loaduh loadsb loadub
      let (sg, c) ← match rest with
        | [c] => pure (true, c)
        | ['s', c] => pure (true, c)
        | ['u', c] => pure (false, c)
        | _ => Macro.throwErrorAt op s!"qbe: unknown operation {name}"
      let some sz := szOf c | unknown
      arity 1
      `(LeanQbe.Expr.load $cls $(mkIdent (`LeanQbe.Sz ++ sz)) $(quote sg) $(args[0]!)
          fun $x => $body)
    | 'c' :: rest =>
      -- c{eq,ne,sle,...}{w,l}
      let some k := rest.getLast? | unknown
      let o := String.ofList rest.dropLast
      unless cmpOps.contains o && (k == 'w' || k == 'l') do unknown
      arity 2
      `(LeanQbe.Expr.let_ (LeanQbe.Op.cmp $(mkIdent (`LeanQbe.Cls ++ .mkSimple (String.singleton k)))
          $(mkIdent (`LeanQbe.CmpOp ++ .mkSimple o)) $(args[0]!) $(args[1]!)) fun $x => $body)
    | _ => unknown

mutual
meta partial def expandTarget : TSyntax `qbe_target → MacroM Term
  | `(qbe_target| @$l:ident $[($as,*)]?) => do
    let as ← match as with | some as => expandArgs as | none => `([])
    `(LeanQbe.Expr.jump $l $as)
  | `(qbe_target| { $ss* }) => expandStmts ss.toList
  | _ => Macro.throwUnsupported

meta partial def expandStmts : List (TSyntax `qbe_stmt) → MacroM Term
  | [] => Macro.throwError "qbe: block does not end in a terminator (ret, jmp, jnz, exit, hlt)"
  | s :: rest => do
    match s with
    | `(qbe_stmt| %$x:ident =$_k:ident call $f($as,*)) =>
      `(LeanQbe.Expr.call $(← symName f) $(← expandArgs as)
          (LeanQbe.Expr.param fun $x => $(← expandStmts rest)))
    | `(qbe_stmt| %$x:ident =$k:ident $op:ident $as,*) =>
      expandLet x k op (← as.getElems.mapM expandArg) (← expandStmts rest)
    | `(qbe_stmt| $st:ident $v, $a) =>
      let sz ← match st.getId.toString with
        | "storel" => pure `l | "storew" => pure `w | "storeh" => pure `h | "storeb" => pure `b
        | n => Macro.throwErrorAt st s!"qbe: unknown statement {n}"
      `(LeanQbe.Expr.store $(mkIdent (`LeanQbe.Sz ++ sz)) $(← expandArg v) $(← expandArg a)
          $(← expandStmts rest))
    | `(qbe_stmt| call $f($as,*)) =>
      `(LeanQbe.Expr.call $(← symName f) $(← expandArgs as) $(← expandStmts rest))
    | `(qbe_stmt| %$x:ident <- $f:ident ( $ys,* )) => do
      let ys ← ys.getElems.mapM paramIdent
      `($f $ys* fun $x => $(← expandStmts rest))
    | `(qbe_stmt| @$_:ident ( $_,* ) { $_* }) =>
      let rec collect : List (TSyntax `qbe_stmt) →
          Array (Ident × Array (TSyntax `qbe_param) × Array (TSyntax `qbe_stmt)) →
          Array (Ident × Array (TSyntax `qbe_param) × Array (TSyntax `qbe_stmt)) ×
            List (TSyntax `qbe_stmt)
        | s :: rest, acc =>
          match s with
          | `(qbe_stmt| @$l:ident ( $ps,* ) { $body* }) =>
            collect rest (acc.push (l, ps.getElems, body))
          | _ => (acc, s :: rest)
        | [], acc => (acc, [])
      let (grp, rest) := collect (s :: rest) #[]
      let mut t ← expandStmts rest
      for (_, ps, body) in grp.reverse do
        t ← `(LeanQbe.Expr.block $(← params ps (← expandStmts body.toList)) $t)
      for (l, _, _) in grp.reverse do
        t ← `(LeanQbe.Expr.label fun $l => $t)
      pure t
    | _ =>
      unless rest.isEmpty do Macro.throwErrorAt rest.head! "qbe: statement after a terminator"
      match s with
      | `(qbe_stmt| jmp @$l:ident $[($as,*)]?) => do
        let as ← match as with | some as => expandArgs as | none => `([])
        `(LeanQbe.Expr.jump $l $as)
      | `(qbe_stmt| jnz $c, $t, $e) =>
        `(LeanQbe.Expr.jnz $(← expandArg c) $(← expandTarget t) $(← expandTarget e))
      | `(qbe_stmt| ret $as,*) => do
        let as ← as.getElems.mapM expandArg
        `(LeanQbe.Expr.ret [$as,*])
      | `(qbe_stmt| exit $f($as,*)) => `(LeanQbe.Expr.exit $(← symName f) $(← expandArgs as))
      | `(qbe_stmt| hlt) => `(LeanQbe.Expr.hlt)
      | `(qbe_stmt| ⟨$e⟩) => pure e
      | _ => Macro.throwUnsupported
end

/-- A code fragment. -/
syntax "qbe " "{" qbe_stmt* "}" : term
/-- A function: its parameters, then its body. -/
syntax "qbe" "(" qbe_param,* ")" " {" qbe_stmt* "}" : term

macro_rules
  | `(qbe { $ss* }) => expandStmts ss.toList
  | `(qbe( $xs,* ) { $ss* }) => do params xs.getElems (← expandStmts ss.toList)

end LeanQbe.Notation
