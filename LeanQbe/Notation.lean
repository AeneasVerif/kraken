module

public import LeanQbe.IL
public meta import Lean.Elab.Term
public meta import Lean.Elab.SyntheticMVars
public meta import Lean.Elab.Command

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
{ … }                     -- a nested scope as the tail (ends the group: nest instead of grouping)
%r, %s <- f(%a, @l)       -- a Lean function as a macro: `f a l fun r s => …`
use f(%a)                 -- a macro whose continuation takes no values: `f a (…)`
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

/- Every word of the notation except `qbe` is a non-reserved symbol (`&"ret"`), so that importing this file does
not turn `ret`, `exit`, `call`, `hlt`, ... into keywords elsewhere (`Expr.ret`, Kraken's `Directive.ret`). -/

open Lean Elab Command Term Meta

declare_syntax_cat qbe_arg
declare_syntax_cat qbe_param
declare_syntax_cat qbe_sym
declare_syntax_cat qbe_target
declare_syntax_cat qbe_stmt (behavior := both)
declare_syntax_cat qbe_marg
declare_syntax_cat qbe_store (behavior := both)

/-- An operand: `%x`, a numeral, or `⟨t⟩` with `t : Arg V`. -/
syntax "%" noWs ident : qbe_arg
syntax num : qbe_arg
syntax "-" noWs num : qbe_arg
syntax "⟨" term "⟩" : qbe_arg

/-- A bound name `%x`. -/
syntax "%" noWs ident : qbe_param

/-- An argument of a Lean macro: a value `%x`, a label `@l`, or a Lean term `⟨t⟩`. -/
syntax "%" noWs ident : qbe_marg
syntax "@" noWs ident : qbe_marg
syntax "⟨" term "⟩" : qbe_marg

/-- A global symbol `$f`. -/
syntax "$" noWs ident : qbe_sym

/-- A `jnz` target: a jump, or an inline block. -/
syntax "@" noWs ident ("(" qbe_arg,* ")")? : qbe_target
syntax "{" qbe_stmt* "}" : qbe_target

/-- `%x =k op a, b` (also `load…`, `call $f(…)`). -/
syntax "%" noWs ident " =" noWs ident ident qbe_arg,* : qbe_stmt
syntax "%" noWs ident " =" noWs ident &"call " qbe_sym "(" qbe_arg,* ")" : qbe_stmt
/-- `store{l,w,h,b} v, a`. -/
syntax qbe_store qbe_arg ", " qbe_arg : qbe_stmt
syntax &"storel" : qbe_store
syntax &"storew" : qbe_store
syntax &"storeh" : qbe_store
syntax &"storeb" : qbe_store
/-- A call without results. -/
syntax &"call " qbe_sym "(" qbe_arg,* ")" : qbe_stmt
syntax &"exit " qbe_sym "(" qbe_arg,* ")" : qbe_stmt
syntax &"jmp " "@" noWs ident ("(" qbe_arg,* ")")? : qbe_stmt
syntax &"jnz " qbe_arg ", " qbe_target ", " qbe_target : qbe_stmt
syntax &"ret" (ppSpace qbe_arg),* : qbe_stmt
syntax &"hlt" : qbe_stmt
/-- A join point. Consecutive ones form one group. -/
syntax "@" noWs ident "(" qbe_param,* ")" " {" qbe_stmt* "}" : qbe_stmt
/-- A Lean function as a macro, in continuation-passing style: `%r, %s <- f(%a, @l)` is
`f a l fun r s => …`, and `use f(%a)` is `f a (…)` (a macro whose continuation takes no values). -/
syntax qbe_param,+ " <- " ident "(" qbe_marg,* ")" : qbe_stmt
syntax &"use " ident "(" qbe_marg,* ")" : qbe_stmt
/-- Splice a Lean term of type `Expr V L` as the tail. -/
syntax "⟨" term "⟩" : qbe_stmt
/-- A nested scope as the tail: ends the current join-point group, so that the groups declared
inside are nested in it (one block per group keeps `wp_loop` / `wp_join` applicable). -/
syntax "{" qbe_stmt* "}" : qbe_stmt

/-! ## Elaboration

`qbe` is a term elaborator that builds the `Expr V L` term directly, with de Bruijn indices for the
binders it introduces, instead of expanding to nested `fun` syntax for the term elaborator: elaborating
nested binders is superlinear (plan risk 8), building them is linear. Only the Lean parts (spliced terms,
macro calls, and `%x` names bound outside the `qbe` block) go through `elabTerm`; for those, every `qbe`
binder in scope is also a local declaration under its own name, and the elaborated term is then
abstracted back to de Bruijn indices. -/

/-- The PHOAS instantiation and the `qbe` binders in scope. -/
structure Ctx where
  V : Lean.Expr
  L : Lean.Expr
  /-- number of `qbe` binders in scope -/
  depth : Nat
  /-- `qbe` name ↦ binder level (0 = outermost) -/
  names : NameMap Nat
  /-- local declaration of a binder ↦ its level -/
  levels : FVarIdMap Nat

meta def Ctx.ref (ctx : Ctx) (lvl : Nat) : Lean.Expr := .bvar (ctx.depth - 1 - lvl)

meta def Ctx.argTy (ctx : Ctx) : Lean.Expr := mkApp (.const ``LeanQbe.Arg []) ctx.V
meta def Ctx.exprTy (ctx : Ctx) : Lean.Expr := mkApp2 (.const ``LeanQbe.Expr []) ctx.V ctx.L

/-- Bring a `qbe` binder into scope for `k`. -/
meta def withBinder {α : Type} (ctx : Ctx) (x : Name) (ty : Lean.Expr) (k : Ctx → TermElabM α) :
    TermElabM α :=
  withLocalDeclD x ty fun fv => k { ctx with
    depth := ctx.depth + 1, names := ctx.names.insert x ctx.depth,
    levels := ctx.levels.insert fv.fvarId! ctx.depth }

/-- Replace the local declarations of `qbe` binders by de Bruijn indices, at binder depth `off`. -/
meta partial def Ctx.abstract (ctx : Ctx) (e : Lean.Expr) (off : Nat := 0) : Lean.Expr :=
  if !e.hasFVar then e else
  match e with
  | .fvar id => match ctx.levels.get? id with
    | some lvl => .bvar (ctx.depth - 1 - lvl + off)
    | none => e
  | .app f a => .app (ctx.abstract f off) (ctx.abstract a off)
  | .lam n t b bi => .lam n (ctx.abstract t off) (ctx.abstract b (off + 1)) bi
  | .forallE n t b bi => .forallE n (ctx.abstract t off) (ctx.abstract b (off + 1)) bi
  | .letE n t v b nd => .letE n (ctx.abstract t off) (ctx.abstract v off) (ctx.abstract b (off + 1)) nd
  | .mdata d b => .mdata d (ctx.abstract b off)
  | .proj s i b => .proj s i (ctx.abstract b off)
  | e => e

/-- Elaborate a Lean term in the scope of the `qbe` binders. -/
meta def elabLean (ctx : Ctx) (t : Syntax) (ty : Lean.Expr) : TermElabM Lean.Expr := do
  let e ← elabTermEnsuringType t ty
  synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  if e.hasExprMVar then
    throwErrorAt t "qbe: could not elaborate{indentExpr e}\ncompletely (add a type ascription)"
  return ctx.abstract e

/-- A value or label name: a `qbe` binder, or else a Lean variable of the given type. -/
meta def elabName (ctx : Ctx) (x : Ident) (ty : Lean.Expr) : TermElabM Lean.Expr :=
  match ctx.names.find? x.getId with
  | some lvl => pure (ctx.ref lvl)
  | none => elabLean ctx x ty

/-- The numeral `n : Val`, exactly as `(n : Val)` elaborates. -/
meta def valLit (n : Nat) : Lean.Expr :=
  mkApp3 (.const ``OfNat.ofNat [.zero]) (.const ``LeanQbe.Val []) (mkRawNatLit n)
    (mkApp2 (.const ``BitVec.instOfNat []) (mkNatLit 64) (mkRawNatLit n))

meta def listLit (ty : Lean.Expr) (es : Array Lean.Expr) : Lean.Expr :=
  es.foldr (fun e acc => mkApp3 (.const ``List.cons [.zero]) ty e acc) (mkApp (.const ``List.nil [.zero]) ty)

meta def elabArg (ctx : Ctx) : TSyntax `qbe_arg → TermElabM Lean.Expr
  | `(qbe_arg| %$x:ident) => return mkApp2 (.const ``LeanQbe.Arg.var []) ctx.V (← elabName ctx x ctx.V)
  | `(qbe_arg| $n:num) => return mkApp2 (.const ``LeanQbe.Arg.imm []) ctx.V (valLit n.getNat)
  | `(qbe_arg| -$n:num) => do elabLean ctx (← `(LeanQbe.Arg.imm (-$n))) ctx.argTy
  | `(qbe_arg| ⟨$t⟩) => elabLean ctx t ctx.argTy
  | stx => throwErrorAt stx "qbe: unsupported operand"

meta def elabArgs (ctx : Ctx) (as : Array (TSyntax `qbe_arg)) : TermElabM Lean.Expr :=
  return listLit ctx.argTy (← as.mapM (elabArg ctx))

meta def paramIdent : TSyntax `qbe_param → TermElabM Ident
  | `(qbe_param| %$x:ident) => pure x
  | stx => throwErrorAt stx "qbe: expected %name"

meta def margTerm : TSyntax `qbe_marg → TermElabM Term
  | `(qbe_marg| %$x:ident) => pure x
  | `(qbe_marg| @$l:ident) => pure l
  | `(qbe_marg| ⟨$t⟩) => pure t
  | stx => throwErrorAt stx "qbe: unsupported macro argument"

/-- `$f` parses as a pseudo-antiquotation node (`"$" [] f []`) outside quotations, so take the
identifier wherever it is. -/
meta def symLit (s : TSyntax `qbe_sym) : TermElabM Lean.Expr := do
  let some f := s.raw.getArgs.find? (·.isIdent) | throwErrorAt s "qbe: expected $symbol"
  return mkStrLit f.getId.toString

meta def mkLam (ctx : Ctx) (x : Name) (body : Lean.Expr) : Lean.Expr := .lam x ctx.V body .default

/-- `params x₁ … xₙ body`: `.param fun x₁ => … .param fun xₙ => body`, with `body` elaborated in scope. -/
meta def elabParams (ctx : Ctx) (xs : List Ident) (body : Ctx → TermElabM Lean.Expr) : TermElabM Lean.Expr :=
  match xs with
  | [] => body ctx
  | x :: xs => do
    let b ← withBinder ctx x.getId ctx.V fun ctx => elabParams ctx xs body
    return mkApp3 (.const ``LeanQbe.Expr.param []) ctx.V ctx.L (mkLam ctx x.getId b)

meta def clsLit (k : Ident) : TermElabM Lean.Expr :=
  match k.getId with
  | `l => pure (.const ``LeanQbe.Cls.l [])
  | `w => pure (.const ``LeanQbe.Cls.w [])
  | _ => throwErrorAt k "qbe: expected class l or w"

meta def szOf : Char → Option Name
  | 'b' => some `b | 'h' => some `h | 'w' => some `w | 'l' => some `l | _ => none

meta def binOps : List String :=
  ["add", "sub", "mul", "div", "rem", "udiv", "urem", "and", "or", "xor", "sar", "shr", "shl"]

meta def cmpOps : List String := ["eq", "ne", "sle", "slt", "sge", "sgt", "ule", "ult", "uge", "ugt"]

/-- `%x =k op args` with continuation `body` (a term under the new binder `x`). -/
meta def mkInstr (ctx : Ctx) (x k op : Ident) (args : Array Lean.Expr) (body : Lean.Expr) : TermElabM Lean.Expr := do
  let cls ← clsLit k
  let name := op.getId.toString
  let unknown {α : Type} : TermElabM α := throwErrorAt op s!"qbe: unknown operation {name}"
  let arity (n : Nat) : TermElabM Unit :=
    unless args.size = n do throwErrorAt op s!"qbe: {name} takes {n} operand(s)"
  let lam := mkLam ctx x.getId body
  let letOp (o : Lean.Expr) : Lean.Expr := mkApp4 (.const ``LeanQbe.Expr.let_ []) ctx.V ctx.L o lam
  if binOps.contains name then
    arity 2
    return letOp (mkApp5 (.const ``LeanQbe.Op.bin []) ctx.V cls
      (.const (`LeanQbe.BinOp ++ .mkSimple name) []) args[0]! args[1]!)
  if name == "copy" then
    arity 1
    return letOp (mkApp3 (.const ``LeanQbe.Op.copy []) ctx.V cls args[0]!)
  match name.toList with
  | ['e', 'x', 't', sg, c] =>
    -- extsb extub extsh extuh extsw extuw
    let some sz := szOf c | unknown
    unless sg == 's' || sg == 'u' do unknown
    arity 1
    return letOp (mkApp5 (.const ``LeanQbe.Op.ext []) ctx.V cls (.const (`LeanQbe.Sz ++ sz) [])
      (toExpr (sg == 's')) args[0]!)
  | 'l' :: 'o' :: 'a' :: 'd' :: rest =>
    -- loadl loadw (= loadsw) loadsw loaduw loadsh loaduh loadsb loadub
    let (sg, c) ← match rest with
      | [c] => pure (true, c)
      | ['s', c] => pure (true, c)
      | ['u', c] => pure (false, c)
      | _ => unknown
    let some sz := szOf c | unknown
    arity 1
    return mkAppN (.const ``LeanQbe.Expr.load []) #[ctx.V, ctx.L, cls, .const (`LeanQbe.Sz ++ sz) [],
      toExpr sg, args[0]!, lam]
  | 'c' :: rest =>
    -- c{eq,ne,sle,...}{w,l}
    let some kc := rest.getLast? | unknown
    let o := String.ofList rest.dropLast
    unless cmpOps.contains o && (kc == 'w' || kc == 'l') do unknown
    arity 2
    return letOp (mkApp5 (.const ``LeanQbe.Op.cmp []) ctx.V
      (.const (`LeanQbe.Cls ++ .mkSimple (String.singleton kc)) [])
      (.const (`LeanQbe.CmpOp ++ .mkSimple o) []) args[0]! args[1]!)
  | _ => unknown

/-- The type `V → … → V → Lean.Expr V L` of a macro continuation with `n` results. -/
meta def contTy (ctx : Ctx) : Nat → Lean.Expr
  | 0 => ctx.exprTy
  | n + 1 => .forallE `x ctx.V (contTy ctx n) .default

mutual
meta partial def elabTarget (ctx : Ctx) : TSyntax `qbe_target → TermElabM Lean.Expr
  | `(qbe_target| @$l:ident $[($as,*)]?) => do
    let as ← elabArgs ctx (as.map (·.getElems) |>.getD #[])
    return mkApp4 (.const ``LeanQbe.Expr.jump []) ctx.V ctx.L (← elabName ctx l ctx.L) as
  | `(qbe_target| { $ss* }) => elabStmts ctx ss.toList
  | stx => throwErrorAt stx "qbe: unsupported jnz target"

meta partial def elabGroup (ctx : Ctx)
    (grp : List (Ident × Array (TSyntax `qbe_param) × Array (TSyntax `qbe_stmt)))
    (rest : List (TSyntax `qbe_stmt)) : TermElabM Lean.Expr :=
  -- declare every label of the group, then define the blocks in order, then the entry
  let rec decl (ctx : Ctx) : List Ident → TermElabM Lean.Expr
    | [] => do
      let mut t ← elabStmts ctx rest
      for (_, ps, body) in grp.reverse do
        let b ← elabParams ctx (← ps.toList.mapM paramIdent) fun ctx => elabStmts ctx body.toList
        t := mkApp4 (.const ``LeanQbe.Expr.block []) ctx.V ctx.L b t
      return t
    | l :: ls => do
      let t ← withBinder ctx l.getId ctx.L fun ctx => decl ctx ls
      return mkApp3 (.const ``LeanQbe.Expr.label []) ctx.V ctx.L (.lam l.getId ctx.L t .default)
  decl ctx (grp.map (·.1))

meta partial def elabStmts (ctx : Ctx) : List (TSyntax `qbe_stmt) → TermElabM Lean.Expr
  | [] => throwError "qbe: block does not end in a terminator (ret, jmp, jnz, exit, hlt)"
  | s :: rest => do
    match s with
    | `(qbe_stmt| %$x:ident =$_k:ident call $f($as,*)) =>
      let as ← elabArgs ctx as.getElems
      let body ← withBinder ctx x.getId ctx.V fun ctx' => elabStmts ctx' rest
      return mkApp5 (.const ``LeanQbe.Expr.call []) ctx.V ctx.L (← symLit f) as
        (mkApp3 (.const ``LeanQbe.Expr.param []) ctx.V ctx.L (mkLam ctx x.getId body))
    | `(qbe_stmt| %$x:ident =$k:ident $op:ident $as,*) =>
      let args ← as.getElems.mapM (elabArg ctx)
      let body ← withBinder ctx x.getId ctx.V fun ctx' => elabStmts ctx' rest
      mkInstr ctx x k op args body
    | `(qbe_stmt| $st:qbe_store $v, $a) =>
      let sz ← match st.raw[0].getAtomVal with
        | "storel" => pure `l | "storew" => pure `w | "storeh" => pure `h | "storeb" => pure `b
        | n => throwErrorAt st s!"qbe: unknown statement {n}"
      return mkAppN (.const ``LeanQbe.Expr.store []) #[ctx.V, ctx.L, .const (`LeanQbe.Sz ++ sz) [],
        ← elabArg ctx v, ← elabArg ctx a, ← elabStmts ctx rest]
    | `(qbe_stmt| call $f:qbe_sym($as,*)) =>
      return mkApp5 (.const ``LeanQbe.Expr.call []) ctx.V ctx.L (← symLit f) (← elabArgs ctx as.getElems)
        (← elabStmts ctx rest)
    | `(qbe_stmt| $xs:qbe_param,* <- $f:ident ( $ys,* )) => do
      let xs ← xs.getElems.mapM paramIdent
      let ys ← ys.getElems.mapM margTerm
      let fn ← elabLean ctx (← `($f $ys*)) (.forallE `k (contTy ctx xs.size) ctx.exprTy .default)
      return .app fn (← elabCont ctx xs.toList rest)
    | `(qbe_stmt| use $f:ident ( $ys,* )) => do
      let ys ← ys.getElems.mapM margTerm
      let fn ← elabLean ctx (← `($f $ys*)) (.forallE `k ctx.exprTy ctx.exprTy .default)
      return .app fn (← elabStmts ctx rest)
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
      elabGroup ctx grp.toList rest
    | _ =>
      unless rest.isEmpty do throwErrorAt rest.head! "qbe: statement after a terminator"
      match s with
      | `(qbe_stmt| jmp @$l:ident $[($as,*)]?) => do
        let as ← elabArgs ctx (as.map (·.getElems) |>.getD #[])
        return mkApp4 (.const ``LeanQbe.Expr.jump []) ctx.V ctx.L (← elabName ctx l ctx.L) as
      | `(qbe_stmt| jnz $c, $t, $e) =>
        return mkApp5 (.const ``LeanQbe.Expr.jnz []) ctx.V ctx.L (← elabArg ctx c) (← elabTarget ctx t)
          (← elabTarget ctx e)
      | `(qbe_stmt| ret $as,*) =>
        return mkApp3 (.const ``LeanQbe.Expr.ret []) ctx.V ctx.L (← elabArgs ctx as.getElems)
      | `(qbe_stmt| exit $f($as,*)) =>
        return mkApp4 (.const ``LeanQbe.Expr.exit []) ctx.V ctx.L (← symLit f) (← elabArgs ctx as.getElems)
      | `(qbe_stmt| hlt) => return mkApp2 (.const ``LeanQbe.Expr.hlt []) ctx.V ctx.L
      | `(qbe_stmt| ⟨$e⟩) => elabLean ctx e ctx.exprTy
      | `(qbe_stmt| { $ss* }) => elabStmts ctx ss.toList
      | _ => throwErrorAt s "qbe: unsupported statement"

/-- The continuation `fun x₁ … xₙ => rest` of a macro call. -/
meta partial def elabCont (ctx : Ctx) (xs : List Ident) (rest : List (TSyntax `qbe_stmt)) :
    TermElabM Lean.Expr :=
  match xs with
  | [] => elabStmts ctx rest
  | x :: xs => do
    let b ← withBinder ctx x.getId ctx.V fun ctx => elabCont ctx xs rest
    return mkLam ctx x.getId b
end

/-- Run `k` with the PHOAS instantiation `V`, `L` of the expected type `Expr V L` or `Func`. -/
meta def withExpectedCtx (ty : Lean.Expr) (k : Ctx → TermElabM Lean.Expr) : TermElabM Lean.Expr := do
  let ty ← whnfR (← instantiateMVars ty)
  if ty.isAppOfArity ``LeanQbe.Expr 2 then
    k { V := ty.appFn!.appArg!, L := ty.appArg!, depth := 0, names := {}, levels := {} }
  else
    let ty ← whnf ty
    if ty.isForall then
      withLocalDecl `V .implicit (.sort 1) fun V =>
      withLocalDecl `L .implicit (.sort 1) fun L => do
        let e ← k { V, L, depth := 0, names := {}, levels := {} }
        mkLambdaFVars #[V, L] e
    else
      throwError "qbe: expected type{indentExpr ty}\nis not `LeanQbe.Expr V L` or `LeanQbe.Func`"

/-- A code fragment. -/
syntax "qbe " "{" qbe_stmt* "}" : term
/-- A function: its parameters, then its body. -/
syntax "qbe" "(" qbe_param,* ")" " {" qbe_stmt* "}" : term

elab_rules : term <= expectedType
  | `(qbe { $ss* }) =>
    withExpectedCtx expectedType fun ctx => elabStmts ctx ss.toList
  | `(qbe( $xs,* ) { $ss* }) =>
    withExpectedCtx expectedType fun ctx => do
      elabParams ctx (← xs.getElems.toList.mapM paramIdent) fun ctx => elabStmts ctx ss.toList

/-- Define a QBE program directly in the kernel, bypassing `addPreDefinitions`, the equation
compiler, and code generation (which are quadratic in binder depth on large PHOAS terms; plan
risk 8). If `: ty` is omitted, the type defaults to `LeanQbe.Func`. -/
syntax (docComment)? "qbe_def " ident (" : " term)? " := " term : command

elab_rules : command
  | `($[$doc:docComment]? qbe_def $id:ident $[: $ty:term]? := $val:term) => do
    let name := (← getCurrNamespace) ++ id.getId
    liftTermElabM do
      let t ← match ty with
        | some ty => elabType ty
        | none => pure (.const ``LeanQbe.Func [])
      let e ← elabTermEnsuringType val t
      synthesizeSyntheticMVarsNoPostponing
      let t ← instantiateMVars t
      let e ← instantiateMVars e
      addDecl (.defnDecl {
        name, levelParams := [], type := t, value := e,
        hints := .regular 0, safety := .safe, all := [name]
      })
      enableRealizationsForConst name
      if let some doc := doc then
        addDocStringCore name (← getDocStringText doc)

end LeanQbe.Notation
