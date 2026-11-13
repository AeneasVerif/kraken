module

public import Kraken.Bedrock2.Syntax
public meta import Kraken.Bedrock2.Syntax
public meta import Lean
import Lean.Data.Options

open Lean Lean.PrettyPrinter.Delaborator Lean.PrettyPrinter.Delaborator.SubExpr

namespace Kraken.Bedrock2.Notation

register_option pp.kraken.bedrock2 : Bool := {
  defValue := true
  descr := "(pretty printer) display Bedrock2 syntax trees in bedrock2 notation"
}

declare_syntax_cat b2expr (behavior := both)
declare_syntax_cat b2cmd (behavior := both)
declare_syntax_cat b2cmds (behavior := both)
declare_syntax_cat b2block
declare_syntax_cat b2func (behavior := both)

syntax:max (name := exprAntiquot) "%" noWs "❰" term "❱" : b2expr
syntax:max (name := exprNum) num : b2expr
syntax:max (name := exprVar) ident : b2expr
syntax:max (name := exprParen) "(" b2expr ")" : b2expr
syntax:max (name := exprLoad1) &"load1" "(" b2expr ")" : b2expr
syntax:max (name := exprLoad2) &"load2" "(" b2expr ")" : b2expr
syntax:max (name := exprLoad4) &"load4" "(" b2expr ")" : b2expr
syntax:max (name := exprLoad8) &"load8" "(" b2expr ")" : b2expr
syntax:max (name := exprTable1) &"inlinetable1" "(" "[" num,* "]" ", " b2expr ")" : b2expr
syntax:max (name := exprTable2) &"inlinetable2" "(" "[" num,* "]" ", " b2expr ")" : b2expr
syntax:max (name := exprTable4) &"inlinetable4" "(" "[" num,* "]" ", " b2expr ")" : b2expr
syntax:max (name := exprTable8) &"inlinetable8" "(" "[" num,* "]" ", " b2expr ")" : b2expr
syntax:max (name := exprMulhuu) &"mulhuu" "(" b2expr ", " b2expr ")" : b2expr
syntax:max (name := exprNot) "~" b2expr:max : b2expr
syntax:max (name := exprOpp) "-" b2expr:max : b2expr
syntax:75 (name := exprSlu) b2expr:75 " << " b2expr:76 : b2expr
syntax:75 (name := exprSru) b2expr:75 " >> " b2expr:76 : b2expr
syntax:75 (name := exprSrs) b2expr:75 " .>> " b2expr:76 : b2expr
syntax:70 (name := exprMul) b2expr:70 " * " b2expr:71 : b2expr
syntax:70 (name := exprDivu) b2expr:70 " / " b2expr:71 : b2expr
syntax:70 (name := exprRemu) b2expr:70 " % " b2expr:71 : b2expr
syntax:65 (name := exprAdd) b2expr:65 " + " b2expr:66 : b2expr
syntax:65 (name := exprSub) b2expr:65 " - " b2expr:66 : b2expr
syntax:58 (name := exprAnd) b2expr:58 " & " b2expr:59 : b2expr
syntax:58 (name := exprXor) b2expr:58 " ^ " b2expr:59 : b2expr
syntax:55 (name := exprOr) b2expr:55 " | " b2expr:56 : b2expr
syntax:50 (name := exprEq) b2expr:51 " == " b2expr:51 : b2expr
syntax:50 (name := exprLtu) b2expr:51 " < " b2expr:51 : b2expr
syntax:50 (name := exprLts) b2expr:51 " .< " b2expr:51 : b2expr
syntax:10 (name := exprIte) b2expr:11 " ? " b2expr:11 " : " b2expr:10 : b2expr

syntax (name := cmdsStx) ppAllowUngrouped sepBy1(b2cmd, ";", ";" ppLine) : b2cmds
syntax (name := blockStx) ppAllowUngrouped "{" ppIndent(ppLine b2cmds) ppLine "}" : b2block

syntax (name := cmdAntiquot) "%" noWs "❰" term "❱" : b2cmd
syntax (name := cmdBlock) ppAllowUngrouped b2block : b2cmd
syntax (name := cmdSkip) &"skip" : b2cmd
syntax (name := cmdSet) ident " = " b2expr : b2cmd
syntax (name := cmdUnset) &"unset" ident : b2cmd
syntax (name := cmdStore1) &"store1" "(" b2expr ", " b2expr ")" : b2cmd
syntax (name := cmdStore2) &"store2" "(" b2expr ", " b2expr ")" : b2cmd
syntax (name := cmdStore4) &"store4" "(" b2expr ", " b2expr ")" : b2cmd
syntax (name := cmdStore8) &"store8" "(" b2expr ", " b2expr ")" : b2cmd
syntax (name := cmdStackalloc) ppAllowUngrouped &"stackalloc" ppSpace num ppSpace &"as" ppSpace ident ppSpace b2block : b2cmd
syntax (name := cmdIf) ppAllowUngrouped "if " b2expr ppSpace b2block : b2cmd
syntax (name := cmdIfElse) ppAllowUngrouped "if " b2expr ppSpace b2block " else " b2block : b2cmd
syntax (name := cmdWhile) ppAllowUngrouped "while " b2expr ppSpace b2block : b2cmd
syntax (name := cmdCall) ident "(" b2expr,* ")" : b2cmd
syntax (name := cmdCallBind) ident,+ " = " ident "(" b2expr,* ")" : b2cmd
syntax (name := cmdInteract) &"interact" ident "(" b2expr,* ")" : b2cmd
syntax (name := cmdInteractBind) ident,+ " = " &"interact" ident "(" b2expr,* ")" : b2cmd

syntax (name := funcStx) ppAllowUngrouped &"fn" ident "(" ident,* ")" (" -> " "(" ident,* ")")? ppSpace b2block : b2func

syntax (name := bedrock2Func) "bedrock2:(" b2func ")" : term
syntax (name := bedrock2Cmd) "bedrock2_cmd:(" b2cmds ")" : term
syntax (name := bedrock2Expr) "bedrock2_expr:(" b2expr ")" : term

public meta section

inductive OpClass
  | arith | shift | bitAnd | bitXor | bitOr | cmp
  deriving BEq

def binOpOfKind : SyntaxNodeKind → Option (Name × OpClass)
  | ``exprSlu => some (``BinOp.slu, .shift)
  | ``exprSru => some (``BinOp.sru, .shift)
  | ``exprSrs => some (``BinOp.srs, .shift)
  | ``exprMul => some (``BinOp.mul, .arith)
  | ``exprDivu => some (``BinOp.divu, .arith)
  | ``exprRemu => some (``BinOp.remu, .arith)
  | ``exprAdd => some (``BinOp.add, .arith)
  | ``exprSub => some (``BinOp.sub, .arith)
  | ``exprAnd => some (``BinOp.and, .bitAnd)
  | ``exprXor => some (``BinOp.xor, .bitXor)
  | ``exprOr => some (``BinOp.or, .bitOr)
  | ``exprEq => some (``BinOp.eq, .cmp)
  | ``exprLtu => some (``BinOp.ltu, .cmp)
  | ``exprLts => some (``BinOp.lts, .cmp)
  | _ => none

def OpClass.isBitwise : OpClass → Bool
  | .bitAnd | .bitXor | .bitOr => true
  | _ => false

def precedenceDiffersFromC (parent child : OpClass) : Bool :=
  (parent == .arith && child == .shift) || (parent == .shift && child == .arith) ||
  (parent.isBitwise && child.isBitwise && parent != child) ||
  (parent.isBitwise && child == .cmp) || (parent == .cmp && child.isBitwise)

def precedenceError (parent child : OpClass) : String :=
  if parent.isBitwise && child.isBitwise && !(parent == .bitAnd && child == .bitXor) then
    "C compilers warn about mixing bitwise operators without parentheses " ++
      "(-Wbitwise-op-parentheses): add parentheses"
  else
    "precedence differs between Lean and C: add parentheses"

def accessSizeOfKind : SyntaxNodeKind → Option Name
  | ``exprLoad1 | ``exprTable1 | ``cmdStore1 => some ``AccessSize.one
  | ``exprLoad2 | ``exprTable2 | ``cmdStore2 => some ``AccessSize.two
  | ``exprLoad4 | ``exprTable4 | ``cmdStore4 => some ``AccessSize.four
  | ``exprLoad8 | ``exprTable8 | ``cmdStore8 => some ``AccessSize.eight
  | _ => none

def identStr (id : Syntax) : MacroM Term :=
  match id.getId.eraseMacroScopes with
  | .str .anonymous s => return Syntax.mkStrLit s
  | _ => Macro.throwErrorAt id "bedrock2 identifiers must be atomic"

def reservedWords : List String :=
  ["load1", "load2", "load4", "load8", "store1", "store2", "store4", "store8", "inlinetable1",
    "inlinetable2", "inlinetable4", "inlinetable8", "mulhuu", "skip", "unset", "stackalloc", "as",
    "interact", "fn"]

def targetStr (id : Syntax) : MacroM Term := do
  if let .str .anonymous s := id.getId.eraseMacroScopes then
    if reservedWords.contains s then
      Macro.throwErrorAt id s!"'{s}' is reserved in bedrock2 notation and cannot name a function or action"
  identStr id

partial def expandExpr (stx : Syntax) : MacroM Term := do
  let k := stx.getKind
  if let some (op, cls) := binOpOfKind k then
    for child in [stx[0], stx[2]] do
      if let some (_, childCls) := binOpOfKind child.getKind then
        if precedenceDiffersFromC cls childCls then
          Macro.throwErrorAt child (precedenceError cls childCls)
    return ← `(Kraken.Bedrock2.Expr.op $(mkCIdent op) $(← expandExpr stx[0]) $(← expandExpr stx[2]))
  if let some sz := accessSizeOfKind k then
    if stx.getNumArgs == 4 then
      return ← `(Kraken.Bedrock2.Expr.load $(mkCIdent sz) $(← expandExpr stx[2]))
    let table : Array Term := stx[3].getSepArgs.map (⟨·⟩)
    for n in table do
      if 256 ≤ n.raw.isNatLit?.getD 0 then
        Macro.throwErrorAt n "inlinetable entries must be less than 256"
    return ← `(Kraken.Bedrock2.Expr.inlinetable $(mkCIdent sz) [$table,*] $(← expandExpr stx[6]))
  match k with
  | ``exprAntiquot => return ⟨stx[2]⟩
  | ``exprNum => `(Kraken.Bedrock2.Expr.literal $(⟨stx[0]⟩))
  | ``exprVar => `(Kraken.Bedrock2.Expr.var $(← identStr stx[0]))
  | ``exprParen => expandExpr stx[1]
  | ``exprMulhuu =>
    `(Kraken.Bedrock2.Expr.op Kraken.Bedrock2.BinOp.mulhuu $(← expandExpr stx[2]) $(← expandExpr stx[4]))
  | ``exprNot => `(Kraken.Bedrock2.Expr.op1 Kraken.Bedrock2.Op1.not $(← expandExpr stx[1]))
  | ``exprOpp => `(Kraken.Bedrock2.Expr.op1 Kraken.Bedrock2.Op1.opp $(← expandExpr stx[1]))
  | ``exprIte =>
    `(Kraken.Bedrock2.Expr.ite $(← expandExpr stx[0]) $(← expandExpr stx[2]) $(← expandExpr stx[4]))
  | _ => Macro.throwUnsupported

def expandArgs (args : Syntax) : MacroM Term := do
  let args ← args.getSepArgs.mapM expandExpr
  `([$args,*])

def expandIdents (ids : Syntax) : MacroM Term := do
  let ids ← ids.getSepArgs.mapM identStr
  `([$ids,*])

partial def expandCmd (stx : Syntax) : MacroM Term := do
  if stx.isOfKind choiceKind then
    let notCall := stx.getArgs.filter fun alt => !alt.isOfKind ``cmdCall && !alt.isOfKind ``cmdCallBind
    if h : notCall.size = 1 then return ← expandCmd notCall[0]
    Macro.throwErrorAt stx "ambiguous bedrock2 command"
  let k := stx.getKind
  if let some sz := accessSizeOfKind k then
    return ← `(Kraken.Bedrock2.Cmd.store $(mkCIdent sz) $(← expandExpr stx[2]) $(← expandExpr stx[4]))
  match k with
  | ``blockStx => expandCmd stx[1]
  | ``cmdAntiquot => return ⟨stx[2]⟩
  | ``cmdBlock => expandCmd stx[0]
  | ``cmdSkip => `(Kraken.Bedrock2.Cmd.skip)
  | ``cmdSet => `(Kraken.Bedrock2.Cmd.set $(← identStr stx[0]) $(← expandExpr stx[2]))
  | ``cmdUnset => `(Kraken.Bedrock2.Cmd.unset $(← identStr stx[1]))
  | ``cmdStackalloc =>
    `(Kraken.Bedrock2.Cmd.stackalloc $(← identStr stx[3]) $(⟨stx[1]⟩) $(← expandCmd stx[4]))
  | ``cmdIf => `(Kraken.Bedrock2.Cmd.cond $(← expandExpr stx[1]) $(← expandCmd stx[2]) Kraken.Bedrock2.Cmd.skip)
  | ``cmdIfElse =>
    `(Kraken.Bedrock2.Cmd.cond $(← expandExpr stx[1]) $(← expandCmd stx[2]) $(← expandCmd stx[4]))
  | ``cmdWhile => `(Kraken.Bedrock2.Cmd.while $(← expandExpr stx[1]) $(← expandCmd stx[2]))
  | ``cmdCall => `(Kraken.Bedrock2.Cmd.call [] $(← targetStr stx[0]) $(← expandArgs stx[2]))
  | ``cmdCallBind =>
    `(Kraken.Bedrock2.Cmd.call $(← expandIdents stx[0]) $(← targetStr stx[2]) $(← expandArgs stx[4]))
  | ``cmdInteract => `(Kraken.Bedrock2.Cmd.interact [] $(← targetStr stx[1]) $(← expandArgs stx[3]))
  | ``cmdInteractBind =>
    `(Kraken.Bedrock2.Cmd.interact $(← expandIdents stx[0]) $(← targetStr stx[3]) $(← expandArgs stx[5]))
  | ``cmdsStx =>
    let cs := stx[0].getSepArgs
    let some last := cs.back? | Macro.throwUnsupported
    cs.pop.foldrM (init := ← expandCmd last) fun c acc => do
      `(Kraken.Bedrock2.Cmd.seq $(← expandCmd c) $acc)
  | _ => Macro.throwUnsupported

def expandFunc (stx : Syntax) : MacroM Term := do
  let rets ← if stx[5].getNumArgs == 0 then `([]) else expandIdents stx[5][2]
  `((($(← identStr stx[1]) : String),
    Kraken.Bedrock2.Func.mk $(← expandIdents stx[3]) $rets $(← expandCmd stx[6])))

end

macro_rules
  | `(bedrock2_expr:( $e )) => expandExpr e
  | `(bedrock2_cmd:( $c )) => expandCmd c
  | `(bedrock2:( $f )) => expandFunc f

public meta section

def ppEnabled : DelabM Bool := do
  if (← getPPOption getPPExplicit) then return false
  return (← getOptions).getBool `pp.kraken.bedrock2 true

def natOfLit? (e : Lean.Expr) : Option Nat :=
  match_expr e with
  | OfNat.ofNat _ n _ => n.rawNatLit?
  | _ => e.rawNatLit?

def byteOfLit? (e : Lean.Expr) : Option Nat := do
  let n ← natOfLit? e
  if n < 256 then some n else none

def numStx (n : Nat) : TSyntax `num :=
  Syntax.mkNumLit (if n < 256 then toString n else "0x" ++ String.ofList (Nat.toDigits 16 n))

def identOfStrLit? (e : Lean.Expr) : Option Ident :=
  match e with
  | .lit (.strVal s) => if s.isEmpty || s == "_" then none else some (mkIdent (.mkSimple s))
  | _ => none

partial def listElems? {α} (f : Lean.Expr → Option α) (e : Lean.Expr) : Option (Array α) :=
  match_expr e with
  | List.cons _ hd tl => do return #[← f hd] ++ (← listElems? f tl)
  | List.nil _ => some #[]
  | _ => none

def exprPrec (s : TSyntax `b2expr) : Nat :=
  match s.raw.getKind with
  | ``exprSlu | ``exprSru | ``exprSrs => 75
  | ``exprMul | ``exprDivu | ``exprRemu => 70
  | ``exprAdd | ``exprSub => 65
  | ``exprAnd | ``exprXor => 58
  | ``exprOr => 55
  | ``exprEq | ``exprLtu | ``exprLts => 50
  | ``exprIte => 10
  | _ => 1024

def parenIf (b : Bool) (s : TSyntax `b2expr) : DelabM (TSyntax `b2expr) :=
  if b then `(b2expr| ($s)) else pure s

def operand (parent : OpClass) (minPrec : Nat) (s : TSyntax `b2expr) : DelabM (TSyntax `b2expr) :=
  let conflict := match binOpOfKind s.raw.getKind with
    | some (_, c) => precedenceDiffersFromC parent c
    | none => false
  parenIf (exprPrec s < minPrec || conflict) s

def binOpKind? (op : Name) : Option (SyntaxNodeKind × OpClass) :=
  [``exprSlu, ``exprSru, ``exprSrs, ``exprMul, ``exprDivu, ``exprRemu, ``exprAdd,
      ``exprSub, ``exprAnd, ``exprXor, ``exprOr, ``exprEq, ``exprLtu, ``exprLts].findSome? fun k =>
    match binOpOfKind k with
    | some (op', cls) => if op' == op then some (k, cls) else none
    | none => none

def binOpStx (op : Name) (a b : TSyntax `b2expr) : DelabM (TSyntax `b2expr) := do
  let some (k, c) := binOpKind? op | failure
  let p := exprPrec ⟨Syntax.node .none k #[]⟩
  let (lp, rp) := if c == .cmp then (p + 1, p + 1) else (p, p + 1)
  let a ← operand c lp a
  let b ← operand c rp b
  match k with
  | ``exprSlu => `(b2expr| $a << $b)
  | ``exprSru => `(b2expr| $a >> $b)
  | ``exprSrs => `(b2expr| $a .>> $b)
  | ``exprMul => `(b2expr| $a * $b)
  | ``exprDivu => `(b2expr| $a / $b)
  | ``exprRemu => `(b2expr| $a % $b)
  | ``exprAdd => `(b2expr| $a + $b)
  | ``exprSub => `(b2expr| $a - $b)
  | ``exprAnd => `(b2expr| $a & $b)
  | ``exprXor => `(b2expr| $a ^ $b)
  | ``exprOr => `(b2expr| $a | $b)
  | ``exprEq => `(b2expr| $a == $b)
  | ``exprLtu => `(b2expr| $a < $b)
  | _ => `(b2expr| $a .< $b)

mutual

partial def delabExprAt : DelabM (TSyntax `b2expr) := do
  try delabExprCore catch _ => do
    let t ← withOptions (·.setBool `pp.kraken.bedrock2 false) delab
    `(b2expr| %❰ $t ❱)

partial def delabExprCore : DelabM (TSyntax `b2expr) := do
  let e ← getExpr
  match_expr e with
  | Kraken.Bedrock2.Expr.literal v =>
    match v.int? with
    | some n => if 0 ≤ n then `(b2expr| $(numStx n.toNat):num) else failure
    | none => failure
  | Kraken.Bedrock2.Expr.var x =>
    let some x := identOfStrLit? x | failure
    `(b2expr| $x:ident)
  | Kraken.Bedrock2.Expr.load sz _ =>
    let some sz := sz.constName? | failure
    unless [``AccessSize.one, ``AccessSize.two, ``AccessSize.four, ``AccessSize.eight].contains sz do
      failure
    let a ← withNaryArg 1 delabExprAt
    match sz with
    | ``AccessSize.one => `(b2expr| load1($a))
    | ``AccessSize.two => `(b2expr| load2($a))
    | ``AccessSize.four => `(b2expr| load4($a))
    | _ => `(b2expr| load8($a))
  | Kraken.Bedrock2.Expr.inlinetable sz t _ =>
    let some sz := sz.constName? | failure
    unless [``AccessSize.one, ``AccessSize.two, ``AccessSize.four, ``AccessSize.eight].contains sz do
      failure
    let some t := listElems? byteOfLit? t | failure
    let t := t.map numStx
    let i ← withNaryArg 2 delabExprAt
    match sz with
    | ``AccessSize.one => `(b2expr| inlinetable1([$[$t],*], $i))
    | ``AccessSize.two => `(b2expr| inlinetable2([$[$t],*], $i))
    | ``AccessSize.four => `(b2expr| inlinetable4([$[$t],*], $i))
    | _ => `(b2expr| inlinetable8([$[$t],*], $i))
  | Kraken.Bedrock2.Expr.op1 o _ =>
    let some o := o.constName? | failure
    unless [``Op1.not, ``Op1.opp].contains o do failure
    let a ← withNaryArg 1 delabExprAt
    let a ← parenIf (exprPrec a < 1024) a
    if o == ``Op1.not then `(b2expr| ~$a) else `(b2expr| -$a)
  | Kraken.Bedrock2.Expr.op o _ _ =>
    let some op := o.constName? | failure
    unless op == ``BinOp.mulhuu || (binOpKind? op).isSome do failure
    let a ← withNaryArg 1 delabExprAt
    let b ← withNaryArg 2 delabExprAt
    if op == ``BinOp.mulhuu then `(b2expr| mulhuu($a, $b)) else binOpStx op a b
  | Kraken.Bedrock2.Expr.ite _ _ _ =>
    let c ← withNaryArg 0 delabExprAt
    let a ← withNaryArg 1 delabExprAt
    let b ← withNaryArg 2 delabExprAt
    let c ← parenIf (exprPrec c ≤ 10) c
    let a ← parenIf (exprPrec a ≤ 10) a
    `(b2expr| $c ? $a : $b)
  | _ => failure

end

partial def delabArgs : DelabM (Array (TSyntax `b2expr)) := do
  match_expr ← getExpr with
  | List.cons _ _ _ =>
    let hd ← withNaryArg 1 delabExprAt
    let tl ← withNaryArg 2 delabArgs
    return #[hd] ++ tl
  | List.nil _ => return #[]
  | _ => failure

def cmdsOf (cs : Array (TSyntax `b2cmd)) : TSyntax `b2cmds :=
  ⟨Syntax.node .none ``cmdsStx #[mkNullNode (mkSepArray (cs.map (·.raw)) (mkAtom ";"))]⟩

def blockOf (cs : Array (TSyntax `b2cmd)) : DelabM (TSyntax `b2block) := `(b2block| { $(cmdsOf cs) })

def funcIdentOfStrLit? (e : Lean.Expr) : Option Ident :=
  match e with
  | .lit (.strVal s) => if reservedWords.contains s then none else identOfStrLit? e
  | _ => none

mutual

partial def delabCmdsWith (head : DelabM (TSyntax `b2cmd)) : DelabM (Array (TSyntax `b2cmd)) := do
  match_expr ← getExpr with
  | Kraken.Bedrock2.Cmd.seq _ _ =>
    let a ← withNaryArg 0 delabCmdAt
    let rest ← withNaryArg 1 (delabCmdsWith delabCmdAt)
    return #[a] ++ rest
  | _ => return #[← head]

partial def delabCmdAt : DelabM (TSyntax `b2cmd) := do
  try delabCmdCore catch _ => do
    let t ← withOptions (·.setBool `pp.kraken.bedrock2 false) delab
    `(b2cmd| %❰ $t ❱)

partial def delabCmdCore : DelabM (TSyntax `b2cmd) := do
  let e ← getExpr
  match_expr e with
  | Kraken.Bedrock2.Cmd.skip => `(b2cmd| skip)
  | Kraken.Bedrock2.Cmd.set x _ =>
    let some x := identOfStrLit? x | failure
    let v ← withNaryArg 1 delabExprAt
    `(b2cmd| $x:ident = $v)
  | Kraken.Bedrock2.Cmd.unset x =>
    let some x := identOfStrLit? x | failure
    `(b2cmd| unset $x:ident)
  | Kraken.Bedrock2.Cmd.store sz _ _ =>
    let (k, kw) ← match sz.constName? with
      | some ``AccessSize.one => pure (``cmdStore1, "store1")
      | some ``AccessSize.two => pure (``cmdStore2, "store2")
      | some ``AccessSize.four => pure (``cmdStore4, "store4")
      | some ``AccessSize.eight => pure (``cmdStore8, "store8")
      | _ => failure
    let a ← withNaryArg 1 delabExprAt
    let v ← withNaryArg 2 delabExprAt
    return ⟨Syntax.node .none k #[mkAtom kw, mkAtom "(", a, mkAtom ",", v, mkAtom ")"]⟩
  | Kraken.Bedrock2.Cmd.stackalloc x n _ =>
    let some x := identOfStrLit? x | failure
    let some n := natOfLit? n | failure
    let body ← blockOf (← withNaryArg 2 (delabCmdsWith delabCmdAt))
    `(b2cmd| stackalloc $(numStx n):num as $x:ident $body)
  | Kraken.Bedrock2.Cmd.cond _ _ c2 =>
    let c ← withNaryArg 0 delabExprAt
    let t ← blockOf (← withNaryArg 1 (delabCmdsWith delabCmdAt))
    if c2.isConstOf ``Cmd.skip then
      `(b2cmd| if $c $t)
    else
      let f ← blockOf (← withNaryArg 2 (delabCmdsWith delabCmdAt))
      `(b2cmd| if $c $t else $f)
  | Kraken.Bedrock2.Cmd.while _ _ =>
    let c ← withNaryArg 0 delabExprAt
    let body ← blockOf (← withNaryArg 1 (delabCmdsWith delabCmdAt))
    `(b2cmd| while $c $body)
  | Kraken.Bedrock2.Cmd.call binds f _ =>
    let some binds := listElems? identOfStrLit? binds | failure
    let some f := funcIdentOfStrLit? f | failure
    let args ← withNaryArg 2 delabArgs
    if binds.isEmpty then `(b2cmd| $f:ident($[$args],*))
    else `(b2cmd| $[$binds:ident],* = $f:ident($[$args],*))
  | Kraken.Bedrock2.Cmd.interact binds f _ =>
    let some binds := listElems? identOfStrLit? binds | failure
    let some f := funcIdentOfStrLit? f | failure
    let args ← withNaryArg 2 delabArgs
    if binds.isEmpty then `(b2cmd| interact $f:ident($[$args],*))
    else `(b2cmd| $[$binds:ident],* = interact $f:ident($[$args],*))
  | Kraken.Bedrock2.Cmd.seq _ _ =>
    let b ← blockOf (← delabCmdsWith delabCmdAt)
    `(b2cmd| $b:b2block)
  | _ => failure

end

def delabFunc (name : Lean.Expr) : DelabM (TSyntax `b2func) := do
  let some name := identOfStrLit? name | failure
  match_expr ← getExpr with
  | Kraken.Bedrock2.Func.mk params rets _ =>
    let some params := listElems? identOfStrLit? params | failure
    let some rets := listElems? identOfStrLit? rets | failure
    let body ← blockOf (← withNaryArg 2 (delabCmdsWith delabCmdAt))
    if rets.isEmpty then `(b2func| fn $name($[$params],*) $body)
    else `(b2func| fn $name($[$params],*) -> ($[$rets],*) $body)
  | _ => failure

@[app_delab Kraken.Bedrock2.Expr.literal, app_delab Kraken.Bedrock2.Expr.var,
  app_delab Kraken.Bedrock2.Expr.load, app_delab Kraken.Bedrock2.Expr.inlinetable,
  app_delab Kraken.Bedrock2.Expr.op1, app_delab Kraken.Bedrock2.Expr.op,
  app_delab Kraken.Bedrock2.Expr.ite]
def delabExpr : Delab := do
  unless ← ppEnabled do failure
  let s ← delabExprCore
  `(bedrock2_expr:($s))

@[app_delab Kraken.Bedrock2.Cmd.skip, app_delab Kraken.Bedrock2.Cmd.set,
  app_delab Kraken.Bedrock2.Cmd.unset, app_delab Kraken.Bedrock2.Cmd.store,
  app_delab Kraken.Bedrock2.Cmd.stackalloc, app_delab Kraken.Bedrock2.Cmd.cond,
  app_delab Kraken.Bedrock2.Cmd.seq, app_delab Kraken.Bedrock2.Cmd.while,
  app_delab Kraken.Bedrock2.Cmd.call, app_delab Kraken.Bedrock2.Cmd.interact]
def delabCmd : Delab := do
  unless ← ppEnabled do failure
  let cs ← delabCmdsWith delabCmdCore
  `(bedrock2_cmd:($(cmdsOf cs)))

@[app_delab Prod.mk]
def delabNamedFunc : Delab := do
  unless ← ppEnabled do failure
  match_expr ← getExpr with
  | Prod.mk α β name _ =>
    unless α.isConstOf ``String && β.isConstOf ``Func do failure
    let f ← withNaryArg 3 (delabFunc name)
    `(bedrock2:($f))
  | _ => failure

end

end Kraken.Bedrock2.Notation
