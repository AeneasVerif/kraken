module

public import LeanQbe.T.Frontend.C0.Elab
public import LeanQbe.T.Frontend.C0.Template.Snippet
public meta import LeanQbe.T.Frontend.C0.Elab
public meta import LeanQbe.T.Frontend.C0.Template.Snippet
public meta import Lean.Elab.Term
public meta import Lean.Parser

/-!
# C0 Template Source Scanner & AST Rewriting (`MetaM` / `TermElabM`)

Scans C0 template strings for typed antiquotations (`$(k)`, `bv$(w)`, `ty$(t)`, `$(op)`,
`$(cmp)`, `$(snip)`, `#unroll`), builds the dummy C0 preamble, and rewrites `Nat` casts,
statement snippet calls, `#unroll` scopes, and `CmpOp` placeholder types.
-/

set_option autoImplicit false

public meta section

namespace LeanQbe.T.Frontend.C0

open Lean Elab Term Meta
open LeanQbe.T

abbrev C0Expr := LeanQbe.T.Frontend.C0.Expr

def liftEx {m : Type → Type} [Monad m] [MonadError m] {α : Type} :
    Except String α → m α
  | .ok a => pure a
  | .error e => throwError e

structure TySplice where
  aliasName : String
  placeholderBits : Nat
  signed : Bool
  leanExpr : Lean.Expr
  isOpaqueTy : Bool := false

inductive CallSpliceKind
  | opCode (opExpr : Lean.Expr) (sigExprs : List Lean.Expr) (rsExprs : List Lean.Expr)
  | cmpOp (cmpExpr : Lean.Expr)
  | exprSnippet (snipExpr : Lean.Expr) (asExprs : List Lean.Expr) (rExpr : Lean.Expr)
  | funcSnippet (funcExpr : Lean.Expr) (asExprs : List Lean.Expr) (rExpr : Lean.Expr)
  | stmtSnippet (snipExpr : Lean.Expr) (tsExprs : List Lean.Expr)

structure CallSplice where
  placeholderName : String
  kind : CallSpliceKind

structure ValSplice where
  placeholderName : String
  leanExpr : Lean.Expr
  c0Ty : C0Type
  tyExpr : Lean.Expr
  isNat : Bool := false
  natRawExpr : Option Lean.Expr := none

structure UnrollSplice where
  uid : Nat
  markName : String
  implName : String
  elemName : String
  elemFVarId : FVarId
  elemTy : Lean.Expr
  listExpr : Lean.Expr
  bodyDeclsSrc : String
  bodyStmts : List Stmt := []
  bodyValSplices : Array ValSplice
  stateVars : List (String × C0Type) := []
  roVars : List (String × C0Type) := []

structure ScanEnv where
  tySplices : Array TySplice := #[]
  callSplices : Array CallSplice := #[]
  valSplices : Array ValSplice := #[]
  unrolls : Array UnrollSplice := #[]
  nextSymWidthIdx : Nat := 0
  nextUid : Nat := 0

def isIdentChar (c : Char) : Bool :=
  c.isAlphanum || c == '_'

partial def skipSpaces (cs : Array Char) (i : Nat) : Nat :=
  if h : i < cs.size then
    let c := cs[i]
    if c == ' ' || c == '\t' then skipSpaces cs (i + 1) else i
  else i

partial def skipWS (cs : Array Char) (i : Nat) : Nat :=
  if h : i < cs.size then
    let c := cs[i]
    if c.isWhitespace then skipWS cs (i + 1) else i
  else i

partial def scanBalancedDelim (cs : Array Char) (start : Nat) (openCh closeCh : Char) :
    TermElabM (String × Nat) := do
  let rec go (i depth : Nat) (inStr : Bool) (esc : Bool) (acc : List Char) :
      TermElabM (String × Nat) := do
    if h : i < cs.size then
      let c := cs[i]
      if inStr then
        if esc then go (i + 1) depth true false (c :: acc)
        else if c == '\\' then go (i + 1) depth true true (c :: acc)
        else if c == '"' then go (i + 1) depth false false (c :: acc)
        else go (i + 1) depth true false (c :: acc)
      else
        if c == '"' then go (i + 1) depth true false (c :: acc)
        else if c == openCh then go (i + 1) (depth + 1) false false (c :: acc)
        else if c == closeCh then
          if depth == 1 then pure (String.ofList acc.reverse, i + 1)
          else go (i + 1) (depth - 1) false false (c :: acc)
        else
          go (i + 1) depth false false (c :: acc)
    else
      throwError "c0 template: unterminated '{openCh}...{closeCh}' in template"
  go start 1 false false []

def parseAndElabLeanTerm (stxRef : Syntax) (raw : String) (expectedTy? : Option Lean.Expr) :
    TermElabM Lean.Expr := do
  let env ← getEnv
  let wrapped := "(" ++ raw ++ ")"
  let termStx ← match Parser.runParserCategory env `term wrapped "<c0_template>" with
    | .ok s => pure s
    | .error err =>
      throwErrorAt stxRef "c0 template antiquotation parse error in '$({raw})': {err}"
  let e ← Term.elabTerm termStx expectedTy?
  Term.synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  if e.hasExprMVar then
    throwErrorAt stxRef
      m!"c0 template antiquotation '$({raw})' has unresolved metavariables:{indentExpr e}"
  pure e

def matchPrefixAt (cs : Array Char) (i : Nat) (pfx : String) : Bool :=
  let pcs := pfx.toList
  let rec go (j : Nat) : List Char → Bool
    | [] => true
    | c :: rest => if h : j < cs.size then cs[j] == c && go (j + 1) rest else false
  go i pcs

def templatePlaceholderBase : Nat := 1000000
def templatePlaceholderStep : Nat := 8

def getOrAddTySplice (stxRef : Syntax) (termStr : String) (signed isOpaqueTy : Bool) :
    StateT ScanEnv TermElabM TySplice := do
  let natTy := Lean.mkConst ``Nat
  let tyTy := Lean.mkConst ``LeanQbe.T.Ty
  let expected := if isOpaqueTy then tyTy else natTy
  let e ← liftM (parseAndElabLeanTerm stxRef termStr (some expected))
  let eWhnf ← liftM (whnf e)
  if !isOpaqueTy then
    if let some n := LeanQbe.T.Notation.fastNat? eWhnf then
      let st ← get
      let idx := st.tySplices.size
      let ts : TySplice := {
        aliasName := s!"__c0tpl_ty_{idx}"
        placeholderBits := n
        signed
        leanExpr := eWhnf
        isOpaqueTy := false
      }
      set { st with tySplices := st.tySplices.push ts }
      return ts
  else
    if let some sh := LeanQbe.T.Notation.toTyShapeFast? eWhnf then
      match sh with
      | .bits (some n) _ =>
        let st ← get
        let idx := st.tySplices.size
        let ts : TySplice := {
          aliasName := s!"__c0tpl_ty_{idx}"
          placeholderBits := n
          signed := false
          leanExpr := eWhnf
          isOpaqueTy := false
        }
        set { st with tySplices := st.tySplices.push ts }
        return ts
      | _ => pure ()
  let st ← get
  for ts in st.tySplices do
    if ts.signed == signed && ts.isOpaqueTy == isOpaqueTy then
      if ← liftM (isDefEq ts.leanExpr eWhnf) then
        return ts
  let mut pw? : Option Nat := none
  if !isOpaqueTy then
    for ts in st.tySplices do
      if !ts.isOpaqueTy then
        if ← liftM (isDefEq ts.leanExpr eWhnf) then
          pw? := some ts.placeholderBits
          break
  let idx := st.tySplices.size
  let (pw, nextSym) := match pw? with
    | some p => (p, st.nextSymWidthIdx)
    | none =>
      let offset := if isOpaqueTy then 1000000 else 0
      (templatePlaceholderBase + offset + templatePlaceholderStep * st.nextSymWidthIdx,
        st.nextSymWidthIdx + 1)
  let ts : TySplice := {
    aliasName := s!"__c0tpl_ty_{idx}"
    placeholderBits := pw
    signed
    leanExpr := eWhnf
    isOpaqueTy
  }
  set { st with tySplices := st.tySplices.push ts, nextSymWidthIdx := nextSym }
  pure ts

def leanTyExprToC0Type (stxRef : Syntax) (tyE : Lean.Expr) :
    StateT ScanEnv TermElabM C0Type := do
  let sh ← liftM (LeanQbe.T.Notation.toTyShape tyE)
  match sh with
  | .bool => pure .bool
  | .bits (some n) _ => pure (.int false n)
  | .bits none nExpr =>
    let nWhnf ← liftM (whnf nExpr)
    let st ← get
    for ts in st.tySplices do
      if !ts.isOpaqueTy then
        if ← liftM (isDefEq ts.leanExpr nWhnf) then
          return .int ts.signed ts.placeholderBits
    let idx := st.tySplices.size
    let pw := templatePlaceholderBase + templatePlaceholderStep * st.nextSymWidthIdx
    let ts : TySplice := {
      aliasName := s!"__c0tpl_ty_{idx}"
      placeholderBits := pw
      signed := false
      leanExpr := nWhnf
      isOpaqueTy := false
    }
    set { st with tySplices := st.tySplices.push ts, nextSymWidthIdx := st.nextSymWidthIdx + 1 }
    pure (.int false pw)
  | .float .d => pure .f64
  | .other e =>
    let st ← get
    for ts in st.tySplices do
      if ts.isOpaqueTy then
        if ← liftM (isDefEq ts.leanExpr e) then
          return .int false ts.placeholderBits
    throwErrorAt stxRef m!"c0 template: unsupported `Ty` in splice signature:{indentExpr e}"
  | _ => throwErrorAt stxRef m!"c0 template: unsupported `Ty` in splice signature:{indentExpr tyE}"

def leanListTyToC0Types (stxRef : Syntax) (listE : Lean.Expr) :
    StateT ScanEnv TermElabM (List Lean.Expr × List C0Type) := do
  let some tys ← liftM (LeanQbe.T.Notation.extractTyList? listE)
    | throwErrorAt stxRef m!"c0 template: expected concrete `List Ty`, got:{indentExpr listE}"
  let c0s ← tys.mapM (leanTyExprToC0Type stxRef)
  pure (tys, c0s)

partial def scanTemplateSrc (stxRef : Syntax) (src : String) :
    StateT ScanEnv TermElabM String := do
  let cs := src.toList.toArray
  let mut i : Nat := 0
  let mut outRev : List Char := []
  let pushStr (acc : List Char) (s : String) : List Char :=
    s.toList.foldl (fun a c => c :: a) acc
  let prevWasIdent (pos : Nat) : Bool :=
    if pos == 0 then false else isIdentChar cs[pos - 1]!
  while i < cs.size do
    let c := cs[i]!
    if c == '/' && i + 1 < cs.size && cs[i + 1]! == '/' then
      while i < cs.size && cs[i]! != '\n' do
        outRev := cs[i]! :: outRev
        i := i + 1
    else if c == '/' && i + 1 < cs.size && cs[i + 1]! == '*' then
      outRev := '*' :: '/' :: outRev
      i := i + 2
      while i < cs.size do
        if cs[i]! == '*' && i + 1 < cs.size && cs[i + 1]! == '/' then
          outRev := '/' :: '*' :: outRev
          i := i + 2
          break
        outRev := cs[i]! :: outRev
        i := i + 1
    else if c == '"' then
      outRev := '"' :: outRev
      i := i + 1
      let mut esc := false
      while i < cs.size do
        let ch := cs[i]!
        outRev := ch :: outRev
        i := i + 1
        if esc then esc := false
        else if ch == '\\' then esc := true
        else if ch == '"' then break
    else if matchPrefixAt cs i "#unroll" &&
        (i + 7 < cs.size && (cs[i + 7]!.isWhitespace || cs[i + 7]! == '(')) then
      let j0 := skipWS cs (i + 7)
      unless j0 < cs.size && cs[j0]! == '(' do
        throwErrorAt stxRef "c0 template: expected '(' after #unroll"
      let (hdr, jAfterHdr) ← liftM (scanBalancedDelim cs (j0 + 1) '(' ')')
      let hdrParts := hdr.splitOn " in "
      unless hdrParts.length == 2 do
        throwErrorAt stxRef "c0 template: #unroll header must have shape `(x in $(listExpr))`"
      let varName := hdrParts[0]!.trimAscii.toString
      let rhs := hdrParts[1]!.trimAscii.toString
      unless rhs.startsWith "$(" && rhs.endsWith ")" do
        throwErrorAt stxRef "c0 template: #unroll list must be an antiquotation `$(listExpr)`"
      let listTermStr := ((rhs.drop 2).dropEnd 1).toString
      let listE ← liftM (parseAndElabLeanTerm stxRef listTermStr none)
      let listTyWhnf ← liftM (whnf (← inferType listE))
      let elemTy ← match listTyWhnf with
        | .app (.const ``List _) a => pure a
        | _ => throwErrorAt stxRef
            m!"c0 template: #unroll expected `List α`, got:{indentExpr listTyWhnf}"
      let jBody0 := skipWS cs jAfterHdr
      unless jBody0 < cs.size && cs[jBody0]! == '{' do
        throwErrorAt stxRef "c0 template: expected '\{' after #unroll header"
      let (bodyRaw, jAfterBody) ← liftM (scanBalancedDelim cs (jBody0 + 1) '{' '}')
      let uid := (← get).nextUid
      modify fun s => { s with nextUid := uid + 1 }
      let markName := s!"__c0tpl_unroll_mark_{uid}"
      let implName := s!"__c0tpl_unroll_impl_{uid}"
      let parentSt ← get
      let (bodyScanned, bodyValSplices, elemFVarId, childAfter) ← liftM <|
        withLocalDeclD (Name.mkSimple varName) elemTy fun elemFVar => do
          let childInit : ScanEnv := {
            tySplices := parentSt.tySplices
            callSplices := parentSt.callSplices
            valSplices := #[]
            unrolls := #[]
            nextSymWidthIdx := parentSt.nextSymWidthIdx
            nextUid := parentSt.nextUid
          }
          let (bSrc, childAfter) ← (scanTemplateSrc stxRef bodyRaw).run childInit
          pure (bSrc, childAfter.valSplices, elemFVar.fvarId!, childAfter)
      unless childAfter.unrolls.isEmpty do
        throwErrorAt stxRef "c0 template: nested #unroll inside #unroll is not supported"
      set {
        parentSt with
        tySplices := childAfter.tySplices
        callSplices := childAfter.callSplices
        nextSymWidthIdx := childAfter.nextSymWidthIdx
        nextUid := childAfter.nextUid
        unrolls := parentSt.unrolls.push {
          uid, markName, implName, elemName := varName, elemFVarId, elemTy, listExpr := listE
          bodyDeclsSrc := bodyScanned, bodyValSplices
        }
      }
      outRev := pushStr outRev s!"{markName}();"
      i := jAfterBody
    else if !prevWasIdent i && matchPrefixAt cs i "sbv$(" then
      let (termStr, jNext) ← liftM (scanBalancedDelim cs (i + 5) '(' ')')
      let ts ← getOrAddTySplice stxRef termStr true false
      outRev := pushStr outRev ts.aliasName
      i := jNext
    else if !prevWasIdent i && matchPrefixAt cs i "bv$(" then
      let (termStr, jNext) ← liftM (scanBalancedDelim cs (i + 4) '(' ')')
      let ts ← getOrAddTySplice stxRef termStr false false
      outRev := pushStr outRev ts.aliasName
      i := jNext
    else if !prevWasIdent i && matchPrefixAt cs i "ty$(" then
      let (termStr, jNext) ← liftM (scanBalancedDelim cs (i + 4) '(' ')')
      let ts ← getOrAddTySplice stxRef termStr false true
      outRev := pushStr outRev ts.aliasName
      i := jNext
    else if !prevWasIdent i && matchPrefixAt cs i "u$(" then
      let (termStr, jNext) ← liftM (scanBalancedDelim cs (i + 3) '(' ')')
      let ts ← getOrAddTySplice stxRef termStr false false
      outRev := pushStr outRev ts.aliasName
      i := jNext
    else if !prevWasIdent i && matchPrefixAt cs i "i$(" then
      let (termStr, jNext) ← liftM (scanBalancedDelim cs (i + 3) '(' ')')
      let ts ← getOrAddTySplice stxRef termStr true false
      outRev := pushStr outRev ts.aliasName
      i := jNext
    else if matchPrefixAt cs i "$(" then
      let (termStr, jNext) ← liftM (scanBalancedDelim cs (i + 2) '(' ')')
      let jLook := skipSpaces cs jNext
      let isCall := jLook < cs.size && cs[jLook]! == '('
      let e ← liftM (parseAndElabLeanTerm stxRef termStr none)
      let ty0 := (← liftM (inferType e)).consumeMData
      let ty ←
        if isCall &&
           (ty0.isAppOfArity ``LeanQbe.T.OpCode 2 ||
            ty0.isConstOf ``LeanQbe.T.CmpOp ||
            ty0.isAppOfArity ``LeanQbe.T.Frontend.C0.C0ExprSnippet 2 ||
            ty0.isAppOfArity ``LeanQbe.T.Func 2 ||
            ty0.isAppOfArity ``LeanQbe.T.Frontend.C0.C0StmtSnippet 1) then
          pure ty0
        else
          liftM (whnf ty0)
      if isCall then
        let st ← get
        let idx := st.callSplices.size
        if ty.isAppOfArity ``LeanQbe.T.OpCode 2 then
          let sigE := ty.getArg! 0
          let rsE := ty.getArg! 1
          let (sigExprs, _) ← leanListTyToC0Types stxRef sigE
          let (rsExprs, _) ← leanListTyToC0Types stxRef rsE
          let ph := s!"__c0tpl_op_{idx}"
          set { st with callSplices := st.callSplices.push {
            placeholderName := ph, kind := .opCode e sigExprs rsExprs
          } }
          outRev := pushStr outRev ph
        else if ty.isConstOf ``LeanQbe.T.CmpOp then
          let ph := s!"__c0tpl_cmp_{idx}"
          set { st with callSplices := st.callSplices.push {
            placeholderName := ph, kind := .cmpOp e
          } }
          outRev := pushStr outRev ph
        else if ty.isAppOfArity ``LeanQbe.T.Frontend.C0.C0ExprSnippet 2 then
          let asE := ty.getArg! 0
          let rE := ty.getArg! 1
          let (asExprs, _) ← leanListTyToC0Types stxRef asE
          let _ ← leanTyExprToC0Type stxRef rE
          let ph := s!"__c0tpl_esnip_{idx}"
          set { st with callSplices := st.callSplices.push {
            placeholderName := ph, kind := .exprSnippet e asExprs rE
          } }
          outRev := pushStr outRev ph
        else if ty.isAppOfArity ``LeanQbe.T.Func 2 then
          let asE := ty.getArg! 0
          let rsE := ty.getArg! 1
          let (asExprs, _) ← leanListTyToC0Types stxRef asE
          let (rsExprs, _) ← leanListTyToC0Types stxRef rsE
          unless rsExprs.length == 1 do
            throwErrorAt stxRef "c0 template: spliced `Func` expression must return 1 value"
          let ph := s!"__c0tpl_fsnip_{idx}"
          set { st with callSplices := st.callSplices.push {
            placeholderName := ph, kind := .funcSnippet e asExprs rsExprs[0]!
          } }
          outRev := pushStr outRev ph
        else if ty.isAppOfArity ``LeanQbe.T.Frontend.C0.C0StmtSnippet 1 then
          let tsE := ty.getArg! 0
          let (tsExprs, _) ← leanListTyToC0Types stxRef tsE
          let ph := s!"__c0tpl_ssnip_{idx}"
          set { st with callSplices := st.callSplices.push {
            placeholderName := ph, kind := .stmtSnippet e tsExprs
          } }
          outRev := pushStr outRev ph
        else
          throwErrorAt stxRef m!"c0 template: unsupported call splice type:{indentExpr ty}"
      else
        let st ← get
        let idx := st.valSplices.size
        let ph := s!"__c0tpl_val_{idx}"
        if ty.isAppOfArity ``BitVec 1 then
          let wE := ty.getArg! 0
          let tyE := LeanQbe.T.Notation.mkBitsTy wE
          let c0ty ← leanTyExprToC0Type stxRef tyE
          modify fun s => { s with valSplices := s.valSplices.push {
            placeholderName := ph, leanExpr := e, c0Ty := c0ty, tyExpr := tyE
          } }
        else if ty.isConstOf ``Bool then
          modify fun s => { s with valSplices := s.valSplices.push {
            placeholderName := ph, leanExpr := e, c0Ty := .bool
            tyExpr := LeanQbe.T.Notation.boolTyExpr
          } }
        else if ty.isConstOf ``Nat then
          let bvExpr := mkApp2 (Lean.mkConst ``BitVec.ofNat) (mkNatLit 64) e
          modify fun s => { s with valSplices := s.valSplices.push {
            placeholderName := ph, leanExpr := bvExpr, c0Ty := .u64
            tyExpr := LeanQbe.T.Notation.i64TyExpr, isNat := true, natRawExpr := some e
          } }
        else
          throwErrorAt stxRef
            m!"c0 template: unsupported value splice type (BitVec w, Nat, Bool):{indentExpr ty}"
        outRev := pushStr outRev ph
      i := jNext
    else
      outRev := c :: outRev
      i := i + 1
  pure (String.ofList outRev.reverse)

def c0TypeToDummyDeclStr : C0Type → String
  | .bool => "bool"
  | .int true 8 => "i8"
  | .int true 16 => "i16"
  | .int true 32 => "i32"
  | .int true 64 => "i64"
  | .int false 8 => "u8"
  | .int false 16 => "u16"
  | .int false 32 => "u32"
  | .int false 64 => "u64"
  | .f64 => "f64"
  | _ => "u64"

def renderC0TypeForHeader (tySplices : Array TySplice) (t : C0Type) : String :=
  match t with
  | .int signed bits =>
    match tySplices.find? (fun ts => ts.signed == signed && ts.placeholderBits == bits) with
    | some ts => ts.aliasName
    | none => c0TypeToDummyDeclStr t
  | _ => c0TypeToDummyDeclStr t

def buildPreamble (env : ScanEnv) : TermElabM String := do
  let mut lines : Array String := #[]
  for ts in env.tySplices do
    let base := if ts.signed then "i64" else "u64"
    lines := lines.push s!"typedef {base} {ts.aliasName};"
  for cs in env.callSplices do
    match cs.kind with
    | .opCode _ sigExprs rsExprs =>
      let mut sigC0s : Array C0Type := #[]
      let mut rsC0s : Array C0Type := #[]
      for sE in sigExprs do
        let (ct, _) ← (leanTyExprToC0Type Syntax.missing sE).run env
        sigC0s := sigC0s.push ct
      for rE in rsExprs do
        let (ct, _) ← (leanTyExprToC0Type Syntax.missing rE).run env
        rsC0s := rsC0s.push ct
      let retStr := match rsC0s.toList with
        | [] => "void"
        | [r] => renderC0TypeForHeader env.tySplices r
        | rs =>
          "(" ++ String.intercalate ", " (rs.map (renderC0TypeForHeader env.tySplices)) ++ ")"
      let argsStr := if sigC0s.isEmpty then "void" else
        String.intercalate ", " (sigC0s.toList.map (renderC0TypeForHeader env.tySplices))
      lines := lines.push s!"extern {retStr} {cs.placeholderName}({argsStr});"
    | .cmpOp _ =>
      lines := lines.push s!"extern bool {cs.placeholderName}();"
    | .exprSnippet _ asExprs rExpr | .funcSnippet _ asExprs rExpr =>
      let mut asC0s : Array C0Type := #[]
      for aE in asExprs do
        let (ct, _) ← (leanTyExprToC0Type Syntax.missing aE).run env
        asC0s := asC0s.push ct
      let (rC0, _) ← (leanTyExprToC0Type Syntax.missing rExpr).run env
      let retStr := renderC0TypeForHeader env.tySplices rC0
      let argsStr := if asC0s.isEmpty then "void" else
        String.intercalate ", " (asC0s.toList.map (renderC0TypeForHeader env.tySplices))
      lines := lines.push s!"extern {retStr} {cs.placeholderName}({argsStr});"
    | .stmtSnippet _ tsExprs =>
      let mut tsC0s : Array C0Type := #[]
      for tE in tsExprs do
        let (ct, _) ← (leanTyExprToC0Type Syntax.missing tE).run env
        tsC0s := tsC0s.push ct
      let tsStrs := tsC0s.toList.map (renderC0TypeForHeader env.tySplices)
      let retStr := match tsStrs with
        | [] => "void"
        | [r] => r
        | rs => "(" ++ String.intercalate ", " rs ++ ")"
      let argsStr := if tsStrs.isEmpty then "void" else String.intercalate ", " tsStrs
      lines := lines.push s!"extern {retStr} {cs.placeholderName}({argsStr});"
  for us in env.unrolls do
    lines := lines.push s!"extern void {us.markName}(void);"
  pure (String.intercalate "\n" lines.toList ++ (if lines.isEmpty then "" else "\n"))

/-! ## AST Rewriting: Typedefs, `Nat` Casts, `CmpOp` Type Inference, `#unroll` Scope -/

def patchTyTypedefs (tySplices : Array TySplice) (decls : List Decl) : List Decl :=
  decls.map fun
    | .typedef nm ty =>
      match tySplices.find? (·.aliasName == nm) with
      | some ts => .typedef nm (.int ts.signed ts.placeholderBits)
      | none => .typedef nm ty
    | d => d

partial def stmtHasControlExit : Stmt → Bool
  | .retStmt _ | .breakStmt | .continueStmt | .gotoStmt _ => true
  | .block ss => ss.any stmtHasControlExit
  | .ifStmt _ t e? => stmtHasControlExit t || (e?.map stmtHasControlExit |>.getD false)
  | .whileStmt _ b | .doWhileStmt b _ | .forStmt _ _ _ b => stmtHasControlExit b
  | .switchStmt _ arms => arms.any (fun a => a.body.any stmtHasControlExit)
  | .labelStmt _ s => stmtHasControlExit s
  | _ => false

partial def collectExprVars : C0Expr → List String
  | .var nm => [nm]
  | .cast _ e | .sizeofExpr e | .unary _ e | .field e _ | .arrow e _ => collectExprVars e
  | .binary _ l r => collectExprVars l ++ collectExprVars r
  | .ternary c t e => collectExprVars c ++ collectExprVars t ++ collectExprVars e
  | .index a i => collectExprVars a ++ collectExprVars i
  | .call _ args => args.flatMap collectExprVars
  | _ => []

partial def collectLValVars : LVal → List String
  | .var nm => [nm]
  | .deref p | .arrow p _ => collectExprVars p
  | .index a i => collectExprVars a ++ collectExprVars i
  | .dot b _ => collectLValVars b

partial def collectStmtVars : Stmt → List String
  | .decl _ _ (.expr e) => collectExprVars e
  | .assign lv _ e => collectLValVars lv ++ collectExprVars e
  | .incDec lv _ => collectLValVars lv
  | .callStmt lhs _ args => lhs ++ args.flatMap collectExprVars
  | .ifStmt c t e? =>
    collectExprVars c ++ collectStmtVars t ++ (e?.map collectStmtVars |>.getD [])
  | .whileStmt c b | .doWhileStmt b c => collectExprVars c ++ collectStmtVars b
  | .forStmt init? cond? step? b =>
    (init?.map collectStmtVars |>.getD []) ++
    (cond?.map collectExprVars |>.getD []) ++
    (step?.map collectStmtVars |>.getD []) ++
    collectStmtVars b
  | .switchStmt c arms =>
    collectExprVars c ++ arms.flatMap (fun a => a.body.flatMap collectStmtVars)
  | .block ss => ss.flatMap collectStmtVars
  | .labelStmt _ s => collectStmtVars s
  | .retStmt es => es.flatMap collectExprVars
  | .assumeStmt c | .checkStmt c _ | .assertStmt c _ => collectExprVars c
  | _ => []

partial def rewriteNatCastsInExpr (tySplices : Array TySplice) (layout : LayoutEnv)
    (e : C0Expr) : StateT (Array ValSplice) (Except String) C0Expr := do
  match e with
  | .cast dstTy (.intLit v ..) =>
    if v == 0 then
      let rDst ← liftM (resolveType layout dstTy)
      if let .int signed w := rDst then
        if let some ts := tySplices.find? (fun ts =>
            !ts.isOpaqueTy && ts.signed == signed && ts.placeholderBits == w &&
            w >= templatePlaceholderBase) then
          let st ← get
          let newIdx := st.size
          let newPh := s!"__c0tpl_val_{newIdx}"
          let tyE := LeanQbe.T.Notation.mkBitsTy ts.leanExpr
          let bvExpr := mkApp2 (Lean.mkConst ``BitVec.ofNat) ts.leanExpr (mkNatLit 0)
          set <| st.push {
            placeholderName := newPh, leanExpr := bvExpr, c0Ty := rDst, tyExpr := tyE
          }
          return .var newPh
    pure e
  | .cast dstTy (.var nm) =>
    let st ← get
    if let some vs := st.find? (fun v => v.placeholderName == nm && v.isNat) then
      let rDst ← liftM (resolveType layout dstTy)
      if let (some rawE, .int signed w) := (vs.natRawExpr, rDst) then
        let newIdx := st.size
        let newPh := s!"__c0tpl_val_{newIdx}"
        let wExpr := match tySplices.find?
            (fun ts => !ts.isOpaqueTy && ts.signed == signed && ts.placeholderBits == w) with
          | some ts => ts.leanExpr
          | none => mkNatLit w
        let tyE := LeanQbe.T.Notation.mkBitsTy wExpr
        let bvExpr := mkApp2 (Lean.mkConst ``BitVec.ofNat) wExpr rawE
        set <| st.push {
          placeholderName := newPh, leanExpr := bvExpr, c0Ty := rDst, tyExpr := tyE
          isNat := true, natRawExpr := some rawE
        }
        return .var newPh
    pure (.cast dstTy (.var nm))
  | .cast dstTy sub => return .cast dstTy (← rewriteNatCastsInExpr tySplices layout sub)
  | .unary op sub => return .unary op (← rewriteNatCastsInExpr tySplices layout sub)
  | .binary op l r =>
    return .binary op (← rewriteNatCastsInExpr tySplices layout l)
      (← rewriteNatCastsInExpr tySplices layout r)
  | .ternary c t el =>
    return .ternary (← rewriteNatCastsInExpr tySplices layout c)
      (← rewriteNatCastsInExpr tySplices layout t)
      (← rewriteNatCastsInExpr tySplices layout el)
  | .field sub fld => return .field (← rewriteNatCastsInExpr tySplices layout sub) fld
  | .arrow sub fld => return .arrow (← rewriteNatCastsInExpr tySplices layout sub) fld
  | .index a i =>
    return .index (← rewriteNatCastsInExpr tySplices layout a)
      (← rewriteNatCastsInExpr tySplices layout i)
  | .call fn args =>
    return .call fn (← args.mapM (rewriteNatCastsInExpr tySplices layout))
  | _ => pure e

partial def rewriteNatCastsInLVal (tySplices : Array TySplice) (layout : LayoutEnv) :
    LVal → StateT (Array ValSplice) (Except String) LVal
  | .deref p => return .deref (← rewriteNatCastsInExpr tySplices layout p)
  | .arrow p f => return .arrow (← rewriteNatCastsInExpr tySplices layout p) f
  | .index a i =>
    return .index (← rewriteNatCastsInExpr tySplices layout a)
      (← rewriteNatCastsInExpr tySplices layout i)
  | .dot b f => return .dot (← rewriteNatCastsInLVal tySplices layout b) f
  | lv => pure lv

partial def rewriteNatCastsInStmt (tySplices : Array TySplice) (layout : LayoutEnv) :
    Stmt → StateT (Array ValSplice) (Except String) Stmt
  | .block ss => return .block (← ss.mapM (rewriteNatCastsInStmt tySplices layout))
  | .decl ty nm (.expr e) =>
    return .decl ty nm (.expr (← rewriteNatCastsInExpr tySplices layout e))
  | .assign lv op? rhs =>
    return .assign (← rewriteNatCastsInLVal tySplices layout lv) op?
      (← rewriteNatCastsInExpr tySplices layout rhs)
  | .incDec lv isInc => return .incDec (← rewriteNatCastsInLVal tySplices layout lv) isInc
  | .callStmt lhs fn args =>
    return .callStmt lhs fn (← args.mapM (rewriteNatCastsInExpr tySplices layout))
  | .ifStmt c t e? =>
    return .ifStmt (← rewriteNatCastsInExpr tySplices layout c)
      (← rewriteNatCastsInStmt tySplices layout t)
      (← e?.mapM (rewriteNatCastsInStmt tySplices layout))
  | .whileStmt c b =>
    return .whileStmt (← rewriteNatCastsInExpr tySplices layout c)
      (← rewriteNatCastsInStmt tySplices layout b)
  | .doWhileStmt b c =>
    return .doWhileStmt (← rewriteNatCastsInStmt tySplices layout b)
      (← rewriteNatCastsInExpr tySplices layout c)
  | .forStmt i? c? s? b =>
    return .forStmt (← i?.mapM (rewriteNatCastsInStmt tySplices layout))
      (← c?.mapM (rewriteNatCastsInExpr tySplices layout))
      (← s?.mapM (rewriteNatCastsInStmt tySplices layout))
      (← rewriteNatCastsInStmt tySplices layout b)
  | .switchStmt sc arms => do
    let sc' ← rewriteNatCastsInExpr tySplices layout sc
    let arms' ← arms.mapM fun a => do
      let b' ← a.body.mapM (rewriteNatCastsInStmt tySplices layout)
      pure { a with body := b' }
    pure (.switchStmt sc' arms')
  | .labelStmt l s => return .labelStmt l (← rewriteNatCastsInStmt tySplices layout s)
  | .retStmt es => return .retStmt (← es.mapM (rewriteNatCastsInExpr tySplices layout))
  | .assumeStmt c => return .assumeStmt (← rewriteNatCastsInExpr tySplices layout c)
  | .checkStmt c ln => return .checkStmt (← rewriteNatCastsInExpr tySplices layout c) ln
  | .assertStmt c ln => return .assertStmt (← rewriteNatCastsInExpr tySplices layout c) ln
  | s => pure s

partial def rewriteStmtSnippetCallsInStmt (callSplices : Array CallSplice) :
    Stmt → Except String Stmt
  | .callStmt [] fn args =>
    if let some cs := callSplices.find? (·.placeholderName == fn) then
      match cs.kind with
      | .stmtSnippet _ ts => do
        unless args.length == ts.length do
          throw s!"statement splice '{fn}' expects {ts.length} state args, got {args.length}"
        let lhs ← args.mapM fun
          | .var nm => pure nm
          | _ => throw s!"statement splice '{fn}' arguments must be local variable names"
        pure (.callStmt lhs fn args)
      | _ => pure (.callStmt [] fn args)
    else pure (.callStmt [] fn args)
  | .block ss => return .block (← ss.mapM (rewriteStmtSnippetCallsInStmt callSplices))
  | .ifStmt c t e? =>
    return .ifStmt c (← rewriteStmtSnippetCallsInStmt callSplices t)
      (← e?.mapM (rewriteStmtSnippetCallsInStmt callSplices))
  | .whileStmt c b => return .whileStmt c (← rewriteStmtSnippetCallsInStmt callSplices b)
  | .doWhileStmt b c => return .doWhileStmt (← rewriteStmtSnippetCallsInStmt callSplices b) c
  | .forStmt i? c? s? b =>
    return .forStmt (← i?.mapM (rewriteStmtSnippetCallsInStmt callSplices)) c?
      (← s?.mapM (rewriteStmtSnippetCallsInStmt callSplices))
      (← rewriteStmtSnippetCallsInStmt callSplices b)
  | .switchStmt sc arms => do
    let arms' ← arms.mapM fun a => do
      let b' ← a.body.mapM (rewriteStmtSnippetCallsInStmt callSplices)
      pure { a with body := b' }
    pure (.switchStmt sc arms')
  | .labelStmt l s => return .labelStmt l (← rewriteStmtSnippetCallsInStmt callSplices s)
  | s => pure s

partial def findCallArgsInExpr (target : String) : C0Expr → Option (List C0Expr)
  | .call fn args =>
    if fn == target then some args else args.findSome? (findCallArgsInExpr target)
  | .cast _ e | .sizeofExpr e | .unary _ e | .field e _ | .arrow e _ => findCallArgsInExpr target e
  | .binary _ l r => findCallArgsInExpr target l <|> findCallArgsInExpr target r
  | .ternary c t e =>
    findCallArgsInExpr target c <|> findCallArgsInExpr target t <|> findCallArgsInExpr target e
  | .index a i => findCallArgsInExpr target a <|> findCallArgsInExpr target i
  | _ => none

partial def findCallWithScope (target : String) (scope : List (String × C0Type)) :
    List Stmt → Option (List C0Expr × List (String × C0Type))
  | [] => none
  | s :: rest =>
    match s with
    | .decl ty nm (.expr e) =>
      if let some args := findCallArgsInExpr target e then some (args, scope)
      else findCallWithScope target (scope ++ [(nm, ty)]) rest
    | .decl ty nm .zeroInit =>
      findCallWithScope target (scope ++ [(nm, ty)]) rest
    | .assign _ _ e =>
      if let some args := findCallArgsInExpr target e then some (args, scope)
      else findCallWithScope target scope rest
    | .callStmt _ fn args =>
      if fn == target then some (args, scope)
      else if let some cargs := args.findSome? (findCallArgsInExpr target) then some (cargs, scope)
      else findCallWithScope target scope rest
    | .ifStmt c t e? =>
      if let some args := findCallArgsInExpr target c then some (args, scope)
      else findCallWithScope target scope [t] <|>
        (e?.bind fun e => findCallWithScope target scope [e]) <|>
        findCallWithScope target scope rest
    | .whileStmt c b | .doWhileStmt b c =>
      (findCallArgsInExpr target c |>.map (·, scope)) <|>
      findCallWithScope target scope [b] <|>
      findCallWithScope target scope rest
    | .forStmt init? cond? step? b =>
      (init?.bind fun i => findCallWithScope target scope [i]) <|>
      (cond?.bind fun c => findCallArgsInExpr target c |>.map (·, scope)) <|>
      (step?.bind fun st => findCallWithScope target scope [st]) <|>
      findCallWithScope target scope [b] <|>
      findCallWithScope target scope rest
    | .block ss => findCallWithScope target scope ss <|> findCallWithScope target scope rest
    | .switchStmt c arms =>
      (findCallArgsInExpr target c |>.map (·, scope)) <|>
      (arms.findSome? fun a => findCallWithScope target scope a.body) <|>
      findCallWithScope target scope rest
    | .labelStmt _ st => findCallWithScope target scope [st] <|> findCallWithScope target scope rest
    | .retStmt es =>
      if let some args := es.findSome? (findCallArgsInExpr target) then some (args, scope)
      else findCallWithScope target scope rest
    | .assumeStmt c | .checkStmt c _ | .assertStmt c _ =>
      (findCallArgsInExpr target c |>.map (·, scope)) <|> findCallWithScope target scope rest
    | _ => findCallWithScope target scope rest

partial def rewriteUnrollMarkInStmt (markName implName : String)
    (stateVars roVars : List (String × C0Type)) : Stmt → Stmt
  | .callStmt [] fn [] =>
    if fn == markName then
      let lhs := stateVars.map (·.1)
      let args := (stateVars ++ roVars).map fun (nm, _) => LeanQbe.T.Frontend.C0.Expr.var nm
      .callStmt lhs implName args
    else .callStmt [] fn []
  | .block ss => .block (ss.map (rewriteUnrollMarkInStmt markName implName stateVars roVars))
  | .ifStmt c t e? =>
    .ifStmt c (rewriteUnrollMarkInStmt markName implName stateVars roVars t)
      (e?.map (rewriteUnrollMarkInStmt markName implName stateVars roVars))
  | .whileStmt c b => .whileStmt c (rewriteUnrollMarkInStmt markName implName stateVars roVars b)
  | .doWhileStmt b c =>
    .doWhileStmt (rewriteUnrollMarkInStmt markName implName stateVars roVars b) c
  | .forStmt i? c? s? b =>
    .forStmt (i?.map (rewriteUnrollMarkInStmt markName implName stateVars roVars)) c?
      (s?.map (rewriteUnrollMarkInStmt markName implName stateVars roVars))
      (rewriteUnrollMarkInStmt markName implName stateVars roVars b)
  | .switchStmt sc arms =>
    .switchStmt sc (arms.map fun a =>
      { a with body := a.body.map (rewriteUnrollMarkInStmt markName implName stateVars roVars) })
  | .labelStmt l s => .labelStmt l (rewriteUnrollMarkInStmt markName implName stateVars roVars s)
  | s => s

def appendValPlaceholders (fd : FnDef) (vs : Array ValSplice) : FnDef :=
  let used := (fd.body.flatMap collectStmtVars).foldl (fun s n => s.insert n)
    ({} : Std.HashSet String)
  let extra := vs.toList.filterMap fun v =>
    if used.contains v.placeholderName then some (v.c0Ty, v.placeholderName) else none
  { fd with params := fd.params ++ extra }

def inferCallArgCommonType (layout : LayoutEnv) (enums : Std.HashMap String Int)
    (fnRets : Std.HashMap String C0Type) (scope : List (String × C0Type))
    (valSplices : Array ValSplice) (a0 a1 : C0Expr) : Except String C0Type := do
  let lookupVar (nm : String) : Except String C0Type :=
    match scope.reverse.find? (·.1 == nm) with
    | some (_, t) => pure t
    | none =>
      match valSplices.find? (·.placeholderName == nm) with
      | some v => pure v.c0Ty
      | none =>
        match enums.get? nm with
        | some v => pure (intLitType v .none true)
        | none => throw s!"c0 template: unbound variable '{nm}' in comparator splice"
  let lookupFnRet (fn : String) : Except String C0Type :=
    match fnRets.get? fn with
    | some t => pure t
    | none => throw s!"c0 template: unknown function '{fn}' in comparator splice"
  let t0 ← resolveType layout (← inferExprType layout lookupVar lookupFnRet a0)
  let t1 ← resolveType layout (← inferExprType layout lookupVar lookupFnRet a1)
  if t0 == t1 then pure t0
  else match t0, t1 with
  | .ptr _, .ptr _ => pure (.ptr .void)
  | _, _ => usualArithType t0 t1


end LeanQbe.T.Frontend.C0

end
