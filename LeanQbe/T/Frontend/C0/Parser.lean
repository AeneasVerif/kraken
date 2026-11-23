module

public import LeanQbe.T.Frontend.C0.Syntax
public import LeanQbe.T.Frontend.C0.Lexer
import Std.Data.HashMap
import Std.Data.HashSet

/-!
# Self-Contained C0 Recursive-Descent Parser (`X0-core`)

Parses real `.c` / `.h` source strings directly into `C0.TranslationUnit`:
* `parseC0 : String → Except String TranslationUnit`
* Handles `typedef` disambiguation, `struct`/`union` (with anonymous nested aggregates,
  bitfields, fixed arrays, and trailing `T arr[];`), `C0_RET2`/`C0_RET3`, `C0_TUP2`/`C0_TUP3`,
  `C0_TIE2`/`C0_TIE3`, `(T1, T2)` multi-return syntax, `c0_assume`, `check`, `assert`,
  and ordered `switch` arms.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Frontend.C0

/-! ## Parser State & Primitives -/

private structure ParseState where
  toks : Array Tok
  pos : Nat := 0
  typedefs : Std.HashSet String
  structs : Std.HashSet String
  unions : Std.HashSet String
  consts : Std.HashMap String Int

private abbrev ParserM := StateT ParseState (Except String)

private def defaultTypedefs : Std.HashSet String :=
  Std.HashSet.ofList
    [ "uint8_t", "uint16_t", "uint32_t", "uint64_t"
    , "int8_t", "int16_t", "int32_t", "int64_t"
    , "size_t", "uintptr_t", "intptr_t", "ptrdiff_t"
    , "c0_u64_bool", "c0_u64_u64", "c0_u32_bool", "c0_u32_u32"
    ]

private def peekTok (off : Nat := 0) : ParserM Tok := do
  let st ← get
  pure (st.toks[st.pos + off]?.getD { kind := .eof, line := 0 })

private def nextTok : ParserM Tok := do
  let tok ← peekTok
  modify fun st => { st with pos := st.pos + 1 }
  pure tok

private def tokDesc : TokKind → String
  | .ident s => s!"identifier '{s}'"
  | .intLit v _ _ => s!"integer literal {v}"
  | .floatLit _ => "float literal"
  | .strLit s => s!"string literal \"{s}\""
  | .kw s => s!"keyword '{s}'"
  | .sym s => s!"symbol '{s}'"
  | .eof => "end of file"

private def failAt {α : Type} (msg : String) : ParserM α := do
  let tok ← peekTok
  throw s!"C0 parse error (line {tok.line}, at {tokDesc tok.kind}): {msg}"

private def liftExceptAt {α : Type} : Except String α → ParserM α
  | .ok a => pure a
  | .error msg => failAt msg

private def expectSym (s : String) : ParserM Unit := do
  let tok ← peekTok
  if tok.kind == .sym s then
    let _ ← nextTok
  else
    failAt s!"expected '{s}', got {tokDesc tok.kind}"

private def matchSym (s : String) : ParserM Bool := do
  let tok ← peekTok
  if tok.kind == .sym s then
    let _ ← nextTok
    pure true
  else pure false

private def matchKw (s : String) : ParserM Bool := do
  let tok ← peekTok
  if tok.kind == .kw s then
    let _ ← nextTok
    pure true
  else pure false

private def expectIdent : ParserM String := do
  let tok ← nextTok
  match tok.kind with
  | .ident s => pure s
  | _ => throw s!"C0 parse error (line {tok.line}): expected identifier, got {tokDesc tok.kind}"

private def tryBacktrack {α : Type} (p : ParserM α) : ParserM (Option α) := do
  let saved ← get
  match p.run saved with
  | .ok (a, st') => set st'; pure (some a)
  | .error _ => set saved; pure none

/-! ## Type Parsing -/

private def isQualifier : TokKind → Bool
  | .kw "const" | .kw "volatile" => true
  | _ => false

private partial def skipQualifiers : ParserM Unit := do
  let tok ← peekTok
  if isQualifier tok.kind then
    let _ ← nextTok
    skipQualifiers

private def builtinTypeMap (s : String) : Option C0Type :=
  match s with
  | "void" => some .void
  | "bool" | "_Bool" => some .bool
  | "u8" | "uint8_t" => some C0Type.u8
  | "u16" | "uint16_t" => some C0Type.u16
  | "u32" | "uint32_t" | "ref" => some C0Type.u32
  | "u64" | "uint64_t" | "size_t" | "uintptr_t" => some C0Type.u64
  | "i8" | "int8_t" => some C0Type.i8
  | "i16" | "int16_t" => some C0Type.i16
  | "i32" | "int32_t" => some C0Type.i32
  | "i64" | "int64_t" | "intptr_t" | "ptrdiff_t" => some C0Type.i64
  | "f64" | "double" => some .f64
  | _ => none

private def isTypeStart : ParserM Bool := do
  let saved ← get
  skipQualifiers
  let tok ← peekTok
  set saved
  match tok.kind with
  | .kw "void" | .kw "bool" | .kw "_Bool" | .kw "char" | .kw "short" | .kw "int"
  | .kw "long" | .kw "signed" | .kw "unsigned" | .kw "double" | .kw "f64"
  | .kw "u8" | .kw "u16" | .kw "u32" | .kw "u64"
  | .kw "i8" | .kw "i16" | .kw "i32" | .kw "i64" | .kw "ref"
  | .kw "struct" | .kw "union" => pure true
  | .ident "C0_RET2" | .ident "C0_RET3" => pure true
  | .ident s =>
    let st ← get
    pure ((builtinTypeMap s).isSome || st.typedefs.contains s)
  | _ => pure false

private partial def evalConstIntExpr (consts : Std.HashMap String Int) : Expr → Except String Int
  | .intLit v _ _ => pure v
  | .boolLit b => pure (if b then 1 else 0)
  | .var nm => match consts.get? nm with
    | some v => pure v
    | none => throw s!"unknown constant '{nm}' in integer constant expression"
  | .unary .neg e => do pure (-(← evalConstIntExpr consts e))
  | .unary .pos e => evalConstIntExpr consts e
  | .unary .bitnot e => do pure (~~~(← evalConstIntExpr consts e))
  | .binary .add a b => do pure ((← evalConstIntExpr consts a) + (← evalConstIntExpr consts b))
  | .binary .sub a b => do pure ((← evalConstIntExpr consts a) - (← evalConstIntExpr consts b))
  | .binary .mul a b => do pure ((← evalConstIntExpr consts a) * (← evalConstIntExpr consts b))
  | .binary .shl a b => do
    let va ← evalConstIntExpr consts a
    let vb ← evalConstIntExpr consts b
    pure (va * Int.ofNat (2 ^ vb.toNat))
  | _ => throw "expected integer constant expression"

mutual
  private partial def parseBaseType : ParserM C0Type := do
    skipQualifiers
    let tok ← peekTok
    match tok.kind with
    | .kw "struct" | .kw "union" =>
      let isUnion := tok.kind == .kw "union"
      let _ ← nextTok
      let next ← peekTok
      match next.kind with
      | .sym "{" =>
        let fields ← parseFieldBlock
        pure (.anonAggregate isUnion fields)
      | .ident name =>
        let _ ← nextTok
        if (← peekTok).kind == .sym "{" then
          let fields ← parseFieldBlock
          if isUnion then
            modify fun st => { st with unions := st.unions.insert name }
          else
            modify fun st => { st with structs := st.structs.insert name }
          -- Note: inline struct/union definition
          pure (.anonAggregate isUnion fields)
        else
          pure (if isUnion then .unionRef name else .structRef name)
      | _ => failAt s!"expected struct/union name or '\{', got {tokDesc next.kind}"
    | .ident "C0_RET2" =>
      let _ ← nextTok
      expectSym "("
      let t0 ← parseType
      expectSym ","
      let t1 ← parseType
      expectSym ")"
      pure (.tuple [t0, t1])
    | .ident "C0_RET3" =>
      let _ ← nextTok
      expectSym "("
      let t0 ← parseType
      expectSym ","
      let t1 ← parseType
      expectSym ","
      let t2 ← parseType
      expectSym ")"
      pure (.tuple [t0, t1, t2])
    | .kw "signed" | .kw "unsigned" | .kw "char" | .kw "short" | .kw "int" | .kw "long" =>
      let mut isUnsigned := false
      let mut isSigned := false
      let mut hasChar := false
      let mut hasShort := false
      let mut longCount : Nat := 0
      let mut hasInt := false
      let mut keepGoing := true
      while keepGoing do
        let t ← peekTok
        match t.kind with
        | .kw "unsigned" => isUnsigned := true; let _ ← nextTok
        | .kw "signed" => isSigned := true; let _ ← nextTok
        | .kw "char" => hasChar := true; let _ ← nextTok
        | .kw "short" => hasShort := true; let _ ← nextTok
        | .kw "long" => longCount := longCount + 1; let _ ← nextTok
        | .kw "int" => hasInt := true; let _ ← nextTok
        | _ => keepGoing := false
        skipQualifiers
      let signed := !isUnsigned
      let _ := (isSigned, hasInt)
      if hasChar then pure (.int signed 8)
      else if hasShort then pure (.int signed 16)
      else if longCount >= 1 then pure (.int signed 64)
      else pure (.int signed 32)
    | .kw s =>
      if let some ty := builtinTypeMap s then
        let _ ← nextTok
        pure ty
      else failAt s!"expected type, got {tokDesc tok.kind}"
    | .ident s =>
      if let some ty := builtinTypeMap s then
        let _ ← nextTok
        pure ty
      else
        let st ← get
        if st.typedefs.contains s then
          let _ ← nextTok
          pure (.typedefRef s)
        else failAt s!"unknown type name '{s}' (at {tokDesc tok.kind})"
    | _ => failAt s!"expected type, got {tokDesc tok.kind}"

  private partial def parsePtrStars (base : C0Type) : ParserM C0Type := do
    let mut ty := base
    while true do
      skipQualifiers
      if ← matchSym "*" then
        ty := .ptr ty
        skipQualifiers
      else break
    pure ty

  private partial def parseType : ParserM C0Type := do
    let base ← parseBaseType
    parsePtrStars base

  private partial def parseFieldBlock : ParserM (List FieldDecl) := do
    expectSym "{"
    let mut fields : List FieldDecl := []
    while !(← matchSym "}") do
      let base ← parseBaseType
      -- Support comma-separated fields like `u32 a, b;`
      let mut more := true
      while more do
        let ty0 ← parsePtrStars base
        let mut fname : Option String := none
        if let .ident s := (← peekTok).kind then
          let _ ← nextTok
          fname := some s
        let mut bw : Option Nat := none
        let mut fty := ty0
        if ← matchSym ":" then
          let wTok ← nextTok
          match wTok.kind with
          | .intLit w _ _ =>
            if w < 0 then
              throw s!"C0 parse error (line {wTok.line}): negative bitfield width {w}"
            bw := some w.toNat
          | _ =>
            throw s!"C0 parse error (line {wTok.line}): expected bitfield width, got {
              tokDesc wTok.kind}"
        else
          let mut dims : List (Option Nat) := []
          while ← matchSym "[" do
            if ← matchSym "]" then
              dims := dims ++ [none]
            else
              let lenExpr ← parseExpr
              expectSym "]"
              let csts := (← get).consts
              let len ← match evalConstIntExpr csts lenExpr with
                | .ok v => if v < 0 then failAt "negative array length" else pure v.toNat
                | .error e => failAt e
              dims := dims ++ [some len]
          fty := dims.foldr (fun d acc => .array acc d) fty
        fields := fields ++ [{ name := fname, ty := fty, bitWidth := bw }]
        more ← matchSym ","
      expectSym ";"
    pure fields

  private partial def parsePrimary : ParserM Expr := do
    let tok ← peekTok
    match tok.kind with
    | .kw "true" => let _ ← nextTok; pure (.boolLit true)
    | .kw "false" => let _ ← nextTok; pure (.boolLit false)
    | .kw "NULL" => let _ ← nextTok; pure .null
    | .intLit v suf isDec => let _ ← nextTok; pure (.intLit v suf isDec)
    | .floatLit bits => let _ ← nextTok; pure (.floatLit bits)
    | .ident s => let _ ← nextTok; pure (.var s)
    | .sym "(" =>
      let _ ← nextTok
      let e ← parseExpr
      expectSym ")"
      pure e
    | _ => failAt s!"expected expression, got {tokDesc tok.kind}"

  private partial def parsePostfix : ParserM Expr := do
    let mut e ← parsePrimary
    while true do
      let tok ← peekTok
      match tok.kind with
      | .sym "[" =>
        let _ ← nextTok
        let idx ← parseExpr
        expectSym "]"
        e := .index e idx
      | .sym "." =>
        let _ ← nextTok
        let fld ← expectIdent
        e := .field e fld
      | .sym "->" =>
        let _ ← nextTok
        let fld ← expectIdent
        e := .arrow e fld
      | .sym "(" =>
        match e with
        | .var fn => e := .call fn (← parseCallArgs)
        | _ => failAt s!"indirect function calls are not supported in C0 (got {tokDesc tok.kind})"
      | _ => break
    pure e

  private partial def parseUnary : ParserM Expr := do
    let tok ← peekTok
    match tok.kind with
    | .sym "-" => let _ ← nextTok; pure (.unary .neg (← parseCast))
    | .sym "+" => let _ ← nextTok; pure (.unary .pos (← parseCast))
    | .sym "~" => let _ ← nextTok; pure (.unary .bitnot (← parseCast))
    | .sym "!" => let _ ← nextTok; pure (.unary .lognot (← parseCast))
    | .sym "*" => let _ ← nextTok; pure (.unary .deref (← parseCast))
    | .sym "&" => let _ ← nextTok; pure (.unary .addrOf (← parseCast))
    | .kw "sizeof" =>
      let _ ← nextTok
      if (← peekTok).kind == .sym "(" then
        let tyOpt ← tryBacktrack do
          expectSym "("
          unless ← isTypeStart do failAt "not a type"
          let ty ← parseType
          expectSym ")"
          pure ty
        match tyOpt with
        | some ty => pure (.sizeofTy ty)
        | none =>
          expectSym "("
          let e ← parseExpr
          expectSym ")"
          pure (.sizeofExpr e)
      else
        pure (.sizeofExpr (← parseUnary))
    | _ => parsePostfix

  private partial def parseCast : ParserM Expr := do
    if (← peekTok).kind == .sym "(" then
      let castOpt ← tryBacktrack do
        expectSym "("
        unless ← isTypeStart do failAt "not a type"
        let ty ← parseType
        expectSym ")"
        let e ← parseCast
        pure (Expr.cast ty e)
      if let some ce := castOpt then
        return ce
    parseUnary

  private partial def parseMul : ParserM Expr := do
    let mut e ← parseCast
    while true do
      if ← matchSym "*" then e := .binary .mul e (← parseCast)
      else if ← matchSym "/" then e := .binary .div e (← parseCast)
      else if ← matchSym "%" then e := .binary .mod e (← parseCast)
      else break
    pure e

  private partial def parseAdd : ParserM Expr := do
    let mut e ← parseMul
    while true do
      if ← matchSym "+" then e := .binary .add e (← parseMul)
      else if ← matchSym "-" then e := .binary .sub e (← parseMul)
      else break
    pure e

  private partial def parseShift : ParserM Expr := do
    let mut e ← parseAdd
    while true do
      if ← matchSym "<<" then e := .binary .shl e (← parseAdd)
      else if ← matchSym ">>" then e := .binary .shr e (← parseAdd)
      else break
    pure e

  private partial def parseRel : ParserM Expr := do
    let mut e ← parseShift
    while true do
      if ← matchSym "<" then e := .binary .lt e (← parseShift)
      else if ← matchSym "<=" then e := .binary .le e (← parseShift)
      else if ← matchSym ">" then e := .binary .gt e (← parseShift)
      else if ← matchSym ">=" then e := .binary .ge e (← parseShift)
      else break
    pure e

  private partial def parseEq : ParserM Expr := do
    let mut e ← parseRel
    while true do
      if ← matchSym "==" then e := .binary .eq e (← parseRel)
      else if ← matchSym "!=" then e := .binary .ne e (← parseRel)
      else break
    pure e

  private partial def parseBitAnd : ParserM Expr := do
    let mut e ← parseEq
    while ← matchSym "&" do
      e := .binary .bitand e (← parseEq)
    pure e

  private partial def parseBitXor : ParserM Expr := do
    let mut e ← parseBitAnd
    while ← matchSym "^" do
      e := .binary .bitxor e (← parseBitAnd)
    pure e

  private partial def parseBitOr : ParserM Expr := do
    let mut e ← parseBitXor
    while ← matchSym "|" do
      e := .binary .bitor e (← parseBitXor)
    pure e

  private partial def parseLogAnd : ParserM Expr := do
    let mut e ← parseBitOr
    while ← matchSym "&&" do
      e := .binary .logand e (← parseBitOr)
    pure e

  private partial def parseLogOr : ParserM Expr := do
    let mut e ← parseLogAnd
    while ← matchSym "||" do
      e := .binary .logor e (← parseLogAnd)
    pure e

  private partial def parseTernary : ParserM Expr := do
    let c ← parseLogOr
    if ← matchSym "?" then
      let t ← parseExpr
      expectSym ":"
      let e ← parseTernary
      pure (.ternary c t e)
    else
      pure c

  private partial def parseCallArgs : ParserM (List Expr) := do
    expectSym "("
    let mut args : List Expr := []
    if !(← matchSym ")") then
      args := args ++ [← parseExpr]
      while ← matchSym "," do
        args := args ++ [← parseExpr]
      expectSym ")"
    pure args

  private partial def parseExpr : ParserM Expr :=
    parseTernary
end

/-! ## Statements -/

private def exprToLVal : Expr → Except String LVal
  | .var x => pure (.var x)
  | .unary .deref p => pure (.deref p)
  | .arrow p f => pure (.arrow p f)
  | .index a i => pure (.index a i)
  | .field base f => do pure (.dot (← exprToLVal base) f)
  | e => throw s!"expression is not an assignable lvalue: {repr e}"

private def parseAssignOp? : ParserM (Option (Option BinOp)) := do
  let tok ← peekTok
  let op? : Option (Option BinOp) := match tok.kind with
    | .sym "=" => some none
    | .sym "+=" => some (some .add)
    | .sym "-=" => some (some .sub)
    | .sym "*=" => some (some .mul)
    | .sym "/=" => some (some .div)
    | .sym "%=" => some (some .mod)
    | .sym "&=" => some (some .bitand)
    | .sym "|=" => some (some .bitor)
    | .sym "^=" => some (some .bitxor)
    | .sym "<<=" => some (some .shl)
    | .sym ">>=" => some (some .shr)
    | _ => none
  if op?.isSome then
    let _ ← nextTok
  pure op?

private def parseSimpleCall : ParserM (String × List Expr) := do
  let fn ← expectIdent
  pure (fn, ← parseCallArgs)

private def parseInitVal : ParserM InitVal := do
  expectSym "="
  if ← matchSym "{" then
    let z ← parseExpr
    match z with
    | .intLit 0 _ _ => expectSym "}"; pure InitVal.zeroInit
    | _ => failAt "only `{0}` aggregate zero-initializer is supported"
  else
    pure (.expr (← parseExpr))

private def parseSimpleAction : ParserM Stmt := do
  if ← isTypeStart then
    let ty ← parseType
    let name ← expectIdent
    pure (.decl ty name (← parseInitVal))
  else if (← peekTok).kind == .sym "++" || (← peekTok).kind == .sym "--" then
    let isInc := (← nextTok).kind == .sym "++"
    let e ← parseUnary
    let lv ← liftExceptAt (exprToLVal e)
    pure (.incDec lv isInc)
  else
    let e ← parseUnary
    if ← matchSym "++" then
      pure (.incDec (← liftExceptAt (exprToLVal e)) true)
    else if ← matchSym "--" then
      pure (.incDec (← liftExceptAt (exprToLVal e)) false)
    else if let some binOp? ← parseAssignOp? then
      let lv ← liftExceptAt (exprToLVal e)
      pure (.assign lv binOp? (← parseExpr))
    else
      match e with
      | .call fn args => pure (.callStmt [] fn args)
      | _ =>
        let tok ← peekTok
        failAt s!"expected assignment, call, or increment/decrement, got {tokDesc tok.kind}"

private def parseLocalDecls : ParserM (List Stmt) := do
  let base ← parseBaseType
  let mut stmts : List Stmt := []
  let mut more := true
  while more do
    let ty ← parsePtrStars base
    let name ← expectIdent
    if (← peekTok).kind == .sym "[" then
      failAt s!"stack arrays are not supported in C0 (variable '{name}', got '[')"
    stmts := stmts ++ [.decl ty name (← parseInitVal)]
    more ← matchSym ","
  expectSym ";"
  pure stmts

mutual
  private partial def parseBlockStmts : ParserM (List Stmt) := do
    expectSym "{"
    let mut acc : List Stmt := []
    while !(← matchSym "}") do
      acc := acc ++ (← parseStmtListItem)
    pure acc

  private partial def parseStmtListItem : ParserM (List Stmt) := do
    if ← isTypeStart then
      parseLocalDecls
    else
      pure [← parseStmt]

  private partial def parseStmt : ParserM Stmt := do
    let tok ← peekTok
    match tok.kind with
    | .sym ";" => let _ ← nextTok; pure .empty
    | .sym "{" => pure (.block (← parseBlockStmts))
    | .kw "if" =>
      let _ ← nextTok
      expectSym "("
      let cond ← parseExpr
      expectSym ")"
      let thn ← parseStmt
      let els ← if ← matchKw "else" then some <$> parseStmt else pure none
      pure (.ifStmt cond thn els)
    | .kw "while" =>
      let _ ← nextTok
      expectSym "("
      let cond ← parseExpr
      expectSym ")"
      let body ← parseStmt
      pure (.whileStmt cond body)
    | .kw "do" =>
      let _ ← nextTok
      let body ← parseStmt
      if !(← matchKw "while") then
        failAt s!"expected 'while' after do body, got {tokDesc (← peekTok).kind}"
      expectSym "("
      let cond ← parseExpr
      expectSym ")"
      expectSym ";"
      pure (.doWhileStmt body cond)
    | .kw "for" =>
      let _ ← nextTok
      expectSym "("
      let init? ←
        if ← matchSym ";" then pure none
        else
          let s ← parseSimpleAction
          expectSym ";"
          pure (some s)
      let cond? ←
        if ← matchSym ";" then pure none
        else
          let c ← parseExpr
          expectSym ";"
          pure (some c)
      let step? ←
        if ← matchSym ")" then pure none
        else
          let s ← parseSimpleAction
          expectSym ")"
          pure (some s)
      let body ← parseStmt
      pure (.forStmt init? cond? step? body)
    | .kw "switch" =>
      let _ ← nextTok
      expectSym "("
      let scrut ← parseExpr
      expectSym ")"
      expectSym "{"
      let mut arms : List SwitchArm := []
      while !(← matchSym "}") do
        let mut vals : List Int := []
        let mut hasDef := false
        let mut anyLbl := false
        while true do
          if ← matchKw "case" then
            anyLbl := true
            let csts := (← get).consts
            let v ← liftExceptAt (evalConstIntExpr csts (← parseExpr))
            expectSym ":"
            vals := vals ++ [v]
          else if ← matchKw "default" then
            anyLbl := true
            expectSym ":"
            hasDef := true
          else break
        unless anyLbl do
          failAt s!"expected 'case' or 'default' in switch, got {tokDesc (← peekTok).kind}"
        let mut body : List Stmt := []
        while (← peekTok).kind != .sym "}" && (← peekTok).kind != .kw "case" &&
            (← peekTok).kind != .kw "default" do
          if ← matchKw "fallthrough" then
            expectSym ";"
          else
            body := body ++ (← parseStmtListItem)
        arms := arms ++ [{ vals, hasDefault := hasDef, body }]
      pure (.switchStmt scrut arms)
    | .kw "break" => let _ ← nextTok; expectSym ";"; pure .breakStmt
    | .kw "continue" => let _ ← nextTok; expectSym ";"; pure .continueStmt
    | .kw "goto" =>
      let _ ← nextTok
      let lbl ← expectIdent
      expectSym ";"
      pure (.gotoStmt lbl)
    | .kw "return" =>
      let _ ← nextTok
      if ← matchSym ";" then
        pure (.retStmt [])
      else if (← peekTok).kind == .ident "C0_TUP2" then
        let _ ← nextTok
        expectSym "("
        let _ ← parseType
        expectSym ","
        let e0 ← parseExpr
        expectSym ","
        let e1 ← parseExpr
        expectSym ")"
        expectSym ";"
        pure (.retStmt [e0, e1])
      else if (← peekTok).kind == .ident "C0_TUP3" then
        let _ ← nextTok
        expectSym "("
        let _ ← parseType
        expectSym ","
        let e0 ← parseExpr
        expectSym ","
        let e1 ← parseExpr
        expectSym ","
        let e2 ← parseExpr
        expectSym ")"
        expectSym ";"
        pure (.retStmt [e0, e1, e2])
      else
        let tupOpt ← tryBacktrack do
          expectSym "("
          let e0 ← parseExpr
          expectSym ","
          let mut es := [e0, ← parseExpr]
          while ← matchSym "," do
            es := es ++ [← parseExpr]
          expectSym ")"
          expectSym ";"
          pure es
        match tupOpt with
        | some es => pure (.retStmt es)
        | none =>
          let e ← parseExpr
          expectSym ";"
          pure (.retStmt [e])
    | .ident "c0_assume" =>
      let _ ← nextTok
      expectSym "("
      let c ← parseExpr
      expectSym ")"
      expectSym ";"
      pure (.assumeStmt c)
    | .ident "check" =>
      let line := tok.line
      let _ ← nextTok
      expectSym "("
      let c ← parseExpr
      expectSym ")"
      expectSym ";"
      pure (.checkStmt c line)
    | .ident "assert" =>
      let line := tok.line
      let _ ← nextTok
      expectSym "("
      let c ← parseExpr
      expectSym ")"
      expectSym ";"
      pure (.assertStmt c line)
    | .ident "C0_TIE2" =>
      let _ ← nextTok
      expectSym "("
      let x0 ← expectIdent
      expectSym ","
      let x1 ← expectIdent
      expectSym ","
      let (fn, args) ← parseSimpleCall
      expectSym ")"
      expectSym ";"
      pure (.callStmt [x0, x1] fn args)
    | .ident "C0_TIE3" =>
      let _ ← nextTok
      expectSym "("
      let x0 ← expectIdent
      expectSym ","
      let x1 ← expectIdent
      expectSym ","
      let x2 ← expectIdent
      expectSym ","
      let (fn, args) ← parseSimpleCall
      expectSym ")"
      expectSym ";"
      pure (.callStmt [x0, x1, x2] fn args)
    | .ident lbl =>
      if (← peekTok 1).kind == .sym ":" then
        let _ ← nextTok; let _ ← nextTok
        let s ← parseStmt
        pure (.labelStmt lbl s)
      else
        let s ← parseSimpleAction
        expectSym ";"
        pure s
    | .sym "(" =>
      let tieOpt ← tryBacktrack do
        expectSym "("
        let x0 ← expectIdent
        expectSym ","
        let mut xs := [x0, ← expectIdent]
        while ← matchSym "," do
          xs := xs ++ [← expectIdent]
        expectSym ")"
        expectSym "="
        let (fn, args) ← parseSimpleCall
        expectSym ";"
        pure (Stmt.callStmt xs fn args)
      match tieOpt with
      | some s => pure s
      | none =>
        let s ← parseSimpleAction
        expectSym ";"
        pure s
    | _ =>
      let s ← parseSimpleAction
      expectSym ";"
      pure s
end

/-! ## Top-Level Declarations -/

private def parseParams : ParserM (List (C0Type × Option String)) := do
  expectSym "("
  if ← matchSym ")" then
    pure []
  else if (← peekTok).kind == .kw "void" && (← peekTok 1).kind == .sym ")" then
    let _ ← nextTok; let _ ← nextTok
    pure []
  else
    let mut ps : List (C0Type × Option String) := []
    let mut more := true
    while more do
      let ty ← parseType
      let nm? ←
        match (← peekTok).kind with
        | .ident s => let _ ← nextTok; pure (some s)
        | _ => pure none
      ps := ps ++ [(ty, nm?)]
      more ← matchSym ","
    expectSym ")"
    pure ps

private def parseTopDecl : ParserM (List Decl) := do
  let tok ← peekTok
  match tok.kind with
  | .kw "typedef" =>
    let _ ← nextTok
    let cur ← peekTok
    if (cur.kind == .kw "struct" || cur.kind == .kw "union") &&
       ((← peekTok 1).kind == .sym "{" || (← peekTok 2).kind == .sym "{") then
      let isUnion := cur.kind == .kw "union"
      let _ ← nextTok
      let tag? ← match (← peekTok).kind with
        | .ident s => let _ ← nextTok; pure (some s)
        | _ => pure none
      let fields ← parseFieldBlock
      let aliasName ← expectIdent
      expectSym ";"
      modify fun st => { st with typedefs := st.typedefs.insert aliasName }
      match tag? with
      | some tag =>
        if isUnion then modify fun st => { st with unions := st.unions.insert tag }
        else modify fun st => { st with structs := st.structs.insert tag }
        let refTy := if isUnion then C0Type.unionRef tag else C0Type.structRef tag
        pure [ .structDef { name := tag, isUnion, fields }
             , .typedef aliasName refTy ]
      | none =>
        pure [.typedef aliasName (.anonAggregate isUnion fields)]
    else
      let ty ← parseType
      let aliasName ← expectIdent
      expectSym ";"
      modify fun st => { st with typedefs := st.typedefs.insert aliasName }
      match ty with
      | .structRef s => modify fun st => { st with structs := st.structs.insert s }
      | .unionRef u => modify fun st => { st with unions := st.unions.insert u }
      | _ => pure ()
      pure [.typedef aliasName ty]
  | .kw "struct" | .kw "union" =>
    -- Could be `struct foo { ... };` or `struct foo;` OR a function returning `struct foo *fn(...)`
    let saved ← get
    let isStructDef :=
      ((← peekTok 1).kind matches .ident _) &&
      ((← peekTok 2).kind == .sym "{" || (← peekTok 2).kind == .sym ";")
    if isStructDef then
      let isUnion := tok.kind == .kw "union"
      let _ ← nextTok
      let name ← expectIdent
      if ← matchSym ";" then
        if isUnion then modify fun st => { st with unions := st.unions.insert name }
        else modify fun st => { st with structs := st.structs.insert name }
        pure []
      else
        let fields ← parseFieldBlock
        expectSym ";"
        if isUnion then modify fun st => { st with unions := st.unions.insert name }
        else modify fun st => { st with structs := st.structs.insert name }
        pure [.structDef { name, isUnion, fields }]
    else
      set saved
      parseFnDeclOrDef
  | .kw "enum" =>
    let _ ← nextTok
    if let .ident _ := (← peekTok).kind then
      let _ ← nextTok
    if ← matchSym ";" then
      pure []
    else
      expectSym "{"
      let mut nextVal : Int := 0
      let mut items : List (String × Int) := []
      while !(← matchSym "}") do
        let nm ← expectIdent
        if ← matchSym "=" then
          let e ← parseExpr
          let csts := (← get).consts
          nextVal ← liftExceptAt (evalConstIntExpr csts e)
        items := items ++ [(nm, nextVal)]
        modify fun st => { st with consts := st.consts.insert nm nextVal }
        nextVal := nextVal + 1
        if !(← matchSym ",") then
          expectSym "}"
          break
      expectSym ";"
      pure [.enumConsts items]
  | _ => parseFnDeclOrDef
where
  parseFnDeclOrDef : ParserM (List Decl) := do
    let mut isStatic := false
    let mut isInline := false
    while true do
      if ← matchKw "static" then isStatic := true
      else if ← matchKw "inline" then isInline := true
      else if ← matchKw "__inline__" then isInline := true
      else if ← matchKw "extern" then pure ()
      else break
    let retTy ←
      if (← peekTok).kind == .sym "(" then
        expectSym "("
        let t0 ← parseType
        let mut ts := [t0]
        while ← matchSym "," do
          ts := ts ++ [← parseType]
        expectSym ")"
        pure (.tuple ts)
      else
        parseType
    let name ← expectIdent
    let params ← parseParams
    if ← matchSym ";" then
      pure [.fnDecl { retTy, name, params }]
    else
      let namedParams ← params.mapM fun (t, nm?) => do
        match nm? with
        | some nm => pure (t, nm)
        | none => failAt s!"function '{name}' definition requires named parameters"
      let body ← parseBlockStmts
      pure [.fnDef { isStatic, isInline, retTy, name, params := namedParams, body }]

/-- Parse a C0 `.c`/`.h` source string into a `TranslationUnit`. -/
def parseC0 (src : String) : Except String TranslationUnit := do
  let toks ← tokenize src
  let initState : ParseState := {
    toks := toks
    pos := 0
    typedefs := defaultTypedefs
    structs := {}
    unions := {}
    consts := {}
  }
  let rec go : ParserM (List Decl) := do
    let mut decls : List Decl := []
    while (← peekTok).kind != .eof do
      decls := decls ++ (← parseTopDecl)
    pure decls
  let (decls, _) ← go.run initState
  pure { decls }

end LeanQbe.T.Frontend.C0
