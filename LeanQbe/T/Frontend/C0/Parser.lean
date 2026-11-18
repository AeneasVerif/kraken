module

public import LeanQbe.T.Frontend.C0.Syntax
import Std.Data.HashMap
import Std.Data.HashSet

/-!
# Self-Contained C0 Lexer and Recursive-Descent Parser (`X0-core`)

Parses real `.c` / `.h` source strings directly into `C0.TranslationUnit`:
* `parseC0 : String → Except String TranslationUnit`
* Ignores `#include`, `#pragma`, `#ifndef`/`#ifdef`/`#endif` cleanly while tracking `#define NAME INT`
  constants and exact 1-based line numbers for `check(cond);`.
* Handles `typedef` disambiguation, `struct`/`union` (with anonymous nested aggregates,
  bitfields, fixed arrays, and trailing `T arr[];`), `C0_RET2`/`C0_RET3`, `C0_TUP2`/`C0_TUP3`,
  `C0_TIE2`/`C0_TIE3`, `(T1, T2)` multi-return syntax, `c0_assume`, `check`, `assert`,
  and `fallthrough;`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Frontend.C0

/-! ## Lexer -/

inductive TokKind : Type
  | ident (s : String)
  | intLit (val : Int) (suffix : IntSuffix)
  | floatLit (bits : UInt64)
  | strLit (s : String)
  | kw (s : String)
  | sym (s : String)
  | eof
  deriving Repr, BEq, Inhabited

structure Tok : Type where
  kind : TokKind
  line : Nat
  deriving Repr, BEq, Inhabited

private def c0Keywords : Std.HashSet String :=
  Std.HashSet.ofList
    [ "typedef", "struct", "union", "enum", "static", "inline", "__inline__", "extern"
    , "const", "volatile", "void", "bool", "_Bool", "char", "short", "int", "long"
    , "signed", "unsigned", "double", "f64", "u8", "u16", "u32", "u64"
    , "i8", "i16", "i32", "i64", "ref", "if", "else", "while", "do", "for"
    , "switch", "case", "default", "break", "continue", "return", "goto"
    , "fallthrough", "sizeof", "true", "false", "NULL"
    ]

private def isIdentStart (c : Char) : Bool :=
  c.isAlpha || c == '_'

private def isIdentCont (c : Char) : Bool :=
  c.isAlphanum || c == '_'

private def isHexDigit (c : Char) : Bool :=
  c.isDigit || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')

private def hexVal (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat
  else if 'a' ≤ c && c ≤ 'f' then 10 + (c.toNat - 'a'.toNat)
  else 10 + (c.toNat - 'A'.toNat)

private def isOctDigit (c : Char) : Bool :=
  '0' ≤ c && c ≤ '7'

private structure LexState where
  chars : Array Char
  idx : Nat := 0
  line : Nat := 1
  atLineStart : Bool := true

private def LexState.peek? (s : LexState) (off : Nat := 0) : Option Char :=
  s.chars[s.idx + off]?

private def LexState.advance (s : LexState) (n : Nat := 1) : LexState :=
  Id.run do
    let mut cur := s
    for _ in [:n] do
      match cur.chars[cur.idx]? with
      | none => break
      | some c =>
        let nl := c == '\n'
        cur := {
          chars := cur.chars
          idx := cur.idx + 1
          line := if nl then cur.line + 1 else cur.line
          atLineStart := if nl then true else if c.isWhitespace then cur.atLineStart else false
        }
    return cur

private partial def skipLineComment (s : LexState) : LexState :=
  match s.peek? with
  | none => s
  | some '\n' => s.advance
  | some _ => skipLineComment s.advance

private partial def skipBlockComment (s : LexState) : Except String LexState :=
  match s.peek?, s.peek? 1 with
  | none, _ => throw s!"unterminated block comment at line {s.line}"
  | some '*', some '/' => pure (s.advance 2)
  | _, _ => skipBlockComment s.advance

private partial def readPreprocessorLine (s : LexState) (acc : List Char := []) : String × LexState :=
  match s.peek?, s.peek? 1 with
  | none, _ => (String.ofList acc.reverse, s)
  | some '\n', _ => (String.ofList acc.reverse, s.advance)
  | some '\\', some '\n' => readPreprocessorLine (s.advance 2) (' ' :: acc)
  | some '\\', some '\r' =>
    match s.peek? 2 with
    | some '\n' => readPreprocessorLine (s.advance 3) (' ' :: acc)
    | _ => readPreprocessorLine s.advance ('\\' :: acc)
  | some '/', some '/' =>
    let s' := skipLineComment s
    (String.ofList acc.reverse, s')
  | some '/', some '*' =>
    match skipBlockComment s with
    | .ok s' => readPreprocessorLine s' (' ' :: acc)
    | .error _ => (String.ofList acc.reverse, s.advance)
  | some c, _ => readPreprocessorLine s.advance (c :: acc)

private def parseIntSuffix (cs : List Char) : IntSuffix × Nat :=
  let lower := cs.take 3 |>.map Char.toLower
  match lower with
  | 'u' :: 'l' :: 'l' :: _ => (.ull, 3)
  | 'l' :: 'l' :: 'u' :: _ => (.ull, 3)
  | 'u' :: 'l' :: _ => (.ul, 2)
  | 'l' :: 'u' :: _ => (.ul, 2)
  | 'l' :: 'l' :: _ => (.ll, 2)
  | 'u' :: _ => (.u, 1)
  | 'l' :: _ => (.l, 1)
  | _ => (.none, 0)

private def parseScientificFloat (mantDigits : List Char) (expSign : Bool) (expDigits : List Char) :
    Except String UInt64 := do
  let mut mant : Nat := 0
  for d in mantDigits do
    mant := mant * 10 + (d.toNat - '0'.toNat)
  let mut exp : Nat := 0
  for d in expDigits do
    exp := exp * 10 + (d.toNat - '0'.toNat)
  let f := Float.ofScientific mant expSign exp
  pure f.toBits

private partial def lexNumber (s : LexState) : Except String (Tok × LexState) := do
  let line := s.line
  let mut cur := s
  let mut chars : List Char := []
  if cur.peek? == some '0' && (cur.peek? 1 == some 'x' || cur.peek? 1 == some 'X') then
    cur := cur.advance 2
    let mut n : Nat := 0
    let mut count := 0
    while true do
      match cur.peek? with
      | some c =>
        if isHexDigit c then
          n := n * 16 + hexVal c
          count := count + 1
          cur := cur.advance
        else break
      | none => break
    if count == 0 then
      throw s!"invalid hex literal at line {line}"
    let mut sufChars : List Char := []
    for i in [:3] do
      if let some c := cur.peek? i then sufChars := sufChars ++ [c]
    let (suf, slen) := parseIntSuffix sufChars
    cur := cur.advance slen
    return ({ kind := .intLit (Int.ofNat n) suf, line }, cur)
  else if cur.peek? == some '0' && (cur.peek? 1 == some 'b' || cur.peek? 1 == some 'B') then
    cur := cur.advance 2
    let mut n : Nat := 0
    let mut count := 0
    while true do
      match cur.peek? with
      | some '0' => n := n * 2; count := count + 1; cur := cur.advance
      | some '1' => n := n * 2 + 1; count := count + 1; cur := cur.advance
      | _ => break
    if count == 0 then
      throw s!"invalid binary literal at line {line}"
    let mut sufChars : List Char := []
    for i in [:3] do
      if let some c := cur.peek? i then sufChars := sufChars ++ [c]
    let (suf, slen) := parseIntSuffix sufChars
    cur := cur.advance slen
    return ({ kind := .intLit (Int.ofNat n) suf, line }, cur)
  -- Decimal or octal int, or floating point
  let mut intDigits : List Char := []
  while true do
    match cur.peek? with
    | some c =>
      if c.isDigit then
        intDigits := intDigits ++ [c]
        chars := chars ++ [c]
        cur := cur.advance
      else break
    | none => break
  let isFloat := cur.peek? == some '.' || cur.peek? == some 'e' || cur.peek? == some 'E'
  if isFloat then
    let mut fracDigits : List Char := []
    if cur.peek? == some '.' then
      cur := cur.advance
      while true do
        match cur.peek? with
        | some c =>
          if c.isDigit then
            fracDigits := fracDigits ++ [c]
            cur := cur.advance
          else break
        | none => break
    let mut expNeg := false
    let mut expVal : Int := 0
    if cur.peek? == some 'e' || cur.peek? == some 'E' then
      cur := cur.advance
      if cur.peek? == some '-' then
        expNeg := true; cur := cur.advance
      else if cur.peek? == some '+' then
        cur := cur.advance
      let mut hasExp := false
      while true do
        match cur.peek? with
        | some c =>
          if c.isDigit then
            hasExp := true
            expVal := expVal * 10 + Int.ofNat (c.toNat - '0'.toNat)
            cur := cur.advance
          else break
        | none => break
      if !hasExp then throw s!"invalid float exponent at line {line}"
    if cur.peek? == some 'f' || cur.peek? == some 'F' || cur.peek? == some 'l' || cur.peek? == some 'L' then
      cur := cur.advance
    let signedExp : Int := (if expNeg then -expVal else expVal) - Int.ofNat fracDigits.length
    let expSign := signedExp < 0
    let expNat := if signedExp < 0 then (-signedExp).toNat else signedExp.toNat
    let mantDigits := intDigits ++ fracDigits
    let mut mant : Nat := 0
    for d in mantDigits do
      mant := mant * 10 + (d.toNat - '0'.toNat)
    let bits := (Float.ofScientific mant expSign expNat).toBits
    return ({ kind := .floatLit bits, line }, cur)
  else
    let n : Nat :=
      if intDigits.head? == some '0' && intDigits.length > 1 then
        Id.run do
          let mut acc : Nat := 0
          for c in intDigits do
            if isOctDigit c then acc := acc * 8 + (c.toNat - '0'.toNat)
          return acc
      else
        Id.run do
          let mut acc : Nat := 0
          for c in intDigits do
            acc := acc * 10 + (c.toNat - '0'.toNat)
          return acc
    let mut sufChars : List Char := []
    for i in [:3] do
      if let some c := cur.peek? i then sufChars := sufChars ++ [c]
    let (suf, slen) := parseIntSuffix sufChars
    cur := cur.advance slen
    return ({ kind := .intLit (Int.ofNat n) suf, line }, cur)

private def lexCharLit (s : LexState) : Except String (Tok × LexState) := do
  let line := s.line
  let cur := s.advance -- skip opening '
  match cur.peek? with
  | none => throw s!"unterminated char literal at line {line}"
  | some '\\' =>
    let cur1 := cur.advance
    let (code, cur2) ← match cur1.peek? with
      | some 'n' => pure (10, cur1.advance)
      | some 't' => pure (9, cur1.advance)
      | some 'r' => pure (13, cur1.advance)
      | some '0' => pure (0, cur1.advance)
      | some '\\' => pure ('\\'.toNat, cur1.advance)
      | some '\'' => pure ('\''.toNat, cur1.advance)
      | some '"' => pure ('"'.toNat, cur1.advance)
      | some 'x' =>
        match cur1.peek? 1, cur1.peek? 2 with
        | some h1, some h2 =>
          if isHexDigit h1 && isHexDigit h2 then
            pure (hexVal h1 * 16 + hexVal h2, cur1.advance 3)
          else throw s!"invalid hex escape at line {line}"
        | _, _ => throw s!"invalid hex escape at line {line}"
      | _ => throw s!"unsupported char escape at line {line}"
    if cur2.peek? != some '\'' then
      throw s!"unterminated char literal at line {line}"
    return ({ kind := .intLit (Int.ofNat code) .none, line }, cur2.advance)
  | some c =>
    let cur1 := cur.advance
    if cur1.peek? != some '\'' then
      throw s!"unterminated char literal at line {line}"
    return ({ kind := .intLit (Int.ofNat c.toNat) .none, line }, cur1.advance)

private partial def lexStringLit (s : LexState) (acc : List Char := []) :
    Except String (Tok × LexState) := do
  let line := s.line
  let cur := s.advance
  let rec go (st : LexState) (cs : List Char) : Except String (String × LexState) :=
    match st.peek? with
    | none => throw s!"unterminated string literal at line {line}"
    | some '"' => pure (String.ofList cs.reverse, st.advance)
    | some '\\' =>
      match st.peek? 1 with
      | none => throw s!"unterminated string escape at line {line}"
      | some c => go (st.advance 2) (c :: cs)
    | some c => go st.advance (c :: cs)
  let (str, cur') ← go cur acc
  return ({ kind := .strLit str, line }, cur')

private def twoCharSyms : List String :=
  [ "->", "++", "--", "<<", ">>", "<=", ">=", "==", "!=", "&&", "||"
  , "+=", "-=", "*=", "/=", "%=", "&=", "|=", "^="
  ]

private def threeCharSyms : List String :=
  [ "<<=", ">>=" ]

private def oneCharSyms : List Char :=
  ['+', '-', '*', '/', '%', '&', '|', '^', '~', '!', '<', '>', '=', '.', '?', ':', ';', ',', '(', ')', '{', '}', '[', ']']

private def tryParseSimpleDefine (body : String) : Option (String × Int × IntSuffix) := do
  let trimmed := body.trimAscii.toString
  -- split name and rest
  let chars := trimmed.toList
  let nameCs := chars.takeWhile isIdentCont
  guard (!nameCs.isEmpty)
  let restCs := chars.drop nameCs.length
  -- reject function-like macro `#define FOO(x) ...`
  guard (restCs.head? != some '(')
  let valStr := (String.ofList restCs).trimAscii.toString
  guard (!valStr.isEmpty)
  -- strip outer parens if simple `(-1)`
  let valStr :=
    if valStr.startsWith "(" && valStr.endsWith ")" then
      ((valStr.drop 1).dropEnd 1).trimAscii.toString
    else valStr
  let neg := valStr.startsWith "-"
  let numStr := if neg then (valStr.drop 1).trimAscii.toString else valStr
  if numStr == "true" then return (String.ofList nameCs, 1, .none)
  if numStr == "false" then return (String.ofList nameCs, 0, .none)
  if numStr == "NULL" then return (String.ofList nameCs, 0, .ull)
  guard (!numStr.isEmpty && numStr.toList.head?.all Char.isDigit)
  -- lex single number
  let st : LexState := { chars := numStr.toList.toArray }
  match lexNumber st with
  | .ok ({ kind := .intLit v suf, .. }, st') =>
    if st'.idx == st'.chars.size then
      some (String.ofList nameCs, if neg then -v else v, suf)
    else none
  | _ => none

private partial def tokenize (src : String) :
    Except String (Array Tok × Std.HashMap String (Int × IntSuffix)) := do
  let mut st : LexState := { chars := src.toList.toArray }
  let mut toks : Array Tok := #[]
  let mut defines : Std.HashMap String (Int × IntSuffix) := {}
  while st.idx < st.chars.size do
    let some c := st.peek? | break
    if c.isWhitespace then
      st := st.advance
    else if c == '/' && st.peek? 1 == some '/' then
      st := skipLineComment st
    else if c == '/' && st.peek? 1 == some '*' then
      st ← skipBlockComment st
    else if c == '#' && st.atLineStart then
      let (lineText, st') := readPreprocessorLine st.advance
      st := st'
      let trimmed := lineText.trimAscii.toString
      if trimmed.startsWith "define" then
        let rest := (trimmed.drop 6).trimAscii.toString
        if let some (nm, v, suf) := tryParseSimpleDefine rest then
          defines := defines.insert nm (v, suf)
    else if isIdentStart c then
      let line := st.line
      let mut cs : List Char := []
      while true do
        match st.peek? with
        | some ch =>
          if isIdentCont ch then
            cs := ch :: cs; st := st.advance
          else break
        | none => break
      let word := String.ofList cs.reverse
      let kind := if c0Keywords.contains word then .kw word else .ident word
      toks := toks.push { kind, line }
    else if c.isDigit then
      let (tok, st') ← lexNumber st
      toks := toks.push tok
      st := st'
    else if c == '\'' then
      let (tok, st') ← lexCharLit st
      toks := toks.push tok
      st := st'
    else if c == '"' then
      let (tok, st') ← lexStringLit st
      toks := toks.push tok
      st := st'
    else
      let line := st.line
      let s3 := String.ofList (([st.peek?, st.peek? 1, st.peek? 2]).filterMap id)
      let s2 := String.ofList (([st.peek?, st.peek? 1]).filterMap id)
      if threeCharSyms.contains s3 then
        toks := toks.push { kind := .sym s3, line }
        st := st.advance 3
      else if twoCharSyms.contains s2 then
        toks := toks.push { kind := .sym s2, line }
        st := st.advance 2
      else if oneCharSyms.contains c then
        toks := toks.push { kind := .sym (String.singleton c), line }
        st := st.advance
      else
        throw s!"unexpected character '{c}' at line {line}"
  toks := toks.push { kind := .eof, line := st.line }
  return (toks, defines)

/-! ## Parser State & Primitives -/

private structure ParseState where
  toks : Array Tok
  pos : Nat := 0
  typedefs : Std.HashSet String
  structs : Std.HashSet String
  unions : Std.HashSet String
  consts : Std.HashMap String (Int × IntSuffix)

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

private def failAt {α : Type} (msg : String) : ParserM α := do
  let tok ← peekTok
  throw s!"C0 parse error (line {tok.line}): {msg}"

private def expectSym (s : String) : ParserM Unit := do
  let tok ← peekTok
  if tok.kind == .sym s then
    let _ ← nextTok
  else
    failAt s!"expected '{s}', got {repr tok.kind}"

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
  | _ => throw s!"C0 parse error (line {tok.line}): expected identifier, got {repr tok.kind}"

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

private partial def evalConstIntExpr : Expr → Except String Int
  | .intLit v _ => pure v
  | .boolLit b => pure (if b then 1 else 0)
  | .unary .neg e => do pure (-(← evalConstIntExpr e))
  | .unary .pos e => evalConstIntExpr e
  | .unary .bitnot e => do pure (~~~(← evalConstIntExpr e))
  | .binary .add a b => do pure ((← evalConstIntExpr a) + (← evalConstIntExpr b))
  | .binary .sub a b => do pure ((← evalConstIntExpr a) - (← evalConstIntExpr b))
  | .binary .mul a b => do pure ((← evalConstIntExpr a) * (← evalConstIntExpr b))
  | .binary .shl a b => do
    let va ← evalConstIntExpr a
    let vb ← evalConstIntExpr b
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
      | _ => failAt "expected struct/union name or '{'"
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
      else failAt s!"expected type, got keyword '{s}'"
    | .ident s =>
      if let some ty := builtinTypeMap s then
        let _ ← nextTok
        pure ty
      else
        let st ← get
        if st.typedefs.contains s then
          let _ ← nextTok
          pure (.typedefRef s)
        else failAt s!"unknown type name '{s}'"
    | _ => failAt s!"expected type, got {repr tok.kind}"

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
          | .intLit w _ =>
            if w < 0 then throw s!"C0 parse error (line {wTok.line}): negative bitfield width"
            bw := some w.toNat
          | _ => throw s!"C0 parse error (line {wTok.line}): expected bitfield width"
        else
          while ← matchSym "[" do
            if ← matchSym "]" then
              fty := .array fty none
            else
              let lenExpr ← parseExpr
              expectSym "]"
              let len ← match evalConstIntExpr lenExpr with
                | .ok v => if v < 0 then failAt "negative array length" else pure v.toNat
                | .error e => failAt e
              fty := .array fty (some len)
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
    | .intLit v suf => let _ ← nextTok; pure (.intLit v suf)
    | .floatLit bits => let _ ← nextTok; pure (.floatLit bits)
    | .ident s =>
      let _ ← nextTok
      let st ← get
      if let some (v, suf) := st.consts.get? s then
        if (← peekTok).kind != .sym "(" then
          return .intLit v suf
      pure (.var s)
    | .sym "(" =>
      let _ ← nextTok
      let e ← parseExpr
      expectSym ")"
      pure e
    | _ => failAt s!"expected expression, got {repr tok.kind}"

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
        | .var fn =>
          let _ ← nextTok
          let mut args : List Expr := []
          if !(← matchSym ")") then
            args := args ++ [← parseExpr]
            while ← matchSym "," do
              args := args ++ [← parseExpr]
            expectSym ")"
          e := .call fn args
        | _ => failAt "indirect function calls are not supported in C0"
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
  expectSym "("
  let mut args : List Expr := []
  if !(← matchSym ")") then
    args := args ++ [← parseExpr]
    while ← matchSym "," do
      args := args ++ [← parseExpr]
    expectSym ")"
  pure (fn, args)

private def parseSimpleAction : ParserM Stmt := do
  if ← isTypeStart then
    let base ← parseBaseType
    let ty ← parsePtrStars base
    let name ← expectIdent
    expectSym "="
    if ← matchSym "{" then
      let z ← parseExpr
      match z with
      | .intLit 0 _ => expectSym "}"; pure (.decl ty name .zeroInit)
      | _ => failAt "only `{0}` aggregate zero-initializer is supported"
    else
      let e ← parseExpr
      pure (.decl ty name (.expr e))
  else if (← peekTok).kind == .sym "++" || (← peekTok).kind == .sym "--" then
    let isInc := (← nextTok).kind == .sym "++"
    let e ← parseUnary
    let lv ← MonadExcept.ofExcept (exprToLVal e)
    pure (.incDec lv isInc)
  else
    let e ← parseUnary
    if ← matchSym "++" then
      let lv ← MonadExcept.ofExcept (exprToLVal e)
      pure (.incDec lv true)
    else if ← matchSym "--" then
      let lv ← MonadExcept.ofExcept (exprToLVal e)
      pure (.incDec lv false)
    else if let some binOp? ← parseAssignOp? then
      let lv ← MonadExcept.ofExcept (exprToLVal e)
      let rhs ← parseExpr
      pure (.assign lv binOp? rhs)
    else
      match e with
      | .call fn args => pure (.callStmt [] fn args)
      | _ => failAt "expected assignment, call, or increment/decrement"

private def parseLocalDecls : ParserM (List Stmt) := do
  let base ← parseBaseType
  let mut stmts : List Stmt := []
  let mut more := true
  while more do
    let ty ← parsePtrStars base
    let name ← expectIdent
    if (← peekTok).kind == .sym "[" then
      failAt "stack arrays are not supported in C0"
    expectSym "="
    let init ←
      if ← matchSym "{" then
        let z ← parseExpr
        match z with
        | .intLit 0 _ => expectSym "}"; pure InitVal.zeroInit
        | _ => failAt "only `{0}` aggregate zero-initializer is supported"
      else
        pure (.expr (← parseExpr))
    stmts := stmts ++ [.decl ty name init]
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
      if !(← matchKw "while") then failAt "expected 'while' after do body"
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
      let mut cases : List SwitchCase := []
      let mut default? : Option (List Stmt) := none
      while !(← matchSym "}") do
        if ← matchKw "default" then
          expectSym ":"
          let mut body : List Stmt := []
          while (← peekTok).kind != .sym "}" && (← peekTok).kind != .kw "case" do
            body := body ++ (← parseStmtListItem)
          default? := some body
        else if ← matchKw "case" then
          let mut vals : List Int := []
          let v0 ← evalConstIntExpr (← parseExpr) |> MonadExcept.ofExcept
          expectSym ":"
          vals := [v0]
          while ← matchKw "case" do
            let vi ← evalConstIntExpr (← parseExpr) |> MonadExcept.ofExcept
            expectSym ":"
            vals := vals ++ [vi]
          let mut body : List Stmt := []
          let mut isFall := false
          while (← peekTok).kind != .sym "}" && (← peekTok).kind != .kw "case" && (← peekTok).kind != .kw "default" do
            if ← matchKw "fallthrough" then
              expectSym ";"
              isFall := true
              break
            body := body ++ (← parseStmtListItem)
          cases := cases ++ [{ vals, body, fallthrough := isFall }]
        else
          failAt "expected 'case' or 'default' in switch"
      pure (.switchStmt scrut cases default?)
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
          nextVal ← MonadExcept.ofExcept (evalConstIntExpr e)
        items := items ++ [(nm, nextVal)]
        modify fun st => { st with consts := st.consts.insert nm (nextVal, .none) }
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
  let (toks, defines) ← tokenize src
  let initState : ParseState := {
    toks := toks
    pos := 0
    typedefs := defaultTypedefs
    structs := {}
    unions := {}
    consts := defines
  }
  let rec go : ParserM (List Decl) := do
    let mut decls : List Decl := []
    while (← peekTok).kind != .eof do
      decls := decls ++ (← parseTopDecl)
    pure decls
  let (decls, _) ← go.run initState
  pure { decls }

end LeanQbe.T.Frontend.C0
