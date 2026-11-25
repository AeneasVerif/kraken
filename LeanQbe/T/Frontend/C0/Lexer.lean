module

public import LeanQbe.T.Frontend.C0.Syntax
public import Std.Data.HashMap
public import Std.Data.HashSet

/-!
# Self-Contained C0 Lexer & Preprocessor

Tokenizes `.c`/`.h` source strings with exact 1-based line numbers, object-like and
function-like/variadic `#define`/`#undef` macro expansion, scoped `#include`,
`#pragma c0_*` directives, `#if`/`#ifdef`/`#ifndef`/`#elif`/`#else`/`#endif`,
and C99 numeric/char/float literals.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Frontend.C0

/-! ## Lexer -/

inductive TokKind : Type
  | ident (s : String)
  | intLit (val : Int) (suffix : IntSuffix) (isDecimal : Bool := true)
  | floatLit (bits : UInt64)
  | strLit (s : String)
  | kw (s : String)
  | sym (s : String)
  | pragma (p : C0Pragma)
  | eof
  deriving Repr, BEq, Inhabited

structure Tok : Type where
  kind : TokKind
  line : Nat
  deriving Repr, BEq, Inhabited

structure FuncMacro : Type where
  params : List String
  isVariadic : Bool
  body : Array Tok
  deriving Repr, BEq, Inhabited

private def c0Keywords : Std.HashSet String :=
  Std.HashSet.ofList
    [ "typedef", "struct", "union", "enum", "static", "inline", "__inline__", "extern"
    , "const", "volatile", "void", "bool", "_Bool", "char", "short", "int", "long"
    , "signed", "unsigned", "double", "f64", "u8", "u16", "u32", "u64"
    , "i8", "i16", "i32", "i64", "ref", "if", "else", "while", "do", "for"
    , "switch", "case", "default", "break", "continue", "return", "goto"
    , "fallthrough", "sizeof", "offsetof", "__builtin_offsetof"
    , "_Static_assert", "static_assert"
    , "true", "false", "NULL"
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

private partial def readPreprocessorLine (s : LexState) (acc : List Char := [])
    (inStr : Bool := false) (inChar : Bool := false) : String × LexState :=
  match s.peek?, s.peek? 1 with
  | none, _ => (String.ofList acc.reverse, s)
  | some '\n', _ => (String.ofList acc.reverse, s.advance)
  | some '\\', some '\n' => readPreprocessorLine (s.advance 2) (' ' :: acc) inStr inChar
  | some '\\', some '\r' =>
    match s.peek? 2 with
    | some '\n' => readPreprocessorLine (s.advance 3) (' ' :: acc) inStr inChar
    | _ => readPreprocessorLine s.advance ('\\' :: acc) inStr inChar
  | some '\\', some c =>
    if inStr || inChar then
      readPreprocessorLine (s.advance 2) (c :: '\\' :: acc) inStr inChar
    else
      readPreprocessorLine s.advance ('\\' :: acc) false false
  | some '"', _ =>
    let inStr' := if inChar then inStr else !inStr
    readPreprocessorLine s.advance ('"' :: acc) inStr' inChar
  | some '\'', _ =>
    let inChar' := if inStr then inChar else !inChar
    readPreprocessorLine s.advance ('\'' :: acc) inStr inChar'
  | some '/', some '/' =>
    if inStr || inChar then readPreprocessorLine s.advance ('/' :: acc) inStr inChar
    else (String.ofList acc.reverse, skipLineComment s)
  | some '/', some '*' =>
    if inStr || inChar then readPreprocessorLine s.advance ('/' :: acc) inStr inChar
    else
      match skipBlockComment s with
      | .ok s' => readPreprocessorLine s' (' ' :: acc) false false
      | .error _ => (String.ofList acc.reverse, s.advance)
  | some c, _ => readPreprocessorLine s.advance (c :: acc) inStr inChar

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
    return ({ kind := .intLit (Int.ofNat n) suf false, line }, cur)
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
    return ({ kind := .intLit (Int.ofNat n) suf false, line }, cur)
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
    if let some sc := cur.peek? then
      if sc == 'f' || sc == 'F' || sc == 'l' || sc == 'L' then
        throw (s!"unsupported float literal suffix '{sc}' at line {line}; " ++
          "C0 supports double (f64) literals only")
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
    let isOct := intDigits.head? == some '0' && intDigits.length > 1
    let isDec := intDigits.head? != some '0'
    let n : Nat :=
      if isOct then
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
    return ({ kind := .intLit (Int.ofNat n) suf isDec, line }, cur)

private def lexCharLit (s : LexState) : Except String (Tok × LexState) := do
  let line := s.line
  let cur := s.advance -- skip opening '
  let finish (code : Nat) (stAfter : LexState) : Except String (Tok × LexState) := do
    if stAfter.peek? != some '\'' then
      throw s!"unterminated char literal at line {line}"
    let b := code % 256
    let sval : Int := if b >= 128 then Int.ofNat b - 256 else Int.ofNat b
    return ({ kind := .intLit sval .none true, line }, stAfter.advance)
  match cur.peek? with
  | none => throw s!"unterminated char literal at line {line}"
  | some '\\' =>
    let cur1 := cur.advance
    let simpleEsc? : Option Nat := match cur1.peek? with
      | some 'a' => some 7 | some 'b' => some 8 | some 'f' => some 12
      | some 'n' => some 10 | some 'r' => some 13 | some 't' => some 9 | some 'v' => some 11
      | some '\\' => some '\\'.toNat | some '\'' => some '\''.toNat
      | some '"' => some '"'.toNat | some '?' => some '?'.toNat
      | _ => none
    if let some code := simpleEsc? then
      finish code cur1.advance
    else if cur1.peek? == some 'x' then
      let mut stx := cur1.advance; let mut v : Nat := 0; let mut cnt := 0
      while cnt < 2 do
        match stx.peek? with
        | some h =>
          if isHexDigit h then v := v * 16 + hexVal h; stx := stx.advance; cnt := cnt + 1
          else break
        | none => break
      if cnt == 0 then throw s!"invalid hex escape at line {line}"
      finish v stx
    else if (cur1.peek?.map isOctDigit).getD false then
      let mut sto := cur1; let mut v : Nat := 0; let mut cnt := 0
      while cnt < 3 do
        match sto.peek? with
        | some d =>
          if isOctDigit d then
            v := v * 8 + (d.toNat - '0'.toNat); sto := sto.advance; cnt := cnt + 1
          else break
        | none => break
      finish v sto
    else throw s!"unsupported char escape at line {line}"
  | some c =>
    finish c.toNat cur.advance

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
  [ '+', '-', '*', '/', '%', '&', '|', '^', '~', '!', '<', '>', '=', '.', '?', ':', ';', ','
  , '(', ')', '{', '}', '[', ']' ]

private partial def lexSingleToken (st : LexState) : Except String (Option Tok × LexState) := do
  let mut cur := st
  while cur.idx < cur.chars.size do
    let some c := cur.peek? | break
    if c.isWhitespace then cur := cur.advance
    else if c == '/' && cur.peek? 1 == some '/' then cur := skipLineComment cur
    else if c == '/' && cur.peek? 1 == some '*' then cur ← skipBlockComment cur
    else break
  let some c := cur.peek? | return (none, cur)
  let line := cur.line
  if isIdentStart c then
    let mut cs : List Char := []
    while true do
      match cur.peek? with
      | some ch => if isIdentCont ch then cs := ch :: cs; cur := cur.advance else break
      | none => break
    let word := String.ofList cs.reverse
    let kind := if c0Keywords.contains word then .kw word else .ident word
    return (some { kind, line }, cur)
  else if c.isDigit then
    let (tok, cur') ← lexNumber cur
    return (some tok, cur')
  else if c == '\'' then
    let (tok, cur') ← lexCharLit cur
    return (some tok, cur')
  else if c == '"' then
    let (tok, cur') ← lexStringLit cur
    return (some tok, cur')
  else
    let s3 := String.ofList (([cur.peek?, cur.peek? 1, cur.peek? 2]).filterMap id)
    let s2 := String.ofList (([cur.peek?, cur.peek? 1]).filterMap id)
    if threeCharSyms.contains s3 then
      return (some { kind := .sym s3, line }, cur.advance 3)
    else if twoCharSyms.contains s2 then
      return (some { kind := .sym s2, line }, cur.advance 2)
    else if oneCharSyms.contains c then
      return (some { kind := .sym (String.singleton c), line }, cur.advance)
    else
      throw s!"unexpected character '{c}' at line {line}"

private partial def tokenizeLineStr (line : Nat) (body : String) : Except String (Array Tok) := do
  let mut st : LexState := { chars := body.toList.toArray, line, atLineStart := false }
  let mut out : Array Tok := #[]
  while st.idx < st.chars.size do
    let (tok?, st') ← lexSingleToken st
    st := st'
    match tok? with
    | some t => out := out.push t
    | none => break
  return out

private def isValidParamName (s : String) : Bool :=
  if s.isEmpty then false
  else
    let cs := s.toList
    isIdentStart cs.head! && cs.all isIdentCont

private def substituteMacroParams (line : Nat) (nm : String) (fm : FuncMacro)
    (args : List (Array Tok)) : Except String (Array Tok) := do
  let posParams := if fm.isVariadic then fm.params.dropLast else fm.params
  let minArgs := posParams.length
  let mut map : Std.HashMap String (Array Tok) := {}
  if fm.isVariadic then
    let actualArgs := if minArgs == 0 && args.length == 1 && args[0]!.isEmpty then [] else args
    if actualArgs.length < minArgs then
      throw (s!"macro '{nm}' requires at least {minArgs} argument(s), " ++
        s!"got {actualArgs.length} at line {line}")
    for i in [:minArgs] do
      if let (some param, some arg) := (posParams[i]?, actualArgs[i]?) then
        map := map.insert param arg
    let vaArgs := actualArgs.drop minArgs
    let mut vaToks : Array Tok := #[]
    let mut first := true
    for va in vaArgs do
      if !first then
        vaToks := vaToks.push { kind := .sym ",", line }
      for t in va do
        vaToks := vaToks.push t
      first := false
    map := map.insert "__VA_ARGS__" vaToks
  else if posParams.isEmpty then
    let actualArgs := if args.length == 1 && args[0]!.isEmpty then [] else args
    if !actualArgs.isEmpty then
      throw s!"macro '{nm}' takes 0 argument(s), got {actualArgs.length} at line {line}"
  else
    let actualArgs := if posParams.length == 1 && args.isEmpty then [ #[] ] else args
    if actualArgs.length != posParams.length then
      throw (s!"macro '{nm}' passed {actualArgs.length} argument(s), " ++
        s!"but takes {posParams.length} at line {line}")
    for i in [:posParams.length] do
      if let (some param, some arg) := (posParams[i]?, actualArgs[i]?) then
        map := map.insert param arg
  let mut out : Array Tok := #[]
  for bt in fm.body do
    match bt.kind with
    | .ident pnm | .kw pnm =>
      if let some repl := map.get? pnm then
        for aTok in repl do out := out.push aTok
      else
        out := out.push { bt with line }
    | _ => out := out.push { bt with line }
  return out

private def parseArgsFromTokArray (nm : String) (toks : Array Tok) (startIdx : Nat) :
    Except String (List (Array Tok) × Nat) := do
  if toks[startIdx]?.map (·.kind) != some (.sym "(") then
    throw s!"expected '(' for macro '{nm}'"
  let mut idx := startIdx + 1
  let mut depth := 1
  let mut currentArg : Array Tok := #[]
  let mut args : List (Array Tok) := []
  let mut hasAnyToken := false
  while idx < toks.size && depth > 0 do
    let tok := toks[idx]!
    match tok.kind with
    | .sym "(" =>
      depth := depth + 1
      currentArg := currentArg.push tok
      idx := idx + 1
      hasAnyToken := true
    | .sym ")" =>
      depth := depth - 1
      idx := idx + 1
      if depth == 0 then
        if hasAnyToken || !args.isEmpty then
          args := args ++ [currentArg]
        break
      else
        currentArg := currentArg.push tok
        hasAnyToken := true
    | .sym "," =>
      idx := idx + 1
      if depth == 1 then
        args := args ++ [currentArg]
        currentArg := #[]
        hasAnyToken := false
      else
        currentArg := currentArg.push tok
        hasAnyToken := true
    | _ =>
      currentArg := currentArg.push tok
      idx := idx + 1
      hasAnyToken := true
  if depth != 0 then
    throw s!"unterminated invocation of macro '{nm}'"
  return (args, idx)

mutual
  private partial def expandFuncMacro (macros : Std.HashMap String (Array Tok))
      (funcMacros : Std.HashMap String FuncMacro)
      (useLine : Nat) (nm : String) (fm : FuncMacro) (args : List (Array Tok))
      (seen : Std.HashSet String) : Except String (Array Tok) := do
    let expArgs ← args.mapM fun arg =>
      expandMacroToks macros funcMacros useLine arg seen false
    let subst ← substituteMacroParams useLine nm fm expArgs
    expandMacroToks macros funcMacros useLine subst (seen.insert nm) false

  private partial def expandMacroToks (macros : Std.HashMap String (Array Tok))
      (funcMacros : Std.HashMap String FuncMacro)
      (useLine : Nat) (toks : Array Tok) (seen : Std.HashSet String := {})
      (stampLine : Bool := false) : Except String (Array Tok) := do
    let mut out : Array Tok := #[]
    let mut i : Nat := 0
    while i < toks.size do
      let t := toks[i]!
      let line := if stampLine then useLine else t.line
      match t.kind with
      | .ident nm | .kw nm =>
        if !seen.contains nm then
          if let some fm := funcMacros.get? nm then
            if toks[i + 1]?.map (·.kind) == some (.sym "(") then
              let (args, nextIdx) ← parseArgsFromTokArray nm toks (i + 1)
              let exp ← expandFuncMacro macros funcMacros line nm fm args seen
              for rt in exp do out := out.push rt
              i := nextIdx
              continue
          if let some repl := macros.get? nm then
            let exp ← expandMacroToks macros funcMacros line repl (seen.insert nm) true
            for rt in exp do out := out.push rt
            i := i + 1
            continue
        out := out.push { t with line }
        i := i + 1
      | _ =>
        out := out.push { t with line }
        i := i + 1
    return out
end

private partial def evalPpTokens (macros : Std.HashMap String (Array Tok))
    (funcMacros : Std.HashMap String FuncMacro)
    (line : Nat) (toks : Array Tok) : Except String Int := do
  let kindAt (q : Nat) : Option TokKind := toks[q]?.map (·.kind)
  let ppPrec : String → Option (Nat × (Int → Int → Int))
    | "||" => some (1, fun a b => if a != 0 || b != 0 then 1 else 0)
    | "&&" => some (2, fun a b => if a != 0 && b != 0 then 1 else 0)
    | "==" => some (3, fun a b => if a == b then 1 else 0)
    | "!=" => some (3, fun a b => if a != b then 1 else 0)
    | "<"  => some (4, fun a b => if a < b then 1 else 0)
    | "<=" => some (4, fun a b => if a <= b then 1 else 0)
    | ">"  => some (4, fun a b => if a > b then 1 else 0)
    | ">=" => some (4, fun a b => if a >= b then 1 else 0)
    | "+"  => some (5, (· + ·))
    | "-"  => some (5, (· - ·))
    | "*"  => some (6, (· * ·))
    | _    => none
  let rec evalExpr (minP : Nat) (p : Nat) : Except String (Int × Nat) := do
    let (lhs, q0) : Int × Nat ← match kindAt p with
      | some (.sym "!") =>
        let (v, q) ← evalExpr 7 (p + 1)
        pure (if v == 0 then (1 : Int) else 0, q)
      | some (.sym "-") => let (v, q) ← evalExpr 7 (p + 1); pure (-v, q)
      | some (.sym "+") => evalExpr 7 (p + 1)
      | some (.ident "defined") =>
        let isDef (s : String) := macros.contains s || funcMacros.contains s
        if kindAt (p + 1) == some (.sym "(") then
          match kindAt (p + 2), kindAt (p + 3) with
          | some (.ident nm), some (.sym ")") =>
            pure (if isDef nm then (1 : Int) else 0, p + 4)
          | _, _ => throw s!"invalid defined(...) in #if at line {line}"
        else match kindAt (p + 1) with
          | some (.ident nm) => pure (if isDef nm then (1 : Int) else 0, p + 2)
          | _ => throw s!"invalid defined in #if at line {line}"
      | some (.intLit v _ _) => pure (v, p + 1)
      | some (.kw "true") => pure ((1 : Int), p + 1)
      | some (.kw "false") => pure ((0 : Int), p + 1)
      | some (.sym "(") =>
        let (v, q) ← evalExpr 1 (p + 1)
        if kindAt q != some (.sym ")") then throw s!"expected ')' in #if at line {line}"
        pure (v, q + 1)
      | some (.ident nm) | some (.kw nm) =>
        if let some fm := funcMacros.get? nm then
          if kindAt (p + 1) == some (.sym "(") then
            let (args, nextIdx) ← parseArgsFromTokArray nm toks (p + 1)
            let exp ← expandFuncMacro macros funcMacros line nm fm args {}
            let v ← evalPpTokens macros funcMacros line exp
            pure (v, nextIdx)
          else pure ((0 : Int), p + 1)
        else if let some repl := macros.get? nm then
          let exp ← expandMacroToks macros funcMacros line repl
            (Std.HashSet.emptyWithCapacity.insert nm) true
          pure (← evalPpTokens macros funcMacros line exp, p + 1)
        else pure ((0 : Int), p + 1)
      | _ => throw s!"unsupported '#if' expression at line {line}"
    let mut acc := lhs
    let mut pos := q0
    while true do
      let some (.sym s) := kindAt pos | break
      let some (prec, fn) := ppPrec s | break
      if prec < minP then break
      let (rhs, q1) ← evalExpr (prec + 1) (pos + 1)
      acc := fn acc rhs
      pos := q1
    pure (acc, pos)
  let (res, endPos) ← evalExpr 1 0
  if endPos != toks.size then throw s!"unexpected trailing token in '#if' expression at line {line}"
  pure res

private def skipWsAndComments (s : LexState) : Except String LexState := do
  let mut cur := s
  while cur.idx < cur.chars.size do
    let some c := cur.peek? | break
    if c.isWhitespace then cur := cur.advance
    else if c == '/' && cur.peek? 1 == some '/' then cur := skipLineComment cur
    else if c == '/' && cur.peek? 1 == some '*' then cur ← skipBlockComment cur
    else break
  pure cur

private def isNextNonWsParen (s : LexState) : Bool :=
  match skipWsAndComments s with
  | .ok cur => cur.peek? == some '('
  | .error _ => false

private partial def lexMacroArgs (startLine : Nat) (macroName : String) (st : LexState) :
    Except String (List (Array Tok) × LexState) := do
  let mut cur ← skipWsAndComments st
  if cur.peek? != some '(' then
    throw s!"expected '(' for macro '{macroName}' at line {startLine}"
  cur := cur.advance
  let mut parenDepth : Nat := 1
  let mut currentArg : Array Tok := #[]
  let mut args : List (Array Tok) := []
  let mut hasAnyToken := false
  while parenDepth > 0 do
    cur ← skipWsAndComments cur
    if cur.idx >= cur.chars.size then
      throw s!"unterminated invocation of macro '{macroName}' starting at line {startLine}"
    let some c := cur.peek? |
      throw s!"unterminated invocation of macro '{macroName}' starting at line {startLine}"
    if c == '(' then
      parenDepth := parenDepth + 1
      currentArg := currentArg.push { kind := .sym "(", line := cur.line }
      cur := cur.advance
      hasAnyToken := true
    else if c == ')' then
      parenDepth := parenDepth - 1
      cur := cur.advance
      if parenDepth == 0 then
        if hasAnyToken || !args.isEmpty then
          args := args ++ [currentArg]
        break
      else
        currentArg := currentArg.push { kind := .sym ")", line := cur.line }
        hasAnyToken := true
    else if c == ',' && parenDepth == 1 then
      cur := cur.advance
      args := args ++ [currentArg]
      currentArg := #[]
      hasAnyToken := false
    else
      let (tok?, cur') ← lexSingleToken cur
      cur := cur'
      match tok? with
      | some t =>
        currentArg := currentArg.push t
        hasAnyToken := true
      | none =>
        throw s!"unterminated invocation of macro '{macroName}' starting at line {startLine}"
  return (args, cur)

private def splitFirstWord (s : String) : String × String :=
  let cs := s.trimAscii.toString.toList
  let hd := cs.takeWhile isIdentCont
  let tl := (String.ofList (cs.drop hd.length)).trimAscii.toString
  (String.ofList hd, tl)

private def splitPragmaArgs (s : String) : List String :=
  let rec go (cs : List Char) (cur : List Char) (inQuotes : Bool) (acc : List String) :
      List String :=
    match cs with
    | [] =>
      let last := String.ofList cur.reverse |>.trimAscii.toString
      let acc := if last.isEmpty then acc else last :: acc
      acc.reverse
    | '"' :: rest =>
      if inQuotes then
        let item := String.ofList cur.reverse
        go rest [] false (item :: acc)
      else
        go rest [] true acc
    | c :: rest =>
      if inQuotes then
        go rest (c :: cur) true acc
      else if c.isWhitespace || c == ',' || c == '(' || c == ')' then
        let item := String.ofList cur.reverse |>.trimAscii.toString
        let acc := if item.isEmpty then acc else item :: acc
        go rest [] false acc
      else
        go rest (c :: cur) false acc
  go s.toList [] false []

private def parsePragmaDirective (rest : String) : Option C0Pragma :=
  let trimmed := rest.trimAscii.toString
  let (pname, argsStr) := splitFirstWord trimmed
  match pname with
  | "c0_upstream" =>
    let args := splitPragmaArgs argsStr
    match args with
    | [loc, fn] => some (.upstream loc (some fn))
    | [loc] => some (.upstream loc none)
    | _ => none
  | "c0_fidelity" => some .fidelity
  | "c0_extension" => some .extension
  | "c0_bounded" =>
    let args := splitPragmaArgs argsStr
    match args with
    | [reason] => some (.bounded reason)
    | _ =>
      let unq := argsStr.trimAscii.toString
      if !unq.isEmpty then some (.bounded unq) else none
  | _ => none

/-- Lookup a header by exact name, `.h`-stripped name, or `.h`-appended name. -/
public def lookupHeader (headers : Std.HashMap String String) (name : String) : Option String :=
  let base? :=
    if name.endsWith ".h" then
      let cs := name.toList
      headers.get? (String.ofList (cs.take (cs.length - 2)))
    else none
  headers.get? name <|> base? <|> headers.get? (name ++ ".h")

/-- Recursively expand registered `#include "name"` directives in C0 source.
System headers (`#include <...>`) and unknown `.h` headers (like `"c0.h"`) are preserved
for backwards compatibility. Throws on missing registered headers when `headers` is non-empty. -/
public partial def expandC0Includes (src : String) (headers : Std.HashMap String String)
    (depth : Nat := 0) : Except String String := do
  if depth > 100 then
    throw "maximum include depth exceeded in #include expansion"
  if headers.isEmpty then
    return src
  let mut st : LexState := { chars := src.toList.toArray }
  let mut out : List Char := []
  while st.idx < st.chars.size do
    let some c := st.peek? | break
    if c == '/' && st.peek? 1 == some '/' then
      while st.idx < st.chars.size do
        let some ch := st.peek? | break
        out := ch :: out
        st := st.advance
        if ch == '\n' then break
    else if c == '/' && st.peek? 1 == some '*' then
      out := '/' :: out
      out := '*' :: out
      st := st.advance 2
      let rec skipComment (s : LexState) (acc : List Char) :
          Except String (LexState × List Char) := do
        match s.peek?, s.peek? 1 with
        | none, _ => throw s!"unterminated block comment at line {s.line}"
        | some '*', some '/' => pure (s.advance 2, '/' :: '*' :: acc)
        | some ch, _ => skipComment s.advance (ch :: acc)
      let (st', acc') ← skipComment st out
      st := st'
      out := acc'
    else if c == '"' then
      out := '"' :: out
      st := st.advance
      let rec skipStr (s : LexState) (acc : List Char) :
          Except String (LexState × List Char) := do
        match s.peek? with
        | none => throw s!"unterminated string literal at line {s.line}"
        | some '"' => pure (s.advance, '"' :: acc)
        | some '\\' =>
          match s.peek? 1 with
          | none => throw s!"unterminated string escape at line {s.line}"
          | some esc => skipStr (s.advance 2) (esc :: '\\' :: acc)
        | some ch => skipStr s.advance (ch :: acc)
      let (st', acc') ← skipStr st out
      st := st'
      out := acc'
    else if c == '\'' then
      out := '\'' :: out
      st := st.advance
      let rec skipChar (s : LexState) (acc : List Char) :
          Except String (LexState × List Char) := do
        match s.peek? with
        | none => throw s!"unterminated char literal at line {s.line}"
        | some '\'' => pure (s.advance, '\'' :: acc)
        | some '\\' =>
          match s.peek? 1 with
          | none => throw s!"unterminated char escape at line {s.line}"
          | some esc => skipChar (s.advance 2) (esc :: '\\' :: acc)
        | some ch => skipChar s.advance (ch :: acc)
      let (st', acc') ← skipChar st out
      st := st'
      out := acc'
    else if c == '#' && st.atLineStart then
      let lineNo := st.line
      let (lineText, st') := readPreprocessorLine st.advance
      let (dir, rest) := splitFirstWord lineText
      if dir == "include" then
        let trimmed := rest.trimAscii.toString
        if trimmed.startsWith "<" then
          let rawLine := ("#" ++ lineText ++ "\n").toList
          out := rawLine.reverse ++ out
          st := st'
        else if trimmed.startsWith "\"" then
          let cs := trimmed.toList.drop 1
          let nameCs := cs.takeWhile (· != '"')
          let afterName := cs.drop nameCs.length
          if afterName.head? == some '"' then
            let hdrName := String.ofList nameCs
            if let some hdrContent := lookupHeader headers hdrName then
              let expHdr ← expandC0Includes hdrContent headers (depth + 1)
              let hdrChars := (expHdr ++ "\n").toList
              out := hdrChars.reverse ++ out
              st := st'
            else if hdrName == "c0.h" || hdrName.endsWith "/c0.h" || hdrName.endsWith ".h" then
              let rawLine := ("#" ++ lineText ++ "\n").toList
              out := rawLine.reverse ++ out
              st := st'
            else
              throw (s!"registered C0 header '{hdrName}' not found in environment " ++
                s!"at line {lineNo}")
          else
            throw s!"unterminated header name in #include at line {lineNo}"
        else
          throw s!"invalid #include directive at line {lineNo}"
      else
        let rawLine := ("#" ++ lineText ++ "\n").toList
        out := rawLine.reverse ++ out
        st := st'
    else
      out := c :: out
      st := st.advance
  return String.ofList out.reverse

partial def tokenize (src : String) (headers : Std.HashMap String String := {}) :
    Except String (Array Tok) := do
  let mut st : LexState := { chars := src.toList.toArray }
  let mut includeStack : List LexState := []
  let mut toks : Array Tok := #[]
  let mut macros : Std.HashMap String (Array Tok) := {}
  let mut funcMacros : Std.HashMap String FuncMacro := {}
  let mut ifStack : List (Bool × Bool × Bool) := [] -- (parentActive, curActive, anyTaken)
  let isActive := fun (stk : List (Bool × Bool × Bool)) =>
    stk.head?.map (fun (_, cur, _) => cur) |>.getD true
  while st.idx < st.chars.size || !includeStack.isEmpty do
    if st.idx >= st.chars.size then
      match includeStack with
      | parentSt :: restStk =>
        st := parentSt
        includeStack := restStk
        continue
      | [] => break
    let some c := st.peek? | continue
    if c.isWhitespace then st := st.advance
    else if c == '/' && st.peek? 1 == some '/' then st := skipLineComment st
    else if c == '/' && st.peek? 1 == some '*' then st ← skipBlockComment st
    else if c == '#' && st.atLineStart then
      let lineNo := st.line
      let (lineText, st') := readPreprocessorLine st.advance
      st := st'
      let (dir, rest) := splitFirstWord lineText
      let active := isActive ifStack
      match dir with
      | "ifdef" | "ifndef" =>
        if !active then ifStack := (false, false, true) :: ifStack
        else
          let (nm, _) := splitFirstWord rest
          let defined := macros.contains nm || funcMacros.contains nm
          let b := if dir == "ifdef" then defined else !defined
          ifStack := (true, b, b) :: ifStack
      | "if" =>
        if !active then ifStack := (false, false, true) :: ifStack
        else
          let ctoks ← tokenizeLineStr lineNo rest
          let v ← evalPpTokens macros funcMacros lineNo ctoks
          let b := v != 0
          ifStack := (true, b, b) :: ifStack
      | "elif" =>
        match ifStack with
        | [] => throw s!"unexpected '#elif' without '#if' at line {lineNo}"
        | (parentAct, _, anyTaken) :: tl =>
          if !parentAct || anyTaken then
            ifStack := (parentAct, false, anyTaken) :: tl
          else
            let ctoks ← tokenizeLineStr lineNo rest
            let v ← evalPpTokens macros funcMacros lineNo ctoks
            let b := v != 0
            ifStack := (true, b, b) :: tl
      | "else" =>
        match ifStack with
        | [] => throw s!"unexpected '#else' without '#if' at line {lineNo}"
        | (parentAct, _, anyTaken) :: tl =>
          ifStack := (parentAct, parentAct && !anyTaken, true) :: tl
      | "endif" =>
        match ifStack with
        | [] => throw s!"unexpected '#endif' without '#if' at line {lineNo}"
        | _ :: tl => ifStack := tl
      | "pragma" =>
        if active then
          if let some p := parsePragmaDirective rest then
            toks := toks.push { kind := .pragma p, line := lineNo }
      | "include" =>
        if active then
          let trimmed := rest.trimAscii.toString
          if trimmed.startsWith "<" then
            if trimmed.contains '>' then pure ()
            else throw s!"unterminated system header in '#include' at line {lineNo}"
          else if trimmed.startsWith "\"" then
            let cs := trimmed.toList.drop 1
            let nameCs := cs.takeWhile (· != '"')
            let afterName := cs.drop nameCs.length
            if afterName.head? == some '"' then
              let hdrName := String.ofList nameCs
              if let some hdrContent := lookupHeader headers hdrName then
                if includeStack.length >= 100 then
                  throw (s!"maximum include depth exceeded at line {lineNo} " ++
                    s!"(including \"{hdrName}\")")
                includeStack := st :: includeStack
                st := {
                  chars := hdrContent.toList.toArray, idx := 0, line := 1, atLineStart := true
                }
              else if hdrName == "c0.h" || hdrName.endsWith "/c0.h" ||
                  hdrName.endsWith ".h" || headers.isEmpty then
                pure ()
              else
                throw (s!"registered C0 header '{hdrName}' not found in environment " ++
                  s!"at line {lineNo}")
            else
              throw (s!"unterminated header name in '#include' at line {lineNo}")
          else
            throw (s!"invalid '#include' directive at line {lineNo}: expected <...> or \"...\"")
      | "undef" =>
        if active then
          let (nm, _) := splitFirstWord rest
          macros := macros.erase nm
          funcMacros := funcMacros.erase nm
      | "define" =>
        if active then
          let cs := rest.toList
          let nameCs := cs.takeWhile isIdentCont
          if nameCs.isEmpty || !isIdentStart nameCs.head! then
            throw s!"invalid '#define' at line {lineNo}"
          let nm := String.ofList nameCs
          let afterNm := cs.drop nameCs.length
          if afterNm.head? == some '(' then
            let afterParen := afterNm.tail
            let paramCs := afterParen.takeWhile (· != ')')
            if paramCs.length == afterParen.length then
              throw s!"unterminated macro parameter list in '#define {nm}' at line {lineNo}"
            let restCs := afterParen.drop (paramCs.length + 1)
            let paramStr := (String.ofList paramCs).trimAscii.toString
            let bodyStr := (String.ofList restCs).trimAscii.toString
            let mut params : List String := []
            let mut isVariadic := false
            if !paramStr.isEmpty then
              let rawParams := paramStr.splitOn "," |>.map (·.trimAscii.toString)
              for i in [:rawParams.length] do
                let p := rawParams[i]!
                if p == "..." then
                  if i + 1 != rawParams.length then
                    throw s!"'...' must be the last parameter in '#define {nm}' at line {lineNo}"
                  isVariadic := true
                  params := params ++ ["__VA_ARGS__"]
                else if !isValidParamName p then
                  throw s!"invalid macro parameter '{p}' in '#define {nm}' at line {lineNo}"
                else if params.contains p then
                  throw s!"duplicate macro parameter '{p}' in '#define {nm}' at line {lineNo}"
                else
                  params := params ++ [p]
            let bodyToks ← tokenizeLineStr lineNo bodyStr
            funcMacros := funcMacros.insert nm { params, isVariadic, body := bodyToks }
            macros := macros.erase nm
          else
            let bodyStr := (String.ofList afterNm).trimAscii.toString
            let bodyToks ← tokenizeLineStr lineNo bodyStr
            macros := macros.insert nm bodyToks
            funcMacros := funcMacros.erase nm
      | _ =>
        if active then throw s!"unsupported preprocessor directive '#{dir}' at line {lineNo}"
    else if !isActive ifStack then
      st := st.advance
    else
      let (tok?, st') ← lexSingleToken st
      st := st'
      if let some tok := tok? then
        match tok.kind with
        | .ident nm | .kw nm =>
          if let some fm := funcMacros.get? nm then
            if isNextNonWsParen st then
              let (args, st'') ← lexMacroArgs tok.line nm st
              st := st''
              let exp ← expandFuncMacro macros funcMacros tok.line nm fm args {}
              for rt in exp do toks := toks.push rt
            else
              toks := toks.push tok
          else if let some repl := macros.get? nm then
            let exp ← expandMacroToks macros funcMacros tok.line repl
              (Std.HashSet.emptyWithCapacity.insert nm) true
            for rt in exp do toks := toks.push rt
          else
            toks := toks.push tok
        | _ => toks := toks.push tok
  unless ifStack.isEmpty do
    throw s!"unterminated '#if'/'#ifdef' directive at end of file"
  toks := toks.push { kind := .eof, line := st.line }
  return toks

end LeanQbe.T.Frontend.C0
