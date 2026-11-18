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
  | intLit (val : Int) (suffix : IntSuffix) (isDecimal : Bool := true)
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
        throw s!"unsupported float literal suffix '{sc}' at line {line}; C0 supports double (f64) literals only"
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
        | some h => if isHexDigit h then v := v * 16 + hexVal h; stx := stx.advance; cnt := cnt + 1 else break
        | none => break
      if cnt == 0 then throw s!"invalid hex escape at line {line}"
      finish v stx
    else if (cur1.peek?.map isOctDigit).getD false then
      let mut sto := cur1; let mut v : Nat := 0; let mut cnt := 0
      while cnt < 3 do
        match sto.peek? with
        | some d => if isOctDigit d then v := v * 8 + (d.toNat - '0'.toNat); sto := sto.advance; cnt := cnt + 1 else break
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
  ['+', '-', '*', '/', '%', '&', '|', '^', '~', '!', '<', '>', '=', '.', '?', ':', ';', ',', '(', ')', '{', '}', '[', ']']

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

private partial def expandMacroToks (macros : Std.HashMap String (Array Tok))
    (useLine : Nat) (toks : Array Tok) (seen : Std.HashSet String := {}) : Array Tok :=
  Id.run do
    let mut out : Array Tok := #[]
    for t in toks do
      match t.kind with
      | .ident nm | .kw nm =>
        if !seen.contains nm then
          if let some repl := macros.get? nm then
            let exp := expandMacroToks macros useLine repl (seen.insert nm)
            for rt in exp do
              out := out.push { rt with line := useLine }
            continue
        out := out.push { t with line := useLine }
      | _ => out := out.push { t with line := useLine }
    return out

private partial def evalPpTokens (macros : Std.HashMap String (Array Tok))
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
      | some (.sym "!") => let (v, q) ← evalExpr 7 (p + 1); pure (if v == 0 then (1 : Int) else 0, q)
      | some (.sym "-") => let (v, q) ← evalExpr 7 (p + 1); pure (-v, q)
      | some (.sym "+") => evalExpr 7 (p + 1)
      | some (.ident "defined") =>
        if kindAt (p + 1) == some (.sym "(") then
          match kindAt (p + 2), kindAt (p + 3) with
          | some (.ident nm), some (.sym ")") => pure (if macros.contains nm then (1 : Int) else 0, p + 4)
          | _, _ => throw s!"invalid defined(...) in #if at line {line}"
        else match kindAt (p + 1) with
          | some (.ident nm) => pure (if macros.contains nm then (1 : Int) else 0, p + 2)
          | _ => throw s!"invalid defined in #if at line {line}"
      | some (.intLit v _ _) => pure (v, p + 1)
      | some (.kw "true") => pure ((1 : Int), p + 1)
      | some (.kw "false") => pure ((0 : Int), p + 1)
      | some (.sym "(") =>
        let (v, q) ← evalExpr 1 (p + 1)
        if kindAt q != some (.sym ")") then throw s!"expected ')' in #if at line {line}"
        pure (v, q + 1)
      | some (.ident nm) | some (.kw nm) =>
        if let some repl := macros.get? nm then
          let exp := expandMacroToks macros line repl (Std.HashSet.emptyWithCapacity.insert nm)
          pure (← evalPpTokens macros line exp, p + 1)
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

private def splitFirstWord (s : String) : String × String :=
  let cs := s.trimAscii.toString.toList
  let hd := cs.takeWhile isIdentCont
  let tl := (String.ofList (cs.drop hd.length)).trimAscii.toString
  (String.ofList hd, tl)

private partial def tokenize (src : String) : Except String (Array Tok) := do
  let mut st : LexState := { chars := src.toList.toArray }
  let mut toks : Array Tok := #[]
  let mut macros : Std.HashMap String (Array Tok) := {}
  let mut funcMacros : Std.HashSet String := {}
  let mut ifStack : List (Bool × Bool × Bool) := [] -- (parentActive, curActive, anyTaken)
  let isActive := fun (stk : List (Bool × Bool × Bool)) =>
    stk.head?.map (fun (_, cur, _) => cur) |>.getD true
  while st.idx < st.chars.size do
    let some c := st.peek? | break
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
          let v ← evalPpTokens macros lineNo ctoks
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
            let v ← evalPpTokens macros lineNo ctoks
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
      | "include" | "pragma" => pure ()
      | "undef" =>
        if active then
          let (nm, _) := splitFirstWord rest
          macros := macros.erase nm
          funcMacros := funcMacros.erase nm
      | "define" =>
        if active then
          let cs := rest.toList
          let nameCs := cs.takeWhile isIdentCont
          if nameCs.isEmpty then throw s!"invalid '#define' at line {lineNo}"
          let nm := String.ofList nameCs
          let afterNm := cs.drop nameCs.length
          if afterNm.head? == some '(' then
            funcMacros := funcMacros.insert nm
          else
            let bodyStr := (String.ofList afterNm).trimAscii.toString
            let bodyToks ← tokenizeLineStr lineNo bodyStr
            macros := macros.insert nm (expandMacroToks macros lineNo bodyToks {})
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
          if funcMacros.contains nm then
            throw s!"function-like macro '{nm}' is not supported at line {tok.line}"
          if let some repl := macros.get? nm then
            let exp := expandMacroToks macros tok.line repl (Std.HashSet.emptyWithCapacity.insert nm)
            for rt in exp do toks := toks.push rt
          else
            toks := toks.push tok
        | _ => toks := toks.push tok
  unless ifStack.isEmpty do
    throw s!"unterminated '#if'/'#ifdef' directive at end of file"
  toks := toks.push { kind := .eof, line := st.line }
  return toks

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
          | .intLit w _ _ =>
            if w < 0 then throw s!"C0 parse error (line {wTok.line}): negative bitfield width"
            bw := some w.toNat
          | _ => throw s!"C0 parse error (line {wTok.line}): expected bitfield width"
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
    let lv ← MonadExcept.ofExcept (exprToLVal e)
    pure (.incDec lv isInc)
  else
    let e ← parseUnary
    if ← matchSym "++" then
      pure (.incDec (← MonadExcept.ofExcept (exprToLVal e)) true)
    else if ← matchSym "--" then
      pure (.incDec (← MonadExcept.ofExcept (exprToLVal e)) false)
    else if let some binOp? ← parseAssignOp? then
      let lv ← MonadExcept.ofExcept (exprToLVal e)
      pure (.assign lv binOp? (← parseExpr))
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
      let mut arms : List SwitchArm := []
      while !(← matchSym "}") do
        let mut vals : List Int := []
        let mut hasDef := false
        let mut anyLbl := false
        while true do
          if ← matchKw "case" then
            anyLbl := true
            let csts := (← get).consts
            let v ← evalConstIntExpr csts (← parseExpr) |> MonadExcept.ofExcept
            expectSym ":"
            vals := vals ++ [v]
          else if ← matchKw "default" then
            anyLbl := true
            expectSym ":"
            hasDef := true
          else break
        unless anyLbl do
          failAt "expected 'case' or 'default' in switch"
        let mut body : List Stmt := []
        while (← peekTok).kind != .sym "}" && (← peekTok).kind != .kw "case" && (← peekTok).kind != .kw "default" do
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
          nextVal ← MonadExcept.ofExcept (evalConstIntExpr csts e)
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
