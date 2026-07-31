/-
Kraken ParserAArch64 - AArch64 Assembly Parser

Parses AArch64 syntax assembly strings into Kraken's Program type.
Uses Lean's built-in Std.Internal.Parsec library.
-/

import Kraken.AArch64.Syntax
import Std.Internal.Parsec.String

namespace Kraken.AArch64.Parser

open Std.Internal.Parsec
open Std.Internal.Parsec.String

-- ============================================================================
-- Lexical Utilities
-- ============================================================================

/-- Skip zero or more horizontal whitespace characters (space, tab). -/
def skipHWs : Parser Unit := do
  let _ ← many (pchar ' ' <|> pchar '\t')

/-- Skip a line comment starting with # or //. -/
def skipLineComment : Parser Unit := do
  let _ ← pchar '#' <|> (pstring "//" *> pure '/')
  let _ ← many (satisfy fun c => c != '\n')
  pure ()

/-- Parse a single decimal digit. -/
def digit : Parser Char := satisfy fun c => c >= '0' && c <= '9'

/-- Parse a single hex digit. -/
def hexDigit : Parser Char := satisfy fun c =>
  (c >= '0' && c <= '9') || (c >= 'a' && c <= 'f') || (c >= 'A' && c <= 'F')

def hexVal (c : Char) : Int :=
  if c >= '0' && c <= '9' then c.toNat - '0'.toNat
  else if c >= 'a' && c <= 'f' then c.toNat - 'a'.toNat + 10
  else c.toNat - 'A'.toNat + 10

def parseHex : Parser Int := do
  let _ ← pstring "0x" <|> pstring "0X"
  let digits ← many1 hexDigit
  pure (digits.foldl (fun acc d => acc * 16 + hexVal d) 0)

/-- Parse a single binary digit (0 or 1). -/
def binDigit : Parser Char := satisfy fun c => c == '0' || c == '1'

def parseBin : Parser Int := do
  let _ ← pstring "0b" <|> pstring "0B"
  let digits ← many1 binDigit
  pure (digits.foldl (fun acc d => acc * 2 + (d.toNat - '0'.toNat)) 0)

def parseDec : Parser Int := do
  let digits ← many1 digit
  pure (digits.foldl (fun acc d => acc * 10 + (d.toNat - '0'.toNat)) 0)

def parseNumber : Parser Int := attempt parseHex <|> attempt parseBin <|> parseDec

/-- Parse a signed integer (hex, binary, or decimal), allowing flexible sign/prefix ordering (`#-16`, `-#16`, or `#16`). -/
def parseInt : Parser Int := do
  skipHWs
  let _ ← optional (pchar '#')
  skipHWs
  let neg ← (pchar '-' *> pure true) <|> (pchar '+' *> pure false) <|> pure false
  skipHWs
  let _ ← optional (pchar '#')
  skipHWs
  let val ← parseNumber
  pure (if neg then -val else val)

/-- Parse a name (identifier or label). -/
def parseName : Parser String := do
  let first ← satisfy fun c => c.isAlpha || c == '_' || c == '.'
  let rest ← many (satisfy fun c => c.isAlphanum || c == '_' || c == '.')
  pure (String.ofList (#[first] ++ rest).toList)

/-- Parse an immediate operand as Int64. -/
def parseInt64 : Parser Int64 := do
  let v ← parseInt
  if v < -9223372036854775808 || v >= 18446744073709551616 then
    fail s!"immediate {v} out of 64-bit range"
  let i64 := if v > 9223372036854775807 then
    Int64.ofInt (v - 18446744073709551616)
  else
    Int64.ofInt v
  pure i64

def parseLabelRaw : Parser Label := parseName

/-- Parses a constant expression, including numeric immediates (`#16`), labels (`main`), and relocation modifiers (`:pg_hi21:main`, `:lo12:main`). -/
partial def parseConstExpr : Parser ConstExpr := do
  skipHWs
  let _ ← optional (pchar '#')
  skipHWs
  let c ← peek!
  if c == ':' then do
    let mod ← (pstring ":pg_hi21:" *> pure ConstExpr.pg_hi21) <|> (pstring ":lo12:" *> pure ConstExpr.lo12)
    let inner ← parseConstExpr
    pure (mod inner)
  else if c == '-' || c == '+' || c.isDigit then do
    let i ← parseInt64
    pure (.int64 i)
  else do
    let l ← parseLabelRaw
    pure (.label l)

-- ============================================================================
-- Register Parsing
-- ============================================================================

def parseXRegName (name : String) : Option (Width × XReg) :=
  match name.toLower with
  | "x0" => some (.W64, .X0) | "x1" => some (.W64, .X1) | "x2" => some (.W64, .X2) | "x3" => some (.W64, .X3)
  | "x4" => some (.W64, .X4) | "x5" => some (.W64, .X5) | "x6" => some (.W64, .X6) | "x7" => some (.W64, .X7)
  | "x8" => some (.W64, .X8) | "x9" => some (.W64, .X9) | "x10" => some (.W64, .X10) | "x11" => some (.W64, .X11)
  | "x12" => some (.W64, .X12) | "x13" => some (.W64, .X13) | "x14" => some (.W64, .X14) | "x15" => some (.W64, .X15)
  | "x16" => some (.W64, .X16) | "x17" => some (.W64, .X17) | "x18" => some (.W64, .X18) | "x19" => some (.W64, .X19)
  | "x20" => some (.W64, .X20) | "x21" => some (.W64, .X21) | "x22" => some (.W64, .X22) | "x23" => some (.W64, .X23)
  | "x24" => some (.W64, .X24) | "x25" => some (.W64, .X25) | "x26" => some (.W64, .X26) | "x27" => some (.W64, .X27)
  | "x28" => some (.W64, .X28) | "x29" | "fp" => some (.W64, .X29) | "x30" | "lr" => some (.W64, .X30)
  | "w0" => some (.W32, .X0) | "w1" => some (.W32, .X1) | "w2" => some (.W32, .X2) | "w3" => some (.W32, .X3)
  | "w4" => some (.W32, .X4) | "w5" => some (.W32, .X5) | "w6" => some (.W32, .X6) | "w7" => some (.W32, .X7)
  | "w8" => some (.W32, .X8) | "w9" => some (.W32, .X9) | "w10" => some (.W32, .X10) | "w11" => some (.W32, .X11)
  | "w12" => some (.W32, .X12) | "w13" => some (.W32, .X13) | "w14" => some (.W32, .X14) | "w15" => some (.W32, .X15)
  | "w16" => some (.W32, .X16) | "w17" => some (.W32, .X17) | "w18" => some (.W32, .X18) | "w19" => some (.W32, .X19)
  | "w20" => some (.W32, .X20) | "w21" => some (.W32, .X21) | "w22" => some (.W32, .X22) | "w23" => some (.W32, .X23)
  | "w24" => some (.W32, .X24) | "w25" => some (.W32, .X25) | "w26" => some (.W32, .X26) | "w27" => some (.W32, .X27)
  | "w28" => some (.W32, .X28) | "w29" | "wfp" => some (.W32, .X29) | "w30" | "wlr" => some (.W32, .X30)
  | _ => none

def checkWidth {T : Width → Type} (expected actual : Width) (val : T actual) : Parser (T expected) :=
  if h : expected = actual then
    pure (h ▸ val)
  else
    fail s!"expected {expected} register, got {actual}"

def parseRegOrSpW : Parser RegOrSpW := do
  skipHWs
  let name ← parseName
  match parseXRegName name with
  | some (w, r) => pure ⟨w, r⟩
  | none =>
    match name.toLower with
    | "sp" => pure ⟨.W64, RegOrSp.SP⟩
    | "wsp" => pure ⟨.W32, RegOrSp.WSP⟩
    | _ => fail s!"unknown register or sp: {name}"

def parseRegOrZrW : Parser RegOrZrW := do
  skipHWs
  let name ← parseName
  match parseXRegName name with
  | some (w, r) => pure ⟨w, r⟩
  | none =>
    match name.toLower with
    | "xzr" => pure ⟨.W64, RegOrZr.XZR⟩
    | "wzr" => pure ⟨.W32, RegOrZr.WZR⟩
    | _ => fail s!"unknown register or xzr: {name}"

def parseRegOrSp (w : Width) : Parser (RegOrSp w) := do
  let ⟨w', r⟩ ← parseRegOrSpW
  checkWidth w w' r

def parseRegOrZr (w : Width) : Parser (RegOrZr w) := do
  let ⟨w', r⟩ ← parseRegOrZrW
  checkWidth w w' r

inductive AnyReg (w : Width)
  | gpr (r : XReg) : AnyReg w
  | sp : AnyReg w
  | xzr : AnyReg w

abbrev AnyRegW := (w : Width) × AnyReg w

def parseAnyRegW : Parser AnyRegW := do
  skipHWs
  let name ← parseName
  match parseXRegName name with
  | some (w, r) => pure ⟨w, .gpr r⟩
  | none =>
    match name.toLower with
    | "sp" => pure ⟨.W64, .sp⟩
    | "wsp" => pure ⟨.W32, .sp⟩
    | "xzr" => pure ⟨.W64, .xzr⟩
    | "wzr" => pure ⟨.W32, .xzr⟩
    | _ => fail s!"unknown register, sp, or xzr: {name}"

def parseAnyReg (w : Width) : Parser (AnyReg w) := do
  let ⟨w', r⟩ ← parseAnyRegW
  checkWidth w w' r

def AnyReg.toRegOrSp {w : Width} : AnyReg w → Parser (RegOrSp w)
  | .gpr r => pure (.low (.reg r) w)
  | .sp => match w with
    | .W64 => pure RegOrSp.SP
    | .W32 => pure RegOrSp.WSP
  | .xzr => fail "xzr/wzr not allowed in immediate/extended register instruction (sp expected)"

def AnyReg.toRegOrZr {w : Width} : AnyReg w → Parser (RegOrZr w)
  | .gpr r => pure (.low (.reg r) w)
  | .xzr => match w with
    | .W64 => pure RegOrZr.XZR
    | .W32 => pure RegOrZr.WZR
  | .sp => fail "sp/wsp not allowed in shifted register instruction (xzr expected)"

def AnyReg.isSp {w : Width} : AnyReg w → Bool
  | .sp => true
  | _ => false

def AnyReg.isXzr {w : Width} : AnyReg w → Bool
  | .xzr => true
  | _ => false

-- ============================================================================
-- Operand Parsing
-- ============================================================================

def parseComma : Parser Unit := do
  skipHWs
  let _ ← pchar ','
  skipHWs

def liftExcept {α : Type} (res : Except String α) : Parser α :=
  match res with
  | .ok a => pure a
  | .error msg => fail msg

def getMemExtendAmount (w : Width) (amt : Nat) : Except String (MemExtendAmount w) :=
  match w, amt with
  | .W32, 0 => .ok .E0
  | .W32, 2 => .ok .E2
  | .W64, 0 => .ok .E0
  | .W64, 3 => .ok .E3
  | _, _ => .error s!"invalid memory extension shift amount {amt} for width {w}"

def getMemExtendType (extName : String) (w : Width) : Except String MemExtendType :=
  match extName.toLower with
  | "uxtw" => .ok MemExtendType.UXTW
  | "sxtw" => .ok MemExtendType.SXTW
  | "uxtx" => .ok MemExtendType.UXTX
  | "sxtx" => .ok MemExtendType.SXTX
  | "lsl" =>
    match w with
    | .W64 => .ok MemExtendType.UXTX
    | .W32 => .ok MemExtendType.UXTW
  | _ => .error s!"unknown memory extension type: {extName}"

def checkUnsignedOffset (w : Width) (imm : Int64) : Except String Unit :=
  let (maxOff, align) := match w with | .W32 => (16380, 4) | .W64 => (32760, 8)
  if imm.toInt < 0 || imm.toInt > maxOff || imm.toInt % align != 0 then
    .error s!"unsigned offset {imm.toInt} out of range [0, {maxOff}] or not a multiple of {align}"
  else .ok ()

def checkShiftAmount (w : Width) (amt : Int64) : Except String Unit :=
  let maxAmt := match w with | .W32 => 31 | .W64 => 63
  if amt.toInt < 0 || amt.toInt > maxAmt then
    .error s!"shift amount {amt.toInt} out of range [0, {maxAmt}] for {w.bits}-bit instruction"
  else .ok ()

def checkPairOffset (w : Width) (imm : Int64) : Except String Unit :=
  let (minOff, maxOff, align) := match w with | .W32 => (-256, 252, 4) | .W64 => (-512, 504, 8)
  if imm.toInt < minOff || imm.toInt > maxOff || imm.toInt % align != 0 then
    .error s!"pair offset {imm.toInt} out of range [{minOff}, {maxOff}] or not a multiple of {align}"
  else .ok ()

def intToHexStr (n : Int) : String :=
  if n < 0 then s!"-0x{String.ofList (Nat.toDigits 16 (-n).natAbs)}"
  else s!"0x{String.ofList (Nat.toDigits 16 n.natAbs)}"

def checkAdrOffset (offset : Int64) : Except String Unit :=
  let val := offset.toInt
  if val < -0x100000 || val > 0xfffff then
    .error s!"adr offset {intToHexStr val} out of range [-0x100000, 0xfffff]"
  else .ok ()

def checkAdrpOffset (offset : Int64) : Except String Unit :=
  let val := offset.toInt
  if val % 0x1000 != 0 then
    .error s!"adrp offset {intToHexStr val} not page aligned (must be multiple of 0x1000)"
  else
    let page_offset := val / 0x1000
    if page_offset < -0x100000 || page_offset > 0xfffff then
      .error s!"adrp offset {intToHexStr val} out of range [-0x100000000, 0xfffff000]"
    else .ok ()

def checkBOffset (offset : Int64) : Except String Unit :=
  let val := offset.toInt
  if val < -0x8000000 || val > 0x7fffffc then
    .error s!"b offset {intToHexStr val} out of range [-0x8000000, 0x7fffffc]"
  else .ok ()

def checkBCondOffset (offset : Int64) : Except String Unit :=
  let val := offset.toInt
  if val < -0x100000 || val > 0xffffc then
    .error s!"b.cond offset {intToHexStr val} out of range [-0x100000, 0xffffc]"
  else .ok ()

def checkCbzOffset (instrName : String) (offset : Int64) : Except String Unit :=
  let val := offset.toInt
  if val < -0x100000 || val > 0xffffc || val % 4 != 0 then
    .error s!"{instrName} offset {intToHexStr val} out of range [-0x100000, 0xffffc] or not a multiple of 4"
  else .ok ()

def checkTbzOffset (instrName : String) (offset : Int64) : Except String Unit :=
  let val := offset.toInt
  if val < -0x8000 || val > 0x7fc || val % 4 != 0 then
    .error s!"{instrName} offset {intToHexStr val} out of range [-0x8000, 0x7fc] or not a multiple of 4"
  else .ok ()

def checkTbzBitPosition (instrName : String) (w : Width) (bit : Int) : Except String Unit :=
  let maxBit := match w with | .W32 => 31 | .W64 => 63
  if bit < 0 || bit > maxBit then
    .error s!"{instrName} bit position {bit} out of range [0, {maxBit}] for {w.bits}-bit instruction"
  else .ok ()

/-- Parses memory addressing operands for general load/store instructions (`LDR`/`STR`).
    Supports the following AArch64 addressing modes:
    1. **Base-only / Post-indexed**: `[base]` or `[base], #imm`
    2. **Immediate / Pre-indexed**: `[base, #imm]` or `[base, #imm]!` or `[base, #:lo12:label]`
    3. **Register offset with optional extension/shift**: `[base, Rm]` or `[base, Rm, ext #amount]` -/
def parseAddr (w : Width) : Parser (AddrExpr w) := do
  skipHWs
  let _ ← pchar '['
  let base ← parseRegOrSp .W64
  skipHWs
  let c ← peek!
  -- Mode 1: Base register closed immediately -> either base-only `[base]` or post-indexed `[base], #imm`
  if c == ']' then do
    skip
    skipHWs
    let nextC? ← peek?
    if nextC? == some ',' then do
      skip
      skipHWs
      let imm ← parseInt64
      if imm.toInt < -256 || imm.toInt > 255 then
        fail s!"post-indexed offset {imm.toInt} out of range [-256, 255]"
      pure ⟨base, .imm { imm := imm, index := some .Post }⟩
    else
      pure ⟨base, .imm { imm := 0, index := none }⟩
  -- Mode 2 & 3: Comma after base -> either immediate/modifier offset or register offset
  else if c == ',' then do
    skip
    skipHWs
    let nextC ← peek!
    -- Mode 2: Immediate / Relocation modifier / Pre-indexed offset (`#imm`, `:lo12:label`, etc.)
    if nextC == '#' || nextC == '-' || nextC.isDigit || nextC == ':' then do
      let expr ← parseConstExpr
      skipHWs
      let _ ← pchar ']'
      skipHWs
      let isPre ← (pchar '!' *> pure (some Index.Pre)) <|> pure none
      match expr with
      | .int64 imm =>
        if isPre == some .Pre then do
          if imm.toInt < -256 || imm.toInt > 255 then
            fail s!"pre-indexed offset {imm.toInt} out of range [-256, 255]"
        else do
          liftExcept (checkUnsignedOffset w imm)
      | _ =>
        if isPre.isSome then
          fail "pre-indexed / post-indexed offsets must be constant numeric immediates"
      pure ⟨base, .imm { imm := expr, index := isPre }⟩
    -- Mode 3: Register offset with optional extension and shift (`Rm` or `Rm, ext #amount`)
    else do
      let regW ← parseRegOrZrW
      skipHWs
      let nextC2 ← peek!
      if nextC2 == ',' then do
        skip
        skipHWs
        let extName ← parseName
        let extType ← liftExcept (getMemExtendType extName regW.w)
        skipHWs
        let _ ← optional (pchar ',')
        skipHWs
        let c? ← peek?
        let amt ← if c? == some '#' || c? == some '-' || (c?.map Char.isDigit).getD false then do
          let val ← parseInt
          pure val.toNat
        else
          pure 0
        let amount ← liftExcept (getMemExtendAmount w amt)
        skipHWs
        let _ ← pchar ']'
        pure ⟨base, .reg { reg := regW, ext := { type := extType, amount := amount } }⟩
      else if nextC2 == ']' then do
        skip
        let extType := match regW.w with
          | .W64 => MemExtendType.UXTX
          | .W32 => MemExtendType.UXTW
        pure ⟨base, .reg { reg := regW, ext := { type := extType, amount := MemExtendAmount.E0 } }⟩
      else
        fail s!"expected ',' or ']' after index register in memory operand, got {nextC2}"
  else
    fail s!"expected ',' or ']' after base register in memory operand, got {c}"

def parseAddrOrLit (w : Width) : Parser (AddrOrLit w) := do
  skipHWs
  let c ← peek!
  if c == '[' then do
    let m ← parseAddr w
    pure (.addr m)
  else if c == '=' then do
    skip
    let e ← parseConstExpr
    pure (.lit (.pool { expr := e }))
  else do
    let l ← parseLabelRaw
    pure (.lit (.addr { label := l }))

def parsePairAddr (w : Width) : Parser (AddrExpr w) := do
  skipHWs
  let _ ← pchar '['
  let base ← parseRegOrSp .W64
  skipHWs
  let c ← peek!
  if c == ']' then do
    skip
    skipHWs
    let nextC? ← peek?
    if nextC? == some ',' then do
      skip
      skipHWs
      let imm ← parseInt64
      liftExcept (checkPairOffset w imm)
      pure ⟨base, .imm { imm := imm, index := some .Post }⟩
    else
      pure ⟨base, .imm { imm := 0, index := none }⟩
  else if c == ',' then do
    skip
    skipHWs
    let nextC ← peek!
    if nextC == '#' || nextC == '-' || nextC.isDigit then do
      let imm ← parseInt64
      skipHWs
      let _ ← pchar ']'
      skipHWs
      let isPre ← (pchar '!' *> pure (some Index.Pre)) <|> pure none
      liftExcept (checkPairOffset w imm)
      pure ⟨base, .imm { imm := imm, index := isPre }⟩
    else
      fail s!"register offsets are not supported for ldp/stp instructions"
  else
    fail s!"expected ',' or ']' after base register in pair memory operand, got {c}"

def parseExtendAmount : Parser ExtendAmount := do
  skipHWs
  (do
    let _ ← optional (pchar ',')
    skipHWs
    let _ ← optional (pchar '#')
    let val ← parseNumber
    match val with
    | 0 => pure ExtendAmount.E0
    | 1 => pure ExtendAmount.E1
    | 2 => pure ExtendAmount.E2
    | 3 => pure ExtendAmount.E3
    | 4 => pure ExtendAmount.E4
    | _ => fail s!"invalid extend amount: {val}"
  ) <|> pure ExtendAmount.E0

def getExtendType (extName : String) (w : Width) : Except String ExtendType :=
  match extName.toLower with
  | "uxtb" => .ok ExtendType.UXTB
  | "sxtb" => .ok ExtendType.SXTB
  | "uxth" => .ok ExtendType.UXTH
  | "sxth" => .ok ExtendType.SXTH
  | "uxtw" => .ok ExtendType.UXTW
  | "sxtw" => .ok ExtendType.SXTW
  | "uxtx" => .ok ExtendType.UXTX
  | "sxtx" => .ok ExtendType.SXTX
  | "lsl" =>
    match w with
    | .W64 => .ok ExtendType.UXTX
    | .W32 => .ok ExtendType.UXTW
  | _ => .error s!"unknown extension type: {extName}"

/-- Parses the second source operand of an `ADD_e` instruction (`add dst, src1, src2`).
    `src2` can either be:
    1. **Immediate operand**: `#imm` or `#imm, lsl #12` (or a relocation modifier `:lo12:label` with no shift).
    2. **Extended/shifted register operand**: `Rm` or `Rm, ext #amount` (e.g. `x2, uxtw #2` or `x2, lsl #2`). -/
def parseExtOrImmReg (w : Width) : Parser (ExtOrImmReg w) := do
  skipHWs
  let c ← peek!
  -- Case 1: Immediate operand (e.g. `#42`, `#42, lsl #12`, or `:lo12:main`)
  if c == '#' || c == '-' || c.isDigit || c == ':' then do
    let expr ← parseConstExpr
    skipHWs
    let nextC? ← peek?
    if nextC? == some ',' then do
      skip
      skipHWs
      let shiftName ← parseName
      if shiftName.toLower == "lsl" then do
        skipHWs
        let amt ← parseInt
        match expr with
        | .int64 imm =>
          if imm.toInt < 0 || imm.toInt > 4095 then
            fail s!"immediate {imm.toInt} out of range [0, 4095]"
          else if amt == 12 then
            pure (.imm { imm := expr, shift := ImmShift.S12 })
          else if amt == 0 then
            pure (.imm { imm := expr, shift := ImmShift.S0 })
          else
            fail s!"invalid immediate shift for add: {amt} (must be 0 or 12)"
        | _ => fail "relocation modifiers and labels cannot be shifted with lsl in immediate operands"
      else
        fail s!"expected lsl for immediate shift, got {shiftName}"
    else
      match expr with
      | .int64 imm =>
        if imm.toInt < 0 || imm.toInt > 4095 then
          fail s!"immediate {imm.toInt} out of range [0, 4095]"
      | _ => pure ()
      pure (.imm { imm := expr, shift := ImmShift.S0 })
  -- Case 2: Extended or shifted register operand (e.g. `x2`, `x2, uxtw #2`, or `x2, lsl #2`)
  else do
    let regW ← parseRegOrZrW
    skipHWs
    let nextC? ← peek?
    if nextC? == some ',' then do
      skip
      skipHWs
      let extName ← parseName
      let extType ← liftExcept (getExtendType extName w)
      let amount ← parseExtendAmount
      pure (.ext { reg := regW, ext := { type := extType, amount := amount } })
    else do
      let extType := match regW.w with
        | .W64 => ExtendType.UXTX
        | .W32 => ExtendType.UXTW
      pure (.ext { reg := regW, ext := { type := extType, amount := ExtendAmount.E0 } })

def parseShiftRegExpr (w : Width) : Parser (ShiftRegExpr w) := do
  let reg ← parseRegOrZr w
  skipHWs
  let nextC? ← peek?
  if nextC? == some ',' then do
    skip
    skipHWs
    let shiftName ← parseName
    let shiftType ← match shiftName.toLower with
      | "lsl" => pure ShiftType.LSL
      | "lsr" => pure ShiftType.LSR
      | "asr" => pure ShiftType.ASR
      | _ => fail s!"unknown shift type: {shiftName}"
    skipHWs
    let amt ← parseInt64
    liftExcept (checkShiftAmount w amt)
    pure { reg := reg, amount := amt, shift := shiftType }
  else
    pure { reg := reg, amount := 0, shift := ShiftType.LSL }

-- ============================================================================
-- Optional Operand Parsing
-- ============================================================================

/-- Checks if the parser is positioned at horizontal whitespace followed by line end, EOF, or comment.
    If a comment is present, it is consumed up to the newline. -/
def isAtLineEndOrComment : Parser Bool := do
  skipHWs
  let c? ← peek?
  match c? with
  | none | some '\n' =>
    pure true
  | _ =>
    (attempt skipLineComment *> pure true) <|> pure false

/-- Parses an optional operand using `p`, or returns `defaultVal` if positioned at line end or comment. -/
def parseOptionalOperand {α : Type} (p : Parser α) (defaultVal : α) : Parser α := do
  if (← isAtLineEndOrComment) then
    pure defaultVal
  else
    p

-- ============================================================================
-- Condition Code Parsing
-- ============================================================================

def parseCondCode (s : String) : Option CondCode :=
  match s.toLower with
  | "eq" => some .EQ
  | "ne" => some .NE
  | "cs" | "hs" => some .CS
  | "cc" | "lo" => some .CC
  | "mi" => some .MI
  | "pl" => some .PL
  | "vs" => some .VS
  | "vc" => some .VC
  | "hi" => some .HI
  | "ls" => some .LS
  | "ge" => some .GE
  | "lt" => some .LT
  | "gt" => some .GT
  | "le" => some .LE
  | "al" => some .AL
  | "nv" => some .NV
  | _ => none

-- ============================================================================
-- Validation Helpers
-- ============================================================================

/-- Extract the underlying `XReg` if this is a general-purpose register (and not `XZR`/`WZR`). -/
def RegOrZr.toXReg? {w : Width} : RegOrZr w → Option XReg
  | .low (.reg r) _ => some r
  | _ => none

/-- Extract the underlying `XReg` if this is a general-purpose register (and not `SP`/`WSP`). -/
def RegOrSp.toXReg? {w : Width} : RegOrSp w → Option XReg
  | .low (.reg r) _ => some r
  | _ => none

/-- Validates architectural constraints for `LDP` and `STP` instructions:
    1. For `LDP`, `rt1` and `rt2` cannot be identical unless they are `XZR`/`WZR`.
    2. If writeback (`!` pre-index or post-index) is used, the base register (`Rn`) cannot be one of the transfer registers (`rt1` or `rt2`). -/
def checkLdpStpRegisters {w : Width} (isLdp : Bool) (reg1 : RegOrZr w) (reg2 : RegOrZr w) (mem : AddrExpr w) : Except String Unit := do
  if isLdp && reg1 == reg2 && (RegOrZr.toXReg? reg1).isSome then
    throw "unpredictable: identical destination registers in ldp instruction"
  let hasWriteback := match mem.off with | .imm i => i.index.isSome | _ => false
  if hasWriteback then
    if let some baseReg := RegOrSp.toXReg? mem.base then
      if RegOrZr.toXReg? reg1 == some baseReg || RegOrZr.toXReg? reg2 == some baseReg then
        throw "unpredictable: writeback base register is also a transfer register"
  pure ()

-- ============================================================================
-- Instruction Parsing Helpers
-- ============================================================================

def parseArithNoFlags
    (mkE : {w : Width} → RegOrSp w → RegOrSp w → ExtOrImmReg w → Operation w)
    (mkS : {w : Width} → RegOrZr w → RegOrZr w → ShiftRegExpr w → Operation w) : Parser Instr := do
  let op1W ← parseAnyRegW
  let w := op1W.1
  parseComma
  let op2 ← parseAnyReg w
  parseComma
  if op1W.2.isSp || op2.isSp then
    let dstSp ← op1W.2.toRegOrSp
    let src1Sp ← op2.toRegOrSp
    let op3 ← parseExtOrImmReg w
    pure ⟨w, mkE dstSp src1Sp op3⟩
  else if op1W.2.isXzr || op2.isXzr then
    let dstZr ← op1W.2.toRegOrZr
    let src1Zr ← op2.toRegOrZr
    let shiftOp ← parseShiftRegExpr w
    pure ⟨w, mkS dstZr src1Zr shiftOp⟩
  else
    (attempt do
      let dstZr ← op1W.2.toRegOrZr
      let src1Zr ← op2.toRegOrZr
      let shiftOp ← parseShiftRegExpr w
      pure ⟨w, mkS dstZr src1Zr shiftOp⟩)
    <|> (do
      let dstSp ← op1W.2.toRegOrSp
      let src1Sp ← op2.toRegOrSp
      let extOp ← parseExtOrImmReg w
      pure ⟨w, mkE dstSp src1Sp extOp⟩)

def parseArithFlags (instrName : String)
    (mkE : {w : Width} → RegOrZr w → RegOrSp w → ExtOrImmReg w → Operation w)
    (mkS : {w : Width} → RegOrZr w → RegOrZr w → ShiftRegExpr w → Operation w) : Parser Instr := do
  let op1W ← parseAnyRegW
  let w := op1W.1
  parseComma
  let op2 ← parseAnyReg w
  parseComma
  if op1W.2.isSp then
    fail s!"SP/WSP is not allowed as destination of {instrName}"
  else if op2.isSp then
    let dstZr ← op1W.2.toRegOrZr
    let src1Sp ← op2.toRegOrSp
    let op3 ← parseExtOrImmReg w
    pure ⟨w, mkE dstZr src1Sp op3⟩
  else if op1W.2.isXzr || op2.isXzr then
    let dstZr ← op1W.2.toRegOrZr
    let src1Zr ← op2.toRegOrZr
    let shiftOp ← parseShiftRegExpr w
    pure ⟨w, mkS dstZr src1Zr shiftOp⟩
  else
    (attempt do
      let dstZr ← op1W.2.toRegOrZr
      let src1Zr ← op2.toRegOrZr
      let shiftOp ← parseShiftRegExpr w
      pure ⟨w, mkS dstZr src1Zr shiftOp⟩)
    <|> (do
      let dstZr ← op1W.2.toRegOrZr
      let src1Sp ← op2.toRegOrSp
      let extOp ← parseExtOrImmReg w
      pure ⟨w, mkE dstZr src1Sp extOp⟩)

def parseCompare
    (mkE : {w : Width} → RegOrZr w → RegOrSp w → ExtOrImmReg w → Operation w)
    (mkS : {w : Width} → RegOrZr w → RegOrZr w → ShiftRegExpr w → Operation w) : Parser Instr := do
  let op1W ← parseAnyRegW
  let w := op1W.1
  parseComma
  let dstZr : RegOrZr w := match w with
    | .W64 => RegOrZr.XZR
    | .W32 => RegOrZr.WZR
  if op1W.2.isSp then
    let src1Sp ← op1W.2.toRegOrSp
    let op2 ← parseExtOrImmReg w
    pure ⟨w, mkE dstZr src1Sp op2⟩
  else if op1W.2.isXzr then
    let src1Zr ← op1W.2.toRegOrZr
    let shiftOp ← parseShiftRegExpr w
    pure ⟨w, mkS dstZr src1Zr shiftOp⟩
  else
    (attempt do
      let src1Zr ← op1W.2.toRegOrZr
      let shiftOp ← parseShiftRegExpr w
      pure ⟨w, mkS dstZr src1Zr shiftOp⟩)
    <|> (do
      let src1Sp ← op1W.2.toRegOrSp
      let extOp ← parseExtOrImmReg w
      pure ⟨w, mkE dstZr src1Sp extOp⟩)

def parseThreeRegs
    (mk : {w : Width} → RegOrZr w → RegOrZr w → RegOrZr w → Operation w) : Parser Instr := do
  let dstW ← parseRegOrZrW
  let w := dstW.w
  parseComma
  let src1 ← parseRegOrZr w
  parseComma
  let src2 ← parseRegOrZr w
  pure ⟨w, mk dstW.reg src1 src2⟩

def parseFourRegs
    (mk : {w : Width} → RegOrZr w → RegOrZr w → RegOrZr w → RegOrZr w → Operation w) : Parser Instr := do
  let dstW ← parseRegOrZrW
  let w := dstW.w
  parseComma
  let src1 ← parseRegOrZr w
  parseComma
  let src2 ← parseRegOrZr w
  parseComma
  let src3 ← parseRegOrZr w
  pure ⟨w, mk dstW.reg src1 src2 src3⟩

def parseLogical
    (mkS : {w : Width} → RegOrZr w → RegOrZr w → ShiftRegExpr w → Operation w) : Parser Instr := do
  let dstW ← parseRegOrZrW
  let w := dstW.w
  parseComma
  let src1 ← parseRegOrZr w
  parseComma
  let shiftOp ← parseShiftRegExpr w
  pure ⟨w, mkS dstW.reg src1 shiftOp⟩

-- ============================================================================
-- Instruction Parsing
-- ============================================================================

def parseInstr : Parser Instr := do
  skipHWs
  let mnemonic ← parseName
  let mn := mnemonic.toLower
  match mn with
  | "ldr" =>
    let dstW ← parseRegOrZrW
    parseComma
    let src ← parseAddrOrLit dstW.w
    pure ⟨dstW.w, .LDR dstW.reg src⟩

  | "str" =>
    let srcW ← parseRegOrZrW
    parseComma
    let dst ← parseAddr srcW.w
    pure ⟨srcW.w, .STR srcW.reg dst⟩

  | "ldp" =>
    let dst1W ← parseRegOrZrW
    parseComma
    let dst2 ← parseRegOrZr dst1W.w
    parseComma
    let src ← parsePairAddr dst1W.w
    liftExcept (checkLdpStpRegisters true dst1W.reg dst2 src)
    pure ⟨dst1W.w, .LDP dst1W.reg dst2 src⟩

  | "stp" =>
    let src1W ← parseRegOrZrW
    parseComma
    let src2 ← parseRegOrZr src1W.w
    parseComma
    let dst ← parsePairAddr src1W.w
    liftExcept (checkLdpStpRegisters false src1W.reg src2 dst)
    pure ⟨src1W.w, .STP src1W.reg src2 dst⟩

  | "add"  => parseArithNoFlags .ADD_e .ADD_s
  | "adds" => parseArithFlags "adds" .ADDS_e .ADDS_s
  | "cmn"  => parseCompare .ADDS_e .ADDS_s
  | "sub"  => parseArithNoFlags .SUB_e .SUB_s
  | "subs" => parseArithFlags "subs" .SUBS_e .SUBS_s
  | "cmp"  => parseCompare .SUBS_e .SUBS_s

  | "adc"  => parseThreeRegs .ADC
  | "adcs" => parseThreeRegs .ADCS
  | "sbc"  => parseThreeRegs .SBC
  | "sbcs" => parseThreeRegs .SBCS

  | "madd"  => parseFourRegs .MADD
  | "msub"  => parseFourRegs .MSUB
  | "mneg"  => do -- Alias of MSUB _, _, _, ZR
    let dstW ← parseRegOrZrW
    let w := dstW.w
    parseComma
    let src1 ← parseRegOrZr w
    parseComma
    let src2 ← parseRegOrZr w
    pure ⟨w, .MSUB dstW.reg src1 src2 (.low .XZR w)⟩

  | "mul"   => do -- Alias of MADD _, _, _, ZR
    let dstW ← parseRegOrZrW
    let w := dstW.w
    parseComma
    let src1 ← parseRegOrZr w
    parseComma
    let src2 ← parseRegOrZr w
    pure ⟨w, .MADD dstW.reg src1 src2 (.low .XZR w)⟩

  | "neg" => do -- Alias of SUB _, ZR, _, LSL #0
    let dstW ← parseRegOrZrW
    let w := dstW.w
    parseComma
    let src ← parseRegOrZr w
    pure ⟨w, .SUB_s dstW.reg (.low .XZR w) { reg := src, amount := 0, shift := .LSL }⟩

  | "negs" => do -- Alias of SUBS _, ZR, _, LSL #0
    let dstW ← parseRegOrZrW
    let w := dstW.w
    parseComma
    let src ← parseRegOrZr w
    pure ⟨w, .SUBS_s dstW.reg (.low .XZR w) { reg := src, amount := 0, shift := .LSL }⟩

  | "smulh" => do
    let dst ← parseRegOrZr .W64
    parseComma
    let src1 ← parseRegOrZr .W64
    parseComma
    let src2 ← parseRegOrZr .W64
    pure ⟨.W64, .SMULH dst src1 src2⟩

  | "umulh" => do
    let dst ← parseRegOrZr .W64
    parseComma
    let src1 ← parseRegOrZr .W64
    parseComma
    let src2 ← parseRegOrZr .W64
    pure ⟨.W64, .UMULH dst src1 src2⟩

  | "and"   => parseLogical .AND_s
  | "ands"  => parseLogical .ANDS_s
  | "orr"   => parseLogical .ORR_s
  | "orn"   => parseLogical .ORN_s
  | "eor"   => parseLogical .EOR_s
  | "bic"   => parseLogical .BIC_s
  | "tst"   => do  -- Alias of ANDS ZR, _, _
    let src1W ← parseRegOrZrW
    let w := src1W.w
    parseComma
    let src2 ← parseShiftRegExpr w
    pure ⟨w, .ANDS_s (.low .XZR w) src1W.reg src2⟩

  | "lsl"   => parseThreeRegs .LSLV -- Alias of LSLV
  | "lsr"   => parseThreeRegs .LSRV -- Alias of LSRV
  | "asr"   => parseThreeRegs .ASRV -- Alias of ASRV
  | "ror"   => parseThreeRegs .RORV -- Alias of RORV
  | "lslv"  => parseThreeRegs .LSLV
  | "lsrv"  => parseThreeRegs .LSRV
  | "asrv"  => parseThreeRegs .ASRV
  | "rorv"  => parseThreeRegs .RORV

  | "adr" =>
    let dst ← parseRegOrZr .W64
    parseComma
    let target ← parseConstExpr
    if let .int64 imm := target then
      liftExcept (checkAdrOffset imm)
    pure ⟨.W64, .ADR dst target⟩

  | "adrp" =>
    let dst ← parseRegOrZr .W64
    parseComma
    let target ← parseConstExpr
    if let .int64 imm := target then
      liftExcept (checkAdrpOffset imm)
    pure ⟨.W64, .ADRP dst target⟩

  | "b" =>
    let target ← parseConstExpr
    if let .int64 imm := target then
      liftExcept (checkBOffset imm)
    pure ⟨.W64, .B target⟩

  | "bl" =>
    let target ← parseConstExpr
    if let .int64 imm := target then
      liftExcept (checkBOffset imm)
    pure ⟨.W64, .BL target⟩

  | "blr" =>
    let target ← parseRegOrZr .W64
    pure ⟨.W64, .BLR target⟩

  | "br" =>
    let target ← parseRegOrZr .W64
    pure ⟨.W64, .BR target⟩

  | "ret" =>
    let target ← parseOptionalOperand (parseRegOrZr .W64) RegOrZr.X30
    pure ⟨.W64, .RET target⟩

  | "cbz" =>
    let regW ← parseRegOrZrW
    parseComma
    let target ← parseConstExpr
    if let .int64 imm := target then
      liftExcept (checkCbzOffset "cbz" imm)
    pure ⟨regW.w, .CBZ regW.reg target⟩

  | "cbnz" =>
    let regW ← parseRegOrZrW
    parseComma
    let target ← parseConstExpr
    if let .int64 imm := target then
      liftExcept (checkCbzOffset "cbnz" imm)
    pure ⟨regW.w, .CBNZ regW.reg target⟩

  | "tbz" =>
    let regW ← parseRegOrZrW
    parseComma
    let bit ← parseInt
    liftExcept (checkTbzBitPosition "tbz" regW.w bit)
    parseComma
    let target ← parseConstExpr
    if let .int64 imm := target then
      liftExcept (checkTbzOffset "tbz" imm)
    pure ⟨regW.w, .TBZ regW.reg bit.toNat target⟩

  | "tbnz" =>
    let regW ← parseRegOrZrW
    parseComma
    let bit ← parseInt
    liftExcept (checkTbzBitPosition "tbnz" regW.w bit)
    parseComma
    let target ← parseConstExpr
    if let .int64 imm := target then
      liftExcept (checkTbzOffset "tbnz" imm)
    pure ⟨regW.w, .TBNZ regW.reg bit.toNat target⟩

  | "nop" =>
    pure ⟨.W64, .NOP⟩

  | _ =>
    if mn.startsWith "b." then
      match parseCondCode (mn.drop 2).toString with
      | some cond =>
        let target ← parseConstExpr
        if let .int64 imm := target then
          liftExcept (checkBCondOffset imm)
        pure ⟨.W64, .B_cond cond target⟩
      | none => fail s!"unknown condition code in branch instruction: {mnemonic}"
    else
      fail s!"unsupported instruction: {mnemonic}"

-- ============================================================================
-- Label Parsing
-- ============================================================================

/-- Parse an optional label (name followed by colon).
    Uses attempt for proper backtracking if colon is not found. -/
def parseLabelDecl : Parser Label := do
  skipHWs
  (attempt do
    let name ← parseName
    skipHWs
    let _ ← pchar ':'
    pure name)

-- ============================================================================
-- Line and Program Parsing
-- ============================================================================

def skipSpaceAndCheckLineEnd : Parser Bool := isAtLineEndOrComment

def parseOptionalInstr : Parser (Option Directive) := do
  if (← skipSpaceAndCheckLineEnd) then
    pure none
  else
    let i ← parseInstr
    pure (some (Directive.instr i))

def checkLineEnd : Parser Unit := do
  if (← skipSpaceAndCheckLineEnd) then
    pure ()
  else
    fail "unexpected trailing characters on line"

/-- Parse a single line: optional label, followed by optional instruction or directive.
    Returns a list of directives found on the line. -/
def parseLine : Parser (List Directive) := do
  skipHWs
  let labels ← many (attempt do
    let l ← parseLabelDecl
    pure (Directive.label l))
  let instr ← parseOptionalInstr
  checkLineEnd
  let labelsList := labels.toList
  match instr with
  | some i => pure (labelsList ++ [i])
  | none   => pure labelsList

-- ============================================================================
-- Public API
-- ============================================================================

instance {T1} : Coe (ParseResult (List T1) (Sigma String.Pos)) (Except String (List T1)) where coe :=
  fun r => match r with
  | .success _ v => .ok v
  | .error _ .eof => .error "unexpected end of input"
  | .error _ (.other msg) => .error msg

def parse (input: String) : Except String Program := do
  let rawLines := (input.splitOn "\n")
  let (_, lines) ← rawLines.foldlM (fun (lineNum, acc) x => do
    match (parseLine ⟨ x, x.startPos ⟩ : Except String (List Directive)) with
    | .ok v => pure (lineNum + 1, v :: acc)
    | .error msg => .error s!"line {lineNum}: {msg}"
  ) ((1 : Nat), [])
  pure lines.reverse.flatten

/-- A version of `parse` that runs at compile-time. -/
scoped elab "parse(" s:str ")" : term => do
  match parse s.getString with
  | .ok p => return Lean.toExpr p
  | .error e => throwErrorAt s e

elab "parseAArch64(" s:str ")" : term => do
  match parse s.getString with
  | .ok p => return Lean.toExpr p
  | .error e => throwErrorAt s e

-- ============================================================================
-- Assembly Preprocessing (Directive Stripping)
-- ============================================================================

private def directiveKeywords : List String :=
  -- Architecture & CPU
  ["file", "text", "data", "bss", "rodata", "tbss", "tdata",
   "arch", "arch_extension", "cpu", "fpu", "eabi_attribute", "syntax",
   "tlsdesccall", "inst", "req", "unreq", "variant_pcs",
   -- Alignment & Layout
   "p2align", "balign", "align", "org", "previous", "pushsection", "popsection", "subsection",
   -- Symbol Binding & Visibility
   "globl", "global", "local", "type", "size", "section", "comm", "lcomm",
   "weak", "hidden", "protected", "internal", "ident", "set", "equ", "equiv",
   -- Call Frame Information (DWARF / PAC / BTI)
   "cfi_startproc", "cfi_endproc", "cfi_def_cfa", "cfi_sections", "cfi_personality", "cfi_lsda",
   "cfi_offset", "cfi_adjust_cfa_offset", "cfi_def_cfa_offset", "cfi_def_cfa_register",
   "cfi_restore", "cfi_remember_state", "cfi_restore_state", "cfi_return_column",
   "cfi_signal_frame", "cfi_window_save", "cfi_escape", "cfi_val_offset", "cfi_register",
   "cfi_same_value", "cfi_undefined", "cfi_rel_offset", "cfi_b_key_frame", "cfi_negate_ra_state",
   -- Data Emission & Buffers
   "byte", "2byte", "4byte", "8byte", "short", "int", "long", "word", "hword",
   "xword", "dword", "quad", "single", "double", "ascii", "asciz", "string",
   "zero", "space", "skip", "fill"]

private def extractDirectiveName (s : String) : String :=
  let rest := s.drop 1
  let nameStr := (rest.takeWhile (fun c => c != ' ' && c != '\t' && c != ',' && c != ':')).toString
  nameStr.toLower

private def keepLine (line : String) : Bool :=
  let stripped := (line.trimAsciiStart).toString
  if stripped.isEmpty || stripped.startsWith "#" || stripped.startsWith "//" then true
  else if !stripped.startsWith "." then true
  else
    let dirName := extractDirectiveName stripped
    if stripped.any (· == ':') then true
    else if directiveKeywords.contains dirName then false
    else false

def stripDirectives (content : String) : String :=
  let lines := content.splitOn "\n"
  let kept := lines.filter keepLine
  "\n".intercalate kept

-- ============================================================================
-- File Parsing Elaborators
-- ============================================================================

open Lean Elab Term

/-- Read a file at elaboration time and return its contents as a string literal. -/
elab "fileAsStringAArch64(" path:str ")" : term => do
  let pathStr := path.getString
  let contents ← IO.FS.readFile pathStr
  return mkStrLit contents

/-- Parse an AArch64 assembly file, stripping directives first.
    Throws error on parse failure. -/
elab "parseFileAArch64(" path:str ")" : term => do
  let pathStr := path.getString
  let content ← IO.FS.readFile pathStr
  let stripped := stripDirectives content
  match parse stripped with
  | .ok p => return Lean.toExpr p
  | .error e => throwErrorAt path e

end Kraken.AArch64.Parser
