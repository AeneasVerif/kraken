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

/-- Consume characters until the end of the line (newline not consumed). -/
def skipToNewline : Parser Unit := do
  let _ ← many (satisfy fun c => c != '\n')
  pure ()

/-- Skip a trailing line comment starting with `//`. -/
def skipTrailingComment : Parser Unit :=
  pstring "//" *> skipToNewline

/-- Skip a full-line comment starting with `#` or `//`. -/
def skipFullLineComment : Parser Unit :=
  (pchar '#' <|> (pstring "//" *> pure '/')) *> skipToNewline

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

/-- Parse a signed integer (hex, binary, or decimal) with optional leading `#` prefix (`#-16`, `-16`, or `#16`). -/
def parseInt : Parser Int := do
  skipHWs
  let _ ← optional (pchar '#')
  skipHWs
  let neg ← (pchar '-' *> pure true) <|> (pchar '+' *> pure false) <|> pure false
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
  pure (if v > 9223372036854775807 then
    Int64.ofInt (v - 18446744073709551616)
  else
    Int64.ofInt v)

def parseLabelRaw : Parser Label := parseName

/-- Parses a constant expression, including numeric immediates (`#16`), labels (`main`), and relocation modifiers (`:pg_hi21:main`, `:lo12:main`). -/
partial def parseConstExpr : Parser ConstExpr := do
  skipHWs
  let _ ← optional (pchar '#')
  skipHWs
  let c ← peek!
  if c == ':' then
    let mod ← (pstring ":pg_hi21:" *> pure ConstExpr.pg_hi21) <|> (pstring ":lo12:" *> pure ConstExpr.lo12)
    let inner ← parseConstExpr
    pure (mod inner)
  else if c == '-' || c == '+' || c.isDigit then
    let i ← parseInt64
    pure (.int64 i)
  else
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
  | "w28" => some (.W32, .X28) | "w29" => some (.W32, .X29) | "w30" => some (.W32, .X30)
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

/-- Extract the underlying `XReg` if this is a general-purpose register (and not `XZR`/`WZR`). -/
def RegOrZr.toXReg? {w : Width} : RegOrZr w → Option XReg
  | .low (.reg r) _ => some r
  | _ => none

/-- Extract the underlying `XReg` if this is a general-purpose register (and not `SP`/`WSP`). -/
def RegOrSp.toXReg? {w : Width} : RegOrSp w → Option XReg
  | .low (.reg r) _ => some r
  | _ => none

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

def getMovShift (w : Width) (amt : Nat) : Except String (MovShift w) :=
  match w, amt with
  | _, 0     => .ok .LSL0
  | _, 16    => .ok .LSL16
  | .W64, 32 => .ok .LSL32
  | .W64, 48 => .ok .LSL48
  | _, _     => .error s!"invalid move wide shift amount {amt} for width {w}"

def getMemExtendType (extName : String) (w : Width) : Except String MemExtendType :=
  match extName.toLower, w with
  | "uxtw", .W32 => .ok MemExtendType.UXTW
  | "uxtw", .W64 => .error "UXTW extension requires a 32-bit index register (Wn)"
  | "sxtw", .W32 => .ok MemExtendType.SXTW
  | "sxtw", .W64 => .error "SXTW extension requires a 32-bit index register (Wn)"
  | "uxtx", .W64 => .ok MemExtendType.UXTX
  | "uxtx", .W32 => .error "UXTX extension requires a 64-bit index register (Xn)"
  | "sxtx", .W64 => .ok MemExtendType.SXTX
  | "sxtx", .W32 => .error "SXTX extension requires a 64-bit index register (Xn)"
  | "lsl",  .W64 => .ok MemExtendType.UXTX
  | "lsl",  .W32 => .ok MemExtendType.UXTW
  | ext,    _    => .error s!"unknown memory extension type: {ext}"

-- ============================================================================
-- Validation Helpers
-- ============================================================================

def checkLoadStoreOffset (w : Width) (imm : Int64) (allowUnscaled : Bool) : Except String Unit :=
  let (maxOff, align) := match w with | .W32 => (16380, 4) | .W64 => (32760, 8)
  let isScaled := imm.toInt >= 0 && imm.toInt <= maxOff && imm.toInt % align == 0
  let isUnscaled := allowUnscaled && imm.toInt >= -256 && imm.toInt <= 255
  if isScaled || isUnscaled then
    .ok ()
  else if allowUnscaled then
    .error s!"offset {imm.toInt} is neither a valid scaled offset [0, {maxOff}] (multiple of {align}) nor a valid unscaled offset [-256, 255]"
  else
    .error s!"unsigned offset {imm.toInt} out of range [0, {maxOff}] or not a multiple of {align}"

def checkUnscaledOffset (imm : Int64) : Except String Unit :=
  if imm.toInt < -256 || imm.toInt > 255 then
    .error s!"unscaled offset {imm.toInt} out of range [-256, 255]"
  else .ok ()

def addrExprNeedsUnscaled {w : Width} (addr : AddrExpr w) : Bool :=
  match addr.off with
  | .imm i =>
    match i.index, i.imm with
    | none, .int64 imm =>
      let (_, align) := match w with | .W32 => (16380, 4) | .W64 => (32760, 8)
      imm.toInt < 0 || imm.toInt % align != 0
    | _, _ => false
  | _ => false

def addrOrLitNeedsUnscaled {w : Width} (a : AddrOrLit w) : Bool :=
  match a with
  | .addr addr => addrExprNeedsUnscaled addr
  | .lit _ => false

def addrExprToUnscaled {w : Width} (addr : AddrExpr w) : Option UnscaledAddrExpr :=
  match addr.off with
  | .imm i =>
    match i.index with
    | none => some { base := addr.base, imm := i.imm }
    | some _ => none
  | _ => none

def addrOrLitToUnscaled {w : Width} (a : AddrOrLit w) : Option UnscaledAddrExpr :=
  match a with
  | .addr addr => addrExprToUnscaled addr
  | .lit _ => none

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

def isContiguousOnes (v : Nat) (E : Nat) : Bool :=
  v > 0 && v < ((1 <<< E) - 1) && ((v + 1) &&& v) == 0

def isRotatedRunOfOnesAux (elem : Nat) (E : Nat) : Nat → Bool
  | 0 => false
  | n + 1 =>
    if isContiguousOnes elem E then
      true
    else
      let nextElem := (elem >>> 1) ||| ((elem &&& 1) <<< (E - 1))
      isRotatedRunOfOnesAux nextElem E n

def isRotatedRunOfOnes (elem : Nat) (E : Nat) : Bool :=
  isRotatedRunOfOnesAux elem E E

def repeatElement (pattern : Nat) (wBits : Nat) (E : Nat) : Nat :=
  match wBits, E with
  | 64, 64 => pattern
  | 64, 32 => pattern * 0x0000000100000001
  | 64, 16 => pattern * 0x0001000100010001
  | 64, 8  => pattern * 0x0101010101010101
  | 64, 4  => pattern * 0x1111111111111111
  | 64, 2  => pattern * 0x5555555555555555
  | 32, 32 => pattern
  | 32, 16 => pattern * 0x00010001
  | 32, 8  => pattern * 0x01010101
  | 32, 4  => pattern * 0x11111111
  | 32, 2  => pattern * 0x55555555
  | _, _ => 0

def isRepeatedPattern (val : Nat) (wBits : Nat) (E : Nat) : Bool :=
  let pattern := val &&& ((1 <<< E) - 1)
  val == repeatElement pattern wBits E

def isValidLogicalImmediate (w : Width) (val : Int64) : Bool :=
  let vNat := match w with
    | .W32 => (val.toBitVec.toNat &&& 0xFFFFFFFF)
    | .W64 => val.toBitVec.toNat
  let wBits := w.bits
  let maxVal := (1 <<< wBits) - 1
  if vNat == 0 || vNat == maxVal then
    false
  else
    let sizes := match w with
      | .W32 => [2, 4, 8, 16, 32]
      | .W64 => [2, 4, 8, 16, 32, 64]
    sizes.any (fun E =>
      isRepeatedPattern vNat wBits E &&
      isRotatedRunOfOnes (vNat &&& ((1 <<< E) - 1)) E)

def checkLogicalImmediate (w : Width) (imm : Int64) : Except String Unit :=
  if isValidLogicalImmediate w imm then
    .ok ()
  else
    .error s!"invalid logical immediate: {intToHexStr imm.toInt}"

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
-- Operand Parsing
-- ============================================================================

/-- Parses memory addressing operands for general load/store instructions (`LDR`/`STR`).
    Supports the following AArch64 addressing modes:
    1. **Base-only / Post-indexed**: `[base]` or `[base], #imm`
    2. **Immediate / Pre-indexed**: `[base, #imm]` or `[base, #imm]!` or `[base, #:lo12:label]`
    3. **Register offset with optional extension/shift**: `[base, Rm]` or `[base, Rm, ext #amount]` -/
def parseAddr (w : Width) (allowUnscaled : Bool := false) : Parser (AddrExpr w) := do
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
          liftExcept (checkLoadStoreOffset w imm allowUnscaled)
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

def parseUnscaledAddr : Parser UnscaledAddrExpr := do
  skipHWs
  let _ ← pchar '['
  let base ← parseRegOrSp .W64
  skipHWs
  let c ← peek!
  if c == ']' then do
    skip
    pure { base := base, imm := .int64 0 }
  else if c == ',' then do
    skip
    skipHWs
    let nextC ← peek!
    if nextC == '#' || nextC == '-' || nextC.isDigit then do
      let expr ← parseConstExpr
      skipHWs
      let _ ← pchar ']'
      match expr with
      | .int64 imm => liftExcept (checkUnscaledOffset imm)
      | _ => pure ()
      pure { base := base, imm := expr }
    else
      fail "expected immediate offset in unscaled address operand"
  else
    fail s!"expected ',' or ']' after base register in unscaled address operand, got {c}"

def parseAddrOrLit (w : Width) (allowUnscaled : Bool := false) : Parser (AddrOrLit w) := do
  skipHWs
  let c ← peek!
  if c == '[' then do
    let m ← parseAddr w allowUnscaled
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

def parseShiftRegExpr (w : Width) (allowRor : Bool := false) : Parser (ShiftRegExpr w) := do
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
      | "ror" =>
        if allowRor then pure ShiftType.ROR
        else fail "arithmetic instructions do not support ROR shift"
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
    (attempt skipTrailingComment *> pure true) <|> pure false

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

def parseCondArg : Parser CondCode := do
  skipHWs
  let name ← parseName
  match parseCondCode name with
  | some c => pure c
  | none => fail s!"unknown condition code: {name}"

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

def parseLogicalNoFlags
    (mkI : {w : Width} → RegOrSp w → RegOrZr w → ConstExpr → Operation w)
    (mkS : {w : Width} → RegOrZr w → RegOrZr w → ShiftRegExpr w → Operation w) : Parser Instr := do
  let dstW ← parseAnyRegW
  let w := dstW.1
  parseComma
  let src1 ← parseRegOrZr w
  parseComma
  skipHWs
  let nextC ← peek!
  if nextC == '#' || nextC == '-' || nextC.isDigit then
    let dstSp ← dstW.2.toRegOrSp
    let imm ← parseConstExpr
    if let .int64 val := imm then
      liftExcept (checkLogicalImmediate w val)
    pure ⟨w, mkI dstSp src1 imm⟩
  else
    let dstZr ← dstW.2.toRegOrZr
    let shiftOp ← parseShiftRegExpr w true
    pure ⟨w, mkS dstZr src1 shiftOp⟩

def parseLogicalFlags
    (mkI : {w : Width} → RegOrZr w → RegOrZr w → ConstExpr → Operation w)
    (mkS : {w : Width} → RegOrZr w → RegOrZr w → ShiftRegExpr w → Operation w) : Parser Instr := do
  let dstW ← parseRegOrZrW
  let w := dstW.w
  parseComma
  let src1 ← parseRegOrZr w
  parseComma
  skipHWs
  let nextC ← peek!
  if nextC == '#' || nextC == '-' || nextC.isDigit then
    let imm ← parseConstExpr
    if let .int64 val := imm then
      liftExcept (checkLogicalImmediate w val)
    pure ⟨w, mkI dstW.reg src1 imm⟩
  else
    let shiftOp ← parseShiftRegExpr w true
    pure ⟨w, mkS dstW.reg src1 shiftOp⟩

def parseLogical
    (mkS : {w : Width} → RegOrZr w → RegOrZr w → ShiftRegExpr w → Operation w) : Parser Instr := do
  let dstW ← parseRegOrZrW
  let w := dstW.w
  parseComma
  let src1 ← parseRegOrZr w
  parseComma
  let shiftOp ← parseShiftRegExpr w true
  pure ⟨w, mkS dstW.reg src1 shiftOp⟩

def parseCondSelect
    (mk : {w : Width} → RegOrZr w → RegOrZr w → RegOrZr w → CondCode → Operation w) : Parser Instr := do
  let dstW ← parseRegOrZrW
  let w := dstW.w
  parseComma
  let src1 ← parseRegOrZr w
  parseComma
  let src2 ← parseRegOrZr w
  parseComma
  let cond ← parseCondArg
  pure ⟨w, mk dstW.reg src1 src2 cond⟩

def parseCondAlias
    (mk : {w : Width} → RegOrZr w → RegOrZr w → RegOrZr w → CondCode → Operation w)
    (sameSrc : Bool) (useXzr : Bool) : Parser Instr := do
  let dstW ← parseRegOrZrW
  let w := dstW.w
  parseComma
  let (src1, src2) ← if useXzr then
    pure (.low .XZR w, .low .XZR w)
  else if sameSrc then do
    let s ← parseRegOrZr w
    parseComma
    pure (s, s)
  else do
    let s1 ← parseRegOrZr w
    parseComma
    let s2 ← parseRegOrZr w
    parseComma
    pure (s1, s2)
  let cond ← parseCondArg
  pure ⟨w, mk dstW.reg src1 src2 cond.invert⟩

def tryMovz (w : Width) (val : BitVec w.bits) : Option (Int64 × MovShift w) :=
  let n := val.toNat
  if n >>> 16 == 0 then
    some (.ofNat n, .LSL0)
  else if n &&& 0xFFFF == 0 && n >>> 32 == 0 then
    some (.ofNat (n >>> 16), .LSL16)
  else
    match w with
    | .W32 => none
    | .W64 =>
      if n &&& 0xFFFFFFFF == 0 && n >>> 48 == 0 then
        some (.ofNat (n >>> 32), .LSL32)
      else if n &&& 0xFFFFFFFFFFFF == 0 then
        some (.ofNat (n >>> 48), .LSL48)
      else
        none

def tryMovzOrMovn (w : Width) (val : BitVec w.bits) : Option (Bool × Int64 × MovShift w) :=
  match tryMovz w val with
  | some (imm16, shift) => some (false, imm16, shift)
  | none =>
    let invVal := ~~~val
    match tryMovz w invVal with
    | some (imm16, shift) => some (true, imm16, shift)
    | none => none

def parseMov : Parser Instr := do
  let dstW ← parseAnyRegW
  let w := dstW.1
  parseComma
  skipHWs
  let nextC ← peek!
  if nextC == '#' || nextC == '-' || nextC.isDigit then
    let imm ← parseConstExpr
    if let .int64 val := imm then
      if !dstW.2.isSp then
        let dstZr ← dstW.2.toRegOrZr
        let valBitVec := BitVec.ofInt w.bits val.toInt
        match tryMovzOrMovn w valBitVec with
        | some (false, imm16, shift) => pure ⟨w, .MOVZ dstZr (.int64 imm16) shift⟩
        | some (true, imm16, shift)  => pure ⟨w, .MOVN dstZr (.int64 imm16) shift⟩
        | none =>
          match checkLogicalImmediate w val with
          | .ok _ =>
            let dstSp ← dstW.2.toRegOrSp
            pure ⟨w, .ORR_i dstSp (.low .XZR w) imm⟩
          | .error _ => fail "immediate cannot be moved by a single instruction (requires MOVZ/MOVK sequence)"
      else
        let dstSp ← dstW.2.toRegOrSp
        liftExcept (checkLogicalImmediate w val)
        pure ⟨w, .ORR_i dstSp (.low .XZR w) imm⟩
    else
      let dstSp ← dstW.2.toRegOrSp
      pure ⟨w, .ORR_i dstSp (.low .XZR w) imm⟩
  else
    let srcAny ← parseAnyReg w
    if dstW.2.isSp || srcAny.isSp then
      let dstSp ← dstW.2.toRegOrSp
      let srcSp ← srcAny.toRegOrSp
      pure ⟨w, .ADD_e dstSp srcSp (.imm { imm := 0, shift := .S0 })⟩
    else
      let dstZr ← dstW.2.toRegOrZr
      let srcZr ← srcAny.toRegOrZr
      pure ⟨w, .ORR_s dstZr (.low .XZR w) { reg := srcZr, amount := 0, shift := .LSL }⟩

def parseMvn : Parser Instr := do
  let dstW ← parseRegOrZrW
  let w := dstW.w
  parseComma
  let shiftOp ← parseShiftRegExpr w true
  pure ⟨w, .ORN_s dstW.reg (.low .XZR w) shiftOp⟩

def parseMoveWide
    (mk : {w : Width} → RegOrZr w → ConstExpr → MovShift w → Operation w) : Parser Instr := do
  let dstW ← parseRegOrZrW
  let w := dstW.w
  parseComma
  let imm ← parseConstExpr
  if let .int64 val := imm then
    if val.toInt < 0 || val.toInt > 0xFFFF then
      fail s!"move wide immediate {val.toInt} out of range [0, 65535]"
  let shift ← (attempt do
    parseComma
    skipHWs
    let name ← parseName
    if name.toLower != "lsl" then fail "only lsl shift supported for move wide"
    let amt ← parseConstExpr
    match amt with
    | .int64 n => liftExcept (getMovShift w n.toBitVec.toNat)
    | _ => liftExcept (getMovShift w 0)
  ) <|> liftExcept (getMovShift w 0)
  pure ⟨w, mk dstW.reg imm shift⟩

def parsePairMem
    (mk : {w : Width} → RegOrZr w → RegOrZr w → AddrExpr w → Operation w)
    (isLdp : Bool) : Parser Instr := do
  let reg1W ← parseRegOrZrW
  parseComma
  let reg2 ← parseRegOrZr reg1W.w
  parseComma
  let mem ← parsePairAddr reg1W.w
  liftExcept (checkLdpStpRegisters isLdp reg1W.reg reg2 mem)
  pure ⟨reg1W.w, mk reg1W.reg reg2 mem⟩

def parseThreeRegsW64
    (mk : RegOrZr .W64 → RegOrZr .W64 → RegOrZr .W64 → Operation .W64) : Parser Instr := do
  let dst ← parseRegOrZr .W64
  parseComma
  let src1 ← parseRegOrZr .W64
  parseComma
  let src2 ← parseRegOrZr .W64
  pure ⟨.W64, mk dst src1 src2⟩

def parseThreeRegsWithZr
    (mk : {w : Width} → RegOrZr w → RegOrZr w → RegOrZr w → RegOrZr w → Operation w) : Parser Instr := do
  let dstW ← parseRegOrZrW
  let w := dstW.w
  parseComma
  let src1 ← parseRegOrZr w
  parseComma
  let src2 ← parseRegOrZr w
  pure ⟨w, mk dstW.reg src1 src2 (.low .XZR w)⟩

def parseNegAlias
    (mk : {w : Width} → RegOrZr w → RegOrZr w → ShiftRegExpr w → Operation w) : Parser Instr := do
  let dstW ← parseRegOrZrW
  let w := dstW.w
  parseComma
  let src ← parseRegOrZr w
  pure ⟨w, mk dstW.reg (.low .XZR w) { reg := src, amount := 0, shift := .LSL }⟩

def parseTstAlias : Parser Instr := do
  let src1W ← parseRegOrZrW
  let w := src1W.w
  parseComma
  skipHWs
  let nextC ← peek!
  if nextC == '#' || nextC == '-' || nextC.isDigit then
    let imm ← parseConstExpr
    if let .int64 val := imm then
      liftExcept (checkLogicalImmediate w val)
    pure ⟨w, .ANDS_i (.low .XZR w) src1W.reg imm⟩
  else
    let src2 ← parseShiftRegExpr w true
    pure ⟨w, .ANDS_s (.low .XZR w) src1W.reg src2⟩

def parseAdr (checkOffset : Int64 → Except String Unit)
    (mk : RegOrZr .W64 → ConstExpr → Operation .W64) : Parser Instr := do
  let dst ← parseRegOrZr .W64
  parseComma
  let target ← parseConstExpr
  if let .int64 imm := target then
    liftExcept (checkOffset imm)
  pure ⟨.W64, mk dst target⟩

def parseBranch (mk : ConstExpr → Operation .W64) : Parser Instr := do
  let target ← parseConstExpr
  if let .int64 imm := target then
    liftExcept (checkBOffset imm)
  pure ⟨.W64, mk target⟩

def parseBranchReg (mk : RegOrZr .W64 → Operation .W64) : Parser Instr := do
  let target ← parseRegOrZr .W64
  pure ⟨.W64, mk target⟩

def parseCbz (name : String)
    (mk : {w : Width} → RegOrZr w → ConstExpr → Operation w) : Parser Instr := do
  let regW ← parseRegOrZrW
  parseComma
  let target ← parseConstExpr
  if let .int64 imm := target then
    liftExcept (checkCbzOffset name imm)
  pure ⟨regW.w, mk regW.reg target⟩

def parseTbz (name : String)
    (mk : {w : Width} → RegOrZr w → Nat → ConstExpr → Operation w) : Parser Instr := do
  let regW ← parseRegOrZrW
  parseComma
  let bit ← parseInt
  liftExcept (checkTbzBitPosition name regW.w bit)
  parseComma
  let target ← parseConstExpr
  if let .int64 imm := target then
    liftExcept (checkTbzOffset name imm)
  pure ⟨regW.w, mk regW.reg bit.toNat target⟩

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
    let src ← parseAddrOrLit dstW.w true
    if addrOrLitNeedsUnscaled src then
      match addrOrLitToUnscaled src with
      | some uoff => pure ⟨dstW.w, .LDUR dstW.reg uoff⟩
      | none => fail "unscaled load cannot be literal or register offset"
    else
      pure ⟨dstW.w, .LDR dstW.reg src⟩

  | "str" =>
    let srcW ← parseRegOrZrW
    parseComma
    let dst ← parseAddr srcW.w true
    if addrExprNeedsUnscaled dst then
      match addrExprToUnscaled dst with
      | some uoff => pure ⟨srcW.w, .STUR srcW.reg uoff⟩
      | none => fail "unscaled store cannot be register offset"
    else
      pure ⟨srcW.w, .STR srcW.reg dst⟩

  | "ldur" =>
    let dstW ← parseRegOrZrW
    parseComma
    let src ← parseUnscaledAddr
    pure ⟨dstW.w, .LDUR dstW.reg src⟩

  | "stur" =>
    let srcW ← parseRegOrZrW
    parseComma
    let dst ← parseUnscaledAddr
    pure ⟨srcW.w, .STUR srcW.reg dst⟩

  | "ldp"   => parsePairMem .LDP true
  | "stp"   => parsePairMem .STP false

  | "add"   => parseArithNoFlags .ADD_e .ADD_s
  | "adds"  => parseArithFlags "adds" .ADDS_e .ADDS_s
  | "cmn"   => parseCompare .ADDS_e .ADDS_s
  | "sub"   => parseArithNoFlags .SUB_e .SUB_s
  | "subs"  => parseArithFlags "subs" .SUBS_e .SUBS_s
  | "cmp"   => parseCompare .SUBS_e .SUBS_s

  | "adc"   => parseThreeRegs .ADC
  | "adcs"  => parseThreeRegs .ADCS
  | "sbc"   => parseThreeRegs .SBC
  | "sbcs"  => parseThreeRegs .SBCS

  | "madd"  => parseFourRegs .MADD
  | "msub"  => parseFourRegs .MSUB
  | "mneg"  => parseThreeRegsWithZr .MSUB
  | "mul"   => parseThreeRegsWithZr .MADD

  | "neg"   => parseNegAlias .SUB_s
  | "negs"  => parseNegAlias .SUBS_s

  | "smulh" => parseThreeRegsW64 .SMULH
  | "umulh" => parseThreeRegsW64 .UMULH

  | "and"   => parseLogicalNoFlags .AND_i .AND_s
  | "ands"  => parseLogicalFlags .ANDS_i .ANDS_s
  | "orr"   => parseLogicalNoFlags .ORR_i .ORR_s
  | "orn"   => parseLogical .ORN_s
  | "eor"   => parseLogicalNoFlags .EOR_i .EOR_s
  | "bic"   => parseLogical .BIC_s
  | "tst"   => parseTstAlias

  | "lsl"   => parseThreeRegs .LSLV
  | "lsr"   => parseThreeRegs .LSRV
  | "asr"   => parseThreeRegs .ASRV
  | "ror"   => parseThreeRegs .RORV
  | "lslv"  => parseThreeRegs .LSLV
  | "lsrv"  => parseThreeRegs .LSRV
  | "asrv"  => parseThreeRegs .ASRV
  | "rorv"  => parseThreeRegs .RORV

  | "csel"  => parseCondSelect .CSEL
  | "csinc" => parseCondSelect .CSINC
  | "csinv" => parseCondSelect .CSINV
  | "csneg" => parseCondSelect .CSNEG
  | "cset"  => parseCondAlias .CSINC true true
  | "csetm" => parseCondAlias .CSINV true true
  | "cinc"  => parseCondAlias .CSINC true false
  | "cinv"  => parseCondAlias .CSINV true false
  | "cneg"  => parseCondAlias .CSNEG true false

  | "mov"   => parseMov
  | "mvn"   => parseMvn
  | "movz"  => parseMoveWide .MOVZ
  | "movk"  => parseMoveWide .MOVK
  | "movn"  => parseMoveWide .MOVN

  | "adr"   => parseAdr checkAdrOffset .ADR
  | "adrp"  => parseAdr checkAdrpOffset .ADRP

  | "b"     => parseBranch .B
  | "bl"    => parseBranch .BL
  | "blr"   => parseBranchReg .BLR
  | "br"    => parseBranchReg .BR
  | "ret"   => do
    let target ← parseOptionalOperand (parseRegOrZr .W64) RegOrZr.X30
    pure ⟨.W64, .RET target⟩

  | "cbz"   => parseCbz "cbz" .CBZ
  | "cbnz"  => parseCbz "cbnz" .CBNZ
  | "tbz"   => parseTbz "tbz" .TBZ
  | "tbnz"  => parseTbz "tbnz" .TBNZ

  | "nop"   => pure ⟨.W64, .NOP⟩

  | _ =>
    let condStr? :=
      if mn.startsWith "b." then some (mn.drop 2).toString
      else if mn.startsWith "b" && mn.length == 3 then some (mn.drop 1).toString
      else none
    match condStr?.bind parseCondCode with
    | some cond =>
      let target ← parseConstExpr
      if let .int64 imm := target then
        liftExcept (checkBCondOffset imm)
      pure ⟨.W64, .B_cond cond target⟩
    | none =>
      if mn.startsWith "b." then
        fail s!"unknown condition code in branch instruction: {mnemonic}"
      else
        fail s!"unsupported instruction: {mnemonic}"

-- ============================================================================
-- Line and Program Parsing
-- ============================================================================

/-- Parse an optional label (name followed by colon).
    Uses attempt for proper backtracking if colon is not found. -/
def parseLabelDecl : Parser Label := do
  skipHWs
  attempt do
    let name ← parseName
    skipHWs
    let _ ← pchar ':'
    pure name

def parseOptionalInstr : Parser (Option Directive) := do
  if (← isAtLineEndOrComment) then
    pure none
  else
    let i ← parseInstr
    pure (some (Directive.instr i))

def checkLineEnd : Parser Unit := do
  if (← isAtLineEndOrComment) then
    pure ()
  else
    fail "unexpected trailing characters on line"

/-- Parse a single line: optional label, followed by optional instruction or directive.
    Returns a list of directives found on the line. -/
def parseLine : Parser (List Directive) := do
  skipHWs
  let c? ← peek?
  if c? == some '#' || c? == some '/' then
    let _ ← attempt skipFullLineComment
    checkLineEnd
    pure []
  else
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
