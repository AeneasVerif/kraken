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

/-- Convert a hexadecimal digit character to its integer value. -/
def hexVal (c : Char) : Int :=
  if c >= '0' && c <= '9' then c.toNat - '0'.toNat
  else if c >= 'a' && c <= 'f' then c.toNat - 'a'.toNat + 10
  else c.toNat - 'A'.toNat + 10

/-- Parse an unsigned hexadecimal integer literal prefixed by `0x` or `0X`. -/
def parseHex : Parser Int := do
  let _ ← pstring "0x" <|> pstring "0X"
  let digits ← many1 hexDigit
  pure (digits.foldl (fun acc d => acc * 16 + hexVal d) 0)

/-- Parse a single binary digit character (`0` or `1`). -/
def binDigit : Parser Char := satisfy fun c => c == '0' || c == '1'

/-- Parse an unsigned binary integer literal prefixed by `0b` or `0B`. -/
def parseBin : Parser Int := do
  let _ ← pstring "0b" <|> pstring "0B"
  let digits ← many1 binDigit
  pure (digits.foldl (fun acc d => acc * 2 + (d.toNat - '0'.toNat)) 0)

/-- Parse an unsigned decimal integer literal (e.g. `4096`). -/
def parseDec : Parser Int := do
  let digits ← many1 digit
  pure (digits.foldl (fun acc d => acc * 10 + (d.toNat - '0'.toNat)) 0)

/--
Parse an unsigned integer literal in hexadecimal (`0x...`), binary (`0b...`),
or decimal format.
-/
def parseNumber : Parser Int := attempt parseHex <|> attempt parseBin <|> parseDec

/--
Parse a signed integer literal (hex, binary, or decimal) with an optional
leading `#` prefix and optional `+`/`-` sign (e.g. `#-16`, `-16`, or `#16`).
-/
def parseInt : Parser Int := do
  skipHWs
  let _ ← optional (pchar '#')
  skipHWs
  let neg ← (pchar '-' *> pure true) <|> (pchar '+' *> pure false) <|> pure false
  skipHWs
  let val ← parseNumber
  pure (if neg then -val else val)

/--
Parse a symbol name or identifier (e.g. a register name, instruction mnemonic,
or label name).
- Starts with an alphabetic character, `_`, or `.`.
- Followed by zero or more alphanumeric characters, `_`, or `.`.
-/
def parseName : Parser String := do
  let first ← satisfy fun c => c.isAlpha || c == '_' || c == '.'
  let rest ← many (satisfy fun c => c.isAlphanum || c == '_' || c == '.')
  pure (String.ofList (#[first] ++ rest).toList)

/--
Parse a signed integer literal and convert it to `Int64`.
- **Limits**: Rejects integer literals outside the signed or unsigned 64-bit
  range (`[-2^63, 2^64 - 1]`).
-/
def parseInt64 : Parser Int64 := do
  let v ← parseInt
  if v < -9223372036854775808 || v >= 18446744073709551616 then
    fail s!"immediate {v} out of 64-bit range"
  pure (if v > 9223372036854775807 then
    Int64.ofInt (v - 18446744073709551616)
  else
    Int64.ofInt v)

/--
Parse a non-negative immediate integer value.
- Fails if the parsed integer is negative.
-/
def parseImmNat : Parser Nat := do
  let i ← parseInt
  if i < 0 then
    fail s!"expected non-negative immediate, got {i}"
  pure i.toNat

/-- Parse a raw label name as a string identifier. -/
def parseLabelRaw : Parser Label := parseName

/--
Parse a constant expression (`ConstExpr`):
- Relocation modifiers: `:pg_hi21:symbol` or `:lo12:symbol`.
- Numeric integer immediate: e.g. `#16`, `#-8`, or `0x1000`.
- Symbol label: e.g. `main` or `loop`.
-/
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

/-- Enforce that an operand's actual parsed width matches the expected instruction width (`w`). -/
def checkWidth {T : Width → Type} (expected actual : Width) (val : T actual) : Parser (T expected) :=
  if h : expected = actual then
    pure (h ▸ val)
  else
    fail s!"expected {expected} register, got {actual}"

/-- Parse a register operand where register index 31 means `SP`/`WSP` (`RegOrSpW`). -/
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

/-- Parse a register operand where register index 31 means `XZR`/`WZR` (`RegOrZrW`). -/
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

/-- Parse a `RegOrSp` register operand and verify it matches width `w`. -/
def parseRegOrSp (w : Width) : Parser (RegOrSp w) := do
  let ⟨w', r⟩ ← parseRegOrSpW
  checkWidth w w' r

/-- Parse a `RegOrZr` register operand and verify it matches width `w`. -/
def parseRegOrZr (w : Width) : Parser (RegOrZr w) := do
  let ⟨w', r⟩ ← parseRegOrZrW
  checkWidth w w' r

/--
A generic parsed register (`gpr`, `sp`, or `xzr`) before instruction-specific
context validation resolves index 31.
-/
inductive AnyReg (w : Width)
  | gpr (r : XReg) : AnyReg w
  | sp : AnyReg w
  | xzr : AnyReg w

abbrev AnyRegW := (w : Width) × AnyReg w

/-- Parse any valid register name and return its width and `AnyReg` variant. -/
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

/-- Parse any register name and verify that its width matches `w`. -/
def parseAnyReg (w : Width) : Parser (AnyReg w) := do
  let ⟨w', r⟩ ← parseAnyRegW
  checkWidth w w' r

/-- Convert `AnyReg w` to `RegOrSp w`, rejecting `XZR`/`WZR` where `SP`/`WSP` is expected. -/
def AnyReg.toRegOrSp {w : Width} : AnyReg w → Parser (RegOrSp w)
  | .gpr r => pure (.low (.reg r) w)
  | .sp => match w with
    | .W64 => pure RegOrSp.SP
    | .W32 => pure RegOrSp.WSP
  | .xzr => fail "xzr/wzr not allowed in immediate/extended register instruction (sp expected)"

/-- Convert `AnyReg w` to `RegOrZr w`, rejecting `SP`/`WSP` where `XZR`/`WZR` is expected. -/
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

/--
Validate a memory extension shift amount (`0` or log2 of access size in bytes).
- `.W32`: Allows `0` (`E0`) or `2` (`E2`, `LSL #2`).
- `.W64`: Allows `0` (`E0`) or `3` (`E3`, `LSL #3`).
-/
def getMemExtendAmount (w : Width) (amt : Nat) : Except String (MemExtendAmount w) :=
  match w, amt with
  | .W32, 0 => .ok .E0
  | .W32, 2 => .ok .E2
  | .W64, 0 => .ok .E0
  | .W64, 3 => .ok .E3
  | _, _ => .error s!"invalid memory extension shift amount {amt} for width {w}"

/--
Validate a move-wide immediate shift amount (`MOVZ`/`MOVK`/`MOVN`).
- `.W32`: Allows `0` or `16`.
- `.W64`: Allows `0`, `16`, `32`, or `48`.
-/
def getMovShift (w : Width) (amt : Nat) : Except String (MovShift w) :=
  match w, amt with
  | _, 0     => .ok .LSL0
  | _, 16    => .ok .LSL16
  | .W64, 32 => .ok .LSL32
  | .W64, 48 => .ok .LSL48
  | _, _     => .error s!"invalid move wide shift amount {amt} for width {w}"

/--
Validate a memory index extension type (`UXTW`, `SXTW`, `UXTX`, `SXTX`, `LSL`)
and check that the register width matches:
- `UXTW`/`SXTW` require a 32-bit register (`Wn`).
- `UXTX`/`SXTX` require a 64-bit register (`Xn`).
-/
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

/--
Validate a load/store immediate byte offset:
- **Unsigned scaled offset (`allowUnscaled = false` or `isScaled = true`)**:
  Must be a multiple of 4 in `[0, 16380]` for `.W32` and a multiple of 8 in
  `[0, 32760]` for `.W64`.
- **Signed unscaled offset (`allowUnscaled = true`)**: Must be in `[-256, 255]`.
-/
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

/-- Validate an unscaled 9-bit signed immediate byte offset for `LDUR`/`STUR` (`[-256, 255]`). -/
def checkUnscaledOffset (imm : Int64) : Except String Unit :=
  if imm.toInt < -256 || imm.toInt > 255 then
    .error s!"unscaled offset {imm.toInt} out of range [-256, 255]"
  else .ok ()

/--
Determine whether a load/store immediate address (`AddrExpr`) requires
automatic conversion to an unscaled `LDUR`/`STUR` instruction (i.e. when the
offset is negative or not aligned to the access size).
-/
def addrExprNeedsUnscaled {w : Width} (addr : AddrExpr w) : Bool :=
  match addr.off with
  | .imm i =>
    match i.index, i.imm with
    | none, .int64 imm =>
      let (_, align) := match w with | .W32 => (16380, 4) | .W64 => (32760, 8)
      imm.toInt < 0 || imm.toInt % align != 0
    | _, _ => false
  | _ => false

/--
Determine whether an `AddrOrLit` load operand requires conversion to an
unscaled instruction.
-/
def addrOrLitNeedsUnscaled {w : Width} (a : AddrOrLit w) : Bool :=
  match a with
  | .addr addr => addrExprNeedsUnscaled addr
  | .lit _ => false

/--
Convert a standard immediate address expression (`AddrExpr`) to an unscaled
address expression (`UnscaledAddrExpr`).
-/
def addrExprToUnscaled {w : Width} (addr : AddrExpr w) : Option UnscaledAddrExpr :=
  match addr.off with
  | .imm i =>
    match i.index with
    | none => some { base := addr.base, imm := i.imm }
    | some _ => none
  | _ => none

/-- Convert an `AddrOrLit` operand to an unscaled address expression (`UnscaledAddrExpr`). -/
def addrOrLitToUnscaled {w : Width} (a : AddrOrLit w) : Option UnscaledAddrExpr :=
  match a with
  | .addr addr => addrExprToUnscaled addr
  | .lit _ => none

/--
Validate an optional shift amount for register operands:
- Must be in `[0, 31]` for 32-bit instructions (`.W32`).
- Must be in `[0, 63]` for 64-bit instructions (`.W64`).
-/
def checkShiftAmount (w : Width) (amt : Int64) : Except String Unit :=
  let maxAmt := match w with | .W32 => 31 | .W64 => 63
  if amt.toInt < 0 || amt.toInt > maxAmt then
    .error s!"shift amount {amt.toInt} out of range [0, {maxAmt}] for {w.bits}-bit instruction"
  else .ok ()

/--
Validate a signed immediate byte offset for load/store pair instructions (`LDP`/`STP`):
- For `.W32`: Multiple of 4 in `[-256, 252]`.
- For `.W64`: Multiple of 8 in `[-512, 504]`.
-/
def checkPairOffset (w : Width) (imm : Int64) : Except String Unit :=
  let (minOff, maxOff, align) := match w with | .W32 => (-256, 252, 4) | .W64 => (-512, 504, 8)
  if imm.toInt < minOff || imm.toInt > maxOff || imm.toInt % align != 0 then
    .error s!"pair offset {imm.toInt} out of range [{minOff}, {maxOff}] or not a multiple of {align}"
  else .ok ()

def intToHexStr (n : Int) : String :=
  if n < 0 then s!"-0x{String.ofList (Nat.toDigits 16 (-n).natAbs)}"
  else s!"0x{String.ofList (Nat.toDigits 16 n.natAbs)}"

/--
Validate a PC-relative byte offset for `ADR`.
- Must be a 21-bit signed integer in `[-0x100000, 0xfffff]` (`±1 MB`).
-/
def checkAdrOffset (offset : Int64) : Except String Unit :=
  let val := offset.toInt
  if val < -0x100000 || val > 0xfffff then
    .error s!"adr offset {intToHexStr val} out of range [-0x100000, 0xfffff]"
  else .ok ()

/--
Check whether an `E`-bit unsigned integer consists of a non-empty contiguous
run of ones starting from bit 0 (`2^k - 1` for `0 < k < E`).
-/
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

/--
Determine whether an `E`-bit number (`0 < elem < 2^E - 1`) is a rotated
contiguous run of ones, as required by ARMv8-A logical immediate encoding.
-/
def isRotatedRunOfOnes (elem : Nat) (E : Nat) : Bool :=
  isRotatedRunOfOnesAux elem E E

/--
Replicate an `E`-bit pattern across an entire `wBits`-wide integer
(`wBits = 32` or `64`, `E ∈ {2, 4, 8, 16, 32, 64}`).
-/
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

/--
Check whether an integer value is formed by repeating its low `E`-bit pattern
across the entire `wBits` width.
-/
def isRepeatedPattern (val : Nat) (wBits : Nat) (E : Nat) : Bool :=
  let pattern := val &&& ((1 <<< E) - 1)
  val == repeatElement pattern wBits E

/--
Determine whether a 32-bit or 64-bit value is a valid ARMv8-A bitmask immediate
for logical instructions (`AND`, `ORR`, `EOR`, `TST`).
- Excludes all-zeros and all-ones values.
- Checks for a repeated rotated run of ones across allowed element sizes `E`.
-/
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

/--
Validate an ARMv8-A bitmask immediate for logical instructions
(`AND`, `ORR`, `EOR`).
- Enforces repeated rotated runs of ones across element sizes
  (2, 4, 8, 16, 32, 64 bits).
- Rejects all-zeros or all-ones bitmasks (`invalid logical immediate: <hex>`).
-/
def checkLogicalImmediate (w : Width) (imm : Int64) : Except String Unit :=
  if isValidLogicalImmediate w imm then
    .ok ()
  else
    .error s!"invalid logical immediate: {intToHexStr imm.toInt}"

/--
Validate a PC-relative page offset for `ADRP`:
- Must be 4 KB page aligned (multiple of `0x1000`).
- Page offset (`offset / 4096`) must fit in a 21-bit signed integer
  (`[-0x100000, 0xfffff]`).
-/
def checkAdrpOffset (offset : Int64) : Except String Unit :=
  let val := offset.toInt
  if val % 0x1000 != 0 then
    .error s!"adrp offset {intToHexStr val} not page aligned (must be multiple of 0x1000)"
  else
    let page_offset := val / 0x1000
    if page_offset < -0x100000 || page_offset > 0xfffff then
      .error s!"adrp offset {intToHexStr val} out of range [-0x100000000, 0xfffff000]"
    else .ok ()

/--
Validate a 26-bit signed word offset for unconditional branch (`B` / `BL`):
- Must be in `[-0x8000000, 0x7fffffc]` (`±128 MB`, multiple of 4).
-/
def checkBOffset (offset : Int64) : Except String Unit :=
  let val := offset.toInt
  if val < -0x8000000 || val > 0x7fffffc then
    .error s!"b offset {intToHexStr val} out of range [-0x8000000, 0x7fffffc]"
  else .ok ()

/--
Validate a 19-bit signed word offset for conditional branch (`B.cond`):
- Must be in `[-0x100000, 0xffffc]` (`±1 MB`, multiple of 4).
-/
def checkBCondOffset (offset : Int64) : Except String Unit :=
  let val := offset.toInt
  if val < -0x100000 || val > 0xffffc then
    .error s!"b.cond offset {intToHexStr val} out of range [-0x100000, 0xffffc]"
  else .ok ()

/--
Validate a 19-bit signed word offset for compare-and-branch (`CBZ` / `CBNZ`):
- Must be in `[-0x100000, 0xffffc]` (`±1 MB`) and a multiple of 4.
-/
def checkCbzOffset (instrName : String) (offset : Int64) : Except String Unit :=
  let val := offset.toInt
  if val < -0x100000 || val > 0xffffc || val % 4 != 0 then
    .error s!"{instrName} offset {intToHexStr val} out of range [-0x100000, 0xffffc] or not a multiple of 4"
  else .ok ()

/--
Validate a 14-bit signed word offset for test-bit-and-branch (`TBZ` / `TBNZ`):
- Must be in `[-0x8000, 0x7fc]` (`±32 KB`) and a multiple of 4.
-/
def checkTbzOffset (instrName : String) (offset : Int64) : Except String Unit :=
  let val := offset.toInt
  if val < -0x8000 || val > 0x7fc || val % 4 != 0 then
    .error s!"{instrName} offset {intToHexStr val} out of range [-0x8000, 0x7fc] or not a multiple of 4"
  else .ok ()

/--
Validate a bit test position for `TBZ` / `TBNZ`:
- Must be in `[0, 31]` for `.W32` and `[0, 63]` for `.W64`.
-/
def checkTbzBitPosition (instrName : String) (w : Width) (bit : Nat) : Except String Unit :=
  let maxBit := match w with | .W32 => 31 | .W64 => 63
  if bit > maxBit then
    .error s!"{instrName} bit position {bit} out of range [0, {maxBit}] for {w.bits}-bit instruction"
  else .ok ()

/--
Validate that an immediate shift amount, bit position, or rotate/size index
is within `[0, w.bits - 1]`.
-/
def checkBitWidthBound (instrName : String) (w : Width) (imm : Nat) : Except String Unit :=
  let maxVal := w.bits - 1
  if imm > maxVal then
    .error s!"{instrName} immediate {imm} out of range [0, {maxVal}]"
  else .ok ()

/--
Validate bitfield extract/insert bounds (`lsb < w.bits`, `width > 0`, and
`lsb + width <= w.bits`).
-/
def checkBitfieldBounds (instrName : String) (w : Width) (lsb width : Nat) : Except String Unit :=
  if lsb >= w.bits || width == 0 || lsb + width > w.bits then
    .error s!"{instrName} bounds invalid: lsb={lsb}, width={width}, w={w.bits}"
  else .ok ()

/-- Validate conditional compare (`CCMP`/`CCMN`) immediate operand (`[0, 31]`). -/
def checkCcmpImmediate (imm : Nat) : Except String Unit :=
  if imm > 31 then
    .error s!"ccmp/ccmn immediate {imm} out of range [0, 31]"
  else .ok ()

/-- Validate NZCV condition flags immediate operand (`[0, 15]`). -/
def checkNzcvFlags (nzcv : Nat) : Except String Unit :=
  if nzcv > 15 then
    .error s!"nzcv immediate {nzcv} out of range [0, 15]"
  else .ok ()

/-- Validate a 12-bit unsigned arithmetic immediate (for ADD/SUB immediate operands). -/
def checkArithmeticImmediate (imm : Int64) : Except String Unit :=
  if imm.toInt < 0 || imm.toInt > 4095 then
    .error s!"immediate {imm.toInt} out of range [0, 4095]"
  else .ok ()

/--
Validate architectural constraints for `LDP` and `STP` instructions:
1. For `LDP`, `rt1` and `rt2` cannot be identical unless they are `XZR`/`WZR`.
2. If writeback (`!` pre-index or post-index) is used, the base register (`Rn`)
   cannot be one of the transfer registers (`rt1` or `rt2`).
-/
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

/--
Parse memory addressing operands for general load/store instructions
(`LDR` / `STR`).
Supports the following AArch64 addressing modes:
1. **Base-only / Post-indexed**: `[base]` or `[base], #imm`
2. **Immediate / Pre-indexed**: `[base, #imm]`, `[base, #imm]!`, or
   `[base, #:lo12:label]`
3. **Register offset with optional extension/shift**: `[base, Rm]` or
   `[base, Rm, ext #amount]`
-/
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
        let amt ← if c? == some '#' || c? == some '-' || (c?.map Char.isDigit).getD false then
          parseImmNat
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

/--
Parse unscaled immediate memory addressing (`[base]` or `[base, #imm]`) for
`LDUR` / `STUR`.
- Enforces that `#imm` is a 9-bit signed integer in `[-256, 255]`.
-/
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

/--
Parse a memory source operand for `LDR`:
- Standard address expression (`[base, ...]`).
- PC-relative literal pool constant (`=const_expr`).
- PC-relative symbol label (`label`).
-/
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

/--
Parse memory addressing for load/store pair (`LDP` / `STP`):
- Supports base-only (`[base]`), immediate offset (`[base, #imm]`),
  pre-indexed (`[base, #imm]!`), and post-indexed (`[base], #imm`).
- Enforces pair offset scaling and alignment via `checkPairOffset`.
-/
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

/--
Parse an optional extend shift amount (`#0` to `#4`) after an extend suffix.
- Defaults to `E0` (`#0`) if omitted.
-/
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

/--
Validate and map an arithmetic extension mnemonic (`UXTB`, `SXTB`, `UXTH`,
`SXTH`, `UXTW`, `SXTW`, `UXTX`, `SXTX`, `LSL`).
- Maps `LSL` to `UXTX` for `.W64` and `UXTW` for `.W32`.
-/
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

/--
Parse the second source operand of an `ADD_e` instruction
(`add dst, src1, src2`).
`src2` can either be:
1. **Immediate operand**: `#imm` or `#imm, lsl #12` (or a relocation modifier
   `:lo12:label` with no shift).
2. **Extended/shifted register operand**: `Rm` or `Rm, ext #amount`
   (e.g. `x2, uxtw #2` or `x2, lsl #2`).
-/
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
        let amt ← parseImmNat
        match expr with
        | .int64 imm =>
          liftExcept (checkArithmeticImmediate imm)
          if amt == 12 then
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
        liftExcept (checkArithmeticImmediate imm)
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

/--
Parse a shifted register operand (`Rm` or `Rm, shift #amount`).
- Supports `LSL`, `LSR`, `ASR`, and optionally `ROR` (if `allowRor = true`).
- Enforces shift amount bounds (`[0, 31]` for `.W32`, `[0, 63]` for `.W64`).
- Rejects `ROR` in arithmetic instructions.
-/
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

/--
Check if the parser is positioned at horizontal whitespace followed by line
end, EOF, or comment.
If a comment is present, it is consumed up to the newline.
-/
def isAtLineEndOrComment : Parser Bool := do
  skipHWs
  let c? ← peek?
  match c? with
  | none | some '\n' =>
    pure true
  | _ =>
    (attempt skipTrailingComment *> pure true) <|> pure false

/--
Parse an optional operand using `p`, or return `defaultVal` if positioned at
line end or comment.
-/
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

/-- Parse a condition code operand (`cond`). -/
def parseCondArg : Parser CondCode := do
  skipHWs
  let name ← parseName
  match parseCondCode name with
  | some c => pure c
  | none => fail s!"unknown condition code: {name}"

-- ============================================================================
-- Instruction Parsing Helpers
-- ============================================================================

/--
Parse arithmetic instructions without flags (`ADD`, `SUB`).
- Supports both extended-register (`_e`: `ADD SP, SP, X0`) and shifted-register
  (`_s`: `ADD X0, X1, X2, lsl #2`) forms.
- Handles stack pointer (`SP`) disambiguation for operand index 31.
-/
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

/--
Parse arithmetic instructions that set flags (`ADDS`, `SUBS`).
- Rejects `SP` / `WSP` as destination register.
- Supports both extended-register (`_e`) and shifted-register (`_s`) forms.
-/
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

/--
Parse comparison instructions (`CMP`, `CMN`).
- Models them architecturally as `SUBS` / `ADDS` with destination hardcoded to
  `XZR` / `WZR`.
-/
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

/--
Parse three-register instructions (`ADC`, `SBC`, `LSLV`, `LSRV`, `ASRV`,
`RORV`).
- Enforces matching register widths across all three operands.
-/
def parseThreeRegs
    (mk : {w : Width} → RegOrZr w → RegOrZr w → RegOrZr w → Operation w) : Parser Instr := do
  let dstW ← parseRegOrZrW
  let w := dstW.w
  parseComma
  let src1 ← parseRegOrZr w
  parseComma
  let src2 ← parseRegOrZr w
  pure ⟨w, mk dstW.reg src1 src2⟩

/--
Parse four-register multiply-accumulate instructions (`MADD`, `MSUB`).
- Enforces matching register widths across all four operands (`dst, rn, rm, ra`).
-/
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

/--
Parse logical instructions without flags (`AND`, `ORR`, `EOR`).
- Supports immediate bitmask (`_i`: `#imm`) and shifted-register (`_s`,
  including `ROR`) forms.
- Validates bitmasks.
-/
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

/--
Parse logical instructions that set flags (`ANDS`, `TST`).
- `TST` is modeled architecturally as `ANDS` with destination `XZR` / `WZR`.
-/
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

/--
Parse register-only logical instructions (`ORN`, `BIC`).
- Supports shifted-register operands (including `ROR`).
-/
def parseLogical
    (mkS : {w : Width} → RegOrZr w → RegOrZr w → ShiftRegExpr w → Operation w) : Parser Instr := do
  let dstW ← parseRegOrZrW
  let w := dstW.w
  parseComma
  let src1 ← parseRegOrZr w
  parseComma
  let shiftOp ← parseShiftRegExpr w true
  pure ⟨w, mkS dstW.reg src1 shiftOp⟩

/-- Parse conditional select instructions (`CSEL`, `CSINC`, `CSINV`, `CSNEG`). -/
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

/--
Parse conditional select alias instructions (`CSET`, `CSETM`, `CNEG`).
- `CSET dst, cond` maps to `CSINC dst, xzr, xzr, cond.invert`.
- `CSETM dst, cond` maps to `CSINV dst, xzr, xzr, cond.invert`.
- `CNEG dst, src, cond` maps to `CSNEG dst, src, src, cond.invert`.
-/
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

/--
Check whether an unsigned bit vector value can be moved into a register using
a single `MOVZ` instruction (i.e., it has at most one non-zero 16-bit halfword).
- Returns `(imm16, shift)` for `LSL0`, `LSL16`, `LSL32`, or `LSL48`.
-/
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

/--
Check whether a bit vector value can be moved using a single `MOVZ` or `MOVN`
instruction.
- First tries `MOVZ` on `val`.
- If that fails, tries `MOVZ` on the bitwise NOT (`~~~val`), which maps to `MOVN`.
- Returns `(isMovn, imm16, shift)`.
-/
def tryMovzOrMovn (w : Width) (val : BitVec w.bits) : Option (Bool × Int64 × MovShift w) :=
  match tryMovz w val with
  | some (imm16, shift) => some (false, imm16, shift)
  | none =>
    let invVal := ~~~val
    match tryMovz w invVal with
    | some (imm16, shift) => some (true, imm16, shift)
    | none => none

/--
Parse flexible `MOV` alias instructions (`MOV dst, src` or `MOV dst, #imm`).
- For register moves:
  - Maps to `ADD_e dstSp, srcSp, #0` if either operand is `SP`/`WSP`.
  - Maps to `ORR_s dstZr, xzr, srcZr` for general-purpose registers.
- For immediate moves (`MOV dst, #imm`):
  - Automatically selects `MOVZ`, `MOVN`, or bitwise `ORR_i` depending on encoding.
  - Fails if the immediate cannot be encoded in a single instruction.
-/
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

/--
Parse `MVN` (Move NOT) alias instructions (`MVN dst, src`).
- Maps architecturally to `ORN dst, xzr, src` with an optional shift.
-/
def parseMvn : Parser Instr := do
  let dstW ← parseRegOrZrW
  let w := dstW.w
  parseComma
  let shiftOp ← parseShiftRegExpr w true
  pure ⟨w, .ORN_s dstW.reg (.low .XZR w) shiftOp⟩

/--
Parse move wide instructions (`MOVZ`, `MOVK`, `MOVN`) with explicit
16-bit immediates and optional `LSL` shift (`#0`, `#16`, `#32`, `#48`).
- Enforces immediate range `[0, 65535]` and only allows `LSL` shifts.
-/
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

/--
Parse load/store pair instructions (`LDP`, `STP`).
- Syntax: `ldp reg1, reg2, [base, #imm]`.
- Validates registers and pair addressing mode via `checkLdpStpRegisters`.
-/
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

/--
Parse instructions that take three 64-bit general-purpose register operands
(`X0`-`X30`), such as `SMULH` and `UMULH`.
-/
def parseThreeRegsW64
    (mk : RegOrZr .W64 → RegOrZr .W64 → RegOrZr .W64 → Operation .W64) : Parser Instr := do
  let dst ← parseRegOrZr .W64
  parseComma
  let src1 ← parseRegOrZr .W64
  parseComma
  let src2 ← parseRegOrZr .W64
  pure ⟨.W64, mk dst src1 src2⟩

/--
Parse 3-register alias instructions that map to 4-register operations with
`XZR`/`WZR` as the implicit fourth register operand (e.g. `MUL dst, src1, src2`
as `MADD dst, src1, src2, xzr`).
-/
def parseThreeRegsWithZr
    (mk : {w : Width} → RegOrZr w → RegOrZr w → RegOrZr w → RegOrZr w → Operation w) : Parser Instr := do
  let dstW ← parseRegOrZrW
  let w := dstW.w
  parseComma
  let src1 ← parseRegOrZr w
  parseComma
  let src2 ← parseRegOrZr w
  pure ⟨w, mk dstW.reg src1 src2 (.low .XZR w)⟩

/--
Parse negation alias instructions (`NEG dst, src` or `NEGS dst, src`).
- Maps architecturally to `SUB dst, xzr, src` or `SUBS dst, xzr, src` with an optional shift.
-/
def parseNegAlias
    (mk : {w : Width} → RegOrZr w → RegOrZr w → ShiftRegExpr w → Operation w) : Parser Instr := do
  let dstW ← parseRegOrZrW
  let w := dstW.w
  parseComma
  let src ← parseRegOrZr w
  pure ⟨w, mk dstW.reg (.low .XZR w) { reg := src, amount := 0, shift := .LSL }⟩

/--
Parse `TST` (Test bits and set flags) alias instructions (`TST src1, src2`
or `TST src1, #imm`).
- Maps architecturally to `ANDS xzr, src1, src2` (register/shifted) or
  `ANDS_i xzr, src1, #imm` (immediate).
-/
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

/--
Parse PC-relative address calculation instructions (`ADR`, `ADRP`).
- Validates offset alignment and bounds via `checkOffset`
  (`checkAdrOffset` / `checkAdrpOffset`).
-/
def parseAdr (checkOffset : Int64 → Except String Unit)
    (mk : RegOrZr .W64 → ConstExpr → Operation .W64) : Parser Instr := do
  let dst ← parseRegOrZr .W64
  parseComma
  let target ← parseConstExpr
  if let .int64 imm := target then
    liftExcept (checkOffset imm)
  pure ⟨.W64, mk dst target⟩

/--
Parse unconditional relative branches (`B`, `BL`).
- Enforces 26-bit signed word offset limits (`±128 MB`).
-/
def parseBranch (mk : ConstExpr → Operation .W64) : Parser Instr := do
  let target ← parseConstExpr
  if let .int64 imm := target then
    liftExcept (checkBOffset imm)
  pure ⟨.W64, mk target⟩

/-- Parse indirect branches via register (`BLR`, `BR`). -/
def parseBranchReg (mk : RegOrZr .W64 → Operation .W64) : Parser Instr := do
  let target ← parseRegOrZr .W64
  pure ⟨.W64, mk target⟩

/--
Parse compare-and-branch instructions (`CBZ`, `CBNZ`).
- Syntax: `cbz reg, target`.
- Validates 19-bit signed word target offset (`±1 MB`).
-/
def parseCbz (name : String)
    (mk : {w : Width} → RegOrZr w → ConstExpr → Operation w) : Parser Instr := do
  let regW ← parseRegOrZrW
  parseComma
  let target ← parseConstExpr
  if let .int64 imm := target then
    liftExcept (checkCbzOffset name imm)
  pure ⟨regW.w, mk regW.reg target⟩

/--
Parse test-bit-and-branch instructions (`TBZ`, `TBNZ`).
- Syntax: `tbz reg, #bit, target`.
- Enforces bit position bounds (`[0, 31]` for `.W32`, `[0, 63]` for `.W64`)
  and 14-bit signed word target offset (`±32 KB`).
-/
def parseTbz (name : String)
    (mk : {w : Width} → RegOrZr w → Nat → ConstExpr → Operation w) : Parser Instr := do
  let regW ← parseRegOrZrW
  parseComma
  let bit ← parseImmNat
  liftExcept (checkTbzBitPosition name regW.w bit)
  parseComma
  let target ← parseConstExpr
  if let .int64 imm := target then
    liftExcept (checkTbzOffset name imm)
  pure ⟨regW.w, mk regW.reg bit target⟩

/--
Parse instructions that take two general-purpose register operands of the same
width (`CLZ`, `CLS`, `RBIT`, `REV`, `REV16`).
-/
def parseTwoRegs (mk : {w : Width} → RegOrZr w → RegOrZr w → Operation w) : Parser Instr := do
  let dstW ← parseRegOrZrW
  let w := dstW.w
  parseComma
  let src ← parseRegOrZr w
  pure ⟨w, mk dstW.reg src⟩

/--
Parse instructions that take two 64-bit general-purpose register operands
(`X0`-`X30`), such as `REV32` and `REV64`.
-/
def parseTwoRegsW64 (mk : RegOrZr .W64 → RegOrZr .W64 → Operation .W64) : Parser Instr := do
  let dst ← parseRegOrZr .W64
  parseComma
  let src ← parseRegOrZr .W64
  pure ⟨.W64, mk dst src⟩

/--
Parse long multiply-accumulate and multiply-subtract instructions (`SMADDL`,
`UMADDL`, `SMSUBL`, `UMSUBL`).
- Takes a 64-bit destination register, two 32-bit source registers, and a 64-bit
  addend/subtrahend register.
-/
def parseFourRegsLong
    (mk : RegOrZr .W64 → RegOrZr .W32 → RegOrZr .W32 → RegOrZr .W64 → Operation .W64) : Parser Instr := do
  let dst ← parseRegOrZr .W64
  parseComma
  let src1 ← parseRegOrZr .W32
  parseComma
  let src2 ← parseRegOrZr .W32
  parseComma
  let src3 ← parseRegOrZr .W64
  pure ⟨.W64, mk dst src1 src2 src3⟩

/--
Parse 3-register long multiply alias instructions (`SMULL`, `UMULL`, `SMNEGL`, `UMNEGL`).
- Maps architecturally to 4-register long operations (`SMADDL`, `UMADDL`, `SMSUBL`, `UMSUBL`)
  with `XZR` as the implicit fourth register operand.
-/
def parseThreeRegsLongWithZr
    (mk : RegOrZr .W64 → RegOrZr .W32 → RegOrZr .W32 → RegOrZr .W64 → Operation .W64) : Parser Instr := do
  let dst ← parseRegOrZr .W64
  parseComma
  let src1 ← parseRegOrZr .W32
  parseComma
  let src2 ← parseRegOrZr .W32
  pure ⟨.W64, mk dst src1 src2 (.low .XZR .W64)⟩

/--
Parse shift alias instructions (`LSL`, `LSR`, `ASR`, `ROR`) with either an
immediate shift amount or a register shift amount.
- Immediate shifts map architecturally to bitfield operations (`UBFM`, `SBFM`, `EXTR`).
- Register shifts map to variable shift instructions (`LSLV`, `LSRV`, `ASRV`, `RORV`).
-/
def parseShiftAlias (regOp : {w : Width} → RegOrZr w → RegOrZr w → RegOrZr w → Operation w)
    (immOp : {w : Width} → RegOrZr w → RegOrZr w → Nat → Operation w) : Parser Instr := do
  let dstW ← parseRegOrZrW
  let w := dstW.w
  parseComma
  let src1 ← parseRegOrZr w
  parseComma
  let nextC ← peek!
  if nextC == '#' || nextC.isDigit || nextC == '-' || nextC == '+' then
    let imm ← parseImmNat
    liftExcept (checkBitWidthBound "shift" w imm)
    pure ⟨w, immOp dstW.reg src1 imm⟩
  else
    let src2 ← parseRegOrZr w
    pure ⟨w, regOp dstW.reg src1 src2⟩

/--
Parse extract register instructions (`EXTR`).
- Syntax: `extr dst, src1, src2, #lsb`.
- Validates that the least significant bit (`lsb`) immediate is in range `[0, w.bits - 1]`.
-/
def parseExtr : Parser Instr := do
  let dstW ← parseRegOrZrW
  let w := dstW.w
  parseComma
  let src1 ← parseRegOrZr w
  parseComma
  let src2 ← parseRegOrZr w
  parseComma
  let lsb ← parseImmNat
  liftExcept (checkBitWidthBound "extr" w lsb)
  pure ⟨w, .EXTR dstW.reg src1 src2 lsb⟩

/--
Parse bitfield move instructions (`BFM`, `SBFM`, `UBFM`).
- Syntax: `bfm dst, src, #immr, #imms`.
- Validates that rotate (`immr`) and size (`imms`) immediates are within bounds `[0, w.bits - 1]`.
-/
def parseBitfield (mk : {w : Width} → RegOrZr w → RegOrZr w → Nat → Nat → Operation w) : Parser Instr := do
  let dstW ← parseRegOrZrW
  let w := dstW.w
  parseComma
  let src ← parseRegOrZr w
  parseComma
  let immr ← parseImmNat
  parseComma
  let imms ← parseImmNat
  liftExcept (checkBitWidthBound "bitfield" w immr)
  liftExcept (checkBitWidthBound "bitfield" w imms)
  pure ⟨w, mk dstW.reg src immr imms⟩

/--
Parse bitfield extract and insert-low alias instructions (`SBFX`, `UBFX`, `BFXIL`).
- Syntax: `sbfx dst, src, #lsb, #width`.
- Validates bounds (`width > 0` and `lsb + width <= w.bits`) and converts `lsb` and
  `width` to bitfield operands (`immr = lsb`, `imms = lsb + width - 1`).
-/
def parseBitfieldExtract (mk : {w : Width} → RegOrZr w → RegOrZr w → Nat → Nat → Operation w) : Parser Instr := do
  let dstW ← parseRegOrZrW
  let w := dstW.w
  parseComma
  let src ← parseRegOrZr w
  parseComma
  let lsb ← parseImmNat
  parseComma
  let width ← parseImmNat
  liftExcept (checkBitfieldBounds "bitfield extract" w lsb width)
  let immr := lsb
  let imms := lsb + width - 1
  pure ⟨w, mk dstW.reg src immr imms⟩

/--
Parse bitfield insert alias instructions (`BFI`, `SBFIZ`, `UBFIZ`).
- Syntax: `bfi dst, src, #lsb, #width`.
- Validates bounds (`width > 0` and `lsb + width <= w.bits`) and maps `lsb` and `width`
  to rotate and size operands (`immr = (w.bits - lsb) % w.bits`, `imms = width - 1`).
-/
def parseBitfieldInsert (mk : {w : Width} → RegOrZr w → RegOrZr w → Nat → Nat → Operation w) : Parser Instr := do
  let dstW ← parseRegOrZrW
  let w := dstW.w
  parseComma
  let src ← parseRegOrZr w
  parseComma
  let lsb ← parseImmNat
  parseComma
  let width ← parseImmNat
  liftExcept (checkBitfieldBounds "bitfield insert" w lsb width)
  let immr := (w.bits - lsb) % w.bits
  let imms := width - 1
  pure ⟨w, mk dstW.reg src immr imms⟩

/--
Parse sign-extend and zero-extend alias instructions (`SXTB`, `SXTH`, `SXTW`, `UXTB`, `UXTH`, `UXTW`).
- Maps architecturally to signed or unsigned bitfield moves (`SBFM` or `UBFM`) with
  `immr = 0` and fixed `imms` corresponding to the source byte, halfword, or word size.
-/
def parseExtendInstr (mk : {w : Width} → RegOrZr w → RegOrZr w → Nat → Nat → Operation w) (imms : Nat) : Parser Instr := do
  let dstW ← parseRegOrZrW
  parseComma
  let srcW ← parseRegOrZrW
  let src : RegOrZr dstW.w := match srcW.reg with
    | .low r _ => .low r dstW.w
  pure ⟨dstW.w, mk dstW.reg src 0 imms⟩

/--
Parse conditional compare instructions (`CCMP`, `CCMN`) with either a register
or immediate second operand.
- Syntax: `ccmp src1, src2|#imm, #nzcv, cond`.
- Validates that `#imm` is in range `[0, 31]` and `#nzcv` flags immediate is in range `[0, 15]`.
-/
def parseCondCompare
    (mkReg : {w : Width} → RegOrZr w → RegOrZr w → Nat → CondCode → Operation w)
    (mkImm : {w : Width} → RegOrZr w → Nat → Nat → CondCode → Operation w) : Parser Instr := do
  let src1W ← parseRegOrZrW
  let w := src1W.w
  parseComma
  let nextC ← peek!
  if nextC == '#' || nextC.isDigit || nextC == '-' || nextC == '+' then
    let imm ← parseImmNat
    liftExcept (checkCcmpImmediate imm)
    parseComma
    let nzcv ← parseImmNat
    liftExcept (checkNzcvFlags nzcv)
    parseComma
    let cond ← parseCondArg
    pure ⟨w, mkImm src1W.reg imm nzcv cond⟩
  else
    let src2 ← parseRegOrZr w
    parseComma
    let nzcv ← parseImmNat
    liftExcept (checkNzcvFlags nzcv)
    parseComma
    let cond ← parseCondArg
    pure ⟨w, mkReg src1W.reg src2 nzcv cond⟩

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
  | "sdiv"  => parseThreeRegs .SDIV
  | "udiv"  => parseThreeRegs .UDIV
  | "smaddl" => parseFourRegsLong .SMADDL
  | "umaddl" => parseFourRegsLong .UMADDL
  | "smsubl" => parseFourRegsLong .SMSUBL
  | "umsubl" => parseFourRegsLong .UMSUBL
  | "smull" => parseThreeRegsLongWithZr .SMADDL
  | "umull" => parseThreeRegsLongWithZr .UMADDL
  | "smnegl" => parseThreeRegsLongWithZr .SMSUBL
  | "umnegl" => parseThreeRegsLongWithZr .UMSUBL

  | "and"   => parseLogicalNoFlags .AND_i .AND_s
  | "ands"  => parseLogicalFlags .ANDS_i .ANDS_s
  | "orr"   => parseLogicalNoFlags .ORR_i .ORR_s
  | "orn"   => parseLogical .ORN_s
  | "eor"   => parseLogicalNoFlags .EOR_i .EOR_s
  | "bic"   => parseLogical .BIC_s
  | "eon"   => parseLogical .EON_s
  | "bics"  => parseLogical .BICS_s
  | "tst"   => parseTstAlias

  | "bfm"   => parseBitfield .BFM
  | "sbfm"  => parseBitfield .SBFM
  | "ubfm"  => parseBitfield .UBFM
  | "sbfx"  => parseBitfieldExtract .SBFM
  | "ubfx"  => parseBitfieldExtract .UBFM
  | "bfxil" => parseBitfieldExtract .BFM
  | "bfi"   => parseBitfieldInsert .BFM
  | "sbfiz" => parseBitfieldInsert .SBFM
  | "ubfiz" => parseBitfieldInsert .UBFM
  | "sxtb"  => parseExtendInstr .SBFM 7
  | "sxth"  => parseExtendInstr .SBFM 15
  | "sxtw"  => parseExtendInstr .SBFM 31
  | "uxtb"  => parseExtendInstr .UBFM 7
  | "uxth"  => parseExtendInstr .UBFM 15
  | "uxtw"  => parseExtendInstr .UBFM 31

  | "clz"   => parseTwoRegs .CLZ
  | "cls"   => parseTwoRegs .CLS
  | "rbit"  => parseTwoRegs .RBIT
  | "rev"   => parseTwoRegs .REV
  | "rev16" => parseTwoRegs .REV16
  | "rev32" => parseTwoRegsW64 .REV32
  | "rev64" => parseTwoRegsW64 .REV
  | "extr"  => parseExtr

  | "lsl"   => parseShiftAlias .LSLV (fun {w} dst src imm => .UBFM dst src ((w.bits - imm) % w.bits) (w.bits - 1 - imm))
  | "lsr"   => parseShiftAlias .LSRV (fun {w} dst src imm => .UBFM dst src imm (w.bits - 1))
  | "asr"   => parseShiftAlias .ASRV (fun {w} dst src imm => .SBFM dst src imm (w.bits - 1))
  | "ror"   => parseShiftAlias .RORV (fun dst src imm => .EXTR dst src src imm)
  | "lslv"  => parseThreeRegs .LSLV
  | "lsrv"  => parseThreeRegs .LSRV
  | "asrv"  => parseThreeRegs .ASRV
  | "rorv"  => parseThreeRegs .RORV

  | "ccmp"  => parseCondCompare .CCMP_reg .CCMP_imm
  | "ccmn"  => parseCondCompare .CCMN_reg .CCMN_imm

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

/--
Parse an optional symbol label declaration (name followed by `:`).
- Uses `attempt` for clean backtracking if `:` is not found after the name.
-/
def parseLabelDecl : Parser Label := do
  skipHWs
  attempt do
    let name ← parseName
    skipHWs
    let _ ← pchar ':'
    pure name

/--
Parse an optional instruction on the current line, returning `none` if at
line end or comment.
-/
def parseOptionalInstr : Parser (Option Directive) := do
  if (← isAtLineEndOrComment) then
    pure none
  else
    let i ← parseInstr
    pure (some (Directive.instr i))

/--
Verify that no unexpected trailing characters remain on the line after
parsing operands/instructions.
- Fails with `unexpected trailing characters on line` if extra tokens exist.
-/
def checkLineEnd : Parser Unit := do
  if (← isAtLineEndOrComment) then
    pure ()
  else
    fail "unexpected trailing characters on line"

/--
Parse a single assembly line:
- Zero or more label declarations (`label:`).
- Optional instruction (`ldr x0, [sp]`).
- Optional comment (`# comment` or `// comment`).
- Returns the list of AST directives (`Directive.label`, `Directive.instr`)
  found on the line.
-/
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
