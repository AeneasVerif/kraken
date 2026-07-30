/-
Kraken Parser - x86_64 AT&T Assembly Parser

Parses AT&T syntax assembly strings into Kraken's Program type.
Uses Lean's built-in Std.Internal.Parsec library.

The primary reference for the syntax is the GAS manual:
https://sourceware.org/binutils/docs/as/
-/

import Kraken.X64.Syntax
import Std.Internal.Parsec.String

namespace Kraken.X64.Parser

open Std.Internal.Parsec
open Std.Internal.Parsec.String

-- ============================================================================
-- Data structures for type inference
-- ============================================================================

-- We need to eagerly parse (to move through the syntax), but we may need to
-- defer choosing a width for those operands that are untyped (as in: may have
-- any width).
def MaybeOpWidth (T: Width → Type) :=
  Σ (w: Option Width), match w with | .some w => T w | .none => { w: Width } → T w

def MaybeAvxOpWidth (T: AvxWidth → Type) :=
  Σ (w: Option AvxWidth), match w with | .some w => T w | .none => { w: AvxWidth } → T w

-- Most of our parsing functions return a MaybeAddrWidth × MaybeTyped T, in case
-- the operand we just parsed happens to be a memory operand, which thus allows
-- the assembler to infer the address width used for the instruction (see
-- comments in Syntax).
abbrev MaybeAddrWidth := Option Width

-- This could be Option.mergeM if it existed.
--
-- No x86 assembly instructions take two memory operands: this means that we
-- have at most one address width hint per instruction.
def mergeAddrWidths (w1 w2: MaybeAddrWidth): Parser MaybeAddrWidth :=
  match w1, w2 with
  | .none, .none => pure .none
  | .some w1, .none
  | .none, .some w1 => pure (.some w1)
  | .some _, .some _ => fail "can't have two memory operands"

-- If the context provides a type annotation, this forces a given width, or
-- errors out if an incompatible one has been inferred.
def ascribe {T: Width → Type} (w: Width) (v: MaybeOpWidth T): Parser (T w) := do
  match v with
  | ⟨ .none, v ⟩ => pure v
  | ⟨ .some w2, v ⟩ =>
    if h: w = w2 then
      pure (h ▸ v)
    else
      fail s!"type error: {w} != {w2}"

def ascribeAvx {T: AvxWidth → Type} (w: AvxWidth) (v: MaybeAvxOpWidth T): Parser (T w) := do
match v with
  | ⟨ .none, v ⟩ => pure v
  | ⟨ .some w2, v ⟩ =>
    if h: w = w2 then
          pure (h ▸ v)
    else
          fail s!"type error: {w} != {w2}"

def ascribeOrInfer {T1 T2} (op1: MaybeAddrWidth × MaybeOpWidth T1) (next: Parser (MaybeAddrWidth × MaybeOpWidth T2)): Parser (MaybeAddrWidth × Σ w, T1 w × T2 w) := do
  let (addr_w2, op2) ← next
  let (addr_w1, op1) := op1
  let addr_w ← mergeAddrWidths addr_w1 addr_w2
  match op1 with
  | ⟨ .some w1, op1 ⟩ =>
    let op2 ← ascribe w1 op2
    pure (addr_w, ⟨ w1, op1, op2 ⟩)
  | ⟨ .none, op1 ⟩ =>
    match op2 with
    | ⟨ .some w2, op2 ⟩ =>
      pure (addr_w, ⟨ w2, op1, op2 ⟩)
    | ⟨ .none, _ ⟩ =>
      fail "missing type annotation"

def ascribeOrInferAvx {T1 T2} (op1: MaybeAddrWidth × MaybeAvxOpWidth T1) (next: Parser (MaybeAddrWidth × MaybeAvxOpWidth T2)): Parser (MaybeAddrWidth × Σ w, T1 w × T2 w) := do
  let (addr_w2, op2) ← next
  let (addr_w1, op1) := op1
  let addr_w ← mergeAddrWidths addr_w1 addr_w2
  match op1 with
    | ⟨ .some w1, op1 ⟩ =>
      let op2 ← ascribeAvx w1 op2
      pure (addr_w, ⟨ w1, op1, op2 ⟩)
    | ⟨ .none, op1 ⟩ =>
      match op2 with
      | ⟨ .some w2, op2 ⟩ =>
        pure (addr_w, ⟨ w2, op1, op2 ⟩)
      | ⟨ .none, _ ⟩ =>
        fail "missing type annotation"

-- Naming convention: O = function takes an operand width
def parseO {T1} (op: Parser (MaybeOpWidth T1)) (w: Width): Parser (T1 w) := do
  let op ← op
  ascribe w op

-- Naming convention: A = function also returns an address width
def parseAO {T1} (op: Parser (MaybeAddrWidth × MaybeOpWidth T1)) (w: Width): Parser (MaybeAddrWidth × T1 w) := do
  let (addr_w, op) ← op
  let op ← ascribe w op
  pure (addr_w, op)

def parseAvxAO {T1} (op: Parser (MaybeAddrWidth × MaybeAvxOpWidth T1)) (w: AvxWidth): Parser (MaybeAddrWidth × T1 w) := do
  let (addr_w, op) ← op
  let op ← ascribeAvx w op
  pure (addr_w, op)

-- ============================================================================
-- Lexical Utilities
-- ============================================================================

/-- Skip zero or more horizontal whitespace characters (space, tab). -/
def skipHWs : Parser Unit := do
  let _ ← many (pchar ' ' <|> pchar '\t')

/-- Skip a line comment starting with # or //. -/
def skipLineComment : Parser Unit := do
  -- JP: the '/' below is presumably a dummy value?
  let _ ← pchar '#' <|> (pstring "//" *> pure '/')
  let _ ← many (satisfy fun c => c != '\n')
  pure ()

/-- Skip horizontal whitespace and comments on the same line. -/
def skipHWsAndComments : Parser Unit := do
  skipHWs
  (skipLineComment *> pure ()) <|> pure ()

/-- Parse a single decimal digit. -/
def digit : Parser Char := satisfy fun c => c >= '0' && c <= '9'

/-- Parse a single hex digit. -/
def hexDigit : Parser Char := satisfy fun c =>
  (c >= '0' && c <= '9') || (c >= 'a' && c <= 'f') || (c >= 'A' && c <= 'F')

def hexVal (c : Char) : Int :=
    if c >= '0' && c <= '9' then c.toNat - '0'.toNat
    else if c >= 'a' && c <= 'f' then c.toNat - 'a'.toNat + 10
    else c.toNat - 'A'.toNat + 10

def parseHexOrDec : Parser Int := do
    let c ← peek!
    if c == '0' then do
      skip
      let c2 ← peek!
      if c2 == 'x' || c2 == 'X' then do
        skip
        let digits ← many1 hexDigit
        pure (digits.foldl (fun acc d => acc * 16 + hexVal d) 0)
      else do
        let rest ← many digit
        let allDigits := #['0'] ++ rest
        pure (allDigits.foldl (fun acc d => acc * 10 + (d.toNat - '0'.toNat)) 0)
    else do
      let digits ← many1 digit
      pure (digits.foldl (fun acc d => acc * 10 + (d.toNat - '0'.toNat)) 0)

/-- Parse a signed integer (decimal or hex). -/
def parseInt : Parser Int := do
  skipHWs
  let neg ← (pchar '-' *> pure true) <|> pure false
  let val ← parseHexOrDec
  pure (if neg then -val else val)

/-- Parse a name (identifier or label). -/
def parseName : Parser String := do
  let first ← satisfy fun c => c.isAlpha || c == '_' || c == '.'
  let rest ← many (satisfy fun c => c.isAlphanum || c == '_' || c == '.')
  pure (String.ofList (#[first] ++ rest).toList)

-- ============================================================================
-- Register Parsing
-- ============================================================================

section RegParsing

open Reg

-- Conventions: the *W variants are dependent pairs, and are used for parsing
-- functions that can synthesize (bottom-up) the width information. Parsing
-- functions that cannot synthesize a type take a width as an argument.

/-- Parse a register name. Returns the Reg (may be an alias like eax, ax, al). -/
def parseRegNameW : Parser RegW := do
  let name ← parseName
  match name.toLower with
  -- 64-bit registers
  | "rax" => pure ⟨ .W64, rax ⟩ | "rbx" => pure ⟨ .W64, rbx ⟩ | "rcx" => pure ⟨ .W64, rcx ⟩ | "rdx" => pure ⟨ .W64, rdx ⟩
  | "rsi" => pure ⟨ .W64, rsi ⟩ | "rdi" => pure ⟨ .W64, rdi ⟩ | "rsp" => pure ⟨ .W64, rsp ⟩ | "rbp" => pure ⟨ .W64, rbp ⟩
  | "r8"  => pure ⟨ .W64, r8  ⟩ | "r9"  => pure ⟨ .W64, r9 ⟩  | "r10" => pure ⟨ .W64, r10 ⟩ | "r11" => pure ⟨ .W64, r11 ⟩
  | "r12" => pure ⟨ .W64, r12 ⟩ | "r13" => pure ⟨ .W64, r13 ⟩ | "r14" => pure ⟨ .W64, r14 ⟩ | "r15" => pure ⟨ .W64, r15 ⟩
  -- 32-bit aliases
  | "eax" => pure ⟨ .W32, eax ⟩ | "ebx" => pure ⟨ .W32, ebx ⟩ | "ecx" => pure ⟨ .W32, ecx ⟩ | "edx" => pure ⟨ .W32, edx ⟩
  | "esi" => pure ⟨ .W32, esi ⟩ | "edi" => pure ⟨ .W32, edi ⟩ | "esp" => pure ⟨ .W32, esp ⟩ | "ebp" => pure ⟨ .W32, ebp ⟩
  | "r8d"  => pure ⟨ .W32, r8d ⟩  | "r9d"  => pure ⟨ .W32, r9d ⟩  | "r10d" => pure ⟨ .W32, r10d ⟩ | "r11d" => pure ⟨ .W32, r11d ⟩
  | "r12d" => pure ⟨ .W32, r12d ⟩ | "r13d" => pure ⟨ .W32, r13d ⟩ | "r14d" => pure ⟨ .W32, r14d ⟩ | "r15d" => pure ⟨ .W32, r15d ⟩
  -- 16-bit aliases
  | "ax" => pure ⟨ .W16, ax ⟩ | "bx" => pure ⟨ .W16, bx ⟩ | "cx" => pure ⟨ .W16, cx ⟩ | "dx" => pure ⟨ .W16, dx ⟩
  | "si" => pure ⟨ .W16, si ⟩ | "di" => pure ⟨ .W16, di ⟩ | "sp" => pure ⟨ .W16, sp ⟩ | "bp" => pure ⟨ .W16, bp ⟩
  | "r8w"  => pure ⟨ .W16, r8w ⟩  | "r9w"  => pure ⟨ .W16, r9w ⟩  | "r10w" => pure ⟨ .W16, r10w ⟩ | "r11w" => pure ⟨ .W16, r11w ⟩
  | "r12w" => pure ⟨ .W16, r12w ⟩ | "r13w" => pure ⟨ .W16, r13w ⟩ | "r14w" => pure ⟨ .W16, r14w ⟩ | "r15w" => pure ⟨ .W16, r15w ⟩
  -- 8-bit aliases
  | "al" => pure ⟨ .W8, al ⟩ | "bl" => pure ⟨ .W8, bl ⟩ | "cl" => pure ⟨ .W8, cl ⟩ | "dl" => pure ⟨ .W8, dl ⟩
  | "sil" => pure ⟨ .W8, sil ⟩ | "dil" => pure ⟨ .W8, dil ⟩ | "spl" => pure ⟨ .W8, spl ⟩ | "bpl" => pure ⟨ .W8, bpl ⟩
  | "r8b"  => pure ⟨ .W8, r8b ⟩  | "r9b"  => pure ⟨ .W8, r9b ⟩  | "r10b" => pure ⟨ .W8, r10b ⟩ | "r11b" => pure ⟨ .W8, r11b ⟩
  | "r12b" => pure ⟨ .W8, r12b ⟩ | "r13b" => pure ⟨ .W8, r13b ⟩ | "r14b" => pure ⟨ .W8, r14b ⟩ | "r15b" => pure ⟨ .W8, r15b ⟩
  -- high-byte registers
  | "ah" => pure ⟨ .W8, ah ⟩ | "bh" => pure ⟨ .W8, bh ⟩ | "ch" => pure ⟨ .W8, ch ⟩ | "dh" => pure ⟨ .W8, dh ⟩
  | _ => fail s!"unknown register: {name}"

/-- Safely map a natural number index to its corresponding RegMm constructor. -/
def toRegMm (idx : Nat) : Option RegMm :=
  match idx with
  | 0  => some .mm0  | 1  => some .mm1  | 2  => some .mm2  | 3  => some .mm3
  | 4  => some .mm4  | 5  => some .mm5  | 6  => some .mm6  | 7  => some .mm7
  | 8  => some .mm8  | 9  => some .mm9  | 10 => some .mm10 | 11 => some .mm11
  | 12 => some .mm12 | 13 => some .mm13 | 14 => some .mm14 | 15 => some .mm15
  | 16 => some .mm16 | 17 => some .mm17 | 18 => some .mm18 | 19 => some .mm19
  | 20 => some .mm20 | 21 => some .mm21 | 22 => some .mm22 | 23 => some .mm23
  | 24 => some .mm24 | 25 => some .mm25 | 26 => some .mm26 | 27 => some .mm27
  | 28 => some .mm28 | 29 => some .mm29 | 30 => some .mm30 | 31 => some .mm31
  | _ => none

/-- Parse an AVX register operand (e.g., %xmm0, %ymm15, %zmm31). -/
def parseAvxRegW : Parser AvxRegW := do
  skipHWs
  let _ ← pchar '%'
  -- Match standard or uppercase variants of the AVX prefixes
  let pfx ← (pstring "xmm" <|> pstring "XMM" <|>
             pstring "ymm" <|> pstring "YMM" <|>
             pstring "zmm" <|> pstring "ZMM")
  let idx ← digits
  match toRegMm idx with
  | none => fail s!"invalid AVX register index: {idx} (must be between 0 and 31)"
  | some mm =>
    match pfx.toLower with
    | "xmm" => pure ⟨ .W128, .xmm mm ⟩
    | "ymm" => pure ⟨ .W256, .ymm mm ⟩
    | "zmm" => pure ⟨ .W512, .zmm mm ⟩
    | _ => fail s!"unknown AVX register prefix: {pfx}"
end RegParsing

/-- Parse a register operand: %rax, %eax, %ax, %al, etc. -/
def parseRegW : Parser RegW := do
  skipHWs
  let _ ← pchar '%'
  parseRegNameW

def parseLowRegName: Parser (Width × Reg64) := do
  let ⟨ w, r ⟩ ← parseRegNameW
  match r with
  | .low r64 _ => pure (w, r64)
  | _ => fail s!"high byte register cannot be used for an addrexpr"

def parseLowReg : Parser (Width × Reg64) := do
  skipHWs
  let _ ← pchar '%'
  parseLowRegName

def parseRegOrRipW : Parser (Width × RegOrRip) := do
  skipHWs
  let _ ← pchar '%'
  (do
    let _ ← pstring "rip"
    -- TODO: once we start parsing %eip here, we need to understand what is the
    -- behavior in 64-bit mode when the .S contains %eip -- does the address get
    -- clamped to 32 bits? in that case, Semantics.lean needs to be updated to
    -- process the `.rip` case via `toAddressSize`
    pure (.W64, .rip)
  ) <|>
  (do
    let (w, r) ← parseLowRegName -- WAS: parseRegNameW
    pure (w, .reg r)
  )


-- ============================================================================
-- Operand Parsing
-- ============================================================================

/-- Parse an immediate operand: $42, $-17, $0xff.
    Accepts any 64-bit value (0 to 2^64-1) as a bit pattern.
    Values like $0xFFFFFFFFFFFFFFFF are interpreted as -1 in two's complement. -/
def parseInt64 : Parser ConstExpr := do
  let _ ← pchar '$'
  let v ← parseInt
  -- JP: why not simply Int64.ofInt? Would that not implement the behavior
  -- below?

  -- Accept any value that fits in 64 bits
  -- Negative values: must be >= Int64.min (-2^63)
  -- Positive values: must be < 2^64 (allows unsigned representation like 0xFFFFFFFFFFFFFFFF)
  if v < -9223372036854775808 || v >= 18446744073709551616 then
    fail s!"immediate {v} out of 64-bit range"
  -- Convert to Int64: values > Int64.max are reinterpreted as negative (two's complement)
  let i64 := if v > 9223372036854775807 then
    -- Reinterpret large positive value as negative two's complement
    Int64.ofInt (v - 18446744073709551616)
  else
    Int64.ofInt v
  pure (.int64 i64)

-- parseName allows for dots
def parseLabelRaw : Parser Label := parseName

def parseLabel : Parser ConstExpr := do
  let n ← parseLabelRaw
  pure (.label n)

/-- Parse a memory operand (a.k.a. "address expression"): disp(%base),
  (%base,%idx,scale), etc. Just like `as`, we enforce consistency at the level
  of operands. For instance, we also error out on this:

  test3.S:1:13: error: base register is 64-bit, but index register is not
  movq %rax, (%rcx, %ebx)
              ^
-/
def parseMemory : Parser (Width × AddrExpr) := do
  skipHWs
  -- Optional displacement; TODO: parse ConstExpr generally
  let disp ← (do let i ← parseInt; pure (.int64 (Int64.ofInt i))) <|> parseLabel <|> pure (.int64 0)
  skipHWs
  let _ ← pchar '('

  skipHWs
  let (w1, base) ← parseRegOrRipW
  -- Check for index register
  let idx ← (do
    skipHWs
    let _ ← pchar ','
    skipHWs
    let r ← parseLowReg
    pure (some r)) <|> pure none
  -- Check for scale
  let scale ← match idx with
    | some _ => (do
        skipHWs
        let _ ← pchar ','
        skipHWs
        let s ← parseInt
        pure s.toNat) <|> pure 1
    | none => pure 1
  let scale ← match scale with
              | 1 => pure Width.W8
              | 2 => pure Width.W16
              | 4 => pure Width.W32
              | 8 => pure Width.W64
              | s => fail s!"invalid scale {s}, must be 1, 2, 4, or 8"
  -- JP: this is slightly inexact, in that we allow parsing a scale without an
  -- index, but not a big deal
  skipHWs
  let _ ← pchar ')'
  -- Some adapters between the parsed components and the expected dependent
  -- pairs:
  let w ← match w1, idx with
    | w1, .some (w2, _) =>
      if w1 ≠ w2 then
        fail "type mismatch in memory addressing operands: base ({w1}) and index ({w2}) have different widths"
      else
        .pure w1
    | w1, .none =>
      .pure w1
  let idx := Option.map (fun (_, idx) => ⟨idx, scale⟩) idx
  pure (w, { base, idx, disp })

def parseImm w : Parser (Operand w) := do
  skipHWs
  let c ← peek!
  let i ←
    match c with
    | '$' => parseInt64
    | _ => parseLabel
  pure (.imm i)

/-- Parse any operand: register, immediate, or memory. -/
def parseOperand: Parser (MaybeAddrWidth × MaybeOpWidth Operand) := do
  skipHWs
  let c ← peek!
  match c with
  | '%' =>
    let ⟨ w, r ⟩ ← parseRegW
    pure (.none, ⟨ w, .reg r ⟩)
  | '$' =>
    let i ← parseInt64
    pure (.none, ⟨ .none, .imm i ⟩)
  | _ =>
    if c == '(' || c == '-' || c.isDigit then
      let (w, m) ← parseMemory
      pure (w, ⟨ .none, .mem m ⟩)
    else
      let i ← parseLabel
      pure (.none, ⟨ .none, .imm i ⟩)

/-- Parse a register or memory operand (not immediate). -/
def parseRegOrMem: Parser (MaybeAddrWidth × MaybeOpWidth RegOrMem) := do
  skipHWs
  let c ← peek!
  if c == '%' then
    let ⟨ w, r ⟩ ← parseRegW
    pure (.none, ⟨ .some w, .reg r ⟩)
  else if c == '(' || c == '-' || c.isDigit then
    let (w, m) ← parseMemory
    pure (w, ⟨ .none, .mem m ⟩)
  else
    fail s!"expected register or memory operand, got {c}"

def parseAvxRegOrMem: Parser (MaybeAddrWidth × MaybeAvxOpWidth AvxRegOrMem) := do
  skipHWs
  let c ← peek!
  if c == '%' then
    let ⟨ w, r ⟩ ← parseAvxRegW
    pure (.none, ⟨ .some w, .avx r ⟩)
  else if c == '(' || c == '-' || c.isDigit then
    let (w, m) ← parseMemory
    pure (w, ⟨ .none, .mem m ⟩)
  else
      fail s!"expected AVX register or memory operand, got {c}"

def parseRelRegOrMem: Parser (MaybeAddrWidth × RelRegOrMem) := do
  skipHWs
  (do
    let ⟨ w, r ⟩ ← parseRegW
    if h: w = .W64 then
      pure (.none, (.reg (h ▸ r)))
    else
      fail "expected a 64-bit register in relative addressing position"
  ) <|> (do
    -- FIXME: allow more cases in the syntax; for now, we only parse labels, and
    -- assume that all jumps are relative, in that this seems to be the behavior
    -- of the assembler
    let e ← parseLabel
    pure (.none, (.rel (.sub e .after_current_instruction)))
  ) <|> (do
    let (w, m) ← parseMemory
    pure (w, (.mem m))
  )

/-- TODO: this ought to be able to parse more in the ConstExpr category, just
  like many of the other functions above -/
def parseShiftExpr: Parser ShiftCountExpr := do
  skipHWs
  (do
    let i ← parseInt64
    pure (.imm8 i))
  <|> (do
    let _ ← pstring "%cl"
    pure .cl)


-- ============================================================================
-- Condition Code Parsing
-- ============================================================================

/-- Parse a condition code from a conditional jump mnemonic suffix. -/
def parseCondCode (suffix : String.Slice) : Parser CondCode :=
  match suffix.copy.toLower with
  | "z" | "e" => .pure .z
  | "nz" | "ne" => .pure .nz
  | "b" | "c" | "nae" => .pure .b
  | "ae" | "nc" | "nb" => .pure .ae
  | "a" | "nbe" => .pure .a
  | "be" | "na" => .pure .be
  | _ => .fail s!"unknown condition code: {suffix}"

-- ============================================================================
-- Instruction Parsing
-- ============================================================================

/-- Helper to construct an Instr from an Operation, defaulting address size to .W64 -/
def toInstr (addr : MaybeAddrWidth) {w : Width} (op : Operation w) : Instr :=
  let _ : AddressSize := { address_size := addr.getD .W64 }
  ↑op

/-- Helper to construct an Instr from an AvxOperation, defaulting address size to .W64 -/
def toAvxInstr (addr : MaybeAddrWidth) {w : AvxWidth} (op : AvxOperation w) : Instr :=
  let _ : AddressSize := { address_size := addr.getD .W64 }
  ↑op

/-- Parse a comma separator. -/
def parseComma : Parser Unit := do
  skipHWs
  let _ ← pchar ','
  skipHWs

/-- Try to parse a shift count followed by a comma; if that fails, default to 1. -/
def parseOptionalShiftAndComma : Parser ShiftCountExpr :=
  (attempt do let cnt ← parseShiftExpr; parseComma; pure cnt) <|> pure (.imm8 (.int64 1))

def parseReg : Parser (MaybeOpWidth Reg) := do
  let p ← parseRegW; pure ⟨ .some p.1, p.2 ⟩

def parseRegO := parseO parseReg

-- For compatibility with commaSeparated -- registers can never provide an
-- inference hint about instruction address width.
def parseRegA : Parser (MaybeAddrWidth × MaybeOpWidth Reg) := do
  let p ← parseRegW; pure (.none, ⟨ .some p.1, p.2 ⟩)

def parseOperandAO := parseAO parseOperand
def parseRegOrMemAO := parseAO parseRegOrMem

-- TODO: why is the dot notation not working here?
def Char.toWidth (c: Char): Parser Width :=
  match c with
  | 'b' => pure .W8
  | 'w' => pure .W16
  | 'l' => pure .W32
  | 'q' => pure .W64
  | _ => fail "impossible: unknown suffix"

def instrWidth (s: String): Parser Width :=
  match s.back? with
  | .none => fail "impossible: empty instruction"
  | .some c => Char.toWidth c

def commaSeparated {T1 T2} (op_w: Option Width) (p1: Parser (MaybeAddrWidth × MaybeOpWidth T1)) (p2: Parser (MaybeAddrWidth × MaybeOpWidth T2))
  (mk: {op_w: Width} → T2 op_w → T1 op_w → Operation op_w): Parser Instr := do
    match op_w with
    | .none =>
      let src ← p1; parseComma
      let (addr_w, ⟨ _w, src, dst ⟩) ← ascribeOrInfer src p2
      pure (toInstr addr_w (mk dst src))
    | .some w =>
      let (addr_w1, src) ← parseAO p1 w
      parseComma
      let (addr_w2, dst) ← parseAO p2 w
      let addr_w ← mergeAddrWidths addr_w1 addr_w2
      pure (toInstr addr_w (mk dst src))

def commaSeparatedAvx {T1 T2} (op_w: Option AvxWidth) (p1: Parser (MaybeAddrWidth × MaybeAvxOpWidth T1)) (p2: Parser (MaybeAddrWidth × MaybeAvxOpWidth T2))
  (mk: {op_w: AvxWidth} → T2 op_w → T1 op_w → AvxOperation op_w): Parser Instr := do
  match op_w with
  | .none =>
    let src ← p1; parseComma
    let (addr_w, ⟨ _w, src, dst ⟩) ← ascribeOrInferAvx src p2
    pure (toAvxInstr addr_w (mk dst src))
  | .some w =>
    let (addr_w1, src) ← parseAvxAO p1 w
    parseComma
    let (addr_w2, dst) ← parseAvxAO p2 w
    let addr_w ← mergeAddrWidths addr_w1 addr_w2
    pure (toAvxInstr addr_w (mk dst src))

def assertW {T} (v: MaybeOpWidth T): Parser (Σ w: Width, T w) :=
  match v with
  | ⟨ .none, _ ⟩ => fail "missing type annotation"
  | ⟨ .some w, T ⟩ => pure ⟨ w, T ⟩

def Option.toParser {T} (self: Option T): Parser T :=
  match self with
  | .some v => pure v
  | .none => fail "empty option"

instance {T} : Coe (Option T) (Parser T) where coe := Option.toParser

/-- Parse an instruction mnemonic and its operands.
    AT&T syntax: src, dst (reversed from Intel). -/
def parseInstr : Parser Instr := do
  skipHWs
  let mnemonic ← parseName
  let mn := mnemonic.toLower
  -- Match on full mnemonic name (no suffix stripping)
  match mn with
  -- Arithmetic (two-operand: src, dst) - 64-bit
  | "add" =>
    commaSeparated .none parseOperand parseRegOrMem .add

  | "addq" | "addl" | "addw" | "addb" =>
    let w ← instrWidth mn
    commaSeparated w parseOperand parseRegOrMem .add

  | "adc" =>
    commaSeparated .none parseOperand parseRegOrMem .adc

  | "adcq" | "adcl" | "adcw" | "adcb" =>
    let w ← instrWidth mn
    commaSeparated w parseOperand parseRegOrMem .adc

  | "adcx" =>
    -- Per Intel SDM: ADCX dest must be a register (r32/r64)
    commaSeparated .none parseRegOrMem parseRegA .adcx

  | "adcxq" | "adcxl" =>
    let w ← instrWidth mn
    commaSeparated w parseRegOrMem parseRegA .adcx

  | "adox" =>
    -- Per Intel SDM: ADOX dest must be a register (r32/r64)
    commaSeparated .none parseRegOrMem parseRegA .adox

  | "adoxq" | "adoxl" =>
    let w ← instrWidth mn
    commaSeparated w parseRegOrMem parseRegA .adox

  | "sub" =>
    commaSeparated .none parseOperand parseRegOrMem .sub

  | "subq" | "subl" | "subw" | "subb" =>
    let w ← instrWidth mn
    commaSeparated w parseOperand parseRegOrMem .sub

  | "sbb" =>
    commaSeparated .none parseOperand parseRegOrMem .sbb

  | "sbbq" | "sbbl" | "sbbw" | "sbbb" =>
    let w ← instrWidth mn
    commaSeparated w parseOperand parseRegOrMem .sbb

  | "mul" =>
    let ( addr_w, src) ← parseRegOrMem
    let ⟨ _w, src ⟩ ← assertW src
    pure (toInstr addr_w (.mul src))

  | "mulq" | "mull" | "mulw" | "mulb" =>
    let w ← instrWidth mn
    let ( addr_w, src ) ← parseRegOrMemAO w
    pure (toInstr addr_w (.mul src))

  | "mulx" =>
    -- Per Intel SDM: MULX dest1 and dest2 must be registers
    -- mulxq src, lo, hi (AT&T: src → rdx*src, result in lo:hi)
    let ( addr_w, src ) ← parseRegOrMem; parseComma
    let lo ← parseRegW; parseComma
    let hi ← parseRegW
    match src, lo, hi with
    | ⟨ .none, src ⟩, ⟨ w1, lo ⟩, ⟨ w2, hi ⟩ =>
      if h: w1 = w2 then
        pure (toInstr addr_w (.mulx (h ▸ hi) lo src))
      else
        fail "mulx not homogenous"
    | ⟨ .some w3, src ⟩, ⟨ w1, lo ⟩, ⟨ w2, hi ⟩ =>
      if h: w1 = w2 then
        let hi := h ▸ hi
        if h: w1 = w3 then
          let src := h ▸ src
          pure (toInstr addr_w (.mulx hi lo src))
        else
          fail "mulx not homogenous"
      else
        fail "mulx not homogenous"

  | "mulxq" | "mulxl" =>
    let w ← instrWidth mn
    let ( addr_w, src ) ← parseRegOrMemAO w; parseComma
    let lo ← parseRegO w; parseComma
    let hi ← parseRegO w
    pure (toInstr addr_w (.mulx hi lo src))

  | "imul" =>
    (attempt do
      let src1 ← parseOperand; parseComma;
      (attempt do
        let src2 ← parseRegOrMem; parseComma
        let (addr_w2, ⟨ w, src2, dst ⟩) ← ascribeOrInfer src2 parseRegA
        let (addr_w1, src1) := src1
        let src1 ← ascribe w src1
        let addr_w ← mergeAddrWidths addr_w1 addr_w2
        pure (toInstr addr_w (.imul (.some dst) src2 src1)))
      <|> (do
        let (addr_w, ⟨_w, src1, src2 ⟩) ← ascribeOrInfer src1 parseRegOrMem
        pure (toInstr addr_w (.imul .none src2 src1))
      )
    ) <|> (do
      let (addr_w, src) ← parseRegOrMem
      let ⟨_w, src ⟩ ← assertW src
      pure (toInstr addr_w (.imul1 src))
    )

  | "imulq" | "imull" | "imulw" | "imulb" =>
    let w ← instrWidth mn
    (attempt do
      let (addr_w1, src1) ← parseOperandAO w; parseComma
      (attempt do
        let (addr_w2, src2) ← parseRegOrMemAO w; parseComma
        let dst ← parseRegO w
        let addr_w ← mergeAddrWidths addr_w1 addr_w2
        pure (toInstr addr_w (.imul (.some dst) src2 src1))
      ) <|>
      (do
        let (addr_w2, src2) ← parseRegOrMemAO w
        let addr_w ← mergeAddrWidths addr_w1 addr_w2
        pure (toInstr addr_w (.imul none src2 src1))
      )
    ) <|>
    (do
      let (addr_w, src) ← parseRegOrMemAO w
      pure (toInstr addr_w (.imul1 src))
    )
  | "neg" =>
    let ( addr_w, dst) ← parseRegOrMem
    let ⟨ _w, dst ⟩ ← assertW dst
    pure (toInstr addr_w (.neg dst))

  | "negq" | "negl" | "negw" | "negb" =>
    let w ← instrWidth mn
    let ( addr_w, dst ) ← parseRegOrMemAO w
    pure (toInstr addr_w (.neg dst))

  | "dec" =>
    let ( addr_w, dst ) ← parseRegOrMem
    let ⟨ _w, dst ⟩ ← assertW dst
    pure (toInstr addr_w (.dec dst))

  | "decq" | "decl" | "decw" | "decb" =>
    let w ← instrWidth mn
    let ( addr_w, dst ) ← parseRegOrMemAO w
    pure (toInstr addr_w (.dec dst))

  | "mov" | "movabs" =>
    commaSeparated .none parseOperand parseRegOrMem .mov

  | "movq" | "movl" | "movw" | "movb"
  | "movabsq" | "movabsl" | "movabsw" | "movabsb" =>
    let w ← instrWidth mn
    commaSeparated w parseOperand parseRegOrMem .mov

  | "movsx" =>
    -- Must be a register otherwise lacking type info
    let ⟨ _w_src, src ⟩ ← parseRegW
    let ⟨ _w_dst, dst ⟩ ← parseRegW
    pure (toInstr .none (.movsx (.reg dst) (.reg src)))

  | "movzx" =>
    -- Must be a register otherwise lacking type info
    let ⟨ _w_src, src ⟩ ← parseRegW
    let ⟨ _w_dst, dst ⟩ ← parseRegW
    pure (toInstr .none (.movzx (.reg dst) (.reg src)))

  | "movsbw" | "movsbl" | "movsbq" | "movswl" | "movswq" =>
    let w_dst ← instrWidth mn
    let c_src ← String.Pos.Raw.get? mn (.mk (mn.length - 2))
    let w_src ← Char.toWidth c_src
    let src ← parseRegO w_src; parseComma
    let dst ← parseRegO w_dst
    pure (toInstr .none (.movsx (.reg dst) (.reg src)))

  | "movzbw" | "movzbl" | "movzbq" | "movzwl" | "movzwq" =>
    let w_dst ← instrWidth mn
    let c_src ← String.Pos.Raw.get? mn (.mk (mn.length - 2))
    let w_src ← Char.toWidth c_src
    let src ← parseRegO w_src; parseComma
    let dst ← parseRegO w_dst
    pure (toInstr .none (.movzx (.reg dst) (.reg src)))

  | "lea" =>
    let ( addr_w, src ) ← parseMemory; parseComma
    let ⟨ _w, dst ⟩ ← parseRegW
    pure (toInstr (some addr_w) (.lea dst src))

  | "leaq" | "leal" | "leaw" | "leab" =>
    let w2 ← instrWidth mn
    let ( addr_w, src ) ← parseMemory; parseComma
    let ⟨ w, dst ⟩ ← parseRegW
    if w2 ≠ w then
      fail "inconsistency in {mn}"
    else
      pure (toInstr (some addr_w) (.lea dst src))

  | "movups" =>
    commaSeparatedAvx .none parseAvxRegOrMem parseAvxRegOrMem .movups

  | "vmovups" =>
    commaSeparatedAvx .none parseAvxRegOrMem parseAvxRegOrMem .vmovups

  -- Bitwise - 64-bit
  | "xor" =>
    commaSeparated .none parseOperand parseRegOrMem .xor

  | "xorq" | "xorl" | "xorw" | "xorb" =>
    let w ← instrWidth mn
    commaSeparated w parseOperand parseRegOrMem .xor

  | "and" =>
    commaSeparated .none parseOperand parseRegOrMem .and

  | "andq" | "andl" | "andw" | "andb" =>
    let w ← instrWidth mn
    commaSeparated w parseOperand parseRegOrMem .and

  | "not" =>
    let ( addr_w, dst ) ← parseRegOrMem
    let ⟨ _w, dst ⟩ ← assertW dst
    pure (toInstr addr_w (.not dst))

  | "notq" | "notl" | "notw" | "notb" =>
    let w ← instrWidth mn
    let ( addr_w, dst ) ← parseRegOrMemAO w
    pure (toInstr addr_w (.not dst))

  | "or" =>
    commaSeparated .none parseOperand parseRegOrMem .or

  | "orq" | "orl" | "orw" | "orb" =>
    let w ← instrWidth mn
    commaSeparated w parseOperand parseRegOrMem .or

  -- Compare - 64-bit
  | "cmp" => do
    commaSeparated .none parseOperand parseRegOrMem .cmp

  | "cmpq" | "cmpl" | "cmpw" | "cmpb" => do
    let w ← instrWidth mn
    commaSeparated w parseOperand parseRegOrMem .cmp

  -- Test (sets flags based on AND without storing result)
  | "test" =>
    commaSeparated .none parseOperand parseRegOrMem .test

  | "testq" | "testl" | "testw" | "testb" =>
    let w ← instrWidth mn
    commaSeparated w parseOperand parseRegOrMem .test

  -- Shift instructions - 64-bit
  | "shl"
  | "sal" =>
    let cnt ← parseOptionalShiftAndComma
    let ( addr_w, dst ) ← parseRegOrMem
    let ⟨ _w, dst ⟩ ← assertW dst
    pure (toInstr addr_w (.shl dst cnt))

  | "shlq" | "shll" | "shlw" | "shlb"
  | "salq" | "sall" | "salw" | "salb" =>
    let w ← instrWidth mn
    let cnt ← parseOptionalShiftAndComma
    let ( addr_w, dst ) ← parseRegOrMemAO w
    pure (toInstr addr_w (.shl dst cnt))

  | "shr" =>
    let cnt ← parseOptionalShiftAndComma
    let ( addr_w, dst ) ← parseRegOrMem
    let ⟨ _w, dst ⟩ ← assertW dst
    pure (toInstr addr_w (.shr dst cnt))

  | "shrq" | "shrl" | "shrw" | "shrb" =>
    let w ← instrWidth mn
    let cnt ← parseOptionalShiftAndComma
    let ( addr_w, dst ) ← parseRegOrMemAO w
    pure (toInstr addr_w (.shr dst cnt))

  | "sar" =>
    let cnt ← parseOptionalShiftAndComma
    let ( addr_w, dst ) ← parseRegOrMem
    let ⟨ _w, dst ⟩ ← assertW dst
    pure (toInstr addr_w (.sar dst cnt))

  | "sarq" | "sarl" | "sarw" | "sarb" =>
    let w ← instrWidth mn
    let cnt ← parseOptionalShiftAndComma
    let ( addr_w, dst ) ← parseRegOrMemAO w
    pure (toInstr addr_w (.sar dst cnt))

  | "shld" =>
    let cnt ← parseShiftExpr; parseComma
    commaSeparated .none parseRegA parseRegOrMem (fun dst src => .shld dst src cnt)

  | "shldq" | "shldl" | "shldw" =>
    let w ← instrWidth mn
    let cnt ← parseShiftExpr; parseComma
    commaSeparated w parseRegA parseRegOrMem (fun dst src => .shld dst src cnt)

  | "shrd" =>
    let cnt ← parseShiftExpr; parseComma
    commaSeparated .none parseRegA parseRegOrMem (fun dst src => .shrd dst src cnt)

  | "shrdq" | "shrdl" | "shrdw" =>
    let w ← instrWidth mn
    let cnt ← parseShiftExpr; parseComma
    commaSeparated w parseRegA parseRegOrMem (fun dst src => .shrd dst src cnt)

  -- Rotate instructions - 64-bit
  | "rol" =>
    let cnt ← parseOptionalShiftAndComma
    let ( addr_w, dst ) ← parseRegOrMem
    let ⟨ _w, dst ⟩ ← assertW dst
    pure (toInstr addr_w (.rol dst cnt))

  | "rolq" | "roll" | "rolw" | "rolb" =>
    let w ← instrWidth mn
    let cnt ← parseOptionalShiftAndComma
    let ( addr_w, dst ) ← parseRegOrMemAO w
    pure (toInstr addr_w (.rol dst cnt))

  | "ror" =>
    let cnt ← parseOptionalShiftAndComma
    let ( addr_w, dst ) ← parseRegOrMem
    let ⟨ _w, dst ⟩ ← assertW dst
    pure (toInstr addr_w (.ror dst cnt))

  | "rorq" | "rorl" | "rorw" | "rorb" =>
    let w ← instrWidth mn
    let cnt ← parseOptionalShiftAndComma
    let ( addr_w, dst ) ← parseRegOrMemAO w
    pure (toInstr addr_w (.ror dst cnt))

  -- Byte swap
  | "bswap" =>
    let ⟨ _w, dst ⟩ ← parseRegW
    pure (toInstr .none (.bswap dst))

  | "bswapq" | "bswapl" =>
    let ⟨ w, dst ⟩ ← parseRegW
    let w2 ← instrWidth mn
    if w2 ≠ w then
      fail "inconsistency in {mn}"
    else
      pure (toInstr .none (.bswap dst))

  -- Stack operations
  | "push" =>
    let ( addr_w, src ) ← parseOperand
    let ⟨ _w, src ⟩ ← assertW src
    pure (toInstr addr_w (.push src))

  | "pushq" | "pushl" | "pushw" | "pushb" =>
    let w ← instrWidth mn
    let ( addr_w, src ) ← parseOperandAO w
    pure (toInstr addr_w (.push src))

  | "pop" =>
    let ( addr_w, dst) ← parseRegOrMem
    let ⟨ _w, dst ⟩ ← assertW dst
    pure (toInstr addr_w (.pop dst))

  | "popq" | "popl" | "popw" | "popb" =>
    let w ← instrWidth mn
    let ( addr_w, dst ) ← parseRegOrMemAO w
    pure (toInstr addr_w (.pop dst))

  | "ret" | "retq" =>
    pure (toInstr .none (w := .W64) .ret)

  | "call" | "callq" =>
    let ( addr_w, target ) ← parseRelRegOrMem
    pure (toInstr addr_w (w := .W64) (.call target))

  -- Control flow - unconditional jump
  | "jmp" | "jmpq" =>
    let ( addr_w, target ) ← parseRelRegOrMem
    pure (toInstr addr_w (w := .W64) (.jmp target))

  | "nop" =>
    (do
      skipHWs
      let sz ← parseHexOrDec
      pure (toInstr .none (w := .W64) (.nop sz.toNat))
    ) <|> (pure (toInstr .none (w := .W64) (.nop 1)))

  -- Control flow - conditional jumps
  | _ =>
    if mn.startsWith "j" then
      let cc ← parseCondCode (mn.drop 1)
      skipHWs
      let target ← parseLabelRaw
      pure (toInstr .none (w := .W64) (.jcc cc target))
    else if mn.startsWith "set" then
      let cc ← parseCondCode (mn.drop 3)
      let (addr_w, dst) ← parseRegOrMemAO .W8
      pure (toInstr addr_w (.setcc cc dst))
    else if mn.startsWith "cmov" then
      -- TODO: are the suffixed variants really used here? do we truly need to
      -- handle cmovzb and the like? how many are there? we could conceivably
      -- just ignore it on the basis that the assembler will bail if there is
      -- something inconsistent like .cmovzb %rax %rbx
      let cc ← parseCondCode (mn.drop 4)
      commaSeparated .none parseRegOrMem parseRegA (.cmovcc cc)
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

def parseAlign : Parser Instr := do
  let _ ← pstring ".align"
  skipHWs
  let alignment ← parseHexOrDec
  let pad ← (do
    skipHWs
    let _ ← parseComma
    skipHWs
    let pad ← parseHexOrDec
    pure (some pad.toNat)
  ) <|> pure none
  pure (toInstr .none (w := .W64) (.nopalign alignment.toNat pad))

def skipSpaceAndCheckLineEnd : Parser Bool := do
  skipHWs
  let c? ← peek?
  match c? with
  | none
  | some '\n' =>
    pure true
  | some '#' =>
    skipLineComment
    pure true
  | some _ =>
    pure false

def parseOptionalInstr : Parser (Option Directive) := do
  if (← skipSpaceAndCheckLineEnd) then
    pure none
  else
    let i ← parseAlign <|> parseInstr
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
elab "parse(" s:str ")" : term => do
  match parse s.getString with
  | .ok p => return Lean.toExpr p
  | .error e => throwErrorAt s e


-- ============================================================================
-- Assembly Preprocessing (Directive Stripping)
-- ============================================================================
-- These delete code that is not presently handled by Kraken. This is useful
-- for running on code without needing to modify it to delete things we do not
-- model. These are used in file parsing.

private def directiveKeywords : List String :=
  ["file", "text", "data", "p2align", "balign",
   "globl", "global", "type", "size", "section",
   "weak", "hidden", "protected", "internal", "ident",
   "cfi_startproc", "cfi_endproc", "cfi_def_cfa",
   "cfi_offset", "cfi_adjust_cfa_offset", "cfi_def_cfa_offset",
   "cfi_def_cfa_register", "cfi_restore", "cfi_remember_state",
   "cfi_restore_state"]

private def extractDirectiveName (s : String) : String :=
  let rest := s.drop 1
  let nameStr := (rest.takeWhile (fun c => c != ' ' && c != '\t' && c != ',' && c != ':')).toString
  nameStr.toLower

private def keepLine (line : String) : Bool :=
  let stripped := (line.trimAsciiStart).toString
  if stripped.isEmpty || stripped.startsWith "#" then true
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
elab "fileAsString(" path:str ")" : term => do
  let pathStr := path.getString
  let contents ← IO.FS.readFile pathStr
  return mkStrLit contents

/-- Parse an assembly file, stripping directives first.
    Throws error on parse failure. -/
elab "parseFile(" path:str ")" : term => do
  let pathStr := path.getString
  let content ← IO.FS.readFile pathStr
  let stripped := stripDirectives content
  match parse stripped with
  | .ok p => return Lean.toExpr p
  | .error e => throwErrorAt path e


end Kraken.X64.Parser
