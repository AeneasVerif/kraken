/-
Kraken Parser - x86_64 AT&T Assembly Parser

Parses AT&T syntax assembly strings into Kraken's Program type.
Uses Lean's built-in Std.Internal.Parsec library.

The primary reference for the syntax is the GAS manual:
https://sourceware.org/binutils/docs/as/
-/

import Kraken.Semantics
import Std.Internal.Parsec.String

namespace Kraken.Parser

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

end RegParsing

/-- Parse a register operand: %rax, %eax, %ax, %al, etc. -/
def parseRegW : Parser RegW := do
  skipHWs
  let _ ← pchar '%'
  parseRegNameW

def parseRegOrRipW : Parser RegOrRip := do
  skipHWs
  let _ ← pchar '%'
  (do
    let _ ← pstring "rip"
    pure .rip
  ) <|>
  (do
    let rw ← parseRegNameW
    pure (.ofRegW rw)
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
  pure (.Int64 i64)

-- parseName allows for dots
def parseLabelRaw : Parser Label := parseName

def parseLabel : Parser ConstExpr := do
  let n ← parseLabelRaw
  pure (.Label n)

/-- Parse a memory operand (a.k.a. "address expression"): disp(%base), (%base,%idx,scale), etc. -/
def parseMemory : Parser AddrExpr := do
  skipHWs
  -- Optional displacement; TODO: parse ConstExpr generally
  let disp ← (do let i ← parseInt; pure (.Int64 (Int64.ofInt i))) <|> parseLabel <|> pure (.Int64 0)
  let _ ← pchar '('

  skipHWs
  let base ← parseRegOrRipW
  -- Check for index register
  let idx ← (do
    skipHWs
    let _ ← pchar ','
    skipHWs
    let r ← parseRegW
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
  let idx := Option.map (fun idx => ⟨idx, scale⟩) idx
  pure ({ base, idx, disp })

def parseImm w : Parser (Operand w) := do
  skipHWs
  let c ← peek!
  let i ←
    match c with
    | '$' => parseInt64
    | _ => parseLabel
  pure (.imm i)

-- We need to eagerly parse (to move through the syntax), but we may need to
-- defer choosing a width for those operands that are untyped (as in: may have
-- any width).
def MaybeTyped (T: Width → Type) :=
  Σ (w: Option Width), match w with | .some w => T w | .none => { w: Width } → T w

/-- Parse any operand: register, immediate, or memory. -/
def parseOperand: Parser (MaybeTyped Operand) := do
  skipHWs
  let c ← peek!
  match c with
  | '%' =>
    let ⟨ w, r ⟩ ← parseRegW
    pure ⟨ w, .reg r ⟩
  | '$' =>
    let i ← parseInt64
    pure ⟨ .none, .imm i ⟩
  | _ =>
    if c == '(' || c == '-' || c.isDigit then
      let m ← parseMemory
      pure ⟨ .none, .mem m ⟩
    else
      let i ← parseLabel
      pure ⟨ .none, .imm i ⟩

/-- Parse a register or memory operand (not immediate). -/
def parseRegOrMem: Parser (MaybeTyped RegOrMem) := do
  skipHWs
  let c ← peek!
  if c == '%' then
    let ⟨ w, r ⟩ ← parseRegW
    pure ⟨ .some w, (.Reg r) ⟩
  else if c == '(' || c == '-' || c.isDigit then
    let m ← parseMemory
    pure ⟨ .none, .mem m ⟩
  else
    fail s!"expected register or memory operand, got {c}"

def parseRelRegOrMem: Parser RelRegOrMem := do
  skipHWs
  (do
    let ⟨ w, r ⟩ ← parseRegW
    if h: w = .W64 then
      pure (.Reg (h ▸ r))
    else
      fail "expected a 64-bit register in relative addressing position"
  ) <|> (do
    -- FIXME: allow more cases in the syntax; for now, we only parse labels, and
    -- assume that all jumps are relative, in that this seems to be the behavior
    -- of the assembler
    let e ← parseLabel
    pure (.Rel (.sub e .after_current_instruction))
  ) <|> (do
    let m ← parseMemory
    pure (.mem m)
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

/-- Parse a comma separator. -/
def parseComma : Parser Unit := do
  skipHWs
  let _ ← pchar ','
  skipHWs

def ascribe {T: Width → Type} (w: Width) (v: MaybeTyped T): Parser (T w) := do
  match v with
  | ⟨ .none, v ⟩ => pure v
  | ⟨ .some w2, v ⟩ =>
    if h: w = w2 then
      pure (h ▸ v)
    else
      fail s!"type error: {w} != {w2}"

def ascribeOrInfer {T1 T2} (op1: MaybeTyped T1) (next: Parser (MaybeTyped T2)): Parser (Σ w, T1 w × T2 w) := do
  let op2 ← next
  match op1 with
  | ⟨ .some w1, op1 ⟩ =>
    let op2 ← ascribe w1 op2
    pure ⟨ w1, op1, op2 ⟩
  | ⟨ .none, op1 ⟩ =>
    match op2 with
    | ⟨ .some w2, op2 ⟩ =>
      pure ⟨ w2, op1, op2 ⟩
    | ⟨ .none, _ ⟩ =>
      fail "missing type annotation"

def parseWithType {T1} (op: Parser (MaybeTyped T1)) (w: Width): Parser (T1 w) := do
  let op ← op
  ascribe w op

def parseReg : Parser (MaybeTyped Reg) := do
  let p ← parseRegW; pure ⟨ .some p.1, p.2 ⟩
def parseRegWithType := parseWithType parseReg
def parseOperandWithType := parseWithType parseOperand
def parseRegOrMemWithType := parseWithType parseRegOrMem

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

def commaSeparated {T1 T2} (w: Option Width) (p1: Parser (MaybeTyped T1)) (p2: Parser (MaybeTyped T2))
  (mk: {w: Width} → T2 w → T1 w → Operation w): Parser Instr := do
    match w with
    | .none =>
      let src ← p1
      parseComma
      let ⟨ w, src, dst ⟩ ← ascribeOrInfer src p2
      pure ⟨ .W64, w, mk dst src ⟩
    | .some w =>
      let src ← parseWithType p1 w
      parseComma
      let dst ← parseWithType p2 w
      -- flip the direction here
      pure ⟨ .W64, w, mk dst src ⟩

def assertW {T} (v: MaybeTyped T): Parser (Σ w: Width, T w) :=
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
    commaSeparated .none parseRegOrMem parseReg .adcx

  | "adcxq" | "adcxl" =>
    let w ← instrWidth mn
    commaSeparated w parseRegOrMem parseReg .adcx

  | "adox" =>
    -- Per Intel SDM: ADOX dest must be a register (r32/r64)
    commaSeparated .none parseRegOrMem parseReg .adox

  | "adoxq" | "adoxl" =>
    let w ← instrWidth mn
    commaSeparated w parseRegOrMem parseReg .adox

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
    let src ← parseRegOrMem
    let ⟨ w, src ⟩ ← assertW src
    pure ⟨ .W64, w, .mul src ⟩

  | "mulq" | "mull" | "mulw" | "mulb" =>
    let w ← instrWidth mn
    let src ← parseRegOrMemWithType w
    pure ⟨ .W64, w, .mul src ⟩

  | "mulx" =>
    -- Per Intel SDM: MULX dest1 and dest2 must be registers
    -- mulxq src, lo, hi (AT&T: src → rdx*src, result in lo:hi)
    let src ← parseRegOrMem; parseComma
    let lo ← parseRegW; parseComma
    let hi ← parseRegW
    match src, lo, hi with
    | ⟨ .none, src ⟩, ⟨ w1, lo ⟩, ⟨ w2, hi ⟩ =>
      if h: w1 = w2 then
        pure ⟨ .W64, w1, .mulx (h ▸ hi) lo src ⟩
      else
        fail "mulx not homogenous"
    | ⟨ .some w3, src ⟩, ⟨ w1, lo ⟩, ⟨ w2, hi ⟩ =>
      if h: w1 = w2 then
        let hi := h ▸ hi
        if h: w1 = w3 then
          let src := h ▸ src
          pure ⟨ .W64, w1, .mulx hi lo src ⟩
        else
          fail "mulx not homogenous"
      else
        fail "mulx not homogenous"

  | "mulxq" | "mulxl" =>
    let w ← instrWidth mn
    let src ← parseRegOrMemWithType w; parseComma
    let lo ← parseRegWithType w; parseComma
    let hi ← parseRegWithType w
    pure ⟨ .W64, w, .mulx hi lo src ⟩

  | "imul" =>
    let src1 ← parseOperand; parseComma;
    (do
      let src2 ← parseRegOrMem; parseComma
      let ⟨ w, src2, dst ⟩ ← ascribeOrInfer src2 parseReg
      let src1 ← match src1 with
        | ⟨ .none, src1 ⟩ => pure src1
        | ⟨ .some w1, src1 ⟩ => if h: w1 = w then pure (h ▸ src1) else fail "type mismatch in imul"
      pure ⟨ .W64, w, .imul (.some dst) src2 src1 ⟩
    ) <|> (do
      let ⟨ w, src1, src2 ⟩ ← ascribeOrInfer src1 parseRegOrMem; parseComma
      pure ⟨ .W64, w, .imul .none src2 src1 ⟩
    )

  | "imulq" | "imull" | "imulw" | "imulb" =>
    let w ← instrWidth mn
    let src1 ← parseOperandWithType w; parseComma
    (do
      let src2 ← parseRegOrMemWithType w; parseComma
      let dst ← parseRegWithType w
      pure ⟨ .W64, w, .imul (.some dst) src2 src1 ⟩
    ) <|>
    (do
      let src2 ← parseRegOrMemWithType w; parseComma
      pure ⟨ .W64, w, .imul none src2 src1 ⟩
    )

  | "neg" =>
    let dst ← parseRegOrMem
    let ⟨ w, dst ⟩ ← assertW dst
    pure ⟨ .W64, w, .neg dst ⟩

  | "negq" | "negl" | "negw" | "negb" =>
    let w ← instrWidth mn
    let dst ← parseRegOrMemWithType w
    pure ⟨ .W64, w, .neg dst ⟩

  | "dec" =>
    let dst ← parseRegOrMem
    let ⟨ w, dst ⟩ ← assertW dst
    pure ⟨ .W64, w, .dec dst ⟩

  | "decq" | "decl" | "decw" | "decb" =>
    let w ← instrWidth mn
    let dst ← parseRegOrMemWithType w
    pure ⟨ .W64, w, .dec dst ⟩

  | "mov" | "movabs" =>
    commaSeparated .none parseOperand parseRegOrMem .mov

  | "movq" | "movl" | "movw" | "movb"
  | "movabsq" | "movabsl" | "movabsw" | "movabsb" =>
    let w ← instrWidth mn
    commaSeparated w parseOperand parseRegOrMem .mov

  | "moszx" =>
    -- Must be a register otherwise lacking type info
    let ⟨ _w_src, src ⟩ ← parseRegW
    let ⟨ w_dst, dst ⟩ ← parseRegW
    pure ⟨ .W64, w_dst, .movsx dst (.Reg src) ⟩

  | "movzx" =>
    -- Must be a register otherwise lacking type info
    let ⟨ _w_src, src ⟩ ← parseRegW
    let ⟨ w_dst, dst ⟩ ← parseRegW
    pure ⟨ .W64, w_dst, .movzx dst (.Reg src) ⟩

  | "movsbw" | "movsbl" | "movsbq" | "movswl" | "movswq" =>
    let w_dst ← instrWidth mn
    let c_src ← String.Pos.Raw.get? mn (.mk (mn.length - 2))
    let w_src ← Char.toWidth c_src
    let src ← parseRegWithType w_src
    let dst ← parseRegWithType w_dst
    pure ⟨ .W64, w_dst, .movzx dst (.Reg src) ⟩

  | "movzbw" | "movzbl" | "movzbq" | "movzwl" | "movzwq" =>
    let w_dst ← instrWidth mn
    let c_src ← String.Pos.Raw.get? mn (.mk (mn.length - 2))
    let w_src ← Char.toWidth c_src
    let src ← parseRegWithType w_src
    let dst ← parseRegWithType w_dst
    pure ⟨ .W64, w_dst, .movzx dst (.Reg src) ⟩

  | "lea" =>
    let src ← parseMemory; parseComma
    let ⟨ w, dst ⟩ ← parseRegW
    pure ⟨ .W64, w, .lea dst src ⟩

  | "leaq" | "leal" | "leaw" | "leab" =>
    let w2 ← instrWidth mn
    let src ← parseMemory; parseComma
    let ⟨ w, dst ⟩ ← parseRegW
    if w2 ≠ w then
      fail "inconsistency in {mn}"
    else
      pure ⟨ .W64, w, .lea dst src ⟩

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
    let parseOptionalShiftAndComma := (attempt do let cnt ← parseShiftExpr; parseComma; pure cnt) <|> pure (.imm8 (.Int64 1))
    let cnt ← parseOptionalShiftAndComma
    let dst ← parseRegOrMem
    let ⟨ w, dst ⟩ ← assertW dst
    pure ⟨ .W64, w, .shl dst cnt ⟩

  | "shlq" | "shll" | "shlw" | "shlb"
  | "salq" | "sall" | "salw" | "salb" =>
    let w ← instrWidth mn
    let parseOptionalShiftAndComma := (attempt do let cnt ← parseShiftExpr; parseComma; pure cnt) <|> pure (.imm8 (.Int64 1))
    let cnt ← parseOptionalShiftAndComma
    let dst ← parseRegOrMemWithType w
    pure ⟨ .W64, w, .shl dst cnt ⟩

  | "shr" =>
    let parseOptionalShiftAndComma := (attempt do let cnt ← parseShiftExpr; parseComma; pure cnt) <|> pure (.imm8 (.Int64 1))
    let cnt ← parseOptionalShiftAndComma
    let dst ← parseRegOrMem
    let ⟨ w, dst ⟩ ← assertW dst
    pure ⟨ .W64, w, .shr dst cnt ⟩

  | "shrq" | "shrl" | "shrw" | "shrb" =>
    let w ← instrWidth mn
    let parseOptionalShiftAndComma := (attempt do let cnt ← parseShiftExpr; parseComma; pure cnt) <|> pure (.imm8 (.Int64 1))
    let cnt ← parseOptionalShiftAndComma
    let dst ← parseRegOrMemWithType w
    pure ⟨ .W64, w, .shr dst cnt ⟩

  | "sar" =>
    let parseOptionalShiftAndComma := (attempt do let cnt ← parseShiftExpr; parseComma; pure cnt) <|> pure (.imm8 (.Int64 1))
    let cnt ← parseOptionalShiftAndComma
    let dst ← parseRegOrMem
    let ⟨ w, dst ⟩ ← assertW dst
    pure ⟨ .W64, w, .sar dst cnt ⟩

  | "sarq" | "sarl" | "sarw" | "sarb" =>
    let w ← instrWidth mn
    let parseOptionalShiftAndComma := (attempt do let cnt ← parseShiftExpr; parseComma; pure cnt) <|> pure (.imm8 (.Int64 1))
    let cnt ← parseOptionalShiftAndComma
    let dst ← parseRegOrMemWithType w
    pure ⟨ .W64, w, .sar dst cnt ⟩

  | "shld" =>
    let cnt ← parseShiftExpr; parseComma
    commaSeparated .none parseReg parseRegOrMem (fun dst src => .shld dst src cnt)

  | "shldq" | "shldl" | "shldw" =>
    let w ← instrWidth mn
    let cnt ← parseShiftExpr; parseComma
    commaSeparated w parseReg parseRegOrMem (fun dst src => .shld dst src cnt)

  | "shrd" =>
    let cnt ← parseShiftExpr; parseComma
    commaSeparated .none parseReg parseRegOrMem (fun dst src => .shrd dst src cnt)

  | "shrdq" | "shrdl" | "shrdw" =>
    let w ← instrWidth mn
    let cnt ← parseShiftExpr; parseComma
    commaSeparated w parseReg parseRegOrMem (fun dst src => .shrd dst src cnt)

  -- Rotate instructions - 64-bit
  | "rol" =>
    let parseOptionalShiftAndComma := (attempt do let cnt ← parseShiftExpr; parseComma; pure cnt) <|> pure (.imm8 (.Int64 1))
    let cnt ← parseOptionalShiftAndComma
    let dst ← parseRegOrMem
    let ⟨ w, dst ⟩ ← assertW dst
    pure ⟨ .W64, w, .rol dst cnt ⟩

  | "rolq" | "roll" | "rolw" | "rolb" =>
    let w ← instrWidth mn
    let parseOptionalShiftAndComma := (attempt do let cnt ← parseShiftExpr; parseComma; pure cnt) <|> pure (.imm8 (.Int64 1))
    let cnt ← parseOptionalShiftAndComma
    let dst ← parseRegOrMemWithType w
    pure ⟨ .W64, w, .rol dst cnt ⟩

  | "ror" =>
    let parseOptionalShiftAndComma := (attempt do let cnt ← parseShiftExpr; parseComma; pure cnt) <|> pure (.imm8 (.Int64 1))
    let cnt ← parseOptionalShiftAndComma
    let dst ← parseRegOrMem
    let ⟨ w, dst ⟩ ← assertW dst
    pure ⟨ .W64, w, .ror dst cnt ⟩

  | "rorq" | "rorl" | "rorw" | "rorb" =>
    let w ← instrWidth mn
    let parseOptionalShiftAndComma := (attempt do let cnt ← parseShiftExpr; parseComma; pure cnt) <|> pure (.imm8 (.Int64 1))
    let cnt ← parseOptionalShiftAndComma
    let dst ← parseRegOrMemWithType w
    pure ⟨ .W64, w, .ror dst cnt ⟩

  -- Byte swap
  | "bswap" =>
    let ⟨ w, dst ⟩ ← parseRegW
    pure ⟨ .W64, w, .bswap dst ⟩

  | "bswapq" | "bswapl" =>
    let ⟨ w, dst ⟩ ← parseRegW
    let w2 ← instrWidth mn
    if w2 ≠ w then
      fail "inconsistency in {mn}"
    else
      pure ⟨ .W64, w, .bswap dst ⟩

  -- Stack operations
  | "push" =>
    let src ← parseOperand
    let ⟨ w, src ⟩ ← assertW src
    pure ⟨ .W64, w, .push src ⟩

  | "pushq" | "pushl" | "pushw" | "pushb" =>
    let w ← instrWidth mn
    let src ← parseOperandWithType w
    pure ⟨ .W64, w, .push src ⟩

  | "pop" =>
    let dst ← parseRegOrMem
    let ⟨ w, dst ⟩ ← assertW dst
    pure ⟨ .W64, w, .pop dst ⟩

  | "popq" | "popl" | "popw" | "popb" =>
    let w ← instrWidth mn
    let dst ← parseRegOrMemWithType w
    pure ⟨ .W64, w, .pop dst ⟩

  | "ret" | "retq" =>
    pure ⟨ .W64, .W64, .ret ⟩

  | "call" | "callq" =>
    let target ← parseRelRegOrMem
    pure ⟨ .W64, .W64, .call target ⟩

  -- Control flow - unconditional jump
  | "jmp" | "jmpq" =>
    let target ← parseRelRegOrMem
    pure ⟨ .W64, .W64, .jmp target ⟩

  | "nop" =>
    (do
      skipHWs
      let sz ← parseHexOrDec
      pure ⟨ .W64, .W64, .nop sz.toNat ⟩
    ) <|> (pure ⟨ .W64, .W64, .nop 0 ⟩)

  -- Control flow - conditional jumps
  | _ =>
    if mn.startsWith "j" then
      let cc ← parseCondCode (mn.drop 1)
      skipHWs
      let target ← parseLabelRaw
      pure ⟨ .W64, .W64, .jcc cc target ⟩
    else if mn.startsWith "set" then
      let cc ← parseCondCode (mn.drop 3)
      let dst ← parseRegOrMemWithType .W8
      pure ⟨ .W64, .W8, .setcc cc dst ⟩
    else if mn.startsWith "cmov" then
      -- TODO: are the suffixed variants really used here? do we truly need to
      -- handle cmovzb and the like? how many are there? we could conceivably
      -- just ignore it on the basis that the assembler will bail if there is
      -- something inconsistent like .cmovzb %rax %rbx
      let cc ← parseCondCode (mn.drop 4)
      commaSeparated .none parseRegOrMem parseReg (.cmovcc cc)
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

/-- Parse a single line: optional label, followed by optional instruction or directive.
    Returns a list of directives found on the line. -/
def parseLine : Parser (List Directive) := do
  skipHWs
  let c ← peek!
  -- Skip empty lines and comment-only lines
  if c == '\n' || c == '#' then
    if c == '#' then skipLineComment
    pure []
  else
    let label ← (attempt do
      let l ← parseLabelDecl
      pure (some (Directive.Label l))) <|> pure none
    skipHWs
    let instr ← (do
      let c ← peek!
      if c == '\n' || c == '#' then
        pure none
      else
        -- Try to parse a .align directive
        (do
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
          pure (some (Directive.Instr ⟨ .W64, .W64, .nopalign alignment.toNat pad ⟩))
        ) <|> (do
          let instr ← parseInstr
          pure (some (Directive.Instr instr)))
    ) <|> pure none
    match label, instr with
    | some l, some i => pure [l, i]
    | some l, none   => pure [l]
    | none,   some i => pure [i]
    | none,   none   => pure []

-- ============================================================================
-- Public API
-- ============================================================================

instance {T1} : Coe (ParseResult (List T1) (Sigma String.Pos)) (Except String (List T1)) where coe :=
  fun r => match r with
  | .success _ v => .ok v
  | .error _ .eof => .ok []
  | .error _ (.other msg) => .error msg

def parse (input: String): Except String Program := do
  let rawLines := (input.splitOn "\n")
  let (_, lines) ← rawLines.foldlM (fun (lineNum, acc) x => do
    match (parseLine ⟨ x, x.startPos ⟩ : Except String (List Directive)) with
    | .ok v => pure (lineNum + 1, v :: acc)
    | .error msg => .error s!"line {lineNum}: {msg}"
  ) ((1 : Nat), [])
  pure lines.reverse.flatten

/-- Parse an assembly string, panicking on failure (for use in #eval). -/
def parse! (input : String) : Program :=
  match parse input with
  | .ok prog => prog
  | .error msg => panic! s!"parse error: {msg}"

end Kraken.Parser
