/-
Kraken Parser - x86_64 AT&T Assembly Parser

Parses AT&T syntax assembly strings into Kraken's Program type.
Uses Lean's built-in Std.Internal.Parsec library.

Compatible with Lean 4.22.0+.
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

/-- Parse a signed integer (decimal or hex). -/
def parseInt : Parser Int := do
  skipHWs
  let neg ← (pchar '-' *> pure true) <|> pure false
  let val ← parseHexOrDec
  pure (if neg then -val else val)
where
  hexVal (c : Char) : Int :=
    if c >= '0' && c <= '9' then c.toNat - '0'.toNat
    else if c >= 'a' && c <= 'f' then c.toNat - 'a'.toNat + 10
    else c.toNat - 'A'.toNat + 10
  parseHexOrDec : Parser Int := do
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

abbrev RegW := Σ w, Reg w

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
  | _ => fail s!"unknown register: {name}"

end RegParsing

def TypedBy (w: Option Width) (T: Width → Type) :=
  match w with
  | .some w => T w
  | .none => Σ w, T w

def MaybeTyped (T: Width → Type) :=
  Σ w: Option Width,
  match w with
  | .some w => T w
  | .none => (w: Width) → T w

def MaybeTypedBy (w_in: Option Width) (T: Width → Type) :=
  match w_in with
  | .some w_in => T w_in
  | .none => MaybeTyped T

/-- Parse a register operand: %rax, %eax, %ax, %al, etc. -/
def parseRegWithWidth (w_in: Option Width) : Parser (TypedBy w_in Reg) := do
  skipHWs
  let _ ← pchar '%'
  let ⟨ w, r ⟩ ← parseRegNameW
  match w_in with
  | .some w_in =>
    if h: w = w_in then
      pure (h ▸ r)
    else
      fail s!"register r was expected to have size {w_in} but has size {w}"
  | .none =>
    pure ⟨ w, r ⟩

abbrev RegOrRipW := Σ w, RegOrRip w

def parseRegOrRipW : Parser RegOrRipW := do
  let r ← (do
    let ⟨ w, r ⟩ ← parseRegNameW
    pure ⟨ w, RegOrRip.Reg r ⟩
  ) <|> (do
    let _ ← pstring "%rip"
    pure ⟨ .W64, .Rip ⟩
  )
  pure r

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

def parseLabel : Parser ConstExpr := do
  let _ ← pchar '.'
  let n ← parseName
  pure (.Label n)

/-- Parse a memory operand (a.k.a. "address expression"): disp(%base), (%base,%idx,scale), etc. -/
def parseMemory : Parser AddrExpr := do
  skipHWs
  -- Optional displacement
  let disp ← parseInt64 <|> pure (.Int64 0)
  let _ ← pchar '('
  skipHWs
  let base ← parseRegOrRipW
  -- Check for index register
  let idx ← (do
    skipHWs
    let _ ← pchar ','
    skipHWs
    let r ← parseRegWithWidth .none
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
  let idx := Option.map (fun idx => (idx, scale)) idx
  pure ({ base, idx, disp })

def parseImm w : Parser (Operand w) := do
  skipHWs
  let c ← peek!
  let i ←
    match c with
    | '$' => parseInt64
    | '.' => parseLabel
    | _ => fail "not an immediate"
  pure (.imm i)

/-- Parse any operand: register, immediate, or memory. -/
def parseOperandWithWidth (w_in: Option Width): Parser (MaybeTypedBy w_in Operand) := do
  sorry
  /- skipHWs -/
  /- let c ← peek! -/
  /- match c with -/
  /- | '%' => -/
  /-   let ⟨ w, r ⟩ ← parseRegWithWidth w_in -/
  /-   pure (.Typed w (.reg r)) -/
  /- | '$' => -/
  /-   let i ← parseInt64 -/
  /-   pure (.Untyped fun _ => .imm i) -/
  /- | '.' => -/
  /-   let i ← parseLabel -/
  /-   pure (.Untyped fun _ => .imm i) -/
  /- | _ => -/
  /-   if c == '(' || c == '-' || c.isDigit then -/
  /-     let m ← parseMemory -/
  /-     pure (.Untyped fun _ => .mem m) -/
  /-   else -/
  /-     fail s!"expected operand, got '{c}'" -/

-- We are returning a lambda because otherwise the elaborator transforms the
-- `match w_in` into `match w_in, wp` which leads to type errors further down.
def findOut { T1 T2: Width → Type } (w_in: Option Width) (f: {w: Width} → T1 w → T2 w):
      TypedBy w_in T1 -> MaybeTypedBy w_in T2
:=
  match w_in with
  | .some _ => fun mp => f mp
  | .none => fun mp => ⟨ mp.1, (f mp.2) ⟩

/-- Parse a register or memory operand (not immediate). -/
def parseRegOrMem (w_in: Option Width): Parser (MaybeTypedBy w_in RegOrMem) := do
  skipHWs
  let c ← peek!
  if c == '%' then
    let rww ← parseRegWithWidth w_in
    pure (findOut w_in .Reg rww)
  else if c == '(' || c == '-' || c.isDigit then
    let m ← parseMemory
    match w_in with
    | .some w_in => pure (.mem m)
    | .none => pure ⟨ .none, fun _ => .mem m ⟩
  else
    fail "expected register or memory operand"

-- ============================================================================
-- Condition Code Parsing
-- ============================================================================

/-- Parse a condition code from a conditional jump mnemonic suffix. -/
def parseCondCode (suffix : String) : Except String CondCode :=
  match suffix.toLower with
  | "z" | "e" => .ok .z
  | "nz" | "ne" => .ok .nz
  | "b" | "c" | "nae" => .ok .b
  | "ae" | "nc" | "nb" => .ok .ae
  | "a" | "nbe" => .ok .a
  | "be" | "na" => .ok .be
  | _ => .error s!"unknown condition code: {suffix}"

-- ============================================================================
-- Instruction Parsing
-- ============================================================================

/-- Parse a comma separator. -/
def parseComma : Parser Unit := do
  skipHWs
  let _ ← pchar ','
  skipHWs

/- def ascribe {T: Width → Type} (w: Width) (v: MaybeTyped T): Parser (T w) := do -/
/-   match v with -/
/-   | .Untyped v => pure (v w) -/
/-   | .Typed w2 v => -/
/-     if h: w = w2 then -/
/-       pure (h ▸ v) -/
/-     else -/
/-       fail s!"type error: {w} != {w2}" -/

/- def ascribeOrInfer (op1: MaybeTyped T1) (next: Parser (MaybeTyped T2)): Parser (Σ w, T1 w × T2 w) := do -/
/-   let op2 ← next -/
/-   match op1 with -/
/-   | .Typed w1 op1 => -/
/-     let op2 ← ascribe w1 op2 -/ 
/-     pure ⟨ w1, op1, op2 ⟩ -/
/-   | .Untyped op1 => -/
/-     match op2 with -/
/-     | .Typed w2 op2 => -/
/-       pure ⟨ w2, op1 w2, op2 ⟩ -/
/-     | .Untyped _ => -/
/-       fail "missing type annotation" -/

/- def MaybeTypedBy.get (self: MaybeTypedBy w_in T1) (prev: MaybeTyped T2): -/
  

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
    let ⟨ w, src ⟩ ← parseOperandWithWidth .none
    let dst ← parseRegOrMem w
    match w with
    | .none =>
      let ⟨ w_dst, dst ⟩ := dst
      match w_dst with
      | .none => fail ""
      | .some w_dst =>
        pure ⟨ .W64, w_dst, .add dst (src w_dst)⟩
    | .some w =>
      pure ⟨ .W64, w, .add dst src ⟩

/-     let ⟨ w, src, dst ⟩ ← ascribeOrInfer src parseRegOrMem -/
/-     pure ⟨ .W64, w, .add dst src ⟩ -/
  /- | "addq" => -/
  /-   let src ← parseOperand -/
  /-   let src ← ascribe .W64 src -/
  /-   let dst ← parseRegOrMem -/
  /-   let dst ← ascribe .W64 dst -/
  /-   pure ⟨ .W64, .W64, .add dst src ⟩ -/
  | _ =>
    fail "TODO"
  /- | "adc" | "adcq" => do -/
  /-   let src ← parseOperand; parseComma; let dst ← parseReg -/
  /-   checkNoTwoMemory src dst -/
  /-   pure (.adc dst src) -/
  /- | "adcx" | "adcxq" => do -/
  /-   -- Per Intel SDM: ADCX dest must be a register (r32/r64) -/
  /-   let src ← parseRegOrMem; parseComma; let dst ← parseReg -/
  /-   pure (.adcx dst src) -/
  /- | "adox" | "adoxq" => do -/
  /-   -- Per Intel SDM: ADOX dest must be a register (r32/r64) -/
  /-   let src ← parseRegOrMem; parseComma; let dst ← parseReg -/
  /-   pure (.adox dst src) -/
  /- | "sub" | "subq" => do -/
  /-   let src ← parseOperand; parseComma; let dst ← parseReg -/
  /-   checkNoTwoMemory src dst -/
  /-   pure (.sub dst src) -/
  /- | "sbb" | "sbbq" => do -/
  /-   let src ← parseOperand; parseComma; let dst ← parseReg -/
  /-   checkNoTwoMemory src dst -/
  /-   pure (.sbb dst src) -/
  /- | "mul" | "mulq" => do -/
  /-   let src ← parseRegOrMem -/
  /-   -- Only 64-bit MUL is supported (mulb/mulw/mull have different semantics) -/
  /-   match src with -/
  /-   | .reg r => if r.width != .W64 then fail s!"mul only supports 64-bit operands, got {repr r}" -/
  /-   | _ => pure ()  -- Memory operands OK (assume 64-bit in 64-bit mode) -/
  /-   pure (.mul src) -/
  /- | "mulx" | "mulxq" => do -/
  /-   -- Per Intel SDM: MULX dest1 and dest2 must be registers -/
  /-   -- mulxq src, lo, hi (AT&T: src → rdx*src, result in lo:hi) -/
  /-   let src ← parseRegOrMem; parseComma -/
  /-   let lo ← parseReg; parseComma -/
  /-   let hi ← parseReg -/
  /-   pure (.mulx hi lo src) -/
  /- | "imul" | "imulq" => do -/
  /-   let src ← parseRegOrMem; parseComma; let dst ← parseRegOrMem -/
  /-   checkNoTwoMemory src dst -/
  /-   -- Only 64-bit IMUL is supported (two-operand form) -/
  /-   match dst with -/
  /-   | .reg r => if r.width != .W64 then fail s!"imul only supports 64-bit operands, got {repr r}" -/
  /-   | _ => pure () -/
  /-   pure (.imul dst src) -/
  /- | "neg" | "negq" => do -/
  /-   let dst ← parseRegOrMem -/
  /-   pure (.neg dst) -/
  /- | "dec" | "decq" => do -/
  /-   let dst ← parseRegOrMem -/
  /-   pure (.dec dst) -/

  /- -- Move/Load - 64-bit -/
  /- | "mov" | "movq" | "movabs" | "movabsq" => do -/
  /-   let src ← parseOperand; parseComma; let dst ← parseRegOrMem -/
  /-   checkNoTwoMemory src dst -/
  /-   pure (.mov dst src) -/
  /- | "movl" => do -/
  /-   let src ← parseOperand; parseComma; let dst ← parseRegOrMem -/
  /-   checkNoTwoMemory src dst -/
  /-   pure (.movl dst src) -/
  /- | "lea" | "leaq" => do -/
  /-   let src ← parseMemory; parseComma -/
  /-   let dst ← parseReg64 -/
  /-   pure (.lea dst src) -/

  /- -- Bitwise - 64-bit -/
  /- | "xor" | "xorq" => do -/
  /-   let src ← parseOperand; parseComma; let dst ← parseRegOrMem -/
  /-   checkNoTwoMemory src dst -/
  /-   pure (.xor dst src) -/
  /- | "and" | "andq" => do -/
  /-   let src ← parseOperand; parseComma; let dst ← parseRegOrMem -/
  /-   checkNoTwoMemory src dst -/
  /-   pure (.and dst src) -/
  /- | "or" | "orq" => do -/
  /-   let src ← parseOperand; parseComma; let dst ← parseRegOrMem -/
  /-   checkNoTwoMemory src dst -/
  /-   pure (.or dst src) -/

  /- -- Compare - 64-bit -/
  /- | "cmp" | "cmpq" => do -/
  /-   let src ← parseOperand; parseComma; let dst ← parseRegOrMem -/
  /-   checkNoTwoMemory src dst -/
  /-   pure (.cmp dst src) -/

  /- -- 32-bit compare variants -/
  /- | "cmpl" => do -/
  /-   let src ← parseOperand; parseComma; let dst ← parseRegOrMem -/
  /-   pure (.cmpl dst src) -/
  /- | "cmpb" => do -/
  /-   let src ← parseOperand; parseComma; let dst ← parseRegOrMem -/
  /-   pure (.cmpb dst src) -/

  /- -- Test (sets flags based on AND without storing result) -/
  /- | "test" | "testq" => do -/
  /-   let src ← parseOperand; parseComma; let dst ← parseRegOrMem -/
  /-   pure (.test dst src) -/

  /- -- Shift instructions - 64-bit -/
  /- | "shl" | "shlq" | "sal" | "salq" => do -/
  /-   let cnt ← parseOperand; parseComma; let dst ← parseRegOrMem -/
  /-   pure (.shl dst cnt) -/
  /- | "shll" | "sall" => do -/
  /-   let cnt ← parseOperand; parseComma; let dst ← parseRegOrMem -/
  /-   pure (.shll dst cnt) -/
  /- | "shr" | "shrq" => do -/
  /-   let cnt ← parseOperand; parseComma; let dst ← parseRegOrMem -/
  /-   pure (.shr dst cnt) -/
  /- | "shrl" => do -/
  /-   let cnt ← parseOperand; parseComma; let dst ← parseRegOrMem -/
  /-   pure (.shrl dst cnt) -/
  /- | "sar" | "sarq" => do -/
  /-   let cnt ← parseOperand; parseComma; let dst ← parseRegOrMem -/
  /-   pure (.sar dst cnt) -/
  /- | "shld" | "shldq" => do -/
  /-   -- shld %cl, %src, %dst (shift dst left, fill with src high bits) -/
  /-   let cnt ← parseOperand; parseComma -/
  /-   let src ← parseRegOrMem; parseComma -/
  /-   let dst ← parseRegOrMem -/
  /-   pure (.shld dst src cnt) -/
  /- | "shrd" | "shrdq" => do -/
  /-   let cnt ← parseOperand; parseComma -/
  /-   let src ← parseRegOrMem; parseComma -/
  /-   let dst ← parseRegOrMem -/
  /-   pure (.shrd dst src cnt) -/

  /- -- Rotate instructions - 64-bit -/
  /- | "rol" | "rolq" => do -/
  /-   let cnt ← parseOperand; parseComma; let dst ← parseRegOrMem -/
  /-   pure (.rol dst cnt) -/
  /- | "roll" => do -/
  /-   let cnt ← parseOperand; parseComma; let dst ← parseRegOrMem -/
  /-   pure (.roll dst cnt) -/
  /- | "ror" | "rorq" => do -/
  /-   let cnt ← parseOperand; parseComma; let dst ← parseRegOrMem -/
  /-   pure (.ror dst cnt) -/
  /- | "rorl" => do -/
  /-   let cnt ← parseOperand; parseComma; let dst ← parseRegOrMem -/
  /-   pure (.rorl dst cnt) -/

  /- -- Byte swap -/
  /- | "bswap" | "bswapq" => do -/
  /-   let dst ← parseReg -/
  /-   pure (.bswap dst) -/
  /- | "bswapl" => do -/
  /-   let dst ← parseReg -/
  /-   pure (.bswapl dst) -/

  /- -- 32-bit arithmetic -/
  /- | "addl" => do -/
  /-   let src ← parseOperand; parseComma; let dst ← parseRegOrMem -/
  /-   pure (.addl dst src) -/
  /- | "subl" => do -/
  /-   let src ← parseOperand; parseComma; let dst ← parseRegOrMem -/
  /-   pure (.subl dst src) -/
  /- | "negl" => do -/
  /-   let dst ← parseRegOrMem -/
  /-   pure (.negl dst) -/
  /- | "notl" => do -/
  /-   let dst ← parseRegOrMem -/
  /-   pure (.notl dst) -/
  /- | "decl" => do -/
  /-   let dst ← parseRegOrMem -/
  /-   pure (.decl dst) -/
  /- | "leal" => do -/
  /-   let src ← parseMemory; parseComma -/
  /-   let dst ← parseReg32 -/
  /-   pure (.leal dst src) -/

  /- -- 32-bit bitwise -/
  /- | "xorl" => do -/
  /-   let src ← parseOperand; parseComma; let dst ← parseRegOrMem -/
  /-   pure (.xorl dst src) -/
  /- | "andl" => do -/
  /-   let src ← parseOperand; parseComma; let dst ← parseRegOrMem -/
  /-   pure (.andl dst src) -/
  /- | "orl" => do -/
  /-   let src ← parseOperand; parseComma; let dst ← parseRegOrMem -/
  /-   pure (.orl dst src) -/

  /- -- Move variants - 16-bit -/
  /- | "movw" => do -/
  /-   let src ← parseOperand; parseComma; let dst ← parseRegOrMem -/
  /-   pure (.movw dst src) -/
  /- -- Zero-extending moves -/
  /- | "movzbl" => do -/
  /-   let src ← parseOperand; parseComma; let dst ← parseRegOrMem -/
  /-   pure (.movzbl dst src) -/
  /- | "movzbq" => do -/
  /-   let src ← parseOperand; parseComma; let dst ← parseRegOrMem -/
  /-   pure (.movzbq dst src) -/
  /- | "movzwl" => do -/
  /-   let src ← parseOperand; parseComma; let dst ← parseRegOrMem -/
  /-   pure (.movzwl dst src) -/

  /- -- Set byte on condition -/
  /- | "setc" | "setb" => do -/
  /-   let dst ← parseRegOrMem -/
  /-   pure (.setcc CondCode.c dst) -/
  /- | "setnc" | "setae" | "setnb" => do -/
  /-   let dst ← parseRegOrMem -/
  /-   pure (.setcc CondCode.nc dst) -/

  /- -- Conditional moves (64-bit only - non-q variants are 32-bit which we don't support) -/
  /- | "cmovcq" | "cmovbq" => do -/
  /-   let src ← parseRegOrMem; parseComma; let dst ← parseReg -/
  /-   pure (.cmovcc CondCode.c dst src) -/
  /- | "cmoveq" | "cmovzq" => do -/
  /-   let src ← parseRegOrMem; parseComma; let dst ← parseReg -/
  /-   pure (.cmovcc CondCode.z dst src) -/

  /- -- Stack operations -/
  /- | "push" => do -/
  /-   let src ← parseOperand -/
  /-   pure (.push src) -/
  /- | "pop" => do -/
  /-   let dst ← parseRegOrMem -/
  /-   pure (.pop dst) -/
  /- | "ret" | "retq" => -/
  /-   pure .ret -/

  /- -- Control flow - unconditional jump -/
  /- | "jmp" | "jmpq" => do -/
  /-   skipHWs -/
  /-   let target ← parseName -/
  /-   pure (.jmp target) -/

  /- -- Control flow - conditional jumps -/
  /- | _ => -/
  /-   if mn.startsWith "j" then do -/
  /-     match parseCondCode (mn.drop 1) with -/
  /-     | .ok cc => do -/
  /-       skipHWs -/
  /-       let target ← parseName -/
  /-       pure (.jcc cc target) -/
  /-     | .error msg => fail msg -/
  /-   else -/
  /-     fail s!"unsupported instruction: {mnemonic}" -/

-- ============================================================================
-- Label Parsing
-- ============================================================================

/-- Parse an optional label (name followed by colon).
    Uses attempt for proper backtracking if colon is not found. -/
def parseLabel : Parser (Option Label) := do
  skipHWs
  (attempt do
    let name ← parseName
    skipHWs
    let _ ← pchar ':'
    pure (some name)) <|> pure none

-- ============================================================================
-- Line and Program Parsing
-- ============================================================================

/-- Parse a single line: optional label, optional instruction.
    Returns None if the line is empty or comment-only. -/
def parseLine : Parser (Option (Option Label × Instr)) := do
  skipHWs
  let c ← peek!
  -- Skip empty lines and comment-only lines
  if c == '\n' || c == '#' then
    if c == '#' then skipLineComment
    pure none
  else
    -- Try to parse label
    let lbl ← parseLabel
    skipHWs
    let c2 ← peek!
    -- Check if there's an instruction after the label
    if c2 == '\n' || c2 == '#' then
      -- Label-only line (forward declaration) - not common, but handle it
      match lbl with
      | some l => fail s!"label '{l}' without instruction not supported"
      | none => pure none
    else
      let instr ← parseInstr
      pure (some (lbl, instr))

/-- Skip to the end of the current line. -/
def skipToEndOfLine : Parser Unit := do
  let _ ← many (satisfy fun c => c != '\n')
  let _ ← (pchar '\n' *> pure ()) <|> pure ()

/-- Parse multiple lines into a Program. -/
partial def parseProgramAux (acc : Program) : Parser Program := do
  skipHWs
  let done ← (eof *> pure true) <|> pure false
  if done then
    pure acc
  else
    let line ← parseLine
    skipToEndOfLine
    match line with
    | some entry => parseProgramAux (acc ++ [entry])
    | none => parseProgramAux acc

def parseProgram : Parser Program := parseProgramAux []

-- ============================================================================
-- Public API
-- ============================================================================

/-- Parse an assembly string into a Program.
    Returns an error message on failure. -/
def parse (input : String) : Except String Program :=
  match parseProgram input.mkIterator with
  | .success _ prog => .ok prog
  | .error _ msg => .error msg

/-- Parse an assembly string, panicking on failure (for use in #eval). -/
def parse! (input : String) : Program :=
  match parse input with
  | .ok prog => prog
  | .error msg => panic! s!"parse error: {msg}"

end Kraken.Parser

-- ============================================================================
-- Tests
-- ============================================================================

section Tests
open Kraken.Parser

-- Test: Simple instruction
#eval parse! "addq %rax, %rbx"
-- Expected: [(.none, .add (.reg .rbx) (.reg .rax))]

-- Test: Immediate operand
#eval parse! "movq $42, %rax"
-- Expected: [(.none, .mov (.reg .rax) (.imm 42))]

-- Test: Memory operand with displacement
#eval parse! "movq 8(%rsp), %rax"
-- Expected: [(.none, .mov (.reg .rax) (.mem .rsp .none 1 8))]

-- Test: Memory operand with index and scale
#eval parse! "movq (%rsi, %r15, 8), %rax"
-- Expected: [(.none, .mov (.reg .rax) (.mem .rsi (some .r15) 8 0))]

-- Test: Labeled instruction
#eval parse! "loop: addq $1, %rcx"
-- Expected: [(some "loop", .add (.reg .rcx) (.imm 1))]

-- Test: Conditional jump
#eval parse! "jnz loop"
-- Expected: [(.none, .jcc .nz "loop")]

-- Test: Multi-line program
#eval parse! "
  movq $0, %rax
loop:
  addq $1, %rax
  cmpq $10, %rax
  jne loop
"

-- Test: Negative immediate
#eval parse! "addq $-1, %rax"

-- Test: Hex immediate
#eval parse! "movq $0xff, %rax"

-- Test: mulx instruction
#eval parse! "mulxq %r8, %r9, %r10"

-- Test: xor for zeroing
#eval parse! "xorq %rax, %rax"

-- Test: lea with complex addressing
#eval parse! "leaq 16(%rbp, %rcx, 4), %rax"

end Tests
