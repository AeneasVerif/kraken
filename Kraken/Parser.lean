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
  pure (String.mk (#[first] ++ rest).toList)

-- ============================================================================
-- Register Parsing
-- ============================================================================

/-- Parse a register name. Returns the Reg (may be an alias like eax, ax, al). -/
def parseRegName : Parser Reg := do
  let name ← parseName
  match name.toLower with
  -- 64-bit registers
  | "rax" => pure .rax | "rbx" => pure .rbx | "rcx" => pure .rcx | "rdx" => pure .rdx
  | "rsi" => pure .rsi | "rdi" => pure .rdi | "rsp" => pure .rsp | "rbp" => pure .rbp
  | "r8"  => pure .r8  | "r9"  => pure .r9  | "r10" => pure .r10 | "r11" => pure .r11
  | "r12" => pure .r12 | "r13" => pure .r13 | "r14" => pure .r14 | "r15" => pure .r15
  -- 32-bit aliases
  | "eax" => pure .eax | "ebx" => pure .ebx | "ecx" => pure .ecx | "edx" => pure .edx
  | "esi" => pure .esi | "edi" => pure .edi | "esp" => pure .esp | "ebp" => pure .ebp
  | "r8d"  => pure .r8d  | "r9d"  => pure .r9d  | "r10d" => pure .r10d | "r11d" => pure .r11d
  | "r12d" => pure .r12d | "r13d" => pure .r13d | "r14d" => pure .r14d | "r15d" => pure .r15d
  -- 16-bit aliases
  | "ax" => pure .ax | "bx" => pure .bx | "cx" => pure .cx | "dx" => pure .dx
  | "si" => pure .si | "di" => pure .di | "sp" => pure .sp | "bp" => pure .bp
  | "r8w"  => pure .r8w  | "r9w"  => pure .r9w  | "r10w" => pure .r10w | "r11w" => pure .r11w
  | "r12w" => pure .r12w | "r13w" => pure .r13w | "r14w" => pure .r14w | "r15w" => pure .r15w
  -- 8-bit aliases
  | "al" => pure .al | "bl" => pure .bl | "cl" => pure .cl | "dl" => pure .dl
  | "sil" => pure .sil | "dil" => pure .dil | "spl" => pure .spl | "bpl" => pure .bpl
  | "r8b"  => pure .r8b  | "r9b"  => pure .r9b  | "r10b" => pure .r10b | "r11b" => pure .r11b
  | "r12b" => pure .r12b | "r13b" => pure .r13b | "r14b" => pure .r14b | "r15b" => pure .r15b
  | _ => fail s!"unknown register: {name}"

/-- Parse a register operand: %rax, %eax, %ax, %al, etc. -/
def parseReg : Parser Reg := do
  skipHWs
  let _ ← pchar '%'
  parseRegName

/-- Parse a register, requiring 64-bit. -/
def parseReg64 : Parser Reg := do
  let r ← parseReg
  if r.width != .W64 then fail "expected 64-bit register"
  else pure r

/-- Parse a register, requiring 32-bit. -/
def parseReg32 : Parser Reg := do
  let r ← parseReg
  if r.width != .W32 then fail "expected 32-bit register"
  else pure r

-- ============================================================================
-- Operand Parsing
-- ============================================================================

/-- Parse an immediate operand: $42, $-17, $0xff.
    Accepts any 64-bit value (0 to 2^64-1) as a bit pattern.
    Values like $0xFFFFFFFFFFFFFFFF are interpreted as -1 in two's complement. -/
def parseImm : Parser Operand := do
  skipHWs
  let _ ← pchar '$'
  let v ← parseInt
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
  pure (.imm i64)

/-- Parse a memory operand: disp(%base), (%base,%idx,scale), etc. -/
def parseMemory : Parser Operand := do
  skipHWs
  -- Optional displacement
  let disp ← parseInt <|> pure 0
  let _ ← pchar '('
  skipHWs
  let base ← parseReg64
  -- Check for index register
  let idx ← (do
    skipHWs
    let _ ← pchar ','
    skipHWs
    let r ← parseReg64
    pure (some r)) <|> pure none
  -- Check for scale
  let scale ← match idx with
    | some _ => (do
        skipHWs
        let _ ← pchar ','
        skipHWs
        let s ← parseInt
        if s != 1 && s != 2 && s != 4 && s != 8 then
          fail s!"invalid scale {s}, must be 1, 2, 4, or 8"
        pure s.toNat) <|> pure 1
    | none => pure 1
  skipHWs
  let _ ← pchar ')'
  pure (.mem base idx scale disp)

/-- Parse any operand: register, immediate, or memory. -/
def parseOperand : Parser Operand := do
  skipHWs
  let c ← peek!
  if c == '%' then
    let r ← parseReg
    pure (.reg r)
  else if c == '$' then
    parseImm
  else if c == '(' || c == '-' || c.isDigit then
    parseMemory
  else
    fail s!"expected operand, got '{c}'"

/-- Parse a register or memory operand (not immediate). -/
def parseRegOrMem : Parser Operand := do
  skipHWs
  let c ← peek!
  if c == '%' then
    let r ← parseReg
    pure (.reg r)
  else if c == '(' || c == '-' || c.isDigit then
    parseMemory
  else
    fail "expected register or memory operand"

/-- Parse a register operand (as Operand type). -/
def parseRegOperand : Parser Operand := do
  let r ← parseReg64
  pure (.reg r)

/-- Check if operand is a memory operand. -/
def isMemory : Operand → Bool
  | .mem _ _ _ _ => true
  | _ => false

/-- Validate that we don't have two memory operands (illegal in x86). -/
def checkNoTwoMemory (src dst : Operand) : Parser Unit := do
  if isMemory src && isMemory dst then
    fail "x86 does not allow two memory operands in one instruction"
  else
    pure ()

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

/-- Parse an instruction mnemonic and its operands.
    AT&T syntax: src, dst (reversed from Intel). -/
def parseInstr : Parser Instr := do
  skipHWs
  let mnemonic ← parseName
  let mn := mnemonic.toLower
  -- Match on full mnemonic name (no suffix stripping)
  match mn with
  -- Arithmetic (two-operand: src, dst) - 64-bit
  | "add" | "addq" => do
    let src ← parseOperand; parseComma; let dst ← parseRegOrMem
    checkNoTwoMemory src dst
    pure (.add dst src)
  | "adc" | "adcq" => do
    let src ← parseOperand; parseComma; let dst ← parseRegOrMem
    checkNoTwoMemory src dst
    pure (.adc dst src)
  | "adcx" | "adcxq" => do
    -- Per Intel SDM: ADCX dest must be a register (r32/r64)
    let src ← parseRegOrMem; parseComma; let dst ← parseRegOperand
    pure (.adcx dst src)
  | "adox" | "adoxq" => do
    -- Per Intel SDM: ADOX dest must be a register (r32/r64)
    let src ← parseRegOrMem; parseComma; let dst ← parseRegOperand
    pure (.adox dst src)
  | "sub" | "subq" => do
    let src ← parseOperand; parseComma; let dst ← parseRegOrMem
    checkNoTwoMemory src dst
    pure (.sub dst src)
  | "sbb" | "sbbq" => do
    let src ← parseOperand; parseComma; let dst ← parseRegOrMem
    checkNoTwoMemory src dst
    pure (.sbb dst src)
  | "mul" | "mulq" => do
    let src ← parseRegOrMem
    -- Only 64-bit MUL is supported (mulb/mulw/mull have different semantics)
    match src with
    | .reg r => if r.width != .W64 then fail s!"mul only supports 64-bit operands, got {repr r}"
    | _ => pure ()  -- Memory operands OK (assume 64-bit in 64-bit mode)
    pure (.mul src)
  | "mulx" | "mulxq" => do
    -- Per Intel SDM: MULX dest1 and dest2 must be registers
    -- mulxq src, lo, hi (AT&T: src → rdx*src, result in lo:hi)
    let src ← parseRegOrMem; parseComma
    let lo ← parseRegOperand; parseComma
    let hi ← parseRegOperand
    pure (.mulx hi lo src)
  | "imul" | "imulq" => do
    -- Two-operand form: src can be immediate, register, or memory
    -- AT&T syntax: imul $imm, %reg OR imul %src, %dst
    let src ← parseOperand; parseComma; let dst ← parseRegOrMem
    checkNoTwoMemory src dst
    -- Only 64-bit IMUL is supported
    match dst with
    | .reg r => if r.width != .W64 then fail s!"imul only supports 64-bit operands, got {repr r}"
    | _ => pure ()
    pure (.imul dst src)
  | "neg" | "negq" => do
    let dst ← parseRegOrMem
    pure (.neg dst)
  | "dec" | "decq" => do
    let dst ← parseRegOrMem
    pure (.dec dst)

  -- Move/Load - 64-bit
  | "mov" | "movq" | "movabs" | "movabsq" => do
    let src ← parseOperand; parseComma; let dst ← parseRegOrMem
    checkNoTwoMemory src dst
    pure (.mov dst src)
  | "movl" => do
    let src ← parseOperand; parseComma; let dst ← parseRegOrMem
    checkNoTwoMemory src dst
    pure (.movl dst src)
  | "lea" | "leaq" => do
    let src ← parseMemory; parseComma
    let dst ← parseReg64
    pure (.lea dst src)

  -- Bitwise - 64-bit
  | "xor" | "xorq" => do
    let src ← parseOperand; parseComma; let dst ← parseRegOrMem
    checkNoTwoMemory src dst
    pure (.xor dst src)
  | "and" | "andq" => do
    let src ← parseOperand; parseComma; let dst ← parseRegOrMem
    checkNoTwoMemory src dst
    pure (.and dst src)
  | "or" | "orq" => do
    let src ← parseOperand; parseComma; let dst ← parseRegOrMem
    checkNoTwoMemory src dst
    pure (.or dst src)

  -- Compare - 64-bit
  | "cmp" | "cmpq" => do
    let src ← parseOperand; parseComma; let dst ← parseRegOrMem
    checkNoTwoMemory src dst
    pure (.cmp dst src)

  -- 32-bit compare variants
  | "cmpl" => do
    let src ← parseOperand; parseComma; let dst ← parseRegOrMem
    pure (.cmpl dst src)
  | "cmpb" => do
    let src ← parseOperand; parseComma; let dst ← parseRegOrMem
    pure (.cmpb dst src)

  -- Test (sets flags based on AND without storing result)
  | "test" | "testq" => do
    let src ← parseOperand; parseComma; let dst ← parseRegOrMem
    pure (.test dst src)
  | "testb" => do
    let src ← parseOperand; parseComma; let dst ← parseRegOrMem
    pure (.testb dst src)

  -- Shift instructions - 64-bit
  | "shl" | "shlq" | "sal" | "salq" => do
    -- Support both forms: shlq $count, %dst OR shlq %dst (implicit count=1)
    let first ← parseOperand
    let hasComma ← (attempt parseComma *> pure true) <|> pure false
    if hasComma then
      let dst ← parseRegOrMem
      pure (.shl dst first)
    else
      pure (.shl first (.imm 1))
  | "shll" | "sall" => do
    let first ← parseOperand
    let hasComma ← (attempt parseComma *> pure true) <|> pure false
    if hasComma then
      let dst ← parseRegOrMem
      pure (.shll dst first)
    else
      pure (.shll first (.imm 1))
  | "shr" | "shrq" => do
    -- Support both forms: shrq $count, %dst OR shrq %dst (implicit count=1)
    let first ← parseOperand
    let hasComma ← (attempt parseComma *> pure true) <|> pure false
    if hasComma then
      let dst ← parseRegOrMem
      pure (.shr dst first)
    else
      pure (.shr first (.imm 1))
  | "shrl" => do
    let first ← parseOperand
    let hasComma ← (attempt parseComma *> pure true) <|> pure false
    if hasComma then
      let dst ← parseRegOrMem
      pure (.shrl dst first)
    else
      pure (.shrl first (.imm 1))
  | "sar" | "sarq" => do
    -- Support both forms: sarq $count, %dst OR sarq %dst (implicit count=1)
    let first ← parseOperand
    let hasComma ← (attempt parseComma *> pure true) <|> pure false
    if hasComma then
      let dst ← parseRegOrMem
      pure (.sar dst first)
    else
      pure (.sar first (.imm 1))
  | "shld" | "shldq" => do
    -- shld %cl, %src, %dst (shift dst left, fill with src high bits)
    let cnt ← parseOperand; parseComma
    let src ← parseRegOrMem; parseComma
    let dst ← parseRegOrMem
    pure (.shld dst src cnt)
  | "shrd" | "shrdq" => do
    let cnt ← parseOperand; parseComma
    let src ← parseRegOrMem; parseComma
    let dst ← parseRegOrMem
    pure (.shrd dst src cnt)

  -- Rotate instructions - 64-bit
  | "rol" | "rolq" => do
    let cnt ← parseOperand; parseComma; let dst ← parseRegOrMem
    pure (.rol dst cnt)
  | "roll" => do
    let cnt ← parseOperand; parseComma; let dst ← parseRegOrMem
    pure (.roll dst cnt)
  | "ror" | "rorq" => do
    let cnt ← parseOperand; parseComma; let dst ← parseRegOrMem
    pure (.ror dst cnt)
  | "rorl" => do
    let cnt ← parseOperand; parseComma; let dst ← parseRegOrMem
    pure (.rorl dst cnt)

  -- Byte swap
  | "bswap" | "bswapq" => do
    let dst ← parseRegOrMem
    pure (.bswap dst)
  | "bswapl" => do
    let dst ← parseRegOrMem
    pure (.bswapl dst)

  -- 32-bit arithmetic
  | "addl" => do
    let src ← parseOperand; parseComma; let dst ← parseRegOrMem
    pure (.addl dst src)
  | "subl" => do
    let src ← parseOperand; parseComma; let dst ← parseRegOrMem
    pure (.subl dst src)
  | "negl" => do
    let dst ← parseRegOrMem
    pure (.negl dst)
  | "notl" => do
    let dst ← parseRegOrMem
    pure (.notl dst)
  | "decl" => do
    let dst ← parseRegOrMem
    pure (.decl dst)
  | "leal" => do
    let src ← parseMemory; parseComma
    let dst ← parseReg32
    pure (.leal dst src)

  -- 32-bit bitwise
  | "xorl" => do
    let src ← parseOperand; parseComma; let dst ← parseRegOrMem
    pure (.xorl dst src)
  | "andl" => do
    let src ← parseOperand; parseComma; let dst ← parseRegOrMem
    pure (.andl dst src)
  | "orl" => do
    let src ← parseOperand; parseComma; let dst ← parseRegOrMem
    pure (.orl dst src)

  -- Move variants - 16-bit
  | "movw" => do
    let src ← parseOperand; parseComma; let dst ← parseRegOrMem
    pure (.movw dst src)
  -- Zero-extending moves
  | "movzbl" => do
    let src ← parseOperand; parseComma; let dst ← parseRegOrMem
    pure (.movzbl dst src)
  | "movzbq" => do
    let src ← parseOperand; parseComma; let dst ← parseRegOrMem
    pure (.movzbq dst src)
  | "movzwl" => do
    let src ← parseOperand; parseComma; let dst ← parseRegOrMem
    pure (.movzwl dst src)

  -- Set byte on condition
  | "setc" | "setb" => do
    let dst ← parseRegOrMem
    pure (.setc dst)
  | "setnc" | "setae" | "setnb" => do
    let dst ← parseRegOrMem
    pure (.setnc dst)

  -- Conditional moves (64-bit only - non-q variants are 32-bit which we don't support)
  | "cmovcq" | "cmovbq" => do
    let src ← parseOperand; parseComma; let dst ← parseRegOrMem
    pure (.cmovc dst src)
  | "cmoveq" | "cmovzq" => do
    let src ← parseOperand; parseComma; let dst ← parseRegOrMem
    pure (.cmove dst src)

  -- Stack operations
  | "push" => do
    let src ← parseOperand
    pure (.push src)
  | "pop" => do
    let dst ← parseRegOrMem
    pure (.pop dst)
  | "ret" | "retq" =>
    pure .ret

  -- Control flow - unconditional jump
  | "jmp" | "jmpq" => do
    skipHWs
    let target ← parseName
    pure (.jmp target)

  -- Control flow - conditional jumps
  | _ =>
    if mn.startsWith "j" then do
      match parseCondCode (mn.drop 1) with
      | .ok cc => do
        skipHWs
        let target ← parseName
        pure (.jcc cc target)
      | .error msg => fail msg
    else
      fail s!"unsupported instruction: {mnemonic}"

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
      -- Label-only line: treat as "label: nop"
      -- NOTE: This is an imperfect fix. Ideally, standalone labels should be
      -- associated with the *next* instruction's address, not inserted as a separate
      -- nop instruction. However, this simple approach works for most cases where
      -- labels are just jump targets. The extra nop has no semantic effect beyond
      -- consuming one instruction slot.
      match lbl with
      | some l => pure (some (some l, .nop))
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

/-- Parse a single line of assembly (used internally with line tracking). -/
def parseSingleLine (line : String) : Except String (Option (Option Label × Instr)) :=
  if line.trim.isEmpty || line.trim.startsWith "#" then
    .ok none
  else
    match parseLine (line ++ "\n").mkIterator with
    | .success _ result => .ok result
    | .error _ msg => .error msg

/-- Parse an assembly string into a Program.
    Returns an error message with line number and content on failure. -/
def parse (input : String) : Except String Program :=
  let lines := input.splitOn "\n"
  parseLines lines 1 []
where
  parseLines (lines : List String) (lineNum : Nat) (acc : Program) : Except String Program :=
    match lines with
    | [] => .ok acc
    | line :: rest =>
      let trimmed := line.trim
      -- Skip empty lines and pure comment lines quickly
      if trimmed.isEmpty || trimmed.startsWith "#" then
        parseLines rest (lineNum + 1) acc
      else
        -- Try to parse the line
        match parseSingleLine line with
        | .ok none => parseLines rest (lineNum + 1) acc
        | .ok (some entry) => parseLines rest (lineNum + 1) (acc ++ [entry])
        | .error msg =>
            -- Include line number and content in error message
            let preview := if line.length > 60 then line.take 60 ++ "..." else line
            .error s!"line {lineNum}: {msg}\n  | {preview}"

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
