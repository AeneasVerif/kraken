/-
Kraken - x86_64 Assembly Parser

Parses x86_64 AT&T syntax assembly into Kraken's Instr type.
Uses simple string parsing for Lean 4.22.0+ compatibility.
-/

import AsmInterp.Semantics
import Parsing.Config

namespace Parsing

-- ============================================================================
-- Simple String Parsing Utilities (4.22.0+ compatible)
-- ============================================================================

/-- Convert a list of characters to a string. -/
def charsToString (cs : List Char) : String :=
  cs.foldl (fun s c => s.push c) ""

/-- Trim leading and trailing whitespace from a string. -/
def trimStr (s : String) : String :=
  let chars := s.toList
  let trimLeft := chars.dropWhile (· ∈ [' ', '\t', '\r', '\n'])
  let trimRight := trimLeft.reverse.dropWhile (· ∈ [' ', '\t', '\r', '\n'])
  charsToString trimRight.reverse

/-- Check if list starts with prefix. -/
def listStartsWith (xs ys : List Char) : Bool :=
  match xs, ys with
  | _, [] => true
  | [], _ :: _ => false
  | x :: xs', y :: ys' => x == y && listStartsWith xs' ys'

/-- Check if string contains a substring. -/
def containsSub (s : String) (sub : String) : Bool :=
  go s.toList sub.toList
where
  go : List Char → List Char → Bool
    | _, [] => true
    | [], _ :: _ => false
    | x :: xs, ys =>
      if listStartsWith (x :: xs) ys then true
      else go xs ys

/-- Find index of character in string. -/
def findChar (s : String) (c : Char) : Option Nat :=
  s.toList.findIdx? (· == c)

/-- Take first n characters of a string. -/
def takeStr (s : String) (n : Nat) : String :=
  charsToString (s.toList.take n)

/-- Drop first n characters of a string. -/
def dropStr (s : String) (n : Nat) : String :=
  charsToString (s.toList.drop n)

/-- Split string by a character. -/
def splitByChar (s : String) (c : Char) : List String :=
  go s.toList [] []
where
  go : List Char → List Char → List String → List String
    | [], acc, result => result ++ [charsToString acc.reverse]
    | x :: xs, acc, result =>
      if x == c then go xs [] (result ++ [charsToString acc.reverse])
      else go xs (x :: acc) result

-- ============================================================================
-- Register Parsing
-- ============================================================================

/-- Parse a 64-bit register name. Returns none for unknown/unsupported registers. -/
def parseRegName (name : String) : Option Reg :=
  match name with
  | "%rax" | "%eax" | "%ax" | "%al" => some .rax
  | "%rbx" | "%ebx" | "%bx" | "%bl" => some .rbx
  | "%rcx" | "%ecx" | "%cx" | "%cl" => some .rcx
  | "%rdx" | "%edx" | "%dx" | "%dl" => some .rdx
  | "%rsi" | "%esi" | "%si" | "%sil" => some .rsi
  | "%rdi" | "%edi" | "%di" | "%dil" => some .rdi
  | "%rsp" | "%esp" | "%sp" | "%spl" => some .rsp
  | "%rbp" | "%ebp" | "%bp" | "%bpl" => some .rbp
  | "%r8"  | "%r8d"  | "%r8w"  | "%r8b"  => some .r8
  | "%r9"  | "%r9d"  | "%r9w"  | "%r9b"  => some .r9
  | "%r10" | "%r10d" | "%r10w" | "%r10b" => some .r10
  | "%r11" | "%r11d" | "%r11w" | "%r11b" => some .r11
  | "%r12" | "%r12d" | "%r12w" | "%r12b" => some .r12
  | "%r13" | "%r13d" | "%r13w" | "%r13b" => some .r13
  | "%r14" | "%r14d" | "%r14w" | "%r14b" => some .r14
  | "%r15" | "%r15d" | "%r15w" | "%r15b" => some .r15
  | _ => none

-- ============================================================================
-- Immediate Parsing
-- ============================================================================

/-- Parse a hex or decimal integer. -/
def parseIntStr (s : String) : Option Int :=
  let trimmed := trimStr s
  if trimmed.isEmpty then none
  else
    let (neg, rest) := if trimmed.startsWith "-" then (true, dropStr trimmed 1) else (false, trimmed)
    let value :=
      if rest.startsWith "0x" || rest.startsWith "0X" then
        -- Hex
        let hexPart := dropStr rest 2
        hexPart.toList.foldl (fun acc c =>
          match acc with
          | none => none
          | some n =>
            let digit := if c.isDigit then some (c.toNat - '0'.toNat)
              else if c >= 'a' && c <= 'f' then some (c.toNat - 'a'.toNat + 10)
              else if c >= 'A' && c <= 'F' then some (c.toNat - 'A'.toNat + 10)
              else none
            digit.map (n * 16 + ·)
        ) (some 0)
      else
        -- Decimal
        rest.toNat?
    value.map fun n => if neg then -(Int.ofNat n) else Int.ofNat n

/-- Parse an immediate operand (starts with $). -/
def parseImmediateOp (s : String) : Option (Int64 × ImmWidth) := do
  if !s.startsWith "$" then none
  let value ← parseIntStr (dropStr s 1)
  let width :=
    if value >= -128 && value <= 127 then ImmWidth.w8
    else if value >= -(2^31) && value < 2^31 then ImmWidth.w32
    else ImmWidth.w64
  some (Int64.ofInt value, width)

-- ============================================================================
-- Memory Operand Parsing
-- ============================================================================

/-- Parse a memory operand like: disp(%base), (%base,%idx,scale), etc. -/
def parseMemoryOp (s : String) : Option Operand := do
  -- Find the opening paren
  let parenIdx ← findChar s '('
  -- Displacement is everything before the paren
  let dispPart := trimStr (takeStr s parenIdx)
  let disp := if dispPart.isEmpty then 0 else (parseIntStr dispPart).getD 0
  -- Find closing paren
  let closeIdx ← findChar s ')'
  -- Extract contents between parens
  let inner := takeStr (dropStr s (parenIdx + 1)) (closeIdx - parenIdx - 1)
  let parts := splitByChar inner ','
  match parts with
  | [base] =>
    let reg ← parseRegName (trimStr base)
    some (.mem reg none 8 disp)
  | [base, idx] =>
    let baseReg ← parseRegName (trimStr base)
    let idxReg ← parseRegName (trimStr idx)
    some (.mem baseReg (some idxReg) 8 disp)
  | [base, idx, scale] =>
    let baseReg ← parseRegName (trimStr base)
    let idxReg ← parseRegName (trimStr idx)
    let scaleVal := (trimStr scale).toNat?.getD 8
    some (.mem baseReg (some idxReg) scaleVal disp)
  | _ => none

-- ============================================================================
-- Operand Parsing
-- ============================================================================

/-- Parse any operand (register, immediate, or memory). -/
def parseOperandStr (s : String) : Option Operand := do
  let trimmed := trimStr s
  if trimmed.startsWith "%" then
    -- Register
    let reg ← parseRegName trimmed
    some (.reg reg)
  else if trimmed.startsWith "$" then
    -- Immediate
    let (v, w) ← parseImmediateOp trimmed
    some (.imm v w)
  else
    -- Memory
    parseMemoryOp trimmed

-- ============================================================================
-- Instruction Parsing
-- ============================================================================

/-- Set of opcodes that indicate end of function. -/
def endOpcodes : List String := ["ret", "retq"]

/-- Check if an opcode is a SIMD/XMM instruction (unsupported). -/
def isSimdOpcode (op : String) : Bool :=
  op.startsWith "p" ||  -- pxor, pand, etc.
  op.startsWith "v" ||  -- vaddps, vmovdqa, etc.
  containsSub op "xmm" || containsSub op "ymm" || containsSub op "zmm" ||
  (op.startsWith "mov" && (containsSub op "dq" || containsSub op "ps" || containsSub op "pd"))

/-- Check if a line is a directive. -/
def isDirective (line : String) : Bool :=
  let trimmed := trimStr line
  trimmed.startsWith "." &&
  (trimmed.startsWith ".globl" ||
   trimmed.startsWith ".type" ||
   trimmed.startsWith ".align" ||
   trimmed.startsWith ".cfi_" ||
   trimmed.startsWith ".size" ||
   trimmed.startsWith ".text" ||
   trimmed.startsWith ".hidden" ||
   trimmed.startsWith ".extern" ||
   trimmed.startsWith ".section")

/-- Check if this line indicates end of function. -/
def isEndOfFunction (line : String) : Bool :=
  let trimmed := trimStr line
  trimmed.startsWith ".size" || trimmed == "ret" || trimmed == "retq" ||
  trimmed.startsWith "ret\t" || trimmed.startsWith "retq\t" ||
  trimmed.startsWith "ret " || trimmed.startsWith "retq "

/-- Structure representing a parsed line. -/
inductive ParsedLine
  | label (name : String)
  | instr (label : Option String) (i : Instr)
  | unsupported (opcode : String)
  | endOfFunction
  | skip  -- directive, empty, or comment
  deriving Repr

/-- Parse a two-operand instruction. In AT&T syntax: opcode src, dst. -/
def parseTwoOp (operands : String) (mkInstr : Operand → Operand → Instr) : Option Instr := do
  let commaIdx ← findChar operands ','
  let src := takeStr operands commaIdx
  let dst := dropStr operands (commaIdx + 1)
  let srcOp ← parseOperandStr src
  let dstOp ← parseOperandStr dst
  some (mkInstr dstOp srcOp)  -- Kraken uses dst, src order

/-- Parse a one-operand instruction. -/
def parseOneOp (operands : String) (mkInstr : Operand → Instr) : Option Instr := do
  let op ← parseOperandStr operands
  some (mkInstr op)

/-- Parse a jump target (just a label name). -/
def parseJumpTarget (operands : String) (mkInstr : Label → Instr) : Option Instr :=
  let target := trimStr operands
  if target.isEmpty then none else some (mkInstr target)

/-- Parse a lea instruction: leaq src, %dst (dst must be register). -/
def parseLeaInstr (operands : String) : Option Instr := do
  let commaIdx ← findChar operands ','
  let src := takeStr operands commaIdx
  let dst := dropStr operands (commaIdx + 1)
  let srcOp ← parseMemoryOp (trimStr src)
  let dstReg ← parseRegName (trimStr dst)
  some (.lea dstReg srcOp)

/-- Parse a mulx instruction: mulxq src, lo, hi. -/
def parseMulxInstr (operands : String) : Option Instr := do
  let parts := splitByChar operands ','
  match parts with
  | [src, lo, hi] =>
    let srcOp ← parseOperandStr src
    let loOp ← parseOperandStr lo
    let hiOp ← parseOperandStr hi
    some (.mulx hiOp loOp srcOp)
  | _ => none

/-- Parse an instruction given opcode and operands. -/
def parseInstr (opcode : String) (operands : String) : Option Instr :=
  match opcode with
  -- Arithmetic (two operand)
  | "addq" => parseTwoOp operands .add
  | "adcq" => parseTwoOp operands .adc
  | "adcxq" => parseTwoOp operands .adcx
  | "adoxq" => parseTwoOp operands .adox
  | "subq" => parseTwoOp operands .sub
  | "sbbq" => parseTwoOp operands .sbb
  | "imulq" => parseTwoOp operands .imul
  -- Arithmetic (one operand)
  | "mulq" => parseOneOp operands .mul
  | "negq" => parseOneOp operands .neg
  | "decq" => parseOneOp operands .dec
  -- Move/Load
  | "movq" | "movl" => parseTwoOp operands .mov
  | "leaq" => parseLeaInstr operands
  | "mulxq" => parseMulxInstr operands
  -- Bitwise
  | "xorq" => parseTwoOp operands .xor
  | "andq" => parseTwoOp operands .and
  | "orq" => parseTwoOp operands .or
  -- Compare
  | "cmpq" => parseTwoOp operands .cmp
  -- Jumps
  | "jmp" => parseJumpTarget operands .jmp
  | "jz" | "je" => parseJumpTarget operands .jz
  | "jnz" | "jne" => parseJumpTarget operands .jnz
  | "jb" | "jc" => parseJumpTarget operands .jb
  | "jae" | "jnc" => parseJumpTarget operands .jae
  | "ja" => parseJumpTarget operands .ja
  | _ => none

-- ============================================================================
-- Line Parsing
-- ============================================================================

/-- Parse a single line of assembly. -/
def parseLine (line : String) (config : ParseConfig) : Except String ParsedLine := do
  let trimmed := trimStr line
  -- Empty or comment
  if trimmed.isEmpty || trimmed.startsWith "//" || trimmed.startsWith "#" then
    return ParsedLine.skip
  -- Directive
  if isDirective trimmed then
    return ParsedLine.skip
  -- End of function
  if isEndOfFunction trimmed then
    return ParsedLine.endOfFunction
  -- Try to parse as label (ends with : but not in middle of instruction)
  if let some colonIdx := findChar trimmed ':' then
    let beforeColon := takeStr trimmed colonIdx
    let afterColon := trimStr (dropStr trimmed (colonIdx + 1))
    if beforeColon.all (fun c => c.isAlpha || c.isDigit || c == '_' || c == '.') then
      if afterColon.isEmpty then
        return ParsedLine.label beforeColon
      -- Label with instruction on same line
      let parts := afterColon.splitOn "\t"
      if parts.length >= 1 then
        let opcode := trimStr parts[0]!
        let operands := if parts.length > 1 then parts[1]! else ""
        if isSimdOpcode opcode then
          if config.skipUnsupported then return ParsedLine.unsupported opcode
          else throw s!"unsupported SIMD instruction: {opcode}"
        match parseInstr opcode operands with
        | some instr => return ParsedLine.instr (some beforeColon) instr
        | none =>
          if config.skipUnsupported then return ParsedLine.unsupported opcode
          else throw s!"unsupported instruction: {opcode}"
  -- Parse as instruction
  let parts := trimmed.splitOn "\t"
  if parts.length == 0 then return ParsedLine.skip
  let opcode := trimStr parts[0]!
  let operands := if parts.length > 1 then parts[1]! else ""
  -- Check for end opcodes
  if endOpcodes.contains opcode then
    return ParsedLine.endOfFunction
  -- Check for SIMD/unsupported
  if isSimdOpcode opcode then
    if config.skipUnsupported then return ParsedLine.unsupported opcode
    else throw s!"unsupported SIMD instruction: {opcode}"
  -- Parse the instruction
  match parseInstr opcode operands with
  | some instr => return ParsedLine.instr none instr
  | none =>
    if config.skipUnsupported then return ParsedLine.unsupported opcode
    else throw s!"unsupported instruction: {opcode}"

-- ============================================================================
-- Function Extraction
-- ============================================================================

/-- Parse a complete function from assembly text, extracting instructions from
    startLabel until ret or .size directive. -/
def parseFunction (text : String) (startLabel : String) (config : ParseConfig := {}) :
    Except String Program := do
  let lines := text.splitOn "\n"
  let mut inFunction := false
  let mut program : Program := []
  let mut currentLabel : Option Label := none

  for line in lines do
    match parseLine line config with
    | .ok (ParsedLine.label name) =>
      if name == startLabel then
        inFunction := true
      if inFunction then
        currentLabel := some name
    | .ok (ParsedLine.instr labelOpt instr) =>
      if inFunction then
        let lbl := labelOpt <|> currentLabel
        program := program ++ [(lbl, instr)]
        currentLabel := none
    | .ok ParsedLine.endOfFunction =>
      if inFunction then
        break
    | .ok (ParsedLine.unsupported _) =>
      -- Skip unsupported instructions
      pure ()
    | .ok ParsedLine.skip =>
      pure ()
    | .error e =>
      if inFunction then
        throw e
      -- Outside target function, skip errors

  if program.isEmpty then
    throw s!"function '{startLabel}' not found or empty"
  return program

end Parsing
