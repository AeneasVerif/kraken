/-
Kraken - x86_64 Assembly Parser Configuration

Configuration options for parsing x86_64 AT&T assembly files.
-/

namespace Parsing

/-- Configuration for the x86_64 assembly parser. -/
structure ParseConfig where
  /-- Target function to extract. If empty, extract all functions. -/
  targetFunction : Option String := none
  /-- If true, skip unsupported instructions instead of erroring. -/
  skipUnsupported : Bool := true
  deriving Repr, Inhabited

/-- Result of parsing a line. -/
inductive LineResult
  /-- A label definition (e.g., .Lloop:) -/
  | label (name : String)
  /-- A directive to skip (e.g., .globl, .type, .cfi_*) -/
  | directive
  /-- An instruction that was parsed successfully -/
  | instruction
  /-- An unsupported instruction (SIMD, etc.) -/
  | unsupported (opcode : String)
  /-- End of function marker (ret, .size directive) -/
  | endOfFunction
  /-- Empty line or comment -/
  | empty
  deriving Repr

end Parsing
