/-
  Parser Tests - Extracted from Parser.lean
  Uses #guard_msgs to verify parser output against expected results.
-/

import Kraken.Parser

section Tests
open Kraken.Parser

open Instr Operand Reg

-- Test: Simple instruction
/--
info: [Directive.instr
    (regular Width.W64 Width.W64
      (Operation.add ↑(low Reg64.rbx Width.W64) ↑↑(low Reg64.rax Width.W64)))] : List Directive
-/
#guard_msgs in
#check parse("addq %rax, %rbx")

-- Test: Immediate operand
/--
info: [Directive.instr (regular Width.W64 Width.W64 (Operation.mov ↑(low Reg64.rax Width.W64) ↑↑42))] : List Directive
-/
#guard_msgs in
#check parse("movq $42, %rax")
-- Expected: [.Instr { address_size := .W64, operation_size := .W64, operation := .mov (.Reg (.low .rax .W64)) (.imm 42) }]

-- Test: Memory operand with displacement
/--
info: [Directive.instr
    (regular Width.W64 Width.W64
      (Operation.mov ↑(low Reg64.rax Width.W64)
        ↑↑{ base := some (RegOrRip.reg Reg64.rsp), idx := none, disp := ↑8 }))] : List Directive
-/
#guard_msgs in
#check parse("movq 8(%rsp), %rax")
-- Expected: [.Instr { address_size := .W64, operation_size := .W64, operation := .mov (.Reg (.low .rax .W64)) (.mem .rsp .none 1 8) }]

-- Test: Memory operand with index and scale
/--
info: [Directive.instr
    (regular Width.W64 Width.W64
      (Operation.mov ↑(low Reg64.rax Width.W64)
        ↑↑{ base := some (RegOrRip.reg Reg64.rsi),
              idx := some { reg := Reg64.r15, scale := Width.W64 } }))] : List Directive
-/
#guard_msgs in
#check parse("movq (%rsi, %r15, 8), %rax")
-- Expected: [.Instr { address_size := .W64, operation_size := .W64, operation := .mov (.Reg (.low .rax .W64)) (.mem .rsi (some .r15) 8 0) }]

-- Test: Labeled instruction
/--
info: [Directive.label "loop",
  Directive.instr (regular Width.W64 Width.W64 (Operation.add ↑(low Reg64.rcx Width.W64) ↑↑1))] : List Directive
-/
#guard_msgs in
#check parse("loop: addq $1, %rcx")
-- Expected: [.Label "loop", .Instr { address_size := .W64, operation_size := .W64, operation := .add (.Reg (.low .rcx .W64)) (.imm 1) }]

-- Test: Conditional jump
/--
info: [Directive.instr (regular Width.W64 Width.W64 (Operation.jcc CondCode.nz "loop"))] : List Directive
-/
#guard_msgs in
#check parse("jnz loop")
-- Expected: [.Instr { address_size := .W64, operation_size := .W64, operation := .jcc .nz "loop" }]

-- Test: Multi-line program
/--
info: [Directive.instr (regular Width.W64 Width.W64 (Operation.mov ↑(low Reg64.rax Width.W64) ↑↑0)), Directive.label "loop",
  Directive.instr (regular Width.W64 Width.W64 (Operation.add ↑(low Reg64.rax Width.W64) ↑↑1)),
  Directive.instr (regular Width.W64 Width.W64 (Operation.cmp ↑(low Reg64.rax Width.W64) ↑↑10)),
  Directive.instr (regular Width.W64 Width.W64 (Operation.jcc CondCode.nz "loop"))] : List Directive
-/
#guard_msgs in
#check parse("
  movq $0, %rax
loop:
  addq $1, %rax
  cmpq $10, %rax
  jne loop
")

-- Test: Negative immediate
/--
info: [Directive.instr (regular Width.W64 Width.W64 (Operation.add ↑(low Reg64.rax Width.W64) ↑↑(-1)))] : List Directive
-/
#guard_msgs in
#check parse("addq $-1, %rax")

-- Test: Hex immediate
/--
info: [Directive.instr (regular Width.W64 Width.W64 (Operation.mov ↑(low Reg64.rax Width.W64) ↑↑255))] : List Directive
-/
#guard_msgs in
#check parse("movq $0xff, %rax")

-- Test: mulx instruction
/--
info: [Directive.instr
    (regular Width.W64 Width.W64
      (Operation.mulx (low Reg64.r10 Width.W64) (low Reg64.r9 Width.W64) ↑(low Reg64.r8 Width.W64)))] : List Directive
-/
#guard_msgs in
#check parse("mulxq %r8, %r9, %r10")

-- Test: xor for zeroing
/--
info: [Directive.instr
    (regular Width.W64 Width.W64
      (Operation.xor ↑(low Reg64.rax Width.W64) ↑↑(low Reg64.rax Width.W64)))] : List Directive
-/
#guard_msgs in
#check parse("xorq %rax, %rax")

-- Test: lea with complex addressing
/--
info: [Directive.instr
    (regular Width.W64 Width.W64
      (Operation.lea (low Reg64.rax Width.W64)
        { base := some (RegOrRip.reg Reg64.rbp), idx := some { reg := Reg64.rcx, scale := Width.W32 },
          disp := ↑16 }))] : List Directive
-/
#guard_msgs in
#check parse("leaq 16(%rbp, %rcx, 4), %rax")

/--
info: [Directive.instr
    (regular Width.W32 Width.W64
      (Operation.lea (low Reg64.rax Width.W64)
        { base := some (RegOrRip.reg Reg64.rbp), idx := some { reg := Reg64.rcx, scale := Width.W32 },
          disp := ↑16 }))] : List Directive
-/
#guard_msgs in
#check parse("leaq 16(%ebp, %ecx, 4), %rax")

section error_reporting

/-- error: line 1: unknown register: unlikely -/
#guard_msgs in
#check parse("xorq %rax, %unlikely")

/--
error: line 1: type mismatch in memory addressing operands: base ({w1}) and index ({w2}) have different widths
-/
#guard_msgs in
#check parse("mov (%rax, %ebx)")

/-- error: line 1: can't have two memory operands -/
#guard_msgs in
#check parse("mov (%rax), (%rax)")

/-- error: line 1: high byte register cannot be used for an addrexpr -/
#guard_msgs in
#check parse("mov $2, (%ah)")

/-- error: line 1: unexpected end of input -/
#guard_msgs in
#check parse("addq %rax")

/-- error: line 1: unexpected end of input -/
#guard_msgs in
#check parse("xorq %rax, 1")

/-- error: line 1: unexpected end of input -/
#guard_msgs in
#check parse("addq")

/-- error: line 2: unexpected end of input -/
#guard_msgs in
#check parse("
  addq %rax
  cmpq $10, %rax
")

/-- error: line 1: type error: w64 != w32 -/
#guard_msgs in
#check parse("movq %eax, %rbx")

/-- error: line 1: invalid scale 3, must be 1, 2, 4, or 8 -/
#guard_msgs in
#check parse("movq (%rax, %rcx, 3), %rbx")

/-- error: line 1: unexpected trailing characters on line -/
#guard_msgs in
#check parse("movq %rax, %rbx garbage")

end error_reporting

section broken

-- TODO: Support absolute memory addressing (bare displacements) and add reliable integration tests for it.
-- Currently, the parser requires '(' after displacement, so this fails to parse with "expected: '('".
-- Also, testing this on real x86 is tricky because we need a guaranteed mapped addresses.
/-- error: line 1: expected: '(' -/
#guard_msgs in
#check parse("movq 1, %rax")

end broken

end Tests
