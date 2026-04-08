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
info: [Directive.Instr
    { address_size := Width.W64, operation_size := Width.W64,
      operation := Operation.add ↑(low Reg64.rbx Width.W64) ↑↑(low Reg64.rax Width.W64) }]
-/
#guard_msgs in
#eval parse! "addq %rax, %rbx"

-- Test: Immediate operand
/--
info: [Directive.Instr
    { address_size := Width.W64, operation_size := Width.W64,
      operation := Operation.mov ↑(low Reg64.rax Width.W64) ↑↑42 }]
-/
#guard_msgs in
#eval parse! "movq $42, %rax"
-- Expected: [.Instr { address_size := .W64, operation_size := .W64, operation := .mov (.Reg (.low .rax .W64)) (.imm 42) }]

-- Test: Memory operand with displacement
/--
info: [Directive.Instr
    { address_size := Width.W64, operation_size := Width.W64,
      operation :=
        Operation.mov ↑(low Reg64.rax Width.W64)
          ↑↑{ base := some (RegOrRip.ofRegW { w := Width.W64, reg := low Reg64.rsp Width.W64 }), idx := none,
                disp := ↑8 } }]-/
#guard_msgs in
#eval parse! "movq 8(%rsp), %rax"
-- Expected: [.Instr { address_size := .W64, operation_size := .W64, operation := .mov (.Reg (.low .rax .W64)) (.mem .rsp .none 1 8) }]

-- Test: Memory operand with index and scale
/--
info: [Directive.Instr
    { address_size := Width.W64, operation_size := Width.W64,
      operation :=
        Operation.mov ↑(low Reg64.rax Width.W64)
          ↑↑{ base := some (RegOrRip.ofRegW { w := Width.W64, reg := low Reg64.rsi Width.W64 }),
                idx := some { reg := { w := Width.W64, reg := low Reg64.r15 Width.W64 }, scale := Width.W64 } } }]
-/
#guard_msgs in
#eval parse! "movq (%rsi, %r15, 8), %rax"
-- Expected: [.Instr { address_size := .W64, operation_size := .W64, operation := .mov (.Reg (.low .rax .W64)) (.mem .rsi (some .r15) 8 0) }]

-- Test: Labeled instruction
/--
info: [Directive.Label "loop",
  Directive.Instr
    { address_size := Width.W64, operation_size := Width.W64,
      operation := Operation.add ↑(low Reg64.rcx Width.W64) ↑↑1 }]
-/
#guard_msgs in
#eval parse! "loop: addq $1, %rcx"
-- Expected: [.Label "loop", .Instr { address_size := .W64, operation_size := .W64, operation := .add (.Reg (.low .rcx .W64)) (.imm 1) }]

-- Test: Conditional jump
/--
info: [Directive.Instr
    { address_size := Width.W64, operation_size := Width.W64, operation := Operation.jcc CondCode.nz "loop" }]
-/
#guard_msgs in
#eval parse! "jnz loop"
-- Expected: [.Instr { address_size := .W64, operation_size := .W64, operation := .jcc .nz "loop" }]

-- Test: Multi-line program
/--
info: [Directive.Instr
    { address_size := Width.W64, operation_size := Width.W64,
      operation := Operation.mov ↑(low Reg64.rax Width.W64) ↑↑0 },
  Directive.Label "loop",
  Directive.Instr
    { address_size := Width.W64, operation_size := Width.W64,
      operation := Operation.add ↑(low Reg64.rax Width.W64) ↑↑1 },
  Directive.Instr
    { address_size := Width.W64, operation_size := Width.W64,
      operation := Operation.cmp ↑(low Reg64.rax Width.W64) ↑↑10 },
  Directive.Instr
    { address_size := Width.W64, operation_size := Width.W64, operation := Operation.jcc CondCode.nz "loop" }]
-/
#guard_msgs in
#eval parse! "
  movq $0, %rax
loop:
  addq $1, %rax
  cmpq $10, %rax
  jne loop
"

-- Test: Negative immediate
/--
info: [Directive.Instr
    { address_size := Width.W64, operation_size := Width.W64,
      operation := Operation.add ↑(low Reg64.rax Width.W64) ↑↑(-1) }]
-/
#guard_msgs in
#eval parse! "addq $-1, %rax"

-- Test: Hex immediate
/--
info: [Directive.Instr
    { address_size := Width.W64, operation_size := Width.W64,
      operation := Operation.mov ↑(low Reg64.rax Width.W64) ↑↑255 }]
-/
#guard_msgs in
#eval parse! "movq $0xff, %rax"

-- Test: mulx instruction
/--
info: [Directive.Instr
    { address_size := Width.W64, operation_size := Width.W64,
      operation := Operation.mulx (low Reg64.r10 Width.W64) (low Reg64.r9 Width.W64) ↑(low Reg64.r8 Width.W64) }]
-/
#guard_msgs in
#eval parse! "mulxq %r8, %r9, %r10"

-- Test: xor for zeroing
/--
info: [Directive.Instr
    { address_size := Width.W64, operation_size := Width.W64,
      operation := Operation.xor ↑(low Reg64.rax Width.W64) ↑↑(low Reg64.rax Width.W64) }]
-/
#guard_msgs in
#eval parse! "xorq %rax, %rax"

-- Test: lea with complex addressing
/--
info: [Directive.Instr
    { address_size := Width.W64, operation_size := Width.W64,
      operation :=
        Operation.lea (low Reg64.rax Width.W64)
          { base := some (RegOrRip.ofRegW { w := Width.W64, reg := low Reg64.rbp Width.W64 }),
            idx := some { reg := { w := Width.W64, reg := low Reg64.rcx Width.W64 }, scale := Width.W32 },
            disp := ↑16 } }]
-/
#guard_msgs in
#eval parse! "leaq 16(%rbp, %rcx, 4), %rax"

end Tests
