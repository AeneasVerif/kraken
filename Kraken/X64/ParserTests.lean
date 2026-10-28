module

/-
  Parser Tests - Extracted from Parser.lean
  Uses #guard_msgs to verify parser output against expected results.
-/

import Kraken.X64.Parser

section Tests
open Kraken.X64.Parser

open Instr Operand Reg
open Kraken hiding Directive

-- Test: Simple instruction
/--
info: [x64|
  addq %rax, %rbx] : List Directive
-/
#guard_msgs (whitespace := lax) in
#check parse("addq %rax, %rbx")

-- Test: Immediate operand
/--
info: [x64|
  movq $42, %rax] : List Directive
-/
#guard_msgs (whitespace := lax) in
#check parse("movq $42, %rax")
-- Expected: [.Instr { address_size := .W64, operation_size := .W64, operation := .mov (.Reg (.low .rax .W64)) (.imm 42) }]

/--
info: [x64|
  movq $0, %rax] : List Directive
-/
#guard_msgs (whitespace := lax) in
#check parse("movq $0, %rax")

/--
info: [x64|
  pushq $0] : List Directive
-/
#guard_msgs (whitespace := lax) in
#check parse("pushq $0x0")

/--
info: [x64|
  pushq $0] : List Directive
-/
#guard_msgs (whitespace := lax) in
#check parse("pushq $0")

-- Test: unsuffixed push and pop take their width from a register, else 64 bits
/--
info: [x64|
  pushw %ax] : List Directive
-/
#guard_msgs (whitespace := lax) in
#check parse("push %ax")

/--
info: [x64|
  pushq $1] : List Directive
-/
#guard_msgs (whitespace := lax) in
#check parse("push $1")

/--
info: [x64|
  pushq (%rax)] : List Directive
-/
#guard_msgs (whitespace := lax) in
#check parse("push (%rax)")

/--
info: [x64|
  popw %ax] : List Directive
-/
#guard_msgs (whitespace := lax) in
#check parse("pop %ax")

/--
info: [x64|
  popq (%rax)] : List Directive
-/
#guard_msgs (whitespace := lax) in
#check parse("pop (%rax)")

-- Test: Memory operand with displacement
/--
info: [x64|
  movq 8(%rsp), %rax] : List Directive
-/
#guard_msgs (whitespace := lax) in
#check parse("movq 8(%rsp), %rax")
-- Expected: [.Instr { address_size := .W64, operation_size := .W64, operation := .mov (.Reg (.low .rax .W64)) (.mem .rsp .none 1 8) }]

-- Test: Memory operand with index and scale
/--
info: [x64|
  movq (%rsi, %r15, 8), %rax] : List Directive
-/
#guard_msgs (whitespace := lax) in
#check parse("movq (%rsi, %r15, 8), %rax")
-- Expected: [.Instr { address_size := .W64, operation_size := .W64, operation := .mov (.Reg (.low .rax .W64)) (.mem .rsi (some .r15) 8 0) }]

-- Test: movsx/movzx with a memory source, movslq and movsxd
/--
info: [x64|
  movsbw (%rax), %bx] : List Directive
-/
#guard_msgs (whitespace := lax) in
#check parse("movsbw (%rax), %bx")

/--
info: [x64|
  movsbl (%rax), %ebx] : List Directive
-/
#guard_msgs (whitespace := lax) in
#check parse("movsbl (%rax), %ebx")

/--
info: [x64|
  movslq (%rax), %rbx] : List Directive
-/
#guard_msgs (whitespace := lax) in
#check parse("movslq (%rax), %rbx")

/--
info: [x64|
  movsx %eax, %rbx] : List Directive
-/
#guard_msgs (whitespace := lax) in
#check parse("movslq %eax, %rbx")

/--
info: [x64|
  movslq (%rax), %rbx] : List Directive
-/
#guard_msgs (whitespace := lax) in
#check parse("movsxd (%rax), %rbx")

/--
info: [x64|
  movsx %eax, %rbx] : List Directive
-/
#guard_msgs (whitespace := lax) in
#check parse("movsxd %eax, %rbx")

/--
info: [x64|
  movzbl (%rax), %ebx] : List Directive
-/
#guard_msgs (whitespace := lax) in
#check parse("movzbl (%rax), %ebx")

-- Test: Labeled instruction
/--
info: [x64|
  loop:
  addq $1, %rcx] : List Directive
-/
#guard_msgs (whitespace := lax) in
#check parse("loop: addq $1, %rcx")
-- Expected: [.Label "loop", .Instr { address_size := .W64, operation_size := .W64, operation := .add (.Reg (.low .rcx .W64)) (.imm 1) }]

-- Test: Conditional jump
/--
info: [x64|
  jnz loop] : List Directive
-/
#guard_msgs (whitespace := lax) in
#check parse("jnz loop")
-- Expected: [.Instr { address_size := .W64, operation_size := .W64, operation := .jcc .nz "loop" }]

-- Symbol operands, as in GNU as: a bare symbol is a memory operand at that
-- absolute address (a load, not the address), `$sym` is the symbol's address
-- as an immediate, and `sym(%rip)` / `sym(%reg)` are memory operands with a
-- symbolic displacement.
/--
info: [x64|
  movq sym, %rax] : List Directive
-/
#guard_msgs (whitespace := lax) in
#check parse("movq sym, %rax")

/--
info: [x64|
  movq $sym, %rax] : List Directive
-/
#guard_msgs (whitespace := lax) in
#check parse("movq $sym, %rax")

/--
info: [x64|
  movq $sym+8, %rax] : List Directive
-/
#guard_msgs (whitespace := lax) in
#check parse("movq $sym+8, %rax")

/--
info: [x64|
  movq sym(%rip), %rax] : List Directive
-/
#guard_msgs (whitespace := lax) in
#check parse("movq sym(%rip), %rax")

/--
info: [x64|
  movq sym+8(%rip), %rax] : List Directive
-/
#guard_msgs (whitespace := lax) in
#check parse("movq sym+8(%rip), %rax")

/--
info: [x64|
  movq sym(%rax), %rbx] : List Directive
-/
#guard_msgs (whitespace := lax) in
#check parse("movq sym(%rax), %rbx")

/--
info: [x64|
  movq sym-8(%rax, %rcx, 4), %rbx] : List Directive
-/
#guard_msgs (whitespace := lax) in
#check parse("movq sym-8(%rax,%rcx,4), %rbx")

/--
info: [x64|
  addq %rax, sym] : List Directive
-/
#guard_msgs (whitespace := lax) in
#check parse("addq %rax, sym")

/--
info: [x64|
  movups sym(%rip), %xmm0] : List Directive
-/
#guard_msgs (whitespace := lax) in
#check parse("movups sym(%rip), %xmm0")

-- Neighbouring forms: lea, branch targets, numeric
-- RIP-relative offsets.
/--
info: [x64|
  lea sym(%rip), %rax] : List Directive
-/
#guard_msgs (whitespace := lax) in
#check parse("leaq sym(%rip), %rax")

/--
info: [x64|
  lea sym(%rax), %rax] : List Directive
-/
#guard_msgs (whitespace := lax) in
#check parse("leaq sym(%rax), %rax")

/--
info: [x64|
  jmp sym] : List Directive
-/
#guard_msgs (whitespace := lax) in
#check parse("jmp sym")

/--
info: [x64|
  call sym] : List Directive
-/
#guard_msgs (whitespace := lax) in
#check parse("call sym")

/--
info: [x64|
  movq 8(%rip), %rax] : List Directive
-/
#guard_msgs (whitespace := lax) in
#check parse("movq 8(%rip), %rax")

-- Like a bare symbol, a bare number is a memory operand at that absolute
-- address (`as`: `mov 0x1,%rax`, `xor %rax,0x1`).
/--
info: [x64|
  movq 1, %rax] : List Directive
-/
#guard_msgs (whitespace := lax) in
#check parse("movq 1, %rax")

/--
info: [x64|
  xorq %rax, 1] : List Directive
-/
#guard_msgs (whitespace := lax) in
#check parse("xorq %rax, 1")

-- Test: Multi-line program
/--
info: [x64|
  movq $0, %rax
  loop:
  addq $1, %rax
  cmpq $10, %rax
  jnz loop] : List Directive
-/
#guard_msgs (whitespace := lax) in
#check parse("
  movq $0, %rax
loop:
  addq $1, %rax
  cmpq $10, %rax
  jne loop
")

-- Test: Negative immediate
/--
info: [x64|
  addq $-1, %rax] : List Directive
-/
#guard_msgs (whitespace := lax) in
#check parse("addq $-1, %rax")

-- Test: Hex immediate
/--
info: [x64|
  movq $255, %rax] : List Directive
-/
#guard_msgs (whitespace := lax) in
#check parse("movq $0xff, %rax")

-- Test: mulx instruction
/--
info: [x64|
  mulx %r8, %r9, %r10] : List Directive
-/
#guard_msgs (whitespace := lax) in
#check parse("mulxq %r8, %r9, %r10")

-- Test: xor for zeroing
/--
info: [x64|
  xorq %rax, %rax] : List Directive
-/
#guard_msgs (whitespace := lax) in
#check parse("xorq %rax, %rax")

-- Test: lea with complex addressing
/--
info: [x64|
  lea 16(%rbp, %rcx, 4), %rax] : List Directive
-/
#guard_msgs (whitespace := lax) in
#check parse("leaq 16(%rbp, %rcx, 4), %rax")

/--
info: [x64|
  lea 16(%ebp, %ecx, 4), %rax] : List Directive
-/
#guard_msgs (whitespace := lax) in
#check parse("leaq 16(%ebp, %ecx, 4), %rax")

section error_reporting

/-- error: <input>:1:12: expected x64_reg_name -/
#guard_msgs in
#check parse("xorq %rax, %unlikely")

/-- error: type error: w64 != w32 -/
#guard_msgs in
#check parse("mov (%rax, %ebx), %rax")

/-- error: can't have two memory operands -/
#guard_msgs in
#check parse("mov (%rax), (%rax)")

/-- error: high byte register cannot be used for an addrexpr -/
#guard_msgs in
#check parse("mov $2, (%ah)")

/-- error: <input>:1:9: unexpected end of input; expected ',' -/
#guard_msgs in
#check parse("addq %rax")

/-- error: expected register or memory operand, got $ -/
#guard_msgs in
#check parse("xorq %rax, $1")

/-- error: can't have two memory operands -/
#guard_msgs in
#check parse("movq sym, sym2")

/-- error: absolute branch targets are not supported -/
#guard_msgs in
#check parse("jmp 0x10")

/-- error: <input>:1:4: unexpected end of input -/
#guard_msgs in
#check parse("addq")

/-- error: <input>:3:2: expected ',' -/
#guard_msgs in
#check parse("
  addq %rax
  cmpq $10, %rax
")

/-- error: type error: w64 != w32 -/
#guard_msgs in
#check parse("movq %eax, %rbx")

/-- error: invalid scale 3, must be 1, 2, 4, or 8 -/
#guard_msgs in
#check parse("movq (%rax, %rcx, 3), %rbx")

/-- error: <input>:1:16: unexpected element; expected ';' -/
#guard_msgs in
#check parse("movq %rax, %rbx garbage")

/-- error: <input>:1:9: unexpected element; expected ';' -/
#guard_msgs in
#check parse("shlq %rcx, %rax")

/-- error: <input>:1:0: expected end of input -/
#guard_msgs in
#check parse("foo\n:")

end error_reporting

section syntax_cat_and_include

/--
info: [x64|
  loop:
  addq $1, %rax
  jnz loop] : List Directive
-/
#guard_msgs in
#check [x64|
  loop:
    addq $1, %rax
    jnz loop
]

/--
info: [x64|
  nop] : List Directive
-/
#guard_msgs in
#check include_x64 "Kraken/X64/Test/asm/test_nop.S"

/--
info: [x64|
  aa.1.aa.1:
  jmp .L.str.1.llvm.12345] : List Directive
-/
#guard_msgs in
#check [x64|
  aa.1.aa.1:
    jmp .L.str.1.llvm.12345
]

end syntax_cat_and_include

section antiquotations

variable {w : Width} (r : Reg w) (q : Reg .W64) (r64 : Reg64) (v : AvxReg .W256)

-- Test: an antiquoted register decides the width of its instruction, which may be a variable
/--
info: [x64|
  add $2, %❰r❱] : List Directive
-/
#guard_msgs in
#check [x64| add $2, %❰r❱ ]

-- Test: antiquoted and concrete registers unify
/--
info: [x64|
  movq %rax, %❰q❱] : List Directive
-/
#guard_msgs in
#check [x64| mov %rax, %❰q❱ ]

-- Test: a width suffix must agree with the antiquoted register's width
/--
error: Type mismatch
  r
has type
  Reg w
but is expected to have type
  Reg Width.W64
-/
#guard_msgs in
#check [x64| addq $1, %❰r❱ ]

/-- error: type error: w != w32 -/
#guard_msgs in
#check [x64| add %❰r❱, %eax ]

-- Test: in address positions, antiquotations denote `Reg64`
/--
info: [x64|
  movq 8(%❰r64❱, %rax, 4), %rcx] : List Directive
-/
#guard_msgs in
#check [x64| mov 8(%❰r64❱, %rax, 4), %rcx ]

-- Test: AVX registers
/--
info: [x64|
  vmovups (%rax), %❰v❱] : List Directive
-/
#guard_msgs in
#check [x64| vmovups (%rax), %❰v❱ ]

-- Test: a width that no operand or suffix determines is an error
/-- error: could not infer operand width -/
#guard_msgs in
#check [x64| add $1, (%rax) ]

-- Test: the source of a widening move must be narrower than its destination
/-- error: source width w64 must be narrower than destination width w16 -/
#guard_msgs in
#check [x64| movsx %rax, %bx ]

-- Test: antiquotations for operands, instructions and directives
variable (o : Operand .W32) (rm : RegOrMem w) (av : AvxRegOrMem .W128) (rt : RelRegOrMem) (i : Instr) (d : Directive)

/--
info: [x64|
  addl ❰o❱, %eax] : List Directive
-/
#guard_msgs in
#check [x64| add ❰o❱, %eax ]

/--
info: [x64|
  inc ❰rm❱] : List Directive
-/
#guard_msgs in
#check [x64| inc ❰rm❱ ]

/--
info: [x64|
  movaps ❰av❱, %xmm1] : List Directive
-/
#guard_msgs in
#check [x64| movaps ❰av❱, %xmm1 ]

/--
info: [x64|
  jmp ❰rt❱] : List Directive
-/
#guard_msgs in
#check [x64| jmp ❰rt❱ ]

/--
info: [x64|
  ❰Directive.instr i❱
  ❰d❱
  ret] : List Directive
-/
#guard_msgs in
#check [x64| ❰.instr i❱; ❰d❱; ret ]

/--
info: [x64|
  foo:
  ret] : List Directive
-/
#guard_msgs in
#check [x64| ❰.label "foo"❱; ❰.instr <| .regular .W64 .W64 .ret❱ ]

-- Test: open program tail delaborates as `[x64| ...] ++ rest`
variable (rest : List Directive)

/--
info: [x64|
    movq $1, %rax] ++
  rest : List (Kraken.Directive Instr)
-/
#guard_msgs in
#check (Directive.instr (regular .W64 .W64 (.mov ↑Reg.rax ↑(1 : Int64))) :: rest)

end antiquotations

end Tests
