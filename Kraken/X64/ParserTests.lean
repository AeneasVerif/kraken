module

/-
  Parser Tests - Extracted from Parser.lean
  Uses #guard_msgs to verify parser output against expected results.
-/

public import Lean
public meta import Lean
public import Kraken.X64.Parser
public meta import Kraken.X64.Parser
import Kraken.X64.PrintATT
meta import Kraken.X64.PrintATT

section Tests
open Kraken.X64.Parser

open Instr Operand Reg Kraken

-- Test: Simple instruction
/-- info: [⸨dir| addq %rax, %rbx ⸩] : List _root_.Directive -/
#guard_msgs (whitespace := lax) in
#check ⸨prog| addq %rax, %rbx ⸩

-- Test: Immediate operand
/-- info: [⸨dir| movq $42, %rax ⸩] : List _root_.Directive -/
#guard_msgs (whitespace := lax) in
#check ⸨prog| movq $42, %rax ⸩
-- Expected: [.Instr { address_size := .W64, operation_size := .W64, operation := .mov (.Reg (.low .rax .W64)) (.imm 42) }]

/-- info: [⸨dir| movq $0, %rax ⸩] : List _root_.Directive -/
#guard_msgs (whitespace := lax) in
#check ⸨prog| movq $0, %rax ⸩

/-- info: [⸨dir| pushq $0 ⸩] : List _root_.Directive -/
#guard_msgs (whitespace := lax) in
#check ⸨prog| pushq $0x0 ⸩

/-- info: [⸨dir| pushq $0 ⸩] : List _root_.Directive -/
#guard_msgs (whitespace := lax) in
#check ⸨prog| pushq $0 ⸩

-- Test: unsuffixed push and pop take their width from a register, else 64 bits
-- TODO (pp.maxSteps: the 8- and 16-bit wrappers are tried last; prints as a Lean term):
-- /--
-- info: ⸨prog|
--   pushw %ax⸩ : List _root_.Directive
-- -/
-- #guard_msgs (whitespace := lax) in
-- #check ⸨prog| push %ax ⸩

/-- info: [⸨dir| pushq $1 ⸩] : List _root_.Directive -/
#guard_msgs (whitespace := lax) in
#check ⸨prog| push $1 ⸩

/-- info: [⸨dir| pushq (%rax) ⸩] : List _root_.Directive -/
#guard_msgs (whitespace := lax) in
#check ⸨prog| push (%rax) ⸩

-- TODO (pp.maxSteps: the 8- and 16-bit wrappers are tried last; prints as a Lean term):
-- /--
-- info: ⸨prog|
--   popw %ax⸩ : List _root_.Directive
-- -/
-- #guard_msgs (whitespace := lax) in
-- #check ⸨prog| pop %ax ⸩

/-- info: [⸨dir| popq (%rax) ⸩] : List _root_.Directive -/
#guard_msgs (whitespace := lax) in
#check ⸨prog| pop (%rax) ⸩

-- Test: Memory operand with displacement
/-- info: [⸨dir| movq 8(%rsp), %rax ⸩] : List _root_.Directive -/
#guard_msgs (whitespace := lax) in
#check ⸨prog| movq 8(%rsp), %rax ⸩
-- Expected: [.Instr { address_size := .W64, operation_size := .W64, operation := .mov (.Reg (.low .rax .W64)) (.mem .rsp .none 1 8) }]

-- Test: Memory operand with index and scale
/-- info: [⸨dir| movq (%rsi, %r15, 8), %rax ⸩] : List _root_.Directive -/
#guard_msgs (whitespace := lax) in
#check ⸨prog| movq (%rsi, %r15, 8), %rax ⸩
-- Expected: [.Instr { address_size := .W64, operation_size := .W64, operation := .mov (.Reg (.low .rax .W64)) (.mem .rsi (some .r15) 8 0) }]

-- Test: movsx/movzx with a memory source, movslq and movsxd
-- TODO (pp.maxSteps: the 8- and 16-bit wrappers are tried last; prints as a Lean term):
-- /--
-- info: ⸨prog|
--   movsbw (%rax), %bx⸩ : List _root_.Directive
-- -/
-- #guard_msgs (whitespace := lax) in
-- #check ⸨prog| movsbw (%rax), %bx ⸩

-- TODO (pp.maxSteps: the 8- and 16-bit wrappers are tried last; prints as a Lean term):
-- /--
-- info: ⸨prog|
--   movsbl (%rax), %ebx⸩ : List _root_.Directive
-- -/
-- #guard_msgs (whitespace := lax) in
-- #check ⸨prog| movsbl (%rax), %ebx ⸩

/-- info: [⸨dir| movslq (%rax), %rbx ⸩] : List _root_.Directive -/
#guard_msgs (whitespace := lax) in
#check ⸨prog| movslq (%rax), %rbx ⸩

/-- info: [⸨dir| movslq %eax, %rbx ⸩] : List _root_.Directive -/
#guard_msgs (whitespace := lax) in
#check ⸨prog| movslq %eax, %rbx ⸩

/-- info: [⸨dir| movslq (%rax), %rbx ⸩] : List _root_.Directive -/
#guard_msgs (whitespace := lax) in
#check ⸨prog| movsxd (%rax), %rbx ⸩

/-- info: [⸨dir| movslq %eax, %rbx ⸩] : List _root_.Directive -/
#guard_msgs (whitespace := lax) in
#check ⸨prog| movsxd %eax, %rbx ⸩

-- TODO (pp.maxSteps: the 8- and 16-bit wrappers are tried last; prints as a Lean term):
-- /--
-- info: ⸨prog|
--   movzbl (%rax), %ebx⸩ : List _root_.Directive
-- -/
-- #guard_msgs (whitespace := lax) in
-- #check ⸨prog| movzbl (%rax), %ebx ⸩

-- TODO (a label followed by an instruction on the same line):
-- -- Test: Labeled instruction
-- /--
-- info: ⸨prog|
--   loop:
--   addq $1, %rcx⸩ : List _root_.Directive
-- -/
-- #guard_msgs (whitespace := lax) in
-- #check ⸨prog| loop: addq $1, %rcx ⸩
-- -- Expected: [.Label "loop", .Instr { address_size := .W64, operation_size := .W64, operation := .add (.Reg (.low .rcx .W64)) (.imm 1) }]

-- Test: Conditional jump
/-- info: [⸨dir| jnz loop ⸩] : List _root_.Directive -/
#guard_msgs (whitespace := lax) in
#check ⸨prog| jnz loop ⸩
-- Expected: [.Instr { address_size := .W64, operation_size := .W64, operation := .jcc .nz "loop" }]

-- Symbol operands, as in GNU as: a bare symbol is a memory operand at that
-- absolute address (a load, not the address), `$sym` is the symbol's address
-- as an immediate, and `sym(%rip)` / `sym(%reg)` are memory operands with a
-- symbolic displacement.
/-- info: [⸨dir| movq sym, %rax ⸩] : List _root_.Directive -/
#guard_msgs (whitespace := lax) in
#check ⸨prog| movq sym, %rax ⸩

-- TODO ($sym is read as a Lean antiquotation, issue 6):
-- /--
-- info: ⸨prog|
--   movq $sym, %rax⸩ : List _root_.Directive
-- -/
-- #guard_msgs (whitespace := lax) in
-- #check ⸨prog| movq $sym, %rax ⸩

-- TODO ($sym is read as a Lean antiquotation, issue 6):
-- /--
-- info: ⸨prog|
--   movq $sym+8, %rax⸩ : List _root_.Directive
-- -/
-- #guard_msgs (whitespace := lax) in
-- #check ⸨prog| movq $sym+8, %rax ⸩

/-- info: [⸨dir| movq sym(%rip), %rax ⸩] : List _root_.Directive -/
#guard_msgs (whitespace := lax) in
#check ⸨prog| movq sym(%rip), %rax ⸩

/-- info: [⸨dir| movq sym+8(%rip), %rax ⸩] : List _root_.Directive -/
#guard_msgs (whitespace := lax) in
#check ⸨prog| movq sym+8(%rip), %rax ⸩

/-- info: [⸨dir| movq sym(%rax), %rbx ⸩] : List _root_.Directive -/
#guard_msgs (whitespace := lax) in
#check ⸨prog| movq sym(%rax), %rbx ⸩

/-- info: [⸨dir| movq sym-8(%rax, %rcx, 4), %rbx ⸩] : List _root_.Directive -/
#guard_msgs (whitespace := lax) in
#check ⸨prog| movq sym-8(%rax,%rcx,4), %rbx ⸩

/-- info: [⸨dir| addq %rax, sym ⸩] : List _root_.Directive -/
#guard_msgs (whitespace := lax) in
#check ⸨prog| addq %rax, sym ⸩

/-- info: [⸨dir| movups sym(%rip), %xmm0 ⸩] : List _root_.Directive -/
#guard_msgs (whitespace := lax) in
#check ⸨prog| movups sym(%rip), %xmm0 ⸩

-- Neighbouring forms: lea, branch targets, numeric
-- RIP-relative offsets.
/-- info: [⸨dir| leaq sym(%rip), %rax ⸩] : List _root_.Directive -/
#guard_msgs (whitespace := lax) in
#check ⸨prog| leaq sym(%rip), %rax ⸩

/-- info: [⸨dir| leaq sym(%rax), %rax ⸩] : List _root_.Directive -/
#guard_msgs (whitespace := lax) in
#check ⸨prog| leaq sym(%rax), %rax ⸩

/-- info: [⸨dir| jmp sym ⸩] : List _root_.Directive -/
#guard_msgs (whitespace := lax) in
#check ⸨prog| jmp sym ⸩

/-- info: [⸨dir| call sym ⸩] : List _root_.Directive -/
#guard_msgs (whitespace := lax) in
#check ⸨prog| call sym ⸩

/-- info: [⸨dir| movq 8(%rip), %rax ⸩] : List _root_.Directive -/
#guard_msgs (whitespace := lax) in
#check ⸨prog| movq 8(%rip), %rax ⸩

-- Like a bare symbol, a bare number is a memory operand at that absolute
-- address (`as`: `mov 0x1,%rax`, `xor %rax,0x1`).
/-- info: [⸨dir| movq 1, %rax ⸩] : List _root_.Directive -/
#guard_msgs (whitespace := lax) in
#check ⸨prog| movq 1, %rax ⸩

/-- info: [⸨dir| xorq %rax, 1 ⸩] : List _root_.Directive -/
#guard_msgs (whitespace := lax) in
#check ⸨prog| xorq %rax, 1 ⸩

-- Test: Multi-line program
/--
info: [⸨dir| movq $0, %rax ⸩, ⸨dir| loop: ⸩, ⸨dir| addq $1, %rax ⸩, ⸨dir| cmpq $10, %rax ⸩,
  ⸨dir| jnz loop ⸩] : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog|
  movq $0, %rax
loop:
  addq $1, %rax
  cmpq $10, %rax
  jne loop
⸩

-- Test: Negative immediate
/-- info: [⸨dir| addq $-1, %rax ⸩] : List _root_.Directive -/
#guard_msgs (whitespace := lax) in
#check ⸨prog| addq $-1, %rax ⸩

-- Test: Hex immediate
/-- info: [⸨dir| movq $255, %rax ⸩] : List _root_.Directive -/
#guard_msgs (whitespace := lax) in
#check ⸨prog| movq $0xff, %rax ⸩

-- Test: mulx instruction
/-- info: [⸨dir| mulxq %r8, %r9, %r10 ⸩] : List _root_.Directive -/
#guard_msgs (whitespace := lax) in
#check ⸨prog| mulxq %r8, %r9, %r10 ⸩

-- Test: xor for zeroing
/-- info: [⸨dir| xorq %rax, %rax ⸩] : List _root_.Directive -/
#guard_msgs (whitespace := lax) in
#check ⸨prog| xorq %rax, %rax ⸩

-- Test: lea with complex addressing
/-- info: [⸨dir| leaq 16(%rbp, %rcx, 4), %rax ⸩] : List _root_.Directive -/
#guard_msgs (whitespace := lax) in
#check ⸨prog| leaq 16(%rbp, %rcx, 4), %rax ⸩

-- TODO (32-bit register names in addresses are not read yet, issue 1):
-- /--
-- info: ⸨prog|
--   lea 16(%ebp, %ecx, 4), %rax⸩ : List _root_.Directive
-- -/
-- #guard_msgs (whitespace := lax) in
-- #check ⸨prog| leaq 16(%ebp, %ecx, 4), %rax ⸩

section data_words

/-- info: [⸨dir| .long end-start ⸩] : List _root_.Directive -/
#guard_msgs (whitespace := lax) in
#check ⸨prog| .long end - start ⸩

/-- info: [⸨dir| .quad sym ⸩] : List _root_.Directive -/
#guard_msgs (whitespace := lax) in
#check ⸨prog| .quad sym ⸩

/-- info: [⸨dir| .short 7 ⸩] : List _root_.Directive -/
#guard_msgs (whitespace := lax) in
#check ⸨prog| .short 7 ⸩

/-- info: [⸨dir| .long sym+8 ⸩] : List _root_.Directive -/
#guard_msgs (whitespace := lax) in
#check ⸨prog| .long sym+8 ⸩

/-- info: [⸨dir| .quad -1 ⸩] : List _root_.Directive -/
#guard_msgs (whitespace := lax) in
#check ⸨prog| .quad -1 ⸩

-- TODO ($sym is read as a Lean antiquotation, issue 6):
-- /--
-- info: ⸨prog|
--   movq $b-a, %rax⸩ : List _root_.Directive
-- -/
-- #guard_msgs (whitespace := lax) in
-- #check ⸨prog| movq $b-a, %rax ⸩

-- A label that begins with a directive word is still a label.
/-- info: [⸨dir| .longest: ⸩, ⸨dir| nop 1 ⸩] : List _root_.Directive -/
#guard_msgs (whitespace := lax) in
#check ⸨prog|
.longest:
  nop
⸩

-- The jump table of clang's `sel` (as in `PrintATTTests.jumpTable`) elaborates to the same words as
-- the combinator parser produces.
#guard (⸨prog|
sel:
  cmpl $2, %edi
  ja .Ldefault
  movl %edi, %eax
  leaq .LJTI0_0(%rip), %rcx
  movslq (%rcx,%rax,4), %rax
  addq %rcx, %rax
  jmp %rax
.Lcase0:
  movl $10, %eax
  ret
.Lcase1:
  movl $20, %eax
  ret
.Lcase2:
  movl $30, %eax
  ret
.Ldefault:
  xorl %eax, %eax
  ret
  .align 4
.LJTI0_0:
  .long .Lcase0 - .LJTI0_0
  .long .Lcase1 - .LJTI0_0
  .long .Lcase2 - .LJTI0_0
⸩ : Program).drop 22 ==
  [0, 1, 2].map (fun k => .word 4 (.sub (.label s!".Lcase{k}") (.label ".LJTI0_0")))

/-- Printing `p` in AT&T syntax and reading it back with the combinator parser gives `p`. -/
def agreesWithCombinatorParser (p : Program) : Bool :=
  match Kraken.X64.Parser.parse (Kraken.X64.toATT p) with
  | .ok p' => p' == p
  | .error _ => false

#guard [⸨prog| .long end - start ⸩, ⸨prog| .quad sym ⸩, ⸨prog| .short 7 ⸩, ⸨prog| .long sym+8 ⸩,
-- TODO ($sym is read as a Lean antiquotation, issue 6): `⸨prog| movq $b-a, %rax ⸩` removed from the list.
  ⸨prog| .quad -1 ⸩, ⸨prog|
.longest:
  nop
⸩].all agreesWithCombinatorParser

end data_words

section error_reporting

local elab "elabX64% " s:str : term => elabX64 s.getString

/-- error: <input>:1:5: unexpected end of input; expected ':' -/
#guard_msgs in
#check elabX64% ".long"

/--
error: <input>:1:12: expected 'r10', 'r11', 'r12', 'r13', 'r14', 'r15', 'r8', 'r9', 'rax', 'rbp', 'rbx', 'rcx', 'rdi', 'rdx', 'rsi', 'rsp' or '❰'
-/
#guard_msgs in
#check elabX64% "xorq %rax, %unlikely"

/--
error: <input>:1:12: expected 'r10', 'r11', 'r12', 'r13', 'r14', 'r15', 'r8', 'r9', 'rax', 'rbp', 'rbx', 'rcx', 'rdi', 'rdx', 'rsi', 'rsp' or '❰'
-/
#guard_msgs in
#check elabX64% "mov (%rax, %ebx), %rax"

/--
error: Ambiguous term
  mov (%rax), (%rax)
Possible interpretations:
  ⸨instr| movq (%rax), (%rax) ⸩ : Instr
  
  ⸨instr| movl (%rax), (%rax) ⸩ : Instr
  
  ⸨instr| movw (%rax), (%rax) ⸩ : Instr
  
  regular ⋯ ⋯ ⋯ : Instr
---
info: [⸨dir| ❰sorry❱ ⸩] : List _root_.Directive
-/
#guard_msgs in
#check ⸨prog| mov (%rax), (%rax) ⸩

/--
error: <input>:1:10: expected 'r10', 'r11', 'r12', 'r13', 'r14', 'r15', 'r8', 'r9', 'rax', 'rbp', 'rbx', 'rcx', 'rdi', 'rdx', 'rip', 'rsi', 'rsp' or '❰'
-/
#guard_msgs in
#check elabX64% "mov $2, (%ah)"

/-- error: <input>:1:9: unexpected end of input; expected ',' -/
#guard_msgs in
#check elabX64% "addq %rax"

/--
error: <input>:1:11: identifier; expected '(', '_', identifier, numeral or x64_register64
-/
#guard_msgs in
#check elabX64% "xorq %rax, $1"

/-- info: [⸨dir| movq sym, sym2 ⸩] : List _root_.Directive -/
#guard_msgs in
#check ⸨prog| movq sym, sym2 ⸩

/-- info: [⸨dir| jmp 16 ⸩] : List _root_.Directive -/
#guard_msgs in
#check ⸨prog| jmp 0x10 ⸩

/-- error: <input>:1:4: unexpected end of input; expected ':' -/
#guard_msgs in
#check elabX64% "addq"

/-- error: <input>:3:2: expected ',' -/
#guard_msgs in
#check elabX64% "
  addq %rax
  cmpq $10, %rax
"

/--
error: <input>:1:6: expected 'r10', 'r11', 'r12', 'r13', 'r14', 'r15', 'r8', 'r9', 'rax', 'rbp', 'rbx', 'rcx', 'rdi', 'rdx', 'rsi', 'rsp' or '❰'
-/
#guard_msgs in
#check elabX64% "movq %eax, %rbx"

/--
error: overloaded, errors 
  elaboration function for `«x64_index,_,__3»` has not been implemented
    , %rcx, 3
  
  elaboration function for `«x64_index,_,__2»` has not been implemented
    , %rcx, 3
  
  elaboration function for `«x64_index,_,__1»` has not been implemented
    , %rcx, 3
  
  elaboration function for `«x64_index,_,_»` has not been implemented
    , %rcx, 3
---
info: [⸨dir|
    movq ❰↑{ base := Option.some (RegOrRip.reg (⸨base| %rax ⸩)), idx := Option.some sorry }❱,
          %rbx ⸩] : List _root_.Directive
-/
#guard_msgs in
#check ⸨prog| movq (%rax, %rcx, 3), %rbx ⸩

/-- error: <input>:1:16: unexpected element -/
#guard_msgs in
#check elabX64% "movq %rax, %rbx garbage"

/-- error: <input>:1:9: unexpected element -/
#guard_msgs in
#check elabX64% "shlq %rcx, %rax"

/-- error: <input>:2:0: expected checkLineEq -/
#guard_msgs in
#check elabX64% "foo\n:"

end error_reporting

section syntax_cat_and_include

/--
info: [⸨dir| loop: ⸩, ⸨dir| addq $1, %rax ⸩, ⸨dir| jnz loop ⸩] : List _root_.Directive
-/
#guard_msgs in
#check ⸨prog|
  loop:
    addq $1, %rax
    jnz loop
⸩

/-- info: [⸨dir| nop 1 ⸩] : List _root_.Directive -/
#guard_msgs in
#check include_x64 "Kraken/X64/Test/asm/test_nop.S"

/--
info: [⸨dir| aa.1.aa.1: ⸩, ⸨dir| jmp .L.str.1.llvm.12345 ⸩] : List _root_.Directive
-/
#guard_msgs in
#check ⸨prog|
  aa.1.aa.1:
    jmp .L.str.1.llvm.12345
⸩

/-- info: ⸨dir| addq $1, %rax ⸩ : Kraken.Directive Instr ?m.2 -/
#guard_msgs in
#check ⸨dir| addq $1, %rax ⸩

/--
info: { directive := ⸨dir| addq $1, %rax ⸩, size := Layout.size Instr ConstExpr 1 } : Sized _root_.Directive
-/
#guard_msgs (whitespace := lax) in
variable [Kraken.Layout Instr ConstExpr] in
#check ⸨dir 1 | addq $1, %rax ⸩

end syntax_cat_and_include

section antiquotations

variable {w : Width} (r : Reg w) (q : Reg .W64) (r64 : Reg64) (v : AvxReg .W256)

-- Test: an antiquoted register decides the width of its instruction, which may be a variable
-- TODO (registers with a width variable: one category per width):
-- /--
-- info: ⸨prog|
--   add $2, %❰r❱⸩ : List _root_.Directive
-- -/
-- #guard_msgs in
-- #check ⸨prog| add $2, %❰r❱ ⸩

-- Test: antiquoted and concrete registers unify
/-- info: [⸨dir| movq %rax, %❰q❱ ⸩] : List _root_.Directive -/
#guard_msgs in
#check ⸨prog| mov %rax, %❰q❱ ⸩

-- Test: a width suffix must agree with the antiquoted register's width
-- TODO (registers with a width variable: one category per width):
-- /--
-- error: Type mismatch
--   r
-- has type
--   Reg w
-- but is expected to have type
--   Reg Width.W64
-- -/
-- #guard_msgs in
-- #check ⸨prog| addq $1, %❰r❱ ⸩

-- TODO (registers with a width variable: one category per width):
-- /-- error: type error: w != w32 -/
-- #guard_msgs in
-- #check ⸨prog| add %❰r❱, %eax ⸩

-- Test: in address positions, antiquotations denote `Reg64`
/-- info: [⸨dir| movq 8(%❰r64❱, %rax, 4), %rcx ⸩] : List _root_.Directive -/
#guard_msgs in
#check ⸨prog| mov 8(%❰r64❱, %rax, 4), %rcx ⸩

-- Test: AVX registers
/-- info: [⸨dir| vmovups (%rax), %❰v❱ ⸩] : List _root_.Directive -/
#guard_msgs in
#check ⸨prog| vmovups (%rax), %❰v❱ ⸩

-- Test: a width that no operand or suffix determines is an error
/--
error: Ambiguous term
  add $1, (%rax)
Possible interpretations:
  ⸨instr| addq $1, (%rax) ⸩ : Instr
  
  ⸨instr| addl $1, (%rax) ⸩ : Instr
  
  ⸨instr| addw $1, (%rax) ⸩ : Instr
  
  ⸨instr| addb $1, (%rax) ⸩ : Instr
---
info: [⸨dir| ❰sorry❱ ⸩] : List _root_.Directive
-/
#guard_msgs in
#check ⸨prog| add $1, (%rax) ⸩

-- TODO (now a parse error, which `#guard_msgs` cannot check):
-- -- Test: the source of a widening move must be narrower than its destination
-- /-- error: source width w64 must be narrower than destination width w16 -/
-- #guard_msgs in
-- #check ⸨prog| movsx %rax, %bx ⸩

-- Test: antiquotations for operands, instructions and directives
variable (o : Operand .W32) (rm : RegOrMem w) (av : AvxRegOrMem .W128) (rt : RelRegOrMem) (i : Instr) (d : Directive)

/-- info: [⸨dir| addl ❰o❱, %eax ⸩] : List _root_.Directive -/
#guard_msgs in
#check ⸨prog| add ❰o❱, %eax ⸩

-- TODO (operands with a width variable: one category per width):
-- /--
-- info: ⸨prog|
--   inc ❰rm❱⸩ : List _root_.Directive
-- -/
-- #guard_msgs in
-- #check ⸨prog| inc ❰rm❱ ⸩

/-- info: [⸨dir| movaps ❰av❱, %xmm1 ⸩] : List _root_.Directive -/
#guard_msgs in
#check ⸨prog| movaps ❰av❱, %xmm1 ⸩

/-- info: [⸨dir| jmp ❰rt❱ ⸩] : List _root_.Directive -/
#guard_msgs in
#check ⸨prog| jmp ❰rt❱ ⸩

/-- info: [⸨dir| ❰i❱ ⸩, d, ⸨dir| ret ⸩] : List _root_.Directive -/
#guard_msgs in
#check ⸨prog| ❰.instr i❱; ❰d❱; ret ⸩

/-- info: [⸨dir| foo: ⸩, ⸨dir| ret ⸩] : List _root_.Directive -/
#guard_msgs in
#check ⸨prog| ❰.label "foo"❱; ❰.instr <| .regular .W64 .W64 .ret❱ ⸩

-- Test: label antiquotations (`x64_ident`)
variable (lbl : Kraken.Label)

-- TODO (a label followed by an instruction on the same line):
-- /--
-- info: ⸨prog|
--   ❰lbl❱:
--   ret⸩ : List _root_.Directive
-- -/
-- #guard_msgs in
-- #check ⸨prog| ❰lbl❱: ret ⸩

/-- info: [⸨dir| jz ❰lbl❱ ⸩] : List _root_.Directive -/
#guard_msgs in
#check ⸨prog| jz ❰lbl❱ ⸩

/-- info: [⸨dir| movq $❰lbl❱, %rax ⸩] : List _root_.Directive -/
#guard_msgs in
#check ⸨prog| movq $❰lbl❱, %rax ⸩

/-- info: [⸨dir| movq $❰lbl❱+8, %rax ⸩] : List _root_.Directive -/
#guard_msgs in
#check ⸨prog| movq $❰lbl❱+8, %rax ⸩

/-- info: [⸨dir| movq $❰lbl❱-8, %rax ⸩] : List _root_.Directive -/
#guard_msgs in
#check ⸨prog| movq $❰lbl❱-8, %rax ⸩

/-- info: [⸨dir| leaq ❰lbl❱(%rip), %rax ⸩] : List _root_.Directive -/
#guard_msgs in
#check ⸨prog| leaq ❰lbl❱(%rip), %rax ⸩

/-- info: [⸨dir| movq ❰lbl❱+8(%rip), %rax ⸩] : List _root_.Directive -/
#guard_msgs in
#check ⸨prog| movq ❰lbl❱+8(%rip), %rax ⸩

/-- info: [⸨dir| movq ❰lbl❱-8(%rax, %rcx, 4), %rdx ⸩] : List _root_.Directive -/
#guard_msgs in
#check ⸨prog| movq ❰lbl❱-8(%rax, %rcx, 4), %rdx ⸩

/-- info: [⸨dir| movq ❰lbl❱+8, %rax ⸩] : List _root_.Directive -/
#guard_msgs in
#check ⸨prog| movq ❰lbl❱+8, %rax ⸩

/-- info: [⸨dir| .long ❰lbl❱-start ⸩] : List _root_.Directive -/
#guard_msgs in
#check ⸨prog| .long ❰lbl❱ - start ⸩

/--
error: Type mismatch
  r
has type
  Reg w
but is expected to have type
  Kraken.Label
---
info: [⸨dir| jz ❰sorry❱ ⸩] : List _root_.Directive
-/
#guard_msgs in
#check ⸨prog| jz ❰r❱ ⸩

-- Test: `Int64` / `ConstExpr` antiquotations (`x64_const` and `x64_operand`)
variable (imm : Int64) (ce : ConstExpr)

/-- info: [⸨dir| movq $❰imm❱, %rax ⸩] : List _root_.Directive -/
#guard_msgs in
#check ⸨prog| mov $❰imm❱, %rax ⸩

/-- info: [⸨dir| movq $❰imm❱, %rax ⸩] : List _root_.Directive -/
#guard_msgs in
#check ⸨prog| mov ❰imm❱, %rax ⸩

/-- info: [⸨dir| movl $❰imm❱, %eax ⸩] : List _root_.Directive -/
#guard_msgs in
#check ⸨prog| mov ❰imm❱, %eax ⸩

/-- info: [⸨dir| pushq $❰imm❱ ⸩] : List _root_.Directive -/
#guard_msgs in
#check ⸨prog| push ❰imm❱ ⸩

/-- info: [⸨dir| movq ❰imm❱(%rsp), %rax ⸩] : List _root_.Directive -/
#guard_msgs in
#check ⸨prog| movq ❰imm❱(%rsp), %rax ⸩

/-- info: [⸨dir| movq ❰imm❱(%rip), %rax ⸩] : List _root_.Directive -/
#guard_msgs in
#check ⸨prog| movq ❰imm❱(%rip), %rax ⸩

/-- info: [⸨dir| movq $❰ce❱, %rax ⸩] : List _root_.Directive -/
#guard_msgs in
#check ⸨prog| mov $❰ce❱, %rax ⸩

end antiquotations

-- Test: flag control instructions (`cld`/`std`), string parser and `⸨prog| ⸩` syntax
/-- info: [⸨dir| cld ⸩, ⸨dir| std ⸩] : List _root_.Directive -/
#guard_msgs (whitespace := lax) in
#check ⸨prog|
cld
std
⸩

/-- info: [⸨dir| cld ⸩, ⸨dir| std ⸩] : List _root_.Directive -/
#guard_msgs (whitespace := lax) in
#check ⸨prog| cld; std ⸩

section string_instructions

#guard [
  ⸨prog|
movsb
movsq
rep movsb
rep movsl
stosw
rep stosb
rep stosq
⸩,
  ⸨prog|
.byte 0x67; movsb
.byte 0x67; rep movsq
.byte 0x67; stosl
.byte 0x67; rep stosw
⸩
].all agreesWithCombinatorParser

#guard ⸨instr| .byte 0x67; rep movsb ⸩ = Instr.regular .W32 .W8 (.movs true)
#guard ⸨instr| stosq ⸩ = Instr.regular .W64 .W64 (.stos false)

/--
info: [⸨dir| rep movsb ⸩, ⸨dir| movsq ⸩, ⸨dir| .byte 0x67; rep stosl ⸩, ⸨dir| .byte 0x67; stosw ⸩] : List _root_.Directive
-/
#guard_msgs in
#check ⸨prog|
  rep movsb
  movsq
  .byte 0x67; rep stosl
  .byte 0x67; stosw
⸩

end string_instructions

section sse_and_vex

#guard [
  ⸨prog|
movdqu (%rsp), %xmm0
movdqa %xmm1, 16(%rsp)
paddd (%rax), %xmm2
pshufb %xmm3, %xmm4
⸩,
  ⸨prog|
pshufd $0x1b, %xmm5, %xmm6
palignr $8, (%rsp), %xmm7
pblendw $0xf0, %xmm8, %xmm9
⸩,
  ⸨prog|
vmovdqu (%rsp), %ymm0
vmovd %eax, %xmm0
vmovd %xmm1, 16(%rsp)
vmovq %rax, %xmm0
vmovq %xmm3, %xmm2
vmovq %xmm1, 24(%rsp)
vzeroupper
⸩,
  ⸨prog|
seto %al
setno %bl
sets %cl
setns %dl
setp %sil
setnp %dil
setge %r8b
setg %r9b
⸩
].all agreesWithCombinatorParser

-- TODO (now a parse error, which `#guard_msgs` cannot check):
-- /-- error: vmovd takes no two xmm operands -/
-- #guard_msgs in
-- #check ⸨prog| vmovd %xmm0, %xmm1 ⸩

-- TODO (pp.maxSteps: prints as a Lean term):
-- /--
-- info: [⸨dir| vmovd %eax, %xmm0 ⸩, ⸨dir| vmovq %xmm0, 24(%rsp) ⸩, ⸨dir| ❰Instr.avx ⋯ ⋯ ⋯❱ ⸩, ⋯] : List _root_.Directive
-- -/
-- #guard_msgs in
-- #check ⸨prog|
--   vmovd %eax, %xmm0
--   vmovq %xmm0, 24(%rsp)
--   pshufd $0x1b, %xmm5, %xmm6
--   vzeroupper
-- ⸩

variable (rest : List _root_.Directive) in
/-- info: ⸨dir| addq $1, %rax ⸩ :: rest : List (Kraken.Directive Instr ConstExpr) -/
#guard_msgs in
#check (⸨dir| addq $1, %rax ⸩ :: rest)

end sse_and_vex

end Tests

