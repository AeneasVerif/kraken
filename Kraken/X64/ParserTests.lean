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
/--
info: ⸨prog|
  addq %rax, %rbx⸩ : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| addq %rax, %rbx ⸩

-- Test: Immediate operand
/--
info: ⸨prog|
  movq $42, %rax⸩ : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| movq $42, %rax ⸩
-- Expected: [.Instr { address_size := .W64, operation_size := .W64, operation := .mov (.Reg (.low .rax .W64)) (.imm 42) }]

/--
info: ⸨prog|
  movq $0, %rax⸩ : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| movq $0, %rax ⸩

/--
info: ⸨prog|
  pushq $0⸩ : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| pushq $0x0 ⸩

/--
info: ⸨prog|
  pushq $0⸩ : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| pushq $0 ⸩

-- Test: unsuffixed push and pop take their width from a register, else 64 bits
/--
info: ⸨prog|
  pushw %ax⸩ : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| push %ax ⸩

/--
info: ⸨prog|
  pushq $1⸩ : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| push $1 ⸩

/--
info: ⸨prog|
  pushq (%rax)⸩ : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| push (%rax) ⸩

/--
info: ⸨prog|
  popw %ax⸩ : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| pop %ax ⸩

/--
info: ⸨prog|
  popq (%rax)⸩ : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| pop (%rax) ⸩

-- Test: Memory operand with displacement
/--
info: ⸨prog|
  movq 8(%rsp), %rax⸩ : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| movq 8(%rsp), %rax ⸩
-- Expected: [.Instr { address_size := .W64, operation_size := .W64, operation := .mov (.Reg (.low .rax .W64)) (.mem .rsp .none 1 8) }]

-- Test: Memory operand with index and scale
/--
info: ⸨prog|
  movq (%rsi, %r15, 8), %rax⸩ : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| movq (%rsi, %r15, 8), %rax ⸩
-- Expected: [.Instr { address_size := .W64, operation_size := .W64, operation := .mov (.Reg (.low .rax .W64)) (.mem .rsi (some .r15) 8 0) }]

-- Test: movsx/movzx with a memory source, movslq and movsxd
/--
info: ⸨prog|
  movsbw (%rax), %bx⸩ : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| movsbw (%rax), %bx ⸩

/--
info: ⸨prog|
  movsbl (%rax), %ebx⸩ : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| movsbl (%rax), %ebx ⸩

/--
info: ⸨prog|
  movslq (%rax), %rbx⸩ : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| movslq (%rax), %rbx ⸩

/--
info: ⸨prog|
  movsx %eax, %rbx⸩ : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| movslq %eax, %rbx ⸩

/--
info: ⸨prog|
  movslq (%rax), %rbx⸩ : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| movsxd (%rax), %rbx ⸩

/--
info: ⸨prog|
  movsx %eax, %rbx⸩ : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| movsxd %eax, %rbx ⸩

/--
info: ⸨prog|
  movzbl (%rax), %ebx⸩ : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| movzbl (%rax), %ebx ⸩

-- Test: Labeled instruction
/--
info: ⸨prog|
  loop:
  addq $1, %rcx⸩ : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| loop: addq $1, %rcx ⸩
-- Expected: [.Label "loop", .Instr { address_size := .W64, operation_size := .W64, operation := .add (.Reg (.low .rcx .W64)) (.imm 1) }]

-- Test: Conditional jump
/--
info: ⸨prog|
  jnz loop⸩ : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| jnz loop ⸩
-- Expected: [.Instr { address_size := .W64, operation_size := .W64, operation := .jcc .nz "loop" }]

-- Symbol operands, as in GNU as: a bare symbol is a memory operand at that
-- absolute address (a load, not the address), `$sym` is the symbol's address
-- as an immediate, and `sym(%rip)` / `sym(%reg)` are memory operands with a
-- symbolic displacement.
/--
info: ⸨prog|
  movq sym, %rax⸩ : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| movq sym, %rax ⸩

/--
info: ⸨prog|
  movq $sym, %rax⸩ : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| movq $sym, %rax ⸩

/--
info: ⸨prog|
  movq $sym+8, %rax⸩ : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| movq $sym+8, %rax ⸩

/--
info: ⸨prog|
  movq sym(%rip), %rax⸩ : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| movq sym(%rip), %rax ⸩

/--
info: ⸨prog|
  movq sym+8(%rip), %rax⸩ : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| movq sym+8(%rip), %rax ⸩

/--
info: ⸨prog|
  movq sym(%rax), %rbx⸩ : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| movq sym(%rax), %rbx ⸩

/--
info: ⸨prog|
  movq sym-8(%rax, %rcx, 4), %rbx⸩ : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| movq sym-8(%rax,%rcx,4), %rbx ⸩

/--
info: ⸨prog|
  addq %rax, sym⸩ : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| addq %rax, sym ⸩

/--
info: ⸨prog|
  movups sym(%rip), %xmm0⸩ : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| movups sym(%rip), %xmm0 ⸩

-- Neighbouring forms: lea, branch targets, numeric
-- RIP-relative offsets.
/--
info: ⸨prog|
  lea sym(%rip), %rax⸩ : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| leaq sym(%rip), %rax ⸩

/--
info: ⸨prog|
  lea sym(%rax), %rax⸩ : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| leaq sym(%rax), %rax ⸩

/--
info: ⸨prog|
  jmp sym⸩ : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| jmp sym ⸩

/--
info: ⸨prog|
  call sym⸩ : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| call sym ⸩

/--
info: ⸨prog|
  movq 8(%rip), %rax⸩ : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| movq 8(%rip), %rax ⸩

-- Like a bare symbol, a bare number is a memory operand at that absolute
-- address (`as`: `mov 0x1,%rax`, `xor %rax,0x1`).
/--
info: ⸨prog|
  movq 1, %rax⸩ : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| movq 1, %rax ⸩

/--
info: ⸨prog|
  xorq %rax, 1⸩ : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| xorq %rax, 1 ⸩

-- Test: Multi-line program
/--
info: ⸨prog|
  movq $0, %rax
  loop:
  addq $1, %rax
  cmpq $10, %rax
  jnz loop⸩ : List _root_.Directive
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
/--
info: ⸨prog|
  addq $-1, %rax⸩ : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| addq $-1, %rax ⸩

-- Test: Hex immediate
/--
info: ⸨prog|
  movq $255, %rax⸩ : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| movq $0xff, %rax ⸩

-- Test: mulx instruction
/--
info: ⸨prog|
  mulx %r8, %r9, %r10⸩ : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| mulxq %r8, %r9, %r10 ⸩

-- Test: xor for zeroing
/--
info: ⸨prog|
  xorq %rax, %rax⸩ : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| xorq %rax, %rax ⸩

-- Test: lea with complex addressing
/--
info: ⸨prog|
  lea 16(%rbp, %rcx, 4), %rax⸩ : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| leaq 16(%rbp, %rcx, 4), %rax ⸩

/--
info: ⸨prog|
  lea 16(%ebp, %ecx, 4), %rax⸩ : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| leaq 16(%ebp, %ecx, 4), %rax ⸩

section data_words

/--
info: ⸨prog|
  .long end-start⸩ : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| .long end - start ⸩

/--
info: ⸨prog|
  .quad sym⸩ : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| .quad sym ⸩

/--
info: ⸨prog|
  .short 7⸩ : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| .short 7 ⸩

/--
info: ⸨prog|
  .long sym+8⸩ : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| .long sym+8 ⸩

/--
info: ⸨prog|
  .quad -1⸩ : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| .quad -1 ⸩

/--
info: ⸨prog|
  movq $b-a, %rax⸩ : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| movq $b-a, %rax ⸩

-- A label that begins with a directive word is still a label.
/--
info: ⸨prog|
  .longest:
  nop⸩ : List _root_.Directive
-/
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
  ⸨prog| .quad -1 ⸩, ⸨prog| movq $b-a, %rax ⸩, ⸨prog|
.longest:
  nop
⸩].all agreesWithCombinatorParser

end data_words

section error_reporting

local elab "elabX64% " s:str : term => elabX64 s.getString

/-- error: <input>:1:5: unexpected end of input -/
#guard_msgs in
#check elabX64% ".long"

/-- error: <input>:1:12: expected x64_reg_name -/
#guard_msgs in
#check elabX64% "xorq %rax, %unlikely"

/-- error: type error: w64 != w32 -/
#guard_msgs in
#check ⸨prog| mov (%rax, %ebx), %rax ⸩

/-- error: can't have two memory operands -/
#guard_msgs in
#check ⸨prog| mov (%rax), (%rax) ⸩

/-- error: high byte register cannot be used for an addrexpr -/
#guard_msgs in
#check ⸨prog| mov $2, (%ah) ⸩

/-- error: <input>:1:9: unexpected end of input; expected ',' -/
#guard_msgs in
#check elabX64% "addq %rax"

/-- error: expected register or memory operand, got $ -/
#guard_msgs in
#check ⸨prog| xorq %rax, $1 ⸩

/-- error: can't have two memory operands -/
#guard_msgs in
#check ⸨prog| movq sym, sym2 ⸩

/-- error: absolute branch targets are not supported -/
#guard_msgs in
#check ⸨prog| jmp 0x10 ⸩

/-- error: <input>:1:4: unexpected end of input -/
#guard_msgs in
#check elabX64% "addq"

/-- error: <input>:3:2: expected ',' -/
#guard_msgs in
#check elabX64% "
  addq %rax
  cmpq $10, %rax
"

/-- error: type error: w64 != w32 -/
#guard_msgs in
#check ⸨prog| movq %eax, %rbx ⸩

/-- error: invalid scale 3, must be 1, 2, 4, or 8 -/
#guard_msgs in
#check ⸨prog| movq (%rax, %rcx, 3), %rbx ⸩

/-- error: <input>:1:16: unexpected element; expected ';' -/
#guard_msgs in
#check elabX64% "movq %rax, %rbx garbage"

/-- error: <input>:1:9: unexpected element; expected ';' -/
#guard_msgs in
#check elabX64% "shlq %rcx, %rax"

/-- error: <input>:1:0: expected end of input -/
#guard_msgs in
#check elabX64% "foo\n:"

end error_reporting

section syntax_cat_and_include

/--
info: ⸨prog|
  loop:
  addq $1, %rax
  jnz loop⸩ : List _root_.Directive
-/
#guard_msgs in
#check ⸨prog|
  loop:
    addq $1, %rax
    jnz loop
⸩

/--
info: ⸨prog|
  nop⸩ : List _root_.Directive
-/
#guard_msgs in
#check include_x64 "Kraken/X64/Test/asm/test_nop.S"

/--
info: ⸨prog|
  aa.1.aa.1:
  jmp .L.str.1.llvm.12345⸩ : List _root_.Directive
-/
#guard_msgs in
#check ⸨prog|
  aa.1.aa.1:
    jmp .L.str.1.llvm.12345
⸩

/-- info: ⸨dir| addq $1, %rax ⸩ : Kraken.Directive Instr ConstExpr -/
#guard_msgs in
#check ⸨dir| addq $1, %rax ⸩

/-- info: ⸨dir 1| addq $1, %rax ⸩ : Sized _root_.Directive -/
#guard_msgs (whitespace := lax) in
variable [Kraken.Layout Instr ConstExpr] in
#check ⸨dir 1 | addq $1, %rax ⸩

end syntax_cat_and_include

section antiquotations

variable {w : Width} (r : Reg w) (q : Reg .W64) (r64 : Reg64) (v : AvxReg .W256)

-- Test: an antiquoted register decides the width of its instruction, which may be a variable
/--
info: ⸨prog|
  add $2, %❰r❱⸩ : List _root_.Directive
-/
#guard_msgs in
#check ⸨prog| add $2, %❰r❱ ⸩

-- Test: antiquoted and concrete registers unify
/--
info: ⸨prog|
  movq %rax, %❰q❱⸩ : List _root_.Directive
-/
#guard_msgs in
#check ⸨prog| mov %rax, %❰q❱ ⸩

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
#check ⸨prog| addq $1, %❰r❱ ⸩

/-- error: type error: w != w32 -/
#guard_msgs in
#check ⸨prog| add %❰r❱, %eax ⸩

-- Test: in address positions, antiquotations denote `Reg64`
/--
info: ⸨prog|
  movq 8(%❰r64❱, %rax, 4), %rcx⸩ : List _root_.Directive
-/
#guard_msgs in
#check ⸨prog| mov 8(%❰r64❱, %rax, 4), %rcx ⸩

-- Test: AVX registers
/--
info: ⸨prog|
  vmovups (%rax), %❰v❱⸩ : List _root_.Directive
-/
#guard_msgs in
#check ⸨prog| vmovups (%rax), %❰v❱ ⸩

-- Test: a width that no operand or suffix determines is an error
/-- error: could not infer operand width -/
#guard_msgs in
#check ⸨prog| add $1, (%rax) ⸩

-- Test: the source of a widening move must be narrower than its destination
/-- error: source width w64 must be narrower than destination width w16 -/
#guard_msgs in
#check ⸨prog| movsx %rax, %bx ⸩

-- Test: antiquotations for operands, instructions and directives
variable (o : Operand .W32) (rm : RegOrMem w) (av : AvxRegOrMem .W128) (rt : RelRegOrMem) (i : Instr) (d : Directive)

/--
info: ⸨prog|
  addl ❰o❱, %eax⸩ : List _root_.Directive
-/
#guard_msgs in
#check ⸨prog| add ❰o❱, %eax ⸩

/--
info: ⸨prog|
  inc ❰rm❱⸩ : List _root_.Directive
-/
#guard_msgs in
#check ⸨prog| inc ❰rm❱ ⸩

/--
info: ⸨prog|
  movaps ❰av❱, %xmm1⸩ : List _root_.Directive
-/
#guard_msgs in
#check ⸨prog| movaps ❰av❱, %xmm1 ⸩

/--
info: ⸨prog|
  jmp ❰rt❱⸩ : List _root_.Directive
-/
#guard_msgs in
#check ⸨prog| jmp ❰rt❱ ⸩

/--
info: ⸨prog|
  ❰Directive.instr i❱
  ❰d❱
  ret⸩ : List _root_.Directive
-/
#guard_msgs in
#check ⸨prog| ❰.instr i❱; ❰d❱; ret ⸩

/--
info: ⸨prog|
  foo:
  ret⸩ : List _root_.Directive
-/
#guard_msgs in
#check ⸨prog| ❰.label "foo"❱; ❰.instr <| .regular .W64 .W64 .ret❱ ⸩

-- Test: label antiquotations (`x64_ident`)
variable (lbl : Kraken.Label)

/--
info: ⸨prog|
  ❰lbl❱:
  ret⸩ : List _root_.Directive
-/
#guard_msgs in
#check ⸨prog| ❰lbl❱: ret ⸩

/--
info: ⸨prog|
  jz ❰lbl❱⸩ : List _root_.Directive
-/
#guard_msgs in
#check ⸨prog| jz ❰lbl❱ ⸩

/--
info: ⸨prog|
  movq $❰lbl❱, %rax⸩ : List _root_.Directive
-/
#guard_msgs in
#check ⸨prog| movq $❰lbl❱, %rax ⸩

/--
info: ⸨prog|
  movq $❰lbl❱+8, %rax⸩ : List _root_.Directive
-/
#guard_msgs in
#check ⸨prog| movq $❰lbl❱+8, %rax ⸩

/--
info: ⸨prog|
  movq $❰lbl❱-8, %rax⸩ : List _root_.Directive
-/
#guard_msgs in
#check ⸨prog| movq $❰lbl❱-8, %rax ⸩

/--
info: ⸨prog|
  lea ❰lbl❱(%rip), %rax⸩ : List _root_.Directive
-/
#guard_msgs in
#check ⸨prog| leaq ❰lbl❱(%rip), %rax ⸩

/--
info: ⸨prog|
  movq ❰lbl❱+8(%rip), %rax⸩ : List _root_.Directive
-/
#guard_msgs in
#check ⸨prog| movq ❰lbl❱+8(%rip), %rax ⸩

/--
info: ⸨prog|
  movq ❰lbl❱-8(%rax, %rcx, 4), %rdx⸩ : List _root_.Directive
-/
#guard_msgs in
#check ⸨prog| movq ❰lbl❱-8(%rax, %rcx, 4), %rdx ⸩

/--
info: ⸨prog|
  movq ❰lbl❱+8, %rax⸩ : List _root_.Directive
-/
#guard_msgs in
#check ⸨prog| movq ❰lbl❱+8, %rax ⸩

/--
info: ⸨prog|
  .long ❰lbl❱-start⸩ : List _root_.Directive
-/
#guard_msgs in
#check ⸨prog| .long ❰lbl❱ - start ⸩

/--
error: Type mismatch
  r
has type
  Reg w
but is expected to have type
  Kraken.Label
-/
#guard_msgs in
#check ⸨prog| jz ❰r❱ ⸩

-- Test: `Int64` / `ConstExpr` antiquotations (`x64_const` and `x64_operand`)
variable (imm : Int64) (ce : ConstExpr)

/--
info: ⸨prog|
  movq $❰imm❱, %rax⸩ : List _root_.Directive
-/
#guard_msgs in
#check ⸨prog| mov $❰imm❱, %rax ⸩

/--
info: ⸨prog|
  movq $❰imm❱, %rax⸩ : List _root_.Directive
-/
#guard_msgs in
#check ⸨prog| mov ❰imm❱, %rax ⸩

/--
info: ⸨prog|
  movl $❰imm❱, %eax⸩ : List _root_.Directive
-/
#guard_msgs in
#check ⸨prog| mov ❰imm❱, %eax ⸩

/--
info: ⸨prog|
  pushq $❰imm❱⸩ : List _root_.Directive
-/
#guard_msgs in
#check ⸨prog| push ❰imm❱ ⸩

/--
info: ⸨prog|
  movq ❰imm❱(%rsp), %rax⸩ : List _root_.Directive
-/
#guard_msgs in
#check ⸨prog| movq ❰imm❱(%rsp), %rax ⸩

/--
info: ⸨prog|
  movq ❰imm❱(%rip), %rax⸩ : List _root_.Directive
-/
#guard_msgs in
#check ⸨prog| movq ❰imm❱(%rip), %rax ⸩

/--
info: ⸨prog|
  movq $❰ce❱, %rax⸩ : List _root_.Directive
-/
#guard_msgs in
#check ⸨prog| mov $❰ce❱, %rax ⸩

end antiquotations

-- Test: flag control instructions (`cld`/`std`), string parser and `⸨prog| ⸩` syntax
/--
info: ⸨prog|
  cld
  std⸩ : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog|
cld
std
⸩

/--
info: ⸨prog|
  cld
  std⸩ : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| cld; std ⸩

-- Test: processor identification (`cpuid`/`xgetbv`)
#guard [⸨prog| cpuid; xgetbv ⸩].all agreesWithCombinatorParser
#guard ⸨instr| cpuid ⸩ = Instr.regular .W64 .W64 .cpuid

/--
info: ⸨prog|
  cpuid
  xgetbv⸩ : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| cpuid; xgetbv ⸩

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
addr32 movsb
addr32 rep movsq
addr32 stosl
addr32 rep stosw
⸩
].all agreesWithCombinatorParser

#guard ⸨instr| addr32 rep movsb ⸩ = Instr.regular .W32 .W8 (.movs true)
#guard ⸨instr| stosq ⸩ = Instr.regular .W64 .W64 (.stos false)

/--
info: ⸨prog|
  rep movsb
  movsq
  addr32 rep stosl
  addr32 stosw⸩ : List _root_.Directive
-/
#guard_msgs in
#check ⸨prog|
  rep movsb
  movsq
  addr32 rep stosl
  addr32 stosw
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
pxor %xmm1, %xmm2
pand 16(%rsp), %xmm3
pandn %xmm15, %xmm14
psrld $7, %xmm4
pslld $0x20, %xmm15
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

/-- error: vmovd takes no two xmm operands -/
#guard_msgs in
#check ⸨prog| vmovd %xmm0, %xmm1 ⸩

/--
info: ⸨prog|
  vmovd %eax, %xmm0
  vmovq %xmm0, 24(%rsp)
  pshufd $27, %xmm5, %xmm6
  vzeroupper⸩ : List _root_.Directive
-/
#guard_msgs in
#check ⸨prog|
  vmovd %eax, %xmm0
  vmovq %xmm0, 24(%rsp)
  pshufd $0x1b, %xmm5, %xmm6
  vzeroupper
⸩

/--
info: ⸨prog|
  pxor %xmm1, %xmm2
  pandn (%rax), %xmm3
  psrld $7, %xmm4
  pslld $32, %xmm5⸩ : List _root_.Directive
-/
#guard_msgs in
#check ⸨prog|
  pxor %xmm1, %xmm2
  pandn (%rax), %xmm3
  psrld $7, %xmm4
  pslld $0x20, %xmm5
⸩

variable (rest : List _root_.Directive) in
/--
info: ⸨prog|
    addq $1, %rax⸩ ++
  rest : List (Kraken.Directive Instr ConstExpr)
-/
#guard_msgs in
#check (⸨dir| addq $1, %rax ⸩ :: rest)

end sse_and_vex

section sha_and_avx512

#guard [
  ⸨prog|
sha256rnds2 %xmm0, %xmm1, %xmm2
sha256rnds2 (%rsp), %xmm3
sha256msg1 %xmm4, %xmm5
sha256msg2 16(%rsp), %xmm6
⸩,
  ⸨prog|
vmovdqu32 (%rsp), %zmm0
vmovdqa32 %zmm1, 64(%rsp)
vpaddd %zmm2, %zmm3, %zmm4
vpaddd (%rax), %ymm5, %ymm6
vprord $7, %zmm7, %zmm8
vpsrld $3, %xmm9, %xmm10
vpternlogd $0xca, %zmm11, %zmm12, %zmm13
vpternlogd $0x96, 64(%rsp), %zmm14, %zmm31
⸩,
  ⸨prog|
vpshufb %zmm0, %zmm1, %zmm2
vpshufb (%rax), %ymm3, %ymm4
vshufps $0x44, %zmm5, %zmm6, %zmm7
vshufps $0xdd, 64(%rsp), %xmm8, %xmm9
vpermi2q %zmm10, %zmm11, %zmm12
vpermi2d (%rsp), %zmm13, %zmm24
vinserti64x4 $1, %ymm14, %zmm15, %zmm16
vinserti64x4 $0, 32(%rsp), %zmm17, %zmm18
⸩,
  ⸨prog|
vpslld $3, %xmm1, %xmm2
vpslld $10, (%rsp), %ymm3
vpslld $31, %zmm4, %zmm5
vmovdqa (%rsp), %xmm0
vmovdqa %ymm1, 32(%rsp)
vmovdqa %ymm2, %ymm3
vpand %xmm0, %xmm1, %xmm2
vpandn (%rax), %ymm3, %ymm4
vpor %ymm5, %ymm6, %ymm7
vpxor 32(%rsp), %xmm8, %xmm15
vpunpckldq %xmm0, %xmm1, %xmm2
vpunpckhdq (%rax), %ymm3, %ymm4
vpunpcklqdq %zmm5, %zmm6, %zmm7
vpunpckhqdq 64(%rsp), %zmm8, %zmm25
vperm2i128 $0x20, %ymm9, %ymm10, %ymm11
vperm2i128 $0x31, 32(%rsp), %ymm12, %ymm13
⸩
].all agreesWithCombinatorParser

/-- error: the implicit operand of sha256rnds2 is %xmm0 -/
#guard_msgs in
#check ⸨prog| sha256rnds2 %xmm1, %xmm2, %xmm3 ⸩

/-- error: type error: w256 != w512 -/
#guard_msgs in
#check ⸨prog| vinserti64x4 $1, %zmm14, %zmm15, %zmm16 ⸩

/--
info: ⸨prog|
  sha256rnds2 %xmm0, %xmm1, %xmm2
  vpaddd (%rax), %ymm5, %ymm6
  vpternlogd $202, %zmm11, %zmm12, %zmm13
  vpermi2q %zmm10, %zmm11, %zmm12
  vinserti64x4 $1, 32(%rsp), %zmm15, %zmm16⸩ : List _root_.Directive
-/
#guard_msgs in
#check ⸨prog|
  sha256rnds2 %xmm1, %xmm2
  vpaddd (%rax), %ymm5, %ymm6
  vpternlogd $0xca, %zmm11, %zmm12, %zmm13
  vpermi2q %zmm10, %zmm11, %zmm12
  vinserti64x4 $1, 32(%rsp), %zmm15, %zmm16
⸩

/-- error: type error: w256 != w512 -/
#guard_msgs in
#check ⸨prog| vperm2i128 $0x20, %zmm9, %zmm10, %zmm11 ⸩

/--
info: ⸨prog|
  vpunpckldq %xmm0, %xmm1, %xmm2
  vpunpckhqdq 64(%rsp), %zmm8, %zmm25
  vperm2i128 $49, 32(%rsp), %ymm12, %ymm13⸩ : List _root_.Directive
-/
#guard_msgs in
#check ⸨prog|
  vpunpckldq %xmm0, %xmm1, %xmm2
  vpunpckhqdq 64(%rsp), %zmm8, %zmm25
  vperm2i128 $0x31, 32(%rsp), %ymm12, %ymm13
⸩

end sha_and_avx512

section avx2_bitwise

local elab "elabX64% " s:str : term => elabX64 s.getString

/-- error: vpxor has no 512-bit form -/
#guard_msgs in
#check ⸨prog| vpxor %zmm0, %zmm1, %zmm2 ⸩

/-- error: vmovdqa has no 512-bit form -/
#guard_msgs in
#check ⸨prog| vmovdqa (%rsp), %zmm0 ⸩

/-- error: vpandn has no 512-bit form -/
#guard_msgs in
#check elabX64% "vpandn %zmm0, %zmm1, %zmm2"

/-- error: vmovdqa has no 512-bit form -/
#guard_msgs in
#check elabX64% "vmovdqa %zmm0, 64(%rsp)"

/--
info: ⸨prog|
  vpslld $10, (%rsp), %ymm3
  vmovdqa %ymm1, 32(%rsp)
  vpandn (%rax), %ymm3, %ymm4
  vpxor %xmm0, %xmm1, %xmm2⸩ : List _root_.Directive
-/
#guard_msgs in
#check ⸨prog|
  vpslld $10, (%rsp), %ymm3
  vmovdqa %ymm1, 32(%rsp)
  vpandn (%rax), %ymm3, %ymm4
  vpxor %xmm0, %xmm1, %xmm2
⸩

end avx2_bitwise
section division

#guard [
  ⸨prog|
divb %bl
divw %cx
divl %r8d
divq %rbx
div %r9
divb (%rsp)
divq 8(%rsp,%rcx,8)
divl (%eax)
⸩
].all agreesWithCombinatorParser

#guard ⸨instr| divq %rbx ⸩ = Instr.regular .W64 .W64 (.div (.reg (.low .rbx .W64)))

/--
info: ⸨prog|
  divb %ah
  divl %r8d
  divq 8(%rsp)⸩ : List _root_.Directive
-/
#guard_msgs in
#check ⸨prog|
  divb %ah
  div %r8d
  divq 8(%rsp)
⸩

end division

end Tests

