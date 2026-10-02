module

/-
  Round-trip tests for the AT&T printer: `parse (toATT p) = .ok p` for programs
  `p` produced by `parse`.
-/

import Kraken.X64.Parser
meta import Kraken.X64.Parser
import Kraken.X64.PrintATT
meta import Kraken.X64.PrintATT

open Kraken.X64 Kraken.X64.Parser

/-- `s` parses, and printing the result then re-parsing gives the same program. -/
def roundtrips (s : String) : Bool :=
  match parse s with
  | .ok p => match parse (toATT p) with
    | .ok p' => p' == p
    | .error _ => false
  | .error _ => false

/-- One line per `Operation`/`AvxOperation` constructor and operand form. -/
def corpus : List String := [
  -- data movement, all widths and operand kinds
  "movq $42, %rax", "movl $-1, %r9d", "movw %ax, %r15w", "movb %ah, %sil",
  "movabsq $0xFFFFFFFFFFFFFFFF, %rdx", "movq $-9223372036854775808, %rdx",
  "movq sym, %rax", "movq 8(%rsp), %rax", "movq %rax, -16(%rbp,%rcx,8)",
  "movb $1, (%eax)", "movl %eax, 4(%r8d,%r9d,2)", "movq (%rax,%rbx), %rcx",
  "movq 8(%rip), %rax", "movsx %al, %ecx", "movzx %bx, %rdx", "movsbq %al, %rax",
  "movzwl %cx, %edx", "pushq %rbx", "pushq $7", "pushw (%rsp)", "popq %rax", "popq 8(%rsp)",
  "sete %al", "setnz 3(%rsp)", "setb %dh", "setae %bl", "seta %cl", "setbe %al",
  "setl %al", "setle %al", "cmovz %rax, %rbx", "cmovl (%rsp), %ecx",
  -- arithmetic
  "leaq 8(%rax,%rbx,4), %rcx", "leal (%eax), %ecx", "lea sym(%rip), %rax",
  "addq $1, %rax", "addb %al, (%rsp)", "adcl (%rsp), %eax", "adcx %rax, %rbx",
  "adox (%rsp), %ecx", "incq %rax", "incb (%rsp)", "decw %ax", "negl %eax",
  "subq %rax, %rbx", "sbbb $1, %al", "cmpq $0, (%rsp)", "cmpl %eax, %ebx",
  "mulq %rbx", "mulb (%rsp)", "mulx %rax, %rbx, %rcx", "mulxl (%rsp), %eax, %ebx",
  "imulq %rbx", "imulw %ax, %bx", "imulq (%rsp), %rbx", "imulq $3, %rax, %rbx",
  "imull $-3, (%rsp), %eax",
  -- bitwise
  "testq $1, %rax", "testb %al, (%rsp)", "andq %rax, %rbx", "notq %rax",
  "orw $5, %ax", "xorl %eax, %eax",
  "shlq %rax", "shlq $3, %rax", "shlb %cl, (%rsp)", "salq $1, %rax",
  "shrw $2, %ax", "sarl %cl, %eax", "shldq $4, %rax, %rbx", "shrd %cl, %ax, (%rsp)",
  "rolq $1, %rax", "rorb %cl, %al", "rclq $1, %rax", "rcrl %cl, (%rsp)",
  "bswap %eax", "bswapq %rax",
  -- control flow
  "foo:\n  jmp foo", "je foo", "jne .L1", "jb foo", "jae foo", "ja foo", "jbe foo",
  "jl foo", "jle foo", "call foo", "call %rax", "jmp %rax",
  "jmp 8(%rax)", "call (%rsp)", "ret", "nop", "nop 5", ".align 16", ".align 16, 0x90",
  "a:\nb: ret\n\nc:",
  -- AVX
  "movups %xmm0, %xmm1", "vmovups (%rsp), %ymm2", "vmovups %zmm31, 64(%rsp)",
  "movaps %xmm3, %xmm4", "addps (%rax), %xmm5", "subps %xmm6, %xmm7"
]

/-- info: [] -/
#guard_msgs in
#eval corpus.filter (!roundtrips ·)

-- Printed form is canonical AT&T.
#guard match parse "movq %rax, -16(%rbp,%rcx,8)\nfoo: imul $3, 8(%eax), %ebx\njne foo\nnop" with
  | .ok p => toATT p == "movq %rax, -16(%rbp,%rcx,8)\nfoo:\nimull $3, 8(%eax), %ebx\njne foo\nnop"
  | .error _ => false

-- Every program in the hardware test corpus round-trips.
#eval show IO Unit from do
  for f in ← System.FilePath.readDir "Kraken/X64/Test/asm" do
    if f.path.extension == some "S" then
      unless roundtrips (stripDirectives (← IO.FS.readFile f.path)) do
        throw <| .userError s!"{f.path} does not round-trip"

/-- The mnemonics of family `α` for which one of `forms` doesn't round-trip. -/
def failing (α) [Mnemonic α] (forms : α → String → List String) : List String :=
  (Mnemonic.names (α := α)).toList.filterMap fun (op, mn) =>
    if (forms op mn).all roundtrips then none else some mn

/-- Programs the parser rejects. -/
def rejected : List String := [
  -- `rep` prefixes only apply to string instructions.
  "rep addq %rax, %rbx", "rep nop", "rep ret",
  -- EVEX-only registers: the model has no EVEX forms except `vmovups`
  "movups %xmm16, %xmm1"
]

/-- info: [] -/
#guard_msgs in
#eval rejected.filter (parse · matches .ok _)
