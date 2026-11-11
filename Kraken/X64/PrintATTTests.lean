module

/-
  Round-trip tests for the AT&T printer: `parse (toATT p) = .ok p` for programs
  `p` produced by `parse`.
-/

import Kraken.X64.Parser
meta import Kraken.X64.Parser
import Kraken.X64.PrintATT
meta import Kraken.X64.PrintATT
import Kraken.X64.Semantics
meta import Kraken.X64.Semantics

open Kraken.X64 Kraken.X64.Parser Kraken.Parser

/-- `s` parses, and printing the result then re-parsing gives the same program. -/
def roundtrips (s : String) : Bool :=
  match parse s with
  | .ok p => match parse (toATT p) with
    | .ok p' => p' == p
    | .error _ => false
  | .error _ => false

/-- clang `-O2` output for `switch (x) { case 0: return 10; case 1: return 20; case 2: return 30;
default: return 0; }`, with its jump table behind the code. -/
def jumpTable : String :=
  "sel:\n  cmpl $2, %edi\n  ja .Ldefault\n  movl %edi, %eax\n  leaq .LJTI0_0(%rip), %rcx\n  movslq (%rcx,%rax,4), %rax\n  addq %rcx, %rax\n  jmp %rax\n.Lcase0:\n  movl $10, %eax\n  ret\n.Lcase1:\n  movl $20, %eax\n  ret\n.Lcase2:\n  movl $30, %eax\n  ret\n.Ldefault:\n  xorl %eax, %eax\n  ret\n  .align 4\n.LJTI0_0:\n  .long .Lcase0 - .LJTI0_0\n  .long .Lcase1 - .LJTI0_0\n  .long .Lcase2 - .LJTI0_0\n"

/-- One line per `Operation`/`AvxOperation` constructor and operand form. -/
def corpus : List String := [
  -- data movement, all widths and operand kinds
  "movq $42, %rax", "movl $-1, %r9d", "movw %ax, %r15w", "movb %ah, %sil",
  "movabsq $0xFFFFFFFFFFFFFFFF, %rdx", "movq $-9223372036854775808, %rdx",
  "movq sym, %rax", "movq $sym+8, %rax", "movq sym-4(%rax), %rcx", "addq 16, %rax", "pushq sym",
  "movq 8(%rsp), %rax", "movq %rax, -16(%rbp,%rcx,8)",
  "movb $1, (%eax)", "movl %eax, 4(%r8d,%r9d,2)", "movq (%rax,%rbx), %rcx",
  "movq 8(%rip), %rax", "movsx %al, %ecx", "movzx %bx, %rdx", "movsbq %al, %rax",
  "movzwl %cx, %edx", "movsbl (%rsp), %ecx", "movzwq 8(%rax), %rdx", "movslq (%rax), %rbx",
  "movsxd %eax, %rbx", "pushq %rbx", "pushq $7", "pushw (%rsp)", "popq %rax", "popq 8(%rsp)",
  "sete %al", "setnz 3(%rsp)", "setb %dh", "setae %bl", "seta %cl", "setbe %al",
  "setl %al", "setle %al", "seto %al", "setno %al", "sets %al", "setns %al",
  "setp %al", "setnp %al", "setge %al", "setg %al",
  "cmovz %rax, %rbx", "cmovl (%rsp), %ecx", "cmovge %rax, %rbx", "cmovg (%rsp), %ecx",
  "movsb", "movsq", "rep movsb", "rep movsl", "stosw", "rep stosb", "rep stosq",
  "addr32 movsb", "addr32 rep movsq", "addr32 stosl", "addr32 rep stosw",
  -- arithmetic
  "leaq 8(%rax,%rbx,4), %rcx", "leal (%eax), %ecx", "lea sym(%rip), %rax",
  "addq $1, %rax", "addb %al, (%rsp)", "adcl (%rsp), %eax", "adcx %rax, %rbx",
  "adox (%rsp), %ecx", "incq %rax", "incb (%rsp)", "decw %ax", "negl %eax",
  "subq %rax, %rbx", "sbbb $1, %al", "cmpq $0, (%rsp)", "cmpl %eax, %ebx",
  "mulq %rbx", "mulb (%rsp)", "mulx %rax, %rbx, %rcx", "mulxl (%rsp), %eax, %ebx",
  "imulq %rbx", "imulw %ax, %bx", "imulq (%rsp), %rbx", "imulq $3, %rax, %rbx",
  "imull $-3, (%rsp), %eax", "divb %bl", "divw %cx", "divl (%rsp)", "divq %rbx", "divb (%rsp)",
  -- bitwise
  "testq $1, %rax", "testb %al, (%rsp)", "andq %rax, %rbx", "notq %rax",
  "orw $5, %ax", "xorl %eax, %eax",
  "shlq %rax", "shlq $3, %rax", "shlb %cl, (%rsp)", "salq $1, %rax",
  "shrw $2, %ax", "sarl %cl, %eax", "shldq $4, %rax, %rbx", "shrd %cl, %ax, (%rsp)",
  "rolq $1, %rax", "rorb %cl, %al", "rclq $1, %rax", "rcrl %cl, (%rsp)",
  "bswap %eax", "bswapq %rax",
  -- flag control
  "cld", "std",
  -- control flow
  "foo:\n  jmp foo", "je foo", "jne .L1", "jb foo", "jae foo", "ja foo", "jbe foo",
  "jl foo", "jle foo", "call foo", "call %rax", "jmp %rax",
  "jmp 8(%rax)", "call (%rsp)", "ret", "nop", "nop 5", ".align 16", ".align 16, 0x90",
  "a:\nb: ret\n\nc:",
  -- AVX
  "movups %xmm0, %xmm1", "vmovups (%rsp), %ymm2", "vmovups %zmm31, 64(%rsp)",
  "movaps %xmm3, %xmm4", "addps (%rax), %xmm5", "subps %xmm6, %xmm7",
  "movdqu (%rsp), %xmm0", "movdqa %xmm1, 16(%rsp)", "paddd (%rax), %xmm2", "pshufb %xmm3, %xmm4",
  "pshufd $0x1b, %xmm5, %xmm6", "palignr $8, (%rsp), %xmm7", "pblendw $0xf0, %xmm8, %xmm9",
  "pxor %xmm1, %xmm2", "pand 16(%rsp), %xmm3", "pandn %xmm15, %xmm14", "psrld $7, %xmm4",
  "pslld $32, %xmm15",
  "vmovdqu (%rsp), %xmm0", "vmovdqu %ymm1, 32(%rsp)", "vmovdqu %ymm2, %ymm3",
  "vmovd %eax, %xmm4", "vmovd 4(%rsp), %xmm5", "vmovd %xmm6, %r9d", "vmovd %xmm7, (%rsp)",
  "vmovq %rax, %xmm8", "vmovq 8(%rsp), %xmm9", "vmovq %xmm10, %rbx", "vmovq %xmm11, (%rsp)",
  "vmovq %xmm12, %xmm13", "vzeroupper",
  "sha256rnds2 %xmm0, %xmm2, %xmm1", "sha256rnds2 (%rax), %xmm3", "sha256rnds2 %xmm0, %xmm4", "sha256msg1 %xmm4, %xmm5",
  "sha256msg2 16(%rsp), %xmm6",
  "vmovdqu32 (%rsp), %zmm0", "vmovdqa32 %zmm1, 64(%rsp)", "vpaddd %zmm2, %zmm3, %zmm4",
  "vpaddd (%rax), %ymm5, %ymm6", "vprord $7, %zmm7, %zmm8", "vpsrld $3, %xmm9, %xmm10",
  "vpternlogd $0xca, %zmm11, %zmm12, %zmm13", "vpternlogd $0x96, 64(%rsp), %zmm14, %zmm31",
  "vpshufb %zmm0, %zmm1, %zmm2", "vpshufb (%rax), %ymm3, %ymm4", "vshufps $0x44, %zmm5, %zmm6, %zmm7",
  "vshufps $0xdd, 64(%rsp), %xmm8, %xmm9", "vpermi2q %zmm10, %zmm11, %zmm12", "vpermi2d (%rsp), %zmm13, %zmm24",
  "vinserti64x4 $1, %ymm14, %zmm15, %zmm16", "vinserti64x4 $0, 32(%rsp), %zmm17, %zmm18",
  "vpslld $3, %xmm1, %xmm2", "vpslld $10, (%rsp), %ymm3", "vpslld $31, %zmm4, %zmm5",
  "vmovdqa (%rsp), %xmm0", "vmovdqa %ymm1, 32(%rsp)", "vmovdqa %ymm2, %ymm3",
  "vpand %xmm0, %xmm1, %xmm2", "vpandn (%rax), %ymm3, %ymm4", "vpor %ymm5, %ymm6, %ymm7",
  "vpxor 32(%rsp), %xmm8, %xmm15",
  "vpunpckldq %xmm0, %xmm1, %xmm2", "vpunpckhdq (%rax), %ymm3, %ymm4", "vpunpcklqdq %zmm5, %zmm6, %zmm7",
  "vpunpckhqdq 64(%rsp), %zmm8, %zmm25", "vperm2i128 $0x20, %ymm9, %ymm10, %ymm11",
  "vperm2i128 $0x31, 32(%rsp), %ymm12, %ymm13",
  -- data words: a label, a difference of labels, a literal
  ".short sym", "a:\nb:\n  .short b - a", ".short 7",
  ".long sym", "a:\nb:\n  .long b-a", ".long -1",
  ".quad sym", "a:\nb:\n  .quad b-a", ".quad 0xFFFFFFFFFFFFFFFF", ".quad sym+8",
  "movq $b-a, %rax",
  -- a jump table: clang -O2 output for a three-case switch
  jumpTable
]

/-- info: [] -/
#guard_msgs in
#eval corpus.filter (!roundtrips ·)

-- Data words keep their symbolic value.
#guard match parse ".LJT:\n  .long .Lcase0 - .LJT\n  .quad 5" with
  | .ok p => p == [.label ".LJT", .word 4 (.sub (.label ".Lcase0") (.label ".LJT")),
      .word 8 (.int64 5)]
  | .error _ => false

-- The jump-table entries are label differences, kept symbolic, so a jump table round-trips
-- without fixing the layout.
#guard match parse jumpTable with
  | .ok p =>
    let table := p.drop (p.length - 3)
    table == [0, 1, 2].map (fun k => .word 4 (.sub (.label s!".Lcase{k}") (.label ".LJTI0_0"))) &&
      (table.map (_root_.Directive.fakeSize 0)).sum == 12
  | .error _ => false

-- Data words print with the directive of their size.
#guard toATT [.word 1 (.label "a"), .word 2 (.label "a"), .word 4 (.int64 3),
    .word 8 (.sub (.label "b") (.label "a"))] == ".byte a\n.short a\n.long 3\n.quad b-a"

-- `vperm2i128` exists at 256 bits only.
#guard ["vperm2i128 $0x20, %xmm9, %xmm10, %xmm11", "vperm2i128 $0x20, %zmm9, %zmm10, %zmm11"].all
  fun s => (parse s).toOption.isNone

#guard ["cmove %ax, %bx", "cmovzl %eax, %ebx", "cmovnew %ax, %bx", "cmovnel %eax, %ebx", "cmovneq %rax, %rbx"].all roundtrips

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
