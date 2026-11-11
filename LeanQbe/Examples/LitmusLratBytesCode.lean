module

public import LeanQbe.Examples.Litmus
public import LeanQbe.Examples.LratBytes
public import LeanQbe.MainLemmas
import all Kraken.Separation
import all Kraken.Mem

/-!
# Untrusted-bytes LRAT proof checker end to end on x64 (`lrat_check_bytes`)

Compiles the six-function verified untrusted-bytes LRAT checker module `LratBytes.lratBytesFns`:
* `lb_parse_dimacs_header` (136-byte stack bound)
* `lb_parse_dimacs_body` (664-byte stack bound)
* `lb_read_add_lits` (168-byte stack bound)
* `lb_rup_check` (632-byte stack bound)
* `lb_check_prf` (728-byte stack bound)
* `lrat_check_bytes` (968-byte stack bound)

through the verified fast-path x64 pipeline (`compileModule Amd64.fastIsa`), checks the emitted x64
assembly (2,268 directives) and computed stack bounds in the kernel (`kernel_rfl`), and instantiates
a concrete x64 `Host` (`lratBytesHost`) with unique labels (`lratBytesHost_unique`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.Litmus

open LeanQbe LeanQbe.LratBytes Rega Amd64 Kraken Kraken.X64

abbrev lbHdrFn : Fn := ⟨"lb_parse_dimacs_header", lbParseDimacsHeader⟩
abbrev lbBodyFn : Fn := ⟨"lb_parse_dimacs_body", lbParseDimacsBody⟩
abbrev lbAddLitsFn : Fn := ⟨"lb_read_add_lits", lbReadAddLits⟩
abbrev lbRupCheckFn : Fn := ⟨"lb_rup_check", lbRupCheck⟩
abbrev lbCheckPrfFn : Fn := ⟨"lb_check_prf", lbCheckPrf⟩
abbrev lbCheckBytesFn : Fn := ⟨"lrat_check_bytes", lratCheckBytes⟩

def hdrCode : Program := parse("lb_parse_dimacs_header:
subq $24, %rsp
movq %rbx, (%rsp)
movq %rbp, 8(%rsp)
movq %rdx, %rbp
movq %rdi, %rax
lb_parse_dimacs_header.L2:
cmpq %rsi, %rax
je lb_parse_dimacs_header.L3
movzbl (%rax), %ecx
lea 1(%rax), %rdx
cmpq $32, %rcx
sete %r11b
movzx %r11b, %edi
movq %rcx, %r8
subq $9, %r8
cmpq $5, %r8
setb %r11b
movzx %r11b, %ebx
orq %rbx, %rdi
testl %edi, %edi
jne lb_parse_dimacs_header.L4
cmpq $99, %rcx
je lb_parse_dimacs_header.L5
jmp lb_parse_dimacs_header.L1
lb_parse_dimacs_header.L5:
movq %rdx, %rax
lb_parse_dimacs_header.L6:
cmpq %rsi, %rax
je lb_parse_dimacs_header.L7
movzbl (%rax), %ecx
addq $1, %rax
cmpq $10, %rcx
je lb_parse_dimacs_header.L8
jmp lb_parse_dimacs_header.L6
lb_parse_dimacs_header.L8:
jmp lb_parse_dimacs_header.L2
lb_parse_dimacs_header.L7:
jmp lb_parse_dimacs_header.L1
lb_parse_dimacs_header.L4:
movq %rdx, %rax
jmp lb_parse_dimacs_header.L2
lb_parse_dimacs_header.L3:
lb_parse_dimacs_header.L1:
cmpq %rsi, %rax
je lb_parse_dimacs_header.L9
movzbl (%rax), %ecx
cmpq $112, %rcx
je lb_parse_dimacs_header.L10
jmp lb_parse_dimacs_header.L0
lb_parse_dimacs_header.L10:
addq $1, %rax
cmpq %rsi, %rax
je lb_parse_dimacs_header.L11
movzbl (%rax), %ecx
cmpq $32, %rcx
sete %r11b
movzx %r11b, %edx
subq $9, %rcx
cmpq $5, %rcx
setb %r11b
movzx %r11b, %ecx
orq %rcx, %rdx
testl %edx, %edx
jne lb_parse_dimacs_header.L12
jmp lb_parse_dimacs_header.L0
lb_parse_dimacs_header.L12:
addq $1, %rax
lb_parse_dimacs_header.L14:
cmpq %rsi, %rax
je lb_parse_dimacs_header.L15
movzbl (%rax), %ecx
cmpq $32, %rcx
sete %r11b
movzx %r11b, %edx
subq $9, %rcx
cmpq $5, %rcx
setb %r11b
movzx %r11b, %ecx
orq %rcx, %rdx
testl %edx, %edx
jne lb_parse_dimacs_header.L16
jmp lb_parse_dimacs_header.L13
lb_parse_dimacs_header.L16:
addq $1, %rax
jmp lb_parse_dimacs_header.L14
lb_parse_dimacs_header.L15:
lb_parse_dimacs_header.L13:
cmpq %rsi, %rax
je lb_parse_dimacs_header.L17
movzbl (%rax), %ecx
cmpq $99, %rcx
je lb_parse_dimacs_header.L18
jmp lb_parse_dimacs_header.L0
lb_parse_dimacs_header.L18:
lea 1(%rax), %rcx
cmpq %rsi, %rcx
je lb_parse_dimacs_header.L19
movzbl (%rcx), %ecx
cmpq $110, %rcx
je lb_parse_dimacs_header.L20
jmp lb_parse_dimacs_header.L0
lb_parse_dimacs_header.L20:
lea 2(%rax), %rcx
cmpq %rsi, %rcx
je lb_parse_dimacs_header.L21
movzbl (%rcx), %ecx
cmpq $102, %rcx
je lb_parse_dimacs_header.L22
jmp lb_parse_dimacs_header.L0
lb_parse_dimacs_header.L22:
addq $3, %rax
cmpq %rsi, %rax
je lb_parse_dimacs_header.L23
movzbl (%rax), %ecx
cmpq $32, %rcx
sete %r11b
movzx %r11b, %edx
subq $9, %rcx
cmpq $5, %rcx
setb %r11b
movzx %r11b, %ecx
orq %rcx, %rdx
testl %edx, %edx
jne lb_parse_dimacs_header.L24
jmp lb_parse_dimacs_header.L0
lb_parse_dimacs_header.L24:
addq $1, %rax
lb_parse_dimacs_header.L26:
cmpq %rsi, %rax
je lb_parse_dimacs_header.L27
movzbl (%rax), %ecx
cmpq $32, %rcx
sete %r11b
movzx %r11b, %edx
subq $9, %rcx
cmpq $5, %rcx
setb %r11b
movzx %r11b, %ecx
orq %rcx, %rdx
testl %edx, %edx
jne lb_parse_dimacs_header.L28
jmp lb_parse_dimacs_header.L25
lb_parse_dimacs_header.L28:
addq $1, %rax
jmp lb_parse_dimacs_header.L26
lb_parse_dimacs_header.L27:
lb_parse_dimacs_header.L25:
cmpq %rsi, %rax
je lb_parse_dimacs_header.L29
movzbl (%rax), %ecx
subq $48, %rcx
cmpq $10, %rcx
jb lb_parse_dimacs_header.L30
jmp lb_parse_dimacs_header.L0
lb_parse_dimacs_header.L30:
addq $1, %rax
lb_parse_dimacs_header.L32:
cmpq %rsi, %rax
je lb_parse_dimacs_header.L33
movzbl (%rax), %edx
movq %rdx, %rdi
subq $48, %rdi
cmpq $10, %rdi
jb lb_parse_dimacs_header.L34
cmpq $32, %rdx
sete %r11b
movzx %r11b, %edi
subq $9, %rdx
cmpq $5, %rdx
setb %r11b
movzx %r11b, %edx
orq %rdx, %rdi
testl %edi, %edi
jne lb_parse_dimacs_header.L35
jmp lb_parse_dimacs_header.L0
lb_parse_dimacs_header.L35:
movq %rcx, %rbx
jmp lb_parse_dimacs_header.L31
lb_parse_dimacs_header.L34:
imulq $10, %rcx
addq %rdi, %rcx
cmpq $268435456, %rcx
jb lb_parse_dimacs_header.L36
jmp lb_parse_dimacs_header.L0
lb_parse_dimacs_header.L36:
addq $1, %rax
jmp lb_parse_dimacs_header.L32
lb_parse_dimacs_header.L33:
movq %rcx, %rbx
lb_parse_dimacs_header.L31:
cmpq %rsi, %rax
je lb_parse_dimacs_header.L37
movzbl (%rax), %ecx
cmpq $32, %rcx
sete %r11b
movzx %r11b, %edx
subq $9, %rcx
cmpq $5, %rcx
setb %r11b
movzx %r11b, %ecx
orq %rcx, %rdx
testl %edx, %edx
jne lb_parse_dimacs_header.L38
jmp lb_parse_dimacs_header.L0
lb_parse_dimacs_header.L38:
addq $1, %rax
lb_parse_dimacs_header.L40:
cmpq %rsi, %rax
je lb_parse_dimacs_header.L41
movzbl (%rax), %ecx
cmpq $32, %rcx
sete %r11b
movzx %r11b, %edx
subq $9, %rcx
cmpq $5, %rcx
setb %r11b
movzx %r11b, %ecx
orq %rcx, %rdx
testl %edx, %edx
jne lb_parse_dimacs_header.L42
jmp lb_parse_dimacs_header.L39
lb_parse_dimacs_header.L42:
addq $1, %rax
jmp lb_parse_dimacs_header.L40
lb_parse_dimacs_header.L41:
lb_parse_dimacs_header.L39:
cmpq %rsi, %rax
je lb_parse_dimacs_header.L43
movzbl (%rax), %ecx
subq $48, %rcx
cmpq $10, %rcx
jb lb_parse_dimacs_header.L44
jmp lb_parse_dimacs_header.L0
lb_parse_dimacs_header.L44:
addq $1, %rax
lb_parse_dimacs_header.L46:
cmpq %rsi, %rax
je lb_parse_dimacs_header.L47
movzbl (%rax), %edx
movq %rdx, %rdi
subq $48, %rdi
cmpq $10, %rdi
jb lb_parse_dimacs_header.L48
cmpq $32, %rdx
sete %r11b
movzx %r11b, %esi
subq $9, %rdx
cmpq $5, %rdx
setb %r11b
movzx %r11b, %edx
orq %rdx, %rsi
testl %esi, %esi
jne lb_parse_dimacs_header.L49
jmp lb_parse_dimacs_header.L0
lb_parse_dimacs_header.L49:
jmp lb_parse_dimacs_header.L45
lb_parse_dimacs_header.L48:
imulq $10, %rcx
addq %rdi, %rcx
cmpq $268435456, %rcx
jb lb_parse_dimacs_header.L50
jmp lb_parse_dimacs_header.L0
lb_parse_dimacs_header.L50:
addq $1, %rax
jmp lb_parse_dimacs_header.L46
lb_parse_dimacs_header.L47:
lb_parse_dimacs_header.L45:
movq %rbx, (%rbp)
lea 8(%rbp), %rdx
movq %rcx, (%rdx)
addq $72, %rbp
movq %rax, (%rbp)
movq $1, %rax
movq (%rsp), %rbx
movq 8(%rsp), %rbp
addq $24, %rsp
ret
lb_parse_dimacs_header.L43:
jmp lb_parse_dimacs_header.L0
lb_parse_dimacs_header.L37:
jmp lb_parse_dimacs_header.L0
lb_parse_dimacs_header.L29:
jmp lb_parse_dimacs_header.L0
lb_parse_dimacs_header.L23:
jmp lb_parse_dimacs_header.L0
lb_parse_dimacs_header.L21:
jmp lb_parse_dimacs_header.L0
lb_parse_dimacs_header.L19:
jmp lb_parse_dimacs_header.L0
lb_parse_dimacs_header.L17:
jmp lb_parse_dimacs_header.L0
lb_parse_dimacs_header.L11:
jmp lb_parse_dimacs_header.L0
lb_parse_dimacs_header.L9:
lb_parse_dimacs_header.L0:
movq $0, %rax
movq (%rsp), %rbx
movq 8(%rsp), %rbp
addq $24, %rsp
ret")

def bodyCode : Program := parse("lb_parse_dimacs_body:
subq $72, %rsp
movq %rbx, 24(%rsp)
movq %rbp, 32(%rsp)
movq %r12, 40(%rsp)
movq %r13, 48(%rsp)
movq %r14, 56(%rsp)
movq %r15, 64(%rsp)
movq (%rsi), %r12
lea 8(%rsi), %rax
movq (%rax), %r15
lea 48(%rsi), %rax
movq (%rax), %rax
movq %rax, (%rsp)
lea 56(%rsi), %rax
movq (%rax), %rax
movq %rax, 8(%rsp)
lea 64(%rsi), %rax
movq %rax, 16(%rsp)
movq (%rax), %rbx
addq $72, %rsi
movq (%rsi), %rax
movq $1, %rdx
lb_parse_dimacs_body.L1:
cmpq %rdx, %r15
jb lb_parse_dimacs_body.L2
movq %rax, %rcx
movq %rbx, %rax
lb_parse_dimacs_body.L3:
lb_parse_dimacs_body.L5:
cmpq %rdi, %rcx
je lb_parse_dimacs_body.L6
movzbl (%rcx), %esi
lea 1(%rcx), %rbp
cmpq $32, %rsi
sete %r11b
movzx %r11b, %r13d
movq %rsi, %r8
subq $9, %r8
cmpq $5, %r8
setb %r11b
movzx %r11b, %r14d
orq %r14, %r13
testl %r13d, %r13d
jne lb_parse_dimacs_body.L7
cmpq $99, %rsi
je lb_parse_dimacs_body.L8
jmp lb_parse_dimacs_body.L4
lb_parse_dimacs_body.L8:
movq %rbp, %rcx
lb_parse_dimacs_body.L9:
cmpq %rdi, %rcx
je lb_parse_dimacs_body.L10
movzbl (%rcx), %esi
addq $1, %rcx
cmpq $10, %rsi
je lb_parse_dimacs_body.L11
jmp lb_parse_dimacs_body.L9
lb_parse_dimacs_body.L11:
jmp lb_parse_dimacs_body.L5
lb_parse_dimacs_body.L10:
jmp lb_parse_dimacs_body.L4
lb_parse_dimacs_body.L7:
movq %rbp, %rcx
jmp lb_parse_dimacs_body.L5
lb_parse_dimacs_body.L6:
lb_parse_dimacs_body.L4:
cmpq %rdi, %rcx
sete %r11b
movzx %r11b, %esi
testl %esi, %esi
jne lb_parse_dimacs_body.L12
movq 8(%rsp), %r8
cmpq %r8, %rax
je lb_parse_dimacs_body.L13
movzbl (%rcx), %r8d
cmpq $45, %r8
je lb_parse_dimacs_body.L14
testl %esi, %esi
jne lb_parse_dimacs_body.L15
movzbl (%rcx), %esi
subq $48, %rsi
cmpq $10, %rsi
jb lb_parse_dimacs_body.L16
jmp lb_parse_dimacs_body.L0
lb_parse_dimacs_body.L16:
addq $1, %rcx
lb_parse_dimacs_body.L18:
cmpq %rdi, %rcx
je lb_parse_dimacs_body.L19
movzbl (%rcx), %r8d
movq %r8, %rbp
subq $48, %rbp
cmpq $10, %rbp
jb lb_parse_dimacs_body.L20
cmpq $32, %r8
sete %r11b
movzx %r11b, %ebp
subq $9, %r8
cmpq $5, %r8
setb %r11b
movzx %r11b, %r13d
orq %r13, %rbp
testl %ebp, %ebp
jne lb_parse_dimacs_body.L21
jmp lb_parse_dimacs_body.L0
lb_parse_dimacs_body.L21:
jmp lb_parse_dimacs_body.L17
lb_parse_dimacs_body.L20:
imulq $10, %rsi
addq %rbp, %rsi
cmpq $268435456, %rsi
jb lb_parse_dimacs_body.L22
jmp lb_parse_dimacs_body.L0
lb_parse_dimacs_body.L22:
addq $1, %rcx
jmp lb_parse_dimacs_body.L18
lb_parse_dimacs_body.L19:
lb_parse_dimacs_body.L17:
cmpq $0, %rsi
je lb_parse_dimacs_body.L23
cmpq %rsi, %r12
jb lb_parse_dimacs_body.L24
movl %esi, (%rax)
addq $4, %rax
jmp lb_parse_dimacs_body.L3
lb_parse_dimacs_body.L24:
jmp lb_parse_dimacs_body.L0
lb_parse_dimacs_body.L23:
movl $0, (%rax)
addq $4, %rax
movq %rdx, %rsi
shlq $3, %rsi
movq (%rsp), %r8
addq %r8, %rsi
movq %rbx, (%rsi)
addq $1, %rdx
movq %rax, %rbx
movq %rcx, %rax
jmp lb_parse_dimacs_body.L1
lb_parse_dimacs_body.L15:
jmp lb_parse_dimacs_body.L0
lb_parse_dimacs_body.L14:
addq $1, %rcx
cmpq %rdi, %rcx
je lb_parse_dimacs_body.L25
movzbl (%rcx), %esi
subq $48, %rsi
cmpq $10, %rsi
jb lb_parse_dimacs_body.L26
jmp lb_parse_dimacs_body.L0
lb_parse_dimacs_body.L26:
addq $1, %rcx
lb_parse_dimacs_body.L28:
cmpq %rdi, %rcx
je lb_parse_dimacs_body.L29
movzbl (%rcx), %r8d
movq %r8, %rbp
subq $48, %rbp
cmpq $10, %rbp
jb lb_parse_dimacs_body.L30
cmpq $32, %r8
sete %r11b
movzx %r11b, %ebp
subq $9, %r8
cmpq $5, %r8
setb %r11b
movzx %r11b, %r13d
orq %r13, %rbp
testl %ebp, %ebp
jne lb_parse_dimacs_body.L31
jmp lb_parse_dimacs_body.L0
lb_parse_dimacs_body.L31:
jmp lb_parse_dimacs_body.L27
lb_parse_dimacs_body.L30:
imulq $10, %rsi
addq %rbp, %rsi
cmpq $268435456, %rsi
jb lb_parse_dimacs_body.L32
jmp lb_parse_dimacs_body.L0
lb_parse_dimacs_body.L32:
addq $1, %rcx
jmp lb_parse_dimacs_body.L28
lb_parse_dimacs_body.L29:
lb_parse_dimacs_body.L27:
cmpq $0, %rsi
je lb_parse_dimacs_body.L33
cmpq %rsi, %r12
jb lb_parse_dimacs_body.L34
movq $0, %r11
movq %rsi, %r10
subq %r10, %r11
movq %r11, %rsi
movl %esi, (%rax)
addq $4, %rax
jmp lb_parse_dimacs_body.L3
lb_parse_dimacs_body.L34:
jmp lb_parse_dimacs_body.L0
lb_parse_dimacs_body.L33:
jmp lb_parse_dimacs_body.L0
lb_parse_dimacs_body.L25:
jmp lb_parse_dimacs_body.L0
lb_parse_dimacs_body.L13:
jmp lb_parse_dimacs_body.L0
lb_parse_dimacs_body.L12:
jmp lb_parse_dimacs_body.L0
lb_parse_dimacs_body.L2:
lb_parse_dimacs_body.L36:
cmpq %rdi, %rax
je lb_parse_dimacs_body.L37
movzbl (%rax), %ecx
lea 1(%rax), %rdx
cmpq $32, %rcx
sete %r11b
movzx %r11b, %esi
movq %rcx, %r8
subq $9, %r8
cmpq $5, %r8
setb %r11b
movzx %r11b, %ebp
orq %rbp, %rsi
testl %esi, %esi
jne lb_parse_dimacs_body.L38
cmpq $99, %rcx
je lb_parse_dimacs_body.L39
jmp lb_parse_dimacs_body.L35
lb_parse_dimacs_body.L39:
movq %rdx, %rax
lb_parse_dimacs_body.L40:
cmpq %rdi, %rax
je lb_parse_dimacs_body.L41
movzbl (%rax), %ecx
addq $1, %rax
cmpq $10, %rcx
je lb_parse_dimacs_body.L42
jmp lb_parse_dimacs_body.L40
lb_parse_dimacs_body.L42:
jmp lb_parse_dimacs_body.L36
lb_parse_dimacs_body.L41:
jmp lb_parse_dimacs_body.L35
lb_parse_dimacs_body.L38:
movq %rdx, %rax
jmp lb_parse_dimacs_body.L36
lb_parse_dimacs_body.L37:
lb_parse_dimacs_body.L35:
cmpq %rdi, %rax
je lb_parse_dimacs_body.L43
jmp lb_parse_dimacs_body.L0
lb_parse_dimacs_body.L43:
movq 16(%rsp), %rax
movq %rbx, (%rax)
movq $1, %rax
movq 24(%rsp), %rbx
movq 32(%rsp), %rbp
movq 40(%rsp), %r12
movq 48(%rsp), %r13
movq 56(%rsp), %r14
movq 64(%rsp), %r15
addq $72, %rsp
ret
lb_parse_dimacs_body.L0:
movq $0, %rax
movq 24(%rsp), %rbx
movq 32(%rsp), %rbp
movq 40(%rsp), %r12
movq 48(%rsp), %r13
movq 56(%rsp), %r14
movq 64(%rsp), %r15
addq $72, %rsp
ret")

def addLitsCode : Program := parse("lb_read_add_lits:
subq $56, %rsp
movq %rbx, 8(%rsp)
movq %rbp, 16(%rsp)
movq %r12, 24(%rsp)
movq %r13, 32(%rsp)
movq %r14, 40(%rsp)
movq %r15, 48(%rsp)
movq %rsi, %r14
movq %rdi, %r13
movq (%r13), %r15
lea 56(%r13), %rax
movq (%rax), %rax
movq %rax, (%rsp)
lea 64(%r13), %rbp
movq (%rbp), %r12
addq $72, %r13
movq (%r13), %rcx
movq %r12, %rax
lb_read_add_lits.L1:
movq (%rsp), %rdx
cmpq %rdx, %rax
je lb_read_add_lits.L2
movq $0, %rdi
movq $0, %rdx
lb_read_add_lits.L4:
cmpq %r14, %rcx
je lb_read_add_lits.L5
movzbl (%rcx), %esi
addq $1, %rcx
movq %rsi, %rbx
andq $127, %rbx
movq %rbx, %r11
movq %rcx, %r10
movq %rdx, %rcx
shlq %cl, %r11
movq %r10, %rcx
movq %r11, %rbx
orq %rbx, %rdi
andq $128, %rsi
cmpq $0, %rsi
jne lb_read_add_lits.L6
movq %rcx, %rsi
movq %rdi, %rcx
jmp lb_read_add_lits.L3
lb_read_add_lits.L6:
addq $7, %rdx
cmpq $28, %rdx
jb lb_read_add_lits.L7
jmp lb_read_add_lits.L0
lb_read_add_lits.L7:
jmp lb_read_add_lits.L4
lb_read_add_lits.L5:
jmp lb_read_add_lits.L0
lb_read_add_lits.L3:
cmpq $0, %rcx
je lb_read_add_lits.L8
movq %rcx, %rdx
shrq $1, %rdx
cmpq $0, %rdx
je lb_read_add_lits.L9
cmpq %rdx, %r15
jb lb_read_add_lits.L10
andq $1, %rcx
movq $0, %r11
movq %rcx, %r10
subq %r10, %r11
movq %r11, %rcx
xorq %rcx, %rdx
subq %rcx, %rdx
movl %edx, (%rax)
addq $4, %rax
movq %rsi, %rcx
jmp lb_read_add_lits.L1
lb_read_add_lits.L10:
jmp lb_read_add_lits.L0
lb_read_add_lits.L9:
jmp lb_read_add_lits.L0
lb_read_add_lits.L8:
movl $0, (%rax)
lea 4(%rax), %rcx
movq %rcx, (%rbp)
movq %rsi, (%r13)
cmpq %r12, %rax
je lb_read_add_lits.L11
movq $1, %rax
movq 8(%rsp), %rbx
movq 16(%rsp), %rbp
movq 24(%rsp), %r12
movq 32(%rsp), %r13
movq 40(%rsp), %r14
movq 48(%rsp), %r15
addq $56, %rsp
ret
lb_read_add_lits.L11:
movq $2, %rax
movq 8(%rsp), %rbx
movq 16(%rsp), %rbp
movq 24(%rsp), %r12
movq 32(%rsp), %r13
movq 40(%rsp), %r14
movq 48(%rsp), %r15
addq $56, %rsp
ret
lb_read_add_lits.L2:
lb_read_add_lits.L0:
movq $0, %rax
movq 8(%rsp), %rbx
movq 16(%rsp), %rbp
movq 24(%rsp), %r12
movq 32(%rsp), %r13
movq 40(%rsp), %r14
movq 48(%rsp), %r15
addq $56, %rsp
ret")

def rupCheckCode : Program := parse("lb_rup_check:
subq $88, %rsp
movq %rbx, 32(%rsp)
movq %rbp, 40(%rsp)
movq %r12, 48(%rsp)
movq %r13, 56(%rsp)
movq %r14, 64(%rsp)
movq %r15, 72(%rsp)
movq %rcx, %r15
movq %rsi, %r14
movq %rdx, %rsi
lea 24(%rdi), %rax
movq (%rax), %rbx
lea 32(%rdi), %rax
movq (%rax), %rax
movq %rax, 16(%rsp)
lea 40(%rdi), %rax
movq (%rax), %rax
movq %rax, (%rsp)
lea 48(%rdi), %rax
movq (%rax), %rax
movq %rax, 8(%rsp)
addq $72, %rdi
movq %rdi, 24(%rsp)
movq (%rdi), %rbp
movq 16(%rsp), %rax
lb_rup_check.L3:
movslq (%rsi), %rcx
testl %ecx, %ecx
jne lb_rup_check.L4
jmp lb_rup_check.L2
lb_rup_check.L4:
movq %rcx, %rdx
sarq $63, %rdx
movq %rcx, %rdi
xorq %rdx, %rdi
subq %rdx, %rdi
addq %rbx, %rdi
movsbq (%rdi), %r12
xorq %rdx, %r12
movq %r12, %r11
movq %rdx, %r10
subq %r10, %r11
movq %r11, %rdx
addq $4, %rsi
cmpq $0, %rdx
jl lb_rup_check.L5
movq $0, %r10
cmpq %rdx, %r10
jl lb_rup_check.L6
movq $0, %r11
movq %rcx, %r10
subq %r10, %r11
movq %r11, %rcx
movq (%rsp), %rdx
cmpq %rdx, %rax
je lb_rup_check.L7
movq %rcx, %rdx
sarq $63, %rdx
orq $1, %rdx
movb %dl, (%rdi)
movl %ecx, (%rax)
addq $4, %rax
jmp lb_rup_check.L3
lb_rup_check.L7:
jmp lb_rup_check.L0
lb_rup_check.L6:
movq %rax, %r10
movq %rbp, %rax
movq %r10, %rbp
jmp lb_rup_check.L1
lb_rup_check.L5:
jmp lb_rup_check.L3
lb_rup_check.L2:
movq %rax, %rdi
movq %rbp, %rax
lb_rup_check.L8:
movq $0, %rsi
movq $0, %rcx
lb_rup_check.L10:
cmpq %r15, %rax
je lb_rup_check.L11
movzbl (%rax), %edx
addq $1, %rax
movq %rdx, %rbp
andq $127, %rbp
movq %rbp, %r11
movq %rcx, %r10
movq %rcx, %rcx
shlq %cl, %r11
movq %r10, %rcx
movq %r11, %rbp
orq %rbp, %rsi
andq $128, %rdx
cmpq $0, %rdx
jne lb_rup_check.L12
movq %rax, %rbp
movq %rsi, %rax
jmp lb_rup_check.L9
lb_rup_check.L12:
addq $7, %rcx
cmpq $28, %rcx
jb lb_rup_check.L13
jmp lb_rup_check.L0
lb_rup_check.L13:
jmp lb_rup_check.L10
lb_rup_check.L11:
jmp lb_rup_check.L0
lb_rup_check.L9:
cmpq $0, %rax
je lb_rup_check.L14
movq %rax, %rcx
andq $1, %rcx
cmpq $0, %rcx
jne lb_rup_check.L15
shrq $1, %rax
cmpq %r14, %rax
jb lb_rup_check.L16
jmp lb_rup_check.L0
lb_rup_check.L16:
shlq $3, %rax
movq 8(%rsp), %rcx
addq %rcx, %rax
movq (%rax), %rax
cmpq $0, %rax
jne lb_rup_check.L17
jmp lb_rup_check.L0
lb_rup_check.L17:
movq %rdi, %rcx
movq %rax, %rdi
movq $0, %rdx
lb_rup_check.L19:
movslq (%rdi), %rax
testl %eax, %eax
jne lb_rup_check.L20
jmp lb_rup_check.L18
lb_rup_check.L20:
movq %rax, %rsi
sarq $63, %rsi
movq %rax, %r12
xorq %rsi, %r12
subq %rsi, %r12
addq %rbx, %r12
movsbq (%r12), %r13
xorq %rsi, %r13
subq %rsi, %r13
addq $4, %rdi
cmpq $0, %r13
jl lb_rup_check.L21
testl %edx, %edx
jne lb_rup_check.L23
jmp lb_rup_check.L22
lb_rup_check.L23:
cmpq %rax, %rdx
je lb_rup_check.L24
jmp lb_rup_check.L0
lb_rup_check.L24:
lb_rup_check.L22:
cmpq $0, %r13
je lb_rup_check.L25
movq %rax, %rdx
jmp lb_rup_check.L19
lb_rup_check.L25:
movq (%rsp), %rdx
cmpq %rdx, %rcx
je lb_rup_check.L26
orq $1, %rsi
movb %sil, (%r12)
movl %eax, (%rcx)
addq $4, %rcx
movq %rax, %rdx
jmp lb_rup_check.L19
lb_rup_check.L26:
jmp lb_rup_check.L0
lb_rup_check.L21:
movq $0, %r11
movq %rax, %r10
subq %r10, %r11
movq %r11, %rax
cmpq %rax, %rdx
je lb_rup_check.L27
jmp lb_rup_check.L19
lb_rup_check.L27:
jmp lb_rup_check.L0
lb_rup_check.L18:
testl %edx, %edx
jne lb_rup_check.L28
movq %rbp, %rax
movq %rcx, %rbp
jmp lb_rup_check.L1
lb_rup_check.L28:
movq %rbp, %rax
movq %rcx, %rdi
jmp lb_rup_check.L8
lb_rup_check.L15:
jmp lb_rup_check.L0
lb_rup_check.L14:
jmp lb_rup_check.L0
lb_rup_check.L1:
lb_rup_check.L29:
movq $0, %rsi
movq $0, %rcx
lb_rup_check.L31:
cmpq %r15, %rax
je lb_rup_check.L32
movzbl (%rax), %edx
addq $1, %rax
movq %rdx, %rdi
andq $127, %rdi
movq %rdi, %r11
movq %rcx, %r10
movq %rcx, %rcx
shlq %cl, %r11
movq %r10, %rcx
movq %r11, %rdi
orq %rdi, %rsi
andq $128, %rdx
cmpq $0, %rdx
jne lb_rup_check.L33
movq %rax, %rcx
movq %rsi, %rax
jmp lb_rup_check.L30
lb_rup_check.L33:
addq $7, %rcx
cmpq $28, %rcx
jb lb_rup_check.L34
jmp lb_rup_check.L0
lb_rup_check.L34:
jmp lb_rup_check.L31
lb_rup_check.L32:
jmp lb_rup_check.L0
lb_rup_check.L30:
cmpq $0, %rax
je lb_rup_check.L35
movq %rax, %rdx
andq $1, %rdx
cmpq $0, %rdx
jne lb_rup_check.L36
shrq $1, %rax
cmpq %r14, %rax
jb lb_rup_check.L37
jmp lb_rup_check.L0
lb_rup_check.L37:
shlq $3, %rax
movq 8(%rsp), %rdx
addq %rdx, %rax
movq (%rax), %rax
cmpq $0, %rax
jne lb_rup_check.L38
jmp lb_rup_check.L0
lb_rup_check.L38:
movq %rcx, %rax
jmp lb_rup_check.L29
lb_rup_check.L36:
jmp lb_rup_check.L0
lb_rup_check.L35:
movq 16(%rsp), %rax
lb_rup_check.L39:
cmpq %rbp, %rax
je lb_rup_check.L40
movslq (%rax), %rdx
movq %rdx, %rsi
sarq $63, %rsi
xorq %rsi, %rdx
subq %rsi, %rdx
addq %rbx, %rdx
movb $0, (%rdx)
addq $4, %rax
jmp lb_rup_check.L39
lb_rup_check.L40:
movq 24(%rsp), %rax
movq %rcx, (%rax)
movq $1, %rax
movq 32(%rsp), %rbx
movq 40(%rsp), %rbp
movq 48(%rsp), %r12
movq 56(%rsp), %r13
movq 64(%rsp), %r14
movq 72(%rsp), %r15
addq $88, %rsp
ret
lb_rup_check.L0:
movq $0, %rax
movq 32(%rsp), %rbx
movq 40(%rsp), %rbp
movq 48(%rsp), %r12
movq 56(%rsp), %r13
movq 64(%rsp), %r14
movq 72(%rsp), %r15
addq $88, %rsp
ret")

def checkPrfCode : Program := parse("lb_check_prf:
subq $88, %rsp
movq %rbx, 40(%rsp)
movq %rbp, 48(%rsp)
movq %r12, 56(%rsp)
movq %r13, 64(%rsp)
movq %r14, 72(%rsp)
movq %r15, 80(%rsp)
movq %rdi, (%rsp)
movq %rsi, %rbx
lea 8(%rdi), %rax
movq (%rax), %rax
movq %rax, 24(%rsp)
movq (%rsp), %rax
addq $16, %rax
movq (%rax), %rax
movq %rax, 8(%rsp)
movq (%rsp), %rax
addq $48, %rax
movq (%rax), %rax
movq %rax, 16(%rsp)
movq (%rsp), %rax
addq $64, %rax
movq %rax, 32(%rsp)
movq (%rsp), %rax
lea 72(%rax), %r12
lb_check_prf.L1:
movq (%r12), %rax
cmpq %rbx, %rax
je lb_check_prf.L2
movzbl (%rax), %ecx
addq $1, %rax
cmpq $97, %rcx
je lb_check_prf.L3
cmpq $100, %rcx
je lb_check_prf.L4
jmp lb_check_prf.L0
lb_check_prf.L4:
lb_check_prf.L5:
movq $0, %rsi
movq $0, %rcx
lb_check_prf.L7:
cmpq %rbx, %rax
je lb_check_prf.L8
movzbl (%rax), %edx
addq $1, %rax
movq %rdx, %rdi
andq $127, %rdi
movq %rdi, %r11
movq %rcx, %r10
movq %rcx, %rcx
shlq %cl, %r11
movq %r10, %rcx
movq %r11, %rdi
orq %rdi, %rsi
andq $128, %rdx
cmpq $0, %rdx
jne lb_check_prf.L9
movq %rax, %rcx
movq %rsi, %rax
jmp lb_check_prf.L6
lb_check_prf.L9:
addq $7, %rcx
cmpq $28, %rcx
jb lb_check_prf.L10
jmp lb_check_prf.L0
lb_check_prf.L10:
jmp lb_check_prf.L7
lb_check_prf.L8:
jmp lb_check_prf.L0
lb_check_prf.L6:
cmpq $0, %rax
je lb_check_prf.L11
movq %rax, %rdx
andq $1, %rdx
cmpq $0, %rdx
jne lb_check_prf.L12
shrq $1, %rax
cmpq $0, %rax
je lb_check_prf.L13
movq 8(%rsp), %rdx
cmpq %rdx, %rax
jb lb_check_prf.L14
jmp lb_check_prf.L0
lb_check_prf.L14:
shlq $3, %rax
movq 16(%rsp), %rdx
addq %rdx, %rax
movq (%rax), %rdx
cmpq $0, %rdx
jne lb_check_prf.L15
jmp lb_check_prf.L0
lb_check_prf.L15:
movq $0, (%rax)
movq %rcx, %rax
jmp lb_check_prf.L5
lb_check_prf.L13:
jmp lb_check_prf.L0
lb_check_prf.L12:
jmp lb_check_prf.L0
lb_check_prf.L11:
movq %rcx, (%r12)
jmp lb_check_prf.L1
lb_check_prf.L3:
movq $0, %rsi
movq $0, %rcx
lb_check_prf.L17:
cmpq %rbx, %rax
je lb_check_prf.L18
movzbl (%rax), %edx
addq $1, %rax
movq %rdx, %rdi
andq $127, %rdi
movq %rdi, %r11
movq %rcx, %r10
movq %rcx, %rcx
shlq %cl, %r11
movq %r10, %rcx
movq %r11, %rdi
orq %rdi, %rsi
andq $128, %rdx
cmpq $0, %rdx
jne lb_check_prf.L19
jmp lb_check_prf.L16
lb_check_prf.L19:
addq $7, %rcx
cmpq $28, %rcx
jb lb_check_prf.L20
jmp lb_check_prf.L0
lb_check_prf.L20:
jmp lb_check_prf.L17
lb_check_prf.L18:
jmp lb_check_prf.L0
lb_check_prf.L16:
movq %rsi, %rcx
andq $1, %rcx
cmpq $0, %rcx
jne lb_check_prf.L21
movq %rsi, %rbp
shrq $1, %rbp
movq 24(%rsp), %rcx
cmpq %rbp, %rcx
jb lb_check_prf.L22
jmp lb_check_prf.L0
lb_check_prf.L22:
movq 8(%rsp), %rcx
cmpq %rcx, %rbp
jb lb_check_prf.L23
jmp lb_check_prf.L0
lb_check_prf.L23:
movq %rbp, %rcx
shlq $3, %rcx
movq 16(%rsp), %rdx
lea (%rdx,%rcx,1), %r13
movq (%r13), %rcx
cmpq $0, %rcx
jne lb_check_prf.L24
movq %rax, (%r12)
movq 32(%rsp), %rax
movq (%rax), %r14
movq (%rsp), %rdi
movq %rbx, %rsi
call lb_read_add_lits
movq %rax, %r15
cmpq $0, %r15
jne lb_check_prf.L25
jmp lb_check_prf.L0
lb_check_prf.L25:
movq (%rsp), %rdi
movq %rbp, %rsi
movq %r14, %rdx
movq %rbx, %rcx
call lb_rup_check
cmpq $0, %rax
jne lb_check_prf.L26
jmp lb_check_prf.L0
lb_check_prf.L26:
cmpq $2, %r15
je lb_check_prf.L27
movq %r14, (%r13)
jmp lb_check_prf.L1
lb_check_prf.L27:
movq $1, %rax
movq 40(%rsp), %rbx
movq 48(%rsp), %rbp
movq 56(%rsp), %r12
movq 64(%rsp), %r13
movq 72(%rsp), %r14
movq 80(%rsp), %r15
addq $88, %rsp
ret
lb_check_prf.L24:
jmp lb_check_prf.L0
lb_check_prf.L21:
jmp lb_check_prf.L0
lb_check_prf.L2:
lb_check_prf.L0:
movq $0, %rax
movq 40(%rsp), %rbx
movq 48(%rsp), %rbp
movq 56(%rsp), %r12
movq 64(%rsp), %r13
movq 72(%rsp), %r14
movq 80(%rsp), %r15
addq $88, %rsp
ret")

def checkBytesCode : Program := parse("lrat_check_bytes:
subq $72, %rsp
movq %rbx, 24(%rsp)
movq %rbp, 32(%rsp)
movq %r12, 40(%rsp)
movq %r13, 48(%rsp)
movq %r14, 56(%rsp)
movq %r15, 64(%rsp)
movq %r9, %rbp
movq %r8, %rbx
movq %rcx, %r13
movq %rdx, %r12
cmpq $128, %rbp
jb lrat_check_bytes.L0
lea (%rdi,%rsi,1), %r14
lea (%r12,%r13,1), %rax
movq %rax, 8(%rsp)
movq %r14, %rsi
movq %rbx, %rdx
call lb_parse_dimacs_header
cmpq $0, %rax
jne lrat_check_bytes.L1
movq $0, %rax
movq 24(%rsp), %rbx
movq 32(%rsp), %rbp
movq 40(%rsp), %r12
movq 48(%rsp), %r13
movq 56(%rsp), %r14
movq 64(%rsp), %r15
addq $72, %rsp
ret
lrat_check_bytes.L1:
movq (%rbx), %rsi
lea 8(%rbx), %rax
movq (%rax), %rax
lea 1(%rsi), %r8
lea 8(%rsi), %rcx
andq $-8, %rcx
shlq $2, %r8
lea 7(%r8), %r15
andq $-8, %r15
lea (%rcx,%r15,1), %rdx
addq $80, %rdx
cmpq %rdx, %rbp
jb lrat_check_bytes.L2
movq %rbp, %r11
movq %rdx, %r10
subq %r10, %r11
movq %r11, %rdx
movq %rdx, (%rsp)
shrq $4, %rdx
andq $268435455, %r13
lea (%rax,%r13,1), %rbp
addq $32, %rbp
cmpq %rbp, %rdx
jb lrat_check_bytes.L4
movq %rbp, %rdx
jmp lrat_check_bytes.L3
lrat_check_bytes.L4:
lrat_check_bytes.L3:
cmpq %rax, %rdx
jbe lrat_check_bytes.L5
lea 80(%rbx), %rdi
lea (%rdi,%rcx,1), %rbp
lea (%rbp,%r8,1), %rax
movq %rax, 16(%rsp)
lea (%rbp,%r15,1), %r8
movq %rdx, %rax
shlq $3, %rax
lea (%r8,%rax,1), %r13
movq (%rsp), %rcx
movq %rcx, %r11
movq %rax, %r10
subq %r10, %r11
movq %r11, %rax
andq $-4, %rax
lea (%r13,%rax,1), %r15
movq $0, %rax
lrat_check_bytes.L7:
cmpq %rsi, %rax
jbe lrat_check_bytes.L8
jmp lrat_check_bytes.L6
lrat_check_bytes.L8:
lea (%rdi,%rax,1), %rcx
movb $0, (%rcx)
addq $1, %rax
jmp lrat_check_bytes.L7
lrat_check_bytes.L6:
movq $0, %rax
lrat_check_bytes.L10:
cmpq %rdx, %rax
jb lrat_check_bytes.L11
jmp lrat_check_bytes.L9
lrat_check_bytes.L11:
movq %rax, %rcx
shlq $3, %rcx
addq %r8, %rcx
movq $0, (%rcx)
addq $1, %rax
jmp lrat_check_bytes.L10
lrat_check_bytes.L9:
lea 16(%rbx), %rax
movq %rdx, (%rax)
lea 24(%rbx), %rax
movq %rdi, (%rax)
lea 32(%rbx), %rax
movq %rbp, (%rax)
lea 40(%rbx), %rax
movq 16(%rsp), %rcx
movq %rcx, (%rax)
lea 48(%rbx), %rax
movq %r8, (%rax)
lea 56(%rbx), %rax
movq %r15, (%rax)
lea 64(%rbx), %rax
movq %r13, (%rax)
movq %r14, %rdi
movq %rbx, %rsi
call lb_parse_dimacs_body
cmpq $0, %rax
jne lrat_check_bytes.L12
movq $0, %rax
movq 24(%rsp), %rbx
movq 32(%rsp), %rbp
movq 40(%rsp), %r12
movq 48(%rsp), %r13
movq 56(%rsp), %r14
movq 64(%rsp), %r15
addq $72, %rsp
ret
lrat_check_bytes.L12:
lea 72(%rbx), %rax
movq %r12, (%rax)
movq %rbx, %rdi
movq 8(%rsp), %rsi
call lb_check_prf
movq 24(%rsp), %rbx
movq 32(%rsp), %rbp
movq 40(%rsp), %r12
movq 48(%rsp), %r13
movq 56(%rsp), %r14
movq 64(%rsp), %r15
addq $72, %rsp
ret
lrat_check_bytes.L5:
movq $0, %rax
movq 24(%rsp), %rbx
movq 32(%rsp), %rbp
movq 40(%rsp), %r12
movq 48(%rsp), %r13
movq 56(%rsp), %r14
movq 64(%rsp), %r15
addq $72, %rsp
ret
lrat_check_bytes.L2:
movq $0, %rax
movq 24(%rsp), %rbx
movq 32(%rsp), %rbp
movq 40(%rsp), %r12
movq 48(%rsp), %r13
movq 56(%rsp), %r14
movq 64(%rsp), %r15
addq $72, %rsp
ret
lrat_check_bytes.L0:
movq $0, %rax
movq 24(%rsp), %rbx
movq 32(%rsp), %rbp
movq 40(%rsp), %r12
movq 48(%rsp), %r13
movq 56(%rsp), %r14
movq 64(%rsp), %r15
addq $72, %rsp
ret")


def lratBytesCode : Program :=
  hdrCode ++ (bodyCode ++ (addLitsCode ++ (rupCheckCode ++ (checkPrfCode ++ (checkBytesCode ++ [])))))

def lratBytesBounds : List (String × Nat) :=
  [("lb_parse_dimacs_header", 24),
   ("lb_parse_dimacs_body", 72),
   ("lb_read_add_lits", 56),
   ("lb_rup_check", 88),
   ("lb_check_prf", 184),
   ("lrat_check_bytes", 264)]

theorem lb_hdr_compile : compileFn Amd64.fastIsa lbHdrFn = .ok hdrCode := by kernel_rfl
theorem lb_body_compile : compileFn Amd64.fastIsa lbBodyFn = .ok bodyCode := by kernel_rfl
theorem lb_addLits_compile : compileFn Amd64.fastIsa lbAddLitsFn = .ok addLitsCode := by kernel_rfl
theorem lb_rupCheck_compile : compileFn Amd64.fastIsa lbRupCheckFn = .ok rupCheckCode := by kernel_rfl
theorem lb_checkPrf_compile : compileFn Amd64.fastIsa lbCheckPrfFn = .ok checkPrfCode := by kernel_rfl
theorem lb_checkBytes_compile : compileFn Amd64.fastIsa lbCheckBytesFn = .ok checkBytesCode := by kernel_rfl

theorem lrat_bytes_module_compile :
    compileModule Amd64.fastIsa 8 [] [] 0 lratBytesFns =
      .ok (lratBytesCode, lratBytesBounds) := by kernel_rfl

private theorem sum_sized_mapIdx_le_four (sz : Nat → Nat) (hsz : ∀ i, sz i ≤ 4) :
    ∀ (xs : List Directive) (k : Nat),
      (List.map (·.size)
        (List.mapIdx (fun i d => ({ directive := d, size := sz (k + i) } : Kraken.Sized Directive)) xs)).sum ≤
        4 * xs.length
  | [], _ => by simp
  | _ :: xs, k => by
    rw [List.mapIdx_cons, List.map_cons, List.sum_cons, List.length_cons]
    have h0 : sz (k + 0) ≤ 4 := hsz (k + 0)
    have ih := sum_sized_mapIdx_le_four sz hsz xs (k + 1)
    have hconv : (List.mapIdx (fun i d => ({ directive := d, size := sz (k + (i + 1)) } : Kraken.Sized Directive)) xs) =
        (List.mapIdx (fun i d => ({ directive := d, size := sz (k + 1 + i) } : Kraken.Sized Directive)) xs) := by
      congr 1; funext i d; congr 2; omega
    rw [hconv]
    dsimp only
    omega

theorem layoutOf_small (p : Program) (h : 4 * p.length < 2 ^ 64) :
    (@Kraken.Layout.apply _ (layoutOf p) p).sizeBefore p.length < 2 ^ 64 := by
  refine Nat.lt_of_le_of_lt ?_ h
  simp only [Kraken.Executable.sizeBefore, Kraken.Layout.apply]
  rw [List.take_of_length_le (by simp)]
  simpa using sum_sized_mapIdx_le_four (fun i => @Kraken.Layout.size _ (layoutOf p) i)
    (fun i => by
      show (match p[i]? with | some (.label _) => 0 | _ => 4) ≤ 4
      split <;> decide) p 0

abbrev lratBytesHost : Host :=
  .ofLayout lratBytesCode (layoutOf lratBytesCode) (layoutOf_zero _)
    (layoutOf_small _ (of_decide_eq_true (by kernel_rfl)))

attribute [local instance] lratBytesHost

theorem lratBytesHost_prog : Host.prog = lratBytesCode := rfl

theorem lratBytesHost_unique : Host.LabelsUnique :=
  Host.labelsUnique_of_nodup (of_decide_eq_true (by kernel_rfl))

end LeanQbe.Litmus
