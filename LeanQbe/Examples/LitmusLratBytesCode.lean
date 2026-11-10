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
subq $136, %rsp
movq %rdi, %rax
jmp lb_parse_dimacs_header.L2
lb_parse_dimacs_header.L2:
cmpq %rsi, %rax
sete %r11b
movzx %r11b, %ecx
testl %ecx, %ecx
jne lb_parse_dimacs_header.L3
movzbl (%rax), %ecx
movq %rax, %r11
movq $1, %r10
addq %r10, %r11
movq %r11, %rdi
movq $32, %r10
cmpq %r10, %rcx
sete %r11b
movzx %r11b, %r8d
movq %r8, (%rsp)
movq %rcx, %r11
movq $9, %r10
subq %r10, %r11
movq %r11, %r8
movq %r8, 8(%rsp)
movq $5, %r10
cmpq %r10, %r8
setb %r11b
movzx %r11b, %r8d
movq %r8, 16(%rsp)
movq (%rsp), %r9
orq %r9, %r8
movq %r8, 24(%rsp)
testl %r8d, %r8d
jne lb_parse_dimacs_header.L4
movq $99, %r10
cmpq %r10, %rcx
sete %r11b
movzx %r11b, %ecx
testl %ecx, %ecx
jne lb_parse_dimacs_header.L5
jmp lb_parse_dimacs_header.L1
lb_parse_dimacs_header.L5:
movq %rdi, %rax
jmp lb_parse_dimacs_header.L6
lb_parse_dimacs_header.L6:
cmpq %rsi, %rax
sete %r11b
movzx %r11b, %ecx
testl %ecx, %ecx
jne lb_parse_dimacs_header.L7
movzbl (%rax), %ecx
movq $1, %r10
addq %r10, %rax
movq $10, %r10
cmpq %r10, %rcx
sete %r11b
movzx %r11b, %ecx
testl %ecx, %ecx
jne lb_parse_dimacs_header.L8
jmp lb_parse_dimacs_header.L6
lb_parse_dimacs_header.L8:
jmp lb_parse_dimacs_header.L2
lb_parse_dimacs_header.L7:
jmp lb_parse_dimacs_header.L1
lb_parse_dimacs_header.L4:
movq %rdi, %rax
jmp lb_parse_dimacs_header.L2
lb_parse_dimacs_header.L3:
jmp lb_parse_dimacs_header.L1
lb_parse_dimacs_header.L1:
cmpq %rsi, %rax
sete %r11b
movzx %r11b, %ecx
testl %ecx, %ecx
jne lb_parse_dimacs_header.L9
movzbl (%rax), %ecx
movq $112, %r10
cmpq %r10, %rcx
sete %r11b
movzx %r11b, %ecx
testl %ecx, %ecx
jne lb_parse_dimacs_header.L10
jmp lb_parse_dimacs_header.L0
lb_parse_dimacs_header.L10:
movq $1, %r10
addq %r10, %rax
cmpq %rsi, %rax
sete %r11b
movzx %r11b, %ecx
testl %ecx, %ecx
jne lb_parse_dimacs_header.L11
movzbl (%rax), %ecx
movq $32, %r10
cmpq %r10, %rcx
sete %r11b
movzx %r11b, %edi
movq $9, %r10
subq %r10, %rcx
movq $5, %r10
cmpq %r10, %rcx
setb %r11b
movzx %r11b, %ecx
orq %rdi, %rcx
testl %ecx, %ecx
jne lb_parse_dimacs_header.L12
jmp lb_parse_dimacs_header.L0
lb_parse_dimacs_header.L12:
movq $1, %r10
addq %r10, %rax
jmp lb_parse_dimacs_header.L14
lb_parse_dimacs_header.L14:
cmpq %rsi, %rax
sete %r11b
movzx %r11b, %ecx
testl %ecx, %ecx
jne lb_parse_dimacs_header.L15
movzbl (%rax), %ecx
movq $32, %r10
cmpq %r10, %rcx
sete %r11b
movzx %r11b, %edi
movq $9, %r10
subq %r10, %rcx
movq $5, %r10
cmpq %r10, %rcx
setb %r11b
movzx %r11b, %ecx
orq %rdi, %rcx
testl %ecx, %ecx
jne lb_parse_dimacs_header.L16
jmp lb_parse_dimacs_header.L13
lb_parse_dimacs_header.L16:
movq $1, %r10
addq %r10, %rax
jmp lb_parse_dimacs_header.L14
lb_parse_dimacs_header.L15:
jmp lb_parse_dimacs_header.L13
lb_parse_dimacs_header.L13:
cmpq %rsi, %rax
sete %r11b
movzx %r11b, %ecx
testl %ecx, %ecx
jne lb_parse_dimacs_header.L17
movzbl (%rax), %ecx
movq $99, %r10
cmpq %r10, %rcx
sete %r11b
movzx %r11b, %ecx
testl %ecx, %ecx
jne lb_parse_dimacs_header.L18
jmp lb_parse_dimacs_header.L0
lb_parse_dimacs_header.L18:
movq %rax, %r11
movq $1, %r10
addq %r10, %r11
movq %r11, %rcx
cmpq %rsi, %rcx
sete %r11b
movzx %r11b, %edi
testl %edi, %edi
jne lb_parse_dimacs_header.L19
movzbl (%rcx), %ecx
movq $110, %r10
cmpq %r10, %rcx
sete %r11b
movzx %r11b, %ecx
testl %ecx, %ecx
jne lb_parse_dimacs_header.L20
jmp lb_parse_dimacs_header.L0
lb_parse_dimacs_header.L20:
movq %rax, %r11
movq $2, %r10
addq %r10, %r11
movq %r11, %rcx
cmpq %rsi, %rcx
sete %r11b
movzx %r11b, %edi
testl %edi, %edi
jne lb_parse_dimacs_header.L21
movzbl (%rcx), %ecx
movq $102, %r10
cmpq %r10, %rcx
sete %r11b
movzx %r11b, %ecx
testl %ecx, %ecx
jne lb_parse_dimacs_header.L22
jmp lb_parse_dimacs_header.L0
lb_parse_dimacs_header.L22:
movq $3, %r10
addq %r10, %rax
cmpq %rsi, %rax
sete %r11b
movzx %r11b, %ecx
testl %ecx, %ecx
jne lb_parse_dimacs_header.L23
movzbl (%rax), %ecx
movq $32, %r10
cmpq %r10, %rcx
sete %r11b
movzx %r11b, %edi
movq $9, %r10
subq %r10, %rcx
movq $5, %r10
cmpq %r10, %rcx
setb %r11b
movzx %r11b, %ecx
orq %rdi, %rcx
testl %ecx, %ecx
jne lb_parse_dimacs_header.L24
jmp lb_parse_dimacs_header.L0
lb_parse_dimacs_header.L24:
movq $1, %r10
addq %r10, %rax
jmp lb_parse_dimacs_header.L26
lb_parse_dimacs_header.L26:
cmpq %rsi, %rax
sete %r11b
movzx %r11b, %ecx
testl %ecx, %ecx
jne lb_parse_dimacs_header.L27
movzbl (%rax), %ecx
movq $32, %r10
cmpq %r10, %rcx
sete %r11b
movzx %r11b, %edi
movq $9, %r10
subq %r10, %rcx
movq $5, %r10
cmpq %r10, %rcx
setb %r11b
movzx %r11b, %ecx
orq %rdi, %rcx
testl %ecx, %ecx
jne lb_parse_dimacs_header.L28
jmp lb_parse_dimacs_header.L25
lb_parse_dimacs_header.L28:
movq $1, %r10
addq %r10, %rax
jmp lb_parse_dimacs_header.L26
lb_parse_dimacs_header.L27:
jmp lb_parse_dimacs_header.L25
lb_parse_dimacs_header.L25:
cmpq %rsi, %rax
sete %r11b
movzx %r11b, %ecx
testl %ecx, %ecx
jne lb_parse_dimacs_header.L29
movzbl (%rax), %ecx
movq $48, %r10
subq %r10, %rcx
movq $10, %r10
cmpq %r10, %rcx
setb %r11b
movzx %r11b, %edi
testl %edi, %edi
jne lb_parse_dimacs_header.L30
jmp lb_parse_dimacs_header.L0
lb_parse_dimacs_header.L30:
movq $1, %r10
addq %r10, %rax
jmp lb_parse_dimacs_header.L32
lb_parse_dimacs_header.L32:
cmpq %rsi, %rax
sete %r11b
movzx %r11b, %edi
testl %edi, %edi
jne lb_parse_dimacs_header.L33
movzbl (%rax), %edi
movq %rdi, %r11
movq $48, %r10
subq %r10, %r11
movq %r11, %r8
movq %r8, 32(%rsp)
movq $10, %r10
cmpq %r10, %r8
setb %r11b
movzx %r11b, %r8d
movq %r8, 40(%rsp)
testl %r8d, %r8d
jne lb_parse_dimacs_header.L34
movq $32, %r10
cmpq %r10, %rdi
sete %r11b
movzx %r11b, %r8d
movq %r8, 48(%rsp)
movq $9, %r10
subq %r10, %rdi
movq $5, %r10
cmpq %r10, %rdi
setb %r11b
movzx %r11b, %edi
movq 48(%rsp), %r8
orq %r8, %rdi
testl %edi, %edi
jne lb_parse_dimacs_header.L35
jmp lb_parse_dimacs_header.L0
lb_parse_dimacs_header.L35:
movq %rax, %r10
movq %rcx, %rax
movq %r10, %rcx
jmp lb_parse_dimacs_header.L31
lb_parse_dimacs_header.L34:
movq $10, %r10
imulq %r10, %rcx
movq 32(%rsp), %rdi
addq %rdi, %rcx
movq $268435456, %r10
cmpq %r10, %rcx
setb %r11b
movzx %r11b, %edi
testl %edi, %edi
jne lb_parse_dimacs_header.L36
jmp lb_parse_dimacs_header.L0
lb_parse_dimacs_header.L36:
movq $1, %r10
addq %r10, %rax
jmp lb_parse_dimacs_header.L32
lb_parse_dimacs_header.L33:
movq %rax, %r10
movq %rcx, %rax
movq %r10, %rcx
jmp lb_parse_dimacs_header.L31
lb_parse_dimacs_header.L31:
cmpq %rsi, %rcx
sete %r11b
movzx %r11b, %edi
testl %edi, %edi
jne lb_parse_dimacs_header.L37
movzbl (%rcx), %edi
movq $32, %r10
cmpq %r10, %rdi
sete %r11b
movzx %r11b, %r8d
movq %r8, 56(%rsp)
movq $9, %r10
subq %r10, %rdi
movq $5, %r10
cmpq %r10, %rdi
setb %r11b
movzx %r11b, %edi
movq 56(%rsp), %r8
orq %r8, %rdi
testl %edi, %edi
jne lb_parse_dimacs_header.L38
jmp lb_parse_dimacs_header.L0
lb_parse_dimacs_header.L38:
movq $1, %r10
addq %r10, %rcx
jmp lb_parse_dimacs_header.L40
lb_parse_dimacs_header.L40:
cmpq %rsi, %rcx
sete %r11b
movzx %r11b, %edi
testl %edi, %edi
jne lb_parse_dimacs_header.L41
movzbl (%rcx), %edi
movq $32, %r10
cmpq %r10, %rdi
sete %r11b
movzx %r11b, %r8d
movq %r8, 64(%rsp)
movq $9, %r10
subq %r10, %rdi
movq $5, %r10
cmpq %r10, %rdi
setb %r11b
movzx %r11b, %edi
movq 64(%rsp), %r8
orq %r8, %rdi
testl %edi, %edi
jne lb_parse_dimacs_header.L42
jmp lb_parse_dimacs_header.L39
lb_parse_dimacs_header.L42:
movq $1, %r10
addq %r10, %rcx
jmp lb_parse_dimacs_header.L40
lb_parse_dimacs_header.L41:
jmp lb_parse_dimacs_header.L39
lb_parse_dimacs_header.L39:
cmpq %rsi, %rcx
sete %r11b
movzx %r11b, %edi
testl %edi, %edi
jne lb_parse_dimacs_header.L43
movzbl (%rcx), %edi
movq $48, %r10
subq %r10, %rdi
movq $10, %r10
cmpq %r10, %rdi
setb %r11b
movzx %r11b, %r8d
movq %r8, 72(%rsp)
testl %r8d, %r8d
jne lb_parse_dimacs_header.L44
jmp lb_parse_dimacs_header.L0
lb_parse_dimacs_header.L44:
movq $1, %r10
addq %r10, %rcx
jmp lb_parse_dimacs_header.L46
lb_parse_dimacs_header.L46:
cmpq %rsi, %rcx
sete %r11b
movzx %r11b, %r8d
movq %r8, 80(%rsp)
testl %r8d, %r8d
jne lb_parse_dimacs_header.L47
movzbl (%rcx), %r8d
movq %r8, 88(%rsp)
movq $48, %r10
subq %r10, %r8
movq %r8, 96(%rsp)
movq $10, %r10
cmpq %r10, %r8
setb %r11b
movzx %r11b, %r8d
movq %r8, 104(%rsp)
testl %r8d, %r8d
jne lb_parse_dimacs_header.L48
movq 88(%rsp), %rsi
movq $32, %r10
cmpq %r10, %rsi
sete %r11b
movzx %r11b, %esi
movq 88(%rsp), %r8
movq $9, %r10
subq %r10, %r8
movq %r8, 112(%rsp)
movq $5, %r10
cmpq %r10, %r8
setb %r11b
movzx %r11b, %r8d
movq %r8, 120(%rsp)
orq %r8, %rsi
testl %esi, %esi
jne lb_parse_dimacs_header.L49
jmp lb_parse_dimacs_header.L0
lb_parse_dimacs_header.L49:
movq %rcx, %rsi
movq %rdi, %rcx
jmp lb_parse_dimacs_header.L45
lb_parse_dimacs_header.L48:
movq $10, %r10
imulq %r10, %rdi
movq 96(%rsp), %r8
addq %r8, %rdi
movq $268435456, %r10
cmpq %r10, %rdi
setb %r11b
movzx %r11b, %r8d
movq %r8, 128(%rsp)
testl %r8d, %r8d
jne lb_parse_dimacs_header.L50
jmp lb_parse_dimacs_header.L0
lb_parse_dimacs_header.L50:
movq $1, %r10
addq %r10, %rcx
jmp lb_parse_dimacs_header.L46
lb_parse_dimacs_header.L47:
movq %rcx, %rsi
movq %rdi, %rcx
jmp lb_parse_dimacs_header.L45
lb_parse_dimacs_header.L45:
movq %rax, (%rdx)
movq %rdx, %r11
movq $8, %r10
addq %r10, %r11
movq %r11, %rax
movq %rcx, (%rax)
movq %rdx, %r11
movq $72, %r10
addq %r10, %r11
movq %r11, %rax
movq %rsi, (%rax)
movq $1, %rax
addq $136, %rsp
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
jmp lb_parse_dimacs_header.L0
lb_parse_dimacs_header.L0:
movq $0, %rax
addq $136, %rsp
ret")

def bodyCode : Program := parse("lb_parse_dimacs_body:
subq $664, %rsp
movq (%rsi), %rax
movq %rsi, %r11
movq $8, %r10
addq %r10, %r11
movq %r11, %rcx
movq (%rcx), %rcx
movq %rsi, %r11
movq $48, %r10
addq %r10, %r11
movq %r11, %rdx
movq (%rdx), %rdx
movq %rsi, %r11
movq $56, %r10
addq %r10, %r11
movq %r11, %r8
movq %r8, (%rsp)
movq (%r8), %r8
movq %r8, 8(%rsp)
movq %rsi, %r11
movq $64, %r10
addq %r10, %r11
movq %r11, %r8
movq %r8, 16(%rsp)
movq (%r8), %r8
movq %r8, 24(%rsp)
movq $72, %r10
addq %r10, %rsi
movq (%rsi), %rsi
movq %rsi, %r8
movq 24(%rsp), %r9
movq $1, %rsi
jmp lb_parse_dimacs_body.L1
lb_parse_dimacs_body.L1:
movq %r8, 32(%rsp)
movq %r9, 40(%rsp)
cmpq %rsi, %rcx
setb %r11b
movzx %r11b, %r8d
movq %r8, 48(%rsp)
testl %r8d, %r8d
jne lb_parse_dimacs_body.L2
movq 32(%rsp), %r8
jmp lb_parse_dimacs_body.L3
lb_parse_dimacs_body.L3:
movq %r8, 56(%rsp)
movq %r9, 64(%rsp)
jmp lb_parse_dimacs_body.L5
lb_parse_dimacs_body.L5:
movq %r8, 72(%rsp)
cmpq %rdi, %r8
sete %r11b
movzx %r11b, %r8d
movq %r8, 80(%rsp)
testl %r8d, %r8d
jne lb_parse_dimacs_body.L6
movq 72(%rsp), %r8
movzbl (%r8), %r8d
movq %r8, 88(%rsp)
movq 72(%rsp), %r8
movq $1, %r10
addq %r10, %r8
movq %r8, 96(%rsp)
movq 88(%rsp), %r8
movq $32, %r10
cmpq %r10, %r8
sete %r11b
movzx %r11b, %r8d
movq %r8, 104(%rsp)
movq 88(%rsp), %r8
movq $9, %r10
subq %r10, %r8
movq %r8, 112(%rsp)
movq $5, %r10
cmpq %r10, %r8
setb %r11b
movzx %r11b, %r8d
movq %r8, 120(%rsp)
movq 104(%rsp), %r9
orq %r9, %r8
movq %r8, 128(%rsp)
testl %r8d, %r8d
jne lb_parse_dimacs_body.L7
movq 88(%rsp), %r8
movq $99, %r10
cmpq %r10, %r8
sete %r11b
movzx %r11b, %r8d
movq %r8, 136(%rsp)
testl %r8d, %r8d
jne lb_parse_dimacs_body.L8
movq 72(%rsp), %r8
jmp lb_parse_dimacs_body.L4
lb_parse_dimacs_body.L8:
movq 96(%rsp), %r8
jmp lb_parse_dimacs_body.L9
lb_parse_dimacs_body.L9:
movq %r8, 144(%rsp)
cmpq %rdi, %r8
sete %r11b
movzx %r11b, %r8d
movq %r8, 152(%rsp)
testl %r8d, %r8d
jne lb_parse_dimacs_body.L10
movq 144(%rsp), %r8
movzbl (%r8), %r8d
movq %r8, 160(%rsp)
movq 144(%rsp), %r8
movq $1, %r10
addq %r10, %r8
movq %r8, 168(%rsp)
movq 160(%rsp), %r8
movq $10, %r10
cmpq %r10, %r8
sete %r11b
movzx %r11b, %r8d
movq %r8, 176(%rsp)
testl %r8d, %r8d
jne lb_parse_dimacs_body.L11
movq 168(%rsp), %r8
jmp lb_parse_dimacs_body.L9
lb_parse_dimacs_body.L11:
movq 168(%rsp), %r8
jmp lb_parse_dimacs_body.L5
lb_parse_dimacs_body.L10:
movq 144(%rsp), %r8
jmp lb_parse_dimacs_body.L4
lb_parse_dimacs_body.L7:
movq 96(%rsp), %r8
jmp lb_parse_dimacs_body.L5
lb_parse_dimacs_body.L6:
movq 72(%rsp), %r8
jmp lb_parse_dimacs_body.L4
lb_parse_dimacs_body.L4:
movq %r8, 184(%rsp)
cmpq %rdi, %r8
sete %r11b
movzx %r11b, %r8d
movq %r8, 192(%rsp)
testl %r8d, %r8d
jne lb_parse_dimacs_body.L12
movq 64(%rsp), %r8
movq 8(%rsp), %r9
cmpq %r9, %r8
sete %r11b
movzx %r11b, %r8d
movq %r8, 200(%rsp)
testl %r8d, %r8d
jne lb_parse_dimacs_body.L13
movq 184(%rsp), %r8
movzbl (%r8), %r8d
movq %r8, 208(%rsp)
movq $45, %r10
cmpq %r10, %r8
sete %r11b
movzx %r11b, %r8d
movq %r8, 216(%rsp)
testl %r8d, %r8d
jne lb_parse_dimacs_body.L14
movq 192(%rsp), %r8
testl %r8d, %r8d
jne lb_parse_dimacs_body.L15
movq 184(%rsp), %r8
movzbl (%r8), %r8d
movq %r8, 224(%rsp)
movq $48, %r10
subq %r10, %r8
movq %r8, 232(%rsp)
movq $10, %r10
cmpq %r10, %r8
setb %r11b
movzx %r11b, %r8d
movq %r8, 240(%rsp)
testl %r8d, %r8d
jne lb_parse_dimacs_body.L16
jmp lb_parse_dimacs_body.L0
lb_parse_dimacs_body.L16:
movq 184(%rsp), %r8
movq $1, %r10
addq %r10, %r8
movq %r8, 248(%rsp)
movq 232(%rsp), %r9
jmp lb_parse_dimacs_body.L18
lb_parse_dimacs_body.L18:
movq %r8, 256(%rsp)
movq %r9, 264(%rsp)
cmpq %rdi, %r8
sete %r11b
movzx %r11b, %r8d
movq %r8, 272(%rsp)
testl %r8d, %r8d
jne lb_parse_dimacs_body.L19
movq 256(%rsp), %r8
movzbl (%r8), %r8d
movq %r8, 280(%rsp)
movq $48, %r10
subq %r10, %r8
movq %r8, 288(%rsp)
movq $10, %r10
cmpq %r10, %r8
setb %r11b
movzx %r11b, %r8d
movq %r8, 296(%rsp)
testl %r8d, %r8d
jne lb_parse_dimacs_body.L20
movq 280(%rsp), %r8
movq $32, %r10
cmpq %r10, %r8
sete %r11b
movzx %r11b, %r8d
movq %r8, 304(%rsp)
movq 280(%rsp), %r8
movq $9, %r10
subq %r10, %r8
movq %r8, 312(%rsp)
movq $5, %r10
cmpq %r10, %r8
setb %r11b
movzx %r11b, %r8d
movq %r8, 320(%rsp)
movq 304(%rsp), %r9
orq %r9, %r8
movq %r8, 328(%rsp)
testl %r8d, %r8d
jne lb_parse_dimacs_body.L21
jmp lb_parse_dimacs_body.L0
lb_parse_dimacs_body.L21:
movq 264(%rsp), %r8
movq 256(%rsp), %r9
jmp lb_parse_dimacs_body.L17
lb_parse_dimacs_body.L20:
movq 264(%rsp), %r8
movq $10, %r10
imulq %r10, %r8
movq %r8, 336(%rsp)
movq 288(%rsp), %r9
addq %r9, %r8
movq %r8, 344(%rsp)
movq $268435456, %r10
cmpq %r10, %r8
setb %r11b
movzx %r11b, %r8d
movq %r8, 352(%rsp)
testl %r8d, %r8d
jne lb_parse_dimacs_body.L22
jmp lb_parse_dimacs_body.L0
lb_parse_dimacs_body.L22:
movq 256(%rsp), %r8
movq $1, %r10
addq %r10, %r8
movq %r8, 360(%rsp)
movq 344(%rsp), %r9
jmp lb_parse_dimacs_body.L18
lb_parse_dimacs_body.L19:
movq %r9, %r8
movq 256(%rsp), %r9
jmp lb_parse_dimacs_body.L17
lb_parse_dimacs_body.L17:
movq %r8, 368(%rsp)
movq %r9, 376(%rsp)
movq $0, %r10
cmpq %r10, %r8
sete %r11b
movzx %r11b, %r8d
movq %r8, 384(%rsp)
testl %r8d, %r8d
jne lb_parse_dimacs_body.L23
movq 368(%rsp), %r8
cmpq %r8, %rax
setb %r11b
movzx %r11b, %r8d
movq %r8, 392(%rsp)
testl %r8d, %r8d
jne lb_parse_dimacs_body.L24
movq 368(%rsp), %r8
movq 64(%rsp), %r9
movl %r8d, (%r9)
movq 64(%rsp), %r8
movq $4, %r10
addq %r10, %r8
movq %r8, 400(%rsp)
movq 376(%rsp), %r8
movq 400(%rsp), %r9
jmp lb_parse_dimacs_body.L3
lb_parse_dimacs_body.L24:
jmp lb_parse_dimacs_body.L0
lb_parse_dimacs_body.L23:
movq 64(%rsp), %r8
movq $0, %r11
movl %r11d, (%r8)
movq 64(%rsp), %r8
movq $4, %r10
addq %r10, %r8
movq %r8, 408(%rsp)
movq %rsi, %r8
shlq $3, %r8
movq %r8, 416(%rsp)
addq %rdx, %r8
movq %r8, 424(%rsp)
movq 40(%rsp), %r9
movq %r9, (%r8)
movq $1, %r10
addq %r10, %rsi
movq 376(%rsp), %r8
movq 408(%rsp), %r9
jmp lb_parse_dimacs_body.L1
lb_parse_dimacs_body.L15:
jmp lb_parse_dimacs_body.L0
lb_parse_dimacs_body.L14:
movq 184(%rsp), %r8
movq $1, %r10
addq %r10, %r8
movq %r8, 432(%rsp)
cmpq %rdi, %r8
sete %r11b
movzx %r11b, %r8d
movq %r8, 440(%rsp)
testl %r8d, %r8d
jne lb_parse_dimacs_body.L25
movq 432(%rsp), %r8
movzbl (%r8), %r8d
movq %r8, 448(%rsp)
movq $48, %r10
subq %r10, %r8
movq %r8, 456(%rsp)
movq $10, %r10
cmpq %r10, %r8
setb %r11b
movzx %r11b, %r8d
movq %r8, 464(%rsp)
testl %r8d, %r8d
jne lb_parse_dimacs_body.L26
jmp lb_parse_dimacs_body.L0
lb_parse_dimacs_body.L26:
movq 432(%rsp), %r8
movq $1, %r10
addq %r10, %r8
movq %r8, 472(%rsp)
movq 456(%rsp), %r9
jmp lb_parse_dimacs_body.L28
lb_parse_dimacs_body.L28:
movq %r8, 480(%rsp)
movq %r9, 488(%rsp)
cmpq %rdi, %r8
sete %r11b
movzx %r11b, %r8d
movq %r8, 496(%rsp)
testl %r8d, %r8d
jne lb_parse_dimacs_body.L29
movq 480(%rsp), %r8
movzbl (%r8), %r8d
movq %r8, 504(%rsp)
movq $48, %r10
subq %r10, %r8
movq %r8, 512(%rsp)
movq $10, %r10
cmpq %r10, %r8
setb %r11b
movzx %r11b, %r8d
movq %r8, 520(%rsp)
testl %r8d, %r8d
jne lb_parse_dimacs_body.L30
movq 504(%rsp), %r8
movq $32, %r10
cmpq %r10, %r8
sete %r11b
movzx %r11b, %r8d
movq %r8, 528(%rsp)
movq 504(%rsp), %r8
movq $9, %r10
subq %r10, %r8
movq %r8, 536(%rsp)
movq $5, %r10
cmpq %r10, %r8
setb %r11b
movzx %r11b, %r8d
movq %r8, 544(%rsp)
movq 528(%rsp), %r9
orq %r9, %r8
movq %r8, 552(%rsp)
testl %r8d, %r8d
jne lb_parse_dimacs_body.L31
jmp lb_parse_dimacs_body.L0
lb_parse_dimacs_body.L31:
movq 488(%rsp), %r8
movq 480(%rsp), %r9
jmp lb_parse_dimacs_body.L27
lb_parse_dimacs_body.L30:
movq 488(%rsp), %r8
movq $10, %r10
imulq %r10, %r8
movq %r8, 560(%rsp)
movq 512(%rsp), %r9
addq %r9, %r8
movq %r8, 568(%rsp)
movq $268435456, %r10
cmpq %r10, %r8
setb %r11b
movzx %r11b, %r8d
movq %r8, 576(%rsp)
testl %r8d, %r8d
jne lb_parse_dimacs_body.L32
jmp lb_parse_dimacs_body.L0
lb_parse_dimacs_body.L32:
movq 480(%rsp), %r8
movq $1, %r10
addq %r10, %r8
movq %r8, 584(%rsp)
movq 568(%rsp), %r9
jmp lb_parse_dimacs_body.L28
lb_parse_dimacs_body.L29:
movq %r9, %r8
movq 480(%rsp), %r9
jmp lb_parse_dimacs_body.L27
lb_parse_dimacs_body.L27:
movq %r8, 592(%rsp)
movq %r9, 600(%rsp)
movq $0, %r10
cmpq %r10, %r8
sete %r11b
movzx %r11b, %r8d
movq %r8, 608(%rsp)
testl %r8d, %r8d
jne lb_parse_dimacs_body.L33
movq 592(%rsp), %r8
cmpq %r8, %rax
setb %r11b
movzx %r11b, %r8d
movq %r8, 616(%rsp)
testl %r8d, %r8d
jne lb_parse_dimacs_body.L34
movq 592(%rsp), %r8
movq $0, %r11
movq %r8, %r10
subq %r10, %r11
movq %r11, %r8
movq %r8, 624(%rsp)
movq 64(%rsp), %r9
movl %r8d, (%r9)
movq 64(%rsp), %r8
movq $4, %r10
addq %r10, %r8
movq %r8, 632(%rsp)
movq 600(%rsp), %r8
movq 632(%rsp), %r9
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
movq 32(%rsp), %rax
jmp lb_parse_dimacs_body.L36
lb_parse_dimacs_body.L36:
cmpq %rdi, %rax
sete %r11b
movzx %r11b, %ecx
testl %ecx, %ecx
jne lb_parse_dimacs_body.L37
movzbl (%rax), %ecx
movq %rax, %r11
movq $1, %r10
addq %r10, %r11
movq %r11, %rdx
movq $32, %r10
cmpq %r10, %rcx
sete %r11b
movzx %r11b, %esi
movq %rcx, %r11
movq $9, %r10
subq %r10, %r11
movq %r11, %r8
movq %r8, 640(%rsp)
movq $5, %r10
cmpq %r10, %r8
setb %r11b
movzx %r11b, %r8d
movq %r8, 648(%rsp)
orq %r8, %rsi
testl %esi, %esi
jne lb_parse_dimacs_body.L38
movq $99, %r10
cmpq %r10, %rcx
sete %r11b
movzx %r11b, %ecx
testl %ecx, %ecx
jne lb_parse_dimacs_body.L39
jmp lb_parse_dimacs_body.L35
lb_parse_dimacs_body.L39:
movq %rdx, %rax
jmp lb_parse_dimacs_body.L40
lb_parse_dimacs_body.L40:
cmpq %rdi, %rax
sete %r11b
movzx %r11b, %ecx
testl %ecx, %ecx
jne lb_parse_dimacs_body.L41
movzbl (%rax), %ecx
movq $1, %r10
addq %r10, %rax
movq $10, %r10
cmpq %r10, %rcx
sete %r11b
movzx %r11b, %ecx
testl %ecx, %ecx
jne lb_parse_dimacs_body.L42
jmp lb_parse_dimacs_body.L40
lb_parse_dimacs_body.L42:
jmp lb_parse_dimacs_body.L36
lb_parse_dimacs_body.L41:
jmp lb_parse_dimacs_body.L35
lb_parse_dimacs_body.L38:
movq %rdx, %rax
jmp lb_parse_dimacs_body.L36
lb_parse_dimacs_body.L37:
jmp lb_parse_dimacs_body.L35
lb_parse_dimacs_body.L35:
cmpq %rdi, %rax
sete %r11b
movzx %r11b, %eax
testl %eax, %eax
jne lb_parse_dimacs_body.L43
jmp lb_parse_dimacs_body.L0
lb_parse_dimacs_body.L43:
movq 40(%rsp), %rax
movq 16(%rsp), %rcx
movq %rax, (%rcx)
movq $1, %rax
addq $664, %rsp
ret
lb_parse_dimacs_body.L0:
movq $0, %rax
addq $664, %rsp
ret")

def addLitsCode : Program := parse("lb_read_add_lits:
subq $168, %rsp
movq (%rdi), %rax
movq %rdi, %r11
movq $56, %r10
addq %r10, %r11
movq %r11, %rcx
movq (%rcx), %rcx
movq %rdi, %r11
movq $64, %r10
addq %r10, %r11
movq %r11, %rdx
movq (%rdx), %r8
movq %r8, (%rsp)
movq $72, %r10
addq %r10, %rdi
movq %rdi, 8(%rsp)
movq (%rdi), %rdi
jmp lb_read_add_lits.L1
lb_read_add_lits.L1:
movq %r8, 16(%rsp)
cmpq %rcx, %r8
sete %r11b
movzx %r11b, %r8d
movq %r8, 24(%rsp)
testl %r8d, %r8d
jne lb_read_add_lits.L2
movq $0, %r8
movq $0, %r9
jmp lb_read_add_lits.L4
lb_read_add_lits.L4:
movq %r8, 32(%rsp)
movq %r9, 40(%rsp)
cmpq %rsi, %rdi
sete %r11b
movzx %r11b, %r8d
movq %r8, 48(%rsp)
testl %r8d, %r8d
jne lb_read_add_lits.L5
movzbl (%rdi), %r8d
movq %r8, 56(%rsp)
movq $1, %r10
addq %r10, %rdi
movq 56(%rsp), %r8
movq $127, %r10
andq %r10, %r8
movq %r8, 64(%rsp)
movq 40(%rsp), %r9
movq %r8, %r11
movq %rcx, %r10
movq %r9, %rcx
shlq %cl, %r11
movq %r10, %rcx
movq %r11, %r8
movq %r8, 72(%rsp)
movq 32(%rsp), %r9
orq %r9, %r8
movq %r8, 80(%rsp)
movq 56(%rsp), %r8
movq $128, %r10
andq %r10, %r8
movq %r8, 88(%rsp)
movq $0, %r10
cmpq %r10, %r8
setne %r11b
movzx %r11b, %r8d
movq %r8, 96(%rsp)
testl %r8d, %r8d
jne lb_read_add_lits.L6
movq %rdi, %r8
movq 80(%rsp), %rdi
jmp lb_read_add_lits.L3
lb_read_add_lits.L6:
movq 40(%rsp), %r8
movq $7, %r10
addq %r10, %r8
movq %r8, 104(%rsp)
movq $28, %r10
cmpq %r10, %r8
setb %r11b
movzx %r11b, %r8d
movq %r8, 112(%rsp)
testl %r8d, %r8d
jne lb_read_add_lits.L7
jmp lb_read_add_lits.L0
lb_read_add_lits.L7:
movq 80(%rsp), %r8
movq 104(%rsp), %r9
jmp lb_read_add_lits.L4
lb_read_add_lits.L5:
jmp lb_read_add_lits.L0
lb_read_add_lits.L3:
movq %r8, 120(%rsp)
movq $0, %r10
cmpq %r10, %rdi
sete %r11b
movzx %r11b, %r8d
movq %r8, 128(%rsp)
testl %r8d, %r8d
jne lb_read_add_lits.L8
movq %rdi, %r8
shrq $1, %r8
movq %r8, 136(%rsp)
movq $0, %r10
cmpq %r10, %r8
sete %r11b
movzx %r11b, %r8d
movq %r8, 144(%rsp)
testl %r8d, %r8d
jne lb_read_add_lits.L9
movq 136(%rsp), %r8
cmpq %r8, %rax
setb %r11b
movzx %r11b, %r8d
movq %r8, 152(%rsp)
testl %r8d, %r8d
jne lb_read_add_lits.L10
movq $1, %r10
andq %r10, %rdi
movq $0, %r11
movq %rdi, %r10
subq %r10, %r11
movq %r11, %rdi
movq 136(%rsp), %r8
xorq %rdi, %r8
movq %r8, 160(%rsp)
movq %r8, %r11
movq %rdi, %r10
subq %r10, %r11
movq %r11, %rdi
movq 16(%rsp), %r8
movl %edi, (%r8)
movq 16(%rsp), %rdi
movq $4, %r10
addq %r10, %rdi
movq %rdi, %r8
movq 120(%rsp), %rdi
jmp lb_read_add_lits.L1
lb_read_add_lits.L10:
jmp lb_read_add_lits.L0
lb_read_add_lits.L9:
jmp lb_read_add_lits.L0
lb_read_add_lits.L8:
movq 16(%rsp), %rax
movq $0, %r11
movl %r11d, (%rax)
movq 16(%rsp), %rax
movq $4, %r10
addq %r10, %rax
movq %rax, (%rdx)
movq 120(%rsp), %rax
movq 8(%rsp), %rcx
movq %rax, (%rcx)
movq 16(%rsp), %rax
movq (%rsp), %rcx
cmpq %rcx, %rax
sete %r11b
movzx %r11b, %eax
testl %eax, %eax
jne lb_read_add_lits.L11
movq $1, %rax
addq $168, %rsp
ret
lb_read_add_lits.L11:
movq $2, %rax
addq $168, %rsp
ret
lb_read_add_lits.L2:
jmp lb_read_add_lits.L0
lb_read_add_lits.L0:
movq $0, %rax
addq $168, %rsp
ret")

def rupCheckCode : Program := parse("lb_rup_check:
subq $632, %rsp
movq %rdi, %r11
movq $24, %r10
addq %r10, %r11
movq %r11, %rax
movq (%rax), %rax
movq %rdi, %r11
movq $32, %r10
addq %r10, %r11
movq %r11, %r8
movq %r8, (%rsp)
movq (%r8), %r8
movq %r8, 8(%rsp)
movq %rdi, %r11
movq $40, %r10
addq %r10, %r11
movq %r11, %r8
movq %r8, 16(%rsp)
movq (%r8), %r8
movq %r8, 24(%rsp)
movq %rdi, %r11
movq $48, %r10
addq %r10, %r11
movq %r11, %r8
movq %r8, 32(%rsp)
movq (%r8), %r8
movq %r8, 40(%rsp)
movq $72, %r10
addq %r10, %rdi
movq (%rdi), %r8
movq %r8, 48(%rsp)
movq 8(%rsp), %r8
jmp lb_rup_check.L3
lb_rup_check.L3:
movq %r8, 56(%rsp)
movslq (%rdx), %r8
movq %r8, 64(%rsp)
testl %r8d, %r8d
jne lb_rup_check.L4
movq 48(%rsp), %rdx
movq 56(%rsp), %r8
jmp lb_rup_check.L2
lb_rup_check.L4:
movq 64(%rsp), %r8
sarq $63, %r8
movq %r8, 72(%rsp)
movq 64(%rsp), %r9
xorq %r9, %r8
movq %r8, 80(%rsp)
movq 72(%rsp), %r9
subq %r9, %r8
movq %r8, 88(%rsp)
addq %rax, %r8
movq %r8, 96(%rsp)
movsbq (%r8), %r8
movq %r8, 104(%rsp)
movq 72(%rsp), %r9
xorq %r9, %r8
movq %r8, 112(%rsp)
movq 72(%rsp), %r9
subq %r9, %r8
movq %r8, 120(%rsp)
movq $4, %r10
addq %r10, %rdx
movq 120(%rsp), %r8
movq $0, %r10
cmpq %r10, %r8
setl %r11b
movzx %r11b, %r8d
movq %r8, 128(%rsp)
testl %r8d, %r8d
jne lb_rup_check.L5
movq 120(%rsp), %r8
movq $0, %r10
cmpq %r8, %r10
setl %r11b
movzx %r11b, %r8d
movq %r8, 136(%rsp)
testl %r8d, %r8d
jne lb_rup_check.L6
movq 64(%rsp), %r8
movq $0, %r11
movq %r8, %r10
subq %r10, %r11
movq %r11, %r8
movq %r8, 144(%rsp)
movq 56(%rsp), %r8
movq 24(%rsp), %r9
cmpq %r9, %r8
sete %r11b
movzx %r11b, %r8d
movq %r8, 152(%rsp)
testl %r8d, %r8d
jne lb_rup_check.L7
movq 144(%rsp), %r8
sarq $63, %r8
movq %r8, 160(%rsp)
movq $1, %r10
orq %r10, %r8
movq %r8, 168(%rsp)
movq 96(%rsp), %r9
movb %r8b, (%r9)
movq 144(%rsp), %r8
movq 56(%rsp), %r9
movl %r8d, (%r9)
movq 56(%rsp), %r8
movq $4, %r10
addq %r10, %r8
movq %r8, 176(%rsp)
jmp lb_rup_check.L3
lb_rup_check.L7:
jmp lb_rup_check.L0
lb_rup_check.L6:
movq 48(%rsp), %rdx
movq 56(%rsp), %r8
jmp lb_rup_check.L1
lb_rup_check.L5:
movq 56(%rsp), %r8
jmp lb_rup_check.L3
lb_rup_check.L2:
movq %r8, 184(%rsp)
jmp lb_rup_check.L8
lb_rup_check.L8:
movq %r8, 192(%rsp)
movq $0, %r8
movq $0, %r9
jmp lb_rup_check.L10
lb_rup_check.L10:
movq %r8, 200(%rsp)
movq %r9, 208(%rsp)
cmpq %rcx, %rdx
sete %r11b
movzx %r11b, %r8d
movq %r8, 216(%rsp)
testl %r8d, %r8d
jne lb_rup_check.L11
movzbl (%rdx), %r8d
movq %r8, 224(%rsp)
movq $1, %r10
addq %r10, %rdx
movq 224(%rsp), %r8
movq $127, %r10
andq %r10, %r8
movq %r8, 232(%rsp)
movq 208(%rsp), %r9
movq %r8, %r11
movq %rcx, %r10
movq %r9, %rcx
shlq %cl, %r11
movq %r10, %rcx
movq %r11, %r8
movq %r8, 240(%rsp)
movq 200(%rsp), %r9
orq %r9, %r8
movq %r8, 248(%rsp)
movq 224(%rsp), %r8
movq $128, %r10
andq %r10, %r8
movq %r8, 256(%rsp)
movq $0, %r10
cmpq %r10, %r8
setne %r11b
movzx %r11b, %r8d
movq %r8, 264(%rsp)
testl %r8d, %r8d
jne lb_rup_check.L12
movq %rdx, %r8
movq 248(%rsp), %rdx
jmp lb_rup_check.L9
lb_rup_check.L12:
movq 208(%rsp), %r8
movq $7, %r10
addq %r10, %r8
movq %r8, 272(%rsp)
movq $28, %r10
cmpq %r10, %r8
setb %r11b
movzx %r11b, %r8d
movq %r8, 280(%rsp)
testl %r8d, %r8d
jne lb_rup_check.L13
jmp lb_rup_check.L0
lb_rup_check.L13:
movq 248(%rsp), %r8
movq 272(%rsp), %r9
jmp lb_rup_check.L10
lb_rup_check.L11:
jmp lb_rup_check.L0
lb_rup_check.L9:
movq %r8, 288(%rsp)
movq $0, %r10
cmpq %r10, %rdx
sete %r11b
movzx %r11b, %r8d
movq %r8, 296(%rsp)
testl %r8d, %r8d
jne lb_rup_check.L14
movq %rdx, %r11
movq $1, %r10
andq %r10, %r11
movq %r11, %r8
movq %r8, 304(%rsp)
movq $0, %r10
cmpq %r10, %r8
setne %r11b
movzx %r11b, %r8d
movq %r8, 312(%rsp)
testl %r8d, %r8d
jne lb_rup_check.L15
shrq $1, %rdx
cmpq %rsi, %rdx
setb %r11b
movzx %r11b, %r8d
movq %r8, 320(%rsp)
testl %r8d, %r8d
jne lb_rup_check.L16
jmp lb_rup_check.L0
lb_rup_check.L16:
shlq $3, %rdx
movq 40(%rsp), %r8
addq %r8, %rdx
movq (%rdx), %rdx
movq $0, %r10
cmpq %r10, %rdx
setne %r11b
movzx %r11b, %r8d
movq %r8, 328(%rsp)
testl %r8d, %r8d
jne lb_rup_check.L17
jmp lb_rup_check.L0
lb_rup_check.L17:
movq 192(%rsp), %r9
movq $0, %r8
jmp lb_rup_check.L19
lb_rup_check.L19:
movq %r8, 336(%rsp)
movq %r9, 344(%rsp)
movslq (%rdx), %r8
movq %r8, 352(%rsp)
testl %r8d, %r8d
jne lb_rup_check.L20
movq 336(%rsp), %rdx
movq %r9, %r8
jmp lb_rup_check.L18
lb_rup_check.L20:
movq 352(%rsp), %r8
sarq $63, %r8
movq %r8, 360(%rsp)
movq 352(%rsp), %r9
xorq %r9, %r8
movq %r8, 368(%rsp)
movq 360(%rsp), %r9
subq %r9, %r8
movq %r8, 376(%rsp)
addq %rax, %r8
movq %r8, 384(%rsp)
movsbq (%r8), %r8
movq %r8, 392(%rsp)
movq 360(%rsp), %r9
xorq %r9, %r8
movq %r8, 400(%rsp)
movq 360(%rsp), %r9
subq %r9, %r8
movq %r8, 408(%rsp)
movq $4, %r10
addq %r10, %rdx
movq 408(%rsp), %r8
movq $0, %r10
cmpq %r10, %r8
setl %r11b
movzx %r11b, %r8d
movq %r8, 416(%rsp)
testl %r8d, %r8d
jne lb_rup_check.L21
movq 336(%rsp), %r8
testl %r8d, %r8d
jne lb_rup_check.L23
jmp lb_rup_check.L22
lb_rup_check.L23:
movq 336(%rsp), %r8
movq 352(%rsp), %r9
cmpq %r9, %r8
sete %r11b
movzx %r11b, %r8d
movq %r8, 424(%rsp)
testl %r8d, %r8d
jne lb_rup_check.L24
jmp lb_rup_check.L0
lb_rup_check.L24:
jmp lb_rup_check.L22
lb_rup_check.L22:
movq 408(%rsp), %r8
movq $0, %r10
cmpq %r10, %r8
sete %r11b
movzx %r11b, %r8d
movq %r8, 432(%rsp)
testl %r8d, %r8d
jne lb_rup_check.L25
movq 352(%rsp), %r8
movq 344(%rsp), %r9
jmp lb_rup_check.L19
lb_rup_check.L25:
movq 344(%rsp), %r8
movq 24(%rsp), %r9
cmpq %r9, %r8
sete %r11b
movzx %r11b, %r8d
movq %r8, 440(%rsp)
testl %r8d, %r8d
jne lb_rup_check.L26
movq 360(%rsp), %r8
movq $1, %r10
orq %r10, %r8
movq %r8, 448(%rsp)
movq 384(%rsp), %r9
movb %r8b, (%r9)
movq 352(%rsp), %r8
movq 344(%rsp), %r9
movl %r8d, (%r9)
movq 344(%rsp), %r8
movq $4, %r10
addq %r10, %r8
movq %r8, 456(%rsp)
movq 352(%rsp), %r8
movq 456(%rsp), %r9
jmp lb_rup_check.L19
lb_rup_check.L26:
jmp lb_rup_check.L0
lb_rup_check.L21:
movq 352(%rsp), %r8
movq $0, %r11
movq %r8, %r10
subq %r10, %r11
movq %r11, %r8
movq %r8, 464(%rsp)
movq 336(%rsp), %r9
cmpq %r8, %r9
sete %r11b
movzx %r11b, %r8d
movq %r8, 472(%rsp)
testl %r8d, %r8d
jne lb_rup_check.L27
movq %r9, %r8
movq 344(%rsp), %r9
jmp lb_rup_check.L19
lb_rup_check.L27:
jmp lb_rup_check.L0
lb_rup_check.L18:
movq %r8, 480(%rsp)
testl %edx, %edx
jne lb_rup_check.L28
movq 288(%rsp), %rdx
jmp lb_rup_check.L1
lb_rup_check.L28:
movq 288(%rsp), %rdx
jmp lb_rup_check.L8
lb_rup_check.L15:
jmp lb_rup_check.L0
lb_rup_check.L14:
jmp lb_rup_check.L0
lb_rup_check.L1:
movq %r8, 488(%rsp)
jmp lb_rup_check.L29
lb_rup_check.L29:
movq $0, %r8
movq $0, %r9
jmp lb_rup_check.L31
lb_rup_check.L31:
movq %r8, 496(%rsp)
movq %r9, 504(%rsp)
cmpq %rcx, %rdx
sete %r11b
movzx %r11b, %r8d
movq %r8, 512(%rsp)
testl %r8d, %r8d
jne lb_rup_check.L32
movzbl (%rdx), %r8d
movq %r8, 520(%rsp)
movq $1, %r10
addq %r10, %rdx
movq 520(%rsp), %r8
movq $127, %r10
andq %r10, %r8
movq %r8, 528(%rsp)
movq 504(%rsp), %r9
movq %r8, %r11
movq %rcx, %r10
movq %r9, %rcx
shlq %cl, %r11
movq %r10, %rcx
movq %r11, %r8
movq %r8, 536(%rsp)
movq 496(%rsp), %r9
orq %r9, %r8
movq %r8, 544(%rsp)
movq 520(%rsp), %r8
movq $128, %r10
andq %r10, %r8
movq %r8, 552(%rsp)
movq $0, %r10
cmpq %r10, %r8
setne %r11b
movzx %r11b, %r8d
movq %r8, 560(%rsp)
testl %r8d, %r8d
jne lb_rup_check.L33
movq %rdx, %r8
movq 544(%rsp), %rdx
jmp lb_rup_check.L30
lb_rup_check.L33:
movq 504(%rsp), %r8
movq $7, %r10
addq %r10, %r8
movq %r8, 568(%rsp)
movq $28, %r10
cmpq %r10, %r8
setb %r11b
movzx %r11b, %r8d
movq %r8, 576(%rsp)
testl %r8d, %r8d
jne lb_rup_check.L34
jmp lb_rup_check.L0
lb_rup_check.L34:
movq 544(%rsp), %r8
movq 568(%rsp), %r9
jmp lb_rup_check.L31
lb_rup_check.L32:
jmp lb_rup_check.L0
lb_rup_check.L30:
movq %r8, 584(%rsp)
movq $0, %r10
cmpq %r10, %rdx
sete %r11b
movzx %r11b, %r8d
movq %r8, 592(%rsp)
testl %r8d, %r8d
jne lb_rup_check.L35
movq %rdx, %r11
movq $1, %r10
andq %r10, %r11
movq %r11, %r8
movq %r8, 600(%rsp)
movq $0, %r10
cmpq %r10, %r8
setne %r11b
movzx %r11b, %r8d
movq %r8, 608(%rsp)
testl %r8d, %r8d
jne lb_rup_check.L36
shrq $1, %rdx
cmpq %rsi, %rdx
setb %r11b
movzx %r11b, %r8d
movq %r8, 616(%rsp)
testl %r8d, %r8d
jne lb_rup_check.L37
jmp lb_rup_check.L0
lb_rup_check.L37:
shlq $3, %rdx
movq 40(%rsp), %r8
addq %r8, %rdx
movq (%rdx), %rdx
movq $0, %r10
cmpq %r10, %rdx
setne %r11b
movzx %r11b, %edx
testl %edx, %edx
jne lb_rup_check.L38
jmp lb_rup_check.L0
lb_rup_check.L38:
movq 584(%rsp), %rdx
jmp lb_rup_check.L29
lb_rup_check.L36:
jmp lb_rup_check.L0
lb_rup_check.L35:
movq 8(%rsp), %rcx
jmp lb_rup_check.L39
lb_rup_check.L39:
movq 488(%rsp), %rdx
cmpq %rdx, %rcx
sete %r11b
movzx %r11b, %edx
testl %edx, %edx
jne lb_rup_check.L40
movslq (%rcx), %rdx
movq %rdx, %rsi
sarq $63, %rsi
xorq %rsi, %rdx
subq %rsi, %rdx
addq %rax, %rdx
movq $0, %r11
movb %r11b, (%rdx)
movq $4, %r10
addq %r10, %rcx
jmp lb_rup_check.L39
lb_rup_check.L40:
movq 584(%rsp), %rax
movq %rax, (%rdi)
movq $1, %rax
addq $632, %rsp
ret
lb_rup_check.L0:
movq $0, %rax
addq $632, %rsp
ret")

def checkPrfCode : Program := parse("lb_check_prf:
subq $88, %rsp
movq %rdi, (%rsp)
movq %rsi, 8(%rsp)
movq %rdi, %r11
movq $8, %r10
addq %r10, %r11
movq %r11, %rax
movq (%rax), %rax
movq %rax, 16(%rsp)
movq (%rsp), %rax
movq $16, %r10
addq %r10, %rax
movq (%rax), %rax
movq %rax, 24(%rsp)
movq (%rsp), %rax
movq $48, %r10
addq %r10, %rax
movq (%rax), %rax
movq %rax, 32(%rsp)
movq (%rsp), %rax
movq $64, %r10
addq %r10, %rax
movq %rax, 40(%rsp)
movq (%rsp), %rax
movq $72, %r10
addq %r10, %rax
movq %rax, 48(%rsp)
jmp lb_check_prf.L1
lb_check_prf.L1:
movq 48(%rsp), %rax
movq (%rax), %rax
movq 8(%rsp), %rcx
cmpq %rcx, %rax
sete %r11b
movzx %r11b, %ecx
testl %ecx, %ecx
jne lb_check_prf.L2
movzbl (%rax), %ecx
movq $1, %r10
addq %r10, %rax
movq $97, %r10
cmpq %r10, %rcx
sete %r11b
movzx %r11b, %edx
testl %edx, %edx
jne lb_check_prf.L3
movq $100, %r10
cmpq %r10, %rcx
sete %r11b
movzx %r11b, %ecx
testl %ecx, %ecx
jne lb_check_prf.L4
jmp lb_check_prf.L0
lb_check_prf.L4:
jmp lb_check_prf.L5
lb_check_prf.L5:
movq $0, %rcx
movq $0, %rdx
jmp lb_check_prf.L7
lb_check_prf.L7:
movq 8(%rsp), %rsi
cmpq %rsi, %rax
sete %r11b
movzx %r11b, %esi
testl %esi, %esi
jne lb_check_prf.L8
movzbl (%rax), %esi
movq $1, %r10
addq %r10, %rax
movq %rsi, %r11
movq $127, %r10
andq %r10, %r11
movq %r11, %rdi
movq %rdi, %r11
movq %rcx, %r10
movq %rdx, %rcx
shlq %cl, %r11
movq %r10, %rcx
movq %r11, %rdi
orq %rdi, %rcx
movq $128, %r10
andq %r10, %rsi
movq $0, %r10
cmpq %r10, %rsi
setne %r11b
movzx %r11b, %esi
testl %esi, %esi
jne lb_check_prf.L9
movq %rax, %r10
movq %rcx, %rax
movq %r10, %rcx
jmp lb_check_prf.L6
lb_check_prf.L9:
movq $7, %r10
addq %r10, %rdx
movq $28, %r10
cmpq %r10, %rdx
setb %r11b
movzx %r11b, %esi
testl %esi, %esi
jne lb_check_prf.L10
jmp lb_check_prf.L0
lb_check_prf.L10:
jmp lb_check_prf.L7
lb_check_prf.L8:
jmp lb_check_prf.L0
lb_check_prf.L6:
movq $0, %r10
cmpq %r10, %rax
sete %r11b
movzx %r11b, %edx
testl %edx, %edx
jne lb_check_prf.L11
movq %rax, %r11
movq $1, %r10
andq %r10, %r11
movq %r11, %rdx
movq $0, %r10
cmpq %r10, %rdx
setne %r11b
movzx %r11b, %edx
testl %edx, %edx
jne lb_check_prf.L12
shrq $1, %rax
movq $0, %r10
cmpq %r10, %rax
sete %r11b
movzx %r11b, %edx
testl %edx, %edx
jne lb_check_prf.L13
movq 24(%rsp), %rdx
cmpq %rdx, %rax
setb %r11b
movzx %r11b, %edx
testl %edx, %edx
jne lb_check_prf.L14
jmp lb_check_prf.L0
lb_check_prf.L14:
shlq $3, %rax
movq 32(%rsp), %rdx
addq %rdx, %rax
movq (%rax), %rdx
movq $0, %r10
cmpq %r10, %rdx
setne %r11b
movzx %r11b, %edx
testl %edx, %edx
jne lb_check_prf.L15
jmp lb_check_prf.L0
lb_check_prf.L15:
movq $0, %r11
movq %r11, (%rax)
movq %rcx, %rax
jmp lb_check_prf.L5
lb_check_prf.L13:
jmp lb_check_prf.L0
lb_check_prf.L12:
jmp lb_check_prf.L0
lb_check_prf.L11:
movq 48(%rsp), %rax
movq %rcx, (%rax)
jmp lb_check_prf.L1
lb_check_prf.L3:
movq $0, %rcx
movq $0, %rdx
jmp lb_check_prf.L17
lb_check_prf.L17:
movq 8(%rsp), %rsi
cmpq %rsi, %rax
sete %r11b
movzx %r11b, %esi
testl %esi, %esi
jne lb_check_prf.L18
movzbl (%rax), %esi
movq $1, %r10
addq %r10, %rax
movq %rsi, %r11
movq $127, %r10
andq %r10, %r11
movq %r11, %rdi
movq %rdi, %r11
movq %rcx, %r10
movq %rdx, %rcx
shlq %cl, %r11
movq %r10, %rcx
movq %r11, %rdi
orq %rdi, %rcx
movq $128, %r10
andq %r10, %rsi
movq $0, %r10
cmpq %r10, %rsi
setne %r11b
movzx %r11b, %esi
testl %esi, %esi
jne lb_check_prf.L19
movq %rax, %r10
movq %rcx, %rax
movq %r10, %rcx
jmp lb_check_prf.L16
lb_check_prf.L19:
movq $7, %r10
addq %r10, %rdx
movq $28, %r10
cmpq %r10, %rdx
setb %r11b
movzx %r11b, %esi
testl %esi, %esi
jne lb_check_prf.L20
jmp lb_check_prf.L0
lb_check_prf.L20:
jmp lb_check_prf.L17
lb_check_prf.L18:
jmp lb_check_prf.L0
lb_check_prf.L16:
movq %rax, %r11
movq $1, %r10
andq %r10, %r11
movq %r11, %rdx
movq $0, %r10
cmpq %r10, %rdx
setne %r11b
movzx %r11b, %edx
testl %edx, %edx
jne lb_check_prf.L21
shrq $1, %rax
movq %rax, 56(%rsp)
movq 16(%rsp), %rdx
cmpq %rax, %rdx
setb %r11b
movzx %r11b, %eax
testl %eax, %eax
jne lb_check_prf.L22
jmp lb_check_prf.L0
lb_check_prf.L22:
movq 56(%rsp), %rax
movq 24(%rsp), %rdx
cmpq %rdx, %rax
setb %r11b
movzx %r11b, %eax
testl %eax, %eax
jne lb_check_prf.L23
jmp lb_check_prf.L0
lb_check_prf.L23:
movq 56(%rsp), %rax
shlq $3, %rax
movq 32(%rsp), %rdx
addq %rdx, %rax
movq %rax, 64(%rsp)
movq (%rax), %rax
movq $0, %r10
cmpq %r10, %rax
setne %r11b
movzx %r11b, %eax
testl %eax, %eax
jne lb_check_prf.L24
movq 48(%rsp), %rax
movq %rcx, (%rax)
movq 40(%rsp), %rax
movq (%rax), %rax
movq %rax, 72(%rsp)
movq (%rsp), %rdi
movq 8(%rsp), %rsi
call lb_read_add_lits
movq %rax, 80(%rsp)
movq $0, %r10
cmpq %r10, %rax
setne %r11b
movzx %r11b, %eax
testl %eax, %eax
jne lb_check_prf.L25
jmp lb_check_prf.L0
lb_check_prf.L25:
movq (%rsp), %rdi
movq 56(%rsp), %rsi
movq 72(%rsp), %rdx
movq 8(%rsp), %rcx
call lb_rup_check
movq $0, %r10
cmpq %r10, %rax
setne %r11b
movzx %r11b, %eax
testl %eax, %eax
jne lb_check_prf.L26
jmp lb_check_prf.L0
lb_check_prf.L26:
movq 80(%rsp), %rax
movq $2, %r10
cmpq %r10, %rax
sete %r11b
movzx %r11b, %eax
testl %eax, %eax
jne lb_check_prf.L27
movq 72(%rsp), %rax
movq 64(%rsp), %rcx
movq %rax, (%rcx)
jmp lb_check_prf.L1
lb_check_prf.L27:
movq $1, %rax
addq $88, %rsp
ret
lb_check_prf.L24:
jmp lb_check_prf.L0
lb_check_prf.L21:
jmp lb_check_prf.L0
lb_check_prf.L2:
jmp lb_check_prf.L0
lb_check_prf.L0:
movq $0, %rax
addq $88, %rsp
ret")

def checkBytesCode : Program := parse("lrat_check_bytes:
subq $232, %rsp
movq %rdx, (%rsp)
movq %rcx, 8(%rsp)
movq %r8, 16(%rsp)
movq %r9, 24(%rsp)
movq $128, %r10
cmpq %r10, %r9
setb %r11b
movzx %r11b, %eax
testl %eax, %eax
jne lrat_check_bytes.L0
movq %rdi, %rax
addq %rsi, %rax
movq %rax, 32(%rsp)
movq (%rsp), %rax
movq 8(%rsp), %rcx
addq %rcx, %rax
movq %rax, 40(%rsp)
movq 32(%rsp), %rsi
movq %r8, %rdx
call lb_parse_dimacs_header
movq $0, %r10
cmpq %r10, %rax
setne %r11b
movzx %r11b, %eax
testl %eax, %eax
jne lrat_check_bytes.L1
movq $0, %rax
addq $232, %rsp
ret
lrat_check_bytes.L1:
movq 16(%rsp), %rax
movq (%rax), %rax
movq 16(%rsp), %rcx
movq $8, %r10
addq %r10, %rcx
movq (%rcx), %rcx
movq %rax, %r11
movq $1, %r10
addq %r10, %r11
movq %r11, %rdx
movq %rax, %r11
movq $8, %r10
addq %r10, %r11
movq %r11, %rsi
movq $-8, %r10
andq %r10, %rsi
shlq $2, %rdx
movq %rdx, %r11
movq $7, %r10
addq %r10, %r11
movq %r11, %rdi
movq $-8, %r10
andq %r10, %rdi
movq %rsi, %r8
addq %rdi, %r8
movq %r8, 48(%rsp)
movq $80, %r11
movq %r8, %r10
addq %r10, %r11
movq %r11, %r8
movq %r8, 56(%rsp)
movq 24(%rsp), %r9
cmpq %r8, %r9
setb %r11b
movzx %r11b, %r8d
movq %r8, 64(%rsp)
testl %r8d, %r8d
jne lrat_check_bytes.L2
movq 24(%rsp), %r8
movq 56(%rsp), %r9
subq %r9, %r8
movq %r8, 72(%rsp)
shrq $4, %r8
movq %r8, 80(%rsp)
movq 8(%rsp), %r8
movq $268435455, %r10
andq %r10, %r8
movq %r8, 88(%rsp)
addq %rcx, %r8
movq %r8, 96(%rsp)
movq $32, %r10
addq %r10, %r8
movq %r8, 104(%rsp)
movq 80(%rsp), %r9
cmpq %r8, %r9
setb %r11b
movzx %r11b, %r8d
movq %r8, 112(%rsp)
testl %r8d, %r8d
jne lrat_check_bytes.L4
movq 104(%rsp), %r8
jmp lrat_check_bytes.L3
lrat_check_bytes.L4:
movq %r9, %r8
jmp lrat_check_bytes.L3
lrat_check_bytes.L3:
movq %r8, 120(%rsp)
cmpq %rcx, %r8
setbe %r11b
movzx %r11b, %ecx
testl %ecx, %ecx
jne lrat_check_bytes.L5
movq 16(%rsp), %rcx
movq $80, %r10
addq %r10, %rcx
addq %rcx, %rsi
addq %rsi, %rdx
addq %rsi, %rdi
movq 120(%rsp), %r8
shlq $3, %r8
movq %r8, 128(%rsp)
addq %rdi, %r8
movq %r8, 136(%rsp)
movq 72(%rsp), %r8
movq 128(%rsp), %r9
subq %r9, %r8
movq %r8, 144(%rsp)
movq $-4, %r10
andq %r10, %r8
movq %r8, 152(%rsp)
movq 136(%rsp), %r9
addq %r9, %r8
movq %r8, 160(%rsp)
movq $0, %r8
jmp lrat_check_bytes.L7
lrat_check_bytes.L7:
movq %r8, 168(%rsp)
cmpq %rax, %r8
setbe %r11b
movzx %r11b, %r8d
movq %r8, 176(%rsp)
testl %r8d, %r8d
jne lrat_check_bytes.L8
jmp lrat_check_bytes.L6
lrat_check_bytes.L8:
movq 168(%rsp), %r8
addq %rcx, %r8
movq %r8, 184(%rsp)
movq $0, %r11
movb %r11b, (%r8)
movq 168(%rsp), %r8
movq $1, %r10
addq %r10, %r8
movq %r8, 192(%rsp)
jmp lrat_check_bytes.L7
lrat_check_bytes.L6:
movq $0, %rax
jmp lrat_check_bytes.L10
lrat_check_bytes.L10:
movq 120(%rsp), %r8
cmpq %r8, %rax
setb %r11b
movzx %r11b, %r8d
movq %r8, 200(%rsp)
testl %r8d, %r8d
jne lrat_check_bytes.L11
jmp lrat_check_bytes.L9
lrat_check_bytes.L11:
movq %rax, %r8
shlq $3, %r8
movq %r8, 208(%rsp)
addq %rdi, %r8
movq %r8, 216(%rsp)
movq $0, %r11
movq %r11, (%r8)
movq $1, %r10
addq %r10, %rax
jmp lrat_check_bytes.L10
lrat_check_bytes.L9:
movq 16(%rsp), %rax
movq $16, %r10
addq %r10, %rax
movq 120(%rsp), %r8
movq %r8, (%rax)
movq 16(%rsp), %rax
movq $24, %r10
addq %r10, %rax
movq %rcx, (%rax)
movq 16(%rsp), %rax
movq $32, %r10
addq %r10, %rax
movq %rsi, (%rax)
movq 16(%rsp), %rax
movq $40, %r10
addq %r10, %rax
movq %rdx, (%rax)
movq 16(%rsp), %rax
movq $48, %r10
addq %r10, %rax
movq %rdi, (%rax)
movq 16(%rsp), %rax
movq $56, %r10
addq %r10, %rax
movq 160(%rsp), %rcx
movq %rcx, (%rax)
movq 16(%rsp), %rax
movq $64, %r10
addq %r10, %rax
movq 136(%rsp), %rcx
movq %rcx, (%rax)
movq 32(%rsp), %rdi
movq 16(%rsp), %rsi
call lb_parse_dimacs_body
movq $0, %r10
cmpq %r10, %rax
setne %r11b
movzx %r11b, %eax
testl %eax, %eax
jne lrat_check_bytes.L12
movq $0, %rax
addq $232, %rsp
ret
lrat_check_bytes.L12:
movq 16(%rsp), %rax
movq $72, %r10
addq %r10, %rax
movq (%rsp), %rcx
movq %rcx, (%rax)
movq 16(%rsp), %rdi
movq 40(%rsp), %rsi
call lb_check_prf
addq $232, %rsp
ret
lrat_check_bytes.L5:
movq $0, %rax
addq $232, %rsp
ret
lrat_check_bytes.L2:
movq $0, %rax
addq $232, %rsp
ret
lrat_check_bytes.L0:
movq $0, %rax
addq $232, %rsp
ret")


def lratBytesCode : Program :=
  hdrCode ++ (bodyCode ++ (addLitsCode ++ (rupCheckCode ++ (checkPrfCode ++ (checkBytesCode ++ [])))))

def lratBytesBounds : List (String × Nat) :=
  [("lb_parse_dimacs_header", 136),
   ("lb_parse_dimacs_body", 664),
   ("lb_read_add_lits", 168),
   ("lb_rup_check", 632),
   ("lb_check_prf", 728),
   ("lrat_check_bytes", 968)]

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
