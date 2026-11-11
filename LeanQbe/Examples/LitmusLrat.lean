module

public import LeanQbe.Examples.Litmus
public import LeanQbe.Examples.LratTrimCheckLemmas
public import LeanQbe.MainLemmas
import all Kraken.Separation
import all Kraken.Mem

/-!
# LRAT-trim checker end to end on x64 (plan step 7)

Compiles the four-function verified LRAT checker module `LratTrim.lratCheckFns`:
* `br_check_clause_non_strictly_by_propagation` (`LratRup.checkRup`, 59 spill slots, 472-byte frame)
* `br_check_clause_strictly_by_resolution` (`LratTrim.strictCheck`, 37 spill slots, 296-byte frame)
* `br_check_clause` (`LratTrim.checkClause`, 4 spill slots, 40-byte frame)
* `br_check_proof` (`LratTrim.checkProof`, 7 spill slots, 56-byte frame)

through the full verified pipeline (`compile Amd64.isa`), checks the emitted x64 assembly in the
kernel (`kernel_rfl`), links all four contracts via `compile_correct` and `lratEnv_step`
(`lrat_module_fnspec`), and proves the closed Kraken-x64 end-to-end theorem `checkProof_x64_correct`
concluding `cnf₀.Unsat` on normal return (or exit to `"lrat_fail"`), plus a concrete-byte
non-vacuity instance `checkProof_x64_nonvacuous`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.Litmus

open LeanQbe LeanQbe.LratRup LeanQbe.LratTrim Rega Amd64
open Std.Sat Std.Tactic.BVDecide.LRAT.Internal Kraken.Bedrock2.Test

abbrev rupFn : Fn := ⟨"br_check_clause_non_strictly_by_propagation", LratRup.checkRup⟩
abbrev strictFn : Fn := ⟨"br_check_clause_strictly_by_resolution", strictCheck⟩
abbrev clauseFn : Fn := ⟨"br_check_clause", checkClause⟩
abbrev proofFn : Fn := ⟨"br_check_proof", checkProof⟩

def rupCode : Program := parse("br_check_clause_non_strictly_by_propagation:
subq $104, %rsp
movq %rbx, 56(%rsp)
movq %rbp, 64(%rsp)
movq %r12, 72(%rsp)
movq %r13, 80(%rsp)
movq %r14, 88(%rsp)
movq %r15, 96(%rsp)
movq %rsi, 48(%rsp)
movq %rcx, %r14
movq %rdi, %r11
movq $16, %r10
addq %r10, %r11
movq %r11, %rax
movq (%rax), %rax
movq %rax, 40(%rsp)
movq %rdi, %r11
movq $24, %r10
addq %r10, %r11
movq %r11, %rax
movq (%rax), %r13
movq %rdi, %r11
movq $40, %r10
addq %r10, %r11
movq %r11, %rax
movq (%rax), %rax
movq %rax, 32(%rsp)
movq %rdi, %r11
movq $48, %r10
addq %r10, %r11
movq %r11, %rax
movq %rax, 8(%rsp)
movq (%rax), %rax
movq %rdi, %r11
movq $144, %r10
addq %r10, %r11
movq %r11, %rcx
movq %rcx, 16(%rsp)
movq (%rcx), %r12
movq %r12, %r11
movq $1, %r10
addq %r10, %r11
movq %r11, %r12
movq %rdi, %r11
movq $152, %r10
addq %r10, %r11
movq %r11, %rdi
movq %rdi, 24(%rsp)
movq (%rdi), %rcx
movq %rdx, %rdi
br_check_clause_non_strictly_by_propagation.L3:
movslq (%rdi), %rdx
testl %edx, %edx
jne br_check_clause_non_strictly_by_propagation.L4
jmp br_check_clause_non_strictly_by_propagation.L2
br_check_clause_non_strictly_by_propagation.L4:
movq %rdx, %r11
movq %rcx, %r10
movq $63, %rcx
sarq %cl, %r11
movq %r10, %rcx
movq %r11, %rsi
movq %rdx, %r11
movq %rsi, %r10
xorq %r10, %r11
movq %r11, %rbx
movq %rbx, %r11
movq %rsi, %r10
subq %r10, %r11
movq %r11, %rbx
movq %r13, %r11
movq %rbx, %r10
addq %r10, %r11
movq %r11, %rbx
movsbq (%rbx), %rbp
movq %rbp, %r11
movq %rsi, %r10
xorq %r10, %r11
movq %r11, %rbp
movq %rbp, %r11
movq %rsi, %r10
subq %r10, %r11
movq %r11, %rsi
movq %rdi, %r11
movq $4, %r10
addq %r10, %r11
movq %r11, %rdi
movq %rsi, %r11
movq $0, %r10
cmpq %r10, %r11
setl %r11b
movzx %r11b, %r8d
testl %r8d, %r8d
jne br_check_clause_non_strictly_by_propagation.L5
movq $0, %r11
movq %rsi, %r10
cmpq %r10, %r11
setl %r11b
movzx %r11b, %esi
testl %esi, %esi
jne br_check_clause_non_strictly_by_propagation.L6
movq $0, %r11
movq %rdx, %r10
subq %r10, %r11
movq %r11, %rdx
movq %rdx, %r11
movq %rcx, %r10
movq $63, %rcx
sarq %cl, %r11
movq %r10, %rcx
movq %r11, %rsi
movq %rsi, %r11
movq $1, %r10
orq %r10, %r11
movq %r11, %rsi
movq %rsi, %r11
movb %r11b, (%rbx)
movq %rdx, %r11
movl %r11d, (%rax)
movq %rax, %r11
movq $4, %r10
addq %r10, %r11
movq %r11, %rax
movq %rcx, %r11
movq $1, %r10
addq %r10, %r11
movq %r11, %rcx
jmp br_check_clause_non_strictly_by_propagation.L3
br_check_clause_non_strictly_by_propagation.L6:
movq %rax, %rsi
movq %r12, %rbp
movq %rcx, %rdi
jmp br_check_clause_non_strictly_by_propagation.L1
br_check_clause_non_strictly_by_propagation.L5:
jmp br_check_clause_non_strictly_by_propagation.L3
br_check_clause_non_strictly_by_propagation.L2:
movq %r12, %rbp
movq %rcx, %rsi
movq %rax, %rcx
br_check_clause_non_strictly_by_propagation.L7:
movslq (%r14), %rdx
testl %edx, %edx
jne br_check_clause_non_strictly_by_propagation.L8
movq $3, %rdi
movq $0, %rdx
jmp br_check_clause_non_strictly_by_propagation.L0
br_check_clause_non_strictly_by_propagation.L8:
movq %rdx, %r11
movq $0, %r10
cmpq %r10, %r11
setl %r11b
movzx %r11b, %eax
testl %eax, %eax
jne br_check_clause_non_strictly_by_propagation.L9
movq %rdx, %r11
movq %rcx, %r10
movq $3, %rcx
shlq %cl, %r11
movq %r10, %rcx
movq %r11, %rax
movq 40(%rsp), %rdi
movq %rdi, %r11
movq %rax, %r10
addq %r10, %r11
movq %r11, %rax
movq (%rax), %r12
movq %rbp, %r11
movq $1, %r10
addq %r10, %r11
movq %r11, %rbp
movq $0, %rdi
br_check_clause_non_strictly_by_propagation.L11:
movslq (%r12), %rax
testl %eax, %eax
jne br_check_clause_non_strictly_by_propagation.L12
jmp br_check_clause_non_strictly_by_propagation.L10
br_check_clause_non_strictly_by_propagation.L12:
movq %rax, %r11
movq %rcx, %r10
movq $63, %rcx
sarq %cl, %r11
movq %r10, %rcx
movq %r11, %rbx
movq %rax, %r11
movq %rbx, %r10
xorq %r10, %r11
movq %r11, %r15
movq %r15, %r11
movq %rbx, %r10
subq %r10, %r11
movq %r11, %r15
movq %r13, %r11
movq %r15, %r10
addq %r10, %r11
movq %r11, %r15
movsbq (%r15), %r8
movq %r8, (%rsp)
movq %r8, %r11
movq %rbx, %r10
xorq %r10, %r11
movq %r11, %r8
movq %r8, (%rsp)
movq %r8, %r11
movq %rbx, %r10
subq %r10, %r11
movq %r11, %r8
movq %r8, (%rsp)
movq %r12, %r11
movq $4, %r10
addq %r10, %r11
movq %r11, %r12
movq (%rsp), %r8
movq %r8, %r11
movq $0, %r10
cmpq %r10, %r11
setl %r11b
movzx %r11b, %r8d
testl %r8d, %r8d
jne br_check_clause_non_strictly_by_propagation.L13
testl %edi, %edi
jne br_check_clause_non_strictly_by_propagation.L15
jmp br_check_clause_non_strictly_by_propagation.L14
br_check_clause_non_strictly_by_propagation.L15:
movq %rdi, %r11
movq %rax, %r10
cmpq %r10, %r11
sete %r11b
movzx %r11b, %edi
testl %edi, %edi
jne br_check_clause_non_strictly_by_propagation.L16
movq $2, %rdi
jmp br_check_clause_non_strictly_by_propagation.L0
br_check_clause_non_strictly_by_propagation.L16:
br_check_clause_non_strictly_by_propagation.L14:
movq (%rsp), %rdi
movq %rdi, %r11
movq $0, %r10
cmpq %r10, %r11
sete %r11b
movzx %r11b, %edi
testl %edi, %edi
jne br_check_clause_non_strictly_by_propagation.L17
movq %rax, %rdi
jmp br_check_clause_non_strictly_by_propagation.L11
br_check_clause_non_strictly_by_propagation.L17:
movq %rbx, %r11
movq $1, %r10
orq %r10, %r11
movq %r11, %rbx
movq %rbx, %r11
movb %r11b, (%r15)
movq %rax, %r11
movl %r11d, (%rcx)
movq %rcx, %r11
movq $4, %r10
addq %r10, %r11
movq %r11, %rcx
movq %rsi, %r11
movq $1, %r10
addq %r10, %r11
movq %r11, %rsi
movq %rax, %rdi
jmp br_check_clause_non_strictly_by_propagation.L11
br_check_clause_non_strictly_by_propagation.L13:
movq $0, %r11
movq %rax, %r10
subq %r10, %r11
movq %r11, %rax
movq %rdi, %r11
movq %rax, %r10
cmpq %r10, %r11
sete %r11b
movzx %r11b, %eax
testl %eax, %eax
jne br_check_clause_non_strictly_by_propagation.L18
jmp br_check_clause_non_strictly_by_propagation.L11
br_check_clause_non_strictly_by_propagation.L18:
movq $2, %rdi
jmp br_check_clause_non_strictly_by_propagation.L0
br_check_clause_non_strictly_by_propagation.L10:
testl %edi, %edi
jne br_check_clause_non_strictly_by_propagation.L19
movq %rsi, %rdi
movq %rcx, %rsi
jmp br_check_clause_non_strictly_by_propagation.L1
br_check_clause_non_strictly_by_propagation.L19:
movq %r14, %r11
movq $4, %r10
addq %r10, %r11
movq %r11, %r14
jmp br_check_clause_non_strictly_by_propagation.L7
br_check_clause_non_strictly_by_propagation.L9:
movq $1, %rdi
jmp br_check_clause_non_strictly_by_propagation.L0
br_check_clause_non_strictly_by_propagation.L1:
movq 32(%rsp), %rax
br_check_clause_non_strictly_by_propagation.L20:
movq %rax, %r11
movq %rsi, %r10
cmpq %r10, %r11
sete %r11b
movzx %r11b, %ecx
testl %ecx, %ecx
jne br_check_clause_non_strictly_by_propagation.L21
movslq (%rax), %rcx
movq %rcx, %r11
movq %rcx, %r10
movq $63, %rcx
sarq %cl, %r11
movq %r10, %rcx
movq %r11, %rdx
movq %rcx, %r11
movq %rdx, %r10
xorq %r10, %r11
movq %r11, %rcx
movq %rcx, %r11
movq %rdx, %r10
subq %r10, %r11
movq %r11, %rcx
movq %r13, %r11
movq %rcx, %r10
addq %r10, %r11
movq %r11, %rcx
movq $0, %r11
movb %r11b, (%rcx)
movq %rax, %r11
movq $4, %r10
addq %r10, %r11
movq %r11, %rax
jmp br_check_clause_non_strictly_by_propagation.L20
br_check_clause_non_strictly_by_propagation.L21:
movq 32(%rsp), %rax
movq 8(%rsp), %rcx
movq %rax, %r11
movq %r11, (%rcx)
movq 16(%rsp), %rax
movq %rbp, %r11
movq %r11, (%rax)
movq 24(%rsp), %rax
movq %rdi, %r11
movq %r11, (%rax)
movq 56(%rsp), %rbx
movq 64(%rsp), %rbp
movq 72(%rsp), %r12
movq 80(%rsp), %r13
movq 88(%rsp), %r14
movq 96(%rsp), %r15
addq $104, %rsp
ret
br_check_clause_non_strictly_by_propagation.L0:
movq 8(%rsp), %rax
movq %rcx, %r11
movq %r11, (%rax)
movq 16(%rsp), %rax
movq %rbp, %r11
movq %r11, (%rax)
movq 24(%rsp), %rax
movq %rsi, %r11
movq %r11, (%rax)
movq 48(%rsp), %rsi
movq $0, %rcx
movq $0, %r8
movq 56(%rsp), %rbx
movq 64(%rsp), %rbp
movq 72(%rsp), %r12
movq 80(%rsp), %r13
movq 88(%rsp), %r14
movq 96(%rsp), %r15
addq $104, %rsp
jmp lrat_fail")

def strictCode : Program := parse("br_check_clause_strictly_by_resolution:
subq $104, %rsp
movq %rbx, 48(%rsp)
movq %rbp, 56(%rsp)
movq %r12, 64(%rsp)
movq %r13, 72(%rsp)
movq %r14, 80(%rsp)
movq %r15, 88(%rsp)
movq %rcx, 24(%rsp)
movq %rdx, 40(%rsp)
movq %rdi, %r15
movq %rcx, %rax
br_check_clause_strictly_by_resolution.L1:
movslq (%rax), %rdx
testl %edx, %edx
jne br_check_clause_strictly_by_resolution.L2
jmp br_check_clause_strictly_by_resolution.L0
br_check_clause_strictly_by_resolution.L2:
movq %rdx, %r11
movq $0, %r10
cmpq %r10, %r11
setl %r11b
movzx %r11b, %ecx
testl %ecx, %ecx
jne br_check_clause_strictly_by_resolution.L3
movq %rax, %r11
movq $4, %r10
addq %r10, %r11
movq %r11, %rax
jmp br_check_clause_strictly_by_resolution.L1
br_check_clause_strictly_by_resolution.L3:
movq $1, %rdi
movq $0, %rcx
movq $0, %r8
movq 48(%rsp), %rbx
movq 56(%rsp), %rbp
movq 64(%rsp), %r12
movq 72(%rsp), %r13
movq 80(%rsp), %r14
movq 88(%rsp), %r15
addq $104, %rsp
jmp lrat_fail
br_check_clause_strictly_by_resolution.L0:
movq %r15, %r11
movq $16, %r10
addq %r10, %r11
movq %r11, %rcx
movq (%rcx), %rcx
movq %rcx, 32(%rsp)
movq %r15, %r11
movq $32, %r10
addq %r10, %r11
movq %r11, %rcx
movq (%rcx), %rcx
movq %rcx, (%rsp)
movq %r15, %r11
movq $144, %r10
addq %r10, %r11
movq %r11, %r15
movq (%r15), %rcx
movq %rax, %r13
movq %rcx, %rax
movq $0, %rbp
movq $1, %r12
br_check_clause_strictly_by_resolution.L5:
movq 24(%rsp), %rcx
movq %r13, %r11
movq %rcx, %r10
cmpq %r10, %r11
sete %r11b
movzx %r11b, %ecx
testl %ecx, %ecx
jne br_check_clause_strictly_by_resolution.L6
movq %r13, %r11
movq $4, %r10
subq %r10, %r11
movq %r11, %r13
movslq (%r13), %rbx
movq %rbx, %r11
movq %rcx, %r10
movq $3, %rcx
shlq %cl, %r11
movq %r10, %rcx
movq %r11, %rcx
movq 32(%rsp), %rdx
movq %rdx, %r11
movq %rcx, %r10
addq %r10, %r11
movq %r11, %rcx
movq (%rcx), %r14
movq %rax, %r11
movq $1, %r10
addq %r10, %r11
movq %r11, %rax
movq $0, %rcx
br_check_clause_strictly_by_resolution.L8:
movslq (%r14), %rdx
testl %edx, %edx
jne br_check_clause_strictly_by_resolution.L9
jmp br_check_clause_strictly_by_resolution.L7
br_check_clause_strictly_by_resolution.L9:
movq %rdx, %r11
movq %rcx, %r10
movq $63, %rcx
sarq %cl, %r11
movq %r10, %rcx
movq %r11, %rdi
movq %rdx, %r11
movq %rdi, %r10
xorq %r10, %r11
movq %r11, %r8
movq %r8, 8(%rsp)
movq %r8, %r11
movq %rdi, %r10
subq %r10, %r11
movq %r11, %r8
movq %r8, 8(%rsp)
movq (%rsp), %r9
movq %r9, %r11
movq %r8, %r10
addq %r10, %r11
movq %r11, %r8
movsbq (%r8), %r9
movq %r9, 8(%rsp)
movq %r14, %r11
movq $4, %r10
addq %r10, %r11
movq %r11, %r14
movq 8(%rsp), %r9
movq %r9, %r11
movq $0, %r10
cmpq %r10, %r11
sete %r11b
movzx %r11b, %r9d
movq %r9, 16(%rsp)
testl %r9d, %r9d
jne br_check_clause_strictly_by_resolution.L10
movq 8(%rsp), %r8
movq %r8, %r11
movq %rdi, %r10
xorq %r10, %r11
movq %r11, %r8
movq %r8, 8(%rsp)
movq %r8, %r11
movq %rdi, %r10
subq %r10, %r11
movq %r11, %rdi
movq $0, %r11
movq %rdi, %r10
cmpq %r10, %r11
setl %r11b
movzx %r11b, %edi
testl %edi, %edi
jne br_check_clause_strictly_by_resolution.L11
testl %ecx, %ecx
jne br_check_clause_strictly_by_resolution.L12
movq %rdx, %rcx
jmp br_check_clause_strictly_by_resolution.L8
br_check_clause_strictly_by_resolution.L12:
movq %rax, %r11
movq %r11, (%r15)
movq %rbx, %r8
movq %rdx, %r10
movq %rcx, %rdx
movq %r10, %rcx
movq $4, %rdi
movq 48(%rsp), %rbx
movq 56(%rsp), %rbp
movq 64(%rsp), %r12
movq 72(%rsp), %r13
movq 80(%rsp), %r14
movq 88(%rsp), %r15
addq $104, %rsp
jmp lrat_fail
br_check_clause_strictly_by_resolution.L11:
jmp br_check_clause_strictly_by_resolution.L8
br_check_clause_strictly_by_resolution.L10:
movq %rdi, %r11
movq $1, %r10
orq %r10, %r11
movq %r11, %rdi
movq %rdi, %r11
movb %r11b, (%r8)
movq %rbp, %r11
movq $1, %r10
addq %r10, %r11
movq %r11, %rbp
jmp br_check_clause_strictly_by_resolution.L8
br_check_clause_strictly_by_resolution.L7:
testl %r12d, %r12d
jne br_check_clause_strictly_by_resolution.L13
testl %ecx, %ecx
jne br_check_clause_strictly_by_resolution.L14
movq %rax, %r11
movq %r11, (%r15)
movq %rbx, %rdx
movq $5, %rdi
movq $0, %rcx
movq $0, %r8
movq 48(%rsp), %rbx
movq 56(%rsp), %rbp
movq 64(%rsp), %r12
movq 72(%rsp), %r13
movq 80(%rsp), %r14
movq 88(%rsp), %r15
addq $104, %rsp
jmp lrat_fail
br_check_clause_strictly_by_resolution.L14:
movq %rcx, %r11
movq %rcx, %r10
movq $63, %rcx
sarq %cl, %r11
movq %r10, %rcx
movq %r11, %rdx
movq %rcx, %r11
movq %rdx, %r10
xorq %r10, %r11
movq %r11, %rcx
movq %rcx, %r11
movq %rdx, %r10
subq %r10, %r11
movq %r11, %rcx
movq (%rsp), %rdx
movq %rdx, %r11
movq %rcx, %r10
addq %r10, %r11
movq %r11, %rcx
movq $0, %r11
movb %r11b, (%rcx)
movq %rbp, %r11
movq $1, %r10
subq %r10, %r11
movq %r11, %rbp
jmp br_check_clause_strictly_by_resolution.L5
br_check_clause_strictly_by_resolution.L13:
testl %ecx, %ecx
jne br_check_clause_strictly_by_resolution.L15
movq $0, %r12
jmp br_check_clause_strictly_by_resolution.L5
br_check_clause_strictly_by_resolution.L15:
movq %rax, %r11
movq %r11, (%r15)
movq $0, %r11
movq %rcx, %r10
subq %r10, %r11
movq %r11, %rdx
movq %rbx, %r8
movq $4, %rdi
movq 48(%rsp), %rbx
movq 56(%rsp), %rbp
movq 64(%rsp), %r12
movq 72(%rsp), %r13
movq 80(%rsp), %r14
movq 88(%rsp), %r15
addq $104, %rsp
jmp lrat_fail
br_check_clause_strictly_by_resolution.L6:
br_check_clause_strictly_by_resolution.L4:
movq %rax, %r11
movq %r11, (%r15)
testl %r12d, %r12d
jne br_check_clause_strictly_by_resolution.L16
movq 40(%rsp), %rcx
movq %rbp, %rdi
br_check_clause_strictly_by_resolution.L18:
movslq (%rcx), %rdx
testl %edx, %edx
jne br_check_clause_strictly_by_resolution.L19
jmp br_check_clause_strictly_by_resolution.L17
br_check_clause_strictly_by_resolution.L19:
movq %rdx, %r11
movq %rcx, %r10
movq $63, %rcx
sarq %cl, %r11
movq %r10, %rcx
movq %r11, %rax
movq %rdx, %r11
movq %rax, %r10
xorq %r10, %r11
movq %r11, %rbx
movq %rbx, %r11
movq %rax, %r10
subq %r10, %r11
movq %r11, %rbx
movq (%rsp), %r8
movq %r8, %r11
movq %rbx, %r10
addq %r10, %r11
movq %r11, %rbx
movsbq (%rbx), %rbp
movq %rbp, %r11
movq $0, %r10
cmpq %r10, %r11
sete %r11b
movzx %r11b, %r8d
testl %r8d, %r8d
jne br_check_clause_strictly_by_resolution.L20
movq %rbp, %r11
movq %rax, %r10
xorq %r10, %r11
movq %r11, %rbp
movq %rbp, %r11
movq %rax, %r10
subq %r10, %r11
movq %r11, %rbp
movq %rbp, %r11
movq $0, %r10
cmpq %r10, %r11
setl %r11b
movzx %r11b, %eax
testl %eax, %eax
jne br_check_clause_strictly_by_resolution.L21
movq $0, %r11
movb %r11b, (%rbx)
movq %rdi, %r11
movq $1, %r10
subq %r10, %r11
movq %r11, %rdi
movq %rcx, %r11
movq $4, %r10
addq %r10, %r11
movq %r11, %rcx
jmp br_check_clause_strictly_by_resolution.L18
br_check_clause_strictly_by_resolution.L21:
movq $7, %rdi
movq $0, %rcx
movq $0, %r8
movq 48(%rsp), %rbx
movq 56(%rsp), %rbp
movq 64(%rsp), %r12
movq 72(%rsp), %r13
movq 80(%rsp), %r14
movq 88(%rsp), %r15
addq $104, %rsp
jmp lrat_fail
br_check_clause_strictly_by_resolution.L20:
movq $6, %rdi
movq $0, %rcx
movq $0, %r8
movq 48(%rsp), %rbx
movq 56(%rsp), %rbp
movq 64(%rsp), %r12
movq 72(%rsp), %r13
movq 80(%rsp), %r14
movq 88(%rsp), %r15
addq $104, %rsp
jmp lrat_fail
br_check_clause_strictly_by_resolution.L17:
movq %rdi, %r11
movq $0, %r10
cmpq %r10, %r11
setne %r11b
movzx %r11b, %eax
testl %eax, %eax
jne br_check_clause_strictly_by_resolution.L22
movq 48(%rsp), %rbx
movq 56(%rsp), %rbp
movq 64(%rsp), %r12
movq 72(%rsp), %r13
movq 80(%rsp), %r14
movq 88(%rsp), %r15
addq $104, %rsp
ret
br_check_clause_strictly_by_resolution.L22:
movq %rdi, %rdx
movq $8, %rdi
movq $0, %rcx
movq $0, %r8
movq 48(%rsp), %rbx
movq 56(%rsp), %rbp
movq 64(%rsp), %r12
movq 72(%rsp), %r13
movq 80(%rsp), %r14
movq 88(%rsp), %r15
addq $104, %rsp
jmp lrat_fail
br_check_clause_strictly_by_resolution.L16:
movq $3, %rdi
movq $0, %rdx
movq $0, %rcx
movq $0, %r8
movq 48(%rsp), %rbx
movq 56(%rsp), %rbp
movq 64(%rsp), %r12
movq 72(%rsp), %r13
movq 80(%rsp), %r14
movq 88(%rsp), %r15
addq $104, %rsp
jmp lrat_fail")

def clauseCode : Program := parse("br_check_clause:
subq $8, %rsp
movq %rdi, %r11
movq $128, %r10
addq %r10, %r11
movq %r11, %rax
movq (%rax), %r8
movq %r8, %r11
movq $1, %r10
addq %r10, %r11
movq %r11, %r8
movq %r8, (%rsp)
movq %r8, %r11
movq %r11, (%rax)
movl (%rdx), %eax
movq %rax, %r11
movq $0, %r10
cmpq %r10, %r11
sete %r11b
movzx %r11b, %eax
testl %eax, %eax
jne br_check_clause.L1
jmp br_check_clause.L0
br_check_clause.L1:
movq %rdi, %r11
movq $136, %r10
addq %r10, %r11
movq %r11, %rax
movq (%rax), %r8
movq %r8, %r11
movq $1, %r10
addq %r10, %r11
movq %r11, %r8
movq %r8, (%rsp)
movq %r8, %r11
movq %r11, (%rax)
br_check_clause.L0:
movq %rdi, %r11
movq $80, %r10
addq %r10, %r11
movq %r11, %rax
movq (%rax), %rax
movq %rax, %r11
movq $0, %r10
cmpq %r10, %r11
setne %r11b
movzx %r11b, %eax
testl %eax, %eax
jne br_check_clause.L2
call br_check_clause_non_strictly_by_propagation
addq $8, %rsp
ret
br_check_clause.L2:
call br_check_clause_strictly_by_resolution
addq $8, %rsp
ret")

def proofCode : Program := parse("br_check_proof:
subq $56, %rsp
movq %rbx, 8(%rsp)
movq %rbp, 16(%rsp)
movq %r12, 24(%rsp)
movq %r13, 32(%rsp)
movq %r14, 40(%rsp)
movq %r15, 48(%rsp)
movq %rdi, %rbp
movq %rbp, %r11
movq $96, %r10
addq %r10, %r11
movq %r11, %rax
movq (%rax), %rax
movq %rbp, %r11
movq $104, %r10
addq %r10, %r11
movq %r11, %rcx
movq (%rcx), %rcx
movq %rbp, %r11
movq $64, %r10
addq %r10, %r11
movq %r11, %rdx
movslq (%rdx), %r12
movq %rbp, %r11
movq $72, %r10
addq %r10, %r11
movq %r11, %rdx
movslq (%rdx), %rbx
movq %rax, %r11
movq $0, %r10
cmpq %r10, %r11
setne %r11b
movzx %r11b, %eax
testl %eax, %eax
jne br_check_proof.L0
movq 8(%rsp), %rbx
movq 16(%rsp), %rbp
movq 24(%rsp), %r12
movq 32(%rsp), %r13
movq 40(%rsp), %r14
movq 48(%rsp), %r15
addq $56, %rsp
ret
br_check_proof.L0:
movq %rcx, %r11
movq $0, %r10
cmpq %r10, %r11
sete %r11b
movzx %r11b, %eax
testl %eax, %eax
jne br_check_proof.L1
movq 8(%rsp), %rbx
movq 16(%rsp), %rbp
movq 24(%rsp), %r12
movq 32(%rsp), %r13
movq 40(%rsp), %r14
movq 48(%rsp), %r15
addq $56, %rsp
ret
br_check_proof.L1:
testl %r12d, %r12d
jne br_check_proof.L2
movq 8(%rsp), %rbx
movq 16(%rsp), %rbp
movq 24(%rsp), %r12
movq 32(%rsp), %r13
movq 40(%rsp), %r14
movq 48(%rsp), %r15
addq $56, %rsp
ret
br_check_proof.L2:
testl %ebx, %ebx
jne br_check_proof.L3
movq 8(%rsp), %rbx
movq 16(%rsp), %rbp
movq 24(%rsp), %r12
movq 32(%rsp), %r13
movq 40(%rsp), %r14
movq 48(%rsp), %r15
addq $56, %rsp
ret
br_check_proof.L3:
movq %rbp, %r11
movq $88, %r10
addq %r10, %r11
movq %r11, %rax
movq (%rax), %r13
movq (%rbp), %r14
movq %rbp, %r11
movq $16, %r10
addq %r10, %r11
movq %r11, %rax
movq (%rax), %r15
movq %rbp, %r11
movq $8, %r10
addq %r10, %r11
movq %r11, %rax
movq (%rax), %rax
movq %rax, (%rsp)
br_check_proof.L4:
movq %r12, %r11
movq %rbx, %r10
cmpq %r10, %r11
setl %r11b
movzx %r11b, %eax
testl %eax, %eax
jne br_check_proof.L5
movq %r13, %r11
movq $0, %r10
cmpq %r10, %r11
setne %r11b
movzx %r11b, %eax
testl %eax, %eax
jne br_check_proof.L8
movq $-1, %rax
jmp br_check_proof.L7
br_check_proof.L8:
movq %rbx, %r11
movq %rcx, %r10
movq $2, %rcx
shlq %cl, %r11
movq %r10, %rcx
movq %r11, %rax
movq %r14, %r11
movq %rax, %r10
addq %r10, %r11
movq %r11, %rax
movslq (%rax), %rax
br_check_proof.L7:
testl %eax, %eax
jne br_check_proof.L9
jmp br_check_proof.L6
br_check_proof.L9:
movq %rbx, %r11
movq %rcx, %r10
movq $3, %rcx
shlq %cl, %r11
movq %r10, %rcx
movq %r11, %rax
movq %r15, %r11
movq %rax, %r10
addq %r10, %r11
movq %r11, %rcx
movq (%rcx), %rdx
movq (%rsp), %rcx
movq %rcx, %r11
movq %rax, %r10
addq %r10, %r11
movq %r11, %rax
movq (%rax), %rcx
movq %rbp, %rdi
movq %rbx, %rsi
call br_check_clause
br_check_proof.L6:
movq %rbx, %r11
movq $1, %r10
addq %r10, %r11
movq %r11, %rbx
jmp br_check_proof.L4
br_check_proof.L5:
movq 8(%rsp), %rbx
movq 16(%rsp), %rbp
movq 24(%rsp), %r12
movq 32(%rsp), %r13
movq 40(%rsp), %r14
movq 48(%rsp), %r15
addq $56, %rsp
ret")

def lratCheckCode : Program := rupCode ++ (strictCode ++ (clauseCode ++ proofCode))

def lratBounds : List (String × Nat) :=
  [("br_check_clause_non_strictly_by_propagation", 296),
   ("br_check_clause_strictly_by_resolution", 296),
   ("br_check_clause", 312),
   ("br_check_proof", 376)]

theorem rup_compile : compileFn Amd64.isa rupFn = .ok rupCode := by kernel_rfl
theorem strict_compile : compileFn Amd64.isa strictFn = .ok strictCode := by kernel_rfl
theorem clause_compile : compileFn Amd64.isa clauseFn = .ok clauseCode := by kernel_rfl
theorem proof_compile : compileFn Amd64.isa proofFn = .ok proofCode := by kernel_rfl

theorem lrat_module_compile :
    compileModule Amd64.isa 8 [] ["lrat_fail"] 296 lratCheckFns =
      .ok (lratCheckCode, lratBounds) := by kernel_rfl

section Generic
variable [hh : Host]

/-- Linking `lratCheckFns` (`checkRup`, `strictCheck`, `checkClause`, `checkProof`) via
`compile_sound` in any x64 host that also defines `"lrat_fail"`. -/
theorem lrat_module_fnspec (k₀ : Nat)
    (hc : lratCheckCode.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (hfail : Amd64.target.Defined hh "lrat_fail") :
    ∀ p ∈ lratBounds,
      Amd64.target.Defined hh p.1 ∧
        Amd64.target.FnSpec hh p.1 (lratEnv p.1) p.2 296 :=
  compile_sound (T := Amd64.target) hh lratEnv [] ["lrat_fail"] 296 lratCheckFns
    lratCheckCode lratBounds k₀ lrat_module_compile hc hu lratCheckFns_wf lratEnv_sound
    (fun _ h => nomatch h) (fun g hg => by simp at hg; subst hg; exact hfail)

/-- Linking `lratCheckFns` against the accepting contracts `lratAcceptEnv` via `compile_sound`. -/
theorem lrat_module_accepts_fnspec (k₀ : Nat)
    (hc : lratCheckCode.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (hfail : Amd64.target.Defined hh "lrat_fail") :
    ∀ p ∈ lratBounds,
      Amd64.target.Defined hh p.1 ∧
        Amd64.target.FnSpec hh p.1 (lratAcceptEnv p.1) p.2 296 :=
  compile_sound (T := Amd64.target) hh lratAcceptEnv [] ["lrat_fail"] 296 lratCheckFns
    lratCheckCode lratBounds k₀ lrat_module_compile hc hu lratCheckFns_wf lratAcceptEnv_sound
    (fun _ h => nomatch h) (fun g hg => by simp at hg; subst hg; exact hfail)

/-- End-to-end correctness of compiled `br_check_proof` on Kraken x64: in every host containing
`lratCheckCode` at `k₀` and defining `"lrat_fail"` with unique labels, from a state at
`Labels.label "br_check_proof"` meeting `CheckProofPre` for formula `cnf₀` with `st` in `rdi`,
584 bytes of stack space below `rsp`, and return address `ra` at `rsp`, execution of
`br_check_proof` either:
* returns to `ra` with `cnf₀.Unsat` established, callee-saved registers intact, `rsp` popped, and
  `FullMemInv` preserved in memory; or
* exits to `"lrat_fail"` at `Labels.label "lrat_fail"` with a 16-byte aligned entry stack pointer. -/
theorem checkProof_x64_correct (k₀ : Nat)
    (hc : lratCheckCode.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (hfail : Amd64.target.Defined hh "lrat_fail")
    {max_var n : Nat} {st_ptr : BitVec 64} {k₀_fields : KernelFields}
    {usedWords litsPtrs antePtrs trail_free0 : List Val} {cnf₀ : CNF Nat}
    {clauses : List (CNF.Clause Nat)} {litsTable anteTable : List (List Val)}
    {P_ro : Mem 64 → Prop} {m : Mem 64}
    (pre : CheckProofPre max_var n st_ptr k₀_fields usedWords litsPtrs antePtrs trail_free0 cnf₀
      clauses litsTable anteTable P_ro m)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hrdi : s.regs.get64 .rdi = st_ptr)
    (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hmem : s.dmem =⋆ Eq m ⋆
      ((fun f => ∃ bs : List UInt8, bs.length = 376 ∧ f = bs.At (s.regs.get64 .rsp - 376#64)) ⋆
        Eq (ra.toUInt64.At (s.regs.get64 .rsp))) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st =>
        (st.pc = ra ∧ cnf₀.Unsat ∧
          (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15], st.data.regs.get64 r = s.regs.get64 r) ∧
          st.data.regs.get64 .rsp = s.regs.get64 .rsp + 8#64 ∧
          ∃ m' k', FullMemInv max_var n trail_free0.length st_ptr k₀_fields P_ro k' m' ∧
            (st.data.dmem =⋆ Eq m' ⋆
              (fun f => ∃ bs : List UInt8, bs.length = 384 ∧ f = bs.At (s.regs.get64 .rsp - 376#64)) ⋆ R)) ∨
        (st.pc = Labels.label "lrat_fail" ∧ (st.data.regs.get64 .rsp + 8#64).toNat % 16 = 0))
      ⟨s, Labels.label "br_check_proof"⟩ := by
  let Q : LeanQbe.Post := fun rets m' =>
    rets = [] ∧ (∃ k', FullMemInv max_var n trail_free0.length st_ptr k₀_fields P_ro k' m') ∧ cnf₀.Unsat
  let X : XPost := fun g _ _ => g = "lrat_fail"
  have hspec : checkProofSpec [st_ptr] m Q X :=
    ⟨max_var, n, st_ptr, k₀_fields, usedWords, litsPtrs, antePtrs, trail_free0, cnf₀,
      clauses, litsTable, anteTable, P_ro, rfl, pre,
      fun _ hinv hunsat => ⟨rfl, hinv, hunsat⟩, fun _ _ => rfl⟩
  have hargs : Amd64.target.ArgsIn [st_ptr] s := by
    simp [Target.ArgsIn, Target.ValsIn, Amd64.target, Amd64.isa, hrdi]
  have hf := (lrat_module_fnspec k₀ hc hu hfail ("br_check_proof", 376) (by simp [lratBounds])).2
    [st_ptr] m Q X hspec s ra R hargs trivial hsp hmem
  refine eventually_weaken _ _ _ _ ?_ hf
  rintro st (⟨hpc, rets, m', ⟨rfl, ⟨k', hinv'⟩, hunsat⟩, -, ⟨hcs, hsp'⟩, hm'⟩ |
    ⟨sym', as', m', rfl, _, hpc, _, hspE, _⟩)
  · exact Or.inl ⟨hpc, hunsat, fun r hr => hcs r hr, hsp', m', k', hinv', hm'⟩
  · exact Or.inr ⟨hpc, hspE⟩

end Generic

/-! ## Non-vacuity: concrete host and concrete memory `nvCheckBytes` -/

def lratProg : Program := lratCheckCode ++ [.label "lrat_fail"]

abbrev lratHost : Host :=
  .ofLayout lratProg (layoutOf lratProg) (layoutOf_zero _) (of_decide_eq_true (by kernel_rfl))

attribute [local instance] lratHost

theorem lratHost_prog : Host.prog = lratProg := rfl

theorem lratHost_unique : Host.LabelsUnique :=
  Host.labelsUnique_of_nodup (of_decide_eq_true (by kernel_rfl))

def zeros376 : List UInt8 := List.replicate 376 0

def lratState0 : MachineData :=
  { regs := { rdi := 0x1000, rsp := 0x0ff8 },
    dmem := ((zeros376 ++ raBytes0) ++ nvCheckBytes).At 0x0e80#64 }

theorem checkProof_x64_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st =>
        (st.pc = 0x1234 ∧ (CNF.empty : CNF Nat).Unsat) ∨
        st.pc = Labels.label "lrat_fail")
      ⟨lratState0, Labels.label "br_check_proof"⟩ := by
  have hlen : raBytes0.length = 8 := UInt64.toBytes_length _
  have h376 : zeros376.length = 376 := List.length_replicate
  have hnv_len : nvCheckBytes.length = 210 := by
    simp [nvCheckBytes, bytesN_length, KernelFields.toList]
  have hmem : lratState0.dmem =⋆ Eq (nvCheckBytes.At 0x1000#64) ⋆
      ((fun f => ∃ bs : List UInt8, bs.length = 376 ∧ f = bs.At (lratState0.regs.get64 .rsp - 376#64)) ⋆
        Eq ((0x1234 : Int64).toUInt64.At (lratState0.regs.get64 .rsp))) ⋆
      Std.ExtHashMap.emp := by
    rw [Std.ExtHashMap.sep_emp, Std.ExtHashMap.sep_comm]
    have h1 := Mem.At_append_sep (zeros376 ++ raBytes0) nvCheckBytes 0x0e80#64
      (by simp [hlen, h376, hnv_len])
    have e1 : (0x0e80#64 + BitVec.ofNat 64 (zeros376 ++ raBytes0).length) = 0x1000#64 := by
      simp [h376, hlen]
    rw [e1] at h1
    have h2 := Mem.At_append_sep zeros376 raBytes0 0x0e80#64 (by simp [hlen, h376])
    have e2 : (0x0e80#64 + BitVec.ofNat 64 zeros376.length) = 0x0ff8#64 := by simp [h376]
    rw [e2] at h2
    have h0 : (Eq (((zeros376 ++ raBytes0) ++ nvCheckBytes).At 0x0e80#64)) lratState0.dmem := rfl
    rw [h1] at h0
    refine sep_mono (fun f hf => ?_) h0
    rw [h2] at hf
    exact sep_mono (fun f1 hf1 => ⟨zeros376, h376, hf1.symm⟩) hf
  have hc : lratCheckCode.IsInfixAt Host.prog 0 := by
    rw [lratHost_prog]; exact ⟨[.label "lrat_fail"], rfl⟩
  have hfail : Amd64.target.Defined lratHost "lrat_fail" := by
    refine ⟨lratCheckCode.length, ?_⟩
    change Host.prog[lratCheckCode.length]? = some (.label "lrat_fail")
    rw [lratHost_prog, lratProg, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  have hrdi : lratState0.regs.get64 .rdi = 0x1000#64 := rfl
  have hsp : (lratState0.regs.get64 .rsp + 8#64).toNat % 16 = 0 :=
    show (0x0ff8#64 + 8#64).toNat % 16 = 0 by decide
  have h := checkProof_x64_correct 0 hc lratHost_unique hfail nvCheck_pre
    lratState0 0x1234 Std.ExtHashMap.emp hrdi hsp hmem
  refine eventually_weaken _ _ _ _ ?_ h
  rintro st (⟨hpc, hunsat, -⟩ | ⟨hpc, -⟩)
  · exact Or.inl ⟨hpc, hunsat⟩
  · exact Or.inr hpc

/-! ## Accepting UNSAT instance: concrete bytes `nvAcceptBytes` (`[[1], [-1]]`), normal return -/

def lratAcceptState0 : MachineData :=
  { regs := { rdi := 0x1000, rsp := 0x0ff8 },
    dmem := ((zeros376 ++ raBytes0) ++ nvAcceptBytes).At 0x0e80#64 }

/-- Concrete accepting execution of compiled `br_check_proof` on Kraken x64: on the 2-clause
unsatisfiable formula `nvAcceptCnf` (`(x₁) ∧ (¬x₁)`) and 1-step LRAT resolution proof encoded in
`nvAcceptBytes` (which satisfies `CheckProofPre` by `nvAccept_pre`), execution from
`Labels.label "br_check_proof"` returns normally to `ra = 0x1234` (with exit postcondition `False`)
and establishes `nvAcceptCnf.Unsat`. -/
theorem checkProof_x64_accepts :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧ nvAcceptCnf.Unsat)
      ⟨lratAcceptState0, Labels.label "br_check_proof"⟩ := by
  have hlen : raBytes0.length = 8 := UInt64.toBytes_length _
  have h376 : zeros376.length = 376 := List.length_replicate
  have hnv_len : nvAcceptBytes.length = 274 := nvAcceptBytes_length
  have hmem : lratAcceptState0.dmem =⋆ Eq (nvAcceptBytes.At 0x1000#64) ⋆
      ((fun f => ∃ bs : List UInt8, bs.length = 376 ∧ f = bs.At (lratAcceptState0.regs.get64 .rsp - 376#64)) ⋆
        Eq ((0x1234 : Int64).toUInt64.At (lratAcceptState0.regs.get64 .rsp))) ⋆
      Std.ExtHashMap.emp := by
    rw [Std.ExtHashMap.sep_emp, Std.ExtHashMap.sep_comm]
    have h1 := Mem.At_append_sep (zeros376 ++ raBytes0) nvAcceptBytes 0x0e80#64
      (by simp [hlen, h376, hnv_len])
    have e1 : (0x0e80#64 + BitVec.ofNat 64 (zeros376 ++ raBytes0).length) = 0x1000#64 := by
      simp [h376, hlen]
    rw [e1] at h1
    have h2 := Mem.At_append_sep zeros376 raBytes0 0x0e80#64 (by simp [hlen, h376])
    have e2 : (0x0e80#64 + BitVec.ofNat 64 zeros376.length) = 0x0ff8#64 := by simp [h376]
    rw [e2] at h2
    have h0 : (Eq (((zeros376 ++ raBytes0) ++ nvAcceptBytes).At 0x0e80#64)) lratAcceptState0.dmem := rfl
    rw [h1] at h0
    refine sep_mono (fun f hf => ?_) h0
    rw [h2] at hf
    exact sep_mono (fun f1 hf1 => ⟨zeros376, h376, hf1.symm⟩) hf
  have hc : lratCheckCode.IsInfixAt Host.prog 0 := by
    rw [lratHost_prog]; exact ⟨[.label "lrat_fail"], rfl⟩
  have hfail : Amd64.target.Defined lratHost "lrat_fail" := by
    refine ⟨lratCheckCode.length, ?_⟩
    change Host.prog[lratCheckCode.length]? = some (.label "lrat_fail")
    rw [lratHost_prog, lratProg, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  have hrdi : lratAcceptState0.regs.get64 .rdi = 0x1000#64 := rfl
  have hargs : Amd64.target.ArgsIn [0x1000#64] lratAcceptState0 := by
    simp [Target.ArgsIn, Target.ValsIn, Amd64.target, Amd64.isa, hrdi]
  have hsp : (lratAcceptState0.regs.get64 .rsp + 8#64).toNat % 16 = 0 :=
    show (0x0ff8#64 + 8#64).toNat % 16 = 0 by decide
  have hspec : lratAcceptEnv ("br_check_proof", 376).1 [0x1000#64] (nvAcceptBytes.At 0x1000#64)
      (fun rs m' => rs = [] ∧ nvAcceptMem nvAcceptK2 Std.ExtHashMap.emp m' ∧ nvAcceptCnf.Unsat)
      (fun _ _ _ => False) := by
    simpa [lratAcceptEnv] using checkProof_accepts_nonvacuous
  have hf := (lrat_module_accepts_fnspec 0 hc lratHost_unique hfail
      ("br_check_proof", 376) (by simp [lratBounds])).2
    [0x1000#64] (nvAcceptBytes.At 0x1000#64) _ _ hspec
    lratAcceptState0 0x1234 Std.ExtHashMap.emp hargs trivial hsp hmem
  refine eventually_weaken _ _ _ _ ?_ hf
  rintro st (⟨hpc, _, _, ⟨_, _, hunsat⟩, -⟩ | ⟨_, _, _, hx, _⟩)
  · exact ⟨hpc, hunsat⟩
  · exact hx.elim

end LeanQbe.Litmus
