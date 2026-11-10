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

open Lean Elab Tactic Meta in
elab "kernel_rfl" : tactic => do
  let goal ← getMainGoal
  let tgt ← instantiateMVars (← goal.getType)
  let some (α, lhs, _) := tgt.eq?
    | throwError "kernel_rfl: goal is not an equality{indentExpr tgt}"
  let u ← getLevel α
  goal.assign (mkApp2 (mkConst ``Eq.refl [u]) α lhs)
  replaceMainGoal []

@[expose] public section

namespace LeanQbe.Litmus

open LeanQbe LeanQbe.LratRup LeanQbe.LratTrim Rega Amd64
open Std.Sat Std.Tactic.BVDecide.LRAT.Internal Kraken.Bedrock2.Test

abbrev rupFn : Fn := ⟨"br_check_clause_non_strictly_by_propagation", LratRup.checkRup⟩
abbrev strictFn : Fn := ⟨"br_check_clause_strictly_by_resolution", strictCheck⟩
abbrev clauseFn : Fn := ⟨"br_check_clause", checkClause⟩
abbrev proofFn : Fn := ⟨"br_check_proof", checkProof⟩

def rupCode : Program := parse("br_check_clause_non_strictly_by_propagation:
  subq $472, %rsp
  movq %rdi, %r11
  movq $16, %r10
  addq %r10, %r11
  movq %r11, %rax
  movq (%rax), %rax
  movq %rdi, %r11
  movq $24, %r10
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
  movq %rdi, %r11
  movq $144, %r10
  addq %r10, %r11
  movq %r11, %r8
  movq %r8, 48(%rsp)
  movq (%r8), %r8
  movq %r8, 56(%rsp)
  movq %r8, %r11
  movq $1, %r10
  addq %r10, %r11
  movq %r11, %r8
  movq %r8, 64(%rsp)
  movq %rdi, %r11
  movq $152, %r10
  addq %r10, %r11
  movq %r11, %rdi
  movq (%rdi), %r8
  movq %r8, 72(%rsp)
  movq 40(%rsp), %r8
  movq 72(%rsp), %r9
  jmp br_check_clause_non_strictly_by_propagation.L3
  br_check_clause_non_strictly_by_propagation.L3:
  movq %r8, 80(%rsp)
  movq %r9, 88(%rsp)
  movslq (%rdx), %r8
  movq %r8, 96(%rsp)
  testl %r8d, %r8d
  jne br_check_clause_non_strictly_by_propagation.L4
  movq 80(%rsp), %rdx
  movq %r9, %r8
  jmp br_check_clause_non_strictly_by_propagation.L2
  br_check_clause_non_strictly_by_propagation.L4:
  movq 96(%rsp), %r8
  movq %r8, %r11
  movq %rcx, %r10
  movq $63, %rcx
  sarq %cl, %r11
  movq %r10, %rcx
  movq %r11, %r8
  movq %r8, 104(%rsp)
  movq 96(%rsp), %r9
  movq %r9, %r11
  movq %r8, %r10
  xorq %r10, %r11
  movq %r11, %r8
  movq %r8, 112(%rsp)
  movq 104(%rsp), %r9
  movq %r8, %r11
  movq %r9, %r10
  subq %r10, %r11
  movq %r11, %r8
  movq %r8, 120(%rsp)
  movq 8(%rsp), %r9
  movq %r9, %r11
  movq %r8, %r10
  addq %r10, %r11
  movq %r11, %r8
  movq %r8, 128(%rsp)
  movsbq (%r8), %r8
  movq %r8, 136(%rsp)
  movq 104(%rsp), %r9
  movq %r8, %r11
  movq %r9, %r10
  xorq %r10, %r11
  movq %r11, %r8
  movq %r8, 144(%rsp)
  movq 104(%rsp), %r9
  movq %r8, %r11
  movq %r9, %r10
  subq %r10, %r11
  movq %r11, %r8
  movq %r8, 152(%rsp)
  movq %rdx, %r11
  movq $4, %r10
  addq %r10, %r11
  movq %r11, %rdx
  movq 152(%rsp), %r8
  movq %r8, %r11
  movq $0, %r10
  cmpq %r10, %r11
  setl %r11b
  movzx %r11b, %r8d
  movq %r8, 160(%rsp)
  testl %r8d, %r8d
  jne br_check_clause_non_strictly_by_propagation.L5
  movq 152(%rsp), %r8
  movq $0, %r11
  movq %r8, %r10
  cmpq %r10, %r11
  setl %r11b
  movzx %r11b, %r8d
  movq %r8, 168(%rsp)
  testl %r8d, %r8d
  jne br_check_clause_non_strictly_by_propagation.L6
  movq 96(%rsp), %r8
  movq $0, %r11
  movq %r8, %r10
  subq %r10, %r11
  movq %r11, %r8
  movq %r8, 176(%rsp)
  movq %r8, %r11
  movq %rcx, %r10
  movq $63, %rcx
  sarq %cl, %r11
  movq %r10, %rcx
  movq %r11, %r8
  movq %r8, 184(%rsp)
  movq %r8, %r11
  movq $1, %r10
  orq %r10, %r11
  movq %r11, %r8
  movq %r8, 192(%rsp)
  movq 128(%rsp), %r9
  movq %r8, %r11
  movb %r11b, (%r9)
  movq 176(%rsp), %r8
  movq 80(%rsp), %r9
  movq %r8, %r11
  movl %r11d, (%r9)
  movq 80(%rsp), %r8
  movq %r8, %r11
  movq $4, %r10
  addq %r10, %r11
  movq %r11, %r8
  movq %r8, 200(%rsp)
  movq 88(%rsp), %r8
  movq %r8, %r11
  movq $1, %r10
  addq %r10, %r11
  movq %r11, %r8
  movq %r8, 208(%rsp)
  movq 200(%rsp), %r8
  movq 208(%rsp), %r9
  jmp br_check_clause_non_strictly_by_propagation.L3
  br_check_clause_non_strictly_by_propagation.L6:
  movq 80(%rsp), %rax
  movq 64(%rsp), %rcx
  movq 88(%rsp), %rdx
  jmp br_check_clause_non_strictly_by_propagation.L1
  br_check_clause_non_strictly_by_propagation.L5:
  movq 80(%rsp), %r8
  movq 88(%rsp), %r9
  jmp br_check_clause_non_strictly_by_propagation.L3
  br_check_clause_non_strictly_by_propagation.L2:
  movq %r8, 216(%rsp)
  movq 64(%rsp), %r8
  movq 216(%rsp), %r9
  jmp br_check_clause_non_strictly_by_propagation.L7
  br_check_clause_non_strictly_by_propagation.L7:
  movq %rcx, 224(%rsp)
  movq %r9, 232(%rsp)
  movslq (%rcx), %rcx
  movq %rcx, 240(%rsp)
  testl %ecx, %ecx
  jne br_check_clause_non_strictly_by_propagation.L8
  movq $3, %rax
  movq $0, %rcx
  jmp br_check_clause_non_strictly_by_propagation.L0
  br_check_clause_non_strictly_by_propagation.L8:
  movq 240(%rsp), %rcx
  movq %rcx, %r11
  movq $0, %r10
  cmpq %r10, %r11
  setl %r11b
  movzx %r11b, %ecx
  movq %rcx, 248(%rsp)
  testl %ecx, %ecx
  jne br_check_clause_non_strictly_by_propagation.L9
  movq 240(%rsp), %rcx
  movq %rcx, %r11
  movq %rcx, %r10
  movq $3, %rcx
  shlq %cl, %r11
  movq %r10, %rcx
  movq %r11, %rcx
  movq %rcx, 256(%rsp)
  movq %rax, %r11
  movq %rcx, %r10
  addq %r10, %r11
  movq %r11, %rcx
  movq %rcx, 264(%rsp)
  movq (%rcx), %rcx
  movq %rcx, 272(%rsp)
  movq %r8, %r11
  movq $1, %r10
  addq %r10, %r11
  movq %r11, %rcx
  movq %rcx, 280(%rsp)
  movq 272(%rsp), %rcx
  movq %rdx, %r8
  movq $0, %rdx
  jmp br_check_clause_non_strictly_by_propagation.L11
  br_check_clause_non_strictly_by_propagation.L11:
  movq %r8, 288(%rsp)
  movq %r9, 296(%rsp)
  movslq (%rcx), %r8
  movq %r8, 304(%rsp)
  testl %r8d, %r8d
  jne br_check_clause_non_strictly_by_propagation.L12
  movq %rdx, %rcx
  movq 288(%rsp), %rdx
  movq %r9, %r8
  jmp br_check_clause_non_strictly_by_propagation.L10
  br_check_clause_non_strictly_by_propagation.L12:
  movq 304(%rsp), %r8
  movq %r8, %r11
  movq %rcx, %r10
  movq $63, %rcx
  sarq %cl, %r11
  movq %r10, %rcx
  movq %r11, %r8
  movq %r8, 312(%rsp)
  movq 304(%rsp), %r9
  movq %r9, %r11
  movq %r8, %r10
  xorq %r10, %r11
  movq %r11, %r8
  movq %r8, 320(%rsp)
  movq 312(%rsp), %r9
  movq %r8, %r11
  movq %r9, %r10
  subq %r10, %r11
  movq %r11, %r8
  movq %r8, 328(%rsp)
  movq 8(%rsp), %r9
  movq %r9, %r11
  movq %r8, %r10
  addq %r10, %r11
  movq %r11, %r8
  movq %r8, 336(%rsp)
  movsbq (%r8), %r8
  movq %r8, 344(%rsp)
  movq 312(%rsp), %r9
  movq %r8, %r11
  movq %r9, %r10
  xorq %r10, %r11
  movq %r11, %r8
  movq %r8, 352(%rsp)
  movq 312(%rsp), %r9
  movq %r8, %r11
  movq %r9, %r10
  subq %r10, %r11
  movq %r11, %r8
  movq %r8, 360(%rsp)
  movq %rcx, %r11
  movq $4, %r10
  addq %r10, %r11
  movq %r11, %rcx
  movq 360(%rsp), %r8
  movq %r8, %r11
  movq $0, %r10
  cmpq %r10, %r11
  setl %r11b
  movzx %r11b, %r8d
  movq %r8, 368(%rsp)
  testl %r8d, %r8d
  jne br_check_clause_non_strictly_by_propagation.L13
  testl %edx, %edx
  jne br_check_clause_non_strictly_by_propagation.L15
  jmp br_check_clause_non_strictly_by_propagation.L14
  br_check_clause_non_strictly_by_propagation.L15:
  movq 304(%rsp), %r8
  movq %rdx, %r11
  movq %r8, %r10
  cmpq %r10, %r11
  sete %r11b
  movzx %r11b, %edx
  testl %edx, %edx
  jne br_check_clause_non_strictly_by_propagation.L16
  movq 240(%rsp), %rcx
  movq 288(%rsp), %rdx
  movq 280(%rsp), %r8
  movq 296(%rsp), %r9
  movq $2, %rax
  jmp br_check_clause_non_strictly_by_propagation.L0
  br_check_clause_non_strictly_by_propagation.L16:
  jmp br_check_clause_non_strictly_by_propagation.L14
  br_check_clause_non_strictly_by_propagation.L14:
  movq 360(%rsp), %rdx
  movq %rdx, %r11
  movq $0, %r10
  cmpq %r10, %r11
  sete %r11b
  movzx %r11b, %edx
  testl %edx, %edx
  jne br_check_clause_non_strictly_by_propagation.L17
  movq 304(%rsp), %rdx
  movq 288(%rsp), %r8
  movq 296(%rsp), %r9
  jmp br_check_clause_non_strictly_by_propagation.L11
  br_check_clause_non_strictly_by_propagation.L17:
  movq 312(%rsp), %rdx
  movq %rdx, %r11
  movq $1, %r10
  orq %r10, %r11
  movq %r11, %rdx
  movq 336(%rsp), %r8
  movq %rdx, %r11
  movb %r11b, (%r8)
  movq 304(%rsp), %rdx
  movq 288(%rsp), %r8
  movq %rdx, %r11
  movl %r11d, (%r8)
  movq 288(%rsp), %rdx
  movq %rdx, %r11
  movq $4, %r10
  addq %r10, %r11
  movq %r11, %rdx
  movq 296(%rsp), %r8
  movq %r8, %r11
  movq $1, %r10
  addq %r10, %r11
  movq %r11, %r8
  movq %r8, 376(%rsp)
  movq %rdx, %r8
  movq 304(%rsp), %rdx
  movq 376(%rsp), %r9
  jmp br_check_clause_non_strictly_by_propagation.L11
  br_check_clause_non_strictly_by_propagation.L13:
  movq 304(%rsp), %r8
  movq $0, %r11
  movq %r8, %r10
  subq %r10, %r11
  movq %r11, %r8
  movq %r8, 384(%rsp)
  movq %rdx, %r11
  movq %r8, %r10
  cmpq %r10, %r11
  sete %r11b
  movzx %r11b, %r8d
  movq %r8, 392(%rsp)
  testl %r8d, %r8d
  jne br_check_clause_non_strictly_by_propagation.L18
  movq 288(%rsp), %r8
  movq 296(%rsp), %r9
  jmp br_check_clause_non_strictly_by_propagation.L11
  br_check_clause_non_strictly_by_propagation.L18:
  movq 240(%rsp), %rcx
  movq 288(%rsp), %rdx
  movq 280(%rsp), %r8
  movq 296(%rsp), %r9
  movq $2, %rax
  jmp br_check_clause_non_strictly_by_propagation.L0
  br_check_clause_non_strictly_by_propagation.L10:
  movq %r8, 400(%rsp)
  testl %ecx, %ecx
  jne br_check_clause_non_strictly_by_propagation.L19
  movq %rdx, %rax
  movq 280(%rsp), %rcx
  movq %r8, %rdx
  jmp br_check_clause_non_strictly_by_propagation.L1
  br_check_clause_non_strictly_by_propagation.L19:
  movq 224(%rsp), %rcx
  movq %rcx, %r11
  movq $4, %r10
  addq %r10, %r11
  movq %r11, %rcx
  movq 280(%rsp), %r8
  movq 400(%rsp), %r9
  jmp br_check_clause_non_strictly_by_propagation.L7
  br_check_clause_non_strictly_by_propagation.L9:
  movq 240(%rsp), %rcx
  movq $1, %rax
  jmp br_check_clause_non_strictly_by_propagation.L0
  br_check_clause_non_strictly_by_propagation.L1:
  movq 24(%rsp), %rsi
  jmp br_check_clause_non_strictly_by_propagation.L20
  br_check_clause_non_strictly_by_propagation.L20:
  movq %rsi, %r11
  movq %rax, %r10
  cmpq %r10, %r11
  sete %r11b
  movzx %r11b, %r8d
  movq %r8, 408(%rsp)
  testl %r8d, %r8d
  jne br_check_clause_non_strictly_by_propagation.L21
  movslq (%rsi), %r8
  movq %r8, 416(%rsp)
  movq %r8, %r11
  movq %rcx, %r10
  movq $63, %rcx
  sarq %cl, %r11
  movq %r10, %rcx
  movq %r11, %r8
  movq %r8, 424(%rsp)
  movq 416(%rsp), %r9
  movq %r9, %r11
  movq %r8, %r10
  xorq %r10, %r11
  movq %r11, %r8
  movq %r8, 432(%rsp)
  movq 424(%rsp), %r9
  movq %r8, %r11
  movq %r9, %r10
  subq %r10, %r11
  movq %r11, %r8
  movq %r8, 440(%rsp)
  movq 8(%rsp), %r9
  movq %r9, %r11
  movq %r8, %r10
  addq %r10, %r11
  movq %r11, %r8
  movq %r8, 448(%rsp)
  movq $0, %r11
  movb %r11b, (%r8)
  movq %rsi, %r11
  movq $4, %r10
  addq %r10, %r11
  movq %r11, %rsi
  jmp br_check_clause_non_strictly_by_propagation.L20
  br_check_clause_non_strictly_by_propagation.L21:
  movq 24(%rsp), %rax
  movq 32(%rsp), %rsi
  movq %rax, %r11
  movq %r11, (%rsi)
  movq 48(%rsp), %rax
  movq %rcx, %r11
  movq %r11, (%rax)
  movq %rdx, %r11
  movq %r11, (%rdi)
  addq $472, %rsp
  ret
  br_check_clause_non_strictly_by_propagation.L0:
  movq %r8, 456(%rsp)
  movq %r9, 464(%rsp)
  movq 32(%rsp), %r8
  movq %rdx, %r11
  movq %r11, (%r8)
  movq 456(%rsp), %rdx
  movq 48(%rsp), %r8
  movq %rdx, %r11
  movq %r11, (%r8)
  movq 464(%rsp), %rdx
  movq %rdx, %r11
  movq %r11, (%rdi)
  movq %rax, %rdi
  movq %rcx, %rdx
  movq $0, %rcx
  movq $0, %r8
  addq $472, %rsp
  jmp lrat_fail")

def strictCode : Program := parse("br_check_clause_strictly_by_resolution:
  subq $296, %rsp
  movq %rcx, %rax
  jmp br_check_clause_strictly_by_resolution.L1
  br_check_clause_strictly_by_resolution.L1:
  movslq (%rax), %r8
  movq %r8, (%rsp)
  testl %r8d, %r8d
  jne br_check_clause_strictly_by_resolution.L2
  jmp br_check_clause_strictly_by_resolution.L0
  br_check_clause_strictly_by_resolution.L2:
  movq (%rsp), %r8
  movq %r8, %r11
  movq $0, %r10
  cmpq %r10, %r11
  setl %r11b
  movzx %r11b, %r8d
  movq %r8, 8(%rsp)
  testl %r8d, %r8d
  jne br_check_clause_strictly_by_resolution.L3
  movq %rax, %r11
  movq $4, %r10
  addq %r10, %r11
  movq %r11, %rax
  jmp br_check_clause_strictly_by_resolution.L1
  br_check_clause_strictly_by_resolution.L3:
  movq (%rsp), %rdx
  movq $1, %rdi
  movq $0, %rcx
  movq $0, %r8
  addq $296, %rsp
  jmp lrat_fail
  br_check_clause_strictly_by_resolution.L0:
  movq %rdi, %r11
  movq $16, %r10
  addq %r10, %r11
  movq %r11, %r8
  movq %r8, 16(%rsp)
  movq (%r8), %r8
  movq %r8, 24(%rsp)
  movq %rdi, %r11
  movq $32, %r10
  addq %r10, %r11
  movq %r11, %r8
  movq %r8, 32(%rsp)
  movq (%r8), %r8
  movq %r8, 40(%rsp)
  movq %rdi, %r11
  movq $144, %r10
  addq %r10, %r11
  movq %r11, %rdi
  movq %rdi, 48(%rsp)
  movq (%rdi), %rdi
  movq $0, %r8
  movq $1, %r9
  jmp br_check_clause_strictly_by_resolution.L5
  br_check_clause_strictly_by_resolution.L5:
  movq %r8, 56(%rsp)
  movq %r9, 64(%rsp)
  movq %rax, %r11
  movq %rcx, %r10
  cmpq %r10, %r11
  sete %r11b
  movzx %r11b, %r8d
  movq %r8, 72(%rsp)
  testl %r8d, %r8d
  jne br_check_clause_strictly_by_resolution.L6
  movq %rax, %r11
  movq $4, %r10
  subq %r10, %r11
  movq %r11, %rax
  movslq (%rax), %r8
  movq %r8, 80(%rsp)
  movq %r8, %r11
  movq %rcx, %r10
  movq $3, %rcx
  shlq %cl, %r11
  movq %r10, %rcx
  movq %r11, %r8
  movq %r8, 88(%rsp)
  movq 24(%rsp), %r9
  movq %r9, %r11
  movq %r8, %r10
  addq %r10, %r11
  movq %r11, %r8
  movq %r8, 96(%rsp)
  movq (%r8), %r8
  movq %r8, 104(%rsp)
  movq %rdi, %r11
  movq $1, %r10
  addq %r10, %r11
  movq %r11, %rdi
  movq %rdi, 112(%rsp)
  movq %r8, %rdi
  movq 56(%rsp), %r9
  movq $0, %r8
  jmp br_check_clause_strictly_by_resolution.L8
  br_check_clause_strictly_by_resolution.L8:
  movq %r8, 120(%rsp)
  movq %r9, 128(%rsp)
  movslq (%rdi), %r8
  movq %r8, 136(%rsp)
  testl %r8d, %r8d
  jne br_check_clause_strictly_by_resolution.L9
  movq 120(%rsp), %rdi
  movq %r9, %r8
  jmp br_check_clause_strictly_by_resolution.L7
  br_check_clause_strictly_by_resolution.L9:
  movq 136(%rsp), %r8
  movq %r8, %r11
  movq %rcx, %r10
  movq $63, %rcx
  sarq %cl, %r11
  movq %r10, %rcx
  movq %r11, %r8
  movq %r8, 144(%rsp)
  movq 136(%rsp), %r9
  movq %r9, %r11
  movq %r8, %r10
  xorq %r10, %r11
  movq %r11, %r8
  movq %r8, 152(%rsp)
  movq 144(%rsp), %r9
  movq %r8, %r11
  movq %r9, %r10
  subq %r10, %r11
  movq %r11, %r8
  movq %r8, 160(%rsp)
  movq 40(%rsp), %r9
  movq %r9, %r11
  movq %r8, %r10
  addq %r10, %r11
  movq %r11, %r8
  movq %r8, 168(%rsp)
  movsbq (%r8), %r8
  movq %r8, 176(%rsp)
  movq %rdi, %r11
  movq $4, %r10
  addq %r10, %r11
  movq %r11, %rdi
  movq 176(%rsp), %r8
  movq %r8, %r11
  movq $0, %r10
  cmpq %r10, %r11
  sete %r11b
  movzx %r11b, %r8d
  movq %r8, 184(%rsp)
  testl %r8d, %r8d
  jne br_check_clause_strictly_by_resolution.L10
  movq 176(%rsp), %r8
  movq 144(%rsp), %r9
  movq %r8, %r11
  movq %r9, %r10
  xorq %r10, %r11
  movq %r11, %r8
  movq %r8, 192(%rsp)
  movq 144(%rsp), %r9
  movq %r8, %r11
  movq %r9, %r10
  subq %r10, %r11
  movq %r11, %r8
  movq %r8, 200(%rsp)
  movq $0, %r11
  movq %r8, %r10
  cmpq %r10, %r11
  setl %r11b
  movzx %r11b, %r8d
  movq %r8, 208(%rsp)
  testl %r8d, %r8d
  jne br_check_clause_strictly_by_resolution.L11
  movq 120(%rsp), %r8
  testl %r8d, %r8d
  jne br_check_clause_strictly_by_resolution.L12
  movq 136(%rsp), %r8
  movq 128(%rsp), %r9
  jmp br_check_clause_strictly_by_resolution.L8
  br_check_clause_strictly_by_resolution.L12:
  movq 112(%rsp), %rax
  movq 48(%rsp), %rcx
  movq %rax, %r11
  movq %r11, (%rcx)
  movq %r8, %rdx
  movq 136(%rsp), %rcx
  movq 80(%rsp), %r8
  movq $4, %rdi
  addq $296, %rsp
  jmp lrat_fail
  br_check_clause_strictly_by_resolution.L11:
  movq 120(%rsp), %r8
  movq 128(%rsp), %r9
  jmp br_check_clause_strictly_by_resolution.L8
  br_check_clause_strictly_by_resolution.L10:
  movq 144(%rsp), %r8
  movq %r8, %r11
  movq $1, %r10
  orq %r10, %r11
  movq %r11, %r8
  movq %r8, 216(%rsp)
  movq 168(%rsp), %r9
  movq %r8, %r11
  movb %r11b, (%r9)
  movq 128(%rsp), %r8
  movq %r8, %r11
  movq $1, %r10
  addq %r10, %r11
  movq %r11, %r8
  movq %r8, 224(%rsp)
  movq 120(%rsp), %r8
  movq 224(%rsp), %r9
  jmp br_check_clause_strictly_by_resolution.L8
  br_check_clause_strictly_by_resolution.L7:
  movq %r8, 232(%rsp)
  movq 64(%rsp), %r8
  testl %r8d, %r8d
  jne br_check_clause_strictly_by_resolution.L13
  testl %edi, %edi
  jne br_check_clause_strictly_by_resolution.L14
  movq 112(%rsp), %rax
  movq 48(%rsp), %rcx
  movq %rax, %r11
  movq %r11, (%rcx)
  movq 80(%rsp), %rdx
  movq $5, %rdi
  movq $0, %rcx
  movq $0, %r8
  addq $296, %rsp
  jmp lrat_fail
  br_check_clause_strictly_by_resolution.L14:
  movq %rdi, %r11
  movq %rcx, %r10
  movq $63, %rcx
  sarq %cl, %r11
  movq %r10, %rcx
  movq %r11, %r8
  movq %r8, 240(%rsp)
  movq %rdi, %r11
  movq %r8, %r10
  xorq %r10, %r11
  movq %r11, %rdi
  movq 240(%rsp), %r8
  movq %rdi, %r11
  movq %r8, %r10
  subq %r10, %r11
  movq %r11, %rdi
  movq 40(%rsp), %r8
  movq %r8, %r11
  movq %rdi, %r10
  addq %r10, %r11
  movq %r11, %rdi
  movq $0, %r11
  movb %r11b, (%rdi)
  movq 232(%rsp), %rdi
  movq %rdi, %r11
  movq $1, %r10
  subq %r10, %r11
  movq %r11, %rdi
  movq %rdi, %r8
  movq 112(%rsp), %rdi
  movq 64(%rsp), %r9
  jmp br_check_clause_strictly_by_resolution.L5
  br_check_clause_strictly_by_resolution.L13:
  testl %edi, %edi
  jne br_check_clause_strictly_by_resolution.L15
  movq 112(%rsp), %rdi
  movq 232(%rsp), %r8
  movq $0, %r9
  jmp br_check_clause_strictly_by_resolution.L5
  br_check_clause_strictly_by_resolution.L15:
  movq 112(%rsp), %rax
  movq 48(%rsp), %rcx
  movq %rax, %r11
  movq %r11, (%rcx)
  movq $0, %r11
  movq %rdi, %r10
  subq %r10, %r11
  movq %r11, %rax
  movq %rax, %rdx
  movq %rdi, %rcx
  movq 80(%rsp), %r8
  movq $4, %rdi
  addq $296, %rsp
  jmp lrat_fail
  br_check_clause_strictly_by_resolution.L6:
  movq %rdi, %rax
  movq 56(%rsp), %rcx
  movq %r9, %rdi
  jmp br_check_clause_strictly_by_resolution.L4
  br_check_clause_strictly_by_resolution.L4:
  movq 48(%rsp), %r8
  movq %rax, %r11
  movq %r11, (%r8)
  testl %edi, %edi
  jne br_check_clause_strictly_by_resolution.L16
  movq %rdx, %rax
  jmp br_check_clause_strictly_by_resolution.L18
  br_check_clause_strictly_by_resolution.L18:
  movslq (%rax), %rdx
  testl %edx, %edx
  jne br_check_clause_strictly_by_resolution.L19
  movq %rcx, %rax
  jmp br_check_clause_strictly_by_resolution.L17
  br_check_clause_strictly_by_resolution.L19:
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
  movq %r8, 248(%rsp)
  movq %r8, %r11
  movq %rdi, %r10
  subq %r10, %r11
  movq %r11, %r8
  movq %r8, 256(%rsp)
  movq 40(%rsp), %r9
  movq %r9, %r11
  movq %r8, %r10
  addq %r10, %r11
  movq %r11, %r8
  movq %r8, 264(%rsp)
  movsbq (%r8), %r8
  movq %r8, 272(%rsp)
  movq %r8, %r11
  movq $0, %r10
  cmpq %r10, %r11
  sete %r11b
  movzx %r11b, %r8d
  movq %r8, 280(%rsp)
  testl %r8d, %r8d
  jne br_check_clause_strictly_by_resolution.L20
  movq 272(%rsp), %r8
  movq %r8, %r11
  movq %rdi, %r10
  xorq %r10, %r11
  movq %r11, %r8
  movq %r8, 288(%rsp)
  movq %r8, %r11
  movq %rdi, %r10
  subq %r10, %r11
  movq %r11, %rdi
  movq %rdi, %r11
  movq $0, %r10
  cmpq %r10, %r11
  setl %r11b
  movzx %r11b, %edi
  testl %edi, %edi
  jne br_check_clause_strictly_by_resolution.L21
  movq 264(%rsp), %rdx
  movq $0, %r11
  movb %r11b, (%rdx)
  movq %rcx, %r11
  movq $1, %r10
  subq %r10, %r11
  movq %r11, %rcx
  movq %rax, %r11
  movq $4, %r10
  addq %r10, %r11
  movq %r11, %rax
  jmp br_check_clause_strictly_by_resolution.L18
  br_check_clause_strictly_by_resolution.L21:
  movq $7, %rdi
  movq $0, %rcx
  movq $0, %r8
  addq $296, %rsp
  jmp lrat_fail
  br_check_clause_strictly_by_resolution.L20:
  movq $6, %rdi
  movq $0, %rcx
  movq $0, %r8
  addq $296, %rsp
  jmp lrat_fail
  br_check_clause_strictly_by_resolution.L17:
  movq %rax, %r11
  movq $0, %r10
  cmpq %r10, %r11
  setne %r11b
  movzx %r11b, %ecx
  testl %ecx, %ecx
  jne br_check_clause_strictly_by_resolution.L22
  addq $296, %rsp
  ret
  br_check_clause_strictly_by_resolution.L22:
  movq %rax, %rdx
  movq $8, %rdi
  movq $0, %rcx
  movq $0, %r8
  addq $296, %rsp
  jmp lrat_fail
  br_check_clause_strictly_by_resolution.L16:
  movq $3, %rdi
  movq $0, %rdx
  movq $0, %rcx
  movq $0, %r8
  addq $296, %rsp
  jmp lrat_fail")

def clauseCode : Program := parse("br_check_clause:
  subq $40, %rsp
  movq %rdi, %r11
  movq $128, %r10
  addq %r10, %r11
  movq %r11, %rax
  movq (%rax), %r8
  movq %r8, (%rsp)
  movq %r8, %r11
  movq $1, %r10
  addq %r10, %r11
  movq %r11, %r8
  movq %r8, 8(%rsp)
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
  movq %r8, 16(%rsp)
  movq %r8, %r11
  movq $1, %r10
  addq %r10, %r11
  movq %r11, %r8
  movq %r8, 24(%rsp)
  movq %r8, %r11
  movq %r11, (%rax)
  jmp br_check_clause.L0
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
  addq $40, %rsp
  ret
  br_check_clause.L2:
  call br_check_clause_strictly_by_resolution
  addq $40, %rsp
  ret")

def proofCode : Program := parse("br_check_proof:
  subq $56, %rsp
  movq %rdi, (%rsp)
  movq %rdi, %r11
  movq $96, %r10
  addq %r10, %r11
  movq %r11, %rax
  movq (%rax), %rax
  movq (%rsp), %rcx
  movq %rcx, %r11
  movq $104, %r10
  addq %r10, %r11
  movq %r11, %rcx
  movq (%rcx), %rcx
  movq (%rsp), %rdx
  movq %rdx, %r11
  movq $64, %r10
  addq %r10, %r11
  movq %r11, %rdx
  movslq (%rdx), %rdx
  movq %rdx, 8(%rsp)
  movq (%rsp), %rdx
  movq %rdx, %r11
  movq $72, %r10
  addq %r10, %r11
  movq %r11, %rdx
  movslq (%rdx), %rdx
  movq %rax, %r11
  movq $0, %r10
  cmpq %r10, %r11
  setne %r11b
  movzx %r11b, %eax
  testl %eax, %eax
  jne br_check_proof.L0
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
  addq $56, %rsp
  ret
  br_check_proof.L1:
  movq 8(%rsp), %rax
  testl %eax, %eax
  jne br_check_proof.L2
  addq $56, %rsp
  ret
  br_check_proof.L2:
  testl %edx, %edx
  jne br_check_proof.L3
  addq $56, %rsp
  ret
  br_check_proof.L3:
  movq (%rsp), %rax
  movq %rax, %r11
  movq $88, %r10
  addq %r10, %r11
  movq %r11, %rax
  movq (%rax), %rax
  movq %rax, 16(%rsp)
  movq (%rsp), %rax
  movq (%rax), %rax
  movq %rax, 24(%rsp)
  movq (%rsp), %rax
  movq %rax, %r11
  movq $16, %r10
  addq %r10, %r11
  movq %r11, %rax
  movq (%rax), %rax
  movq %rax, 32(%rsp)
  movq (%rsp), %rax
  movq %rax, %r11
  movq $8, %r10
  addq %r10, %r11
  movq %r11, %rax
  movq (%rax), %rax
  movq %rax, 40(%rsp)
  movq %rdx, %rax
  jmp br_check_proof.L4
  br_check_proof.L4:
  movq %rax, 48(%rsp)
  movq 8(%rsp), %rcx
  movq %rcx, %r11
  movq %rax, %r10
  cmpq %r10, %r11
  setl %r11b
  movzx %r11b, %eax
  testl %eax, %eax
  jne br_check_proof.L5
  movq 16(%rsp), %rax
  movq %rax, %r11
  movq $0, %r10
  cmpq %r10, %r11
  setne %r11b
  movzx %r11b, %eax
  testl %eax, %eax
  jne br_check_proof.L8
  movq $-1, %rax
  jmp br_check_proof.L7
  br_check_proof.L8:
  movq 48(%rsp), %rax
  movq %rax, %r11
  movq %rcx, %r10
  movq $2, %rcx
  shlq %cl, %r11
  movq %r10, %rcx
  movq %r11, %rax
  movq 24(%rsp), %rcx
  movq %rcx, %r11
  movq %rax, %r10
  addq %r10, %r11
  movq %r11, %rax
  movslq (%rax), %rax
  jmp br_check_proof.L7
  br_check_proof.L7:
  testl %eax, %eax
  jne br_check_proof.L9
  jmp br_check_proof.L6
  br_check_proof.L9:
  movq 48(%rsp), %rax
  movq %rax, %r11
  movq %rcx, %r10
  movq $3, %rcx
  shlq %cl, %r11
  movq %r10, %rcx
  movq %r11, %rax
  movq 32(%rsp), %rcx
  movq %rcx, %r11
  movq %rax, %r10
  addq %r10, %r11
  movq %r11, %rcx
  movq (%rcx), %rcx
  movq 40(%rsp), %rdx
  movq %rdx, %r11
  movq %rax, %r10
  addq %r10, %r11
  movq %r11, %rax
  movq (%rax), %rax
  movq (%rsp), %rdi
  movq 48(%rsp), %rsi
  movq %rcx, %rdx
  movq %rax, %rcx
  call br_check_clause
  jmp br_check_proof.L6
  br_check_proof.L6:
  movq 48(%rsp), %rax
  movq %rax, %r11
  movq $1, %r10
  addq %r10, %r11
  movq %r11, %rax
  jmp br_check_proof.L4
  br_check_proof.L5:
  addq $56, %rsp
  ret")

def lratCheckCode : Program := rupCode ++ (strictCode ++ (clauseCode ++ proofCode))

theorem rup_compile : compileFn Amd64.isa rupFn = .ok rupCode := by kernel_rfl
theorem strict_compile : compileFn Amd64.isa strictFn = .ok strictCode := by kernel_rfl
theorem clause_compile : compileFn Amd64.isa clauseFn = .ok clauseCode := by kernel_rfl
theorem proof_compile : compileFn Amd64.isa proofFn = .ok proofCode := by kernel_rfl

theorem lrat_module_compile :
    compile Amd64.isa lratCheckFns = .ok lratCheckCode := by kernel_rfl

def lratBound : String → Nat := fun g =>
  if g = "br_check_clause_non_strictly_by_propagation" then 472
  else if g = "br_check_clause_strictly_by_resolution" then 296
  else if g = "br_check_clause" then 520
  else 584

private theorem rupFn_nslots : rupFn.nslots Amd64.isa = 59 := by kernel_rfl
private theorem rupFn_callees : rupFn.opt.ext.callees = [] := by kernel_rfl
private theorem rupFn_exits : rupFn.opt.ext.exits = ["lrat_fail"] := by kernel_rfl

private theorem strictFn_nslots : strictFn.nslots Amd64.isa = 37 := by kernel_rfl
private theorem strictFn_callees : strictFn.opt.ext.callees = [] := by kernel_rfl
private theorem strictFn_exits : strictFn.opt.ext.exits =
    ["lrat_fail", "lrat_fail", "lrat_fail", "lrat_fail",
     "lrat_fail", "lrat_fail", "lrat_fail", "lrat_fail"] := by kernel_rfl

private theorem clauseFn_nslots : clauseFn.nslots Amd64.isa = 4 := by kernel_rfl
private theorem clauseFn_callees : clauseFn.opt.ext.callees =
    ["br_check_clause_strictly_by_resolution",
     "br_check_clause_non_strictly_by_propagation"] := by kernel_rfl
private theorem clauseFn_exits : clauseFn.opt.ext.exits = [] := by kernel_rfl

private theorem proofFn_nslots : proofFn.nslots Amd64.isa = 7 := by kernel_rfl
private theorem proofFn_callees : proofFn.opt.ext.callees = ["br_check_clause"] := by kernel_rfl
private theorem proofFn_exits : proofFn.opt.ext.exits = [] := by kernel_rfl

section Generic
variable [hh : Host]

/-- Linking `lratCheckFns` (`checkRup`, `strictCheck`, `checkClause`, `checkProof`) via
`compile_correct` in any x64 host that also defines `"lrat_fail"`. -/
theorem lrat_module_fnspec (k₀ : Nat)
    (hc : lratCheckCode.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (hfail : Amd64.target.Defined hh "lrat_fail") :
    ∀ f ∈ lratCheckFns,
      Amd64.target.FnSpec hh f.name (lratEnv f.name) (lratBound f.name) 0 := by
  refine compile_correct (T := Amd64.target) hh lratEnv lratBound 0 lratCheckFns
    lratCheckCode k₀ lrat_module_compile hc hu ?_
  intro pre f post heq
  rcases pre with _ | ⟨f1, _ | ⟨f2, _ | ⟨f3, _ | ⟨f4, pre⟩⟩⟩⟩
  · injection heq with hf _
    subst hf
    refine ⟨checkRup_wf, lratEnv_step.1, by rw [rupFn_nslots]; decide, by decide, ?_, ?_⟩
    · rw [rupFn_callees]; intro _ h; nomatch h
    · rw [rupFn_exits]
      intro g hg; simp only [List.mem_cons] at hg
      rcases hg with rfl | hg
      · exact ⟨hfail, by decide⟩
      · nomatch hg
  · injection heq with hf1 h1
    injection h1 with hf _
    subst hf1 hf
    refine ⟨strictCheck_wf, lratEnv_step.2.1, by rw [strictFn_nslots]; decide, by decide, ?_, ?_⟩
    · rw [strictFn_callees]; intro _ h; nomatch h
    · rw [strictFn_exits]
      intro g hg; simp only [List.mem_cons] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hg
      all_goals try exact ⟨hfail, by decide⟩
      nomatch hg
  · injection heq with hf1 h1
    injection h1 with hf2 h2
    injection h2 with hf _
    subst hf1 hf2 hf
    refine ⟨checkClause_wf, lratEnv_step.2.2.1, by rw [clauseFn_nslots]; decide, by decide, ?_, ?_⟩
    · rw [clauseFn_callees]
      intro g hg; simp only [List.mem_cons] at hg
      rcases hg with rfl | rfl | hg
      · exact ⟨Or.inl (by simp), by rw [clauseFn_nslots]; decide⟩
      · exact ⟨Or.inl (by simp), by rw [clauseFn_nslots]; decide⟩
      · nomatch hg
    · rw [clauseFn_exits]; intro _ h; nomatch h
  · injection heq with hf1 h1
    injection h1 with hf2 h2
    injection h2 with hf3 h3
    injection h3 with hf _
    subst hf1 hf2 hf3 hf
    refine ⟨checkProof_wf, lratEnv_step.2.2.2, by rw [proofFn_nslots]; decide, by decide, ?_, ?_⟩
    · rw [proofFn_callees]
      intro g hg; simp only [List.mem_cons] at hg
      rcases hg with rfl | hg
      · exact ⟨Or.inl (by simp), by rw [proofFn_nslots]; decide⟩
      · nomatch hg
    · rw [proofFn_exits]; intro _ h; nomatch h
  · simp [lratCheckFns] at heq

/-- End-to-end correctness of compiled `br_check_proof` on Kraken x64: in every host containing
`lratCheckCode` at `k₀` and `.label "lrat_fail"` at `k_fail` with unique labels, from a state
meeting `CheckProofPre` for formula `cnf₀` with `st` in `rdi`, 584 bytes of stack space below `rsp`,
and return address `ra` at `rsp`, execution of `br_check_proof` either:
* returns to `ra` with `cnf₀.Unsat` established, callee-saved registers intact, `rsp` popped, and
  `FullMemInv` preserved in memory; or
* exits to `"lrat_fail"` at `Host.addrOf k_fail` with a 16-byte aligned entry stack pointer. -/
theorem checkProof_x64_correct (k₀ k_fail : Nat)
    (hc : lratCheckCode.IsInfixAt Host.prog k₀)
    (hfail : Host.prog[k_fail]? = some (.label "lrat_fail")) (hu : Host.LabelsUnique)
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
      ((fun f => ∃ bs : List UInt8, bs.length = 584 ∧ f = bs.At (s.regs.get64 .rsp - 584#64)) ⋆
        Eq (ra.toUInt64.At (s.regs.get64 .rsp))) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st =>
        (st.pc = ra ∧ cnf₀.Unsat ∧
          (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15], st.data.regs.get64 r = s.regs.get64 r) ∧
          st.data.regs.get64 .rsp = s.regs.get64 .rsp + 8#64 ∧
          ∃ m' k', FullMemInv max_var n trail_free0.length st_ptr k₀_fields P_ro k' m' ∧
            (st.data.dmem =⋆ Eq m' ⋆
              (fun f => ∃ bs : List UInt8, bs.length = 592 ∧ f = bs.At (s.regs.get64 .rsp - 584#64)) ⋆ R)) ∨
        (st.pc = Host.addrOf k_fail ∧ (st.data.regs.get64 .rsp + 8#64).toNat % 16 = 0))
      ⟨s, Host.addrOf (k₀ + rupCode.length + strictCode.length + clauseCode.length)⟩ := by
  let Q : LeanQbe.Post := fun rets m' =>
    rets = [] ∧ (∃ k', FullMemInv max_var n trail_free0.length st_ptr k₀_fields P_ro k' m') ∧ cnf₀.Unsat
  let X : XPost := fun g _ _ => g = "lrat_fail"
  have hspec : checkProofSpec [st_ptr] m Q X :=
    ⟨max_var, n, st_ptr, k₀_fields, usedWords, litsPtrs, antePtrs, trail_free0, cnf₀,
      clauses, litsTable, anteTable, P_ro, rfl, pre,
      fun _ hinv hunsat => ⟨rfl, hinv, hunsat⟩, fun _ _ => rfl⟩
  have hargs : Amd64.target.ArgsIn [st_ptr] s := by
    simp [Target.ArgsIn, Target.ValsIn, Amd64.target, Amd64.isa, hrdi]
  have hf := lrat_module_fnspec k₀ hc hu ⟨k_fail, hfail⟩ proofFn (by simp [lratCheckFns, proofFn])
    [st_ptr] m Q X hspec s ra R hargs trivial hsp hmem
  have hproof_infix : proofCode.IsInfixAt Host.prog
      (k₀ + rupCode.length + strictCode.length + clauseCode.length) := by
    have h1 := hc.append.2.append.2.append.2
    simpa only [Nat.add_assoc] using h1
  have hlab : Amd64.target.labelAddr hh proofFn.name =
      Host.addrOf (k₀ + rupCode.length + strictCode.length + clauseCode.length) :=
    labelAddr_of_unique (T := Amd64.target) hu hproof_infix.cons.1
  have hflab : Amd64.target.labelAddr hh "lrat_fail" = Host.addrOf k_fail :=
    labelAddr_of_unique (T := Amd64.target) hu hfail
  rw [hlab] at hf
  refine eventually_weaken _ _ _ _ ?_ hf
  rintro st (⟨hpc, rets, m', ⟨rfl, ⟨k', hinv'⟩, hunsat⟩, -, ⟨hcs, hsp'⟩, hm'⟩ |
    ⟨sym', as', m', rfl, _, hpc, _, hspE, _⟩)
  · exact Or.inl ⟨hpc, hunsat, fun r hr => hcs r hr, hsp', m', k', hinv', hm'⟩
  · rw [hflab] at hpc
    exact Or.inr ⟨hpc, hspE⟩

end Generic

/-! ## Non-vacuity: concrete host and concrete memory `nvCheckBytes` -/

def lratProg : Program := lratCheckCode ++ [.label "lrat_fail"]

abbrev lratHost : Host :=
  .ofLayout lratProg (layoutOf lratProg) (layoutOf_zero _) (of_decide_eq_true (by kernel_rfl))

attribute [local instance] lratHost

theorem lratHost_prog : Host.prog = lratProg := rfl

theorem lratHost_unique : Host.LabelsUnique :=
  Host.labelsUnique_of_nodup (of_decide_eq_true (by kernel_rfl))

def zeros584 : List UInt8 := List.replicate 584 0

def lratState0 : MachineData :=
  { regs := { rdi := 0x1000, rsp := 0x0ff8 },
    dmem := ((zeros584 ++ raBytes0) ++ nvCheckBytes).At 0x0db0#64 }

theorem checkProof_x64_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st =>
        (st.pc = 0x1234 ∧ (CNF.empty : CNF Nat).Unsat) ∨
        st.pc = Host.addrOf lratCheckCode.length)
      ⟨lratState0, Host.addrOf (rupCode.length + strictCode.length + clauseCode.length)⟩ := by
  have hlen : raBytes0.length = 8 := UInt64.toBytes_length _
  have h584 : zeros584.length = 584 := List.length_replicate
  have hnv_len : nvCheckBytes.length = 210 := by
    simp [nvCheckBytes, bytesN_length, KernelFields.toList]
  have hmem : lratState0.dmem =⋆ Eq (nvCheckBytes.At 0x1000#64) ⋆
      ((fun f => ∃ bs : List UInt8, bs.length = 584 ∧ f = bs.At (lratState0.regs.get64 .rsp - 584#64)) ⋆
        Eq ((0x1234 : Int64).toUInt64.At (lratState0.regs.get64 .rsp))) ⋆
      Std.ExtHashMap.emp := by
    rw [Std.ExtHashMap.sep_emp, Std.ExtHashMap.sep_comm]
    have h1 := Mem.At_append_sep (zeros584 ++ raBytes0) nvCheckBytes 0x0db0#64
      (by simp [hlen, h584, hnv_len])
    have e1 : (0x0db0#64 + BitVec.ofNat 64 (zeros584 ++ raBytes0).length) = 0x1000#64 := by
      simp [h584, hlen]
    rw [e1] at h1
    have h2 := Mem.At_append_sep zeros584 raBytes0 0x0db0#64 (by simp [hlen, h584])
    have e2 : (0x0db0#64 + BitVec.ofNat 64 zeros584.length) = 0x0ff8#64 := by simp [h584]
    rw [e2] at h2
    have h0 : (Eq (((zeros584 ++ raBytes0) ++ nvCheckBytes).At 0x0db0#64)) lratState0.dmem := rfl
    rw [h1] at h0
    refine sep_mono (fun f hf => ?_) h0
    rw [h2] at hf
    exact sep_mono (fun f1 hf1 => ⟨zeros584, h584, hf1.symm⟩) hf
  have hc : lratCheckCode.IsInfixAt Host.prog 0 := by
    rw [lratHost_prog]; exact ⟨[.label "lrat_fail"], rfl⟩
  have hfail : Host.prog[lratCheckCode.length]? = some (.label "lrat_fail") := by
    rw [lratHost_prog, lratProg, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  have hrdi : lratState0.regs.get64 .rdi = 0x1000#64 := rfl
  have hsp : (lratState0.regs.get64 .rsp + 8#64).toNat % 16 = 0 :=
    show (0x0ff8#64 + 8#64).toNat % 16 = 0 by decide
  have h := checkProof_x64_correct 0 lratCheckCode.length hc hfail lratHost_unique nvCheck_pre
    lratState0 0x1234 Std.ExtHashMap.emp hrdi hsp hmem
  rw [Nat.zero_add] at h
  refine eventually_weaken _ _ _ _ ?_ h
  rintro st (⟨hpc, hunsat, -⟩ | ⟨hpc, -⟩)
  · exact Or.inl ⟨hpc, hunsat⟩
  · exact Or.inr hpc

end LeanQbe.Litmus
