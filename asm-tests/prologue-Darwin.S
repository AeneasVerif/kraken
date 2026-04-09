.data
.align 8
final_rax: .quad 0
final_rbx: .quad 0
final_rcx: .quad 0
final_rdx: .quad 0
final_rsi: .quad 0
final_rdi: .quad 0
final_rsp: .quad 0
final_rbp: .quad 0
final_r8: .quad 0
final_r9: .quad 0
final_r10: .quad 0
final_r11: .quad 0
final_r12: .quad 0
final_r13: .quad 0
final_r14: .quad 0
final_r15: .quad 0
final_flags: .quad 0

.text
.globl _main

_main:
  xor %rax, %rax
  xor %rbx, %rbx
  xor %rcx, %rcx
  xor %rdx, %rdx
  xor %rsi, %rsi
  xor %rdi, %rdi
  xor %rbp, %rbp
  xor %r8, %r8
  xor %r9, %r9
  xor %r10, %r10
  xor %r11, %r11
  xor %r12, %r12
  xor %r13, %r13
  xor %r14, %r14
  xor %r15, %r15
