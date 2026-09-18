  lea (%rip), %rax
next:
  lea next(%rip), %rcx
  subq %rcx, %rax
  movl $0, %ecx
