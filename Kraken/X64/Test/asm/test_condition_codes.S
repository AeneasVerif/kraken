# Test various condition codes.
# Undefined flags: af, cf, sf, zf, pf, of

  movq $1, %rax
  movq $2, %rcx
  cmpq %rcx, %rax  # %rax - %rcx
  jl ok_l          # %rax <s %rcx
  jmp quit
ok_l:
  addq $1, %rdx
  cmpq %rax, %rcx
  jl quit          # !(%rcx <s %rax)
  addq $1, %rdx
  movq $-1, %rax
  movq $-1, %rcx
  cmpq %rcx, %rax
  jle ok_le        # %rax <=s %rcx
  jmp quit
ok_le:
  addq $1, %rdx
  cmpq %rax, %rcx  # %rcx <=s %rax
  jle ok_le_2
  jmp quit
ok_le_2:
  addq $1, %rdx
quit:
