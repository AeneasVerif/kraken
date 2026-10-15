# Test: symbol operands, with their GNU as AT&T meaning:
#   $sym        the address of sym, as an immediate
#   sym         the memory at the absolute address sym (here: lea)
#   sym(%reg)   memory with the address of sym as displacement
#   sym(%rip)   the memory at sym, encoded RIP-relative
# Symbol addresses differ between native and Kraken, so only differences of
# addresses are left in registers.
  leaq anchor(%rip), %rcx    # rcx = &anchor
anchor:
  movq $anchor, %rax         # rax = &anchor
  subq %rcx, %rax            # rax = 0
  leaq anchor, %rbx          # rbx = &anchor
  subq %rcx, %rbx            # rbx = 0
  leaq anchor+8(%rip), %rdx  # rdx = &anchor + 8
  subq %rcx, %rdx            # rdx = 8
  pushq $7
  pushq $42
  movq %rsp, %rsi
  subq $anchor, %rsi         # rsi = %rsp - &anchor
  movq anchor(%rsi), %rdi    # rdi = (%rsp) = 42
  movq anchor+8(%rsi), %r8   # r8 = 8(%rsp) = 7
  popq %r9
  popq %r10
  movl $0, %ecx
  movl $0, %esi
  cmpq %rax, %rax            # flags independent of symbol addresses
