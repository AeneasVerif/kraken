# Test: native runs start from Kraken's rsp and stack, so absolute rsp values,
# the initial stack contents and a moved final rsp all match.
movq %rsp, %rax         # Kraken's initial rsp
pushq $42
subq $24, %rsp          # flags (e.g. PF) depend on rsp's value
movq %rsp, %rbx
movq 24(%rsp), %rcx     # 42
movq -8(%rsp), %rdx     # the initial stack is filled with 0xff
