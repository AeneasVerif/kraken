# Test: a leading 0 marks an octal number, as in GNU as
# (https://sourceware.org/binutils/docs/as/Integers.html).

movq $033, %rax                 # rax = 27
movq $-010, %rbx                # rbx = -8
leaq 010(%rax), %rsi            # rsi = 27 + 8 = 35
leaq -010(%rax), %rdi           # rdi = 27 - 8 = 19
