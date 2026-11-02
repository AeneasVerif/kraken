# Test that adc adds the carry correctly.

# Set carry
movq $-1, %rax
addq $1, %rax

adc $1, %rax
