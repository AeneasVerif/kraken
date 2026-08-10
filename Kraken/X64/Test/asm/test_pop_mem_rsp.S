# Undefined flags: af

mov %rsp, %rsi

pushq %rsp
pushq %rsp
popq (%rsp)
popq %r11

movq -8(%rsi), %rdi
movq -16(%rsi), %rax
sub %rsi, %rdi
sub %rsi, %rax
mov %rsi, %rsp

xor %rsi, %rsi
xor %r11, %r11
