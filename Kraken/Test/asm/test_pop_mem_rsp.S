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

# AF is undefined after xor
mov $0, %rsi
mov $0, %r11
