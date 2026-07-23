mov %rsp, %rsi

pushq $42
pop %rsp

mov %rsp, %rdi
sub $42, %rdi
mov %rsi, %rsp

# AF is undefined after xor
mov $0, %rsi
