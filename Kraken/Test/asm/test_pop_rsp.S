mov %rsp, %rsi

pushq $42
pop %rsp

mov %rsp, %rdi
sub $42, %rdi
mov %rsi, %rsp
xor %rsi, %rsi
