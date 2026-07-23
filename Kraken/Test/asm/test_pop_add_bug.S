# We need to start the stack at a plausible address, otherwise
# we get trivial CF/ZF flag disagreements. Since we don't control the
# address of the stack when running natively (but we *can* control the
# last byte), byte-align the stack to avoid PF disagreements.

pushq %rax
addq $8, %rsp
