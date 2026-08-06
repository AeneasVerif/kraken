	.text
	.file	"sum_to_n.c"
	.globl	sum_to_n                        # -- Begin function sum_to_n
	.type	sum_to_n,@function
sum_to_n:                               # @sum_to_n
# %bb.0:
	xorl	%eax, %eax
	testq	%rdi, %rdi
	je	.LBB0_2
.LBB0_1:                                # =>This Inner Loop Header: Depth=1
	addq	%rdi, %rax
	#APP
	#NO_APP
	decq	%rdi
	jne	.LBB0_1
.LBB0_2:
	retq
.Lfunc_end0:
	.size	sum_to_n, .Lfunc_end0-sum_to_n
                                        # -- End function
	.section	".note.GNU-stack","",@progbits
	.addrsig
