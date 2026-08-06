	.text
	.file	"sum_to_n.c"
	.globl	sum_to_n                        // -- Begin function sum_to_n
	.p2align	2
	.type	sum_to_n,@function
sum_to_n:                               // @sum_to_n
// %bb.0:
	mov	x8, xzr
	cbz	x0, .LBB0_2
.LBB0_1:                                // =>This Inner Loop Header: Depth=1
	add	x8, x8, x0
	//APP
	//NO_APP
	subs	x0, x0, #1
	b.ne	.LBB0_1
.LBB0_2:
	mov	x0, x8
	ret
.Lfunc_end0:
	.size	sum_to_n, .Lfunc_end0-sum_to_n
                                        // -- End function
	.section	".note.GNU-stack","",@progbits
	.addrsig
