// b.eq / b.ne
cmp x0, x0
b.eq _eq_taken
add x1, x1, #1
_eq_taken:
b.ne _ne_taken
add x2, x2, #10
_ne_taken:

// b.cs / b.cc
adds x10, x0, x1
b.cs _cs_target
add x3, x3, #100
_cs_target:
b.cc _cc_target
add x3, x3, #200
_cc_target:

// b.gt / b.lt / b.ge / b.le
cmp x0, x1
b.gt _gt_target
add x4, x4, #300
_gt_target:
b.lt _lt_target
add x5, x5, #400
_lt_target:
b.ge _ge_target
add x6, x6, #500
_ge_target:
b.le _le_target
add x7, x7, #600
_le_target:
