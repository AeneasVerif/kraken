# Undefined flags: n, z, c, v

// cbz (taken)
cbz xzr, _cbz_xzr_taken
add x0, x0, #100
_cbz_xzr_taken:

cbz wzr, _cbz_wzr_taken
add x0, x0, #200
_cbz_wzr_taken:

// cbz (not taken)
add x1, x1, #42
cbz x1, _cbz_not_taken
add x0, x0, #1
_cbz_not_taken:

// cbnz (taken)
add x2, x2, #15
cbnz x2, _cbnz_taken
add x0, x0, #300
_cbnz_taken:

// cbnz (not taken)
cbnz xzr, _cbnz_xzr_not_taken
add x0, x0, #10
_cbnz_xzr_not_taken:

cbnz wzr, _cbnz_wzr_not_taken
add x0, x0, #20
_cbnz_wzr_not_taken:
