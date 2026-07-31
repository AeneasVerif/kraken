# Undefined flags: n, z, c, v

// tbz (taken)
tbz xzr, #0, _tbz_xzr_taken
add x0, x0, #100
_tbz_xzr_taken:

tbz xzr, #63, _tbz_bit63_taken
add x0, x0, #200
_tbz_bit63_taken:

// tbz (not taken)
add x1, x1, #1
tbz x1, #0, _tbz_not_taken
add x0, x0, #1
_tbz_not_taken:

// tbnz (taken)
add x2, x2, #1
tbnz x2, #0, _tbnz_taken
add x0, x0, #300
_tbnz_taken:

// tbnz (not taken)
tbnz xzr, #0, _tbnz_xzr_not_taken
add x0, x0, #10
_tbnz_xzr_not_taken:

tbnz wzr, #31, _tbnz_wzr_not_taken
add x0, x0, #20
_tbnz_wzr_not_taken:
