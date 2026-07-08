import Init.Grind
import KrakenStdlibCandidates.Init.GrindInternHooks

@[grind_homo] theorem Nat.hShiftLeft_eq (a n : Nat) : a <<< n = a * 2^n := Nat.shiftLeft_eq a n
@[grind_homo] theorem Nat.hShiftRight_eq (a n : Nat) : a >>> n = a / 2^n := Nat.shiftRight_eq_div_pow a n
