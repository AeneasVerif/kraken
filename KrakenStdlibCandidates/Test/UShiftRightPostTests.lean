import KrakenStdlibCandidates

example (a : Nat) : (a >>> 3) = a / 8 := by
  grind

example (x : BitVec 64) : (x >>> 3#64).toNat = x.toNat / 8 := by
  grind

example (x : BitVec 64) : ((x &&& 63#64) >>> 3#64).toNat = (x.toNat % 64) / 8 := by
  grind

example (a : Nat) (h : a < 64) : (a >>> 3) < 8 := by
  grind

example (a : Nat) : (a >>> (1 + 2)) = a / 8 := by
  grind

example (x : BitVec 64) : (x >>> BitVec.ofNat 64 (2 + 1)).toNat = x.toNat / 8 := by
  grind

example (x : BitVec 64) : ((x &&& BitVec.ofNat 64 (2^3 - 1)) >>> 3#64).toNat = (x.toNat % 8) / 8 := by
  grind

example (a : Int) : (a >>> 3) = a / 8 := by
  grind
