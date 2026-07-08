import KrakenStdlibCandidates
open Lean.Grind in #remove_toint_instances

example (x : USize) : x.toNat >>> 64 = 0 := by
  grind
