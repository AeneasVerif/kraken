import KrakenStdlibCandidates.Init.GrindInternHooks
open Lean.Grind

#remove_toint_instances

/--
error: failed to synthesize
  ToInt.Add Nat (IntInterval.ci 0)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#synth ToInt.Add Nat (.ci 0)
