module

public import LeanQbe.T.LeanLCNF.Basic
public import LeanQbe.T.LeanLCNF.Lower1
public import LeanQbe.T.Bootstrap0.Splice0
public import LeanQbe.T.LeanLCNF.LcnfC0Full
meta import LeanQbe.T.LeanLCNF.Basic
meta import LeanQbe.T.LeanLCNF.Lower1
meta import LeanQbe.T.Bootstrap0.Splice0

/-!
# Verified Lean `LCNF` Self-Tail Bignum Factorial Demo (`LcnfC0LoopDemo`)

Pure data/IR module (`0` proof imports, `0` target-arch imports) extracting two interdependent
Lean 4 definitions via `lcnf_of_lean!` and `splice_lcnf_tflat!` for linking against `rtC0CoreMod`:

1. `FactLoop.factAcc`: tail-recursive `Nat` factorial accumulator lowered into a single-function
   `.jump` self-tail loop calling R1 `lcnf_nat_slow` (`mul`) on multi-limb MPZs and R0
   `lcnf_dec_ref_cold` to release intermediate heap MPZs at every iteration.
2. `FactLoop.factStr`: `toString (factAcc n 1)` formatting arbitrary-precision factorial results
   (e.g. `25! = 15511210043330985984000000 > 2^64`) via R2b `lcnf_nat_to_str`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.LeanLCNF

open LeanQbe.T

/-- Mathematical factorial specification target for `FactLoop`. -/
@[expose] def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

namespace FactLoop

/-- Self-tail-recursive `Nat` factorial accumulator. -/
@[expose, noinline] def factAcc (n acc : Nat) : Nat :=
  if _h : n = 0 then acc else factAcc (n - 1) (acc * n)
termination_by n

/-- Decimal string formatter for `fact n` (`toString (factAcc n 1)`). -/
@[expose] def factStr (n : Nat) : String :=
  toString (factAcc n 1)

end FactLoop

lcnf_of_lean! factLoopLcMod
  [FactLoop.factAcc, FactLoop.factStr]

splice_lcnf_tflat! factLoopTfs factLoopLcMod

/-- Standalone user `Module` containing the two lowered Lean `LCNF` functions. -/
@[expose] def factLoopProgMod : Module :=
  { fns := Frontend.C0.tflatFnsToFns factLoopTfs, externs := [], exits := rtExitSyms }

/-- Full `88`-function linked `Module`: `rtC0CoreMod` (`86` fns) ++
`factLoopProgMod` (`2` fns). -/
@[expose] def factLoopLinkedMod : Module :=
  linkLcnfWithRtC0 factLoopTfs false

end LeanQbe.T.LeanLCNF
