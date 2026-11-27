module

public import LeanQbe.T.LeanLCNF.Basic
public import LeanQbe.T.LeanLCNF.Lower1
public import LeanQbe.T.Bootstrap0.Splice0
public import LeanQbe.T.LeanLCNF.LcnfC0Full
meta import LeanQbe.T.LeanLCNF.Basic
meta import LeanQbe.T.LeanLCNF.Lower1
meta import LeanQbe.T.Bootstrap0.Splice0

/-!
# Verified Lean `LCNF` `Nat → String` Demo Program (`LcnfC0Demo`)

Pure data/IR module (`0` proof imports, `0` target-arch imports) extracting three interdependent
Lean 4 definitions via `lcnf_of_lean!` and `splice_lcnf_tflat!` for linking against
`rtC0CoreMod`:

1. `DemoNatStr.addNat`: `Nat + Nat` (tagged scalar fast path + R1 `lcnf_nat_slow`).
2. `DemoNatStr.addToStr`: `toString (addNat a b)` (calls `addNat` + R2b `lcnf_nat_to_str` → R0
   `lcnf_alloc`).
3. `DemoNatStr.fmtSumTagged`: `tag ++ addToStr a b` (calls `addToStr` + R2b
   `lcnf_string_append` + R0 `lcnf_dec_ref_cold` → `lcnf_free_obj`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.LeanLCNF

open LeanQbe.T

namespace DemoNatStr

@[expose, noinline] def addNat (a b : Nat) : Nat := a + b

@[expose, noinline] def addToStr (a b : Nat) : String := toString (addNat a b)

@[expose] def fmtSumTagged (tag : String) (a b : Nat) : String := tag ++ addToStr a b

end DemoNatStr

lcnf_of_lean! demoNatStrLcMod
  [DemoNatStr.addNat, DemoNatStr.addToStr, DemoNatStr.fmtSumTagged]

splice_lcnf_tflat! demoNatStrTfs demoNatStrLcMod

/-- Standalone user `Module` containing the three lowered Lean `LCNF` functions. -/
@[expose] def demoNatStrProgMod : Module :=
  { fns := Frontend.C0.tflatFnsToFns demoNatStrTfs, externs := [], exits := rtExitSyms }

/-- Full `89`-function linked `Module`: `rtC0CoreMod` (`86` fns) ++
`demoNatStrProgMod` (`3` fns). -/
@[expose] def demoNatStrLinkedMod : Module :=
  linkLcnfWithRtC0 demoNatStrTfs false

end LeanQbe.T.LeanLCNF
