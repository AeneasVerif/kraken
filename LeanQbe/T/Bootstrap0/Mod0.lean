module

public import LeanQbe.T.Bootstrap0.Compiler0
public import LeanQbe.T.Bootstrap0.Splice0
public import LeanQbe.T.Amd64.TargLemmas
meta import LeanQbe.T.Bootstrap0.Compiler0
meta import LeanQbe.T.Bootstrap0.Splice0
meta import LeanQbe.T.Amd64.Targ

/-!
# Spliced Kernel `T.Module` (`leanqbe0Mod0`) for `leanqbe0Compile`

Materializes `LeanQbe.T.Bootstrap0.leanqbe0LcMod` into a topologically sorted (callees-first),
well-formed, acyclic `LeanQbe.T.Module` (`leanqbe0Mod0`) with proven `Wf` and `checkAcyclic`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Bootstrap0

open LeanQbe.T
open LeanQbe.T.LeanLCNF
open LeanQbe.T.Amd64

splice_lcnf_tflat! leanqbe0Tfs leanqbe0LcMod

/-- Kernel `LeanQbe.T.Module` lowered from `leanqbe0Compile`. -/
def leanqbe0Mod0 : Module :=
  { fns := LeanLRC.tflatFnsToFns leanqbe0Tfs
    externs := rtExterns
    exits := rtExitSyms }

/-- Every lowered function in `leanqbe0Mod0` satisfies `Func.Wf` via `tflatFnsToFns_wf`. -/
theorem leanqbe0Mod0_wf : ∀ f ∈ leanqbe0Mod0.fns, f.Wf :=
  LeanLRC.tflatFnsToFns_wf leanqbe0Tfs

/-- Call graph of `leanqbe0Mod0` is strictly acyclic (`checkAcyclic = true`). -/
theorem leanqbe0Mod0_acyclic : leanqbe0Mod0.checkAcyclic = true := by
  t_kernel_rfl

/-- Extern bounds mapping every `rtExterns` signature to step bound `64`. -/
def rtExtBounds0 : List (SigEntry × Nat) :=
  rtExterns.map fun ex => ((ex.name, ex.as, ex.rs), 64)

end LeanQbe.T.Bootstrap0
