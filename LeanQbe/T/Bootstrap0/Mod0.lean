module

public import LeanQbe.T.Bootstrap0.Compiler0
public import LeanQbe.T.Bootstrap0.Splice0
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.Amd64.LcnfC0FullCertX64Bounds
public import LeanQbe.T.LeanLCNF.LcnfC0Full
meta import LeanQbe.T.Bootstrap0.Compiler0
meta import LeanQbe.T.Bootstrap0.Splice0
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Amd64.LcnfC0FullCertX64Bounds

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
  { fns := Frontend.C0.tflatFnsToFns leanqbe0Tfs
    externs := rtExterns
    exits := rtExitSyms }

/-- Every lowered function in `leanqbe0Mod0` satisfies `Func.Wf` via `tflatFnsToFns_wf`. -/
theorem leanqbe0Mod0_wf : ∀ f ∈ leanqbe0Mod0.fns, f.Wf :=
  Frontend.C0.tflatFnsToFns_wf leanqbe0Tfs

/-- Call graph of `leanqbe0Mod0` is strictly acyclic (`checkAcyclic = true`). -/
theorem leanqbe0Mod0_acyclic : leanqbe0Mod0.checkAcyclic = true := by
  t_kernel_rfl

/-- Verified x86-64 runtime stack-bound table (`rtC0CoreAllExt`, `86` fns) replacing the former
assumed `64`-byte extern bounds. -/
def rtExtBounds0 : List (SigEntry × Nat) :=
  rtC0CoreAllExt

/-- Closed `210`-function whole-program `Module` linking `rtC0CoreMod` (`86` fns) and
`leanqbe0Mod0` (`124` fns) with `0` externs (`exits := rtExitSyms`). -/
def leanqbe0LinkedMod : Module :=
  linkLcnfWithRtC0 leanqbe0Tfs false

end LeanQbe.T.Bootstrap0

end

public section

namespace LeanQbe.T.Bootstrap0

open LeanQbe.T
open LeanQbe.T.LeanLCNF

/-- Every function in `leanqbe0LinkedMod.fns` (`210` fns) satisfies `Func.Wf`. -/
theorem leanqbe0LinkedMod_wf : ∀ f ∈ leanqbe0LinkedMod.fns, f.Wf := by
  intro f hf
  rcases List.mem_append.mp hf with hrt | huser
  · exact rtC0CoreMod_fns_wf f hrt
  · exact leanqbe0Mod0_wf f huser

/-- Call graph of the closed `210`-function module `leanqbe0LinkedMod` is strictly acyclic. -/
theorem leanqbe0LinkedMod_acyclic : leanqbe0LinkedMod.checkAcyclic = true := by
  t_kernel_rfl

end LeanQbe.T.Bootstrap0
