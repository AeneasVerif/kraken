module

public import LeanQbe.T.MainCertCore
public import LeanQbe.T.MainCertFlat
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbeTest.T.CompilerCoverageFixture
public meta import Lean
public meta import LeanQbe.T.MainCertElab
public meta import LeanQbe.T.MainCertFlatElab
public meta import LeanQbe.T.Arm64.Targ

/-!
# AAPCS64 Arm64 Compiler Coverage Ops & Parity Test (`CompilerCoverageArm64OpsTest`)

Compiles `covArm64OpsMod` (shared scalar/cmp/bool/select ops + Arm64 `rbit`/`udiv0`/`sdiv0`)
via BOTH `compile_linked_chunks! ... (flat := false)` and `(flat := true)` on `armTarget`,
verifying `TFlat.supportsSource armLegalTarget` (`rbit`/`udiv0`/`sdiv0` accepted, float/bitcast
rejected), kernel `code = rfl` and `bounds = rfl` parity, and `<= std3` axioms.
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.CompilerCoverageArm64OpsTest

open LeanQbe.T LeanQbe.T.Arm64 LeanQbeTest.T.CompilerCoverage

theorem arm64_bitops_supportsSource :
    TFlat.supportsSource armLegalTarget (reifyFunc fnArm64BitOps.body) = true ∧
      TFlat.supportsSource armLegalTarget (reifyFunc fnLegalFloatBitcast.body) = false := by
  decide +kernel

compile_linked_chunks! covArm64OpsLeg armTarget armLayout armLegalTarget armLabelClean
  covArm64OpsMod 32 (flat := false)

compile_linked_chunks! covArm64OpsFlat armTarget armLayout armLegalTarget armLabelClean
  covArm64OpsMod 32 (flat := true)

theorem arm64_ops_code_eq : covArm64OpsLeg.code = covArm64OpsFlat.code := rfl

theorem arm64_ops_bounds_eq : covArm64OpsLeg.bounds = covArm64OpsFlat.bounds := rfl

noncomputable def covArm64OpsFlatCast :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean
      (covArm64OpsSrcMod.optInlinePolicy {}) [] [] 0 2048 :=
  covArm64OpsFlat.castModule covArm64OpsMod.eq

#print axioms arm64_bitops_supportsSource
#print axioms arm64_ops_code_eq
#print axioms arm64_ops_bounds_eq
#print axioms covArm64OpsLeg
#print axioms covArm64OpsFlat
#print axioms covArm64OpsFlatCast

end LeanQbeTest.T.CompilerCoverageArm64OpsTest