module

import LeanQbe.T.MainCertCore
import LeanQbe.T.MainCertFlat
import LeanQbe.T.Amd64.TargLemmas
import LeanQbeTest.T.CompilerCoverageFixture
meta import Lean
import LeanQbe.T.MainCertElab
import LeanQbe.T.MainCertFlatElab
meta import LeanQbe.T.Amd64.Targ

/-!
# SysV x64 Compiler Coverage Ops/SIMD & Parity Test (`CompilerCoverageX64OpsTest`)

Compiles `covX64OpsMod` (shared scalar/cmp/bool/select ops + x64 `clz`/`cls`/`ctz`/`popcnt` +
128/256-bit SIMD + `v4f32` float ops) via BOTH `compile_linked_chunks! ... (flat := false)` and
`(flat := true)` on `x64Target`, verifying `TFlat.supportsSource x64LegalTarget` on scalar
`f32`/`f64`/`fcvt`/cross-type `bitcast`, kernel `code = rfl` and `bounds = rfl` parity, and
`<= std3` axioms.
-/

set_option autoImplicit false

section

namespace LeanQbeTest.T.CompilerCoverageX64OpsTest

open LeanQbe.T LeanQbe.T.Amd64 LeanQbeTest.T.CompilerCoverage

theorem x64_float_bitcast_supportsSource :
    TFlat.supportsSource x64LegalTarget (reifyFunc fnX64Float32Bitcast.body) = true := by
  decide +kernel

compile_linked_chunks! covX64OpsLeg x64Target x64Layout x64LegalTarget x64LabelClean
  covX64OpsMod 32 (flat := false)

compile_linked_chunks! covX64OpsFlat x64Target x64Layout x64LegalTarget x64LabelClean
  covX64OpsMod 32 (flat := true)

theorem x64_ops_code_eq : covX64OpsLeg.code = covX64OpsFlat.code := rfl

theorem x64_ops_bounds_eq : covX64OpsLeg.bounds = covX64OpsFlat.bounds := rfl

noncomputable def covX64OpsFlatCast :
    LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean
      (covX64OpsSrcMod.optInlinePolicy {}) [] [] 0 2048 :=
  covX64OpsFlat.castModule covX64OpsMod.eq

#print axioms x64_float_bitcast_supportsSource
#print axioms x64_ops_code_eq
#print axioms x64_ops_bounds_eq
#print axioms covX64OpsLeg
#print axioms covX64OpsFlat
#print axioms covX64OpsFlatCast

end LeanQbeTest.T.CompilerCoverageX64OpsTest