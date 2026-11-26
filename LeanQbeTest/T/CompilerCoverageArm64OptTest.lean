module

public import LeanQbe.T.MainCertCore
public import LeanQbe.T.MainCertFlat
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbeTest.T.CompilerCoverageFixture
public meta import Lean
public meta import LeanQbe.T.MainCertElab
public meta import LeanQbe.T.MainCertFlatElab
public meta import LeanQbe.T.Arm64.Targ
public meta import LeanQbe.T.MainFlat

/-!
# AAPCS64 Arm64 Compiler Coverage Opt/Ctrl & Parity Test (`CompilerCoverageArm64OptTest`)

Compiles `covOptMod` (control-flow/syntax constructors + every `MainFlat.lean` optimization gate)
via BOTH `compile_linked_chunks! ... (flat := false)` and `(flat := true)` on `armTarget`,
verifying `MainFlat` gate triggers under `armLegalTarget`, kernel `code = rfl` and `bounds = rfl`
parity, exported `MainFlat` closure audit (`auditMainFlatClosure`), and `<= std3` axioms.
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.CompilerCoverageArm64OptTest

open LeanQbe.T LeanQbe.T.Arm64 LeanQbeTest.T.CompilerCoverage

theorem arm64_straight_gates :
    let st := midAt armLegalTarget fnOptStraight.as (reifyFunc fnOptStraight.body)
    (!(tflatEq st.tf0c st.tfDiv) && !(tflatEq st.tfPreMem st.tfMem) &&
      !(tflatEq st.tfGvn st.tfAssB) && !(tflatEq st.tfMidSimp st.tfDle)) = true := by
  decide +kernel

compile_linked_chunks! covArm64OptLeg armTarget armLayout armLegalTarget armLabelClean
  covOptMod 32 (ext := [(⟨"cov_ext", [i64], [i64]⟩, 0)]) (exits := ["cov_ext_exit"])
  (flat := false)

compile_linked_chunks! covArm64OptFlat armTarget armLayout armLegalTarget armLabelClean
  covOptMod 32 (ext := [(⟨"cov_ext", [i64], [i64]⟩, 0)]) (exits := ["cov_ext_exit"])
  (flat := true)

theorem arm64_opt_code_eq : covArm64OptLeg.code = covArm64OptFlat.code := rfl

theorem arm64_opt_bounds_eq : covArm64OptLeg.bounds = covArm64OptFlat.bounds := rfl

noncomputable def covArm64OptFlatCast :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean
      (covOptSrcMod.optInlinePolicy covPol)
      [(⟨"cov_ext", [i64], [i64]⟩, 0)] ["cov_ext_exit"] 0 2048 :=
  covArm64OptFlat.castModule covOptMod.eq

#eval auditMainFlatClosure

#print axioms arm64_straight_gates
#print axioms arm64_opt_code_eq
#print axioms arm64_opt_bounds_eq
#print axioms covArm64OptLeg
#print axioms covArm64OptFlat
#print axioms covArm64OptFlatCast

end LeanQbeTest.T.CompilerCoverageArm64OptTest