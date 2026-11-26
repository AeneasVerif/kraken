module

public import LeanQbe.T.MainCertCore
public import LeanQbe.T.MainCertFlat
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbeTest.T.CompilerCoverageFixture
public meta import Lean
public meta import LeanQbe.T.MainCertElab
public meta import LeanQbe.T.MainCertFlatElab
public meta import LeanQbe.T.Amd64.Targ
public meta import LeanQbe.T.MainFlat

/-!
# SysV x64 Compiler Coverage Opt/Ctrl & Parity Test (`CompilerCoverageX64OptTest`)

Compiles `covOptMod` (control-flow/syntax constructors + every `MainFlat.lean` optimization gate)
via BOTH `compile_linked_chunks! ... (flat := false)` and `(flat := true)` on `x64Target`,
verifying exact kernel `code = rfl` and `bounds = rfl` parity, exported `MainFlat` closure
audit (`auditMainFlatClosure`), and `<= std3` axioms.
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.CompilerCoverageX64OptTest

open LeanQbe.T LeanQbe.T.Amd64 LeanQbeTest.T.CompilerCoverage

compile_linked_chunks! covX64OptLeg x64Target x64Layout x64LegalTarget x64LabelClean
  covOptMod 32 (ext := [(⟨"cov_ext", [i64], [i64]⟩, 0)]) (exits := ["cov_ext_exit"])
  (flat := false)

compile_linked_chunks! covX64OptFlat x64Target x64Layout x64LegalTarget x64LabelClean
  covOptMod 32 (ext := [(⟨"cov_ext", [i64], [i64]⟩, 0)]) (exits := ["cov_ext_exit"])
  (flat := true)

theorem x64_opt_code_eq : covX64OptLeg.code = covX64OptFlat.code := rfl

theorem x64_opt_bounds_eq : covX64OptLeg.bounds = covX64OptFlat.bounds := rfl

noncomputable def covX64OptFlatCast :
    LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean
      (covOptSrcMod.optInlinePolicy covPol)
      [(⟨"cov_ext", [i64], [i64]⟩, 0)] ["cov_ext_exit"] 0 2048 :=
  covX64OptFlat.castModule covOptMod.eq

#eval auditMainFlatClosure

#print axioms x64_opt_code_eq
#print axioms x64_opt_bounds_eq
#print axioms covX64OptLeg
#print axioms covX64OptFlat
#print axioms covX64OptFlatCast

end LeanQbeTest.T.CompilerCoverageX64OptTest