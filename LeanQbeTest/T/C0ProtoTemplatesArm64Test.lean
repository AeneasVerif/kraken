module

meta import LeanQbeTest.T.C0ProtoTemplatesTest
meta import LeanQbe.T.Driver
meta import LeanQbe.T.Arm64.Isa

/-!
# Arm64 Backend Compilation Check for C0 Template Instances

Kept separate from `LeanQbeTest.T.C0ProtoTemplatesX64Test` because `Kraken.X64` and
`Kraken.AArch64` cannot both be imported into the same Lean environment.
-/

set_option autoImplicit false

namespace LeanQbeTest.T.C0ProtoTemplatesArm64Test

open LeanQbe.T
open LeanQbeTest.T.C0ProtoTemplatesTest

#guard (Driver.compileFns Arm64.armIsa Arm64.armLegalTarget concreteFns).isOk

end LeanQbeTest.T.C0ProtoTemplatesArm64Test
