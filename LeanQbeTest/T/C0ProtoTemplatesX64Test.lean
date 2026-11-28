module

meta import LeanQbeTest.T.C0ProtoTemplatesTest
meta import LeanQbe.T.Driver
meta import LeanQbe.T.Amd64.Isa

/-!
# Amd64 Backend Compilation Check for C0 Template Instances

Kept separate from `LeanQbeTest.T.C0ProtoTemplatesArm64Test` because `Kraken.X64` and
`Kraken.AArch64` cannot both be imported into the same Lean environment.
-/

set_option autoImplicit false

namespace LeanQbeTest.T.C0ProtoTemplatesX64Test

open LeanQbe.T
open LeanQbeTest.T.C0ProtoTemplatesTest

#guard (Driver.compileFns Amd64.x64Isa Amd64.x64LegalTarget concreteFns).isOk

end LeanQbeTest.T.C0ProtoTemplatesX64Test
