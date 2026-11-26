module

public import LeanQbe.T.Arm64.IselLemmas30
public import LeanQbe.T.Arm64.IselLemmas31

/-!
# AArch64 Scalar Instruction Selection Proofs — Part 3

Weakest-precondition correctness for `armDivRemOp`, `bswap`, `clz`/`cls`/`rbit`/`ctz`,
`armCmpOp`, `armSelectOp`, `armAddcOp`, and `armSubbOp`.
-/

set_option autoImplicit false
