module

public import LeanQbe.T.RegaLemmas3a
public import LeanQbe.T.RegaLemmas3b

/-!
# `RegaLemmas` Part 3: Operands, Ops/Loads/Stores, and Structural `LabelsUnique`

* `tryArg_ok`, `pickPArgs_ok`, `tryAddr_ok`, `lowerOp_ok`, `lowerLoad_ok`, `lowerStore_ok`.
* Structural label bounds (`LabelClean`, `lname_inj`, `lowerExpr_labels`/`lowerBlocks_labels`):
  every
  label emitted by `lowerExpr` is `lname fn j` with `j ∈ [nl, nl')`, pairwise distinct, via monotone
  `nl` (no `O(L^2)` `decide`); `lowerFn_labelsUnique`, `lowerFn_label_mem`, `lowerExpr_nv_le`.
-/

set_option autoImplicit false
