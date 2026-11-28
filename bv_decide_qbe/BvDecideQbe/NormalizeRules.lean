module

public import BvDecideQbe.NormalizeTheorems
public import Lean.Meta.Tactic.BVDecide.Attr

/-!
# Scoped `[bv_normalize]` Registration & Rule Name Tables (`E0 / H7` + `H6a`)

Re-exports the zero-axiom theorems from `BvDecideQbe.NormalizeTheorems` and provides:
1. Strictly `scoped` `[bv_normalize]` registrations inside `BvDecideQbe.NormalizeRules`.
2. Programmatic `Array Lean.Name` rule tables for `bv_cut_qbe` and `trySimpNormalizeRules`.
-/

set_option autoImplicit false

public section

namespace BvDecideQbe.NormalizeRules

attribute [scoped bv_normalize]
  mul_one_shiftLeft one_shiftLeft_mul
  mul_one_shiftLeft_bv one_shiftLeft_mul_bv
  mul_ofNat_one_shiftLeft ofNat_one_shiftLeft_mul
  mul_ofNat_one_shiftLeft_bv ofNat_one_shiftLeft_mul_bv
  mul_ofNat_two_pow ofNat_two_pow_mul
  ite_add_left ite_add_right ite_sub_left ite_sub_right
  ite_mul_left ite_mul_right ite_and_left ite_and_right
  ite_or_left ite_or_right ite_xor_left ite_xor_right
  ite_shiftLeft_nat_left ite_shiftLeft_nat_right
  ite_shiftLeft_bv_left ite_shiftLeft_bv_right
  ite_shiftRight_nat_left ite_shiftRight_nat_right
  ite_shiftRight_bv_left ite_shiftRight_bv_right
  ite_sshiftRight_left ite_sshiftRight_right
  ite_sshiftRight'_left ite_sshiftRight'_right
  cond_add_left cond_add_right cond_sub_left cond_sub_right
  cond_mul_left cond_mul_right cond_and_left cond_and_right
  cond_or_left cond_or_right cond_xor_left cond_xor_right
  cond_shiftLeft_nat_left cond_shiftLeft_nat_right
  cond_shiftLeft_bv_left cond_shiftLeft_bv_right
  cond_shiftRight_nat_left cond_shiftRight_nat_right
  cond_shiftRight_bv_left cond_shiftRight_bv_right
  cond_sshiftRight_left cond_sshiftRight_right
  cond_sshiftRight'_left cond_sshiftRight'_right

/-- `shiftmul` rewrite theorem names for explicit `simp only` / `bv_cut_qbe`. -/
def shiftmulRuleNames : Array Lean.Name := #[
  ``mul_one_shiftLeft, ``one_shiftLeft_mul,
  ``mul_one_shiftLeft_bv, ``one_shiftLeft_mul_bv,
  ``mul_ofNat_one_shiftLeft, ``ofNat_one_shiftLeft_mul,
  ``mul_ofNat_one_shiftLeft_bv, ``ofNat_one_shiftLeft_mul_bv,
  ``mul_ofNat_two_pow, ``ofNat_two_pow_mul
]

/-- `opt_share` rewrite theorem names (`ite` + `cond`) for explicit `simp only` / `bv_cut_qbe`. -/
def optShareRuleNames : Array Lean.Name := #[
  ``ite_add_left, ``ite_add_right, ``ite_sub_left, ``ite_sub_right,
  ``ite_mul_left, ``ite_mul_right, ``ite_and_left, ``ite_and_right,
  ``ite_or_left, ``ite_or_right, ``ite_xor_left, ``ite_xor_right,
  ``ite_shiftLeft_nat_left, ``ite_shiftLeft_nat_right,
  ``ite_shiftLeft_bv_left, ``ite_shiftLeft_bv_right,
  ``ite_shiftRight_nat_left, ``ite_shiftRight_nat_right,
  ``ite_shiftRight_bv_left, ``ite_shiftRight_bv_right,
  ``ite_sshiftRight_left, ``ite_sshiftRight_right,
  ``ite_sshiftRight'_left, ``ite_sshiftRight'_right,
  ``cond_add_left, ``cond_add_right, ``cond_sub_left, ``cond_sub_right,
  ``cond_mul_left, ``cond_mul_right, ``cond_and_left, ``cond_and_right,
  ``cond_or_left, ``cond_or_right, ``cond_xor_left, ``cond_xor_right,
  ``cond_shiftLeft_nat_left, ``cond_shiftLeft_nat_right,
  ``cond_shiftLeft_bv_left, ``cond_shiftLeft_bv_right,
  ``cond_shiftRight_nat_left, ``cond_shiftRight_nat_right,
  ``cond_shiftRight_bv_left, ``cond_shiftRight_bv_right,
  ``cond_sshiftRight_left, ``cond_sshiftRight_right,
  ``cond_sshiftRight'_left, ``cond_sshiftRight'_right
]

/-- Combined `H7` normalizer rewrite rule names (`shiftmul` + `opt_share`). -/
def normalizeRuleNames : Array Lean.Name :=
  shiftmulRuleNames ++ optShareRuleNames

/-- Constant `shl → mul` rewrite theorem names used before `grind` ring dispatch (`H6a`). -/
def shiftLeftToMulRuleNames : Array Lean.Name := #[
  ``BitVec.shiftLeft_eq_mul_twoPow,
  ``shiftLeft_bv_ofNat_eq_mul_twoPow
]

/-- Constant-folding theorem names turning `BitVec.twoPow` into concrete `BitVec.ofNat`
(paired with `Simp.getSimprocs` for `BitVec.reduceHShiftLeft` / `BitVec.reduceShiftLeft`). -/
def twoPowReduceRuleNames : Array Lean.Name := #[
  ``BitVec.twoPow_eq,
  ``BitVec.toNat_ofNat
]

end BvDecideQbe.NormalizeRules
