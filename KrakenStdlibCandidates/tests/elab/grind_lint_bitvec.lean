import KrakenStdlibCandidates
import Std
import Lean.Elab.Tactic.Grind.LintExceptions

open Lean.Grind in #remove_toint_instances

/-! `BitVec` exceptions -/

/-! Check BitVec namespace: -/

#guard_msgs in
#grind_lint inspect (min := 21) BitVec.msb_extractLsb

/--
info: instantiating `BitVec.msb_signExtend` triggers 28 additional `grind` theorem instantiations
---
info: Try this to display the actual theorem instances:
  [apply] set_option trace.grind.ematch.instance true in
  #grind_lint inspect  (min := 21)BitVec.msb_signExtend
-/
#guard_msgs in
#grind_lint inspect (min := 21) BitVec.msb_signExtend

/--
info: instantiating `BitVec.toInt_shiftLeftZeroExtend` triggers 45 additional `grind` theorem instantiations
---
info: Try this to display the actual theorem instances:
  [apply] set_option trace.grind.ematch.instance true in
  #grind_lint inspect  (min := 21)BitVec.toInt_shiftLeftZeroExtend
-/
#guard_msgs in
#grind_lint inspect (min := 21) BitVec.toInt_shiftLeftZeroExtend

/-
info: instantiating `BitVec.append_assoc` triggers 61 additional `grind` theorem instantiations
---
info: BitVec.append_assoc
[thm] instances
  [thm] Nat.or_comm ↦ 16
  [thm] Nat.or_assoc ↦ 10
  [thm] BitVec.isLt ↦ 6
  [thm] BitVec.toNat_injective' ↦ 6
  [thm] Nat.pow_pos ↦ 6
  [thm] BitVec.cast_cast ↦ 4
  [thm] BitVec.toNat_append ↦ 4
  [thm] BitVec.cast_eq ↦ 2
  [thm] BitVec.toNat_cast ↦ 2
  [thm] Nat.shiftLeft_or_distrib ↦ 2
  [thm] BitVec.append_assoc ↦ 1
  [thm] BitVec.append_assoc' ↦ 1
  [thm] Nat.shiftLeft_add ↦ 1
---
info: instantiating `BitVec.append_assoc'` triggers 57 additional `grind` theorem instantiations
---
info: BitVec.append_assoc'
[thm] instances
  [thm] Nat.or_comm ↦ 16
  [thm] BitVec.isLt ↦ 6
  [thm] BitVec.toNat_injective' ↦ 6
  [thm] Nat.or_assoc ↦ 6
  [thm] Nat.pow_pos ↦ 6
  [thm] BitVec.cast_cast ↦ 4
  [thm] BitVec.toNat_append ↦ 4
  [thm] BitVec.cast_eq ↦ 2
  [thm] BitVec.toNat_cast ↦ 2
  [thm] Nat.shiftLeft_or_distrib ↦ 2
  [thm] BitVec.append_assoc ↦ 1
  [thm] BitVec.append_assoc' ↦ 1
  [thm] Nat.shiftLeft_add ↦ 1
---
info: instantiating `BitVec.extractLsb'_append_eq_ite` triggers 21 additional `grind` theorem instantiations
---
info: instantiating `BitVec.getMsbD_ofNatLT` triggers 90 additional `grind` theorem instantiations
---
info: BitVec.getMsbD_ofNatLT
[thm] instances
  [thm] BitVec.getMsbD_eq_getLsbD ↦ 8
  [thm] BitVec.getMsbD_ofNatLT ↦ 8
  [thm] BitVec.getMsbD_of_ge ↦ 8
  [thm] BitVec.getMsbD_setWidth ↦ 8
  [thm] BitVec.getElem_eq_testBit_toNat ↦ 7
  [thm] BitVec.getLsbD_eq_getElem ↦ 7
  [thm] BitVec.getLsbD_ofNatLT ↦ 7
  [thm] BitVec.getLsbD_of_ge ↦ 7
  [thm] Nat.pow_pos ↦ 7
  [thm] Nat.testBit_eq_decide_div_mod_eq ↦ 7
  [thm] Nat.testBit_mod_two_pow ↦ 7
  [thm] BitVec.isLt ↦ 1
  [thm] BitVec.ofNatLT_eq_ofNat ↦ 1
  [thm] BitVec.ofNatLT_toNat ↦ 1
  [thm] BitVec.ofNat_toNat ↦ 1
  [thm] BitVec.setWidth_ofNat_of_le ↦ 1
  [thm] BitVec.toNat_injective' ↦ 1
  [thm] BitVec.toNat_ofNat ↦ 1
  [thm] BitVec.toNat_ofNatLT ↦ 1
  [thm] BitVec.toNat_setWidth ↦ 1
---
info: instantiating `BitVec.getMsbD_shiftLeftZeroExtend` triggers 24 additional `grind` theorem instantiations
---
info: instantiating `BitVec.msb_append` triggers 23 additional `grind` theorem instantiations
---
info: instantiating `BitVec.msb_extractLsb'` triggers 24 additional `grind` theorem instantiations
---
info: instantiating `BitVec.msb_rotateRight` triggers 22 additional `grind` theorem instantiations
---
info: instantiating `BitVec.msb_setWidth` triggers 23 additional `grind` theorem instantiations
---
info: instantiating `BitVec.ofBool_append` triggers 25 additional `grind` theorem instantiations
---
info: instantiating `BitVec.signExtend_and` triggers 53 additional `grind` theorem instantiations
---
info: BitVec.signExtend_and
[thm] instances
  [thm] BitVec.isLt ↦ 9
  [thm] Nat.and_comm ↦ 4
  [thm] BitVec.getLsbD_eq_getElem ↦ 3
  [thm] BitVec.getLsbD_last ↦ 3
  [thm] BitVec.getLsbD_of_ge ↦ 3
  [thm] BitVec.getMsbD_eq_getLsbD ↦ 3
  [thm] BitVec.getMsbD_of_ge ↦ 3
  [thm] BitVec.msb_eq_false_iff_two_mul_lt ↦ 3
  [thm] BitVec.msb_eq_getMsbD_zero ↦ 3
  [thm] BitVec.toNat_setWidth ↦ 3
  [thm] BitVec.toNat_signExtend ↦ 3
  [thm] Nat.pow_pos ↦ 3
  [thm] BitVec.toNat_and ↦ 2
  [thm] BitVec.toNat_injective' ↦ 2
  [thm] BitVec.getLsbD_and ↦ 1
  [thm] BitVec.signExtend_and ↦ 1
---
info: instantiating `BitVec.signExtend_not` triggers 35 additional `grind` theorem instantiations
---
info: instantiating `BitVec.signExtend_or` triggers 49 additional `grind` theorem instantiations
---
info: instantiating `BitVec.signExtend_xor` triggers 49 additional `grind` theorem instantiations
---
info: instantiating `BitVec.sshiftRight'_ofNat_eq_sshiftRight` triggers 21 additional `grind` theorem instantiations
---
info: instantiating `BitVec.toFin_and` triggers 22 additional `grind` theorem instantiations
---
info: instantiating `BitVec.toFin_ofNatLT` triggers 24 additional `grind` theorem instantiations
---
info: instantiating `BitVec.toFin_rotateLeft` triggers 25 additional `grind` theorem instantiations
---
info: instantiating `BitVec.toFin_rotateRight` triggers 25 additional `grind` theorem instantiations
---
info: instantiating `BitVec.toFin_setWidth'` triggers 23 additional `grind` theorem instantiations
---
info: instantiating `BitVec.toFin_shiftLeftZeroExtend` triggers 21 additional `grind` theorem instantiations
---
info: instantiating `BitVec.toInt_and` triggers 34 additional `grind` theorem instantiations
---
info: instantiating `BitVec.toInt_or` triggers 32 additional `grind` theorem instantiations
---
info: instantiating `BitVec.toInt_setWidth'_of_lt` triggers 32 additional `grind` theorem instantiations
---
info: instantiating `BitVec.toInt_shiftLeftZeroExtend` triggers 42 additional `grind` theorem instantiations
---
info: instantiating `BitVec.toInt_xor` triggers 32 additional `grind` theorem instantiations
---
info: Try this:
  [apply] #grind_lint check  (min := 20) in BitVec
  #grind_lint inspect BitVec.append_assoc
  #grind_lint inspect BitVec.append_assoc'
  #grind_lint inspect BitVec.extractLsb'_append_eq_ite
  #grind_lint inspect BitVec.getMsbD_ofNatLT
  #grind_lint inspect BitVec.getMsbD_shiftLeftZeroExtend
  #grind_lint inspect BitVec.msb_append
  #grind_lint inspect BitVec.msb_extractLsb'
  #grind_lint inspect BitVec.msb_rotateRight
  #grind_lint inspect BitVec.msb_setWidth
  #grind_lint inspect BitVec.ofBool_append
  #grind_lint inspect BitVec.signExtend_and
  #grind_lint inspect BitVec.signExtend_not
  #grind_lint inspect BitVec.signExtend_or
  #grind_lint inspect BitVec.signExtend_xor
  #grind_lint inspect BitVec.sshiftRight'_ofNat_eq_sshiftRight
  #grind_lint inspect BitVec.toFin_and
  #grind_lint inspect BitVec.toFin_ofNatLT
  #grind_lint inspect BitVec.toFin_rotateLeft
  #grind_lint inspect BitVec.toFin_rotateRight
  #grind_lint inspect BitVec.toFin_setWidth'
  #grind_lint inspect BitVec.toFin_shiftLeftZeroExtend
  #grind_lint inspect BitVec.toInt_and
  #grind_lint inspect BitVec.toInt_or
  #grind_lint inspect BitVec.toInt_setWidth'_of_lt
  #grind_lint inspect BitVec.toInt_shiftLeftZeroExtend
  #grind_lint inspect BitVec.toInt_xor
-/
-- #guard_msgs in
-- #grind_lint check  (min := 20) in BitVec
