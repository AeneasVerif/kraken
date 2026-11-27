/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Bitblast.Proof.OpsShiftMul
public import LeanQbe.T.Examples.Bitblast.Proof.OpsShiftMulSpecs
public import LeanQbe.T.Examples.Bitblast.Proof.OpsShiftMul0
public import LeanQbe.T.Examples.Bitblast.Proof.OpsShiftMul1
public import LeanQbe.T.Examples.Bitblast.Proof.OpsShiftMul2
public meta import LeanQbe.T.Examples.Bitblast.Src.OpsShiftMul
public meta import LeanQbe.T.Examples.Bitblast.Proof.OpsShiftMulSpecs
public meta import LeanQbe.T.Examples.Bitblast.Proof.OpsShiftMul

/-!
# Smoke Tests & Axiom Audit for `Bitblast.Proof.OpsShiftMul` (`S4p`)

Verifies `opsShiftMulModule` counts (`12` fns, `8` externs, `20` spec rows), concrete `Mem 64`
buffer sizes, and `#print axioms` (`<= std3`, `<= 100c`) across all `12` canonical `Func.wp`
theorems, `Spec.XFree` lemmas, `opsShiftMul_moduleOk`, closed restricted-env corollaries, and
non-vacuity witnesses.
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.BitblastOpsShiftMulProofTest

open LeanQbe.T.Examples.Bitblast.Src.OpsShiftMul
open LeanQbe.T.Examples.Bitblast.Proof

#guard opsShiftMulModule.fns.length == 12
#guard opsShiftMulModule.externs.length == 8
#guard opsShiftMulSpecTable.length == 20
#guard nvSmBytes.length == 204
#guard nvSmLp.length == 16

#print axioms smBvSliceOkSpec_xfree
#print axioms smBvBlastAddSpec_xfree
#print axioms bvCopyLitsSpec_xfree
#print axioms bvBlastReplicateSpec_xfree
#print axioms bvBlastRotlSpec_xfree
#print axioms bvBlastRotrSpec_xfree
#print axioms bvBlastAshrcSpec_xfree
#print axioms bvBlastReverseSpec_xfree
#print axioms bvBlastShiftVarSpec_xfree
#print axioms bvBlastShlSpec_xfree
#print axioms bvBlastUshrSpec_xfree
#print axioms bvBlastAshrSpec_xfree
#print axioms bvBlastMulSpec_xfree
#print axioms bvBlastClzSpec_xfree
#print axioms opsShiftMulSpecTable_nodup
#print axioms opsShiftMulEnv_sat

#print axioms bv_copy_lits_wp
#print axioms bv_blast_replicate_wp
#print axioms bv_blast_rotl_wp
#print axioms bv_blast_rotr_wp
#print axioms bv_blast_ashrc_wp
#print axioms bv_blast_reverse_wp
#print axioms bv_blast_shift_var_wp
#print axioms bv_blast_shl_wp
#print axioms bv_blast_ushr_wp
#print axioms bv_blast_ashr_wp
#print axioms bv_blast_mul_wp
#print axioms bv_blast_clz_wp

#print axioms opsShiftMul_moduleOk
#print axioms opsShiftMul_restrict_wp
#print axioms bv_blast_mul_closed_wp
#print axioms bv_blast_clz_closed_wp

#print axioms nvSmAigInv_ok
#print axioms nvSmMem_ok
#print axioms nv_bv_copy_lits
#print axioms nv_bv_blast_replicate
#print axioms nv_bv_blast_rotl
#print axioms nv_bv_blast_rotr
#print axioms nv_bv_blast_ashrc
#print axioms nv_bv_blast_reverse
#print axioms nv_bv_blast_shl
#print axioms nv_bv_blast_mul
#print axioms nv_bv_blast_mul_oom
#print axioms nv_bv_blast_clz

end LeanQbeTest.T.BitblastOpsShiftMulProofTest
