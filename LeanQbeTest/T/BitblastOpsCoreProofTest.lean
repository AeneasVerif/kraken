/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import LeanQbe.T.Examples.Bitblast.Proof.OpsCore

/-!
# Bitblast OpsCore Proof Certificate Tests

Checks canonical `Func.wp`, `Env.Has`, `Spec.XFree`, `SegCert`, `ModuleOk`, and standard
axiom footprint (`<= std3`) for all 13 `Bitblast.Src.OpsCore` C0 functions.
-/

set_option autoImplicit false

namespace LeanQbeTest.T.BitblastOpsCoreProofTest

open LeanQbe.T
open LeanQbe.T.Examples.Bitblast.Proof

example : ModuleOk opsCoreEnv Examples.Bitblast.Src.OpsCore.opsCoreModule := opsCore_moduleOk
example : SegCert opsCoreAigExternSpecs Examples.Bitblast.Src.OpsCore.opsCoreFns
    opsCoreOwnSpecTable := opsCore_segCert
example : opsCoreEnv.Has "bv_slice_ok" bvSliceOkSpec := opsCoreEnv_has_bv_slice_ok
example : opsCoreEnv.Has "bv_blast_extract" bvBlastExtractSpec := opsCoreEnv_has_bv_blast_extract
example : opsCoreEnv.Has "bv_blast_append" bvBlastAppendSpec := opsCoreEnv_has_bv_blast_append
example : opsCoreEnv.Has "bv_blast_not" bvBlastNotSpec := opsCoreEnv_has_bv_blast_not
example : opsCoreEnv.Has "bv_blast_bin_bitwise" bvBlastBinBitwiseSpec :=
  opsCoreEnv_has_bv_blast_bin_bitwise
example : opsCoreEnv.Has "bv_blast_and" bvBlastAndSpec := opsCoreEnv_has_bv_blast_and
example : opsCoreEnv.Has "bv_blast_or" bvBlastOrSpec := opsCoreEnv_has_bv_blast_or
example : opsCoreEnv.Has "bv_blast_xor" bvBlastXorSpec := opsCoreEnv_has_bv_blast_xor
example : opsCoreEnv.Has "bv_full_adder_carry" bvFullAdderCarrySpec :=
  opsCoreEnv_has_bv_full_adder_carry
example : opsCoreEnv.Has "bv_blast_add" bvBlastAddSpec := opsCoreEnv_has_bv_blast_add
example : opsCoreEnv.Has "bv_blast_eq" bvBlastEqSpec := opsCoreEnv_has_bv_blast_eq
example : opsCoreEnv.Has "bv_blast_ult" bvBlastUltSpec := opsCoreEnv_has_bv_blast_ult
example : opsCoreEnv.Has "bv_blast_get_lsb_d" bvBlastGetLsbDSpec :=
  opsCoreEnv_has_bv_blast_get_lsb_d

#print axioms opsCore_moduleOk
#print axioms opsCore_modEnv_moduleOk
#print axioms opsCore_segCert
#print axioms opsCoreEnv_noExit
#print axioms bv_slice_ok_wp
#print axioms bv_blast_extract_wp
#print axioms bv_blast_append_wp
#print axioms bv_blast_not_wp
#print axioms bv_blast_bin_bitwise_wp
#print axioms bv_blast_and_wp
#print axioms bv_blast_or_wp
#print axioms bv_blast_xor_wp
#print axioms bv_full_adder_carry_wp
#print axioms bv_blast_add_wp
#print axioms bv_blast_eq_wp
#print axioms bv_blast_ult_wp
#print axioms bv_blast_get_lsb_d_wp
#print axioms opsCoreEnv_has_bv_slice_ok
#print axioms opsCoreEnv_has_bv_blast_extract
#print axioms opsCoreEnv_has_bv_blast_append
#print axioms opsCoreEnv_has_bv_blast_not
#print axioms opsCoreEnv_has_bv_blast_bin_bitwise
#print axioms opsCoreEnv_has_bv_blast_and
#print axioms opsCoreEnv_has_bv_blast_or
#print axioms opsCoreEnv_has_bv_blast_xor
#print axioms opsCoreEnv_has_bv_full_adder_carry
#print axioms opsCoreEnv_has_bv_blast_add
#print axioms opsCoreEnv_has_bv_blast_eq
#print axioms opsCoreEnv_has_bv_blast_ult
#print axioms opsCoreEnv_has_bv_blast_get_lsb_d

end LeanQbeTest.T.BitblastOpsCoreProofTest
