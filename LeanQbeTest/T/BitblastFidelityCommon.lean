/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityBitblastLemmas
meta import LeanQbe.T.Examples.Kissat.FullFidelityBitblastLemmas

/-!
# Shared Arch-Free Linked Proof Bridge for `Bitblast` + `KissatFidelity` (`BitblastFidelityCommon`)

Re-exports the parametric `Bitblast` + `KissatUnsatPkg` linked WP bridge and concrete Step-12
`581`-function (`517 + 64`) `fidStep12UnsatPkg` instantiation from
`LeanQbe.T.Examples.Kissat.FullFidelityBitblastLemmas` (`<= std3`, `0` externs, `0` exits),
alongside concrete `#guard` sanity checks.
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.BitblastFidelityCommon

export LeanQbe.T.Examples.Kissat.FullFidelityBitblastLemmas
  ( kissatSolveBytesUnsatSpec_refines_pkg
    bitblastLinkedModOfPkg
    bitblastInlLinkedModOfPkg
    bitblastLinkedEnvOfPkg
    bitblastLinkedEnv_noExit
    bitblastLinkedEnv_moduleOk
    bitblastInlLinkedEnv_moduleOk
    bitblastLinked_bvSolveBytesSpec
    bvSolveBytesFn_mem_linked
    bvSolveBytesFn_mem_inlLinked
    nvSlabPtr
    nvSlabWorkPtr
    nvSlabBytes
    nvSlabBytes_length
    nvSlabBytes_le_8192
    nvSlab_trivialUnsat
    nvSlab_sep
    nvSlab_bvSolveBytesSpec
    fidStep12_bitblast_names_disj
    bitblastFidStep12LinkedMod
    bitblastFidStep12InlLinkedMod
    bitblastFidStep12LinkedEnv
    bitblastFidStep12_moduleOk
    bitblastFidStep12Inl_moduleOk
    bitblastFidStep12_checkAcyclic
    bitblastFidStep12Inl_checkAcyclic
    bitblastFidStep12_bvSolveBytesSpec )

end LeanQbeTest.T.BitblastFidelityCommon

end

#guard LeanQbeTest.T.BitblastFidelityCommon.bitblastFidStep12LinkedMod.fns.length == 581
#guard LeanQbeTest.T.BitblastFidelityCommon.bitblastFidStep12InlLinkedMod.fns.length == 581
#guard LeanQbeTest.T.BitblastFidelityCommon.bitblastFidStep12LinkedMod.externs.isEmpty
#guard LeanQbeTest.T.BitblastFidelityCommon.bitblastFidStep12LinkedMod.exits.isEmpty
