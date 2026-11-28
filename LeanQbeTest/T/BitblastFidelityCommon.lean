/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import LeanQbe.T.Examples.Bitblast.FidelityBridgeLemmas
import LeanQbe.T.Examples.Kissat.Proof.Full
meta import LeanQbe.T.Examples.Bitblast.FidelityBridgeLemmas
meta import LeanQbe.T.Examples.Kissat.Proof.Full

/-!
# Shared Arch-Free Linked Proof Bridge for `Bitblast` + `Kissat` (`BitblastFidelityCommon`)

Re-exports the legacy-free parametric `Bitblast` + `Proof.Spec.KissatUnsatPkg` linked WP bridge
from `LeanQbe.T.Examples.Bitblast.FidelityBridgeLemmas` and instantiates it on the canonical
`418 + 64 = 482`-function `Proof.Full` + `Bitblast.Src.Full` linked module (`<= std3`,
`0` externs, `0` exits, `0` legacy `Full*` imports), alongside concrete `#guard` sanity checks.
-/

set_option autoImplicit false

section

namespace LeanQbeTest.T.BitblastFidelityCommon

open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Src.Full
open LeanQbe.T.Examples.Kissat.Src.InlPolicy
open LeanQbe.T.Examples.Kissat.Proof
open LeanQbe.T.Examples.Kissat.Proof.Full
open LeanQbe.T.Examples.Bitblast.Src.Full

export LeanQbe.T.Examples.Bitblast.FidelityBridgeLemmas
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
    nvSlab_bvSolveBytesSpec )

private theorem fidFull_bitblast_names_disj_bool :
    (kissatModule.fns.map Fn.name).all
      (fun s => !(bitblastModule.fns.map Fn.name).contains s) = true := by
  t_kernel_rfl

/-- Zero name collisions between `Src.Full.kissatModule.fns` (`418` fns) and
`bitblastModule.fns` (`64` fns). -/
theorem fidFull_bitblast_names_disj :
    ∀ s ∈ kissatModule.fns.map Fn.name, s ∉ bitblastModule.fns.map Fn.name := by
  intro s hs hbb
  have h1 := List.all_eq_true.mp fidFull_bitblast_names_disj_bool s hs
  rw [List.contains_iff_mem.mpr hbb] at h1
  cases h1

/-- Closed `482`-function un-inlined `Kissat Src.Full + Bitblast` module
(`0` externs, `0` exits). -/
def bitblastFidFullLinkedMod : Module :=
  { fns := kissatModule.fns ++ bitblastModule.fns, externs := [], exits := [] }

/-- Closed `482`-function PGO-inlined `Kissat Src.Full + Bitblast` module (`0` externs,
`0` exits) — exact module emitted by `bv_decide_qbe`. -/
def bitblastFidFullInlLinkedMod : Module :=
  { fns := (kissatModule.optInlinePolicy kissatInlPolicy).fns ++ bitblastModule.fns,
    externs := [], exits := [] }

/-- Closed `482`-function `Env` for `Kissat Proof.Full + Bitblast`. -/
def bitblastFidFullLinkedEnv : Env :=
  bitblastLinkedEnvOfPkg kissatUnsatPkg

theorem bitblastFidFull_moduleOk :
    ModuleOk bitblastFidFullLinkedEnv bitblastFidFullLinkedMod :=
  bitblastLinkedEnv_moduleOk kissatUnsatPkg rfl
    kissatModule_noExterns kissatModule_noExit fidFull_bitblast_names_disj

theorem bitblastFidFullInl_moduleOk :
    ModuleOk bitblastFidFullLinkedEnv bitblastFidFullInlLinkedMod :=
  bitblastInlLinkedEnv_moduleOk kissatUnsatPkg rfl
    kissatModule_noExterns kissatModule_noExit fidFull_bitblast_names_disj

theorem bitblastFidFull_checkAcyclic : bitblastFidFullLinkedMod.checkAcyclic = true :=
  (moduleOk_parts bitblastFidFull_moduleOk).1

theorem bitblastFidFullInl_checkAcyclic : bitblastFidFullInlLinkedMod.checkAcyclic = true :=
  (moduleOk_parts bitblastFidFullInl_moduleOk).1

theorem bitblastFidFull_bvSolveBytesSpec
    {xs : Tup Val [i64, i64, i64, i64, i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (h : LeanQbe.T.Examples.Bitblast.Proof.bvSolveBytesSpec xs m Q X) :
    bitblastFidFullLinkedEnv "bv_solve_bytes" [i64, i64, i64, i64, i64] [i64] xs m Q X :=
  bitblastLinked_bvSolveBytesSpec kissatUnsatPkg h

end LeanQbeTest.T.BitblastFidelityCommon

end

#guard LeanQbeTest.T.BitblastFidelityCommon.bitblastFidFullLinkedMod.fns.length == 482
#guard LeanQbeTest.T.BitblastFidelityCommon.bitblastFidFullInlLinkedMod.fns.length == 482
#guard LeanQbeTest.T.BitblastFidelityCommon.bitblastFidFullLinkedMod.externs.isEmpty
#guard LeanQbeTest.T.BitblastFidelityCommon.bitblastFidFullLinkedMod.exits.isEmpty
