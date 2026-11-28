/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import LeanQbe.T.MainLinkReuseCover
import LeanQbe.T.Arm64.KissatPlainCert2
import LeanQbe.T.Arm64.KissatPlainBounds
import LeanQbe.T.Examples.Kissat.Plain
meta import Lean
meta import LeanQbe.T.MainLinkReuseElab
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Arm64.KissatPlainBounds
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Examples.Kissat.Plain1
meta import LeanQbe.T.Examples.Kissat.Plain

/-!
# Kissat Plain Arm64 Relinked Reuse Dry-Run (`MainLinkReuseM7Arm64Test`)

Dual-arch AAPCS64 Arm64 companion to `MainLinkReuseM7DryRunTest`: verifies `eval_raw_callees!`,
`eval_pruned_ext!`, `calleesCover_of_checkRaw`, `CalleesCoverBundle`, and `relinkLinkedCertCover`
on `LeanQbe.T.Arm64.KissatPlainCert2` under a shifted `plainExtPrefix 15`.
-/

set_option autoImplicit false

section

namespace LeanQbeTest.T.MainLinkReuseM7Arm64Test

open LeanQbe.T LeanQbe.T.Arm64 Kraken
open LeanQbe.T.Arm64.KissatPlainCert2
open LeanQbe.T.Arm64.KissatPlainBounds
open LeanQbe.T.Examples.Kissat.Plain

eval_raw_callees! armS2Callees armLegalTarget ((plainFns.drop 15).take 14)
eval_pruned_ext! armS2PrunedExt armS2Callees (plainExtPrefix 15)

/-- Shifted Arm64 Plain prefix (`+ 8` on every uncalled `[0, 15)` entry). -/
def shiftedArmExt15 : List (SigEntry × Nat) :=
  (plainExtPrefix 15).map fun p =>
    if armS2Callees.any (SigEntry.beq p.1) then p else (p.1, p.2 + 8)

/-- Unpruned `checkLinkList` fails on the shifted Arm64 prefix. -/
theorem arm_unpruned_shifted_rejected :
    checkLinkList armLayout shiftedArmExt15 cert2.chunks = false := by
  t_kernel_rfl

private theorem arm_s2_raw_chk :
    checkRawCallsCover armLegalTarget ((plainFns.drop 15).take 14) armS2Callees = true := by
  t_kernel_rfl

noncomputable def armS2Bundle :
    CalleesCoverBundle armLegalTarget ((plainFns.drop 15).take 14) :=
  CalleesCoverBundle.ofCheckRaw armS2Callees
    (wf_of_take_drop 15 14 plainFns_wf) arm_s2_raw_chk

noncomputable def armS2TargetMod : Module := { fns := (plainFns.drop 15).take 14 }

private theorem arm_s2_eq : armS2TargetMod.fns = slice2Mod.fns :=
  rfl

private theorem arm_s2_cov :
    CalleesCover armLegalTarget (chunksFns cert2.chunks) armS2Callees := by
  rw [← cert2.fns_eq]
  dsimp only [slice2Mod]
  simpa [armS2Bundle] using armS2Bundle.cover

private theorem arm_s2_agree :
    checkChunksExtAgreeOn armS2Callees cert2.chunks armS2PrunedExt = true := by
  t_kernel_rfl

private theorem arm_s2_relink_chk :
    checkChunksExt shiftedArmExt15
      (relinkChunkListCover cert2.chunks armS2PrunedExt armS2Callees
        arm_s2_cov arm_s2_agree) = true := by
  t_kernel_rfl

/-- Relinked Arm64 `LinkedCert` under `shiftedArmExt15`, preserving code and stack bounds. -/
noncomputable def ax_arm_s2 :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean
      armS2TargetMod shiftedArmExt15 [] 0 2048 :=
  relinkLinkedCertCover cert2 arm_s2_eq armS2PrunedExt armS2Callees
    arm_s2_cov arm_s2_agree arm_s2_relink_chk

theorem arm_s2_reuses_code_bounds :
    ax_arm_s2.code = cert2.code ∧ ax_arm_s2.bounds = cert2.bounds :=
  ⟨relinkLinkedCertCover_code _ _ _ _ _ _ _, relinkLinkedCertCover_bounds _ _ _ _ _ _ _⟩

#print axioms ax_arm_s2

end LeanQbeTest.T.MainLinkReuseM7Arm64Test
