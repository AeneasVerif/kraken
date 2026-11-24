/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.MainLinkReuseCover
public import LeanQbe.T.Arm64.KissatM7PlusCert2
public import LeanQbe.T.Arm64.KissatM7FidelityBounds
public import LeanQbe.T.Examples.Kissat.FullM7FidelityM7PlusBridge
public import LeanQbe.T.Examples.Kissat.FullM7PlusAssemblyProof0
public import LeanQbe.T.Examples.Kissat.FullM7InlPolicy
meta import Lean
meta import LeanQbe.T.MainLinkReuseElab
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Arm64.KissatM7FidelityBounds
meta import LeanQbe.T.Examples.Kissat.FullM7PlusInl

/-!
# Kissat M7Plus -> M7Fidelity Arm64 Relinked Reuse Dry-Run (`MainLinkReuseM7Arm64Test`)

Dual-arch AAPCS64 Arm64 companion to `MainLinkReuseM7DryRunTest`: verifies `eval_raw_callees!`,
`eval_pruned_ext!`, `calleesCover_of_checkRaw`, `CalleesCoverBundle`, and `relinkLinkedCertCover`
on `LeanQbe.T.Arm64.KissatM7PlusCert2` under a shifted `m7FidelityExtPrefix 12`.
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.MainLinkReuseM7Arm64Test

open LeanQbe.T LeanQbe.T.Arm64 Kraken
open LeanQbe.T.Arm64.KissatM7PlusCert2
open LeanQbe.T.Arm64.KissatM7FidelityBounds
open LeanQbe.T.Examples.Kissat.FullM7Plus
open LeanQbe.T.Examples.Kissat.FullM7PlusInl
open LeanQbe.T.Examples.Kissat.FullM7InlPolicy
open LeanQbe.T.Examples.Kissat.FullM7FidelityInl
open LeanQbe.T.Examples.Kissat.FullM7FidelityM7PlusBridge

private theorem m7PlusInlFns_wf : ∀ f ∈ m7PlusInlFns, f.Wf := by
  have hwf := Module.optInlinePolicy_wf m7InlPolicy m7Plus_acyclic m7PlusFns_wf
  rw [← m7PlusInlMod.eq] at hwf
  exact hwf

eval_raw_callees! armS2Callees armLegalTarget ((m7PlusInlFns.drop 12).take 12)
eval_pruned_ext! armS2PrunedExt armS2Callees (m7FidelityExtPrefix 12)

/-- Shifted Arm64 Fidelity prefix (`+ 8` on every uncalled `[0, 12)` entry). -/
def shiftedArmExt12 : List (SigEntry × Nat) :=
  (m7FidelityExtPrefix 12).map fun p =>
    if armS2Callees.any (SigEntry.beq p.1) then p else (p.1, p.2 + 8)

/-- Unpruned `checkLinkList` fails on the shifted Arm64 prefix. -/
theorem arm_unpruned_shifted_rejected :
    checkLinkList armLayout shiftedArmExt12 cert2.chunks = false := by
  t_kernel_rfl

private theorem arm_s2_raw_chk :
    checkRawCallsCover armLegalTarget ((m7PlusInlFns.drop 12).take 12) armS2Callees = true := by
  t_kernel_rfl

def armS2Bundle : CalleesCoverBundle armLegalTarget ((m7PlusInlFns.drop 12).take 12) :=
  CalleesCoverBundle.ofCheckRaw armS2Callees
    (wf_of_take_drop 12 12 m7PlusInlFns_wf) arm_s2_raw_chk

def armS2FidMod : Module := { fns := (m7FidInlFns.drop 12).take 12 }

private theorem arm_s2_fid_eq : armS2FidMod.fns = slice2Mod.fns := by
  simpa [armS2FidMod, slice2Mod] using reuse_m7p_eq_2

private theorem arm_s2_cov :
    CalleesCover armLegalTarget (chunksFns cert2.chunks) armS2Callees := by
  rw [← cert2.fns_eq]
  dsimp only [slice2Mod]
  simpa [armS2Bundle] using armS2Bundle.cover

private theorem arm_s2_agree :
    checkChunksExtAgreeOn armS2Callees cert2.chunks armS2PrunedExt = true := by
  t_kernel_rfl

private theorem arm_s2_relink_chk :
    checkChunksExt shiftedArmExt12
      (relinkChunkListCover cert2.chunks armS2PrunedExt armS2Callees
        arm_s2_cov arm_s2_agree) = true := by
  t_kernel_rfl

/-- Relinked Arm64 `LinkedCert` under `shiftedArmExt12`, preserving code and stack bounds. -/
noncomputable def ax_arm_s2 :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean
      armS2FidMod shiftedArmExt12 [] 0 2048 :=
  relinkLinkedCertCover cert2 arm_s2_fid_eq armS2PrunedExt armS2Callees
    arm_s2_cov arm_s2_agree arm_s2_relink_chk

theorem arm_s2_reuses_code_bounds :
    ax_arm_s2.code = cert2.code ∧ ax_arm_s2.bounds = cert2.bounds :=
  ⟨relinkLinkedCertCover_code _ _ _ _ _ _ _, relinkLinkedCertCover_bounds _ _ _ _ _ _ _⟩

#print axioms ax_arm_s2

end LeanQbeTest.T.MainLinkReuseM7Arm64Test
