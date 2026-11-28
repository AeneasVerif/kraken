/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import LeanQbe.T.MainLinkReuseCover
import LeanQbe.T.Amd64.KissatPlainCert2
import LeanQbe.T.Amd64.KissatPlainCert5
import LeanQbe.T.Amd64.KissatPlainBounds
import LeanQbe.T.Examples.Kissat.Plain
meta import Lean
meta import LeanQbe.T.MainLinkReuseElab
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Amd64.KissatPlainBounds
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Examples.Kissat.Plain1
meta import LeanQbe.T.Examples.Kissat.Plain

/-!
# Kissat Plain x64 Relinked Reuse Dry-Run & Benchmark (`MainLinkReuseM7DryRunTest`)

End-to-end SysV x64 dry-run over real `KissatPlainCert2` (`[15, 29)`, `14` fns, `4` chunks)
and `KissatPlainCert5` (`[47, 52)`, `5` fns, `2` chunks):

1. Uses `eval_raw_callees!` + `eval_pruned_ext!` and `calleesCover_of_checkRaw` (Option B) +
   `CalleesCoverBundle.of_eq` (Option A) to certify callee covers without running `Fn.mid`.
2. Relinks multi-chunk `LinkedCert`s both at nominal prefixes (`plainExtPrefix 15`) and under a
   perturbed `shiftedPlainExt47` where verbatim `checkLinkList` fails (`false`) while
   `relinkLinkedCertCover` produces a verified `LinkedCert` preserving code and stack bounds.
-/

set_option autoImplicit false

section

namespace LeanQbeTest.T.MainLinkReuseM7DryRunTest

open LeanQbe.T LeanQbe.T.Amd64 Kraken
open LeanQbe.T.Amd64.KissatPlainCert2
open LeanQbe.T.Amd64.KissatPlainCert5
open LeanQbe.T.Amd64.KissatPlainBounds
open LeanQbe.T.Examples.Kissat.Plain

/-! ## 1. Slice 2 (`KissatPlainCert2`, `[15, 29)`, `14` fns, `4` chunks) -/

eval_raw_callees! s2Callees x64LegalTarget ((plainFns.drop 15).take 14)
eval_pruned_ext! s2PrunedExt s2Callees (plainExtPrefix 15)

private theorem s2_raw_chk :
    checkRawCallsCover x64LegalTarget ((plainFns.drop 15).take 14) s2Callees = true := by
  t_kernel_rfl

/-- Option A bundle built via Option B raw check (`0` `Fn.mid` kernel evaluation). -/
noncomputable def s2Bundle :
    CalleesCoverBundle x64LegalTarget ((plainFns.drop 15).take 14) :=
  CalleesCoverBundle.ofCheckRaw s2Callees (wf_of_take_drop 15 14 plainFns_wf) s2_raw_chk

/-- Target slice 2 module. -/
noncomputable def s2TargetMod : Module := { fns := (plainFns.drop 15).take 14 }

private theorem s2_eq_chunks : s2TargetMod.fns = slice2Mod.fns :=
  rfl

private theorem s2_chunks_cov :
    CalleesCover x64LegalTarget (chunksFns cert2.chunks) s2Callees := by
  rw [← cert2.fns_eq]
  dsimp only [slice2Mod]
  simpa [s2Bundle] using s2Bundle.cover

private theorem s2_agree :
    checkChunksExtAgreeOn s2Callees cert2.chunks s2PrunedExt = true := by
  t_kernel_rfl

private theorem s2_relink_chk :
    checkChunksExt (plainExtPrefix 15)
      (relinkChunkListCover cert2.chunks s2PrunedExt s2Callees
        s2_chunks_cov s2_agree) = true := by
  t_kernel_rfl

/-- Reused & pruned `LinkedCert` for `s2TargetMod` against `plainExtPrefix 15`. -/
noncomputable def ax_s2_cert :
    LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean
      s2TargetMod (plainExtPrefix 15) [] 0 2048 :=
  relinkLinkedCertCover cert2 s2_eq_chunks s2PrunedExt s2Callees
    s2_chunks_cov s2_agree s2_relink_chk

/-- Code and bounds are identical (`rfl`) to `KissatPlainCert2.cert2`. -/
theorem s2_reuses_code_bounds :
    ax_s2_cert.code = cert2.code ∧ ax_s2_cert.bounds = cert2.bounds :=
  ⟨relinkLinkedCertCover_code _ _ _ _ _ _ _, relinkLinkedCertCover_bounds _ _ _ _ _ _ _⟩

/-! ## 2. Slice 5 (`KissatPlainCert5`, `[47, 52)`, `5` fns, `2` chunks) + shifted prefix -/

eval_raw_callees! s5Callees x64LegalTarget ((plainFns.drop 47).take 5)
eval_pruned_ext! s5PrunedExt s5Callees (plainExtPrefix 47)

/-- Synthetic shifted prefix: bumps bounds (`+ 8`) on every uncalled prefix entry, simulating
upstream regalloc/frame-size changes before `[47, 52)`. -/
def shiftedPlainExt47 : List (SigEntry × Nat) :=
  (plainExtPrefix 47).map fun p =>
    if s5Callees.any (SigEntry.beq p.1) then p else (p.1, p.2 + 8)

/-- Without callee pruning, verbatim `checkLinkList` rejects `cert5.chunks`. -/
theorem unpruned_shifted_rejected :
    checkLinkList x64Layout shiftedPlainExt47 cert5.chunks = false := by
  t_kernel_rfl

private theorem s5_raw_chk :
    checkRawCallsCover x64LegalTarget ((plainFns.drop 47).take 5) s5Callees = true := by
  t_kernel_rfl

/-- Option A bundle for slice 5 transported by `O(1)` `of_eq`. -/
noncomputable def s5Bundle :
    CalleesCoverBundle x64LegalTarget ((plainFns.drop 47).take 5) :=
  (CalleesCoverBundle.ofCheckRaw s5Callees
    (wf_of_take_drop 47 5 plainFns_wf) s5_raw_chk).of_eq rfl

/-- Option B direct `calleesCover_rawLegal` soundness theorem without reflection. -/
theorem ax_s5_raw :
    CalleesCover x64LegalTarget ((plainFns.drop 47).take 5)
      (rawLegalCalleesOf x64LegalTarget ((plainFns.drop 47).take 5)) :=
  calleesCover_rawLegal x64LegalTarget (wf_of_take_drop 47 5 plainFns_wf)

/-- Target slice 5 module. -/
noncomputable def s5TargetMod : Module := { fns := (plainFns.drop 47).take 5 }

private theorem s5_eq_chunks : s5TargetMod.fns = slice5Mod.fns :=
  rfl

private theorem s5_chunks_cov :
    CalleesCover x64LegalTarget (chunksFns cert5.chunks) s5Callees := by
  rw [← cert5.fns_eq]
  dsimp only [slice5Mod]
  simpa [s5Bundle] using s5Bundle.cover

private theorem s5_agree :
    checkChunksExtAgreeOn s5Callees cert5.chunks s5PrunedExt = true := by
  t_kernel_rfl

private theorem s5_relink_chk :
    checkChunksExt shiftedPlainExt47
      (relinkChunkListCover cert5.chunks s5PrunedExt s5Callees
        s5_chunks_cov s5_agree) = true := by
  t_kernel_rfl

/-- Pruned & relinked `LinkedCert` for `s5TargetMod` under `shiftedPlainExt47`. -/
noncomputable def ax_s5_cert :
    LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean
      s5TargetMod shiftedPlainExt47 [] 0 2048 :=
  relinkLinkedCertCover cert5 s5_eq_chunks s5PrunedExt s5Callees
    s5_chunks_cov s5_agree s5_relink_chk

/-- Relinking preserves `cert5`'s exact emitted code and stack bounds. -/
theorem s5_reuses_code_bounds :
    ax_s5_cert.code = cert5.code ∧ ax_s5_cert.bounds = cert5.bounds :=
  ⟨relinkLinkedCertCover_code _ _ _ _ _ _ _, relinkLinkedCertCover_bounds _ _ _ _ _ _ _⟩

/-! ## 3. Axiom audit (`std3` only) -/

#print axioms LeanQbe.T.calleesCover_of_checkRaw
#print axioms LeanQbe.T.calleesCover_rawLegal
#print axioms LeanQbe.T.relinkLinkedCertCover
#print axioms ax_s2_cert
#print axioms ax_s5_raw
#print axioms ax_s5_cert

end LeanQbeTest.T.MainLinkReuseM7DryRunTest
