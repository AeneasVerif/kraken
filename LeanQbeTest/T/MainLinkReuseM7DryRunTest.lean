/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.MainLinkReuseCover
public import LeanQbe.T.Amd64.KissatM7PlusCert2
public import LeanQbe.T.Amd64.KissatM7PlusCert44
public import LeanQbe.T.Amd64.KissatM7FidelityBounds
public import LeanQbe.T.Examples.Kissat.FullM7FidelityM7PlusBridge
public import LeanQbe.T.Examples.Kissat.FullM7PlusAssemblyProof0
public import LeanQbe.T.Examples.Kissat.FullM7InlPolicy
meta import Lean
meta import LeanQbe.T.MainLinkReuseElab
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Amd64.KissatM7FidelityBounds
meta import LeanQbe.T.Examples.Kissat.FullM7PlusInl

/-!
# Kissat M7Plus -> M7Fidelity Relinked Reuse Dry-Run & Benchmark (`MainLinkReuseM7DryRunTest`)

End-to-end SysV x64 dry-run over real `KissatM7PlusCert2` (`[12, 24)`, `12` fns, `3` chunks)
and `KissatM7PlusCert44` (`[333, 340)`, `7` fns, `2` chunks):

1. Proves `∀ f ∈ m7PlusInlFns, f.Wf` via `Module.optInlinePolicy_wf` without walking ASTs.
2. Uses `eval_raw_callees!` + `eval_pruned_ext!` and `calleesCover_of_checkRaw` (Option B) +
   `CalleesCoverBundle.of_eq` (Option A) to certify callee covers without running `Fn.mid`.
3. Relinks multi-chunk `LinkedCert`s into `m7FidInlFns` (`FullM7FidelityM7PlusBridge`) both at
   nominal prefixes and under a perturbed `shiftedFidExt333` where verbatim `checkLinkList`
   fails (`false`) while `relinkLinkedCertCover` produces a verified `LinkedCert`.
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.MainLinkReuseM7DryRunTest

open LeanQbe.T LeanQbe.T.Amd64 Kraken
open LeanQbe.T.Amd64.KissatM7PlusCert2
open LeanQbe.T.Amd64.KissatM7PlusCert44
open LeanQbe.T.Amd64.KissatM7FidelityBounds
open LeanQbe.T.Examples.Kissat.FullM7Plus
open LeanQbe.T.Examples.Kissat.FullM7PlusInl
open LeanQbe.T.Examples.Kissat.FullM7InlPolicy
open LeanQbe.T.Examples.Kissat.FullM7FidelityInl
open LeanQbe.T.Examples.Kissat.FullM7FidelityM7PlusBridge

/-- All `410` inlined functions of `m7PlusInlFns` are well-formed (`Fn.Wf`). -/
theorem m7PlusInlFns_wf : ∀ f ∈ m7PlusInlFns, f.Wf := by
  have hwf := Module.optInlinePolicy_wf m7InlPolicy m7Plus_acyclic m7PlusFns_wf
  rw [← m7PlusInlMod.eq] at hwf
  exact hwf

/-! ## 1. Slice 2 (`KissatM7PlusCert2`, `[12, 24)`, `12` fns, `3` chunks) -> M7Fidelity -/

eval_raw_callees! s2Callees x64LegalTarget ((m7PlusInlFns.drop 12).take 12)
eval_pruned_ext! s2PrunedExt s2Callees (m7FidelityExtPrefix 12)

private theorem s2_raw_chk :
    checkRawCallsCover x64LegalTarget ((m7PlusInlFns.drop 12).take 12) s2Callees = true := by
  t_kernel_rfl

/-- Option A bundle built via Option B raw check (`0` `Fn.mid` kernel evaluation). -/
noncomputable def s2Bundle :
    CalleesCoverBundle x64LegalTarget ((m7PlusInlFns.drop 12).take 12) :=
  CalleesCoverBundle.ofCheckRaw s2Callees (wf_of_take_drop 12 12 m7PlusInlFns_wf) s2_raw_chk

/-- Target slice 2 module in `FullM7FidelityInl`. -/
noncomputable def s2FidMod : Module := { fns := (m7FidInlFns.drop 12).take 12 }

private theorem s2_fid_eq_chunks : s2FidMod.fns = slice2Mod.fns := by
  simpa [s2FidMod, slice2Mod] using reuse_m7p_eq_2

private theorem s2_chunks_cov :
    CalleesCover x64LegalTarget (chunksFns cert2.chunks) s2Callees := by
  rw [← cert2.fns_eq]
  dsimp only [slice2Mod]
  simpa [s2Bundle] using s2Bundle.cover

private theorem s2_agree :
    checkChunksExtAgreeOn s2Callees cert2.chunks s2PrunedExt = true := by
  t_kernel_rfl

private theorem s2_relink_chk :
    checkChunksExt (m7FidelityExtPrefix 12)
      (relinkChunkListCover cert2.chunks s2PrunedExt s2Callees
        s2_chunks_cov s2_agree) = true := by
  t_kernel_rfl

/-- Reused & pruned `LinkedCert` for `s2FidMod` against `m7FidelityExtPrefix 12`. -/
noncomputable def ax_s2_cert :
    LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean
      s2FidMod (m7FidelityExtPrefix 12) [] 0 2048 :=
  relinkLinkedCertCover cert2 s2_fid_eq_chunks s2PrunedExt s2Callees
    s2_chunks_cov s2_agree s2_relink_chk

/-- Code and bounds are identical (`rfl`) to `KissatM7PlusCert2.cert2`. -/
theorem s2_reuses_code_bounds :
    ax_s2_cert.code = cert2.code ∧ ax_s2_cert.bounds = cert2.bounds :=
  ⟨relinkLinkedCertCover_code _ _ _ _ _ _ _, relinkLinkedCertCover_bounds _ _ _ _ _ _ _⟩

/-! ## 2. Slice 44 (`KissatM7PlusCert44`, `[333, 340)`, `7` fns, `2` chunks) + shifted prefix -/

eval_raw_callees! s44Callees x64LegalTarget ((m7PlusInlFns.drop 333).take 7)
eval_pruned_ext! s44PrunedExt s44Callees (m7FidelityExtPrefix 333)

/-- Synthetic M7p -> M7f shifted prefix: bumps bounds (`+ 8`) on every uncalled prefix entry,
simulating upstream regalloc/frame-size changes before `[333, 340)`. -/
def shiftedFidExt333 : List (SigEntry × Nat) :=
  (m7FidelityExtPrefix 333).map fun p =>
    if s44Callees.any (SigEntry.beq p.1) then p else (p.1, p.2 + 8)

/-- Without callee pruning, verbatim `checkLinkList` rejects `cert44.chunks`. -/
theorem unpruned_shifted_rejected :
    checkLinkList x64Layout shiftedFidExt333 cert44.chunks = false := by
  t_kernel_rfl

private theorem s44_raw_chk :
    checkRawCallsCover x64LegalTarget ((m7PlusInlFns.drop 333).take 7) s44Callees = true := by
  t_kernel_rfl

/-- Option A bundle for slice 44 transported by `O(1)` `of_eq` onto `m7FidInlFns`. -/
noncomputable def s44BundleFid :
    CalleesCoverBundle x64LegalTarget ((m7FidInlFns.drop 333).take 7) :=
  (CalleesCoverBundle.ofCheckRaw s44Callees
    (wf_of_take_drop 333 7 m7PlusInlFns_wf) s44_raw_chk).of_eq reuse_m7p_eq_44

/-- Option B direct `calleesCover_rawLegal` soundness theorem without reflection. -/
theorem ax_s44_raw :
    CalleesCover x64LegalTarget ((m7FidInlFns.drop 333).take 7)
      (rawLegalCalleesOf x64LegalTarget ((m7FidInlFns.drop 333).take 7)) := by
  rw [reuse_m7p_eq_44]
  exact calleesCover_rawLegal x64LegalTarget (wf_of_take_drop 333 7 m7PlusInlFns_wf)

/-- Target slice 44 module in `FullM7FidelityInl`. -/
noncomputable def s44FidMod : Module := { fns := (m7FidInlFns.drop 333).take 7 }

private theorem s44_fid_eq_chunks : s44FidMod.fns = slice44Mod.fns := by
  simpa [s44FidMod, slice44Mod] using reuse_m7p_eq_44

private theorem s44_chunks_cov :
    CalleesCover x64LegalTarget (chunksFns cert44.chunks) s44Callees := by
  rw [← cert44.fns_eq]
  dsimp only [slice44Mod]
  simpa [s44BundleFid] using s44BundleFid.cover.of_eq reuse_m7p_eq_44.symm

private theorem s44_agree :
    checkChunksExtAgreeOn s44Callees cert44.chunks s44PrunedExt = true := by
  t_kernel_rfl

private theorem s44_relink_chk :
    checkChunksExt shiftedFidExt333
      (relinkChunkListCover cert44.chunks s44PrunedExt s44Callees
        s44_chunks_cov s44_agree) = true := by
  t_kernel_rfl

/-- Pruned & relinked `LinkedCert` for `s44FidMod` under `shiftedFidExt333`. -/
noncomputable def ax_s44_cert :
    LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean
      s44FidMod shiftedFidExt333 [] 0 2048 :=
  relinkLinkedCertCover cert44 s44_fid_eq_chunks s44PrunedExt s44Callees
    s44_chunks_cov s44_agree s44_relink_chk

/-- Relinking preserves `cert44`'s exact emitted code and stack bounds. -/
theorem s44_reuses_code_bounds :
    ax_s44_cert.code = cert44.code ∧ ax_s44_cert.bounds = cert44.bounds :=
  ⟨relinkLinkedCertCover_code _ _ _ _ _ _ _, relinkLinkedCertCover_bounds _ _ _ _ _ _ _⟩

/-! ## 3. Axiom audit (`std3` only) -/

#print axioms LeanQbe.T.calleesCover_of_checkRaw
#print axioms LeanQbe.T.calleesCover_rawLegal
#print axioms LeanQbe.T.relinkLinkedCertCover
#print axioms ax_s2_cert
#print axioms ax_s44_raw
#print axioms ax_s44_cert

end LeanQbeTest.T.MainLinkReuseM7DryRunTest
