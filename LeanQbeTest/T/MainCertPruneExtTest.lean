/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import LeanQbe.T.MainCertSlices
import LeanQbe.T.Amd64.TargLemmas
import LeanQbeTest.T.Common.Fixtures
import LeanQbe.T.FlatLemmas
meta import Lean
import LeanQbe.T.MainCertElab
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbeTest.T.Common.Fixtures

/-!
# Pruned-`ext` (`N4`) & 2-Level Balanced `MainCertSlices` Tree (`N6`) Tests

Fast kernel-checked verification (`std3` axioms only, `0` `sorry`, `0` `MainLinkReuseCover`):
1. `compile_linked_chunks! ... (pruneExt := true)` emits ONLY direct `ext.callees` bounds in
   `c{i}_ext`, passing kernel `compileModule` `Eq.refl` and `checkLinkList`.
2. **Automatic verbatim reuse across upstream changes (`0` `MainLinkReuseCover` boilerplate):**
   adding an uncalled upstream function (`fnExtra`) AND shifting an uncalled upstream function's
   stack bound (`fnUnusedHeavy` vs `fnUnusedLight`) leaves a `(pruneExt := true)` slice 100%
   verbatim-reusable via `ChunkSlice.ofCert` + `LinkedCert.ofChunkSlices` + `checkLinkList`!
3. `eval_prefix_ext! ... (pruneFor := ...)` computes minimal per-slice callee bounds directly.
4. 2-level balanced `CheckedSliceGroup` + `LinkedCert.ofCheckedGroups` tree linking (`N6`).
-/

set_option autoImplicit false

section

namespace LeanQbeTest.T.MainCertPruneExtTest

open LeanQbe.T LeanQbe.T.Amd64
open LeanQbeTest.T.Common.Fixtures

/-! ## 1. Base Module (`v1`: `[fnUsed, fnUnusedLight, fnCaller, fnTop]`) -/

/-- Direct callee of `fnCaller`. -/
def fnUsed : Fn :=
  ⟨"p_used", [i64], [i64], fun _ _ (x, ()) =>
    .let_ ⟨.add i64, (.var x, .imm 7#64, ())⟩ fun (r, ()) =>
    .ret (.var r, ())⟩

/-- Uncalled upstream leaf (small stack bound). -/
def fnUnusedLight : Fn :=
  ⟨"p_unused", [i64], [i64], fun _ _ (x, ()) =>
    .ret (.var x, ())⟩

/-- Extra uncalled upstream function inserted in `v2`. -/
def fnExtra : Fn :=
  ⟨"p_extra", [i64], [i64], fun _ _ (x, ()) =>
    .let_ ⟨.add i64, (.var x, .imm 1#64, ())⟩ fun (r, ()) =>
    .ret (.var r, ())⟩

/-- Uncalled upstream function with a shifted (larger) stack bound in `v2` (calls `p_extra`). -/
def fnUnusedHeavy : Fn :=
  ⟨"p_unused", [i64], [i64], fun _ _ (x, ()) =>
    .call "p_extra" (as := [i64]) (bs := [i64]) (.var x, ()) fun (a, ()) =>
    .call "p_extra" (as := [i64]) (bs := [i64]) (.var a, ()) fun (b, ()) =>
    .let_ ⟨.add i64, (.var a, .var b, ())⟩ fun (s, ()) =>
    .ret (.var s, ())⟩

/-- Calls ONLY `p_used` (never `p_unused` or `p_extra`). -/
def fnCaller : Fn :=
  ⟨"p_caller", [i64], [i64], fun _ _ (x, ()) =>
    .call "p_used" (as := [i64]) (bs := [i64]) (.var x, ()) fun (y, ()) =>
    .let_ ⟨.add i64, (.var y, .var x, ())⟩ fun (z, ()) =>
    .ret (.var z, ())⟩

/-- Top entry calling `p_caller`. -/
def fnTop : Fn :=
  ⟨"p_top", [i64], [i64], fun _ _ (x, ()) =>
    .call "p_caller" (as := [i64]) (bs := [i64]) (.var x, ()) fun (y, ()) =>
    .ret (.var y, ())⟩

def modV1 : Module := { fns := [fnUsed, fnUnusedLight, fnCaller, fnTop] }
def modV2 : Module := { fns := [fnExtra, fnUsed, fnUnusedHeavy, fnCaller, fnTop] }

theorem modV1_len : modV1.fns.length = 4 := by rfl
theorem modV2_len : modV2.fns.length = 5 := by rfl

abbrev v1Slice1Mod : Module := { fns := modV1.fns.take 2 }
abbrev v1Slice2Mod : Module := { fns := modV1.fns.drop 2 }

compile_linked_chunks! certV1S1
  x64Target x64Layout x64LegalTarget x64LabelClean v1Slice1Mod 1 (pruneExt := true)

eval_prefix_ext! extV1S1Pruned
  x64Target x64LegalTarget (modV1.fns.take 2) (pruneFor := v1Slice2Mod.fns)

compile_linked_chunks! certV1S2
  x64Target x64Layout x64LegalTarget x64LabelClean v1Slice2Mod 1
  (ext := extV1S1Pruned) (pruneExt := true)

/-! Confirm `extV1S1Pruned` and `c0_ext` contain ONLY `p_used` (length 1, omitting `p_unused`). -/

theorem pruned_prefix_len : extV1S1Pruned.length = 1 := rfl
theorem pruned_c0_ext_len : certV1S2.aux.c0_ext.length = 1 := rfl
theorem pruned_c0_ext_name : certV1S2.aux.c0_ext.map (fun p => p.1.1) = ["p_used"] := rfl
theorem pruned_c1_ext_len : certV1S2.aux.c1_ext.length = 1 := rfl
theorem pruned_c1_ext_name : certV1S2.aux.c1_ext.map (fun p => p.1.1) = ["p_caller"] := rfl

noncomputable def v1Slices :
    List (ChunkSlice x64Target x64LegalTarget [] 0 2048 modV1.fns) :=
  [ ChunkSlice.ofCert 0 2 certV1S1 rfl
  , ChunkSlice.ofDrop 2 2 certV1S2 modV1_len (by decide) rfl ]

theorem v1Slices_link :
    checkLinkList x64Layout [] (ChunkSlice.allChunks v1Slices) = true := by
  t_kernel_rfl

noncomputable def certV1 :
    LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean modV1 [] [] 0 2048 :=
  LinkedCert.ofChunkSlices v1Slices modV1_len (by decide) v1Slices_link

/-! ## 2. Verbatim Reuse of `certV1S2` Inside `modV2` (Added `fnExtra` + Shifted `fnUnused`) -/

abbrev v2PrefixMod : Module := { fns := modV2.fns.take 3 }

compile_linked_chunks! certV2Prefix
  x64Target x64Layout x64LegalTarget x64LabelClean v2PrefixMod 1 (pruneExt := true)

/-- Confirm `p_unused` actually changed stack bound between `v1` and `v2`. -/
theorem unused_bound_shifted :
    certV1S1.aux.c1_bounds ≠ certV2Prefix.aux.c2_bounds := by
  decide

theorem v2_tail_eq : modV2.fns.drop 3 = v1Slice2Mod.fns := by rfl

/-- Reuse `certV1S2` **100% verbatim** in `modV2` with ZERO `MainLinkReuseCover`! -/
noncomputable def v2Slices :
    List (ChunkSlice x64Target x64LegalTarget [] 0 2048 modV2.fns) :=
  [ ChunkSlice.ofCert 0 3 certV2Prefix rfl
  , ChunkSlice.ofDrop 3 2 certV1S2 modV2_len (by decide) v2_tail_eq ]

theorem v2Slices_link :
    checkLinkList x64Layout [] (ChunkSlice.allChunks v2Slices) = true := by
  t_kernel_rfl

noncomputable def certV2VerbatimReuse :
    LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean modV2 [] [] 0 2048 :=
  LinkedCert.ofChunkSlices v2Slices modV2_len (by decide) v2Slices_link

/-! ## 3. 2-Level Balanced `CheckedSliceGroup` + `LinkedCert.ofCheckedGroups` Tree (`N6`) -/

theorem certMod_len : certMod.fns.length = 6 := rfl

compile_linked_chunks! pS1
  x64Target x64Layout x64LegalTarget x64LabelClean slice1Mod 1 (pruneExt := true)

eval_prefix_ext! pExt1 x64Target x64LegalTarget (autoFns.take 2) (pruneFor := slice2Mod.fns)

compile_linked_chunks! pS2
  x64Target x64Layout x64LegalTarget x64LabelClean slice2Mod 1 (ext := pExt1) (pruneExt := true)

eval_prefix_ext! pExt2 x64Target x64LegalTarget (autoFns.take 4) (pruneFor := slice3Mod.fns)

compile_linked_chunks! pS3
  x64Target x64Layout x64LegalTarget x64LabelClean slice3Mod 1 (ext := pExt2) (pruneExt := true)

noncomputable def treeSl1 :
    ChunkSlice x64Target x64LegalTarget [] 0 2048 certMod.fns :=
  ChunkSlice.ofCert 0 2 pS1 rfl

noncomputable def treeSl2 :
    ChunkSlice x64Target x64LegalTarget [] 0 2048 certMod.fns :=
  ChunkSlice.ofCert 2 2 pS2 rfl

noncomputable def treeSl3 :
    ChunkSlice x64Target x64LegalTarget [] 0 2048 certMod.fns :=
  ChunkSlice.ofDrop 4 2 pS3 certMod_len (by decide) rfl

noncomputable def grp0Slice :
    ChunkSlice x64Target x64LegalTarget [] 0 2048 certMod.fns :=
  ChunkSlice.ofSlices 0 4 [treeSl1, treeSl2] (by decide)

noncomputable def grp1Slice :
    ChunkSlice x64Target x64LegalTarget [] 0 2048 certMod.fns :=
  ChunkSlice.ofSlices 4 2 [treeSl3] (by decide)

noncomputable def grp0ExtIn : List (SigEntry × Nat) := []
noncomputable def grp1ExtIn : List (SigEntry × Nat) :=
  chunksNextExt grp0ExtIn grp0Slice.chunks

theorem grp0_ext : checkChunksExt grp0ExtIn grp0Slice.chunks = true := by t_kernel_rfl
theorem grp1_ext : checkChunksExt grp1ExtIn grp1Slice.chunks = true := by t_kernel_rfl

noncomputable def treeGroups :
    List (CheckedSliceGroup x64Target x64LegalTarget [] 0 2048 certMod.fns) :=
  [ ⟨grp0Slice, grp0ExtIn, grp0_ext⟩
  , ⟨grp1Slice, grp1ExtIn, grp1_ext⟩ ]

theorem treeGroups_meta :
    checkLinkMeta x64Layout (ChunkSlice.allChunks (treeGroups.map (·.slice))) = true := by
  t_kernel_rfl

noncomputable def certTree :
    LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean certMod [] [] 0 2048 :=
  LinkedCert.ofCheckedGroups treeGroups certMod_len (by decide)
    ⟨rfl, rfl, trivial⟩ treeGroups_meta

/-! ## 4. Single-Line `< 115c` Standard-Axiom Audit -/

noncomputable abbrev ax_v1 := certV1
noncomputable abbrev ax_v2_reuse := certV2VerbatimReuse
noncomputable abbrev ax_tree := certTree

#print axioms ax_v1
#print axioms ax_v2_reuse
#print axioms ax_tree

end LeanQbeTest.T.MainCertPruneExtTest

end
