/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Spec.HdrView
public import LeanQbe.T.Examples.Kissat.Proof.Spec.HdrViewEquiv
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts2
public import LeanQbe.T.Logic.CanonicalEnv
public import LeanQbe.T.Logic.C0Step
public import Kraken.Mem

/-!
# Verification Tests for `Kissat.Proof.Spec.HdrView` & `HdrViewEquiv`

1. `HdrView.decode_ofCfg`, `@[simp]` field projection, and single-word update preservation
   (`HdrView.decode_set`, `HdrView.decode_set_of_none`, `HdrView.decode_hdrWordField_set`).
2. `HdrModifies` and `HdrWsModifies` framing algebra (`refl`, `trans`, `mono`,
   `get_of_not_mem`, `set`) collapsing multi-step header framing to one-liners.
3. Bidirectional `Spec.Le`, `↔`, `Spec.XFree`, and `Env.Has.of_le` adapters for
   `fullInitPtrsSpec`, `fullInitArenasSpec`, `fullSweepCopySpec`, and `fullAnalyzeRsnSpec`.
4. `#print axioms` checks (`<= std3`).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.KissatHdrViewTest

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Proof.Spec

/-! ## 1. `HdrView.decode`, `ofCfg` & Single-Word Update Simp Automation -/

example (c : FullCfg) (s : FullState) :
    (HdrView.decode (hdrTailWords c s)).map (fun v => (v.arenaCap, v.pVals, v.pLastLearned)) =
      some (BitVec.ofNat 64 c.arena_cap, c.pVals, c.pLastLearned) := by
  simp

example (c : FullCfg) (s : FullState) :
    HdrView.decode ((hdrTailWords c s).set 2 42#64) = some (HdrView.ofCfg c) := by
  simp [show HdrField.ofTailIdx? 2 = none from rfl]

example (c : FullCfg) (s : FullState) (w : BitVec 64) :
    HdrView.decode ((hdrTailWords c s).set HdrField.pVals.tailIdx w) =
      some ((HdrView.ofCfg c).set .pVals w) := by
  simp

example (c : FullCfg) (s : FullState) (w1 w2 : BitVec 64) :
    let ws1 := (hdrTailWords c s).set HdrField.arenaCap.tailIdx w1
    let ws2 := ws1.set HdrField.wcap.tailIdx w2
    ∃ v, HdrView.decode ws2 = some v ∧ v.get .pVals = c.pVals ∧
      v.get .arenaCap = w1 ∧ v.get .wcap = w2 := by
  refine ⟨((HdrView.ofCfg c).set .arenaCap w1).set .wcap w2, by simp, by simp, by simp, by simp⟩

theorem hdrWordField_arena_len_preserves_hdrView (c : FullCfg) (s : FullState) (v : BitVec 64) :
    HdrView.decode (hdrTailWords c (HdrWordField.arena_len.set s v)) = some (HdrView.ofCfg c) :=
  HdrView.decode_hdrWordField_set (wf := .arena_len) rfl v rfl

/-! ## 2. `HdrModifies` & `HdrWsModifies` Framing Automation -/

theorem frame_two_updates (v : HdrView) (w1 w2 : BitVec 64) :
    let v1 := v.set .arenaCap w1
    let v2 := v1.set .wcap w2
    HdrModifies [.arenaCap, .wcap] v v2 ∧ v2.get .pVals = v.get .pVals ∧
      v2.get .pHeap = v.get .pHeap := by
  have hm : HdrModifies [.arenaCap, .wcap] v ((v.set .arenaCap w1).set .wcap w2) :=
    (HdrModifies.set_singleton v .arenaCap w1).trans (HdrModifies.set_singleton _ .wcap w2)
  exact ⟨hm, hm.get_of_not_mem (by decide), hm.get_of_not_mem (by decide)⟩

theorem frame_mono_example (v1 v2 v3 : HdrView)
    (h12 : HdrModifies [.arenaCap] v1 v2) (h23 : HdrModifies [.wcap] v2 v3) :
    HdrModifies HdrField.arenaDynFields v1 v3 :=
  (h12.trans h23).mono (by decide)

theorem ws_frame_example (ws : List (BitVec 64)) (w : BitVec 64) :
    HdrWsModifies [.pVals] ws (ws.set HdrField.pVals.tailIdx w) :=
  HdrWsModifies.set w (by simp)

/-! ## 3. Bidirectional Spec Equivalences & `Env.Has` Transport -/

theorem initPtrs_roundtrip (a : Tup Val [i64, i64, i64]) (m : Mem 64) (Q : Post []) (X : XPost) :
    fullInitPtrsSpec a m Q X ↔ fullInitPtrsHdrSpec a m Q X :=
  fullInitPtrsSpec_iff_hdr a m Q X

theorem initArenas_roundtrip (a : Tup Val [i64, i64, i64, i64]) (m : Mem 64)
    (Q : Post []) (X : XPost) :
    fullInitArenasSpec a m Q X ↔ fullInitArenasHdrSpec a m Q X :=
  fullInitArenasSpec_iff_hdr a m Q X

theorem sweepCopy_roundtrip (a : Tup Val [i64, i64, i64, i32, .bool]) (m : Mem 64)
    (Q : Post [i64]) (X : XPost) :
    fullSweepCopySpec a m Q X ↔ fullSweepCopyHdrSpec a m Q X :=
  fullSweepCopySpec_iff_hdr a m Q X

theorem analyzeRsn_roundtrip (a : Tup Val [i64, i32, i32]) (m : Mem 64)
    (Q : Post [.bool]) (X : XPost) :
    fullAnalyzeRsnSpec a m Q X ↔ fullAnalyzeRsnHdrSpec a m Q X :=
  fullAnalyzeRsnSpec_iff_hdr a m Q X

example (Γ : Env) (h : Γ.Has "full_init_ptrs" fullInitPtrsSpec) :
    Γ.Has "full_init_ptrs" fullInitPtrsHdrSpec :=
  h.of_le fullInitPtrsHdrSpec_le

example (Γ : Env) (h : Γ.Has "full_init_arenas" fullInitArenasSpec) :
    Γ.Has "full_init_arenas" fullInitArenasHdrSpec :=
  h.of_le fullInitArenasHdrSpec_le

example (Γ : Env) (h : Γ.Has "full_sweep_copy" fullSweepCopySpec) :
    Γ.Has "full_sweep_copy" fullSweepCopyHdrSpec :=
  h.of_le fullSweepCopyHdrSpec_le

example (Γ : Env) (h : Γ.Has "full_analyze_rsn" fullAnalyzeRsnSpec) :
    Γ.Has "full_analyze_rsn" fullAnalyzeRsnHdrSpec :=
  h.of_le fullAnalyzeRsnHdrSpec_le

example : Spec.XFree fullInitPtrsHdrSpec := fullInitPtrsHdrSpec_xfree
example : Spec.XFree fullInitArenasHdrSpec := fullInitArenasHdrSpec_xfree
example : Spec.XFree fullSweepCopyHdrSpec := fullSweepCopyHdrSpec_xfree
example : Spec.XFree fullAnalyzeRsnHdrSpec := fullAnalyzeRsnHdrSpec_xfree

end LeanQbeTest.T.KissatHdrViewTest

#print axioms LeanQbe.T.Examples.Kissat.Proof.Spec.HdrView.decode_ofCfg
#print axioms LeanQbe.T.Examples.Kissat.Proof.Spec.HdrView.decode_eq_some_iff
#print axioms LeanQbe.T.Examples.Kissat.Proof.Spec.HdrView.decode_set
#print axioms LeanQbe.T.Examples.Kissat.Proof.Spec.HdrView.decode_set_of_none
#print axioms LeanQbe.T.Examples.Kissat.Proof.Spec.HdrModifies.trans
#print axioms LeanQbe.T.Examples.Kissat.Proof.Spec.HdrModifies.mono
#print axioms LeanQbe.T.Examples.Kissat.Proof.Spec.fullInitPtrsSpec_iff_hdr
#print axioms LeanQbe.T.Examples.Kissat.Proof.Spec.fullInitArenasSpec_iff_hdr
#print axioms LeanQbe.T.Examples.Kissat.Proof.Spec.fullSweepCopySpec_iff_hdr
#print axioms LeanQbe.T.Examples.Kissat.Proof.Spec.fullAnalyzeRsnSpec_iff_hdr
#print axioms LeanQbeTest.T.KissatHdrViewTest.frame_two_updates
#print axioms LeanQbeTest.T.KissatHdrViewTest.frame_mono_example
#print axioms LeanQbeTest.T.KissatHdrViewTest.initPtrs_roundtrip
#print axioms LeanQbeTest.T.KissatHdrViewTest.initArenas_roundtrip
#print axioms LeanQbeTest.T.KissatHdrViewTest.sweepCopy_roundtrip
#print axioms LeanQbeTest.T.KissatHdrViewTest.analyzeRsn_roundtrip