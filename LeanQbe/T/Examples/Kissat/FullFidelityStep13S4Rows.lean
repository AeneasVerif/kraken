/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S4EVSIDSReorder
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S4Analysis
public import LeanQbe.T.Examples.Kissat.PatchModule

/-!
# Kissat Fidelity Step 13 Shard S4 Data-Pure Patch Barrel (`FullFidelityStep13S4Rows`)

Data-pure barrel (`0` `*Proof*`/`*Spec*`/`*Lemmas*` imports, passing
`check_firewall.py --require-isa --data-proof`) exporting all `18` Step-13 S4 functions
(`15` replacements + `3` inserted helpers), name lists, nodup proofs, and `Func.Wf` bundles.

Proof rows (`fidStep13S4ReplRows`, `fidStep13S4BeforeRows`), `checkCallsOk`, and parametric
`SpecEntry.Impl` proofs live in `FullFidelityStep13S4RowsProof.lean`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S4

open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.PatchModule

@[expose] public section

/-- Combined `15` signature-preserving Step-13 S4 replacement functions (`6` S4-A + `9` S4-B). -/
def fidStep13S4Repls : List Fn :=
  fidStep13S4ARepls ++ fidStep13S4BRepls

/-- Combined `3` inserted Step-13 S4 helper functions anchored in exact `step13` C0 order. -/
def fidStep13S4Befores : List (Sym × List Fn) :=
  [ ("full_bump_analyzed_m6_hdr",
      [fidStep13S4AnalyzeReasonsFidFn, fidStep13S4BumpAnalyzedModeFidFn])
  , ("full_restore_bump_ana_m6_hdr", [fidStep13S4RestoreBumpAnaModeFidFn]) ]

/-- Names of the `15` Step-13 S4 replacement functions in exact order. -/
def fidStep13S4ReplNames : List Sym :=
  [ "full_rescale_m6"
  , "full_bump_var"
  , "full_bump_decay"
  , "full_sort_ana_qs_m6"
  , "full_lucky_scan"
  , "full_reorder_queue_m7"
  , "full_analyze_rsn_m6_hdr"
  , "full_bump_analyzed_m6_hdr"
  , "full_restore_bump_ana_m6_hdr"
  , "full_ana_failed_lit_m6_hdr"
  , "full_min_lit_dfs_m8"
  , "full_shrink_blk_bool_m8"
  , "full_min_shrink_m6"
  , "full_analyze_core_m6"
  , "full_analyze_m6_hdr" ]

/-- Names of the `3` Step-13 S4 inserted helper functions in exact order. -/
def fidStep13S4BeforeNames : List Sym :=
  [ "full_analyze_reasons_fid"
  , "full_bump_analyzed_mode_fid"
  , "full_restore_bump_ana_mode_fid" ]

end

public section

theorem fidStep13S4Repls_map_name :
    fidStep13S4Repls.map Fn.name = fidStep13S4ReplNames :=
  rfl

theorem fidStep13S4Befores_map_name :
    (fidStep13S4Befores.flatMap Prod.snd).map Fn.name = fidStep13S4BeforeNames :=
  rfl

theorem fidStep13S4ReplNames_nodup : fidStep13S4ReplNames.Nodup := by decide

theorem fidStep13S4BeforeNames_nodup : fidStep13S4BeforeNames.Nodup := by decide

theorem fidStep13S4Repls_wf : ∀ f ∈ fidStep13S4Repls, f.Wf := by
  intro f hf
  rw [fidStep13S4Repls, List.mem_append] at hf
  rcases hf with h1 | h2
  · exact fidStep13S4ARepls_wf f h1
  · exact fidStep13S4BRepls_wf f h2

theorem fidStep13S4Befores_wf : ∀ f ∈ fidStep13S4Befores.flatMap Prod.snd, f.Wf := by
  intro f hf
  simp only [fidStep13S4Befores, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · exact fidStep13S4AnalyzeReasonsFid_wf
  · exact fidStep13S4BumpAnalyzedModeFid_wf
  · exact fidStep13S4RestoreBumpAnaModeFid_wf

end

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S4
