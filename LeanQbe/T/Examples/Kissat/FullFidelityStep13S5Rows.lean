/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S5ReduceProbe
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S5VivifyBackbone
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S5BVAFactor

/-!
# Kissat Fidelity Step 13 Shard S5 Data-Pure Patch Barrel (`FullFidelityStep13S5Rows`)

Data-pure barrel (`0` `*Proof*` imports, passing `check_firewall.py --require-isa --data-proof`)
combining all `28` Shard `S5` functions (`27` sig-preserving replacements + `1` inserted helper
`full_viv_recompute_promote_fid` before `full_viv_deduce_m6`):
- S5-A (`8` MOD): `FullFidelityStep13S5ReduceProbe`
- S5-B (`1` ADD + `13` MOD): `FullFidelityStep13S5VivifyBackbone`
- S5-C (`6` MOD): `FullFidelityStep13S5BVAFactor`
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S5

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.FullFidelityStep13S5ReduceProbe
open LeanQbe.T.Examples.Kissat.FullFidelityStep13S5VivifyBackbone
open LeanQbe.T.Examples.Kissat.FullFidelityStep13S5BVAFactor

@[expose] public section

/-- Combined `27` signature-preserving Step-13 Shard S5 replacement functions. -/
def fidStep13S5Repls : List Fn :=
  fidStep13S5ARepls ++ fidStep13S5BRepls ++ fidStep13S5CRepls

/-- Combined Step-13 Shard S5 helper insertions (`+1`: `full_viv_recompute_promote_fid` before
`full_viv_deduce_m6`). -/
def fidStep13S5Befores : List (Sym × List Fn) :=
  fidStep13S5ABefores ++ fidStep13S5BBefores ++ fidStep13S5CBefores

/-- Ordered names of all `27` Shard S5 replacement functions. -/
def fidStep13S5ReplNames : List Sym :=
  [ "full_activate_lit_fid"
  , "full_parse_body_m6"
  , "full_sort_reds"
  , "full_reduce_m6"
  , "full_set_inactive"
  , "full_probe_tail_m6"
  , "full_probe_m6"
  , "full_preprocess_m6"
  , "full_viv_commit_m6"
  , "full_viv_mark_garb_m6"
  , "full_viv_deduce_m6"
  , "full_viv_finish_m6"
  , "full_vivify_tier_m6_hdr"
  , "full_vivify_m6_hdr"
  , "full_backbone_keep_m6"
  , "full_backbone_prop_m6"
  , "full_backbone_analyze_m6"
  , "full_backbone_round_m6"
  , "full_backbone_m6"
  , "full_trans_lit_m6"
  , "full_transitive_m6"
  , "full_add_clause"
  , "full_add_bin_m6"
  , "full_delete_binary"
  , "full_bva_scan_cands"
  , "full_bva_commit"
  , "full_factor" ]

/-- Ordered names of all `1` Shard S5 inserted helper functions. -/
def fidStep13S5BeforeNames : List Sym :=
  [ "full_viv_recompute_promote_fid" ]

end

public section

theorem fidStep13S5Repls_map_name :
    fidStep13S5Repls.map Fn.name = fidStep13S5ReplNames :=
  rfl

theorem fidStep13S5Befores_map_name :
    (fidStep13S5Befores.flatMap Prod.snd).map Fn.name = fidStep13S5BeforeNames :=
  rfl

theorem fidStep13S5ReplNames_nodup : fidStep13S5ReplNames.Nodup := by decide

theorem fidStep13S5BeforeNames_nodup : fidStep13S5BeforeNames.Nodup := by decide

theorem fidStep13S5Repls_wf : ∀ f ∈ fidStep13S5Repls, f.Wf := by
  intro f hf
  simp only [fidStep13S5Repls, List.mem_append] at hf
  rcases hf with (h | h) | h
  · exact fidStep13S5ARepls_wf f h
  · exact fidStep13S5BRepls_wf f h
  · exact fidStep13S5CRepls_wf f h

theorem fidStep13S5Befores_wf :
    ∀ h ∈ fidStep13S5Befores.flatMap Prod.snd, h.Wf := by
  intro h hh
  simp only [fidStep13S5Befores, List.flatMap_append, List.mem_append] at hh
  rcases hh with (h1 | h1) | h1
  · exact fidStep13S5ABefores_wf h h1
  · exact fidStep13S5BBefores_wf h h1
  · exact fidStep13S5CBefores_wf h h1

end

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S5
