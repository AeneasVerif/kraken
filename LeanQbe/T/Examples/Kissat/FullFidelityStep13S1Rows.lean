/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S1Core
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S1SweepDense
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S1BVEFwdSub

/-!
# Kissat Fidelity Step 13 Shard S1 Data-Pure Patch Barrel (`FullFidelityStep13S1Rows`)

Data-pure barrel (`0` `*Proof*` imports, passing `check_firewall.py --require-isa --data-proof`)
exporting the `18` replacement (`fidStep13S1Repls`) and `7` added (`fidStep13S1Adds`) Step-13 S1
functions, name lists, `Nodup` lemmas, and `Func.Wf` bundles.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S1

open LeanQbe.T

@[expose] public section

/-- Combined `18` Step-13 S1 signature-preserving replacement functions (`4 + 8 + 6`). -/
def fidStep13S1Repls : List Fn :=
  fidStep13S1CoreRepls ++ fidStep13S1SweepDenseRepls ++ fidStep13S1BVEFwdSubRepls

/-- Combined `7` Step-13 S1 newly added functions (`5 + 2`). -/
def fidStep13S1Adds : List Fn :=
  fidStep13S1SweepDenseAdds ++ fidStep13S1BVEFwdSubAdds

/-- Names of the `18` Step-13 S1 replacement functions. -/
def fidStep13S1ReplNames : List Sym :=
  [ "full_k6_init"
  , "full_k6_add_clause"
  , "full_k6_core_m7"
  , "full_k6_core_fid"
  , "full_enter_dense"
  , "full_sort_bin_watches_fid"
  , "full_m6_els_ar"
  , "full_m6_els_lit"
  , "full_m6_dense_els"
  , "full_m6_sweep_var"
  , "full_m6_collect_cands"
  , "full_m6_sweep_vars"
  , "full_fwd_scan_lit_m7"
  , "full_fwd_connect_subsumer_m7"
  , "full_forward_sub_m7"
  , "full_bve_certify_unit_fid"
  , "full_bve_var_key_m7"
  , "full_eliminate_m6" ]

/-- Names of the `7` Step-13 S1 newly added functions. -/
def fidStep13S1AddNames : List Sym :=
  [ "full_dense_occ_cnt_fid"
  , "full_enter_dense_ex_fid"
  , "full_dense_bin_roundtrip_fid"
  , "full_dense_bin_sort_roundtrip_fid"
  , "full_watch_large_clauses_fid"
  , "full_has_factor_cands_fid"
  , "full_has_elim_cands_fid" ]

end

public section

theorem fidStep13S1Repls_map_name :
    fidStep13S1Repls.map Fn.name = fidStep13S1ReplNames :=
  rfl

theorem fidStep13S1Adds_map_name :
    fidStep13S1Adds.map Fn.name = fidStep13S1AddNames :=
  rfl

theorem fidStep13S1ReplNames_nodup : fidStep13S1ReplNames.Nodup := by decide

theorem fidStep13S1AddNames_nodup : fidStep13S1AddNames.Nodup := by decide

theorem fidStep13S1AllNames_nodup :
    (fidStep13S1ReplNames ++ fidStep13S1AddNames).Nodup := by decide

theorem fidStep13S1Repls_wf : ∀ f ∈ fidStep13S1Repls, f.Wf := by
  intro f hf
  simp only [fidStep13S1Repls, List.mem_append] at hf
  rcases hf with (h | h) | h
  · exact fidStep13S1CoreRepls_wf f h
  · exact fidStep13S1SweepDenseRepls_wf f h
  · exact fidStep13S1BVEFwdSubRepls_wf f h

theorem fidStep13S1Adds_wf : ∀ f ∈ fidStep13S1Adds, f.Wf := by
  intro f hf
  simp only [fidStep13S1Adds, List.mem_append] at hf
  rcases hf with h | h
  · exact fidStep13S1SweepDenseAdds_wf f h
  · exact fidStep13S1BVEFwdSubAdds_wf f h

end

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S1
