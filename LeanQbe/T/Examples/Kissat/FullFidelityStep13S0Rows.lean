/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S0

/-!
# Kissat Fidelity Step-13 Shard `S0` Row Names (`FullFidelityStep13S0Rows`)

Strictly data-pure (`0` `*Proof*`/`*Lemmas*`/`*Audit*`/`*Spec*` imports) symbol/signature
lists and uniqueness theorems for the `17` `S0` functions (`14` ADD + `3` MOD).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S0

open LeanQbe.T

@[expose] public section

/-- Ordered names of the `14` new `S0` helper functions. -/
def fidStep13S0AddNames : List Sym :=
  [ "f64u_msb64", "f64u_round_pack", "f64u_add", "f64u_sub", "f64u_mul"
  , "f64u_div", "f64u_inv_u64", "f64u_from_u64", "f64u_to_u64", "u64_mul128"
  , "f64u_log10_u64", "f64u_nlogpown", "m6_wm4_get", "m6_wm4_set" ]

/-- Ordered names of the `3` modified `S0` replacement functions. -/
def fidStep13S0ReplNames : List Sym :=
  [ "full_init_hdr", "m6_hdr_init", "m6_hdr_recompute_tiers_mode" ]

/-- Ordered names of all `17` `S0` functions (`14` ADD + `3` MOD). -/
def fidStep13S0AllNames : List Sym :=
  fidStep13S0AddNames ++ fidStep13S0ReplNames

end

public section

theorem fidStep13S0AddFns_length : fidStep13S0AddFns.length = 14 := rfl
theorem fidStep13S0Repls_length : fidStep13S0Repls.length = 3 := rfl
theorem fidStep13S0AllFns_length : fidStep13S0AllFns.length = 17 := rfl

theorem fidStep13S0AddFns_map_name :
    fidStep13S0AddFns.map Fn.name = fidStep13S0AddNames := rfl

theorem fidStep13S0Repls_map_name :
    fidStep13S0Repls.map Fn.name = fidStep13S0ReplNames := rfl

theorem fidStep13S0AllFns_map_name :
    fidStep13S0AllFns.map Fn.name = fidStep13S0AllNames := rfl

theorem fidStep13S0AllNames_nodup : fidStep13S0AllNames.Nodup := by decide

theorem fidStep13S0AllFns_wf :
    ∀ f ∈ fidStep13S0AllFns, f.Wf := by
  intro f hf
  simp only [fidStep13S0AllFns, fidStep13S0AddFns, fidStep13S0Repls,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with (rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl)
  · exact f64u_msb64_wf
  · exact f64u_round_pack_wf
  · exact f64u_add_wf
  · exact f64u_sub_wf
  · exact f64u_mul_wf
  · exact f64u_div_wf
  · exact f64u_inv_u64_wf
  · exact f64u_from_u64_wf
  · exact f64u_to_u64_wf
  · exact u64_mul128_wf
  · exact f64u_log10_u64_wf
  · exact f64u_nlogpown_wf
  · exact m6_wm4_get_wf
  · exact m6_wm4_set_wf
  · exact full_init_hdr_wf
  · exact m6_hdr_init_wf
  · exact m6_hdr_recompute_tiers_mode_wf

end

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S0
