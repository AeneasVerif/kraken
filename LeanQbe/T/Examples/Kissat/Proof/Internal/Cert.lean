/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Dimacs.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Float64.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Heap.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Internal.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Tiers.Spec
public import LeanQbe.T.Examples.Kissat.Src.Internal
public import LeanQbe.T.Logic.CanonicalEnv
import LeanQbe.T.Examples.Kissat.Proof.Internal.Wp0
import LeanQbe.T.Examples.Kissat.Proof.Internal.Wp1
import LeanQbe.T.Examples.Kissat.Proof.Internal.Wp2
import LeanQbe.T.Examples.Kissat.Proof.Internal.Wp3

/-!
# Canonical Segment Certificate for `Kissat.Src.Internal` (`Proof.Internal.Cert`)

Proves `cert : SegCert Spec.deps Src.Internal.fns Spec.specs` via `CanonicalEnv`,
`Env.Sat.has`, `Spec.has_*`, and `SpecEntry.Impl.of` (`15` functions, UNSAT soundness scope).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Internal

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Src.Internal
open LeanQbe.T.Examples.Kissat.Proof.Internal.Spec

theorem cert : SegCert Spec.deps Src.Internal.fns Spec.specs := by
  intro Γ hdeps hrows
  have hTr : Γ.Sat Tiers.Spec.specs := Env.Sat.right hdeps
  have hHp : Γ.Sat Heap.Spec.specs := Env.Sat.right (Env.Sat.left hdeps)
  have hFl : Γ.Sat Float64.Spec.specs := Env.Sat.right (Env.Sat.left (Env.Sat.left hdeps))
  have hDi : Γ.Sat Dimacs.Spec.specs := Env.Sat.left (Env.Sat.left (Env.Sat.left hdeps))
  have hHdr := Dimacs.Spec.has_kissat_parse_header hDi
  have hGet : Γ.Has "m6_wm4_get" (m6HdrW2aSpec [] [i64]) :=
    Float64.Spec.has_m6Wm4Get_to_w2a
      (Env.Sat.has hFl (List.getElem_mem (l := Float64.Spec.specs) (n := 12) (by decide))
        Float64.Spec.m6Wm4GetSpec_xfree)
  have hSet : Γ.Has "m6_wm4_set" (m6HdrW2aSpec [i64] []) :=
    Env.Sat.has hFl (List.getElem_mem (l := Float64.Spec.specs) (n := 13) (by decide))
      (fun _ _ _ _ _ h => m6HdrW2aSpec_monoX h)
  have hUp := Heap.Spec.has_full_heap_up hHp
  have hDown := Heap.Spec.has_full_heap_down hHp
  have hHeapPush := Heap.Spec.has_full_heap_push hHp
  have hHdrInit := Tiers.Spec.has_m6_hdr_init hTr
  have hZt1 := Spec.has_full_zero_tables1 hrows
  have hZt2 := Spec.has_full_zero_tables2 hrows
  have hFixed := Spec.has_full_fixed_bytes hrows
  have hPtrs := Spec.has_full_init_ptrs hrows
  have hInitHdr := Spec.has_full_init_hdr hrows
  have hMaxV := Spec.has_full_calc_max_v hrows
  have hExt := Spec.has_full_calc_ext_cap_m5 hrows
  have hScr := Spec.has_full_calc_scr_cap_m5 hrows
  have hArenas := Spec.has_full_init_arenas hrows
  have hInitM5 := Spec.has_full_init_state_m5 hrows
  have hInitState := Spec.has_full_init_state hrows
  exact
    ⟨ SpecEntry.Impl.of (full_zero_tables1_wp Γ)
    , SpecEntry.Impl.of (full_zero_tables2_wp Γ)
    , SpecEntry.Impl.of (full_fixed_bytes_wp Γ)
    , SpecEntry.Impl.of (full_init_ptrs_wp Γ)
    , SpecEntry.Impl.of (full_init_hdr_wp Γ)
    , SpecEntry.Impl.of (full_calc_max_v_wp Γ hFixed)
    , SpecEntry.Impl.of (full_calc_ext_cap_m5_wp Γ)
    , SpecEntry.Impl.of (full_calc_scr_cap_m5_wp Γ)
    , SpecEntry.Impl.of (full_init_arenas_wp Γ hPtrs)
    , SpecEntry.Impl.of
        (full_init_state_m5_wp Γ hHdr hFixed hMaxV hExt hScr hArenas hInitHdr hZt1 hZt2)
    , SpecEntry.Impl.of (full_init_state_wp Γ hInitM5)
    , SpecEntry.Impl.of (full_m6_mem_init_wp Γ hInitState hHdrInit)
    , SpecEntry.Impl.of (full_set_inactive_wp Γ hUp hDown)
    , SpecEntry.Impl.of (full_init_fresh_var_wp Γ hHeapPush)
    , SpecEntry.Impl.of (full_update_classify_fid_wp Γ hGet hSet)
    , trivial
    ⟩

end LeanQbe.T.Examples.Kissat.Proof.Internal
