/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Dimacs.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Float64.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Heap.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Header
public import LeanQbe.T.Examples.Kissat.Proof.Tiers.Spec
public import LeanQbe.T.Examples.Kissat.Src.Internal
public import LeanQbe.T.Logic.CanonicalEnv

/-!
# Canonical Specification Table for `Kissat.Src.Internal` (`Proof.Internal.Spec`)

Defines canonical `XFree` (`XPost`-polymorphic, UNSAT soundness scope) specifications for all `15`
functions in `Src.Internal.fns`, reuses upstream `Proof.Spec` / `Proof.Spec.Header` contracts
where aligned with `Step-7`/`Step-13`/`M5`/`M6`, defines `fullCalcExtCapM5Spec`,
`fullCalcScrCapM5Spec`, `fullSetInactiveSpec`, and `fullInitFreshVarSpec`, and ties `deps` to
`Dimacs.Spec.specs ++ Float64.Spec.specs ++ Heap.Spec.specs ++ Tiers.Spec.specs`
(`0` legacy imports, `0` `@[expose]` on theorems/lemmas, `<= std3`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Internal.Spec

open Std.Sat
open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Src
open Kraken.Bedrock2.Test

/-- Canonical specification for `full_zero_tables1`. -/
abbrev fullZeroTables1Spec : Spec [i64] [] :=
  Proof.Spec.fullZeroTables1Spec

/-- Canonical specification for `full_zero_tables2`. -/
abbrev fullZeroTables2Spec : Spec [i64] [] :=
  Proof.Spec.fullZeroTables2Spec

/-- Canonical specification for `full_fixed_bytes`. -/
abbrev fullFixedBytesSpec : Spec [i64] [i64] :=
  Proof.Spec.fullFixedBytesSpec

/-- Canonical specification for `full_init_ptrs`. -/
abbrev fullInitPtrsSpec : Spec [i64, i64, i64] [] :=
  Proof.Spec.fullInitPtrsSpec

/-- Canonical specification for `full_init_hdr`. -/
abbrev fullInitHdrSpec : Spec [i64, i64, i64, i64] [] :=
  Proof.Spec.fullInitHdrSpec

/-- Canonical specification for `full_calc_max_v`. -/
abbrev fullCalcMaxVSpec : Spec [i64, i64, i64, i64] [i64] :=
  Proof.Spec.fullCalcMaxVSpec

/-- Canonical `M5` extend-stack capacity sizing contract (`cap ≤ 4194304`). -/
@[expose] def fullCalcExtCapM5Spec : Spec [i64] [i64] := fun (rem, ()) m Q _ =>
  ∀ r : BitVec 64, r.toNat ≤ 4194304 → (rem.toNat < 8192 → r = 0#64) →
    4 * r.toNat ≤ rem.toNat / 8 → Q (r, ()) m

/-- Canonical `M5` scratch-buffer capacity sizing contract (`cap ≤ 8388608`). -/
@[expose] def fullCalcScrCapM5Spec : Spec [i64] [i64] := fun (rem, ()) m Q _ =>
  ∀ r : BitVec 64, r.toNat ≤ 8388608 → (rem.toNat < 8192 → r = 0#64) →
    4 * r.toNat ≤ rem.toNat / 4 → Q (r, ()) m

/-- Canonical specification for `full_init_arenas`. -/
abbrev fullInitArenasSpec : Spec [i64, i64, i64, i64] [] :=
  Proof.Spec.fullInitArenasSpec

/-- Canonical specification for `full_init_state_m5` and `full_init_state`. -/
abbrev fullInitStateSpec : Spec [i64, i64, i64, i64, i64] [.bool] :=
  Proof.Spec.fullInitStateSpec

/-- Canonical specification for `full_m6_mem_init`. -/
abbrev fullM6MemInitSpec : Spec [i64, i64, i64, i64, i64] [i64] :=
  Proof.Spec.fullM6MemInitSpec

/-- Canonical `Step-13` `full_set_inactive` contract preserving `s.core` (modulo `flags` and
`unassigned`) and `FullProbeScratchPres s s'` across VMTF queue removal and EVSIDS heap
rebalance (`full_heap_up` / `full_heap_down`). -/
@[expose] def fullSetInactiveSpec : Spec [i64, i32, i32] [] := fun (h, v, _flag, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
    if s.core.cur_vars ≤ v.toNat then
      Q () m
    else
      ∀ flags' unass' (sc' : FullScratch) m',
        let s' : FullState :=
          { core := { s.core with flags := flags', unassigned := unass' }
            scratch := sc' }
        s'.LengthsOk c → FullProbeScratchPres s s' →
        (FullMem c s' ⋆ R) m' → Q () m'

/-- Canonical `Step-13` `full_init_fresh_var` contract (`step13InitFreshVarSpec` /
`step7InitFreshVarSpec`): initializes literal values, marks, flags, level, reason, watch buckets,
VMTF queue, and pushes active `fv` onto EVSIDS heap when `stable != 0`. -/
@[expose] def fullInitFreshVarSpec : Spec [i64, i32] [] := fun (h, fv, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ fv.toNat < s.core.cur_vars ∧ (FullMem c s ⋆ R) m ∧
    ∀ vals' mrk' flags' lvl' rsns' wvec' unass' sc' m',
      let s' : FullState :=
        { s with
          core := { s.core with vals := vals', mrk := mrk', flags := flags', lvl := lvl',
                                rsns := rsns', wvec := wvec', unassigned := unass' }
          scratch := sc' }
      s'.LengthsOk c → FullExtScratchPres s s' →
      sc'.scratch_buf = s.scratch.scratch_buf →
      sc'.wsort = s.scratch.wsort →
      sc'.tarjan_mark = s.scratch.tarjan_mark →
      sc'.tarjan_reach = s.scratch.tarjan_reach →
      sc'.sim_sig = s.scratch.sim_sig →
      sc'.res_sz = s.scratch.res_sz →
      vals'[2 * fv.toNat]?.getD 1#8 = 0#8 → vals'[2 * fv.toNat + 1]?.getD 1#8 = 0#8 →
      (∀ l < 2 * c.max_vars, l / 2 ≠ fv.toNat → vals'[l]? = s.core.vals[l]?) →
      mrk'[fv.toNat]?.getD 1#8 = 0#8 →
      (∀ v < c.max_vars, v ≠ fv.toNat → mrk'[v]? = s.core.mrk[v]?) →
      lvl'[fv.toNat]?.getD 1#32 = 0#32 →
      (∀ v < c.max_vars, v ≠ fv.toNat → lvl'[v]? = s.core.lvl[v]?) →
      rsns'[fv.toNat]?.getD 0#32 = 0xFFFFFFFF#32 →
      (∀ v < c.max_vars, v ≠ fv.toNat → rsns'[v]? = s.core.rsns[v]?) →
      (∀ k < 4, wvec'[4 * fv.toNat + k]?.getD 1#32 = 0#32) →
      (∀ i < 4 * c.max_vars, i / 4 ≠ fv.toNat → wvec'[i]? = s.core.wvec[i]?) →
      (FullMem c s' ⋆ R) m' → Q () m'

/-- Canonical `FullM6HdrMem` contract for `full_update_classify_fid`. -/
abbrev fullUpdateClassifyFidSpec : Spec [i64] [] :=
  m6HdrW2aSpec [] []

theorem fullZeroTables1Spec_xfree : Spec.XFree fullZeroTables1Spec := by xfree
theorem fullZeroTables2Spec_xfree : Spec.XFree fullZeroTables2Spec := by xfree
theorem fullFixedBytesSpec_xfree : Spec.XFree fullFixedBytesSpec := by xfree
theorem fullInitPtrsSpec_xfree : Spec.XFree fullInitPtrsSpec := by xfree
theorem fullInitHdrSpec_xfree : Spec.XFree fullInitHdrSpec := by xfree
theorem fullCalcMaxVSpec_xfree : Spec.XFree fullCalcMaxVSpec := by xfree
theorem fullCalcExtCapM5Spec_xfree : Spec.XFree fullCalcExtCapM5Spec := by xfree
theorem fullCalcScrCapM5Spec_xfree : Spec.XFree fullCalcScrCapM5Spec := by xfree
theorem fullInitArenasSpec_xfree : Spec.XFree fullInitArenasSpec := by xfree
theorem fullInitStateSpec_xfree : Spec.XFree fullInitStateSpec := by xfree
theorem fullM6MemInitSpec_xfree : Spec.XFree fullM6MemInitSpec := by xfree
theorem fullSetInactiveSpec_xfree : Spec.XFree fullSetInactiveSpec := by xfree
theorem fullInitFreshVarSpec_xfree : Spec.XFree fullInitFreshVarSpec := by xfree
theorem fullUpdateClassifyFidSpec_xfree : Spec.XFree fullUpdateClassifyFidSpec :=
  fun _ _ _ _ _ h => m6HdrW2aSpec_monoX h

/-- Upstream capability dependencies for `Src.Internal`:
`Dimacs` (`kissat_parse_header`), `Float64` (`m6_wm4_get`, `m6_wm4_set`),
`Heap` (`full_heap_up`, `full_heap_down`, `full_heap_push`), and `Tiers` (`m6_hdr_init`). -/
@[expose] def deps : List SpecEntry :=
  Dimacs.Spec.specs ++ Float64.Spec.specs ++ Heap.Spec.specs ++ Tiers.Spec.specs

/-- Canonical `SpecEntry` table matching `Src.Internal.fns` 1-to-1. -/
@[expose] def specs : List SpecEntry :=
  [ ⟨"full_zero_tables1", [i64], [], fullZeroTables1Spec, true⟩
  , ⟨"full_zero_tables2", [i64], [], fullZeroTables2Spec, true⟩
  , ⟨"full_fixed_bytes", [i64], [i64], fullFixedBytesSpec, true⟩
  , ⟨"full_init_ptrs", [i64, i64, i64], [], fullInitPtrsSpec, true⟩
  , ⟨"full_init_hdr", [i64, i64, i64, i64], [], fullInitHdrSpec, true⟩
  , ⟨"full_calc_max_v", [i64, i64, i64, i64], [i64], fullCalcMaxVSpec, true⟩
  , ⟨"full_calc_ext_cap_m5", [i64], [i64], fullCalcExtCapM5Spec, true⟩
  , ⟨"full_calc_scr_cap_m5", [i64], [i64], fullCalcScrCapM5Spec, true⟩
  , ⟨"full_init_arenas", [i64, i64, i64, i64], [], fullInitArenasSpec, true⟩
  , ⟨"full_init_state_m5", [i64, i64, i64, i64, i64], [.bool], fullInitStateSpec, true⟩
  , ⟨"full_init_state", [i64, i64, i64, i64, i64], [.bool], fullInitStateSpec, true⟩
  , ⟨"full_m6_mem_init", [i64, i64, i64, i64, i64], [i64], fullM6MemInitSpec, true⟩
  , ⟨"full_set_inactive", [i64, i32, i32], [], fullSetInactiveSpec, true⟩
  , ⟨"full_init_fresh_var", [i64, i32], [], fullInitFreshVarSpec, true⟩
  , ⟨"full_update_classify_fid", [i64], [], fullUpdateClassifyFidSpec, true⟩ ]

theorem specs_sigs : specs.map SpecEntry.sig = Internal.fns.map Fn.sig := rfl

theorem specs_nodup : (specs.map SpecEntry.name).Nodup := by decide

theorem specs_noExit : specs.all SpecEntry.noExit = true := rfl

theorem specs_xfree : ∀ e ∈ specs, e.spec.XFree := by
  intro e he
  simp only [specs, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl
  · exact fullZeroTables1Spec_xfree
  · exact fullZeroTables2Spec_xfree
  · exact fullFixedBytesSpec_xfree
  · exact fullInitPtrsSpec_xfree
  · exact fullInitHdrSpec_xfree
  · exact fullCalcMaxVSpec_xfree
  · exact fullCalcExtCapM5Spec_xfree
  · exact fullCalcScrCapM5Spec_xfree
  · exact fullInitArenasSpec_xfree
  · exact fullInitStateSpec_xfree
  · exact fullInitStateSpec_xfree
  · exact fullM6MemInitSpec_xfree
  · exact fullSetInactiveSpec_xfree
  · exact fullInitFreshVarSpec_xfree
  · exact fullUpdateClassifyFidSpec_xfree

theorem has_full_zero_tables1 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_zero_tables1" fullZeroTables1Spec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 0) (by decide)) fullZeroTables1Spec_xfree

theorem has_full_zero_tables2 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_zero_tables2" fullZeroTables2Spec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 1) (by decide)) fullZeroTables2Spec_xfree

theorem has_full_fixed_bytes {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_fixed_bytes" fullFixedBytesSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 2) (by decide)) fullFixedBytesSpec_xfree

theorem has_full_init_ptrs {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_init_ptrs" fullInitPtrsSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 3) (by decide)) fullInitPtrsSpec_xfree

theorem has_full_init_hdr {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_init_hdr" fullInitHdrSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 4) (by decide)) fullInitHdrSpec_xfree

theorem has_full_calc_max_v {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_calc_max_v" fullCalcMaxVSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 5) (by decide)) fullCalcMaxVSpec_xfree

theorem has_full_calc_ext_cap_m5 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_calc_ext_cap_m5" fullCalcExtCapM5Spec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 6) (by decide)) fullCalcExtCapM5Spec_xfree

theorem has_full_calc_scr_cap_m5 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_calc_scr_cap_m5" fullCalcScrCapM5Spec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 7) (by decide)) fullCalcScrCapM5Spec_xfree

theorem has_full_init_arenas {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_init_arenas" fullInitArenasSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 8) (by decide)) fullInitArenasSpec_xfree

theorem has_full_init_state_m5 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_init_state_m5" fullInitStateSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 9) (by decide)) fullInitStateSpec_xfree

theorem has_full_init_state {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_init_state" fullInitStateSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 10) (by decide)) fullInitStateSpec_xfree

theorem has_full_m6_mem_init {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_m6_mem_init" fullM6MemInitSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 11) (by decide)) fullM6MemInitSpec_xfree

theorem has_full_set_inactive {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_set_inactive" fullSetInactiveSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 12) (by decide)) fullSetInactiveSpec_xfree

theorem has_full_init_fresh_var {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_init_fresh_var" fullInitFreshVarSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 13) (by decide)) fullInitFreshVarSpec_xfree

theorem has_full_update_classify_fid {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_update_classify_fid" fullUpdateClassifyFidSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 14) (by decide))
    fullUpdateClassifyFidSpec_xfree

end LeanQbe.T.Examples.Kissat.Proof.Internal.Spec
