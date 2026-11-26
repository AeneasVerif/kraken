/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep9MemShrinkProof0
import LeanQbe.T.Logic.MemLemmas
import Kraken.Mem
import Kraken.Separation

/-!
# Step-9 Experimental `MemShrinkV5` Closed `ModuleOk` & UNSAT NV (`FullFidelityStep9MemShrinkProof`)

Certifies `S9-P0.3` (`fidStep9MsStandaloneModule` `14` fns + `1` external decl and
`fidStep9MsM6Module` `16` fns + `1` external decl over `MemShrinkM6HdrMem`, `XPost := False`,
`0` SAT proofs, `<= std3`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep9MemShrink

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullParseInitSpecs
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullFidelityStep9
open LeanQbe.T.Examples.Kissat.FullM7MemShrink hiding
  full_fill_u64_m7_body full_fill_u64_m7_wf full_trans_bytes_m7_body full_trans_bytes_m7_wf
open LeanQbe.T.Examples.Kissat.FullM7MemShrinkV5 hiding
  full_fill_u64_m7_body full_fill_u64_m7_wf full_trans_bytes_m7_body full_trans_bytes_m7_wf
  full_calc_max_v_m7v5_body full_calc_max_v_m7v5_wf
open Kraken.Bedrock2.Test

/-! ## 1. Closed `ModuleOk` (`14`-fn Standalone & `16`-fn `+FullM6Hdr`) -/

section ModuleOkSection

private theorem allFns_of_forall {P : Fn → Prop} :
    ∀ (fs : List Fn), (∀ f ∈ fs, P f) → AllFns P fs
  | [], _ => trivial
  | f :: fs, h => ⟨h f (.head _), allFns_of_forall fs fun g hg => h g (.tail _ hg)⟩

/-- Closed `15`-row spec table for `fidStep9MsStandaloneModule`
(`14` defined fns + `1` external decl). -/
def fidStep9MsSpecTable : List SpecEntry :=
  [ ⟨"full_fill_u64_m7", [i64, i64, i64], [], m7FillU64Spec, true⟩
  , ⟨"full_zero_tables1", [i64], [], m7ZeroTables1Spec, true⟩
  , ⟨"full_zero_tables2", [i64], [], m7ZeroTables2Spec, true⟩
  , ⟨"full_fixed_bytes", [i64], [i64], m7FixedBytesSpec, true⟩
  , ⟨"full_init_ptrs", [i64, i64, i64], [], m7InitPtrsSpec, true⟩
  , ⟨"full_init_hdr", [i64, i64, i64, i64], [], m7InitHdrSpec, true⟩
  , ⟨"full_trans_bytes_m7", [i64], [i64], m7TransBytesSpec, true⟩
  , ⟨"full_calc_max_v", [i64, i64, i64, i64], [i64], s9msCalcMaxVSpec, true⟩
  , ⟨"full_calc_ext_cap_m5", [i64], [i64], m7CalcExtCapSpec, true⟩
  , ⟨"full_calc_scr_cap_m5", [i64], [i64], s9msCalcScrCapSpec, true⟩
  , ⟨"full_init_arenas", [i64, i64, i64, i64], [], m7InitArenasSpec, true⟩
  , ⟨"full_init_state_m5", [i64, i64, i64, i64, i64], [.bool], m7InitStateSpec, true⟩
  , ⟨"full_init_state", [i64, i64, i64, i64, i64], [.bool], m7InitStateSpec, true⟩
  , ⟨"full_compact_vars", [i64, i64, i64], [], m7msCompactVarsSpec, true⟩
  , ⟨"kissat_parse_header", [i64, i64, i64], [.bool], kissatParseHeaderSpec, true⟩ ]

theorem fidStep9MsSpecTable_length : fidStep9MsSpecTable.length = 15 := by
  unfold fidStep9MsSpecTable; rfl

theorem fidStep9MsSpecTable_nodup : (fidStep9MsSpecTable.map SpecEntry.name).Nodup := by
  unfold fidStep9MsSpecTable; decide

theorem fidStep9MsSpecTable_noExit : ∀ e ∈ fidStep9MsSpecTable, e.noExit = true := by
  intro e he
  unfold fidStep9MsSpecTable at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl <;> rfl

/-- Closed specification environment for `fidStep9MsStandaloneModule`. -/
def fidStep9MsEnv : Env := Env.ofTable fidStep9MsSpecTable

private theorem fidStep9MsEnv_row {i : Nat} (nm : Sym) {as rs : List Ty} (sp : Spec as rs)
    (hi : fidStep9MsSpecTable[i]? = some ⟨nm, as, rs, sp, true⟩)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False)) :
    EnvSpec fidStep9MsEnv nm sp := by
  rw [envSpec_eq]; intro xs m Q X h
  exact Env.ofTable_of_mem (List.mem_of_getElem? hi) fidStep9MsSpecTable_nodup
    (by simp only [SpecEntry.eff, ↓reduceIte]; exact hno xs m Q X h)

private theorem fidStep9MsStandalone_tableImpl_gen (Γ : Env)
    (hFill : EnvSpec Γ "full_fill_u64_m7" m7FillU64Spec)
    (hZt1 : EnvSpec Γ "full_zero_tables1" m7ZeroTables1Spec)
    (hZt2 : EnvSpec Γ "full_zero_tables2" m7ZeroTables2Spec)
    (hFixed : EnvSpec Γ "full_fixed_bytes" m7FixedBytesSpec)
    (hPtrs : EnvSpec Γ "full_init_ptrs" m7InitPtrsSpec)
    (hHdr : EnvSpec Γ "full_init_hdr" m7InitHdrSpec)
    (hTrans : EnvSpec Γ "full_trans_bytes_m7" m7TransBytesSpec)
    (hMaxV : EnvSpec Γ "full_calc_max_v" s9msCalcMaxVSpec)
    (hExt : EnvSpec Γ "full_calc_ext_cap_m5" m7CalcExtCapSpec)
    (hScr : EnvSpec Γ "full_calc_scr_cap_m5" s9msCalcScrCapSpec)
    (hArenas : EnvSpec Γ "full_init_arenas" m7InitArenasSpec)
    (hM5 : EnvSpec Γ "full_init_state_m5" m7InitStateSpec)
    (hParse : EnvSpec Γ "kissat_parse_header" kissatParseHeaderSpec)
    {tail : List SpecEntry} :
    TableImpl Γ fidStep9MsStandaloneFns (fidStep9MsSpecTable.take 14 ++ tail) :=
  ⟨ SpecEntry.Impl.of (full_fill_u64_s9ms_wp Γ)
  , SpecEntry.Impl.of (full_zero_tables1_s9ms_wp Γ hFill)
  , SpecEntry.Impl.of (full_zero_tables2_s9ms_wp Γ hFill)
  , SpecEntry.Impl.of (full_fixed_bytes_s9ms_wp Γ)
  , SpecEntry.Impl.of (full_init_ptrs_s9ms_wp Γ)
  , SpecEntry.Impl.of (full_init_hdr_s9ms_wp Γ)
  , SpecEntry.Impl.of (full_trans_bytes_s9ms_wp Γ)
  , SpecEntry.Impl.of (full_calc_max_v_wp Γ hFixed hTrans)
  , SpecEntry.Impl.of (full_calc_ext_cap_s9ms_wp Γ)
  , SpecEntry.Impl.of (full_calc_scr_cap_m5_s9ms_wp Γ)
  , SpecEntry.Impl.of (full_init_arenas_s9ms_wp Γ hPtrs)
  , SpecEntry.Impl.of (full_init_state_m5_s9ms_wp Γ hParse hFixed hTrans hMaxV hExt hScr hArenas
      hHdr hZt1 hZt2)
  , SpecEntry.Impl.of (full_init_state_s9ms_wp Γ hM5)
  , SpecEntry.Impl.of (full_compact_vars_s9ms_wp Γ)
  , trivial ⟩

theorem fidStep9Ms_tableImpl :
    TableImpl fidStep9MsEnv fidStep9MsStandaloneModule.fns fidStep9MsSpecTable := by
  have h14 : fidStep9MsSpecTable = fidStep9MsSpecTable.take 14 ++
      [⟨"kissat_parse_header", [i64, i64, i64], [.bool], kissatParseHeaderSpec, true⟩] := by
    unfold fidStep9MsSpecTable; rfl
  rw [h14]
  exact fidStep9MsStandalone_tableImpl_gen fidStep9MsEnv
    (fidStep9MsEnv_row "full_fill_u64_m7" m7FillU64Spec (i := 0) rfl
      fun xs m Q X h => by rw [m7FillU64Spec_eq] at h ⊢; exact h)
    (fidStep9MsEnv_row "full_zero_tables1" m7ZeroTables1Spec (i := 1) rfl
      fun ⟨h0, ⟨⟩⟩ m Q X h => by rw [m7ZeroTables1Spec_eq] at h ⊢; exact h)
    (fidStep9MsEnv_row "full_zero_tables2" m7ZeroTables2Spec (i := 2) rfl
      fun ⟨h0, ⟨⟩⟩ m Q X h => by rw [m7ZeroTables2Spec_eq] at h ⊢; exact h)
    (fidStep9MsEnv_row "full_fixed_bytes" m7FixedBytesSpec (i := 3) rfl
      fun xs m Q X h => by rw [m7FixedBytesSpec_eq] at h ⊢; exact h)
    (fidStep9MsEnv_row "full_init_ptrs" m7InitPtrsSpec (i := 4) rfl
      fun ⟨h1, h2, h3, ⟨⟩⟩ m Q X h => by rw [m7InitPtrsSpec_eq] at h ⊢; exact h)
    (fidStep9MsEnv_row "full_init_hdr" m7InitHdrSpec (i := 5) rfl
      fun ⟨h1, h2, h3, h4, ⟨⟩⟩ m Q X h => by rw [m7InitHdrSpec_eq] at h ⊢; exact h)
    (fidStep9MsEnv_row "full_trans_bytes_m7" m7TransBytesSpec (i := 6) rfl
      fun xs m Q X h => by rw [m7TransBytesSpec_eq] at h ⊢; exact h)
    (fidStep9MsEnv_row "full_calc_max_v" s9msCalcMaxVSpec (i := 7) rfl
      fun ⟨h1, h2, h3, h4, ⟨⟩⟩ m Q X h => by rw [s9msCalcMaxVSpec_eq] at h ⊢; exact h)
    (fidStep9MsEnv_row "full_calc_ext_cap_m5" m7CalcExtCapSpec (i := 8) rfl
      fun xs m Q X h => by rw [m7CalcExtCapSpec_eq] at h ⊢; exact h)
    (fidStep9MsEnv_row "full_calc_scr_cap_m5" s9msCalcScrCapSpec (i := 9) rfl
      fun xs m Q X h => by rw [s9msCalcScrCapSpec_eq] at h ⊢; exact h)
    (fidStep9MsEnv_row "full_init_arenas" m7InitArenasSpec (i := 10) rfl
      fun ⟨h1, h2, h3, h4, ⟨⟩⟩ m Q X h => by rw [m7InitArenasSpec_eq] at h ⊢; exact h)
    (fidStep9MsEnv_row "full_init_state_m5" m7InitStateSpec (i := 11) rfl
      fun ⟨h1, h2, h3, h4, h5, ⟨⟩⟩ m Q X h => by rw [m7InitStateSpec_eq] at h ⊢; exact h)
    (fidStep9MsEnv_row "kissat_parse_header" kissatParseHeaderSpec (i := 14) rfl
      fun _ _ _ _ h => h)

/-- Closed `ModuleOk` certifying all `14` canonical MemShrink V5 functions + `1` external decl. -/
theorem fidStep9MsStandalone_moduleOk : ModuleOk fidStep9MsEnv fidStep9MsStandaloneModule :=
  Env.ofTable_moduleOk fidStep9MsStandalone_acyclic
    (allFns_of_forall fidStep9MsStandaloneFns fidStep9MsStandaloneFns_wf) fidStep9Ms_tableImpl

/-- Closed `17`-row spec table for `fidStep9MsM6Module` (`16` defined fns + `1` external decl). -/
def fidStep9MsM6SpecTable : List SpecEntry :=
  fidStep9MsSpecTable.take 14 ++
  [ ⟨"m6_hdr_init", [i64], [], m6HdrInitMsSpec, true⟩
  , ⟨"full_m6_mem_init", [i64, i64, i64, i64, i64], [i64], fullM6MemInitMsSpec, true⟩
  , ⟨"kissat_parse_header", [i64, i64, i64], [.bool], kissatParseHeaderSpec, true⟩ ]

theorem fidStep9MsM6SpecTable_length : fidStep9MsM6SpecTable.length = 17 := by
  unfold fidStep9MsM6SpecTable fidStep9MsSpecTable; rfl

theorem fidStep9MsM6SpecTable_nodup : (fidStep9MsM6SpecTable.map SpecEntry.name).Nodup := by
  unfold fidStep9MsM6SpecTable fidStep9MsSpecTable; decide

theorem fidStep9MsM6SpecTable_noExit : ∀ e ∈ fidStep9MsM6SpecTable, e.noExit = true := by
  intro e he
  unfold fidStep9MsM6SpecTable fidStep9MsSpecTable at he
  simp only [List.take, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl <;> rfl

/-- Closed specification environment for `fidStep9MsM6Module`. -/
def fidStep9MsM6Env : Env := Env.ofTable fidStep9MsM6SpecTable

private theorem fidStep9MsM6Env_row {i : Nat} (nm : Sym) {as rs : List Ty} (sp : Spec as rs)
    (hi : fidStep9MsM6SpecTable[i]? = some ⟨nm, as, rs, sp, true⟩)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False)) :
    EnvSpec fidStep9MsM6Env nm sp := by
  rw [envSpec_eq]; intro xs m Q X h
  exact Env.ofTable_of_mem (List.mem_of_getElem? hi) fidStep9MsM6SpecTable_nodup
    (by simp only [SpecEntry.eff, ↓reduceIte]; exact hno xs m Q X h)

private theorem tableImpl_append_cons {Γ : Env} {fs1 fs2 : List Fn} {sp1 sp2 : List SpecEntry}
    (h1 : fs1.length = sp1.length)
    (ht1 : TableImpl Γ fs1 (sp1 ++ sp2))
    (ht2 : TableImpl Γ fs2 sp2) :
    TableImpl Γ (fs1 ++ fs2) (sp1 ++ sp2) := by
  induction fs1 generalizing sp1 with
  | nil =>
    cases sp1 with
    | nil => exact ht2
    | cons _ _ => simp at h1
  | cons f fs ih =>
    cases sp1 with
    | nil => simp at h1
    | cons e es =>
      simp only [List.length_cons, Nat.succ.injEq] at h1
      simp only [List.cons_append, TableImpl] at ht1 ⊢
      exact ⟨ht1.1, ih h1 ht1.2⟩

theorem fidStep9MsM6_tableImpl :
    TableImpl fidStep9MsM6Env fidStep9MsM6Module.fns fidStep9MsM6SpecTable := by
  have h14 : TableImpl fidStep9MsM6Env fidStep9MsStandaloneFns (fidStep9MsSpecTable.take 14 ++
      [ ⟨"m6_hdr_init", [i64], [], m6HdrInitMsSpec, true⟩
      , ⟨"full_m6_mem_init", [i64, i64, i64, i64, i64], [i64], fullM6MemInitMsSpec, true⟩
      , ⟨"kissat_parse_header", [i64, i64, i64], [.bool], kissatParseHeaderSpec, true⟩ ]) :=
    fidStep9MsStandalone_tableImpl_gen fidStep9MsM6Env
      (fidStep9MsM6Env_row "full_fill_u64_m7" m7FillU64Spec (i := 0) rfl
        fun xs m Q X h => by rw [m7FillU64Spec_eq] at h ⊢; exact h)
      (fidStep9MsM6Env_row "full_zero_tables1" m7ZeroTables1Spec (i := 1) rfl
        fun ⟨h0, ⟨⟩⟩ m Q X h => by rw [m7ZeroTables1Spec_eq] at h ⊢; exact h)
      (fidStep9MsM6Env_row "full_zero_tables2" m7ZeroTables2Spec (i := 2) rfl
        fun ⟨h0, ⟨⟩⟩ m Q X h => by rw [m7ZeroTables2Spec_eq] at h ⊢; exact h)
      (fidStep9MsM6Env_row "full_fixed_bytes" m7FixedBytesSpec (i := 3) rfl
        fun xs m Q X h => by rw [m7FixedBytesSpec_eq] at h ⊢; exact h)
      (fidStep9MsM6Env_row "full_init_ptrs" m7InitPtrsSpec (i := 4) rfl
        fun ⟨h1, h2, h3, ⟨⟩⟩ m Q X h => by rw [m7InitPtrsSpec_eq] at h ⊢; exact h)
      (fidStep9MsM6Env_row "full_init_hdr" m7InitHdrSpec (i := 5) rfl
        fun ⟨h1, h2, h3, h4, ⟨⟩⟩ m Q X h => by rw [m7InitHdrSpec_eq] at h ⊢; exact h)
      (fidStep9MsM6Env_row "full_trans_bytes_m7" m7TransBytesSpec (i := 6) rfl
        fun xs m Q X h => by rw [m7TransBytesSpec_eq] at h ⊢; exact h)
      (fidStep9MsM6Env_row "full_calc_max_v" s9msCalcMaxVSpec (i := 7) rfl
        fun ⟨h1, h2, h3, h4, ⟨⟩⟩ m Q X h => by rw [s9msCalcMaxVSpec_eq] at h ⊢; exact h)
      (fidStep9MsM6Env_row "full_calc_ext_cap_m5" m7CalcExtCapSpec (i := 8) rfl
        fun xs m Q X h => by rw [m7CalcExtCapSpec_eq] at h ⊢; exact h)
      (fidStep9MsM6Env_row "full_calc_scr_cap_m5" s9msCalcScrCapSpec (i := 9) rfl
        fun xs m Q X h => by rw [s9msCalcScrCapSpec_eq] at h ⊢; exact h)
      (fidStep9MsM6Env_row "full_init_arenas" m7InitArenasSpec (i := 10) rfl
        fun ⟨h1, h2, h3, h4, ⟨⟩⟩ m Q X h => by rw [m7InitArenasSpec_eq] at h ⊢; exact h)
      (fidStep9MsM6Env_row "full_init_state_m5" m7InitStateSpec (i := 11) rfl
        fun ⟨h1, h2, h3, h4, h5, ⟨⟩⟩ m Q X h => by rw [m7InitStateSpec_eq] at h ⊢; exact h)
      (fidStep9MsM6Env_row "kissat_parse_header" kissatParseHeaderSpec (i := 16) rfl
        fun _ _ _ _ h => h)
  have hm6_hdr : SpecEntry.Impl fidStep9MsM6Env fidStep9MsM6HdrInitFn
      ⟨"m6_hdr_init", [i64], [], m6HdrInitMsSpec, true⟩ :=
    SpecEntry.Impl.of (m6_hdr_init_ms_wp fidStep9MsM6Env)
  have hfull_m6 : SpecEntry.Impl fidStep9MsM6Env fidStep9MsM6MemInitFn
      ⟨"full_m6_mem_init", [i64, i64, i64, i64, i64], [i64], fullM6MemInitMsSpec, true⟩ :=
    SpecEntry.Impl.of (full_m6_mem_init_ms_wp fidStep9MsM6Env
      (fidStep9MsM6Env_row "full_init_state" m7InitStateSpec (i := 12) rfl
        fun ⟨h1, h2, h3, h4, h5, ⟨⟩⟩ m Q X h => by rw [m7InitStateSpec_eq] at h ⊢; exact h)
      (fidStep9MsM6Env_row "m6_hdr_init" m6HdrInitMsSpec (i := 14) rfl
        fun _ _ _ _ h => m6HdrInitMsSpec_monoX h))
  exact tableImpl_append_cons (sp1 := fidStep9MsSpecTable.take 14)
    (by unfold fidStep9MsSpecTable; rfl) h14 ⟨hm6_hdr, hfull_m6, trivial⟩

private theorem fidStep9MsM6MemInitFn_impl : SpecEntry.Impl fidStep9MsM6Env fidStep9MsM6MemInitFn
    ⟨"full_m6_mem_init", [i64, i64, i64, i64, i64], [i64], fullM6MemInitMsSpec, true⟩ :=
  SpecEntry.Impl.of (full_m6_mem_init_ms_wp fidStep9MsM6Env
    (fidStep9MsM6Env_row "full_init_state" m7InitStateSpec (i := 12) rfl
      fun ⟨h1, h2, h3, h4, h5, ⟨⟩⟩ m Q X h => by rw [m7InitStateSpec_eq] at h ⊢; exact h)
    (fidStep9MsM6Env_row "m6_hdr_init" m6HdrInitMsSpec (i := 14) rfl
      fun _ _ _ _ h => m6HdrInitMsSpec_monoX h))

/-- Closed `ModuleOk` certifying all `16` functions of `fidStep9MsM6Module` (standalone V5 +
`FullM6Hdr` zero-edit prefix framing) with `1` extern and `0` exits. -/
theorem fidStep9MsM6_moduleOk : ModuleOk fidStep9MsM6Env fidStep9MsM6Module :=
  Env.ofTable_moduleOk fidStep9MsM6_acyclic
    (allFns_of_forall _ fidStep9MsM6Fns_wf) fidStep9MsM6_tableImpl

end ModuleOkSection

/-! ## 6. Concrete `Mem 64` UNSAT Non-Vacuity (`XPost := False`, `0` SAT Proofs) -/

theorem fidStep9MsM6Env_noExit :
    ∀ f as bs xs m Q X X',
      fidStep9MsM6Env f as bs xs m Q X → fidStep9MsM6Env f as bs xs m Q X' :=
  Env.ofTable_noExit fidStep9MsM6SpecTable_noExit

section ConcreteUnsatNv

def nvS9MsUnsatCnf : CNF Nat :=
  CNF.empty |>.add (CNF.Clause.ofLiterals [(1, true)]) |>.add (CNF.Clause.ofLiterals [(1, false)])

theorem nvS9MsUnsatCnf_unsat : nvS9MsUnsatCnf.Unsat := by
  rw [CNF.unsat_iff_not_sat]
  intro α hsat
  rw [nvS9MsUnsatCnf, CNF.sat_add, CNF.sat_add] at hsat
  rcases hsat with ⟨hc2, hc1, _⟩
  rw [CNF.Clause.sat_iff_exists_mem_eq] at hc1 hc2
  obtain ⟨⟨v1, p1⟩, hm1, he1⟩ := hc1
  obtain ⟨⟨v2, p2⟩, hm2, he2⟩ := hc2
  rw [← CNF.Clause.mem_literals_iff] at hm1 hm2
  simp at hm1 hm2
  rcases hm1 with ⟨rfl, rfl⟩
  rcases hm2 with ⟨rfl, rfl⟩
  rw [he1] at he2
  exact nomatch he2

def nvS9MsUnsatBytes : List UInt8 :=
  [ 0x70, 0x20, 0x63, 0x6e, 0x66, 0x20, 0x31, 0x20, 0x32, 0x0a
  , 0x31, 0x20, 0x30, 0x0a, 0x2d, 0x31, 0x20, 0x30, 0x0a ]

theorem nvS9MsUnsat_header :
    parseHeader nvS9MsUnsatBytes = some (1, 2, nvS9MsUnsatBytes.drop 9) := by
  unfold nvS9MsUnsatBytes; rfl

def nvS9MsCnfPtr : BitVec 64 := 0x1000#64
def nvS9MsHdrPtr : BitVec 64 := nvS9MsCnfPtr + BitVec.ofNat 64 nvS9MsUnsatBytes.length

def nvS9MsInitMem : Mem 64 :=
  (nvS9MsUnsatBytes ++ List.replicate 4096 (0 : UInt8)).At nvS9MsCnfPtr

def nvS9MsTinyInitMem : Mem 64 :=
  (nvS9MsUnsatBytes ++ List.replicate 1000 (0 : UInt8)).At 0x2000#64

def nvS9Ms4kInitMem : Mem 64 :=
  (nvS9MsUnsatBytes ++ List.replicate 6400 (0 : UInt8)).At 0x2000#64

private theorem nv_s9ms_mem_split (base : BitVec 64) (k : Nat)
    (hk : nvS9MsUnsatBytes.length + k ≤ 2 ^ 64) :
    (bytes base nvS9MsUnsatBytes ⋆
      region (base + BitVec.ofNat 64 nvS9MsUnsatBytes.length) k ⋆ emp)
      ((nvS9MsUnsatBytes ++ List.replicate k (0 : UInt8)).At base) := by
  rw [sep_emp]
  have e := Mem.At_append_sep nvS9MsUnsatBytes
    (List.replicate k (0 : UInt8)) base (by simpa using hk)
  have hbase : (Eq (nvS9MsUnsatBytes.At base) ⋆
      Eq ((List.replicate k (0 : UInt8)).At
        (base + BitVec.ofNat 64 nvS9MsUnsatBytes.length)))
      ((nvS9MsUnsatBytes ++ List.replicate k (0 : UInt8)).At base) :=
    (congrFun e _).mp rfl
  exact sep_mono2 (fun _ h => h)
    (fun _ h => ⟨List.replicate k (0 : UInt8), by simp, h.symm⟩) _ hbase

/-- Concrete `Mem 64` UNSAT NV (`XPost := False`, `0` SAT proofs) for `full_init_state_m5`
on `(x1) ∧ (~x1)` with `4,096 B` budget (`mv = 1`, `nc = 2`, `avail = 4096`). -/
theorem nv_s9ms_init_state_unsat :
    Func.wp fidStep9MsEnv full_init_state_m5_body
      (nvS9MsCnfPtr, nvS9MsCnfPtr + BitVec.ofNat 64 nvS9MsUnsatBytes.length,
        nvS9MsHdrPtr, 4096#64, 16#64, ())
      nvS9MsInitMem
      (fun (r, ()) m' =>
        r = true ∧ ∃ c s,
          c.hdr = nvS9MsHdrPtr ∧ c.avail = 4096 ∧ c.mv = 1 ∧ c.nc = 2 ∧
          nvS9MsUnsatCnf.Unsat ∧ MemShrinkSparseInv c s ∧
          (bytes nvS9MsCnfPtr nvS9MsUnsatBytes ⋆ MemShrinkMem c s) m')
      (fun _ _ _ _ => False) := by
  have hm := nv_s9ms_mem_split nvS9MsCnfPtr 4096 (by unfold nvS9MsUnsatBytes; decide)
  apply full_init_state_m5_s9ms_wp fidStep9MsEnv
    (fidStep9MsEnv_row "kissat_parse_header" kissatParseHeaderSpec (i := 14) rfl
      fun _ _ _ _ h => h)
    (fidStep9MsEnv_row "full_fixed_bytes" m7FixedBytesSpec (i := 3) rfl
      fun xs m Q X h => by rw [m7FixedBytesSpec_eq] at h ⊢; exact h)
    (fidStep9MsEnv_row "full_trans_bytes_m7" m7TransBytesSpec (i := 6) rfl
      fun xs m Q X h => by rw [m7TransBytesSpec_eq] at h ⊢; exact h)
    (fidStep9MsEnv_row "full_calc_max_v" s9msCalcMaxVSpec (i := 7) rfl
      fun ⟨h1, h2, h3, h4, ⟨⟩⟩ m Q X h => by rw [s9msCalcMaxVSpec_eq] at h ⊢; exact h)
    (fidStep9MsEnv_row "full_calc_ext_cap_m5" m7CalcExtCapSpec (i := 8) rfl
      fun xs m Q X h => by rw [m7CalcExtCapSpec_eq] at h ⊢; exact h)
    (fidStep9MsEnv_row "full_calc_scr_cap_m5" s9msCalcScrCapSpec (i := 9) rfl
      fun xs m Q X h => by rw [s9msCalcScrCapSpec_eq] at h ⊢; exact h)
    (fidStep9MsEnv_row "full_init_arenas" m7InitArenasSpec (i := 10) rfl
      fun ⟨h1, h2, h3, h4, ⟨⟩⟩ m Q X h => by rw [m7InitArenasSpec_eq] at h ⊢; exact h)
    (fidStep9MsEnv_row "full_init_hdr" m7InitHdrSpec (i := 5) rfl
      fun ⟨h1, h2, h3, h4, ⟨⟩⟩ m Q X h => by rw [m7InitHdrSpec_eq] at h ⊢; exact h)
    (fidStep9MsEnv_row "full_zero_tables1" m7ZeroTables1Spec (i := 1) rfl
      fun ⟨h0, ⟨⟩⟩ m Q X h => by rw [m7ZeroTables1Spec_eq] at h ⊢; exact h)
    (fidStep9MsEnv_row "full_zero_tables2" m7ZeroTables2Spec (i := 2) rfl
      fun ⟨h0, ⟨⟩⟩ m Q X h => by rw [m7ZeroTables2Spec_eq] at h ⊢; exact h)
  rw [m7InitStateSpec_eq]
  refine ⟨nvS9MsUnsatBytes, emp, rfl,
    (by unfold nvS9MsCnfPtr nvS9MsUnsatBytes; decide),
    (by unfold nvS9MsHdrPtr nvS9MsCnfPtr nvS9MsUnsatBytes; decide),
    (by decide),
    (by unfold nvS9MsHdrPtr nvS9MsInitMem; exact hm), ?_, ?_⟩
  · intro _ _ hfail
    have hlt := hfail 1 2 (nvS9MsUnsatBytes.drop 9) nvS9MsUnsat_header
    have hge : ¬ (4096#64).toNat < m7FixedBytes 1 + m7TransBytes 1 + 2 * 40 + 136 := by
      simp only [m7FixedBytes_def, m7TransBytes_def]
      unfold valsBytes markBytes u32FullBytes fullMinDepthOf; decide
    exact absurd hlt hge
  · intro c s j rest m' hhdr hav hph _ _ hsp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      _ _ _ _ _ _ hm'
    rw [sep_emp] at hm'
    simp only [nvS9MsUnsat_header, Option.some.injEq, Prod.mk.injEq] at hph
    refine ⟨rfl, c, s, hhdr, by simpa using hav, hph.1.symm, hph.2.1.symm,
      nvS9MsUnsatCnf_unsat, hsp, hm'⟩

/-- Concrete `Mem 64` NV (`XPost := False`) for `full_m6_mem_init` on an undersized `1,000 B`
workspace (`< 3,456 B`): returns `0#64` cleanly without underflow and preserves memory. -/
theorem nv_s9ms_m6_mem_init_tiny :
    Func.wp fidStep9MsM6Env FullM6Hdr.full_m6_mem_init_body
      (0x2000#64, 0x2000#64 + BitVec.ofNat 64 nvS9MsUnsatBytes.length,
       0x2000#64 + BitVec.ofNat 64 nvS9MsUnsatBytes.length, 1000#64, 16#64, ())
      nvS9MsTinyInitMem
      (fun (r, ()) m' => r = 0#64 ∧ nvS9MsUnsatCnf.Unsat ∧
        (bytes 0x2000#64 nvS9MsUnsatBytes ⋆
          region (0x2000#64 + BitVec.ofNat 64 nvS9MsUnsatBytes.length) 1000) m')
      (fun _ _ _ _ => False) := by
  have hm := nv_s9ms_mem_split 0x2000#64 1000 (by unfold nvS9MsUnsatBytes; decide)
  apply full_m6_mem_init_ms_wp fidStep9MsM6Env
    (fidStep9MsM6Env_row "full_init_state" m7InitStateSpec (i := 12) rfl
      fun ⟨h1, h2, h3, h4, h5, ⟨⟩⟩ m Q X h => by rw [m7InitStateSpec_eq] at h ⊢; exact h)
    (fidStep9MsM6Env_row "m6_hdr_init" m6HdrInitMsSpec (i := 14) rfl
      fun _ _ _ _ h => m6HdrInitMsSpec_monoX h)
  refine fullM6MemInitMsSpec_of rfl (by unfold nvS9MsUnsatBytes; decide) (by decide)
    (by unfold nvS9MsTinyInitMem; exact hm)
    (fun m' hm' _ => by rw [sep_emp] at hm'; exact ⟨rfl, nvS9MsUnsatCnf_unsat, hm'⟩)
    (fun c _ _ _ _ _ _ hcavail _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => by
      have hcav0 : c.avail = 0 := by simpa [fullM6ExtBytes] using hcavail
      have hfx : 1472 ≤ m7FixedBytes c.max_vars := by simp only [m7FixedBytes_def]; omega
      have := c.hsize; omega)

/-- Concrete `Mem 64` UNSAT NV (`XPost := False`, `0` SAT proofs) for `full_m6_mem_init`
on `(x1) ∧ (~x1)` with `6,400 B` workspace: carves `2,304 B` initialized `M6HdrExt` + `4,096 B`
`MemShrinkMem` (`c.mv = 1`, `c.nc = 2`) and returns `work_base + 2304`. -/
theorem nv_s9ms_m6_mem_init_4k :
    Func.wp fidStep9MsM6Env FullM6Hdr.full_m6_mem_init_body
      (0x2000#64, 0x2000#64 + BitVec.ofNat 64 nvS9MsUnsatBytes.length,
       0x2000#64 + BitVec.ofNat 64 nvS9MsUnsatBytes.length, 6400#64, 16#64, ())
      nvS9Ms4kInitMem
      (fun (r, ()) m' => ∃ (c : MemShrinkCfg) (ext : List (BitVec 64)) (s : FullState),
        r = c.hdr ∧ c.hdr = (0x2000#64 + BitVec.ofNat 64 nvS9MsUnsatBytes.length) +
          BitVec.ofNat 64 fullM6ExtBytes ∧
        c.avail = 4096 ∧ c.mv = 1 ∧ c.nc = 2 ∧ nvS9MsUnsatCnf.Unsat ∧
        MsM6HdrExtInitOk ext ∧ MemShrinkM6HdrInv c ext s ∧
        (bytes 0x2000#64 nvS9MsUnsatBytes ⋆ MemShrinkM6HdrMem c ext s) m')
      (fun _ _ _ _ => False) := by
  have hm := nv_s9ms_mem_split 0x2000#64 6400 (by unfold nvS9MsUnsatBytes; decide)
  apply full_m6_mem_init_ms_wp fidStep9MsM6Env
    (fidStep9MsM6Env_row "full_init_state" m7InitStateSpec (i := 12) rfl
      fun ⟨h1, h2, h3, h4, h5, ⟨⟩⟩ m Q X h => by rw [m7InitStateSpec_eq] at h ⊢; exact h)
    (fidStep9MsM6Env_row "m6_hdr_init" m6HdrInitMsSpec (i := 14) rfl
      fun _ _ _ _ h => m6HdrInitMsSpec_monoX h)
  refine fullM6MemInitMsSpec_of rfl (by unfold nvS9MsUnsatBytes; decide) (by decide)
    (by unfold nvS9Ms4kInitMem; exact hm)
    (fun _ _ hfail => by
      rcases hfail with h1 | h2
      · exact absurd h1 (by decide)
      · have hlt := h2 1 2 (nvS9MsUnsatBytes.drop 9) nvS9MsUnsat_header
        have hge : ¬ (6400#64).toNat - fullM6ExtBytes <
            m7FixedBytes 1 + m7TransBytes 1 + 2 * 40 + 136 := by
          simp only [m7FixedBytes_def, m7TransBytes_def]
          unfold valsBytes markBytes u32FullBytes fullMinDepthOf fullM6ExtBytes; decide
        exact absurd hlt hge)
    (fun c ext s j rest m' hchdr hcavail hinv hext_init hparse _ _ _ _ _ _ _ _ _ _ _ _ hm' => by
      rw [sep_emp] at hm'
      simp only [nvS9MsUnsat_header, Option.some.injEq, Prod.mk.injEq] at hparse
      have hcav4k : c.avail = 4096 := by simpa [fullM6ExtBytes] using hcavail
      exact ⟨c, ext, s, rfl, hchdr, hcav4k, hparse.1.symm, hparse.2.1.symm,
        nvS9MsUnsatCnf_unsat, hext_init, hinv, hm'⟩)

end ConcreteUnsatNv

end LeanQbe.T.Examples.Kissat.FullFidelityStep9MemShrink

end
