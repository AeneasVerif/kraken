/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM7MemShrink
public import LeanQbe.T.Examples.Kissat.FullM7MemShrinkProof
public import LeanQbe.T.PrintCpp
public import LeanQbe.T.PrintQbe
public import LeanQbe.T.Legal
meta import LeanQbe.T.Examples.Kissat.FullM7MemShrink
meta import LeanQbe.T.Examples.Kissat.FullM7MemShrinkProof
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal

/-!
# Verification, Compilation Guards, Splice & Axiom Audit for `FullM7MemShrink`

1. Executable `#guard` checks on standalone `m7MemShrinkModule` (`12` fns, `1` extern, `0` exits)
   and `m7SplicedM7Module` (`421 = 410 + 11` fns spliced onto `FullM7.m7Module`), `PrintCpp`,
   `PrintQbe`, and 4-ISA legalization (`.aarch64`, `.scalar64`, `.x64AVX2`, `.x64AVX512`).
2. Audit-ready restated headline theorems covering `Wf`, `checkAcyclic`, all `12` `Func.wp`
   contracts, closed `ModuleOk`, `11` canonical `SpecEntry.Impl` bridges, `-40.4%` footprint
   shrinkage, transient pool mutual exclusion, and concrete `Mem 64` UNSAT non-vacuity
   (`XPost := False`, zero SAT model proofs).
3. Single-line `< 115c` `#print axioms` checks (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.KissatM7MemShrinkTest

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.PrintCpp
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullParseInitSpecs
open LeanQbe.T.Examples.Kissat.FullM7
open LeanQbe.T.Examples.Kissat.FullM7MemShrink
open Kraken.Bedrock2.Test

/-! ## 1. Executable `#guard` Codegen, Legalization & `FullM7` Splice Checks -/

#guard m7MemShrinkFns.length == 12
#guard m7MemShrinkExterns.length == 1
#guard m7MemShrinkModule.exits.isEmpty == true
#guard m7MemShrinkModule.checkAcyclic == true
#guard m7MemShrinkSpecTable.length == 13
#guard m7MemShrinkSpecTable.all (·.noExit) == true
#guard m7MemShrinkSpecTable.map (fun e => (e.name, e.as, e.rs)) == m7MemShrinkModule.sigs
#guard m7ZeroTables1Fn.name == "full_zero_tables1"
#guard m7ZeroTables2Fn.name == "full_zero_tables2"
#guard m7FixedBytesFn.name == "full_fixed_bytes"
#guard m7InitPtrsFn.name == "full_init_ptrs"
#guard m7InitHdrFn.name == "full_init_hdr"
#guard m7CalcMaxVFn.name == "full_calc_max_v"
#guard m7CalcExtCapM5Fn.name == "full_calc_ext_cap_m5"
#guard m7CalcScrCapM5Fn.name == "full_calc_scr_cap_m5"
#guard m7InitArenasFn.name == "full_init_arenas"
#guard m7InitStateFn.name == "full_init_state"
#guard m7InitStateM5Fn.name == "full_init_state_m5"
#guard m7FixedBytes 10000 == 909592
#guard Full.fullFixedBytes 10000 == 1519592
#guard Full.fullFixedBytes 10000 - m7FixedBytes 10000 == 610000
#guard (ppTModule m7MemShrinkModule).isOk
#guard (PrintQbe.module m7MemShrinkModule).isOk
#guard (ppModule (m7MemShrinkFns.map (Fn.legal .aarch64))).isOk
#guard (ppModule (m7MemShrinkFns.map (Fn.legal .scalar64))).isOk
#guard (ppModule (m7MemShrinkFns.map (Fn.legal .x64AVX2))).isOk
#guard m7MemShrinkFns.all fun fn => (Fn.legal .aarch64 fn).body.isLegal .aarch64
#guard m7MemShrinkFns.all fun fn => (Fn.legal .scalar64 fn).body.isLegal .scalar64
#guard m7MemShrinkFns.all fun fn => (Fn.legal .x64AVX2 fn).body.isLegal .x64AVX2
#guard m7MemShrinkFns.all fun fn => (Fn.legal .x64AVX512 fn).body.isLegal .x64AVX512

#guard m7SplicedM7Fns.length == FullM7.m7Fns.length + 11
#guard (m7SplicedM7Fns.map Fn.name).eraseDups.length == m7SplicedM7Fns.length
#guard m7SplicedM7Module.exits.isEmpty == true
#guard m7SplicedM7Module.externs.isEmpty == true
#guard m7SplicedM7Module.checkAcyclic == true
#guard (ppTModule m7SplicedM7Module).isOk
#guard (PrintQbe.module m7SplicedM7Module).isOk
#guard m7SplicedM7Fns.all fun fn => (Fn.legal .aarch64 fn).body.isLegal .aarch64
#guard m7SplicedM7Fns.all fun fn => (Fn.legal .scalar64 fn).body.isLegal .scalar64
#guard m7SplicedM7Fns.all fun fn => (Fn.legal .x64AVX2 fn).body.isLegal .x64AVX2
#guard m7SplicedM7Fns.all fun fn => (Fn.legal .x64AVX512 fn).body.isLegal .x64AVX512

/-! ## 2. Audit-Ready Restated Headline Theorems -/

theorem ms_fns_wf : ∀ f ∈ m7MemShrinkFns, f.Wf := m7MemShrinkFns_wf
theorem ms_acyc : m7MemShrinkModule.checkAcyclic = true := m7MemShrink_acyclic
theorem ms_tbl_len : m7MemShrinkSpecTable.length = 13 := m7MemShrinkSpecTable_length
theorem ms_tbl_impl : TableImpl m7MemShrinkEnv m7MemShrinkModule.fns m7MemShrinkSpecTable :=
  m7MemShrink_tableImpl
theorem ms_mod_ok : ModuleOk m7MemShrinkEnv m7MemShrinkModule := m7MemShrink_moduleOk
theorem ms_spliced_wf : ∀ f ∈ m7SplicedM7Fns, f.Wf := m7SplicedM7Fns_wf
theorem ms_spliced_len : m7SplicedM7Fns.length = FullM7.m7Fns.length + 11 :=
  m7SplicedM7Fns_length
theorem ms_spliced_acyc : m7SplicedM7Module.checkAcyclic = true := m7SplicedM7_acyclic

theorem ms_shrink_40pct :
    1000 * (Full.fullFixedBytes 10000 - m7FixedBytes 10000) ≥ 401 * Full.fullFixedBytes 10000 ∧
      1000 * (Full.fullFixedBytes 100000 - m7FixedBytes 100000) ≥
        403 * Full.fullFixedBytes 100000 ∧
      ∀ n, Full.fullFixedBytes n - m7FixedBytes n =
        2 * valsBytes n + markBytes n + 56 * n :=
  m7FixedBytes_shrink_40pct

theorem ms_trans_excl {c : MemShrinkCfg} {m : Mem 64} (h : MemShrinkTransRegions c m) :
    (∃ ws ws1 ws2 tmk trc wv wb,
      ws.length = 2 * c.max_vars ∧ ws1.length = 2 * c.max_vars ∧
      ws2.length = 2 * c.max_vars ∧ tmk.length = 2 * c.max_vars ∧
      trc.length = 2 * c.max_vars ∧ wv.length = 2 * c.max_vars ∧
      wb.length = c.max_vars ∧ MemShrinkTransWalk c ws ws1 ws2 tmk trc wv wb m) ∧
    (∃ ws ws1 ws2 tmk trc repr sig,
      ws.length = 2 * c.max_vars ∧ ws1.length = 2 * c.max_vars ∧
      ws2.length = 2 * c.max_vars ∧ tmk.length = 2 * c.max_vars ∧
      trc.length = 2 * c.max_vars ∧ repr.length = 2 * c.max_vars ∧
      sig.length = c.max_vars ∧ MemShrinkTransCong c ws ws1 ws2 tmk trc repr sig m) :=
  m7_transient_phases_excl h

theorem ms_fill_wp (Γ : Env) :
    ∀ a m Q X, m7FillU64Spec a m Q X → Func.wp Γ full_fill_u64_m7_body a m Q X :=
  full_fill_u64_m7_wp Γ

theorem ms_zt1_wp (Γ : Env) (hFill : EnvSpec Γ "full_fill_u64_m7" m7FillU64Spec) :
    ∀ a m Q X, m7ZeroTables1Spec a m Q X → Func.wp Γ full_zero_tables1_m7_body a m Q X :=
  full_zero_tables1_m7_wp Γ hFill

theorem ms_zt2_wp (Γ : Env) (hFill : EnvSpec Γ "full_fill_u64_m7" m7FillU64Spec) :
    ∀ a m Q X, m7ZeroTables2Spec a m Q X → Func.wp Γ full_zero_tables2_m7_body a m Q X :=
  full_zero_tables2_m7_wp Γ hFill

theorem ms_fixed_wp (Γ : Env) :
    ∀ a m Q X, m7FixedBytesSpec a m Q X → Func.wp Γ full_fixed_bytes_m7_body a m Q X :=
  full_fixed_bytes_m7_wp Γ

theorem ms_trans_wp (Γ : Env) :
    ∀ a m Q X, m7TransBytesSpec a m Q X → Func.wp Γ full_trans_bytes_m7_body a m Q X :=
  full_trans_bytes_m7_wp Γ

theorem ms_ptrs_wp (Γ : Env) :
    ∀ a m Q X, m7InitPtrsSpec a m Q X → Func.wp Γ full_init_ptrs_m7_body a m Q X :=
  full_init_ptrs_m7_wp Γ

theorem ms_hdr_wp (Γ : Env) :
    ∀ a m Q X, m7InitHdrSpec a m Q X → Func.wp Γ full_init_hdr_m7_body a m Q X :=
  full_init_hdr_m7_wp Γ

theorem ms_maxv_wp (Γ : Env)
    (hFx : EnvSpec Γ "full_fixed_bytes_m7" m7FixedBytesSpec)
    (hTr : EnvSpec Γ "full_trans_bytes_m7" m7TransBytesSpec) :
    ∀ a m Q X, m7CalcMaxVSpec a m Q X → Func.wp Γ full_calc_max_v_m7_body a m Q X :=
  full_calc_max_v_m7_wp Γ hFx hTr

theorem ms_ext_wp (Γ : Env) :
    ∀ a m Q X, m7CalcExtCapSpec a m Q X → Func.wp Γ full_calc_ext_cap_m7_body a m Q X :=
  full_calc_ext_cap_m7_wp Γ

theorem ms_scr_wp (Γ : Env) :
    ∀ a m Q X, m7CalcScrCapSpec a m Q X → Func.wp Γ full_calc_scr_cap_m7_body a m Q X :=
  full_calc_scr_cap_m7_wp Γ

theorem ms_arenas_wp (Γ : Env) (hPtrs : EnvSpec Γ "full_init_ptrs_m7" m7InitPtrsSpec) :
    ∀ a m Q X, m7InitArenasSpec a m Q X → Func.wp Γ full_init_arenas_m7_body a m Q X :=
  full_init_arenas_m7_wp Γ hPtrs

theorem ms_init_wp (Γ : Env)
    (hHdr : EnvSpec Γ "kissat_parse_header" kissatParseHeaderSpec)
    (hFixed : EnvSpec Γ "full_fixed_bytes_m7" m7FixedBytesSpec)
    (hTrans : EnvSpec Γ "full_trans_bytes_m7" m7TransBytesSpec)
    (hMaxV : EnvSpec Γ "full_calc_max_v_m7" m7CalcMaxVSpec)
    (hExt : EnvSpec Γ "full_calc_ext_cap_m7" m7CalcExtCapSpec)
    (hScr : EnvSpec Γ "full_calc_scr_cap_m7" m7CalcScrCapSpec)
    (hArenas : EnvSpec Γ "full_init_arenas_m7" m7InitArenasSpec)
    (hInitHdr : EnvSpec Γ "full_init_hdr_m7" m7InitHdrSpec)
    (hZt1 : EnvSpec Γ "full_zero_tables1_m7" m7ZeroTables1Spec)
    (hZt2 : EnvSpec Γ "full_zero_tables2_m7" m7ZeroTables2Spec) :
    ∀ a m Q X, m7InitStateSpec a m Q X → Func.wp Γ full_init_state_m7_body a m Q X :=
  full_init_state_m7_wp Γ hHdr hFixed hTrans hMaxV hExt hScr hArenas hInitHdr hZt1 hZt2

theorem ms_zt1_impl : SpecEntry.Impl m7MemShrinkEnv m7ZeroTables1Fn
    (.ofFn m7ZeroTables1Fn m7ZeroTables1Spec true) := m7ZeroTables1Fn_impl
theorem ms_zt2_impl : SpecEntry.Impl m7MemShrinkEnv m7ZeroTables2Fn
    (.ofFn m7ZeroTables2Fn m7ZeroTables2Spec true) := m7ZeroTables2Fn_impl
theorem ms_fx_impl : SpecEntry.Impl m7MemShrinkEnv m7FixedBytesFn
    (.ofFn m7FixedBytesFn m7FixedBytesSpec true) := m7FixedBytesFn_impl
theorem ms_ptrs_impl : SpecEntry.Impl m7MemShrinkEnv m7InitPtrsFn
    (.ofFn m7InitPtrsFn m7InitPtrsSpec true) := m7InitPtrsFn_impl
theorem ms_hdr_impl : SpecEntry.Impl m7MemShrinkEnv m7InitHdrFn
    (.ofFn m7InitHdrFn m7InitHdrSpec true) := m7InitHdrFn_impl
theorem ms_maxv_impl : SpecEntry.Impl m7MemShrinkEnv m7CalcMaxVFn
    (.ofFn m7CalcMaxVFn m7CalcMaxVSpec true) := m7CalcMaxVFn_impl
theorem ms_ext_impl : SpecEntry.Impl m7MemShrinkEnv m7CalcExtCapM5Fn
    (.ofFn m7CalcExtCapM5Fn m7CalcExtCapSpec true) := m7CalcExtCapM5Fn_impl
theorem ms_scr_impl : SpecEntry.Impl m7MemShrinkEnv m7CalcScrCapM5Fn
    (.ofFn m7CalcScrCapM5Fn m7CalcScrCapSpec true) := m7CalcScrCapM5Fn_impl
theorem ms_ar_impl : SpecEntry.Impl m7MemShrinkEnv m7InitArenasFn
    (.ofFn m7InitArenasFn m7InitArenasSpec true) := m7InitArenasFn_impl
theorem ms_st_impl : SpecEntry.Impl m7MemShrinkEnv m7InitStateFn
    (.ofFn m7InitStateFn m7InitStateSpec true) := m7InitStateFn_impl
theorem ms_stm5_impl : SpecEntry.Impl m7MemShrinkEnv m7InitStateM5Fn
    (.ofFn m7InitStateM5Fn m7InitStateSpec true) := m7InitStateM5Fn_impl

theorem ms_nv_unsat :
    Func.wp m7MemShrinkEnv full_init_state_m7_body
      (nvM7CnfPtr, nvM7CnfPtr + BitVec.ofNat 64 nvM7UnsatBytes.length,
        nvM7HdrPtr, 4096#64, 16#64, ())
      nvM7InitMem
      (fun (r, ()) m' =>
        r = true ∧ ∃ c s,
          c.hdr = nvM7HdrPtr ∧ c.avail = 4096 ∧ c.mv = 1 ∧ c.nc = 2 ∧
          nvM7UnsatCnf.Unsat ∧ MemShrinkSparseInv c s ∧
          (bytes nvM7CnfPtr nvM7UnsatBytes ⋆ MemShrinkMem c s) m')
      (fun _ _ _ _ => False) :=
  nv_m7_init_state_unsat

theorem ms_nv_small_unsat :
    Func.wp m7MemShrinkEnv full_init_state_m7_body
      (nvM7CnfPtr, nvM7CnfPtr + BitVec.ofNat 64 nvM7UnsatBytes.length,
        nvM7HdrPtr, 1200#64, 16#64, ())
      nvM7SmallMem
      (fun (r, ()) m' =>
        r = false ∧ nvM7UnsatCnf.Unsat ∧
          (bytes nvM7CnfPtr nvM7UnsatBytes ⋆ region nvM7HdrPtr 1200) m')
      (fun _ _ _ _ => False) :=
  nv_m7_init_state_small_unsat

end LeanQbeTest.T.KissatM7MemShrinkTest

/-! ## 3. Single-Line `#print axioms` Audit (`⊆ [propext, Classical.choice, Quot.sound]`) -/

abbrev ms_ax_wf := @LeanQbeTest.T.KissatM7MemShrinkTest.ms_fns_wf
abbrev ms_ax_acyc := @LeanQbeTest.T.KissatM7MemShrinkTest.ms_acyc
abbrev ms_ax_tlen := @LeanQbeTest.T.KissatM7MemShrinkTest.ms_tbl_len
abbrev ms_ax_tbl := @LeanQbeTest.T.KissatM7MemShrinkTest.ms_tbl_impl
abbrev ms_ax_mod := @LeanQbeTest.T.KissatM7MemShrinkTest.ms_mod_ok
abbrev ms_ax_swf := @LeanQbeTest.T.KissatM7MemShrinkTest.ms_spliced_wf
abbrev ms_ax_slen := @LeanQbeTest.T.KissatM7MemShrinkTest.ms_spliced_len
abbrev ms_ax_sacyc := @LeanQbeTest.T.KissatM7MemShrinkTest.ms_spliced_acyc
abbrev ms_ax_pct := @LeanQbeTest.T.KissatM7MemShrinkTest.ms_shrink_40pct
abbrev ms_ax_excl := @LeanQbeTest.T.KissatM7MemShrinkTest.ms_trans_excl
abbrev ms_ax_fill := @LeanQbeTest.T.KissatM7MemShrinkTest.ms_fill_wp
abbrev ms_ax_zt1 := @LeanQbeTest.T.KissatM7MemShrinkTest.ms_zt1_wp
abbrev ms_ax_zt2 := @LeanQbeTest.T.KissatM7MemShrinkTest.ms_zt2_wp
abbrev ms_ax_fx := @LeanQbeTest.T.KissatM7MemShrinkTest.ms_fixed_wp
abbrev ms_ax_tr := @LeanQbeTest.T.KissatM7MemShrinkTest.ms_trans_wp
abbrev ms_ax_ptrs := @LeanQbeTest.T.KissatM7MemShrinkTest.ms_ptrs_wp
abbrev ms_ax_hdr := @LeanQbeTest.T.KissatM7MemShrinkTest.ms_hdr_wp
abbrev ms_ax_maxv := @LeanQbeTest.T.KissatM7MemShrinkTest.ms_maxv_wp
abbrev ms_ax_ext := @LeanQbeTest.T.KissatM7MemShrinkTest.ms_ext_wp
abbrev ms_ax_scr := @LeanQbeTest.T.KissatM7MemShrinkTest.ms_scr_wp
abbrev ms_ax_ar := @LeanQbeTest.T.KissatM7MemShrinkTest.ms_arenas_wp
abbrev ms_ax_init := @LeanQbeTest.T.KissatM7MemShrinkTest.ms_init_wp
abbrev ms_ax_izt1 := @LeanQbeTest.T.KissatM7MemShrinkTest.ms_zt1_impl
abbrev ms_ax_izt2 := @LeanQbeTest.T.KissatM7MemShrinkTest.ms_zt2_impl
abbrev ms_ax_ifx := @LeanQbeTest.T.KissatM7MemShrinkTest.ms_fx_impl
abbrev ms_ax_iptrs := @LeanQbeTest.T.KissatM7MemShrinkTest.ms_ptrs_impl
abbrev ms_ax_ihdr := @LeanQbeTest.T.KissatM7MemShrinkTest.ms_hdr_impl
abbrev ms_ax_imaxv := @LeanQbeTest.T.KissatM7MemShrinkTest.ms_maxv_impl
abbrev ms_ax_iext := @LeanQbeTest.T.KissatM7MemShrinkTest.ms_ext_impl
abbrev ms_ax_iscr := @LeanQbeTest.T.KissatM7MemShrinkTest.ms_scr_impl
abbrev ms_ax_iar := @LeanQbeTest.T.KissatM7MemShrinkTest.ms_ar_impl
abbrev ms_ax_ist := @LeanQbeTest.T.KissatM7MemShrinkTest.ms_st_impl
abbrev ms_ax_istm5 := @LeanQbeTest.T.KissatM7MemShrinkTest.ms_stm5_impl
abbrev ms_ax_nvu := @LeanQbeTest.T.KissatM7MemShrinkTest.ms_nv_unsat
abbrev ms_ax_nvs := @LeanQbeTest.T.KissatM7MemShrinkTest.ms_nv_small_unsat

#print axioms ms_ax_wf
#print axioms ms_ax_acyc
#print axioms ms_ax_tlen
#print axioms ms_ax_tbl
#print axioms ms_ax_mod
#print axioms ms_ax_swf
#print axioms ms_ax_slen
#print axioms ms_ax_sacyc
#print axioms ms_ax_pct
#print axioms ms_ax_excl
#print axioms ms_ax_fill
#print axioms ms_ax_zt1
#print axioms ms_ax_zt2
#print axioms ms_ax_fx
#print axioms ms_ax_tr
#print axioms ms_ax_ptrs
#print axioms ms_ax_hdr
#print axioms ms_ax_maxv
#print axioms ms_ax_ext
#print axioms ms_ax_scr
#print axioms ms_ax_ar
#print axioms ms_ax_init
#print axioms ms_ax_izt1
#print axioms ms_ax_izt2
#print axioms ms_ax_ifx
#print axioms ms_ax_iptrs
#print axioms ms_ax_ihdr
#print axioms ms_ax_imaxv
#print axioms ms_ax_iext
#print axioms ms_ax_iscr
#print axioms ms_ax_iar
#print axioms ms_ax_ist
#print axioms ms_ax_istm5
#print axioms ms_ax_nvu
#print axioms ms_ax_nvs
