/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM7MemShrinkV5
public import LeanQbe.T.Examples.Kissat.FullM7MemShrinkV5Proof
public import LeanQbe.T.PrintCpp
public import LeanQbe.T.PrintQbe
public import LeanQbe.T.Legal
meta import LeanQbe.T.Examples.Kissat.FullM7MemShrinkV5
meta import LeanQbe.T.Examples.Kissat.FullM7MemShrinkV5Proof
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal

/-!
# Verification, V5 BVA Parity Guards, `ModuleOk`, Framing & Axiom Audit (`KissatM7MemShrinkV5Test`)

1. Executable `#guard` checks on `m7msStandaloneModule` (`14` fns, `1` extern, `0` exits),
   `m7msM6Module` (`16` fns, `1` extern, `0` exits), V5 `cand = 4096` BVA parity (`Cause B` fix),
   `PrintCpp`, `PrintQbe`, and 4-ISA legalization.
2. Audit-ready restated headline theorems covering `Wf`, `checkAcyclic`, `m7msStandalone_moduleOk`,
   `m7msM6_moduleOk`, `full_calc_max_v_m7v5_wp`, `full_init_arenas_m7ms_wp`,
   `full_init_state_m7ms_wp`, `full_compact_vars_m7ms_wp`, `memShrinkMem_to_region`,
   `memShrinkM6HdrMem_to_region`, `memShrinkM6Hdr_frame`, `m6_hdr_init_ms_wp`,
   `full_m6_mem_init_ms_wp`, and concrete `Mem 64` UNSAT non-vacuity (`XPost := False`).
3. Single-line `< 115c` `#print axioms` checks (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.KissatM7MemShrinkV5Test

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.PrintCpp
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM7
open LeanQbe.T.Examples.Kissat.FullM7MemShrink
open LeanQbe.T.Examples.Kissat.FullM7MemShrinkV5
open Kraken.Bedrock2.Test

/-! ## 1. Executable `#guard` V5 Parity, Legalization & Module Checks -/

#guard m7msStandaloneFns.length == 14
#guard m7msStandaloneExterns.length == 1
#guard m7msStandaloneModule.exits.isEmpty == true
#guard m7msStandaloneModule.checkAcyclic == true
#guard m7msSpecTable.length == 15
#guard m7msSpecTable.all (·.noExit) == true
#guard m7msSpecTable.map (fun e => (e.name, e.as, e.rs)) == m7msStandaloneModule.sigs
#guard m7msM6Module.fns.length == 16
#guard m7msM6Module.exits.isEmpty == true
#guard m7msM6Module.checkAcyclic == true
#guard m7msM6SpecTable.length == 17
#guard m7msM6SpecTable.all (·.noExit) == true
#guard m7msM6SpecTable.map (fun e => (e.name, e.as, e.rs)) == m7msM6Module.sigs
#guard m7V5BvaCap 20000000 2000 100000 1000000 == 4096
#guard m7V5CalcMaxV 20000000 2000 100000 (m7FixedBytes 2000) == 6096
#guard (ppTModule m7msStandaloneModule).isOk
#guard (PrintQbe.module m7msStandaloneModule).isOk
#guard (ppTModule m7msM6Module).isOk
#guard (PrintQbe.module m7msM6Module).isOk
#guard m7msM6Module.fns.all fun fn => (Fn.legal .aarch64 fn).body.isLegal .aarch64
#guard m7msM6Module.fns.all fun fn => (Fn.legal .scalar64 fn).body.isLegal .scalar64
#guard m7msM6Module.fns.all fun fn => (Fn.legal .x64AVX2 fn).body.isLegal .x64AVX2
#guard m7msM6Module.fns.all fun fn => (Fn.legal .x64AVX512 fn).body.isLegal .x64AVX512

/-! ## 2. Audit-Ready Restated Headline Theorems -/

theorem msv5_standalone_wf : ∀ f ∈ m7msStandaloneFns, f.Wf := m7msStandaloneFns_wf
theorem msv5_standalone_acyc : m7msStandaloneModule.checkAcyclic = true := m7msStandalone_acyclic
theorem msv5_standalone_mod_ok : ModuleOk m7msEnv m7msStandaloneModule := m7msStandalone_moduleOk
theorem msv5_m6_wf : AllFns Fn.Wf m7msM6Module.fns := m7msM6_fns_wf
theorem msv5_m6_acyc : m7msM6Module.checkAcyclic = true := m7msM6_acyclic
theorem msv5_m6_mod_ok : ModuleOk m7msM6Env m7msM6Module := m7msM6_moduleOk

theorem msv5_calc_max_v_wp (Γ : Env)
    (hFixed : EnvSpec Γ "full_fixed_bytes" m7FixedBytesSpec)
    (hTrans : EnvSpec Γ "full_trans_bytes_m7" m7TransBytesSpec) :
    ∀ a m Q X, m7V5CalcMaxVSpec a m Q X → Func.wp Γ full_calc_max_v_m7v5_body a m Q X :=
  full_calc_max_v_m7v5_wp Γ hFixed hTrans

theorem msv5_init_arenas_wp (Γ : Env)
    (hPtrs : EnvSpec Γ "full_init_ptrs" m7InitPtrsSpec) :
    ∀ a m Q X, m7InitArenasSpec a m Q X → Func.wp Γ full_init_arenas_m7ms_body a m Q X :=
  full_init_arenas_m7ms_wp Γ hPtrs

theorem msv5_init_state_wp (Γ : Env)
    (hHdr : EnvSpec Γ "kissat_parse_header" kissatParseHeaderSpec)
    (hFixed : EnvSpec Γ "full_fixed_bytes" m7FixedBytesSpec)
    (hTrans : EnvSpec Γ "full_trans_bytes_m7" m7TransBytesSpec)
    (hMaxV : EnvSpec Γ "full_calc_max_v" m7V5CalcMaxVSpec)
    (hExt : EnvSpec Γ "full_calc_ext_cap_m5" m7CalcExtCapSpec)
    (hScr : EnvSpec Γ "full_calc_scr_cap_m5" m7CalcScrCapSpec)
    (hArenas : EnvSpec Γ "full_init_arenas" m7InitArenasSpec)
    (hInitHdr : EnvSpec Γ "full_init_hdr" m7InitHdrSpec)
    (hZt1 : EnvSpec Γ "full_zero_tables1" m7ZeroTables1Spec)
    (hZt2 : EnvSpec Γ "full_zero_tables2" m7ZeroTables2Spec) :
    ∀ a m Q X, m7InitStateSpec a m Q X → Func.wp Γ full_init_state_m7ms_body a m Q X :=
  full_init_state_m7ms_wp Γ hHdr hFixed hTrans hMaxV hExt hScr hArenas hInitHdr hZt1 hZt2

theorem msv5_init_wrap_wp (Γ : Env)
    (hM5 : EnvSpec Γ "full_init_state_m5" m7InitStateSpec) :
    ∀ a m Q X, m7InitStateSpec a m Q X → Func.wp Γ full_init_state_wrap_m7ms_body a m Q X :=
  full_init_state_wrap_m7ms_wp Γ hM5

theorem msv5_compact_wp (Γ : Env) :
    ∀ a m Q X, m7msCompactVarsSpec a m Q X → Func.wp Γ full_compact_vars_m7ms_body a m Q X :=
  full_compact_vars_m7ms_wp Γ

theorem msv5_mem_to_region {c : MemShrinkCfg} {s : FullState} {m : Mem 64}
    (hlen : MemShrinkLengthsOk c s) (hm : MemShrinkMem c s m) :
    region c.hdr c.avail m :=
  memShrinkMem_to_region hlen hm

theorem msv5_m6_to_region {c : MemShrinkCfg} {ext : List (BitVec 64)} {s : FullState}
    {m : Mem 64} (hcfg : MemShrinkM6HdrCfgOk c) (hext : M6HdrExtOk ext)
    (hlen : MemShrinkLengthsOk c s) (hm : MemShrinkM6HdrMem c ext s m) :
    region (m6ExtAddr c.hdr) (fullM6ExtBytes + c.avail) m :=
  memShrinkM6HdrMem_to_region hcfg hext hlen hm

theorem msv5_m6_frame {c : MemShrinkCfg} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {P : (FullState → Mem 64 → Prop) → Prop}
    (hfn : ∀ F : Mem 64 → Prop,
      (MemShrinkMem c s ⋆ F) m → P (fun s' m' => (MemShrinkMem c s' ⋆ F) m'))
    (hm : (MemShrinkM6HdrMem c ext s ⋆ R) m) :
    P (fun s' m' => (MemShrinkM6HdrMem c ext s' ⋆ R) m') :=
  memShrinkM6Hdr_frame hfn hm

theorem msv5_m6_init_wp (Γ : Env) :
    ∀ a m Q X, m6HdrInitMsSpec a m Q X → Func.wp Γ m6_hdr_init_body a m Q X :=
  m6_hdr_init_ms_wp Γ

theorem msv5_m6_mem_init_wp (Γ : Env)
    (hInitState : EnvSpec Γ "full_init_state" m7InitStateSpec)
    (hHdrInit : EnvSpec Γ "m6_hdr_init" m6HdrInitMsSpec) :
    ∀ a m Q X, fullM6MemInitMsSpec a m Q X → Func.wp Γ full_m6_mem_init_body a m Q X :=
  full_m6_mem_init_ms_wp Γ hInitState hHdrInit

theorem msv5_nv_init_unsat :
    Func.wp m7msEnv full_init_state_m7ms_body
      (nvMsCnfPtr, nvMsCnfPtr + BitVec.ofNat 64 nvMsUnsatBytes.length,
        nvMsHdrPtr, 4096#64, 16#64, ())
      nvMsInitMem
      (fun (r, ()) m' =>
        r = true ∧ ∃ c s,
          c.hdr = nvMsHdrPtr ∧ c.avail = 4096 ∧ c.mv = 1 ∧ c.nc = 2 ∧
          nvMsUnsatCnf.Unsat ∧ MemShrinkSparseInv c s ∧
          (bytes nvMsCnfPtr nvMsUnsatBytes ⋆ MemShrinkMem c s) m')
      (fun _ _ _ _ => False) :=
  nv_m7ms_init_state_unsat

theorem msv5_nv_m6_tiny :
    Func.wp m7msM6Env full_m6_mem_init_body
      (0x2000#64, 0x2000#64 + BitVec.ofNat 64 nvMsUnsatBytes.length,
       0x2000#64 + BitVec.ofNat 64 nvMsUnsatBytes.length, 1000#64, 16#64, ())
      nvMsTinyInitMem
      (fun (r, ()) m' => r = 0#64 ∧ nvMsUnsatCnf.Unsat ∧
        (bytes 0x2000#64 nvMsUnsatBytes ⋆
          region (0x2000#64 + BitVec.ofNat 64 nvMsUnsatBytes.length) 1000) m')
      (fun _ _ _ _ => False) :=
  nv_m7ms_m6_mem_init_tiny

theorem msv5_nv_m6_4k :
    Func.wp m7msM6Env full_m6_mem_init_body
      (0x2000#64, 0x2000#64 + BitVec.ofNat 64 nvMsUnsatBytes.length,
       0x2000#64 + BitVec.ofNat 64 nvMsUnsatBytes.length, 6400#64, 16#64, ())
      nvMs4kInitMem
      (fun (r, ()) m' => ∃ (c : MemShrinkCfg) (ext : List (BitVec 64)) (s : FullState),
        r = c.hdr ∧ c.hdr = (0x2000#64 + BitVec.ofNat 64 nvMsUnsatBytes.length) +
          BitVec.ofNat 64 fullM6ExtBytes ∧
        c.avail = 4096 ∧ c.mv = 1 ∧ c.nc = 2 ∧ nvMsUnsatCnf.Unsat ∧
        MsM6HdrExtInitOk ext ∧ MemShrinkM6HdrInv c ext s ∧
        (bytes 0x2000#64 nvMsUnsatBytes ⋆ MemShrinkM6HdrMem c ext s) m')
      (fun _ _ _ _ => False) :=
  nv_m7ms_m6_mem_init_4k

end LeanQbeTest.T.KissatM7MemShrinkV5Test

/-! ## 3. Single-Line `#print axioms` Audit (`⊆ [propext, Classical.choice, Quot.sound]`) -/

abbrev msv5_ax_swf := @LeanQbeTest.T.KissatM7MemShrinkV5Test.msv5_standalone_wf
abbrev msv5_ax_sacyc := @LeanQbeTest.T.KissatM7MemShrinkV5Test.msv5_standalone_acyc
abbrev msv5_ax_smod := @LeanQbeTest.T.KissatM7MemShrinkV5Test.msv5_standalone_mod_ok
abbrev msv5_ax_mwf := @LeanQbeTest.T.KissatM7MemShrinkV5Test.msv5_m6_wf
abbrev msv5_ax_macyc := @LeanQbeTest.T.KissatM7MemShrinkV5Test.msv5_m6_acyc
abbrev msv5_ax_mmod := @LeanQbeTest.T.KissatM7MemShrinkV5Test.msv5_m6_mod_ok
abbrev msv5_ax_maxv := @LeanQbeTest.T.KissatM7MemShrinkV5Test.msv5_calc_max_v_wp
abbrev msv5_ax_arenas := @LeanQbeTest.T.KissatM7MemShrinkV5Test.msv5_init_arenas_wp
abbrev msv5_ax_init := @LeanQbeTest.T.KissatM7MemShrinkV5Test.msv5_init_state_wp
abbrev msv5_ax_wrap := @LeanQbeTest.T.KissatM7MemShrinkV5Test.msv5_init_wrap_wp
abbrev msv5_ax_cmp := @LeanQbeTest.T.KissatM7MemShrinkV5Test.msv5_compact_wp
abbrev msv5_ax_reg := @LeanQbeTest.T.KissatM7MemShrinkV5Test.msv5_mem_to_region
abbrev msv5_ax_m6reg := @LeanQbeTest.T.KissatM7MemShrinkV5Test.msv5_m6_to_region
abbrev msv5_ax_m6frm := @LeanQbeTest.T.KissatM7MemShrinkV5Test.msv5_m6_frame
abbrev msv5_ax_m6ini := @LeanQbeTest.T.KissatM7MemShrinkV5Test.msv5_m6_init_wp
abbrev msv5_ax_m6mem := @LeanQbeTest.T.KissatM7MemShrinkV5Test.msv5_m6_mem_init_wp
abbrev msv5_ax_nv_st := @LeanQbeTest.T.KissatM7MemShrinkV5Test.msv5_nv_init_unsat
abbrev msv5_ax_nv_ty := @LeanQbeTest.T.KissatM7MemShrinkV5Test.msv5_nv_m6_tiny
abbrev msv5_ax_nv_4k := @LeanQbeTest.T.KissatM7MemShrinkV5Test.msv5_nv_m6_4k

#print axioms msv5_ax_swf
#print axioms msv5_ax_sacyc
#print axioms msv5_ax_smod
#print axioms msv5_ax_mwf
#print axioms msv5_ax_macyc
#print axioms msv5_ax_mmod
#print axioms msv5_ax_maxv
#print axioms msv5_ax_arenas
#print axioms msv5_ax_init
#print axioms msv5_ax_wrap
#print axioms msv5_ax_cmp
#print axioms msv5_ax_reg
#print axioms msv5_ax_m6reg
#print axioms msv5_ax_m6frm
#print axioms msv5_ax_m6ini
#print axioms msv5_ax_m6mem
#print axioms msv5_ax_nv_st
#print axioms msv5_ax_nv_ty
#print axioms msv5_ax_nv_4k
