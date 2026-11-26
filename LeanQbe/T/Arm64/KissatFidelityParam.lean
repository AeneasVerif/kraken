/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Arm64.KissatAbi
public import LeanQbe.T.Examples.Kissat.KissatCertParamCommon
public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep9Proof
public import LeanQbe.T.Examples.Kissat.FullFidelityInlPolicy
import Kraken.Mem
import Kraken.Separation

/-!
# KissatFidelity (`504` fns) Tier-1 Parameterized AAPCS64 Arm64 Theorems

Proves full-module `FnSpec`, concrete Kraken AArch64 `Eventually` UNSAT soundness, non-vacuity,
and closed-host `run_unsat` parameterized over both raw
`compileModuleOptInlinePolicy ... = .ok (code, bounds)` and `cert : FidCertArm64`
(exposing both exact `cert.bound` and fixed `2048`-byte stack contracts) over
`FullFidelityAssemblyStep9.fidStep9Module` (`504` fns).
Imports zero `*Cert*`, zero materialized `*Inl*`, and zero `MainCertElab` modules (`std3`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Arm64.KissatFidelityParam

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.KissatCertCommon
open LeanQbe.T.Examples.Kissat.KissatCertParamCommon
open LeanQbe.T.Examples.Kissat.FullM6 LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM7Fidelity
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyUtil
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep9
open LeanQbe.T.Examples.Kissat.FullFidelityInlPolicy
open LeanQbe.T.Arm64 Kraken

/-- Concrete AAPCS64 Arm64 certificate witness type for
`fidStep9Module.optInlinePolicy fidInlPolicy`. -/
abbrev FidCertArm64 : Type 1 :=
  LinkedCert armTarget armLayout armLegalTarget armLabelClean
    (fidStep9Module.optInlinePolicy fidInlPolicy)

private def fidPkg : KissatUnsatPkg where
  mod := fidStep9Module
  inlPolicy := fidInlPolicy
  entryFn := "kissat_solve_bytes"
  entryFn_fn := m6oSolveBytesFn
  entryFn_sig := ⟨rfl, rfl, rfl⟩
  entry_mem := fidStep9_solveBytes_mem
  env := fidStep9Env
  moduleOk := fidStep9_moduleOk
  noExit := fun f _ args m Q X X' h => fidStep9Env_noExit f.name f.as f.rs args m Q X X' h
  solve_intro := fun hcfit hwfit hm hreq =>
    fidStep9Env_solve_bytes_of (m7FidSolveBytesSpec_intro hcfit hwfit hm hreq)

/-! ## 1. Raw `compileModuleOptInlinePolicy`-Parameterized AAPCS64 Arm64 Theorems -/

/-- Whole-module `Defined` + `FnSpec` over raw `compileModuleOptInlinePolicy` (exact bound `b`). -/
theorem fid_module_fnspec_arm64_of_compile
    (hleg : LegalSigAll armLegalTarget fidStep9Module.fns)
    (hints : List armIsa.Hints) (code : List Directive) (bounds : List (Sym × Nat))
    (hcm : compileModuleOptInlinePolicy armIsa armLegalTarget 0 [] [] 0
      fidStep9Module hints fidInlPolicy = .ok (code, bounds))
    [hh : Host] (k₀ : Nat) (hc : code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {f : Fn} (hf : f ∈ fidStep9Module.fns) {b : Nat} (hb : (f.name, b) ∈ bounds) :
    armTarget.Defined hh f.name ∧
      armTarget.FnSpec hh f.name (fidStep9Env f.name f.as f.rs) b 0 :=
  module_fnspec_of_compile arm64KissatAbi fidPkg hleg hints code bounds
    hcm hh k₀ hc hu hf hb

/-- Whole-module `Defined` + `FnSpec` over raw `compileModuleOptInlinePolicy` (fixed `2048B`). -/
theorem fid_module_fnspec_arm64_maxB_of_compile
    (hleg : LegalSigAll armLegalTarget fidStep9Module.fns)
    (hints : List armIsa.Hints) (code : List Directive) (bounds : List (Sym × Nat))
    (hcm : compileModuleOptInlinePolicy armIsa armLegalTarget 0 [] [] 0
      fidStep9Module hints fidInlPolicy = .ok (code, bounds))
    (hble : ∀ p ∈ bounds, p.2 ≤ 2048)
    [hh : Host] (k₀ : Nat) (hc : code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {f : Fn} (hf : f ∈ fidStep9Module.fns) :
    armTarget.Defined hh f.name ∧
      armTarget.FnSpec hh f.name (fidStep9Env f.name f.as f.rs) 2048 0 :=
  module_fnspec_of_compile_maxB arm64KissatAbi fidPkg hleg hints code bounds hble
    (by decide) hcm hh k₀ hc hu hf

/-- Raw `compileModuleOptInlinePolicy`-parameterized AAPCS64 Arm64 UNSAT soundness + framing
(`2048B` fixed stack contract). -/
theorem fid_solve_bytes_unsat_arm64_of_compile
    (hints : List armIsa.Hints) (code : List Directive) (bounds : List (Sym × Nat))
    (hcm : compileModuleOptInlinePolicy armIsa armLegalTarget 0 [] [] 0
      fidStep9Module hints fidInlPolicy = .ok (code, bounds))
    {b : Nat} (hb : ("kissat_solve_bytes", b) ∈ bounds) (hble : b ≤ 2048)
    [hh : Host] (k₀ : Nat) (hc : code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (cnf_ptr work_ptr fuel : BitVec 64) (cnfBytes : List UInt8) (wlen : Nat)
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hx0 : (s.regs.getXReg .X0).toBitVec = cnf_ptr)
    (hx1 : (s.regs.getXReg .X1).toBitVec = BitVec.ofNat 64 cnfBytes.length)
    (hx2 : (s.regs.getXReg .X2).toBitVec = work_ptr)
    (hx3 : (s.regs.getXReg .X3).toBitVec = BitVec.ofNat 64 wlen)
    (hx4 : (s.regs.getXReg .X4).toBitVec = fuel)
    (hra : s.regs.X30 = ra.toUInt64) (hsp : s.regs.SP.toNat % 16 = 0)
    (hmem : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
      region (s.regs.SP.toBitVec - 2048#64) 2048 ⋆ R) s.dmem) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        ((st.data.regs.getXReg .X0).toBitVec = 0#64 ∨
          (st.data.regs.getXReg .X0).toBitVec = 10#64 ∨
          (st.data.regs.getXReg .X0).toBitVec = 20#64) ∧
        ((st.data.regs.getXReg .X0).toBitVec = 20#64 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
          st.data.regs.getXReg r = s.regs.getXReg r) ∧
        st.data.regs.SP = s.regs.SP ∧
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
          region (s.regs.SP.toBitVec - 2048#64) 2048 ⋆ R) st.data.dmem)
      ⟨s, Labels.label "kissat_solve_bytes"⟩ := by
  refine eventually_weaken _ _ _ _
    (fun _ ⟨hpc, hdom, hu', ⟨hcal, hsp'⟩, hst⟩ => ⟨hpc, hdom, hu', hcal, hsp', hst⟩)
    (solve_bytes_unsat_of_compile_maxB arm64KissatAbi fidPkg rfl rfl
      hints code bounds hcm hb hble (by decide) hh k₀ hc hu
      cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit s ra R
      ⟨hx0, hx1, hx2, hx3, hx4⟩ ⟨hra, hsp⟩ hmem)

/-- Answer-only raw `compileModuleOptInlinePolicy`-parameterized AAPCS64 Arm64 UNSAT soundness. -/
theorem kissat_fid_arm64_unsat_correct_of_compile
    (hints : List armIsa.Hints) (code : List Directive) (bounds : List (Sym × Nat))
    (hcm : compileModuleOptInlinePolicy armIsa armLegalTarget 0 [] [] 0
      fidStep9Module hints fidInlPolicy = .ok (code, bounds))
    {b : Nat} (hb : ("kissat_solve_bytes", b) ∈ bounds) (hble : b ≤ 2048)
    [hh : Host] (k₀ : Nat) (hc : code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (cnf_ptr work_ptr fuel : BitVec 64) (cnfBytes : List UInt8) (wlen : Nat)
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hx0 : (s.regs.getXReg .X0).toBitVec = cnf_ptr)
    (hx1 : (s.regs.getXReg .X1).toBitVec = BitVec.ofNat 64 cnfBytes.length)
    (hx2 : (s.regs.getXReg .X2).toBitVec = work_ptr)
    (hx3 : (s.regs.getXReg .X3).toBitVec = BitVec.ofNat 64 wlen)
    (hx4 : (s.regs.getXReg .X4).toBitVec = fuel)
    (hra : s.regs.X30 = ra.toUInt64) (hsp : s.regs.SP.toNat % 16 = 0)
    (hmem : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
      region (s.regs.SP.toBitVec - 2048#64) 2048 ⋆ R) s.dmem) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        ((st.data.regs.getXReg .X0).toBitVec = 0#64 ∨
          (st.data.regs.getXReg .X0).toBitVec = 10#64 ∨
          (st.data.regs.getXReg .X0).toBitVec = 20#64) ∧
        ((st.data.regs.getXReg .X0).toBitVec = 20#64 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat))
      ⟨s, Labels.label "kissat_solve_bytes"⟩ :=
  eventually_weaken _ _ _ _ (fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fid_solve_bytes_unsat_arm64_of_compile hints code bounds hcm hb hble k₀ hc hu
      cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit s ra R
      hx0 hx1 hx2 hx3 hx4 hra hsp hmem)

/-- Raw `compileModuleOptInlinePolicy`-parameterized AAPCS64 Arm64 UNSAT non-vacuity (`2048B`). -/
theorem kissat_fid_arm64_unsat_nonvacuous_of_compile
    (hints : List armIsa.Hints) (code : List Directive) (bounds : List (Sym × Nat))
    (hcm : compileModuleOptInlinePolicy armIsa armLegalTarget 0 [] [] 0
      fidStep9Module hints fidInlPolicy = .ok (code, bounds))
    {b : Nat} (hb : ("kissat_solve_bytes", b) ∈ bounds) (hble : b ≤ 2048)
    [hh : Host] (k₀ : Nat) (hc : code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique) :
    ∃ (cnf_ptr work_ptr fuel : BitVec 64) (cnfBytes : List UInt8) (wlen : Nat)
      (s : MachineData) (ra : Int64) (R : Mem 64 → Prop),
      cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧
      work_ptr.toNat + wlen < 2 ^ 64 ∧
      (s.regs.getXReg .X0).toBitVec = cnf_ptr ∧
      (s.regs.getXReg .X1).toBitVec = BitVec.ofNat 64 cnfBytes.length ∧
      (s.regs.getXReg .X2).toBitVec = work_ptr ∧
      (s.regs.getXReg .X3).toBitVec = BitVec.ofNat 64 wlen ∧
      (s.regs.getXReg .X4).toBitVec = fuel ∧
      s.regs.X30 = ra.toUInt64 ∧
      s.regs.SP.toNat % 16 = 0 ∧
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
        region (s.regs.SP.toBitVec - 2048#64) 2048 ⋆ R) s.dmem ∧
      Eventually (step1 Host.exe)
        (fun st => st.pc = ra ∧ (st.data.regs.getXReg .X0).toBitVec = 20#64 ∧
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat)
        ⟨s, Labels.label "kissat_solve_bytes"⟩ := by
  obtain ⟨cp, wp, fu, cb, wl, s, ra, R, hcf, hwf,
    ⟨h0, h1, h2, h3, h4⟩, ⟨hra, hsp⟩, hdm, hev⟩ :=
    unsat_nonvacuous_of_compile_maxB arm64KissatAbi fidPkg rfl rfl
      hints code bounds hcm hb hble (by decide) arm64KissatAbi.maxStack_ge hh k₀ hc hu
  exact ⟨cp, wp, fu, cb, wl, s, ra, R, hcf, hwf, h0, h1, h2, h3, h4, hra, hsp, hdm, hev⟩

/-- Raw `compileModuleOptInlinePolicy`-parameterized closed `armInit` execution (`2048B`). -/
theorem kissat_fid_arm64_run_unsat_of_compile
    (hints : List armIsa.Hints) (code : List Directive) (bounds : List (Sym × Nat))
    (hcm : compileModuleOptInlinePolicy armIsa armLegalTarget 0 [] [] 0
      fidStep9Module hints fidInlPolicy = .ok (code, bounds))
    {b : Nat} (hb : ("kissat_solve_bytes", b) ∈ bounds) (hble : b ≤ 2048)
    (hh : Host) (k₀ : Nat) (hc : code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique) :
    Eventually (armTarget.mach.step hh)
      (fun st =>
        armTarget.mach.pc st = armInit.ra0 ∧
        armTarget.mach.getGpr (armTarget.mach.data st) armInit.ret0 = 20#64 ∧
        (armTarget.mach.mem (armTarget.mach.data st) =⋆
          (fun m' => nvM6UnsatCnf.Unsat ∧
            (bytes nvM6CnfPtr nvM6UnsatBytes ⋆
              region nvM6UnsatWorkPtr m6NvWorkLen ⋆ emp) m') ⋆
          armTarget.Exit armInit.sp0 2048 ⋆ emp))
      (armTarget.mach.mkState
        (armInit.initState (as := [i64, i64, i64, i64, i64]) 2048
          (m6NvPayload nvM6UnsatBytes)
          (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
            nvM6UnsatWorkPtr, BitVec.ofNat 64 m6NvWorkLen, 16#64, ()))
        (armTarget.mach.labelAddr hh "kissat_solve_bytes")) :=
  run_unsat_of_compile_maxB arm64KissatAbi fidPkg rfl rfl
    hints code bounds hcm hb hble (by decide) arm64KissatAbi.maxStack_ge hh k₀ hc hu

/-! ## 2. `FidCertArm64`-Parameterized Theorems (Exact `cert.bound` & Fixed `2048B`) -/

/-- Whole-module `Defined` + `FnSpec` over `cert : FidCertArm64` and `LegalSigAll`. -/
theorem fid_module_fnspec_of_cert (cert : FidCertArm64)
    (hleg : LegalSigAll armLegalTarget fidStep9Module.fns)
    [hh : Host] (k₀ : Nat) (hc : cert.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {f : Fn} (hf : f ∈ fidStep9Module.fns) :
    armTarget.Defined hh f.name ∧
      armTarget.FnSpec hh f.name (fidStep9Env f.name f.as f.rs) (cert.bound f.name) 0 :=
  module_fnspec_of_abi arm64KissatAbi fidPkg cert hleg hh k₀ hc hu hf

/-- `FidCertArm64`-parameterized AAPCS64 Arm64 UNSAT soundness + framing (exact `cert.bound`). -/
theorem fid_solve_bytes_unsat_arm64_of_cert (cert : FidCertArm64)
    [hh : Host] (k₀ : Nat) (hc : cert.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (cnf_ptr work_ptr fuel : BitVec 64) (cnfBytes : List UInt8) (wlen : Nat)
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hx0 : (s.regs.getXReg .X0).toBitVec = cnf_ptr)
    (hx1 : (s.regs.getXReg .X1).toBitVec = BitVec.ofNat 64 cnfBytes.length)
    (hx2 : (s.regs.getXReg .X2).toBitVec = work_ptr)
    (hx3 : (s.regs.getXReg .X3).toBitVec = BitVec.ofNat 64 wlen)
    (hx4 : (s.regs.getXReg .X4).toBitVec = fuel)
    (hra : s.regs.X30 = ra.toUInt64) (hsp : s.regs.SP.toNat % 16 = 0)
    (hmem : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
      region (s.regs.SP.toBitVec - BitVec.ofNat 64 (cert.bound "kissat_solve_bytes"))
        (cert.bound "kissat_solve_bytes") ⋆ R) s.dmem) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        ((st.data.regs.getXReg .X0).toBitVec = 0#64 ∨
          (st.data.regs.getXReg .X0).toBitVec = 10#64 ∨
          (st.data.regs.getXReg .X0).toBitVec = 20#64) ∧
        ((st.data.regs.getXReg .X0).toBitVec = 20#64 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
          st.data.regs.getXReg r = s.regs.getXReg r) ∧
        st.data.regs.SP = s.regs.SP ∧
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
          region (s.regs.SP.toBitVec - BitVec.ofNat 64 (cert.bound "kissat_solve_bytes"))
            (cert.bound "kissat_solve_bytes") ⋆ R) st.data.dmem)
      ⟨s, Labels.label "kissat_solve_bytes"⟩ := by
  refine eventually_weaken _ _ _ _
    (fun _ ⟨hpc, hdom, hu', ⟨hcal, hsp'⟩, hst⟩ => ⟨hpc, hdom, hu', hcal, hsp', hst⟩)
    (solve_bytes_unsat_entry_of_abi arm64KissatAbi fidPkg cert rfl rfl hh k₀ hc hu
      cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit s ra R
      ⟨hx0, hx1, hx2, hx3, hx4⟩ ⟨hra, hsp⟩ hmem)

/-- `FidCertArm64`-parameterized AAPCS64 Arm64 UNSAT soundness + framing (fixed `2048B` stack). -/
theorem fid_solve_bytes_unsat_arm64_maxB_of_cert (cert : FidCertArm64)
    [hh : Host] (k₀ : Nat) (hc : cert.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (cnf_ptr work_ptr fuel : BitVec 64) (cnfBytes : List UInt8) (wlen : Nat)
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hx0 : (s.regs.getXReg .X0).toBitVec = cnf_ptr)
    (hx1 : (s.regs.getXReg .X1).toBitVec = BitVec.ofNat 64 cnfBytes.length)
    (hx2 : (s.regs.getXReg .X2).toBitVec = work_ptr)
    (hx3 : (s.regs.getXReg .X3).toBitVec = BitVec.ofNat 64 wlen)
    (hx4 : (s.regs.getXReg .X4).toBitVec = fuel)
    (hra : s.regs.X30 = ra.toUInt64) (hsp : s.regs.SP.toNat % 16 = 0)
    (hmem : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
      region (s.regs.SP.toBitVec - 2048#64) 2048 ⋆ R) s.dmem) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        ((st.data.regs.getXReg .X0).toBitVec = 0#64 ∨
          (st.data.regs.getXReg .X0).toBitVec = 10#64 ∨
          (st.data.regs.getXReg .X0).toBitVec = 20#64) ∧
        ((st.data.regs.getXReg .X0).toBitVec = 20#64 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
          st.data.regs.getXReg r = s.regs.getXReg r) ∧
        st.data.regs.SP = s.regs.SP ∧
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
          region (s.regs.SP.toBitVec - 2048#64) 2048 ⋆ R) st.data.dmem)
      ⟨s, Labels.label "kissat_solve_bytes"⟩ := by
  refine eventually_weaken _ _ _ _
    (fun _ ⟨hpc, hdom, hu', ⟨hcal, hsp'⟩, hst⟩ => ⟨hpc, hdom, hu', hcal, hsp', hst⟩)
    (solve_bytes_unsat_maxB_of_abi arm64KissatAbi fidPkg cert rfl rfl (by decide)
      hh k₀ hc hu cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit s ra R
      ⟨hx0, hx1, hx2, hx3, hx4⟩ ⟨hra, hsp⟩ hmem)

/-- Answer-only `FidCertArm64`-parameterized AAPCS64 Arm64 UNSAT soundness
(exact `cert.bound`). -/
theorem kissat_fid_arm64_unsat_correct_of_cert (cert : FidCertArm64)
    [hh : Host] (k₀ : Nat) (hc : cert.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (cnf_ptr work_ptr fuel : BitVec 64) (cnfBytes : List UInt8) (wlen : Nat)
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hx0 : (s.regs.getXReg .X0).toBitVec = cnf_ptr)
    (hx1 : (s.regs.getXReg .X1).toBitVec = BitVec.ofNat 64 cnfBytes.length)
    (hx2 : (s.regs.getXReg .X2).toBitVec = work_ptr)
    (hx3 : (s.regs.getXReg .X3).toBitVec = BitVec.ofNat 64 wlen)
    (hx4 : (s.regs.getXReg .X4).toBitVec = fuel)
    (hra : s.regs.X30 = ra.toUInt64) (hsp : s.regs.SP.toNat % 16 = 0)
    (hmem : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
      region (s.regs.SP.toBitVec - BitVec.ofNat 64 (cert.bound "kissat_solve_bytes"))
        (cert.bound "kissat_solve_bytes") ⋆ R) s.dmem) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        ((st.data.regs.getXReg .X0).toBitVec = 0#64 ∨
          (st.data.regs.getXReg .X0).toBitVec = 10#64 ∨
          (st.data.regs.getXReg .X0).toBitVec = 20#64) ∧
        ((st.data.regs.getXReg .X0).toBitVec = 20#64 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat))
      ⟨s, Labels.label "kissat_solve_bytes"⟩ :=
  eventually_weaken _ _ _ _ (fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fid_solve_bytes_unsat_arm64_of_cert cert k₀ hc hu cnf_ptr work_ptr fuel cnfBytes wlen
      hcfit hwfit s ra R hx0 hx1 hx2 hx3 hx4 hra hsp hmem)

/-- Answer-only `FidCertArm64`-parameterized AAPCS64 Arm64 UNSAT soundness (fixed `2048B`). -/
theorem kissat_fid_arm64_unsat_correct_maxB_of_cert (cert : FidCertArm64)
    [hh : Host] (k₀ : Nat) (hc : cert.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (cnf_ptr work_ptr fuel : BitVec 64) (cnfBytes : List UInt8) (wlen : Nat)
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hx0 : (s.regs.getXReg .X0).toBitVec = cnf_ptr)
    (hx1 : (s.regs.getXReg .X1).toBitVec = BitVec.ofNat 64 cnfBytes.length)
    (hx2 : (s.regs.getXReg .X2).toBitVec = work_ptr)
    (hx3 : (s.regs.getXReg .X3).toBitVec = BitVec.ofNat 64 wlen)
    (hx4 : (s.regs.getXReg .X4).toBitVec = fuel)
    (hra : s.regs.X30 = ra.toUInt64) (hsp : s.regs.SP.toNat % 16 = 0)
    (hmem : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
      region (s.regs.SP.toBitVec - 2048#64) 2048 ⋆ R) s.dmem) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        ((st.data.regs.getXReg .X0).toBitVec = 0#64 ∨
          (st.data.regs.getXReg .X0).toBitVec = 10#64 ∨
          (st.data.regs.getXReg .X0).toBitVec = 20#64) ∧
        ((st.data.regs.getXReg .X0).toBitVec = 20#64 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat))
      ⟨s, Labels.label "kissat_solve_bytes"⟩ :=
  eventually_weaken _ _ _ _ (fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fid_solve_bytes_unsat_arm64_maxB_of_cert cert k₀ hc hu cnf_ptr work_ptr fuel cnfBytes wlen
      hcfit hwfit s ra R hx0 hx1 hx2 hx3 hx4 hra hsp hmem)

/-- `FidCertArm64`-parameterized AAPCS64 Arm64 UNSAT non-vacuity (exact `cert.bound`). -/
theorem kissat_fid_arm64_unsat_nonvacuous_of_cert (cert : FidCertArm64)
    [hh : Host] (k₀ : Nat) (hc : cert.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique) :
    ∃ (cnf_ptr work_ptr fuel : BitVec 64) (cnfBytes : List UInt8) (wlen : Nat)
      (s : MachineData) (ra : Int64) (R : Mem 64 → Prop),
      cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧
      work_ptr.toNat + wlen < 2 ^ 64 ∧
      (s.regs.getXReg .X0).toBitVec = cnf_ptr ∧
      (s.regs.getXReg .X1).toBitVec = BitVec.ofNat 64 cnfBytes.length ∧
      (s.regs.getXReg .X2).toBitVec = work_ptr ∧
      (s.regs.getXReg .X3).toBitVec = BitVec.ofNat 64 wlen ∧
      (s.regs.getXReg .X4).toBitVec = fuel ∧
      s.regs.X30 = ra.toUInt64 ∧
      s.regs.SP.toNat % 16 = 0 ∧
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
        region (s.regs.SP.toBitVec - BitVec.ofNat 64 (cert.bound "kissat_solve_bytes"))
          (cert.bound "kissat_solve_bytes") ⋆ R) s.dmem ∧
      Eventually (step1 Host.exe)
        (fun st => st.pc = ra ∧ (st.data.regs.getXReg .X0).toBitVec = 20#64 ∧
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat)
        ⟨s, Labels.label "kissat_solve_bytes"⟩ := by
  obtain ⟨cp, wp, fu, cb, wl, s, ra, R, hcf, hwf,
    ⟨h0, h1, h2, h3, h4⟩, ⟨hra, hsp⟩, hdm, hev⟩ :=
    unsat_nonvacuous_entry_of_abi arm64KissatAbi fidPkg cert rfl rfl hh k₀ hc hu
  exact ⟨cp, wp, fu, cb, wl, s, ra, R, hcf, hwf, h0, h1, h2, h3, h4, hra, hsp, hdm, hev⟩

/-- `FidCertArm64`-parameterized AAPCS64 Arm64 UNSAT non-vacuity (fixed `2048B` stack). -/
theorem kissat_fid_arm64_unsat_nonvacuous_maxB_of_cert (cert : FidCertArm64)
    [hh : Host] (k₀ : Nat) (hc : cert.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique) :
    ∃ (cnf_ptr work_ptr fuel : BitVec 64) (cnfBytes : List UInt8) (wlen : Nat)
      (s : MachineData) (ra : Int64) (R : Mem 64 → Prop),
      cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧
      work_ptr.toNat + wlen < 2 ^ 64 ∧
      (s.regs.getXReg .X0).toBitVec = cnf_ptr ∧
      (s.regs.getXReg .X1).toBitVec = BitVec.ofNat 64 cnfBytes.length ∧
      (s.regs.getXReg .X2).toBitVec = work_ptr ∧
      (s.regs.getXReg .X3).toBitVec = BitVec.ofNat 64 wlen ∧
      (s.regs.getXReg .X4).toBitVec = fuel ∧
      s.regs.X30 = ra.toUInt64 ∧
      s.regs.SP.toNat % 16 = 0 ∧
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
        region (s.regs.SP.toBitVec - 2048#64) 2048 ⋆ R) s.dmem ∧
      Eventually (step1 Host.exe)
        (fun st => st.pc = ra ∧ (st.data.regs.getXReg .X0).toBitVec = 20#64 ∧
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat)
        ⟨s, Labels.label "kissat_solve_bytes"⟩ := by
  obtain ⟨cp, wp, fu, cb, wl, s, ra, R, hcf, hwf,
    ⟨h0, h1, h2, h3, h4⟩, ⟨hra, hsp⟩, hdm, hev⟩ :=
    unsat_nonvacuous_maxB_of_abi arm64KissatAbi fidPkg cert rfl rfl
      (by decide) hh k₀ hc hu
  exact ⟨cp, wp, fu, cb, wl, s, ra, R, hcf, hwf, h0, h1, h2, h3, h4, hra, hsp, hdm, hev⟩

/-- Closed concrete-host AAPCS64 Arm64 UNSAT execution witness on `cert.host`
(exact `cert.bound`). -/
theorem kissat_fid_arm64_run_unsat_of_cert (cert : FidCertArm64) :
    Eventually (armTarget.mach.step cert.host)
      (fun st =>
        armTarget.mach.pc st = armInit.ra0 ∧
        armTarget.mach.getGpr (armTarget.mach.data st) armInit.ret0 = 20#64 ∧
        (armTarget.mach.mem (armTarget.mach.data st) =⋆
          (fun m' => nvM6UnsatCnf.Unsat ∧
            (bytes nvM6CnfPtr nvM6UnsatBytes ⋆
              region nvM6UnsatWorkPtr m6NvWorkLen ⋆ emp) m') ⋆
          armTarget.Exit armInit.sp0 (cert.bound "kissat_solve_bytes") ⋆ emp))
      (armTarget.mach.mkState
        (armInit.initState (as := [i64, i64, i64, i64, i64])
          (cert.bound "kissat_solve_bytes")
          (m6NvPayload nvM6UnsatBytes)
          (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
            nvM6UnsatWorkPtr, BitVec.ofNat 64 m6NvWorkLen, 16#64, ()))
        (armTarget.mach.labelAddr cert.host "kissat_solve_bytes")) :=
  run_unsat_entry_of_abi arm64KissatAbi fidPkg cert rfl rfl

/-- Closed concrete-host AAPCS64 Arm64 UNSAT execution witness on `cert.host` (fixed `2048B`). -/
theorem kissat_fid_arm64_run_unsat_maxB_of_cert (cert : FidCertArm64) :
    Eventually (armTarget.mach.step cert.host)
      (fun st =>
        armTarget.mach.pc st = armInit.ra0 ∧
        armTarget.mach.getGpr (armTarget.mach.data st) armInit.ret0 = 20#64 ∧
        (armTarget.mach.mem (armTarget.mach.data st) =⋆
          (fun m' => nvM6UnsatCnf.Unsat ∧
            (bytes nvM6CnfPtr nvM6UnsatBytes ⋆
              region nvM6UnsatWorkPtr m6NvWorkLen ⋆ emp) m') ⋆
          armTarget.Exit armInit.sp0 2048 ⋆ emp))
      (armTarget.mach.mkState
        (armInit.initState (as := [i64, i64, i64, i64, i64]) 2048
          (m6NvPayload nvM6UnsatBytes)
          (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
            nvM6UnsatWorkPtr, BitVec.ofNat 64 m6NvWorkLen, 16#64, ()))
        (armTarget.mach.labelAddr cert.host "kissat_solve_bytes")) :=
  run_unsat_maxB_of_abi arm64KissatAbi fidPkg cert rfl rfl (by decide)

end LeanQbe.T.Arm64.KissatFidelityParam
