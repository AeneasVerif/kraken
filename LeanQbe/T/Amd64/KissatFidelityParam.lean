/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Amd64.KissatAbi
public import LeanQbe.T.Examples.Kissat.KissatCertParamCommon
public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyProof
public import LeanQbe.T.Examples.Kissat.FullFidelityInlPolicy
import Kraken.Mem
import Kraken.Separation

/-!
# KissatFidelity (`499` fns) Tier-1 Parameterized SysV x64 Theorems

Proves full-module `FnSpec`, concrete Kraken x64 `Eventually` UNSAT soundness, non-vacuity,
and closed-host `run_unsat` parameterized over both raw
`compileModuleOptInlinePolicy ... = .ok (code, bounds)` and `cert : FidCertX64`
(exposing both exact `cert.bound` and fixed `2048`-byte stack contracts).
Imports zero `*Cert*`, zero materialized `*Inl*`, and zero `MainCertElab` modules (`std3`).

NOTE: Parameterizes `FullFidelityAssembly.fidModule` (`499` fns, matching `FullFidelityInl`),
because `FullFidelityStep7.lean:1495` declares `full_bva_upd_lit_fid` with `7` args
(`[i64, i64, i64, i64, i32, i64, i32]`), exceeding `x64Isa.assignArgs`'s `6`-GPR SysV ABI limit
(`LeanQbeTest.T.KissatFidelityCompileGuardX64` flags `full_bva_upd_lit_fid: fn: abi`).
Once `full_bva_upd_lit_fid` takes `≤ 6` args (or `x64Isa` supports stack args), switch
`FullFidelityAssemblyProof` -> `FullFidelityAssemblyStep7Proof` and `fidModule`/`fidEnv` ->
`fidStep7Module`/`fidStep7Env`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Amd64.KissatFidelityParam

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.KissatCertCommon
open LeanQbe.T.Examples.Kissat.KissatCertParamCommon
open LeanQbe.T.Examples.Kissat.FullM6 LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM7Fidelity
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyUtil
open LeanQbe.T.Examples.Kissat.FullFidelityAssembly
open LeanQbe.T.Examples.Kissat.FullFidelityInlPolicy
open LeanQbe.T.Amd64 Kraken

/-- Concrete SysV x64 certificate witness type for `fidModule.optInlinePolicy fidInlPolicy`. -/
abbrev FidCertX64 : Type 1 :=
  LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean
    (fidModule.optInlinePolicy fidInlPolicy)

private def fidPkg : KissatUnsatPkg where
  mod := fidModule
  inlPolicy := fidInlPolicy
  entryFn := "kissat_solve_bytes"
  entryFn_fn := m6oSolveBytesFn
  entryFn_sig := ⟨rfl, rfl, rfl⟩
  entry_mem := fid_solveBytes_mem
  env := fidEnv
  moduleOk := fid_moduleOk
  noExit := fun f _ args m Q X X' h => fidEnv_noExit f.name f.as f.rs args m Q X X' h
  solve_intro := fun hcfit hwfit hm hreq =>
    fidEnv_solve_bytes_of (m7FidSolveBytesSpec_intro hcfit hwfit hm hreq)

/-! ## 1. Raw `compileModuleOptInlinePolicy`-Parameterized SysV x64 Theorems -/

/-- Whole-module `Defined` + `FnSpec` over raw `compileModuleOptInlinePolicy` (exact bound `b`). -/
theorem fid_module_fnspec_x64_of_compile
    (hleg : LegalSigAll x64LegalTarget fidModule.fns)
    (hints : List x64Isa.Hints) (code : List Directive) (bounds : List (Sym × Nat))
    (hcm : compileModuleOptInlinePolicy x64Isa x64LegalTarget 8 [] [] 0
      fidModule hints fidInlPolicy = .ok (code, bounds))
    [hh : Host] (k₀ : Nat) (hc : code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {f : Fn} (hf : f ∈ fidModule.fns) {b : Nat} (hb : (f.name, b) ∈ bounds) :
    x64Target.Defined hh f.name ∧
      x64Target.FnSpec hh f.name (fidEnv f.name f.as f.rs) b 0 :=
  module_fnspec_of_compile x64KissatAbi fidPkg hleg hints code bounds hcm hh k₀ hc hu hf hb

/-- Whole-module `Defined` + `FnSpec` over raw `compileModuleOptInlinePolicy` (fixed `2048B`). -/
theorem fid_module_fnspec_x64_maxB_of_compile
    (hleg : LegalSigAll x64LegalTarget fidModule.fns)
    (hints : List x64Isa.Hints) (code : List Directive) (bounds : List (Sym × Nat))
    (hcm : compileModuleOptInlinePolicy x64Isa x64LegalTarget 8 [] [] 0
      fidModule hints fidInlPolicy = .ok (code, bounds))
    (hble : ∀ p ∈ bounds, p.2 ≤ 2048)
    [hh : Host] (k₀ : Nat) (hc : code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {f : Fn} (hf : f ∈ fidModule.fns) :
    x64Target.Defined hh f.name ∧
      x64Target.FnSpec hh f.name (fidEnv f.name f.as f.rs) 2048 0 :=
  module_fnspec_of_compile_maxB x64KissatAbi fidPkg hleg hints code bounds hble
    (by decide) hcm hh k₀ hc hu hf

/-- Raw `compileModuleOptInlinePolicy`-parameterized SysV x64 UNSAT soundness + framing
(`2048B` fixed stack contract). -/
theorem fid_solve_bytes_unsat_x64_of_compile
    (hints : List x64Isa.Hints) (code : List Directive) (bounds : List (Sym × Nat))
    (hcm : compileModuleOptInlinePolicy x64Isa x64LegalTarget 8 [] [] 0
      fidModule hints fidInlPolicy = .ok (code, bounds))
    {b : Nat} (hb : ("kissat_solve_bytes", b) ∈ bounds) (hble : b ≤ 2048)
    [hh : Host] (k₀ : Nat) (hc : code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (cnf_ptr work_ptr fuel : BitVec 64) (cnfBytes : List UInt8) (wlen : Nat)
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hrdi : s.regs.get64 .rdi = cnf_ptr)
    (hrsi : s.regs.get64 .rsi = BitVec.ofNat 64 cnfBytes.length)
    (hrdx : s.regs.get64 .rdx = work_ptr)
    (hrcx : s.regs.get64 .rcx = BitVec.ofNat 64 wlen)
    (hr8 : s.regs.get64 .r8 = fuel)
    (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hmem : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
      (region (s.regs.get64 .rsp - 2048#64) 2048 ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) s.dmem) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        (st.data.regs.get64 .rax = 0#64 ∨ st.data.regs.get64 .rax = 10#64 ∨
          st.data.regs.get64 .rax = 20#64) ∧
        (st.data.regs.get64 .rax = 20#64 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15],
          st.data.regs.get64 r = s.regs.get64 r) ∧
        st.data.regs.get64 .rsp = s.regs.get64 .rsp + 8#64 ∧
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
          region (s.regs.get64 .rsp - 2048#64) 2056 ⋆ R) st.data.dmem)
      ⟨s, Labels.label "kissat_solve_bytes"⟩ := by
  refine eventually_weaken _ _ _ _
    (fun _ ⟨hpc, hdom, hu', ⟨hcal, hrsp⟩, hst⟩ => ⟨hpc, hdom, hu', hcal, hrsp, hst⟩)
    (solve_bytes_unsat_of_compile_maxB x64KissatAbi fidPkg rfl rfl
      hints code bounds hcm hb hble (by decide) hh k₀ hc hu
      cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit s ra R
      ⟨hrdi, hrsi, hrdx, hrcx, hr8⟩ hsp hmem)

/-- Answer-only raw `compileModuleOptInlinePolicy`-parameterized SysV x64 UNSAT soundness. -/
theorem kissat_fid_x64_unsat_correct_of_compile
    (hints : List x64Isa.Hints) (code : List Directive) (bounds : List (Sym × Nat))
    (hcm : compileModuleOptInlinePolicy x64Isa x64LegalTarget 8 [] [] 0
      fidModule hints fidInlPolicy = .ok (code, bounds))
    {b : Nat} (hb : ("kissat_solve_bytes", b) ∈ bounds) (hble : b ≤ 2048)
    [hh : Host] (k₀ : Nat) (hc : code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (cnf_ptr work_ptr fuel : BitVec 64) (cnfBytes : List UInt8) (wlen : Nat)
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hrdi : s.regs.get64 .rdi = cnf_ptr)
    (hrsi : s.regs.get64 .rsi = BitVec.ofNat 64 cnfBytes.length)
    (hrdx : s.regs.get64 .rdx = work_ptr)
    (hrcx : s.regs.get64 .rcx = BitVec.ofNat 64 wlen)
    (hr8 : s.regs.get64 .r8 = fuel)
    (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hmem : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
      (region (s.regs.get64 .rsp - 2048#64) 2048 ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) s.dmem) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        (st.data.regs.get64 .rax = 0#64 ∨ st.data.regs.get64 .rax = 10#64 ∨
          st.data.regs.get64 .rax = 20#64) ∧
        (st.data.regs.get64 .rax = 20#64 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat))
      ⟨s, Labels.label "kissat_solve_bytes"⟩ :=
  eventually_weaken _ _ _ _ (fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fid_solve_bytes_unsat_x64_of_compile hints code bounds hcm hb hble k₀ hc hu
      cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit s ra R
      hrdi hrsi hrdx hrcx hr8 hsp hmem)

/-- Raw `compileModuleOptInlinePolicy`-parameterized SysV x64 UNSAT non-vacuity (`2048B`). -/
theorem kissat_fid_x64_unsat_nonvacuous_of_compile
    (hints : List x64Isa.Hints) (code : List Directive) (bounds : List (Sym × Nat))
    (hcm : compileModuleOptInlinePolicy x64Isa x64LegalTarget 8 [] [] 0
      fidModule hints fidInlPolicy = .ok (code, bounds))
    {b : Nat} (hb : ("kissat_solve_bytes", b) ∈ bounds) (hble : b ≤ 2048)
    [hh : Host] (k₀ : Nat) (hc : code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique) :
    ∃ (cnf_ptr work_ptr fuel : BitVec 64) (cnfBytes : List UInt8) (wlen : Nat)
      (s : MachineData) (ra : Int64) (R : Mem 64 → Prop),
      cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧
      work_ptr.toNat + wlen < 2 ^ 64 ∧
      s.regs.get64 .rdi = cnf_ptr ∧
      s.regs.get64 .rsi = BitVec.ofNat 64 cnfBytes.length ∧
      s.regs.get64 .rdx = work_ptr ∧
      s.regs.get64 .rcx = BitVec.ofNat 64 wlen ∧
      s.regs.get64 .r8 = fuel ∧
      (s.regs.get64 .rsp + 8#64).toNat % 16 = 0 ∧
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
        (region (s.regs.get64 .rsp - 2048#64) 2048 ⋆
          cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) s.dmem ∧
      Eventually (step1 Host.exe)
        (fun st => st.pc = ra ∧ st.data.regs.get64 .rax = 20#64 ∧
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat)
        ⟨s, Labels.label "kissat_solve_bytes"⟩ := by
  obtain ⟨cp, wp, fu, cb, wl, s, ra, R, hcf, hwf,
    ⟨h0, h1, h2, h3, h4⟩, hsp, hdm, hev⟩ :=
    unsat_nonvacuous_of_compile_maxB x64KissatAbi fidPkg rfl rfl
      hints code bounds hcm hb hble (by decide) x64KissatAbi.maxStack_ge hh k₀ hc hu
  exact ⟨cp, wp, fu, cb, wl, s, ra, R, hcf, hwf, h0, h1, h2, h3, h4, hsp, hdm, hev⟩

/-- Raw `compileModuleOptInlinePolicy`-parameterized closed `x64Init` execution (`2048B`). -/
theorem kissat_fid_x64_run_unsat_of_compile
    (hints : List x64Isa.Hints) (code : List Directive) (bounds : List (Sym × Nat))
    (hcm : compileModuleOptInlinePolicy x64Isa x64LegalTarget 8 [] [] 0
      fidModule hints fidInlPolicy = .ok (code, bounds))
    {b : Nat} (hb : ("kissat_solve_bytes", b) ∈ bounds) (hble : b ≤ 2048)
    (hh : Host) (k₀ : Nat) (hc : code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique) :
    Eventually (x64Target.mach.step hh)
      (fun st =>
        x64Target.mach.pc st = x64Init.ra0 ∧
        x64Target.mach.getGpr (x64Target.mach.data st) x64Init.ret0 = 20#64 ∧
        (x64Target.mach.mem (x64Target.mach.data st) =⋆
          (fun m' => nvM6UnsatCnf.Unsat ∧
            (bytes nvM6CnfPtr nvM6UnsatBytes ⋆
              region nvM6UnsatWorkPtr m6NvWorkLen ⋆ emp) m') ⋆
          x64Target.Exit x64Init.sp0 2048 ⋆ emp))
      (x64Target.mach.mkState
        (x64Init.initState (as := [i64, i64, i64, i64, i64]) 2048
          (m6NvPayload nvM6UnsatBytes)
          (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
            nvM6UnsatWorkPtr, BitVec.ofNat 64 m6NvWorkLen, 16#64, ()))
        (x64Target.mach.labelAddr hh "kissat_solve_bytes")) :=
  run_unsat_of_compile_maxB x64KissatAbi fidPkg rfl rfl
    hints code bounds hcm hb hble (by decide) x64KissatAbi.maxStack_ge hh k₀ hc hu

/-! ## 2. `FidCertX64`-Parameterized Theorems (Exact `cert.bound` & Fixed `2048B`) -/

/-- Whole-module `Defined` + `FnSpec` over `cert : FidCertX64` and `LegalSigAll`. -/
theorem fid_module_fnspec_of_cert (cert : FidCertX64)
    (hleg : LegalSigAll x64LegalTarget fidModule.fns)
    [hh : Host] (k₀ : Nat) (hc : cert.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {f : Fn} (hf : f ∈ fidModule.fns) :
    x64Target.Defined hh f.name ∧
      x64Target.FnSpec hh f.name (fidEnv f.name f.as f.rs) (cert.bound f.name) 0 :=
  module_fnspec_of_abi x64KissatAbi fidPkg cert hleg hh k₀ hc hu hf

/-- `FidCertX64`-parameterized SysV x64 UNSAT soundness + framing (exact `cert.bound`). -/
theorem fid_solve_bytes_unsat_x64_of_cert (cert : FidCertX64)
    [hh : Host] (k₀ : Nat) (hc : cert.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (cnf_ptr work_ptr fuel : BitVec 64) (cnfBytes : List UInt8) (wlen : Nat)
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hrdi : s.regs.get64 .rdi = cnf_ptr)
    (hrsi : s.regs.get64 .rsi = BitVec.ofNat 64 cnfBytes.length)
    (hrdx : s.regs.get64 .rdx = work_ptr)
    (hrcx : s.regs.get64 .rcx = BitVec.ofNat 64 wlen)
    (hr8 : s.regs.get64 .r8 = fuel)
    (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hmem : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
      (region (s.regs.get64 .rsp - BitVec.ofNat 64 (cert.bound "kissat_solve_bytes"))
          (cert.bound "kissat_solve_bytes") ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) s.dmem) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        (st.data.regs.get64 .rax = 0#64 ∨ st.data.regs.get64 .rax = 10#64 ∨
          st.data.regs.get64 .rax = 20#64) ∧
        (st.data.regs.get64 .rax = 20#64 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15],
          st.data.regs.get64 r = s.regs.get64 r) ∧
        st.data.regs.get64 .rsp = s.regs.get64 .rsp + 8#64 ∧
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
          region (s.regs.get64 .rsp - BitVec.ofNat 64 (cert.bound "kissat_solve_bytes"))
            ((cert.bound "kissat_solve_bytes") + 8) ⋆ R) st.data.dmem)
      ⟨s, Labels.label "kissat_solve_bytes"⟩ := by
  refine eventually_weaken _ _ _ _
    (fun _ ⟨hpc, hdom, hu', ⟨hcal, hrsp⟩, hst⟩ => ⟨hpc, hdom, hu', hcal, hrsp, hst⟩)
    (solve_bytes_unsat_entry_of_abi x64KissatAbi fidPkg cert rfl rfl hh k₀ hc hu
      cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit s ra R
      ⟨hrdi, hrsi, hrdx, hrcx, hr8⟩ hsp hmem)

/-- `FidCertX64`-parameterized SysV x64 UNSAT soundness + framing (fixed `2048B` stack). -/
theorem fid_solve_bytes_unsat_x64_maxB_of_cert (cert : FidCertX64)
    [hh : Host] (k₀ : Nat) (hc : cert.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (cnf_ptr work_ptr fuel : BitVec 64) (cnfBytes : List UInt8) (wlen : Nat)
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hrdi : s.regs.get64 .rdi = cnf_ptr)
    (hrsi : s.regs.get64 .rsi = BitVec.ofNat 64 cnfBytes.length)
    (hrdx : s.regs.get64 .rdx = work_ptr)
    (hrcx : s.regs.get64 .rcx = BitVec.ofNat 64 wlen)
    (hr8 : s.regs.get64 .r8 = fuel)
    (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hmem : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
      (region (s.regs.get64 .rsp - 2048#64) 2048 ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) s.dmem) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        (st.data.regs.get64 .rax = 0#64 ∨ st.data.regs.get64 .rax = 10#64 ∨
          st.data.regs.get64 .rax = 20#64) ∧
        (st.data.regs.get64 .rax = 20#64 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15],
          st.data.regs.get64 r = s.regs.get64 r) ∧
        st.data.regs.get64 .rsp = s.regs.get64 .rsp + 8#64 ∧
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
          region (s.regs.get64 .rsp - 2048#64) 2056 ⋆ R) st.data.dmem)
      ⟨s, Labels.label "kissat_solve_bytes"⟩ := by
  refine eventually_weaken _ _ _ _
    (fun _ ⟨hpc, hdom, hu', ⟨hcal, hrsp⟩, hst⟩ => ⟨hpc, hdom, hu', hcal, hrsp, hst⟩)
    (solve_bytes_unsat_maxB_of_abi x64KissatAbi fidPkg cert rfl rfl (by decide) hh k₀ hc hu
      cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit s ra R
      ⟨hrdi, hrsi, hrdx, hrcx, hr8⟩ hsp hmem)

/-- Answer-only `FidCertX64`-parameterized SysV x64 UNSAT soundness (exact `cert.bound`). -/
theorem kissat_fid_x64_unsat_correct_of_cert (cert : FidCertX64)
    [hh : Host] (k₀ : Nat) (hc : cert.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (cnf_ptr work_ptr fuel : BitVec 64) (cnfBytes : List UInt8) (wlen : Nat)
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hrdi : s.regs.get64 .rdi = cnf_ptr)
    (hrsi : s.regs.get64 .rsi = BitVec.ofNat 64 cnfBytes.length)
    (hrdx : s.regs.get64 .rdx = work_ptr)
    (hrcx : s.regs.get64 .rcx = BitVec.ofNat 64 wlen)
    (hr8 : s.regs.get64 .r8 = fuel)
    (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hmem : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
      (region (s.regs.get64 .rsp - BitVec.ofNat 64 (cert.bound "kissat_solve_bytes"))
          (cert.bound "kissat_solve_bytes") ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) s.dmem) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        (st.data.regs.get64 .rax = 0#64 ∨ st.data.regs.get64 .rax = 10#64 ∨
          st.data.regs.get64 .rax = 20#64) ∧
        (st.data.regs.get64 .rax = 20#64 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat))
      ⟨s, Labels.label "kissat_solve_bytes"⟩ :=
  eventually_weaken _ _ _ _ (fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fid_solve_bytes_unsat_x64_of_cert cert k₀ hc hu cnf_ptr work_ptr fuel cnfBytes wlen
      hcfit hwfit s ra R hrdi hrsi hrdx hrcx hr8 hsp hmem)

/-- Answer-only `FidCertX64`-parameterized SysV x64 UNSAT soundness (fixed `2048B` stack). -/
theorem kissat_fid_x64_unsat_correct_maxB_of_cert (cert : FidCertX64)
    [hh : Host] (k₀ : Nat) (hc : cert.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (cnf_ptr work_ptr fuel : BitVec 64) (cnfBytes : List UInt8) (wlen : Nat)
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hrdi : s.regs.get64 .rdi = cnf_ptr)
    (hrsi : s.regs.get64 .rsi = BitVec.ofNat 64 cnfBytes.length)
    (hrdx : s.regs.get64 .rdx = work_ptr)
    (hrcx : s.regs.get64 .rcx = BitVec.ofNat 64 wlen)
    (hr8 : s.regs.get64 .r8 = fuel)
    (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hmem : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
      (region (s.regs.get64 .rsp - 2048#64) 2048 ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) s.dmem) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        (st.data.regs.get64 .rax = 0#64 ∨ st.data.regs.get64 .rax = 10#64 ∨
          st.data.regs.get64 .rax = 20#64) ∧
        (st.data.regs.get64 .rax = 20#64 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat))
      ⟨s, Labels.label "kissat_solve_bytes"⟩ :=
  eventually_weaken _ _ _ _ (fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fid_solve_bytes_unsat_x64_maxB_of_cert cert k₀ hc hu cnf_ptr work_ptr fuel cnfBytes wlen
      hcfit hwfit s ra R hrdi hrsi hrdx hrcx hr8 hsp hmem)

/-- `FidCertX64`-parameterized SysV x64 UNSAT non-vacuity (exact `cert.bound`). -/
theorem kissat_fid_x64_unsat_nonvacuous_of_cert (cert : FidCertX64)
    [hh : Host] (k₀ : Nat) (hc : cert.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique) :
    ∃ (cnf_ptr work_ptr fuel : BitVec 64) (cnfBytes : List UInt8) (wlen : Nat)
      (s : MachineData) (ra : Int64) (R : Mem 64 → Prop),
      cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧
      work_ptr.toNat + wlen < 2 ^ 64 ∧
      s.regs.get64 .rdi = cnf_ptr ∧
      s.regs.get64 .rsi = BitVec.ofNat 64 cnfBytes.length ∧
      s.regs.get64 .rdx = work_ptr ∧
      s.regs.get64 .rcx = BitVec.ofNat 64 wlen ∧
      s.regs.get64 .r8 = fuel ∧
      (s.regs.get64 .rsp + 8#64).toNat % 16 = 0 ∧
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
        (region (s.regs.get64 .rsp - BitVec.ofNat 64 (cert.bound "kissat_solve_bytes"))
            (cert.bound "kissat_solve_bytes") ⋆
          cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) s.dmem ∧
      Eventually (step1 Host.exe)
        (fun st => st.pc = ra ∧ st.data.regs.get64 .rax = 20#64 ∧
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat)
        ⟨s, Labels.label "kissat_solve_bytes"⟩ := by
  obtain ⟨cp, wp, fu, cb, wl, s, ra, R, hcf, hwf,
    ⟨h0, h1, h2, h3, h4⟩, hsp, hdm, hev⟩ :=
    unsat_nonvacuous_entry_of_abi x64KissatAbi fidPkg cert rfl rfl hh k₀ hc hu
  exact ⟨cp, wp, fu, cb, wl, s, ra, R, hcf, hwf, h0, h1, h2, h3, h4, hsp, hdm, hev⟩

/-- `FidCertX64`-parameterized SysV x64 UNSAT non-vacuity (fixed `2048B` stack). -/
theorem kissat_fid_x64_unsat_nonvacuous_maxB_of_cert (cert : FidCertX64)
    [hh : Host] (k₀ : Nat) (hc : cert.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique) :
    ∃ (cnf_ptr work_ptr fuel : BitVec 64) (cnfBytes : List UInt8) (wlen : Nat)
      (s : MachineData) (ra : Int64) (R : Mem 64 → Prop),
      cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧
      work_ptr.toNat + wlen < 2 ^ 64 ∧
      s.regs.get64 .rdi = cnf_ptr ∧
      s.regs.get64 .rsi = BitVec.ofNat 64 cnfBytes.length ∧
      s.regs.get64 .rdx = work_ptr ∧
      s.regs.get64 .rcx = BitVec.ofNat 64 wlen ∧
      s.regs.get64 .r8 = fuel ∧
      (s.regs.get64 .rsp + 8#64).toNat % 16 = 0 ∧
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
        (region (s.regs.get64 .rsp - 2048#64) 2048 ⋆
          cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) s.dmem ∧
      Eventually (step1 Host.exe)
        (fun st => st.pc = ra ∧ st.data.regs.get64 .rax = 20#64 ∧
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat)
        ⟨s, Labels.label "kissat_solve_bytes"⟩ := by
  obtain ⟨cp, wp, fu, cb, wl, s, ra, R, hcf, hwf,
    ⟨h0, h1, h2, h3, h4⟩, hsp, hdm, hev⟩ :=
    unsat_nonvacuous_maxB_of_abi x64KissatAbi fidPkg cert rfl rfl (by decide) hh k₀ hc hu
  exact ⟨cp, wp, fu, cb, wl, s, ra, R, hcf, hwf, h0, h1, h2, h3, h4, hsp, hdm, hev⟩

/-- Closed concrete-host SysV x64 UNSAT execution witness on `cert.host` (exact `cert.bound`). -/
theorem kissat_fid_x64_run_unsat_of_cert (cert : FidCertX64) :
    Eventually (x64Target.mach.step cert.host)
      (fun st =>
        x64Target.mach.pc st = x64Init.ra0 ∧
        x64Target.mach.getGpr (x64Target.mach.data st) x64Init.ret0 = 20#64 ∧
        (x64Target.mach.mem (x64Target.mach.data st) =⋆
          (fun m' => nvM6UnsatCnf.Unsat ∧
            (bytes nvM6CnfPtr nvM6UnsatBytes ⋆
              region nvM6UnsatWorkPtr m6NvWorkLen ⋆ emp) m') ⋆
          x64Target.Exit x64Init.sp0 (cert.bound "kissat_solve_bytes") ⋆ emp))
      (x64Target.mach.mkState
        (x64Init.initState (as := [i64, i64, i64, i64, i64])
          (cert.bound "kissat_solve_bytes")
          (m6NvPayload nvM6UnsatBytes)
          (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
            nvM6UnsatWorkPtr, BitVec.ofNat 64 m6NvWorkLen, 16#64, ()))
        (x64Target.mach.labelAddr cert.host "kissat_solve_bytes")) :=
  run_unsat_entry_of_abi x64KissatAbi fidPkg cert rfl rfl

/-- Closed concrete-host SysV x64 UNSAT execution witness on `cert.host` (fixed `2048B`). -/
theorem kissat_fid_x64_run_unsat_maxB_of_cert (cert : FidCertX64) :
    Eventually (x64Target.mach.step cert.host)
      (fun st =>
        x64Target.mach.pc st = x64Init.ra0 ∧
        x64Target.mach.getGpr (x64Target.mach.data st) x64Init.ret0 = 20#64 ∧
        (x64Target.mach.mem (x64Target.mach.data st) =⋆
          (fun m' => nvM6UnsatCnf.Unsat ∧
            (bytes nvM6CnfPtr nvM6UnsatBytes ⋆
              region nvM6UnsatWorkPtr m6NvWorkLen ⋆ emp) m') ⋆
          x64Target.Exit x64Init.sp0 2048 ⋆ emp))
      (x64Target.mach.mkState
        (x64Init.initState (as := [i64, i64, i64, i64, i64]) 2048
          (m6NvPayload nvM6UnsatBytes)
          (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
            nvM6UnsatWorkPtr, BitVec.ofNat 64 m6NvWorkLen, 16#64, ()))
        (x64Target.mach.labelAddr cert.host "kissat_solve_bytes")) :=
  run_unsat_maxB_of_abi x64KissatAbi fidPkg cert rfl rfl (by decide)

end LeanQbe.T.Amd64.KissatFidelityParam
