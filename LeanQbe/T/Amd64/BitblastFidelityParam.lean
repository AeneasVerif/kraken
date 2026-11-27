/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Amd64.KissatAbi
public import LeanQbe.T.Examples.Kissat.FullFidelityBitblastLemmas
import Kraken.Mem
import Kraken.Separation

/-!
# Bitblast + KissatFidelity (`581` fns) Tier-1 Parameterized SysV x64 Theorems

Proves end-to-end SysV x86-64 machine-code UNSAT soundness (`rax = 20#64 -> ∀ prog, parse = some
prog → prog.Unsat`) and concrete closed-host non-vacuity for `bv_solve_bytes`, parameterized over:
1. Raw `compileModuleOptInlinePolicy` on `bitblastFidStep12LinkedMod` (any `InlinePolicy`).
2. Raw `compileModule` on `bitblastFidStep12InlLinkedMod.fns` (`(fidStep12Module.optInlinePolicy
   fidInlPolicy).fns ++ bitblastModule.fns` — exact assembly emitted by `bv_decide_qbe`).
3. Concrete `BitblastFidCertX64` (`LinkedCert` over `bitblastFidStep12InlLinkedMod`, ready for
   1-line swap `fidStep12UnsatPkg -> fidStep13UnsatPkg` +
   `fidStep13Cert.append bitblastTailX64Cert`).

Imports zero `*Cert*`, zero materialized `*Inl*`, and zero `MainCertElab` modules (`<= std3`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Amd64.BitblastFidelityParam

open Std Std.ExtHashMap Std.Tactic.BVDecide
open LeanQbe.T LeanQbe.T.Amd64 Kraken
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.KissatCertCommon
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep12
open LeanQbe.T.Examples.Kissat.FullFidelityBitblastLemmas
open LeanQbe.T.Examples.Bitblast.Ref
open LeanQbe.T.Examples.Bitblast.Ref.BVProg
open LeanQbe.T.Examples.Bitblast.Proof

/-- Concrete SysV x64 certificate witness type for `bitblastFidStep12InlLinkedMod` (`581` fns). -/
abbrev BitblastFidCertX64 : Type 1 :=
  LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean
    bitblastFidStep12InlLinkedMod [] [] 0 2048

/-! ## 1. Raw `compileModuleOptInlinePolicy` & `compileModule` SysV x64 Theorems -/

/-- Raw `compileModuleOptInlinePolicy`-parameterized SysV x64 UNSAT soundness for
`bv_solve_bytes` over `bitblastFidStep12LinkedMod` (`581` fns). -/
theorem bitblast_fid_x64_unsat_of_compile_optInline
    (policy : InlinePolicy)
    (hints : List x64Isa.Hints) (code : List Directive) (bounds : List (Sym × Nat))
    (hcm : compileModuleOptInlinePolicy x64Isa x64LegalTarget 8 [] [] 0
      bitblastFidStep12LinkedMod hints policy = .ok (code, bounds))
    {b : Nat} (hb : ("bv_solve_bytes", b) ∈ bounds)
    [hh : Host] (k₀ : Nat) (hc : code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (progPtr progLen workPtr workCap fuel : BitVec 64)
    (progBytes : List UInt8) (m : Mem 64) (Rm R : Mem 64 → Prop)
    (s : MachineData) (ra : Int64)
    (hplen : progLen.toNat = progBytes.length)
    (hm : (bytes progPtr progBytes ⋆ region workPtr workCap.toNat ⋆ Rm) m)
    (hrdi : s.regs.get64 .rdi = progPtr)
    (hrsi : s.regs.get64 .rsi = progLen)
    (hrdx : s.regs.get64 .rdx = workPtr)
    (hrcx : s.regs.get64 .rcx = workCap)
    (hr8 : s.regs.get64 .r8 = fuel)
    (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hmem : s.dmem =⋆ Eq m ⋆
      (region (s.regs.get64 .rsp - BitVec.ofNat 64 b) b ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧
        (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15],
          st.data.regs.get64 r = s.regs.get64 r) ∧
        st.data.regs.get64 .rsp = s.regs.get64 .rsp + 8#64 ∧
        ∃ m',
          (bytes progPtr progBytes ⋆ region workPtr workCap.toNat ⋆ Rm) m' ∧
          (st.data.regs.get64 .rax = 20#64 →
            ∀ prog : BVLogicalExpr, BVProg.parse progBytes = some prog → prog.Unsat) ∧
          (bvSolveTrivialUnsatCond progPtr progBytes workPtr workCap fuel →
            st.data.regs.get64 .rax = 20#64) ∧
          (st.data.dmem =⋆ Eq m' ⋆
            region (s.regs.get64 .rsp - BitVec.ofNat 64 b) (b + 8) ⋆ R))
      ⟨s, Labels.label "bv_solve_bytes"⟩ := by
  refine eventually_weaken _ _ _ _ (fun _ ⟨hpc, ⟨hcal, hrsp⟩, hrest⟩ => ⟨hpc, hcal, hrsp, hrest⟩)
    (bv_solve_bytes_unsat_of_compile_optInline x64KissatAbi fidStep12Pkg
      rfl fidStep12_externs_empty fidStep12_noExit fidStep12_bitblast_names_disj rfl rfl policy
      hints code bounds hcm hb hh k₀ hc hu
      progPtr progLen workPtr workCap fuel progBytes m Rm R s ra hplen hm
      ⟨hrdi, hrsi, hrdx, hrcx, hr8⟩ hsp hmem)

/-- Raw `compileModule`-parameterized SysV x64 UNSAT soundness for `bv_solve_bytes` over
`bitblastFidStep12InlLinkedMod.fns` (`(fidStep12Module.optInlinePolicy fidInlPolicy).fns ++
bitblastModule.fns`). -/
theorem bitblast_fid_x64_unsat_of_compile
    (hints : List x64Isa.Hints) (code : List Directive) (bounds : List (Sym × Nat))
    (hcm : compileModule x64Isa x64LegalTarget 8 [] [] 0
      bitblastFidStep12InlLinkedMod.fns hints = .ok (code, bounds))
    {b : Nat} (hb : ("bv_solve_bytes", b) ∈ bounds)
    [hh : Host] (k₀ : Nat) (hc : code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (progPtr progLen workPtr workCap fuel : BitVec 64)
    (progBytes : List UInt8) (m : Mem 64) (Rm R : Mem 64 → Prop)
    (s : MachineData) (ra : Int64)
    (hplen : progLen.toNat = progBytes.length)
    (hm : (bytes progPtr progBytes ⋆ region workPtr workCap.toNat ⋆ Rm) m)
    (hrdi : s.regs.get64 .rdi = progPtr)
    (hrsi : s.regs.get64 .rsi = progLen)
    (hrdx : s.regs.get64 .rdx = workPtr)
    (hrcx : s.regs.get64 .rcx = workCap)
    (hr8 : s.regs.get64 .r8 = fuel)
    (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hmem : s.dmem =⋆ Eq m ⋆
      (region (s.regs.get64 .rsp - BitVec.ofNat 64 b) b ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧
        (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15],
          st.data.regs.get64 r = s.regs.get64 r) ∧
        st.data.regs.get64 .rsp = s.regs.get64 .rsp + 8#64 ∧
        ∃ m',
          (bytes progPtr progBytes ⋆ region workPtr workCap.toNat ⋆ Rm) m' ∧
          (st.data.regs.get64 .rax = 20#64 →
            ∀ prog : BVLogicalExpr, BVProg.parse progBytes = some prog → prog.Unsat) ∧
          (bvSolveTrivialUnsatCond progPtr progBytes workPtr workCap fuel →
            st.data.regs.get64 .rax = 20#64) ∧
          (st.data.dmem =⋆ Eq m' ⋆
            region (s.regs.get64 .rsp - BitVec.ofNat 64 b) (b + 8) ⋆ R))
      ⟨s, Labels.label "bv_solve_bytes"⟩ := by
  refine eventually_weaken _ _ _ _ (fun _ ⟨hpc, ⟨hcal, hrsp⟩, hrest⟩ => ⟨hpc, hcal, hrsp, hrest⟩)
    (bv_solve_bytes_unsat_of_compile_inl x64KissatAbi fidStep12Pkg
      rfl fidStep12_externs_empty fidStep12_noExit fidStep12_bitblast_names_disj rfl rfl
      hints code bounds hcm hb hh k₀ hc hu
      progPtr progLen workPtr workCap fuel progBytes m Rm R s ra hplen hm
      ⟨hrdi, hrsi, hrdx, hrcx, hr8⟩ hsp hmem)

/-! ## 2. `BitblastFidCertX64`-Parameterized SysV x64 Theorems -/

/-- `BitblastFidCertX64`-parameterized `Defined` + `FnSpec` for `bv_solve_bytes`. -/
theorem bitblast_fid_x64_fnSpec_of_cert (cert : BitblastFidCertX64)
    [hh : Host] (k₀ : Nat) (hc : cert.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique) :
    x64Target.Defined hh "bv_solve_bytes" ∧
      x64Target.FnSpec hh "bv_solve_bytes"
        (bitblastFidStep12LinkedEnv "bv_solve_bytes" [i64, i64, i64, i64, i64] [i64])
        (cert.bound "bv_solve_bytes") 0 :=
  bv_solve_bytes_fnSpec_of_cert x64KissatAbi fidStep12Pkg
    rfl fidStep12_externs_empty fidStep12_noExit fidStep12_bitblast_names_disj
    rfl rfl cert hh k₀ hc hu

/-- `BitblastFidCertX64`-parameterized end-to-end SysV x64 UNSAT soundness + framing. -/
theorem bitblast_fid_x64_unsat_of_cert (cert : BitblastFidCertX64)
    [hh : Host] (k₀ : Nat) (hc : cert.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (progPtr progLen workPtr workCap fuel : BitVec 64)
    (progBytes : List UInt8) (m : Mem 64) (Rm R : Mem 64 → Prop)
    (s : MachineData) (ra : Int64)
    (hplen : progLen.toNat = progBytes.length)
    (hm : (bytes progPtr progBytes ⋆ region workPtr workCap.toNat ⋆ Rm) m)
    (hrdi : s.regs.get64 .rdi = progPtr)
    (hrsi : s.regs.get64 .rsi = progLen)
    (hrdx : s.regs.get64 .rdx = workPtr)
    (hrcx : s.regs.get64 .rcx = workCap)
    (hr8 : s.regs.get64 .r8 = fuel)
    (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hmem : s.dmem =⋆ Eq m ⋆
      (region (s.regs.get64 .rsp - BitVec.ofNat 64 (cert.bound "bv_solve_bytes"))
          (cert.bound "bv_solve_bytes") ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧
        (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15],
          st.data.regs.get64 r = s.regs.get64 r) ∧
        st.data.regs.get64 .rsp = s.regs.get64 .rsp + 8#64 ∧
        ∃ m',
          (bytes progPtr progBytes ⋆ region workPtr workCap.toNat ⋆ Rm) m' ∧
          (st.data.regs.get64 .rax = 20#64 →
            ∀ prog : BVLogicalExpr, BVProg.parse progBytes = some prog → prog.Unsat) ∧
          (bvSolveTrivialUnsatCond progPtr progBytes workPtr workCap fuel →
            st.data.regs.get64 .rax = 20#64) ∧
          (st.data.dmem =⋆ Eq m' ⋆
            region (s.regs.get64 .rsp - BitVec.ofNat 64 (cert.bound "bv_solve_bytes"))
              (cert.bound "bv_solve_bytes" + 8) ⋆ R))
      ⟨s, Labels.label "bv_solve_bytes"⟩ := by
  refine eventually_weaken _ _ _ _ (fun _ ⟨hpc, ⟨hcal, hrsp⟩, hrest⟩ => ⟨hpc, hcal, hrsp, hrest⟩)
    (bv_solve_bytes_unsat_of_cert x64KissatAbi fidStep12Pkg
      rfl fidStep12_externs_empty fidStep12_noExit fidStep12_bitblast_names_disj
      rfl rfl cert hh k₀ hc hu
      progPtr progLen workPtr workCap fuel progBytes m Rm R s ra hplen hm
      ⟨hrdi, hrsi, hrdx, hrcx, hr8⟩ hsp hmem)

/-- Closed concrete-host SysV x64 UNSAT non-vacuity witness on `cert.host` (`nvSlabBytes`). -/
theorem bitblast_fid_x64_nv_unsat_run_of_cert (cert : BitblastFidCertX64) :
    let args : Tup Val [i64, i64, i64, i64, i64] :=
      (nvSlabPtr, nvProgLen, nvSlabWorkPtr, nvWorkCap, nvFuel, ())
    Eventually (x64Target.mach.step cert.host)
      (fun st =>
        x64Target.mach.pc st = x64Init.ra0 ∧
        x64Target.mach.getGpr (x64Target.mach.data st) x64Init.ret0 = 20#64 ∧
        ∀ prog : BVLogicalExpr, BVProg.parse nvProgBytes = some prog → prog.Unsat)
      (x64Target.mach.mkState
        (x64Init.initState (cert.bound "bv_solve_bytes") nvSlabBytes args)
        (x64Target.mach.labelAddr cert.host "bv_solve_bytes")) :=
  bv_solve_bytes_nv_run_of_cert x64KissatAbi fidStep12Pkg
    rfl fidStep12_externs_empty fidStep12_noExit fidStep12_bitblast_names_disj rfl rfl cert

end LeanQbe.T.Amd64.BitblastFidelityParam
