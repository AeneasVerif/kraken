/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Arm64.KissatAbi
public import LeanQbe.T.Examples.Kissat.FullFidelityBitblastLemmas
import Kraken.Mem
import Kraken.Separation

/-!
# Bitblast + KissatFidelity (`581` fns) Tier-1 Parameterized AAPCS64 Arm64 Theorems

Proves end-to-end AAPCS64 Arm64 machine-code UNSAT soundness (`X0 = 20#64 -> ∀ prog, parse = some
prog → prog.Unsat`) and concrete closed-host non-vacuity for `bv_solve_bytes`, parameterized over:
1. Raw `compileModuleOptInlinePolicy` on `bitblastFidStep12LinkedMod` (any `InlinePolicy`).
2. Raw `compileModule` on `bitblastFidStep12InlLinkedMod.fns` (`(fidStep12Module.optInlinePolicy
   fidInlPolicy).fns ++ bitblastModule.fns` — exact assembly emitted by `bv_decide_qbe`).
3. Concrete `BitblastFidCertArm64` (`LinkedCert` over `bitblastFidStep12InlLinkedMod`, ready for
   1-line swap `fidStep12UnsatPkg -> fidStep13UnsatPkg` +
   `fidStep13Cert.append bitblastTailArm64Cert`).

Imports zero `*Cert*`, zero materialized `*Inl*`, and zero `MainCertElab` modules (`<= std3`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Arm64.BitblastFidelityParam

open Std Std.ExtHashMap Std.Tactic.BVDecide
open LeanQbe.T LeanQbe.T.Arm64 Kraken
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.KissatCertCommon
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep12
open LeanQbe.T.Examples.Kissat.FullFidelityBitblastLemmas
open LeanQbe.T.Examples.Bitblast.Ref
open LeanQbe.T.Examples.Bitblast.Ref.BVProg
open LeanQbe.T.Examples.Bitblast.Proof

/-- Concrete AAPCS64 Arm64 certificate witness type for `bitblastFidStep12InlLinkedMod`
(`581` fns). -/
abbrev BitblastFidCertArm64 : Type 1 :=
  LinkedCert armTarget armLayout armLegalTarget armLabelClean
    bitblastFidStep12InlLinkedMod [] [] 0 2048

/-! ## 1. Raw `compileModuleOptInlinePolicy` & `compileModule` AAPCS64 Arm64 Theorems -/

/-- Raw `compileModuleOptInlinePolicy`-parameterized AAPCS64 Arm64 UNSAT soundness for
`bv_solve_bytes` over `bitblastFidStep12LinkedMod` (`581` fns). -/
theorem bitblast_fid_arm64_unsat_of_compile_optInline
    (policy : InlinePolicy)
    (hints : List armIsa.Hints) (code : List Directive) (bounds : List (Sym × Nat))
    (hcm : compileModuleOptInlinePolicy armIsa armLegalTarget 0 [] [] 0
      bitblastFidStep12LinkedMod hints policy = .ok (code, bounds))
    {b : Nat} (hb : ("bv_solve_bytes", b) ∈ bounds)
    [hh : Host] (k₀ : Nat) (hc : code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (progPtr progLen workPtr workCap fuel : BitVec 64)
    (progBytes : List UInt8) (m : Mem 64) (Rm R : Mem 64 → Prop)
    (s : MachineData) (ra : Int64)
    (hplen : progLen.toNat = progBytes.length)
    (hm : (bytes progPtr progBytes ⋆ region workPtr workCap.toNat ⋆ Rm) m)
    (hx0 : (s.regs.getXReg .X0).toBitVec = progPtr)
    (hx1 : (s.regs.getXReg .X1).toBitVec = progLen)
    (hx2 : (s.regs.getXReg .X2).toBitVec = workPtr)
    (hx3 : (s.regs.getXReg .X3).toBitVec = workCap)
    (hx4 : (s.regs.getXReg .X4).toBitVec = fuel)
    (hra : s.regs.X30 = ra.toUInt64) (hsp : s.regs.SP.toNat % 16 = 0)
    (hmem : s.dmem =⋆ Eq m ⋆ region (s.regs.SP.toBitVec - BitVec.ofNat 64 b) b ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧
        (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
          st.data.regs.getXReg r = s.regs.getXReg r) ∧
        st.data.regs.SP = s.regs.SP ∧
        ∃ m',
          (bytes progPtr progBytes ⋆ region workPtr workCap.toNat ⋆ Rm) m' ∧
          ((st.data.regs.getXReg .X0).toBitVec = 20#64 →
            ∀ prog : BVLogicalExpr, BVProg.parse progBytes = some prog → prog.Unsat) ∧
          (bvSolveTrivialUnsatCond progPtr progBytes workPtr workCap fuel →
            (st.data.regs.getXReg .X0).toBitVec = 20#64) ∧
          (st.data.dmem =⋆ Eq m' ⋆ region (s.regs.SP.toBitVec - BitVec.ofNat 64 b) b ⋆ R))
      ⟨s, Labels.label "bv_solve_bytes"⟩ := by
  refine eventually_weaken _ _ _ _ (fun _ ⟨hpc, ⟨hcal, hsp'⟩, hrest⟩ => ⟨hpc, hcal, hsp', hrest⟩)
    (bv_solve_bytes_unsat_of_compile_optInline arm64KissatAbi fidStep12Pkg
      rfl fidStep12_externs_empty fidStep12_noExit fidStep12_bitblast_names_disj rfl rfl policy
      hints code bounds hcm hb hh k₀ hc hu
      progPtr progLen workPtr workCap fuel progBytes m Rm R s ra hplen hm
      ⟨hx0, hx1, hx2, hx3, hx4⟩ ⟨hra, hsp⟩ hmem)

/-- Raw `compileModule`-parameterized AAPCS64 Arm64 UNSAT soundness for `bv_solve_bytes` over
`bitblastFidStep12InlLinkedMod.fns` (`(fidStep12Module.optInlinePolicy fidInlPolicy).fns ++
bitblastModule.fns`). -/
theorem bitblast_fid_arm64_unsat_of_compile
    (hints : List armIsa.Hints) (code : List Directive) (bounds : List (Sym × Nat))
    (hcm : compileModule armIsa armLegalTarget 0 [] [] 0
      bitblastFidStep12InlLinkedMod.fns hints = .ok (code, bounds))
    {b : Nat} (hb : ("bv_solve_bytes", b) ∈ bounds)
    [hh : Host] (k₀ : Nat) (hc : code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (progPtr progLen workPtr workCap fuel : BitVec 64)
    (progBytes : List UInt8) (m : Mem 64) (Rm R : Mem 64 → Prop)
    (s : MachineData) (ra : Int64)
    (hplen : progLen.toNat = progBytes.length)
    (hm : (bytes progPtr progBytes ⋆ region workPtr workCap.toNat ⋆ Rm) m)
    (hx0 : (s.regs.getXReg .X0).toBitVec = progPtr)
    (hx1 : (s.regs.getXReg .X1).toBitVec = progLen)
    (hx2 : (s.regs.getXReg .X2).toBitVec = workPtr)
    (hx3 : (s.regs.getXReg .X3).toBitVec = workCap)
    (hx4 : (s.regs.getXReg .X4).toBitVec = fuel)
    (hra : s.regs.X30 = ra.toUInt64) (hsp : s.regs.SP.toNat % 16 = 0)
    (hmem : s.dmem =⋆ Eq m ⋆ region (s.regs.SP.toBitVec - BitVec.ofNat 64 b) b ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧
        (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
          st.data.regs.getXReg r = s.regs.getXReg r) ∧
        st.data.regs.SP = s.regs.SP ∧
        ∃ m',
          (bytes progPtr progBytes ⋆ region workPtr workCap.toNat ⋆ Rm) m' ∧
          ((st.data.regs.getXReg .X0).toBitVec = 20#64 →
            ∀ prog : BVLogicalExpr, BVProg.parse progBytes = some prog → prog.Unsat) ∧
          (bvSolveTrivialUnsatCond progPtr progBytes workPtr workCap fuel →
            (st.data.regs.getXReg .X0).toBitVec = 20#64) ∧
          (st.data.dmem =⋆ Eq m' ⋆ region (s.regs.SP.toBitVec - BitVec.ofNat 64 b) b ⋆ R))
      ⟨s, Labels.label "bv_solve_bytes"⟩ := by
  refine eventually_weaken _ _ _ _ (fun _ ⟨hpc, ⟨hcal, hsp'⟩, hrest⟩ => ⟨hpc, hcal, hsp', hrest⟩)
    (bv_solve_bytes_unsat_of_compile_inl arm64KissatAbi fidStep12Pkg
      rfl fidStep12_externs_empty fidStep12_noExit fidStep12_bitblast_names_disj rfl rfl
      hints code bounds hcm hb hh k₀ hc hu
      progPtr progLen workPtr workCap fuel progBytes m Rm R s ra hplen hm
      ⟨hx0, hx1, hx2, hx3, hx4⟩ ⟨hra, hsp⟩ hmem)

/-! ## 2. `BitblastFidCertArm64`-Parameterized AAPCS64 Arm64 Theorems -/

/-- `BitblastFidCertArm64`-parameterized `Defined` + `FnSpec` for `bv_solve_bytes`. -/
theorem bitblast_fid_arm64_fnSpec_of_cert (cert : BitblastFidCertArm64)
    [hh : Host] (k₀ : Nat) (hc : cert.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique) :
    armTarget.Defined hh "bv_solve_bytes" ∧
      armTarget.FnSpec hh "bv_solve_bytes"
        (bitblastFidStep12LinkedEnv "bv_solve_bytes" [i64, i64, i64, i64, i64] [i64])
        (cert.bound "bv_solve_bytes") 0 :=
  bv_solve_bytes_fnSpec_of_cert arm64KissatAbi fidStep12Pkg
    rfl fidStep12_externs_empty fidStep12_noExit fidStep12_bitblast_names_disj
    rfl rfl cert hh k₀ hc hu

/-- `BitblastFidCertArm64`-parameterized end-to-end AAPCS64 Arm64 UNSAT soundness + framing. -/
theorem bitblast_fid_arm64_unsat_of_cert (cert : BitblastFidCertArm64)
    [hh : Host] (k₀ : Nat) (hc : cert.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (progPtr progLen workPtr workCap fuel : BitVec 64)
    (progBytes : List UInt8) (m : Mem 64) (Rm R : Mem 64 → Prop)
    (s : MachineData) (ra : Int64)
    (hplen : progLen.toNat = progBytes.length)
    (hm : (bytes progPtr progBytes ⋆ region workPtr workCap.toNat ⋆ Rm) m)
    (hx0 : (s.regs.getXReg .X0).toBitVec = progPtr)
    (hx1 : (s.regs.getXReg .X1).toBitVec = progLen)
    (hx2 : (s.regs.getXReg .X2).toBitVec = workPtr)
    (hx3 : (s.regs.getXReg .X3).toBitVec = workCap)
    (hx4 : (s.regs.getXReg .X4).toBitVec = fuel)
    (hra : s.regs.X30 = ra.toUInt64) (hsp : s.regs.SP.toNat % 16 = 0)
    (hmem : s.dmem =⋆ Eq m ⋆
      region (s.regs.SP.toBitVec - BitVec.ofNat 64 (cert.bound "bv_solve_bytes"))
        (cert.bound "bv_solve_bytes") ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧
        (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
          st.data.regs.getXReg r = s.regs.getXReg r) ∧
        st.data.regs.SP = s.regs.SP ∧
        ∃ m',
          (bytes progPtr progBytes ⋆ region workPtr workCap.toNat ⋆ Rm) m' ∧
          ((st.data.regs.getXReg .X0).toBitVec = 20#64 →
            ∀ prog : BVLogicalExpr, BVProg.parse progBytes = some prog → prog.Unsat) ∧
          (bvSolveTrivialUnsatCond progPtr progBytes workPtr workCap fuel →
            (st.data.regs.getXReg .X0).toBitVec = 20#64) ∧
          (st.data.dmem =⋆ Eq m' ⋆
            region (s.regs.SP.toBitVec - BitVec.ofNat 64 (cert.bound "bv_solve_bytes"))
              (cert.bound "bv_solve_bytes") ⋆ R))
      ⟨s, Labels.label "bv_solve_bytes"⟩ := by
  refine eventually_weaken _ _ _ _ (fun _ ⟨hpc, ⟨hcal, hsp'⟩, hrest⟩ => ⟨hpc, hcal, hsp', hrest⟩)
    (bv_solve_bytes_unsat_of_cert arm64KissatAbi fidStep12Pkg
      rfl fidStep12_externs_empty fidStep12_noExit fidStep12_bitblast_names_disj
      rfl rfl cert hh k₀ hc hu
      progPtr progLen workPtr workCap fuel progBytes m Rm R s ra hplen hm
      ⟨hx0, hx1, hx2, hx3, hx4⟩ ⟨hra, hsp⟩ hmem)

/-- Closed concrete-host AAPCS64 Arm64 UNSAT non-vacuity witness on `cert.host` (`nvSlabBytes`). -/
theorem bitblast_fid_arm64_nv_unsat_run_of_cert (cert : BitblastFidCertArm64) :
    let args : Tup Val [i64, i64, i64, i64, i64] :=
      (nvSlabPtr, nvProgLen, nvSlabWorkPtr, nvWorkCap, nvFuel, ())
    Eventually (armTarget.mach.step cert.host)
      (fun st =>
        armTarget.mach.pc st = armInit.ra0 ∧
        armTarget.mach.getGpr (armTarget.mach.data st) armInit.ret0 = 20#64 ∧
        ∀ prog : BVLogicalExpr, BVProg.parse nvProgBytes = some prog → prog.Unsat)
      (armTarget.mach.mkState
        (armInit.initState (cert.bound "bv_solve_bytes") nvSlabBytes args)
        (armTarget.mach.labelAddr cert.host "bv_solve_bytes")) :=
  bv_solve_bytes_nv_run_of_cert arm64KissatAbi fidStep12Pkg
    rfl fidStep12_externs_empty fidStep12_noExit fidStep12_bitblast_names_disj rfl rfl cert

end LeanQbe.T.Arm64.BitblastFidelityParam
