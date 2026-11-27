module

public import LeanQbe.T.MainCertProof
public import LeanQbe.T.Arm64.BenchAbi
public import LeanQbe.T.Examples.BenchmarkCertKit
meta import Lean
meta import LeanQbe.T.MainCertElab
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Examples.LratBytes

/-!
# Untrusted-bytes LRAT proof checker (`lratBytesFns`) on AArch64
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Arm64.LratBytes

open Std Std.ExtHashMap Std.Sat
open LeanQbe.T LeanQbe.T.Examples.LratBytes LeanQbe.T.BenchmarkCertKit
open LeanQbe.T.Examples.BenchmarkCertKit LeanQbe.T.Arm64 Kraken

open scoped LeanQbe.T in
compile_linked_chunks! lratCert
  armTarget armLayout armLegalTarget armLabelClean lratBytesModule 1

/-- Concatenated register-allocation hints across all chunks of `lratCert`. -/
@[expose] noncomputable def lratBytesHints : List armTarget.toIsa.Hints :=
  chunksHints lratCert.chunks

theorem compiled_compileModule :
    compileModule armTarget.toIsa armLegalTarget armTarget.frame.raBytes [] [] 0
      lratBytesFns lratBytesHints = .ok (lratCert.code, lratCert.bounds) :=
  linkedCert_compileModule lratCert

theorem compiled_checkLit :
    checkCompileLit armTarget.frame.label armLayout.progSmall
      lratCert.code lratCert.bounds (lratBytesFns.map Fn.name) [] 2048 = true :=
  linkedCert_checkLit lratCert

theorem compiled_check :
    checkCompile armTarget armLayout armLegalTarget [] [] 0 lratBytesFns lratBytesHints 2048 =
      true :=
  linkedCert_checkCompile lratCert

/-- Chunk-linked literal-backed compilation certificate on `lratBytesFns` for AArch64. -/
@[expose] noncomputable def compiled :
    Compiled armTarget armLegalTarget [] [] 0 lratBytesFns lratBytesHints 2048 :=
  linkedCert_to_compiled lratCert

theorem lratBytesFns_supportsSource :
    ∀ f ∈ lratBytesModule.fns, (f.earlyOpt).body.supportsSource armLegalTarget = true :=
  lratCert.supportsAll

section Generic
variable [hh : Host]

/-- Closed `FnSpec` for every function in `lratBytesModule` on `armTarget`. -/
theorem lrat_bytes_module_fnspec (k₀ : Nat)
    (hc : compiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {f : Fn} (hf : f ∈ lratBytesModule.fns) :
    armTarget.Defined hh f.name ∧
      armTarget.FnSpec hh f.name (lratBytesEnv f.name f.as f.rs) (compiled.bound f.name) 0 :=
  lrat_mk_module_fnspec_abi arm64BenchAbi hh compiled lratBytesFns_supportsSource
    lratCheckBytesSpec lratBytesEnv_sound (fun _ _ _ _ _ h => h) k₀ hc hu hf

/-- Lifting any `FnSpec` for `"lrat_check_bytes"` at stack bound `b` and contract
`lratCheckBytesSpec` to the closed Kraken-AArch64 statement. -/
theorem lrat_check_bytes_arm64_of_fnspec {b : Nat}
    (hfnspec : armTarget.FnSpec hh "lrat_check_bytes" lratCheckBytesSpec b 0)
    (cnf_ptr prf_ptr work_ptr : BitVec 64)
    (cnfBytes prfBytes : List UInt8) (work_len : Nat)
    (hcnf : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hprf : prf_ptr.toNat + prfBytes.length < 2 ^ 64)
    (hwork : work_ptr.toNat + work_len < 2 ^ 64)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hx0 : (s.regs.getXReg .X0).toBitVec = cnf_ptr)
    (hx1 : (s.regs.getXReg .X1).toBitVec = BitVec.ofNat 64 cnfBytes.length)
    (hx2 : (s.regs.getXReg .X2).toBitVec = prf_ptr)
    (hx3 : (s.regs.getXReg .X3).toBitVec = BitVec.ofNat 64 prfBytes.length)
    (hx4 : (s.regs.getXReg .X4).toBitVec = work_ptr)
    (hx5 : (s.regs.getXReg .X5).toBitVec = BitVec.ofNat 64 work_len)
    (hra : s.regs.X30 = ra.toUInt64) (hsp : s.regs.SP.toNat % 16 = 0)
    (hmem : s.dmem =⋆
      (Eq (cnfBytes.At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆ region work_ptr work_len) ⋆
      region (s.regs.SP.toBitVec - BitVec.ofNat 64 b) b ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        ((st.data.regs.getXReg .X0).toBitVec = 0 ∨
          (st.data.regs.getXReg .X0).toBitVec = 1) ∧
        ((st.data.regs.getXReg .X0).toBitVec = 1 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
          st.data.regs.getXReg r = s.regs.getXReg r) ∧
        st.data.regs.SP = s.regs.SP ∧
        (st.data.dmem =⋆
          (Eq (cnfBytes.At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆ region work_ptr work_len) ⋆
          region (s.regs.SP.toBitVec - BitVec.ofNat 64 b) b ⋆ R))
      ⟨s, Labels.label "lrat_check_bytes"⟩ :=
  lrat_check_bytes_of_fnspec_abi arm64BenchAbi hh hfnspec cnf_ptr prf_ptr work_ptr
    cnfBytes prfBytes work_len hcnf hprf hwork s ra R hx0 hx1 hx2 hx3 hx4 hx5 ⟨hra, hsp⟩ hmem

/-- Closed end-to-end AArch64 theorem for `lrat_check_bytes`. -/
theorem lrat_check_bytes_arm64_correct (k₀ : Nat)
    (hc : compiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (cnf_ptr prf_ptr work_ptr : BitVec 64)
    (cnfBytes prfBytes : List UInt8) (work_len : Nat)
    (hcnf : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hprf : prf_ptr.toNat + prfBytes.length < 2 ^ 64)
    (hwork : work_ptr.toNat + work_len < 2 ^ 64)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hx0 : (s.regs.getXReg .X0).toBitVec = cnf_ptr)
    (hx1 : (s.regs.getXReg .X1).toBitVec = BitVec.ofNat 64 cnfBytes.length)
    (hx2 : (s.regs.getXReg .X2).toBitVec = prf_ptr)
    (hx3 : (s.regs.getXReg .X3).toBitVec = BitVec.ofNat 64 prfBytes.length)
    (hx4 : (s.regs.getXReg .X4).toBitVec = work_ptr)
    (hx5 : (s.regs.getXReg .X5).toBitVec = BitVec.ofNat 64 work_len)
    (hra : s.regs.X30 = ra.toUInt64) (hsp : s.regs.SP.toNat % 16 = 0)
    (hmem : s.dmem =⋆
      (Eq (cnfBytes.At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆ region work_ptr work_len) ⋆
      region (s.regs.SP.toBitVec - BitVec.ofNat 64 (compiled.bound "lrat_check_bytes"))
        (compiled.bound "lrat_check_bytes") ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        ((st.data.regs.getXReg .X0).toBitVec = 0 ∨
          (st.data.regs.getXReg .X0).toBitVec = 1) ∧
        ((st.data.regs.getXReg .X0).toBitVec = 1 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
          st.data.regs.getXReg r = s.regs.getXReg r) ∧
        st.data.regs.SP = s.regs.SP ∧
        (st.data.dmem =⋆
          (Eq (cnfBytes.At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆ region work_ptr work_len) ⋆
          region (s.regs.SP.toBitVec - BitVec.ofNat 64 (compiled.bound "lrat_check_bytes"))
            (compiled.bound "lrat_check_bytes") ⋆ R))
      ⟨s, Labels.label "lrat_check_bytes"⟩ :=
  lrat_check_bytes_correct_abi arm64BenchAbi hh compiled lratBytesFns_supportsSource k₀ hc hu
    cnf_ptr prf_ptr work_ptr cnfBytes prfBytes work_len
    hcnf hprf hwork s ra R hx0 hx1 hx2 hx3 hx4 hx5 ⟨hra, hsp⟩ hmem

/-- Trivial-postcondition end-to-end Kraken-AArch64 corollary for any `ValidDimacsCnf cnf`. -/
theorem lrat_check_bytes_arm64_unsat (k₀ : Nat)
    (hc : compiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (cnf : CNF Nat) (hvalid : ValidDimacsCnf cnf)
    (cnf_ptr prf_ptr work_ptr : BitVec 64)
    (prfBytes : List UInt8) (work_len : Nat)
    (hcnf : cnf_ptr.toNat + (encodeDimacs cnf).length < 2 ^ 64)
    (hprf : prf_ptr.toNat + prfBytes.length < 2 ^ 64)
    (hwork : work_ptr.toNat + work_len < 2 ^ 64)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hx0 : (s.regs.getXReg .X0).toBitVec = cnf_ptr)
    (hx1 : (s.regs.getXReg .X1).toBitVec = BitVec.ofNat 64 (encodeDimacs cnf).length)
    (hx2 : (s.regs.getXReg .X2).toBitVec = prf_ptr)
    (hx3 : (s.regs.getXReg .X3).toBitVec = BitVec.ofNat 64 prfBytes.length)
    (hx4 : (s.regs.getXReg .X4).toBitVec = work_ptr)
    (hx5 : (s.regs.getXReg .X5).toBitVec = BitVec.ofNat 64 work_len)
    (hra : s.regs.X30 = ra.toUInt64) (hsp : s.regs.SP.toNat % 16 = 0)
    (hmem : s.dmem =⋆
      (Eq ((encodeDimacs cnf).At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆
        region work_ptr work_len) ⋆
      region (s.regs.SP.toBitVec - BitVec.ofNat 64 (compiled.bound "lrat_check_bytes"))
        (compiled.bound "lrat_check_bytes") ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        ((st.data.regs.getXReg .X0).toBitVec = 0 ∨
          (st.data.regs.getXReg .X0).toBitVec = 1) ∧
        ((st.data.regs.getXReg .X0).toBitVec = 1 → cnf.Unsat))
      ⟨s, Labels.label "lrat_check_bytes"⟩ :=
  lrat_check_bytes_unsat_abi arm64BenchAbi hh compiled lratBytesFns_supportsSource k₀ hc hu
    cnf hvalid cnf_ptr prf_ptr work_ptr prfBytes work_len
    hcnf hprf hwork s ra R hx0 hx1 hx2 hx3 hx4 hx5 ⟨hra, hsp⟩ hmem

end Generic

/-! ## Concrete AArch64 Executions in `compiled.host` (`x0 = 1` and `x0 = 0`) -/

noncomputable abbrev lratBytesHost : Host := compiled.host
attribute [local instance] lratBytesHost

abbrev lratBytesArgs (cnfBytes prfBytes : List UInt8) :
    Tup Val [i64, i64, i64, i64, i64, i64] :=
  Examples.BenchmarkCertKit.lratBytesArgs cnfBytes prfBytes

@[expose] noncomputable def lratBytesState (cnfBytes prfBytes : List UInt8) : MachineData :=
  armInit.initState (as := [i64, i64, i64, i64, i64, i64])
    (compiled.bound "lrat_check_bytes")
    (lratBytesPayload cnfBytes prfBytes) (lratBytesArgs cnfBytes prfBytes)

@[expose] noncomputable def lratBytesAcceptState0 : MachineData :=
  lratBytesState nvDimacsBytes nvLratAcceptBytes

/-- Concrete accepting execution of compiled `lrat_check_bytes` on Kraken AArch64. -/
theorem lrat_check_bytes_arm64_accepts :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = 0x1234 ∧ (st.data.regs.getXReg .X0).toBitVec = 1 ∧ nvBytesCnf.Unsat)
      ⟨lratBytesAcceptState0, Labels.label "lrat_check_bytes"⟩ :=
  lrat_check_bytes_accepts_abi arm64BenchAbi compiled lratBytesFns_supportsSource

@[expose] noncomputable def lratBytesRejectState0 : MachineData :=
  lratBytesState nvDimacsBytes nvLratRejectBytes

/-- Concrete rejecting execution of compiled `lrat_check_bytes` on Kraken AArch64. -/
theorem lrat_check_bytes_arm64_rejects :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧ (st.data.regs.getXReg .X0).toBitVec = 0)
      ⟨lratBytesRejectState0, Labels.label "lrat_check_bytes"⟩ :=
  lrat_check_bytes_rejects_abi arm64BenchAbi compiled lratBytesFns_supportsSource

end LeanQbe.T.Arm64.LratBytes
