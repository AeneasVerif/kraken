module

public import LeanQbe.T.MainCertProof
public import LeanQbe.T.Amd64.BenchAbi
public import LeanQbe.T.Examples.BenchmarkCertKit
meta import Lean
meta import LeanQbe.T.MainCertElab
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Examples.LratBytes

/-!
# Untrusted-bytes LRAT proof checker (`lratBytesFns`) on SysV x64
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Amd64.LratBytes

open Std Std.ExtHashMap Std.Sat
open LeanQbe.T LeanQbe.T.Examples.LratBytes LeanQbe.T.BenchmarkCertKit
open LeanQbe.T.Examples.BenchmarkCertKit LeanQbe.T.Amd64 Kraken

open scoped LeanQbe.T in
compile_linked_chunks! lratCert
  x64Target x64Layout x64LegalTarget x64LabelClean lratBytesModule 1

/-- Concatenated register-allocation hints across all chunks of `lratCert`. -/
@[expose] noncomputable def lratBytesHints : List x64Target.toIsa.Hints :=
  chunksHints lratCert.chunks

theorem compiled_compileModule :
    compileModule x64Target.toIsa x64LegalTarget x64Target.frame.raBytes [] [] 0
      lratBytesFns lratBytesHints = .ok (lratCert.code, lratCert.bounds) :=
  linkedCert_compileModule lratCert

theorem compiled_checkLit :
    checkCompileLit x64Target.frame.label x64Layout.progSmall
      lratCert.code lratCert.bounds (lratBytesFns.map Fn.name) [] 2048 = true :=
  linkedCert_checkLit lratCert

theorem compiled_check :
    checkCompile x64Target x64Layout x64LegalTarget [] [] 0 lratBytesFns lratBytesHints 2048 =
      true :=
  linkedCert_checkCompile lratCert

/-- Chunk-linked literal-backed compilation certificate on `lratBytesFns` for SysV x64. -/
@[expose] noncomputable def compiled :
    Compiled x64Target x64LegalTarget [] [] 0 lratBytesFns lratBytesHints 2048 :=
  linkedCert_to_compiled lratCert

theorem lratBytesFns_supportsSource :
    ∀ f ∈ lratBytesModule.fns, (f.earlyOpt).body.supportsSource x64LegalTarget = true :=
  lratCert.supportsAll

section Generic
variable [hh : Host]

/-- Closed `FnSpec` for every function in `lratBytesModule` on `x64Target`. -/
theorem lrat_bytes_module_fnspec (k₀ : Nat)
    (hc : compiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {f : Fn} (hf : f ∈ lratBytesModule.fns) :
    x64Target.Defined hh f.name ∧
      x64Target.FnSpec hh f.name (lratBytesEnv f.name f.as f.rs) (compiled.bound f.name) 0 :=
  lrat_mk_module_fnspec_abi x64BenchAbi hh compiled lratBytesFns_supportsSource
    lratCheckBytesSpec lratBytesEnv_sound (fun _ _ _ _ _ h => h) k₀ hc hu hf

/-- Lifting any `FnSpec` for `"lrat_check_bytes"` at stack bound `b` and contract
`lratCheckBytesSpec` to the closed Kraken-x64 statement. -/
theorem lrat_check_bytes_x64_of_fnspec {b : Nat}
    (hfnspec : x64Target.FnSpec hh "lrat_check_bytes" lratCheckBytesSpec b 0)
    (cnf_ptr prf_ptr work_ptr : BitVec 64)
    (cnfBytes prfBytes : List UInt8) (work_len : Nat)
    (hcnf : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hprf : prf_ptr.toNat + prfBytes.length < 2 ^ 64)
    (hwork : work_ptr.toNat + work_len < 2 ^ 64)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hrdi : s.regs.get64 .rdi = cnf_ptr)
    (hrsi : s.regs.get64 .rsi = BitVec.ofNat 64 cnfBytes.length)
    (hrdx : s.regs.get64 .rdx = prf_ptr)
    (hrcx : s.regs.get64 .rcx = BitVec.ofNat 64 prfBytes.length)
    (hr8 : s.regs.get64 .r8 = work_ptr)
    (hr9 : s.regs.get64 .r9 = BitVec.ofNat 64 work_len)
    (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hmem : s.dmem =⋆
      (Eq (cnfBytes.At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆ region work_ptr work_len) ⋆
      (region (s.regs.get64 .rsp - BitVec.ofNat 64 b) b ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        (st.data.regs.get64 .rax = 0 ∨ st.data.regs.get64 .rax = 1) ∧
        (st.data.regs.get64 .rax = 1 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15],
          st.data.regs.get64 r = s.regs.get64 r) ∧
        st.data.regs.get64 .rsp = s.regs.get64 .rsp + 8#64 ∧
        (st.data.dmem =⋆
          (Eq (cnfBytes.At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆ region work_ptr work_len) ⋆
          region (s.regs.get64 .rsp - BitVec.ofNat 64 b) (b + 8) ⋆ R))
      ⟨s, Labels.label "lrat_check_bytes"⟩ :=
  lrat_check_bytes_of_fnspec_abi x64BenchAbi hh hfnspec cnf_ptr prf_ptr work_ptr
    cnfBytes prfBytes work_len hcnf hprf hwork s ra R hrdi hrsi hrdx hrcx hr8 hr9 hsp hmem

/-- Closed end-to-end correctness of compiled `lrat_check_bytes` on Kraken x64. -/
theorem lrat_check_bytes_x64_correct (k₀ : Nat)
    (hc : compiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (cnf_ptr prf_ptr work_ptr : BitVec 64)
    (cnfBytes prfBytes : List UInt8) (work_len : Nat)
    (hcnf : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hprf : prf_ptr.toNat + prfBytes.length < 2 ^ 64)
    (hwork : work_ptr.toNat + work_len < 2 ^ 64)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hrdi : s.regs.get64 .rdi = cnf_ptr)
    (hrsi : s.regs.get64 .rsi = BitVec.ofNat 64 cnfBytes.length)
    (hrdx : s.regs.get64 .rdx = prf_ptr)
    (hrcx : s.regs.get64 .rcx = BitVec.ofNat 64 prfBytes.length)
    (hr8 : s.regs.get64 .r8 = work_ptr)
    (hr9 : s.regs.get64 .r9 = BitVec.ofNat 64 work_len)
    (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hmem : s.dmem =⋆
      (Eq (cnfBytes.At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆ region work_ptr work_len) ⋆
      (region (s.regs.get64 .rsp - BitVec.ofNat 64 (compiled.bound "lrat_check_bytes"))
          (compiled.bound "lrat_check_bytes") ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        (st.data.regs.get64 .rax = 0 ∨ st.data.regs.get64 .rax = 1) ∧
        (st.data.regs.get64 .rax = 1 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15],
          st.data.regs.get64 r = s.regs.get64 r) ∧
        st.data.regs.get64 .rsp = s.regs.get64 .rsp + 8#64 ∧
        (st.data.dmem =⋆
          (Eq (cnfBytes.At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆ region work_ptr work_len) ⋆
          region (s.regs.get64 .rsp - BitVec.ofNat 64 (compiled.bound "lrat_check_bytes"))
            (compiled.bound "lrat_check_bytes" + 8) ⋆ R))
      ⟨s, Labels.label "lrat_check_bytes"⟩ :=
  lrat_check_bytes_correct_abi x64BenchAbi hh compiled lratBytesFns_supportsSource k₀ hc hu
    cnf_ptr prf_ptr work_ptr cnfBytes prfBytes work_len
    hcnf hprf hwork s ra R hrdi hrsi hrdx hrcx hr8 hr9 hsp hmem

/-- Trivial-postcondition end-to-end Kraken-x64 corollary for any `ValidDimacsCnf cnf`. -/
theorem lrat_check_bytes_x64_unsat (k₀ : Nat)
    (hc : compiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (cnf : CNF Nat) (hvalid : ValidDimacsCnf cnf)
    (cnf_ptr prf_ptr work_ptr : BitVec 64)
    (prfBytes : List UInt8) (work_len : Nat)
    (hcnf : cnf_ptr.toNat + (encodeDimacs cnf).length < 2 ^ 64)
    (hprf : prf_ptr.toNat + prfBytes.length < 2 ^ 64)
    (hwork : work_ptr.toNat + work_len < 2 ^ 64)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hrdi : s.regs.get64 .rdi = cnf_ptr)
    (hrsi : s.regs.get64 .rsi = BitVec.ofNat 64 (encodeDimacs cnf).length)
    (hrdx : s.regs.get64 .rdx = prf_ptr)
    (hrcx : s.regs.get64 .rcx = BitVec.ofNat 64 prfBytes.length)
    (hr8 : s.regs.get64 .r8 = work_ptr)
    (hr9 : s.regs.get64 .r9 = BitVec.ofNat 64 work_len)
    (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hmem : s.dmem =⋆
      (Eq ((encodeDimacs cnf).At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆
        region work_ptr work_len) ⋆
      (region (s.regs.get64 .rsp - BitVec.ofNat 64 (compiled.bound "lrat_check_bytes"))
          (compiled.bound "lrat_check_bytes") ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        (st.data.regs.get64 .rax = 0 ∨ st.data.regs.get64 .rax = 1) ∧
        (st.data.regs.get64 .rax = 1 → cnf.Unsat))
      ⟨s, Labels.label "lrat_check_bytes"⟩ :=
  lrat_check_bytes_unsat_abi x64BenchAbi hh compiled lratBytesFns_supportsSource k₀ hc hu
    cnf hvalid cnf_ptr prf_ptr work_ptr prfBytes work_len
    hcnf hprf hwork s ra R hrdi hrsi hrdx hrcx hr8 hr9 hsp hmem

end Generic

/-! ## Concrete SysV x64 Executions in `compiled.host` (`rax = 1` and `rax = 0`) -/

noncomputable abbrev lratBytesHost : Host := compiled.host
attribute [local instance] lratBytesHost

abbrev lratBytesArgs (cnfBytes prfBytes : List UInt8) :
    Tup Val [i64, i64, i64, i64, i64, i64] :=
  Examples.BenchmarkCertKit.lratBytesArgs cnfBytes prfBytes

@[expose] noncomputable def lratBytesState (cnfBytes prfBytes : List UInt8) : MachineData :=
  x64Init.initState (as := [i64, i64, i64, i64, i64, i64])
    (compiled.bound "lrat_check_bytes")
    (lratBytesPayload cnfBytes prfBytes) (lratBytesArgs cnfBytes prfBytes)

@[expose] noncomputable def lratBytesAcceptState0 : MachineData :=
  lratBytesState nvDimacsBytes nvLratAcceptBytes

/-- Concrete accepting execution of compiled `lrat_check_bytes` on Kraken x64. -/
theorem lrat_check_bytes_x64_accepts :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧ st.data.regs.get64 .rax = 1 ∧ nvBytesCnf.Unsat)
      ⟨lratBytesAcceptState0, Labels.label "lrat_check_bytes"⟩ :=
  lrat_check_bytes_accepts_abi x64BenchAbi compiled lratBytesFns_supportsSource

@[expose] noncomputable def lratBytesRejectState0 : MachineData :=
  lratBytesState nvDimacsBytes nvLratRejectBytes

/-- Concrete rejecting execution of compiled `lrat_check_bytes` on Kraken x64. -/
theorem lrat_check_bytes_x64_rejects :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧ st.data.regs.get64 .rax = 0)
      ⟨lratBytesRejectState0, Labels.label "lrat_check_bytes"⟩ :=
  lrat_check_bytes_rejects_abi x64BenchAbi compiled lratBytesFns_supportsSource

end LeanQbe.T.Amd64.LratBytes
