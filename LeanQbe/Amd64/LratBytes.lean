module

public import LeanQbe.Amd64.TargLemmas
public import LeanQbe.Examples.LratBytesLemmas
import all Kraken.Separation
import all Kraken.Mem

/-!
# Untrusted-bytes LRAT proof checker (`lratBytesFns`) on x64

Instantiates the target-generic 6-function untrusted-bytes DIMACS + Binary LRAT checker module
`lratBytesFns` on `Amd64.target` via a single kernel evaluation (`compileChecked ... (by kernel_rfl)`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.Amd64.LratBytes

open Std.Sat LeanQbe LeanQbe.LratBytes Amd64 Kraken

-- The limit guards the cost of the compiler in the kernel: this check needs about 31,000
-- heartbeats (27 s). Heartbeats count allocations, so the limit holds on a busy machine too.
set_option maxHeartbeats 48000 in
/-- Single kernel evaluation of the compiler on `lratBytesFns` for x64. -/
def compiled : Compiled target [] [] 0 lratBytesFns :=
  compileChecked target targetLayout [] [] 0 lratBytesFns 2048 (by kernel_rfl)

section Generic
variable [hh : Host]

/-- Closed `FnSpec` for every function in `lratBytesFns` on `Amd64.target`. -/
theorem lrat_bytes_module_fnspec (k₀ : Nat)
    (hc : compiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {nm : String} (hnm : nm ∈ lratBytesFns.map Fn.name) :
    target.Defined hh nm ∧ target.FnSpec hh nm (lratBytesEnv nm) (compiled.bound nm) 0 :=
  lrat_bytes_fnSpec compiled hh k₀ hc hu hnm

/-- Lifting any `FnSpec` for `"lrat_check_bytes"` at stack bound `b` and contract
`lratCheckBytesSpec` to the closed Kraken-x64 statement. -/
theorem lrat_check_bytes_x64_of_fnspec {b : Nat}
    (hfnspec : target.FnSpec hh "lrat_check_bytes" lratCheckBytesSpec b 0)
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
      ((fun f => ∃ bs : List UInt8, bs.length = b ∧
          f = bs.At (s.regs.get64 .rsp - BitVec.ofNat 64 b)) ⋆
        Eq (ra.toUInt64.At (s.regs.get64 .rsp))) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        (st.data.regs.get64 .rax = 0 ∨ st.data.regs.get64 .rax = 1) ∧
        (st.data.regs.get64 .rax = 1 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15], st.data.regs.get64 r = s.regs.get64 r) ∧
        st.data.regs.get64 .rsp = s.regs.get64 .rsp + 8#64 ∧
        (st.data.dmem =⋆
          (Eq (cnfBytes.At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆ region work_ptr work_len) ⋆
          (fun f => ∃ bs : List UInt8, bs.length = b + 8 ∧
              f = bs.At (s.regs.get64 .rsp - BitVec.ofNat 64 b)) ⋆ R))
      ⟨s, Labels.label "lrat_check_bytes"⟩ := by
  have hargs : target.ArgsIn
      [cnf_ptr, BitVec.ofNat 64 cnfBytes.length,
       prf_ptr, BitVec.ofNat 64 prfBytes.length,
       work_ptr, BitVec.ofNat 64 work_len] s := by
    simp [Target.ArgsIn, Target.ValsIn, target, isa, hrdi, hrsi, hrdx, hrcx, hr8, hr9]
  refine eventually_weaken _ _ _ _ ?_
    (amd64_of_returns
      (lrat_check_bytes_of_fnspec hfnspec cnf_ptr prf_ptr work_ptr cnfBytes prfBytes work_len
        hcnf hprf hwork)
      s ra R hargs hsp hmem)
  rintro st ⟨hpc, hcs, hsp', rets, hrets,
    f1, f2, hu1, hd1, ⟨m', fe, hu2, hd2, ⟨r, rfl, hr01, hunsat, hP⟩, hexit⟩, hf2⟩
  have hrax : st.data.regs.get64 .rax = r := by
    simpa [Target.RetsIn, Target.ValsIn, target, isa] using hrets
  rw [← hrax] at hr01 hunsat
  exact ⟨hpc, hr01, hunsat, hcs, hsp', f1, f2, hu1, hd1, ⟨m', fe, hu2, hd2, hP, hexit⟩, hf2⟩

/-- Trivial-postcondition lifting helper. -/
theorem lrat_check_bytes_x64_unsat_of_fnspec {b : Nat}
    (hfnspec : target.FnSpec hh "lrat_check_bytes" lratCheckBytesSpec b 0)
    (cnf : CNF Nat) (cnf_ptr prf_ptr work_ptr : BitVec 64)
    (cnfBytes prfBytes : List UInt8) (work_len : Nat)
    (hparse : parseDimacs cnfBytes = some cnf)
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
      ((fun f => ∃ bs : List UInt8, bs.length = b ∧
          f = bs.At (s.regs.get64 .rsp - BitVec.ofNat 64 b)) ⋆
        Eq (ra.toUInt64.At (s.regs.get64 .rsp))) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        (st.data.regs.get64 .rax = 0 ∨ st.data.regs.get64 .rax = 1) ∧
        (st.data.regs.get64 .rax = 1 → cnf.Unsat))
      ⟨s, Labels.label "lrat_check_bytes"⟩ := by
  refine eventually_weaken _ _ _ _ ?_
    (lrat_check_bytes_x64_of_fnspec hfnspec cnf_ptr prf_ptr work_ptr cnfBytes prfBytes work_len
      hcnf hprf hwork s ra R hrdi hrsi hrdx hrcx hr8 hr9 hsp hmem)
  grind

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
      ((fun f => ∃ bs : List UInt8, bs.length = compiled.bound "lrat_check_bytes" ∧
          f = bs.At (s.regs.get64 .rsp - BitVec.ofNat 64 (compiled.bound "lrat_check_bytes"))) ⋆
        Eq (ra.toUInt64.At (s.regs.get64 .rsp))) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        (st.data.regs.get64 .rax = 0 ∨ st.data.regs.get64 .rax = 1) ∧
        (st.data.regs.get64 .rax = 1 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15], st.data.regs.get64 r = s.regs.get64 r) ∧
        st.data.regs.get64 .rsp = s.regs.get64 .rsp + 8#64 ∧
        (st.data.dmem =⋆
          (Eq (cnfBytes.At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆ region work_ptr work_len) ⋆
          (fun f => ∃ bs : List UInt8, bs.length = compiled.bound "lrat_check_bytes" + 8 ∧
              f = bs.At (s.regs.get64 .rsp - BitVec.ofNat 64 (compiled.bound "lrat_check_bytes"))) ⋆ R))
      ⟨s, Labels.label "lrat_check_bytes"⟩ :=
  lrat_check_bytes_x64_of_fnspec
    (by simpa [lratBytesEnv_entry] using
      (lrat_bytes_module_fnspec k₀ hc hu (nm := "lrat_check_bytes") (by decide)).2)
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
      (Eq ((encodeDimacs cnf).At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆ region work_ptr work_len) ⋆
      ((fun f => ∃ bs : List UInt8, bs.length = compiled.bound "lrat_check_bytes" ∧
          f = bs.At (s.regs.get64 .rsp - BitVec.ofNat 64 (compiled.bound "lrat_check_bytes"))) ⋆
        Eq (ra.toUInt64.At (s.regs.get64 .rsp))) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        (st.data.regs.get64 .rax = 0 ∨ st.data.regs.get64 .rax = 1) ∧
        (st.data.regs.get64 .rax = 1 → cnf.Unsat))
      ⟨s, Labels.label "lrat_check_bytes"⟩ :=
  lrat_check_bytes_x64_unsat_of_fnspec
    (by simpa [lratBytesEnv_entry] using
      (lrat_bytes_module_fnspec k₀ hc hu (nm := "lrat_check_bytes") (by decide)).2)
    cnf cnf_ptr prf_ptr work_ptr (encodeDimacs cnf) prfBytes work_len
    (parseDimacs_encodeDimacs hvalid)
    hcnf hprf hwork s ra R hrdi hrsi hrdx hrcx hr8 hr9 hsp hmem

end Generic

/-! ## Concrete x64 executions in `compiled.host` (`rax = 1` and `rax = 0`) -/

abbrev lratBytesHost : Host := compiled.host
attribute [local instance] lratBytesHost

def lratBytesState (cnfBytes prfBytes : List UInt8) : MachineData :=
  initState (compiled.bound "lrat_check_bytes")
    (lratBytesPayload cnfBytes prfBytes) (lratBytesArgs cnfBytes prfBytes)

def lratBytesAcceptState0 : MachineData :=
  lratBytesState nvDimacsBytes nvLratAcceptBytes

/-- Concrete accepting execution of compiled `lrat_check_bytes` on Kraken x64. -/
theorem lrat_check_bytes_x64_accepts :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧ st.data.regs.get64 .rax = 1 ∧ nvBytesCnf.Unsat)
      ⟨lratBytesAcceptState0, Labels.label "lrat_check_bytes"⟩ :=
  lrat_check_bytes_accepts_witness targetInit compiled

def lratBytesRejectState0 : MachineData :=
  lratBytesState nvDimacsBytes nvLratRejectBytes

/-- Concrete rejecting execution of compiled `lrat_check_bytes` on Kraken x64. -/
theorem lrat_check_bytes_x64_rejects :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧ st.data.regs.get64 .rax = 0)
      ⟨lratBytesRejectState0, Labels.label "lrat_check_bytes"⟩ :=
  lrat_check_bytes_rejects_witness targetInit compiled

end LeanQbe.Amd64.LratBytes
