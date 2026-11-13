module

public import LeanQbe.Arm64.Abi
public import LeanQbe.Examples.LratBytesLemmas
import all Kraken.Separation
import all Kraken.Mem

/-!
# Untrusted-bytes LRAT proof checker (`lratBytesFns`) on AArch64

Instantiates the target-generic 6-function untrusted-bytes DIMACS + Binary LRAT checker module
`lratBytesFns` on `Arm64.target` via a single kernel evaluation (`compileChecked ... (by kernel_rfl)`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.Arm64.LratBytes

open Std.Sat LeanQbe LeanQbe.LratBytes Arm64 Kraken

-- The limit guards the cost of the compiler in the kernel: this check needs about 31,000
-- heartbeats (27 s). Heartbeats count allocations, so the limit holds on a busy machine too.
set_option maxHeartbeats 48000 in
/-- Single kernel evaluation of the compiler on `lratBytesFns` for AArch64. -/
def compiled : Compiled target [] [] 0 lratBytesFns :=
  compileChecked target targetLayout [] [] 0 lratBytesFns 2048 (by kernel_rfl)

section Generic
variable [hh : Host]

/-- Closed `FnSpec` for every function in `lratBytesFns` on `Arm64.target`. -/
theorem lrat_bytes_module_fnspec (k₀ : Nat)
    (hc : compiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {nm : String} (hnm : nm ∈ lratBytesFns.map Fn.name) :
    target.Defined hh nm ∧ target.FnSpec hh nm (lratBytesEnv nm) (compiled.bound nm) 0 :=
  lrat_bytes_fnSpec compiled hh k₀ hc hu hnm

/-- Lifting any `FnSpec` for `"lrat_check_bytes"` at stack bound `b` and contract
`lratCheckBytesSpec` to the closed Kraken-AArch64 statement. -/
theorem lrat_check_bytes_arm64_of_fnspec {b : Nat}
    (hfnspec : target.FnSpec hh "lrat_check_bytes" lratCheckBytesSpec b 0)
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
    (hra : s.regs.X30 = ra.toUInt64)
    (hsp : s.regs.SP.toNat % 16 = 0)
    (hmem : s.dmem =⋆
      (Eq (cnfBytes.At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆ region work_ptr work_len) ⋆
      (fun f => ∃ bs : List UInt8, bs.length = b ∧
          f = bs.At (s.regs.SP.toBitVec - BitVec.ofNat 64 b)) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        ((st.data.regs.getXReg .X0).toBitVec = 0 ∨ (st.data.regs.getXReg .X0).toBitVec = 1) ∧
        ((st.data.regs.getXReg .X0).toBitVec = 1 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
          st.data.regs.getXReg r = s.regs.getXReg r) ∧
        st.data.regs.SP = s.regs.SP ∧
        (st.data.dmem =⋆
          (Eq (cnfBytes.At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆ region work_ptr work_len) ⋆
          (fun f => ∃ bs : List UInt8, bs.length = b ∧
            f = bs.At (s.regs.SP.toBitVec - BitVec.ofNat 64 b)) ⋆ R))
      ⟨s, Labels.label "lrat_check_bytes"⟩ := by
  have hargs : target.ArgsIn
      [cnf_ptr, BitVec.ofNat 64 cnfBytes.length,
       prf_ptr, BitVec.ofNat 64 prfBytes.length,
       work_ptr, BitVec.ofNat 64 work_len] s := by
    simp [Target.ArgsIn, Target.ValsIn, argRegs, get_reg, hx0, hx1, hx2, hx3, hx4, hx5]
  refine eventually_weaken _ _ _ _ ?_
    (arm64_of_returns
      (lrat_check_bytes_of_fnspec hfnspec cnf_ptr prf_ptr work_ptr cnfBytes prfBytes work_len
        hcnf hprf hwork)
      s ra R hargs hra hsp hmem)
  rintro st ⟨hpc, hcs, hsp', rets, hrets,
    f1, f2, hu1, hd1, ⟨m', fe, hu2, hd2, ⟨r, rfl, hr01, hunsat, hP⟩, hexit⟩, hf2⟩
  have hx0' : (st.data.regs.getXReg .X0).toBitVec = r := by
    simpa [Target.RetsIn, Target.ValsIn, retRegs, get_reg] using hrets
  rw [← hx0'] at hr01 hunsat
  exact ⟨hpc, hr01, hunsat, hcs, hsp', f1, f2, hu1, hd1, ⟨m', fe, hu2, hd2, hP, hexit⟩, hf2⟩

/-- Trivial-postcondition lifting helper. -/
theorem lrat_check_bytes_arm64_unsat_of_fnspec {b : Nat}
    (hfnspec : target.FnSpec hh "lrat_check_bytes" lratCheckBytesSpec b 0)
    (cnf : CNF Nat) (cnf_ptr prf_ptr work_ptr : BitVec 64)
    (cnfBytes prfBytes : List UInt8) (work_len : Nat)
    (hparse : parseDimacs cnfBytes = some cnf)
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
    (hra : s.regs.X30 = ra.toUInt64)
    (hsp : s.regs.SP.toNat % 16 = 0)
    (hmem : s.dmem =⋆
      (Eq (cnfBytes.At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆ region work_ptr work_len) ⋆
      (fun f => ∃ bs : List UInt8, bs.length = b ∧
          f = bs.At (s.regs.SP.toBitVec - BitVec.ofNat 64 b)) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        ((st.data.regs.getXReg .X0).toBitVec = 0 ∨ (st.data.regs.getXReg .X0).toBitVec = 1) ∧
        ((st.data.regs.getXReg .X0).toBitVec = 1 → cnf.Unsat))
      ⟨s, Labels.label "lrat_check_bytes"⟩ := by
  refine eventually_weaken _ _ _ _ ?_
    (lrat_check_bytes_arm64_of_fnspec hfnspec cnf_ptr prf_ptr work_ptr cnfBytes prfBytes work_len
      hcnf hprf hwork s ra R hx0 hx1 hx2 hx3 hx4 hx5 hra hsp hmem)
  grind

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
    (hra : s.regs.X30 = ra.toUInt64)
    (hsp : s.regs.SP.toNat % 16 = 0)
    (hmem : s.dmem =⋆
      (Eq (cnfBytes.At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆ region work_ptr work_len) ⋆
      (fun f => ∃ bs : List UInt8, bs.length = compiled.bound "lrat_check_bytes" ∧
          f = bs.At (s.regs.SP.toBitVec - BitVec.ofNat 64 (compiled.bound "lrat_check_bytes"))) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        ((st.data.regs.getXReg .X0).toBitVec = 0 ∨ (st.data.regs.getXReg .X0).toBitVec = 1) ∧
        ((st.data.regs.getXReg .X0).toBitVec = 1 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
          st.data.regs.getXReg r = s.regs.getXReg r) ∧
        st.data.regs.SP = s.regs.SP ∧
        (st.data.dmem =⋆
          (Eq (cnfBytes.At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆ region work_ptr work_len) ⋆
          (fun f => ∃ bs : List UInt8, bs.length = compiled.bound "lrat_check_bytes" ∧
            f = bs.At (s.regs.SP.toBitVec - BitVec.ofNat 64 (compiled.bound "lrat_check_bytes"))) ⋆ R))
      ⟨s, Labels.label "lrat_check_bytes"⟩ :=
  lrat_check_bytes_arm64_of_fnspec
    (by simpa [lratBytesEnv_entry] using
      (lrat_bytes_module_fnspec k₀ hc hu (nm := "lrat_check_bytes") (by decide)).2)
    cnf_ptr prf_ptr work_ptr cnfBytes prfBytes work_len
    hcnf hprf hwork s ra R hx0 hx1 hx2 hx3 hx4 hx5 hra hsp hmem

/-- Trivial-postcondition headline corollary on Kraken-AArch64. -/
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
    (hra : s.regs.X30 = ra.toUInt64)
    (hsp : s.regs.SP.toNat % 16 = 0)
    (hmem : s.dmem =⋆
      (Eq ((encodeDimacs cnf).At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆ region work_ptr work_len) ⋆
      (fun f => ∃ bs : List UInt8, bs.length = compiled.bound "lrat_check_bytes" ∧
          f = bs.At (s.regs.SP.toBitVec - BitVec.ofNat 64 (compiled.bound "lrat_check_bytes"))) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        ((st.data.regs.getXReg .X0).toBitVec = 0 ∨ (st.data.regs.getXReg .X0).toBitVec = 1) ∧
        ((st.data.regs.getXReg .X0).toBitVec = 1 → cnf.Unsat))
      ⟨s, Labels.label "lrat_check_bytes"⟩ :=
  lrat_check_bytes_arm64_unsat_of_fnspec
    (by simpa [lratBytesEnv_entry] using
      (lrat_bytes_module_fnspec k₀ hc hu (nm := "lrat_check_bytes") (by decide)).2)
    cnf cnf_ptr prf_ptr work_ptr (encodeDimacs cnf) prfBytes work_len
    (parseDimacs_encodeDimacs hvalid)
    hcnf hprf hwork s ra R hx0 hx1 hx2 hx3 hx4 hx5 hra hsp hmem

end Generic

/-! ## Concrete AArch64 executions in `compiled.host` (`x0 = 1` and `x0 = 0`) -/

abbrev lratBytesHost : Host := compiled.host
attribute [local instance] lratBytesHost

def lratBytesState (cnfBytes prfBytes : List UInt8) : MachineData :=
  initState (compiled.bound "lrat_check_bytes")
    (lratBytesPayload cnfBytes prfBytes) (lratBytesArgs cnfBytes prfBytes)

/-- Concrete accepting execution of compiled `lrat_check_bytes` on Kraken AArch64. -/
theorem lrat_check_bytes_arm64_accepts :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧ (st.data.regs.getXReg .X0).toBitVec = 1 ∧ nvBytesCnf.Unsat)
      ⟨lratBytesState nvDimacsBytes nvLratAcceptBytes, Labels.label "lrat_check_bytes"⟩ :=
  lrat_check_bytes_accepts_witness targetInit compiled

/-- Concrete rejecting execution of compiled `lrat_check_bytes` on Kraken AArch64. -/
theorem lrat_check_bytes_arm64_rejects :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧ (st.data.regs.getXReg .X0).toBitVec = 0)
      ⟨lratBytesState nvDimacsBytes nvLratRejectBytes, Labels.label "lrat_check_bytes"⟩ :=
  lrat_check_bytes_rejects_witness targetInit compiled

end LeanQbe.Arm64.LratBytes
