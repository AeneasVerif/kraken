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
  obtain ⟨f_ab, f_rest, hu1, hd1, ⟨m, f_entry, hu2, hd2, hm_pre, hentry⟩, hrest⟩ := hmem
  let P_mem : Mem 64 → Prop :=
    Eq (cnfBytes.At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆ region work_ptr work_len
  let Q : LeanQbe.Post := fun rets m' =>
    ∃ r : Val, rets = [r] ∧ (r = 0 ∨ r = 1) ∧
      (r = 1 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
      (P_mem ⋆ Std.ExtHashMap.emp) m'
  let X : XPost := fun _ _ _ => False
  have hm_emp : (P_mem ⋆ Std.ExtHashMap.emp) m := by
    dsimp [P_mem]; rwa [Std.ExtHashMap.sep_emp]
  have hspec : lratCheckBytesSpec
      [cnf_ptr, BitVec.ofNat 64 cnfBytes.length,
       prf_ptr, BitVec.ofNat 64 prfBytes.length,
       work_ptr, BitVec.ofNat 64 work_len] m Q X :=
    ⟨cnf_ptr, prf_ptr, work_ptr, cnfBytes, prfBytes, work_len, Std.ExtHashMap.emp,
      rfl, hcnf, hprf, hwork, hm_emp,
      fun r m' hr01 hunsat hm' => ⟨r, rfl, hr01, hunsat, hm'⟩⟩
  have hargs : target.ArgsIn
      [cnf_ptr, BitVec.ofNat 64 cnfBytes.length,
       prf_ptr, BitVec.ofNat 64 prfBytes.length,
       work_ptr, BitVec.ofNat 64 work_len] s := by
    simp [Target.ArgsIn, Target.ValsIn, target, isa, hrdi, hrsi, hrdx, hrcx, hr8, hr9]
  have hsp' : target.spEntry (target.get s target.sp) := hsp
  have hmem' : target.mem s =⋆ Eq m ⋆ target.Entry (target.get s target.sp) ra b ⋆ R :=
    ⟨f_ab, f_rest, hu1, hd1, ⟨m, f_entry, hu2, hd2, rfl, hentry⟩, hrest⟩
  have hf := hfnspec
    [cnf_ptr, BitVec.ofNat 64 cnfBytes.length,
     prf_ptr, BitVec.ofNat 64 prfBytes.length,
     work_ptr, BitVec.ofNat 64 work_len] m Q X hspec s ra R hargs trivial hsp' hmem'
  refine eventually_weaken _ _ _ _ ?_ hf
  rintro st (⟨hpc, rets, m', ⟨r, rfl, hr01, hunsat, hm'⟩, hrets, ⟨hcs, hsp_out⟩, hdmem⟩ |
    ⟨_, _, _, hx, _⟩)
  · rw [Std.ExtHashMap.sep_emp] at hm'
    have hrax : st.data.regs.get64 .rax = r := by
      simpa [Target.RetsIn, Target.ValsIn, target, isa] using hrets
    rw [← hrax] at hr01 hunsat
    exact ⟨hpc, hr01, hunsat, fun reg hreg => hcs reg hreg, hsp_out,
      sep_mono (fun _ => sep_mono (fun _ e => e ▸ hm')) hdmem⟩
  · exact hx.elim

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
  rintro st ⟨hpc, hr01, hunsat, -⟩
  refine ⟨hpc, hr01, fun h1 => ?_⟩
  obtain ⟨cnf', hp', hu'⟩ := hunsat h1
  rw [hparse] at hp'
  injection hp' with h_eq
  exact h_eq ▸ hu'

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

/-! ## Concrete x64 executions in `compiled.host`: accepting (`rax = 1`) and rejecting (`rax = 0`) -/

abbrev lratBytesHost : Host := compiled.host
attribute [local instance] lratBytesHost

def lratBytesState (cnfBytes prfBytes : List UInt8) : MachineData :=
  { regs :=
      { rdi := (nvCnfPtr).toNat.toUInt64
        rsi := cnfBytes.length.toUInt64
        rdx := (nvPrfPtr cnfBytes).toNat.toUInt64
        rcx := prfBytes.length.toUInt64
        r8  := (nvWorkPtr cnfBytes prfBytes).toNat.toUInt64
        r9  := 512
        rsp := 0x0ff8 },
    dmem := initMem (compiled.bound "lrat_check_bytes") 0x1234
      (lratBytesPayload cnfBytes prfBytes) }

theorem lratBytesState_mem (cnfBytes prfBytes : List UInt8)
    (hcb : cnfBytes.length ≤ 1024) (hpb : prfBytes.length ≤ 1024) :
    (lratBytesState cnfBytes prfBytes).dmem =⋆
      (Eq (cnfBytes.At nvCnfPtr) ⋆
        Eq (prfBytes.At (nvPrfPtr cnfBytes)) ⋆
        region (nvWorkPtr cnfBytes prfBytes) 512) ⋆
      ((fun f => ∃ bs : List UInt8, bs.length = compiled.bound "lrat_check_bytes" ∧
          f = bs.At ((lratBytesState cnfBytes prfBytes).regs.get64 .rsp -
            BitVec.ofNat 64 (compiled.bound "lrat_check_bytes"))) ⋆
        Eq ((0x1234 : Int64).toUInt64.At ((lratBytesState cnfBytes prfBytes).regs.get64 .rsp))) ⋆
      Std.ExtHashMap.emp := by
  have hpay_len : (lratBytesPayload cnfBytes prfBytes).length ≤ 8192 := by
    rw [lratBytesPayload_length]; omega
  have h0 := initMem_entry (compiled.bound "lrat_check_bytes") 0x1234
    (lratBytesPayload cnfBytes prfBytes) (compiled.bound_le_max "lrat_check_bytes") hpay_len
  exact sep_mono (fun _ => sep_mono (fun _ e => e ▸
    lratBytesPayload_sep cnfBytes prfBytes (by omega) (by omega))) h0

private theorem lratBytesState_call {spec : Spec}
    (hfnspec : target.FnSpec lratBytesHost "lrat_check_bytes" spec
      (compiled.bound "lrat_check_bytes") 0)
    (cnfBytes prfBytes : List UInt8)
    (hcb : cnfBytes.length ≤ 1024) (hpb : prfBytes.length ≤ 1024)
    {Q : LeanQbe.Post}
    (hspec : ∀ m : Mem 64,
      ((Eq (cnfBytes.At nvCnfPtr) ⋆ Eq (prfBytes.At (nvPrfPtr cnfBytes)) ⋆
        region (nvWorkPtr cnfBytes prfBytes) 512) ⋆ Std.ExtHashMap.emp) m →
      spec
        [nvCnfPtr, BitVec.ofNat 64 cnfBytes.length,
         nvPrfPtr cnfBytes, BitVec.ofNat 64 prfBytes.length,
         nvWorkPtr cnfBytes prfBytes, 512#64] m Q (fun _ _ _ => False)) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = (0x1234 : Int64) ∧ ∃ rets m', Q rets m' ∧ target.RetsIn rets st.data)
      ⟨lratBytesState cnfBytes prfBytes, Labels.label "lrat_check_bytes"⟩ := by
  let s0 := lratBytesState cnfBytes prfBytes
  obtain ⟨f_ab, f_rest, hu1, hd1, ⟨m, f_entry, hu2, hd2, hm_pre, hentry⟩, hrest⟩ :=
    lratBytesState_mem cnfBytes prfBytes hcb hpb
  have hm_emp : ((Eq (cnfBytes.At nvCnfPtr) ⋆ Eq (prfBytes.At (nvPrfPtr cnfBytes)) ⋆
      region (nvWorkPtr cnfBytes prfBytes) 512) ⋆ Std.ExtHashMap.emp) m := by
    rwa [Std.ExtHashMap.sep_emp]
  have hrdi : s0.regs.get64 .rdi = nvCnfPtr := rfl
  have hrsi : s0.regs.get64 .rsi = BitVec.ofNat 64 cnfBytes.length := rfl
  have hrdx : s0.regs.get64 .rdx = nvPrfPtr cnfBytes :=
    BitVec.eq_of_toNat_eq (by
      change (BitVec.ofNat 64 (nvPrfPtr cnfBytes).toNat).toNat = (nvPrfPtr cnfBytes).toNat
      simp)
  have hrcx : s0.regs.get64 .rcx = BitVec.ofNat 64 prfBytes.length := rfl
  have hr8 : s0.regs.get64 .r8 = nvWorkPtr cnfBytes prfBytes :=
    BitVec.eq_of_toNat_eq (by
      change (BitVec.ofNat 64 (nvWorkPtr cnfBytes prfBytes).toNat).toNat =
        (nvWorkPtr cnfBytes prfBytes).toNat
      simp)
  have hr9 : s0.regs.get64 .r9 = 512#64 := rfl
  have hargs : target.ArgsIn
      [nvCnfPtr, BitVec.ofNat 64 cnfBytes.length,
       nvPrfPtr cnfBytes, BitVec.ofNat 64 prfBytes.length,
       nvWorkPtr cnfBytes prfBytes, 512#64] s0 := by
    simp [Target.ArgsIn, Target.ValsIn, target, isa, hrdi, hrsi, hrdx, hrcx, hr8, hr9]
  have hsp : target.spEntry (target.get s0 target.sp) :=
    show (0x0ff8#64 + 8#64).toNat % 16 = 0 by decide
  have hmem' : target.mem s0 =⋆ Eq m ⋆
      target.Entry (target.get s0 target.sp) (0x1234 : Int64)
        (compiled.bound "lrat_check_bytes") ⋆ Std.ExtHashMap.emp :=
    ⟨f_ab, f_rest, hu1, hd1, ⟨m, f_entry, hu2, hd2, rfl, hentry⟩, hrest⟩
  refine eventually_weaken _ _ _ _ ?_
    (hfnspec _ m Q (fun _ _ _ => False) (hspec m hm_emp) s0 0x1234 Std.ExtHashMap.emp
      hargs trivial hsp hmem')
  rintro st (⟨hpc, rets, m', hQ, hrets, -⟩ | ⟨_, _, _, hx, _⟩)
  · exact ⟨hpc, rets, m', hQ, hrets⟩
  · exact hx.elim

def lratBytesAcceptState0 : MachineData :=
  lratBytesState nvDimacsBytes nvLratAcceptBytes

/-- Concrete accepting execution of compiled `lrat_check_bytes` on Kraken x64. -/
theorem lrat_check_bytes_x64_accepts :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧ st.data.regs.get64 .rax = 1 ∧ nvBytesCnf.Unsat)
      ⟨lratBytesAcceptState0, Labels.label "lrat_check_bytes"⟩ := by
  have hf := lratBytesState_call (Q := fun rs _ => rs = [1] ∧ nvBytesCnf.Unsat)
    (lrat_bytes_accepts_fnSpec compiled) nvDimacsBytes nvLratAcceptBytes (by simp) (by simp)
    lratCheckBytesAcceptSpec_nv
  refine eventually_weaken _ _ _ _ ?_ hf
  rintro st ⟨hpc, _, _, ⟨rfl, hu⟩, hrets⟩
  have hrax : st.data.regs.get64 .rax = 1 := by
    simpa [Target.RetsIn, Target.ValsIn, target, isa] using hrets
  exact ⟨hpc, hrax, hu⟩

def lratBytesRejectState0 : MachineData :=
  lratBytesState nvDimacsBytes nvLratRejectBytes

/-- Concrete rejecting execution of compiled `lrat_check_bytes` on Kraken x64. -/
theorem lrat_check_bytes_x64_rejects :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧ st.data.regs.get64 .rax = 0)
      ⟨lratBytesRejectState0, Labels.label "lrat_check_bytes"⟩ := by
  have hf := lratBytesState_call (Q := fun rs _ => rs = [0])
    (lrat_bytes_rejects_fnSpec compiled) nvDimacsBytes nvLratRejectBytes (by simp) (by simp)
    lratCheckBytesRejectSpec_nv
  refine eventually_weaken _ _ _ _ ?_ hf
  rintro st ⟨hpc, _, _, rfl, hrets⟩
  have hrax : st.data.regs.get64 .rax = 0 := by
    simpa [Target.RetsIn, Target.ValsIn, target, isa] using hrets
  exact ⟨hpc, hrax⟩

end LeanQbe.Amd64.LratBytes
