module

public import LeanQbe.Examples.LitmusLratBytesCode
public import LeanQbe.Examples.LratBytesLemmas
import all Kraken.Separation
import all Kraken.Mem

/-!
# Untrusted-bytes LRAT proof checker end to end on x64 (`lrat_check_bytes`)

Links `LratBytes.lratBytesFns` on `Amd64.fastTarget` via `compile_sound` using the kernel-checked
`lrat_bytes_module_compile` from `LitmusLratBytesCode.lean` and the total-correctness proofs from
`LratBytesLemmas.lean`, proving:
1. `lrat_bytes_module_fnspec`: `FnSpec` for all six functions in `lratBytesFns`.
2. `lrat_check_bytes_x64_correct`: closed Kraken-x64 ABI-preserving correctness theorem on
   arbitrary untrusted byte buffers (`cnfBytes`, `prfBytes`, `region work_ptr work_len`).
3. `lrat_check_bytes_x64_unsat`: trivial-postcondition Kraken-x64 theorem on `(encodeDimacs cnf)`:
   `st.pc = ra ∧ (rax = 0 ∨ rax = 1) ∧ (rax = 1 → cnf.Unsat)` with no parser in the conclusion.
4. `lrat_check_bytes_x64_accepts` and `lrat_check_bytes_x64_rejects`: concrete machine-level
   accepting (`rax = 1 ∧ nvBytesCnf.Unsat`) and rejecting (`rax = 0`) executions in `lratBytesHost`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.Litmus

open Std.Sat LeanQbe LeanQbe.LratBytes Rega Amd64 Kraken Kraken.X64

section Generic
variable [hh : Host]

/-- Generic linking helper for `lratBytesFns` on `Amd64.fastTarget` via `compile_sound`. -/
theorem lrat_bytes_module_fnspec_of (Γ : Env) (k₀ : Nat)
    (hc : lratBytesCode.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (hwf : ∀ f ∈ lratBytesFns, Func.Wf f.body)
    (hsound : ∀ f ∈ lratBytesFns, ∀ args m Q X, Γ f.name args m Q X → Func.spec Γ f.body args m Q X) :
    ∀ p ∈ lratBytesBounds,
      Amd64.fastTarget.Defined hh p.1 ∧
        Amd64.fastTarget.FnSpec hh p.1 (Γ p.1) p.2 0 :=
  compile_sound (T := Amd64.fastTarget) hh Γ [] [] 0 lratBytesFns
    lratBytesCode lratBytesBounds k₀ lrat_bytes_module_compile hc hu hwf hsound
    (fun _ h => nomatch h) (fun _ h => nomatch h)

/-- Lifting any `FnSpec` for `"lrat_check_bytes"` at stack bound `968` and contract
`lratCheckBytesSpec` to the closed Kraken-x64 statement. -/
theorem lrat_check_bytes_x64_of_fnspec
    (hfnspec : Amd64.fastTarget.FnSpec hh "lrat_check_bytes" lratCheckBytesSpec 968 0)
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
      ((fun f => ∃ bs : List UInt8, bs.length = 968 ∧ f = bs.At (s.regs.get64 .rsp - 968#64)) ⋆
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
          (fun f => ∃ bs : List UInt8, bs.length = 976 ∧ f = bs.At (s.regs.get64 .rsp - 968#64)) ⋆ R))
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
  have hargs : Amd64.fastTarget.ArgsIn
      [cnf_ptr, BitVec.ofNat 64 cnfBytes.length,
       prf_ptr, BitVec.ofNat 64 prfBytes.length,
       work_ptr, BitVec.ofNat 64 work_len] s := by
    simp [Target.ArgsIn, Target.ValsIn, Amd64.fastTarget, Amd64.target, Amd64.fastIsa, Amd64.isa,
      hrdi, hrsi, hrdx, hrcx, hr8, hr9]
  have hsp' : Amd64.fastTarget.spEntry (Amd64.fastTarget.get s Amd64.fastTarget.sp) := hsp
  have hmem' : Amd64.fastTarget.mem s =⋆ Eq m ⋆
      Amd64.fastTarget.Entry (Amd64.fastTarget.get s Amd64.fastTarget.sp) ra 968 ⋆ R :=
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
      simpa [Target.RetsIn, Target.ValsIn, Amd64.fastTarget, Amd64.target, Amd64.fastIsa, Amd64.isa]
        using hrets
    rw [← hrax] at hr01 hunsat
    exact ⟨hpc, hr01, hunsat, fun reg hreg => hcs reg hreg, hsp_out,
      sep_mono (fun _ => sep_mono (fun _ e => e ▸ hm')) hdmem⟩
  · exact hx.elim

/-- Trivial-postcondition lifting helper: given any `cnfBytes` whose parse is `some cnf`
(e.g. `encodeDimacs cnf` via `parseDimacs_encodeDimacs`), `lrat_check_bytes` returns to `ra`
with `rax ∈ {0, 1}` and `rax = 1 → cnf.Unsat`. -/
theorem lrat_check_bytes_x64_unsat_of_fnspec
    (hfnspec : Amd64.fastTarget.FnSpec hh "lrat_check_bytes" lratCheckBytesSpec 968 0)
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
      ((fun f => ∃ bs : List UInt8, bs.length = 968 ∧ f = bs.At (s.regs.get64 .rsp - 968#64)) ⋆
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

/-! ## Closed module `FnSpec` and Kraken-x64 end-to-end theorems -/

/-- Linking all six functions of `lratBytesFns` on `Amd64.fastTarget` via `compile_sound`:
every `(name, bound)` in `lratBytesBounds` satisfies `Amd64.fastTarget.FnSpec` against
`lratBytesEnv` in any `Host` containing `lratBytesCode` with unique labels. -/
theorem lrat_bytes_module_fnspec (k₀ : Nat)
    (hc : lratBytesCode.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique) :
    ∀ p ∈ lratBytesBounds,
      Amd64.fastTarget.Defined hh p.1 ∧
        Amd64.fastTarget.FnSpec hh p.1 (lratBytesEnv p.1) p.2 0 :=
  lrat_bytes_module_fnspec_of lratBytesEnv k₀ hc hu lratBytesFns_wf lratBytesEnv_sound

/-- Closed end-to-end correctness of compiled `lrat_check_bytes` on Kraken x64:
starting at `Labels.label "lrat_check_bytes"` with arbitrary untrusted byte slices `cnfBytes`,
`prfBytes`, and uninitialized scratch `region work_ptr work_len` (6 register arguments,
`968`-byte stack bound, 16-byte entry alignment), the machine eventually returns to `ra` with
`rax ∈ {0, 1}`, `rax = 1 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat`, callee-saved
registers and `rsp` restored, and memory framed. -/
theorem lrat_check_bytes_x64_correct
    (k₀ : Nat) (hc : lratBytesCode.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
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
      ((fun f => ∃ bs : List UInt8, bs.length = 968 ∧ f = bs.At (s.regs.get64 .rsp - 968#64)) ⋆
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
          (fun f => ∃ bs : List UInt8, bs.length = 976 ∧ f = bs.At (s.regs.get64 .rsp - 968#64)) ⋆ R))
      ⟨s, Labels.label "lrat_check_bytes"⟩ :=
  lrat_check_bytes_x64_of_fnspec
    (lrat_bytes_module_fnspec k₀ hc hu ("lrat_check_bytes", 968) (by simp [lratBytesBounds])).2
    cnf_ptr prf_ptr work_ptr cnfBytes prfBytes work_len
    hcnf hprf hwork s ra R hrdi hrsi hrdx hrcx hr8 hr9 hsp hmem

/-- Trivial-postcondition end-to-end Kraken-x64 corollary for any `cnf : CNF Nat` satisfying
`ValidDimacsCnf cnf`: when `cnf` is serialized via `encodeDimacs cnf` at `cnf_ptr` alongside
arbitrary untrusted proof bytes `prfBytes` and uninitialized scratch `region work_ptr work_len`,
compiled `lrat_check_bytes` returns to `ra` with `rax ∈ {0, 1}` and `rax = 1 → cnf.Unsat`
(no parser appears in the postcondition). -/
theorem lrat_check_bytes_x64_unsat
    (k₀ : Nat) (hc : lratBytesCode.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
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
      ((fun f => ∃ bs : List UInt8, bs.length = 968 ∧ f = bs.At (s.regs.get64 .rsp - 968#64)) ⋆
        Eq (ra.toUInt64.At (s.regs.get64 .rsp))) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        (st.data.regs.get64 .rax = 0 ∨ st.data.regs.get64 .rax = 1) ∧
        (st.data.regs.get64 .rax = 1 → cnf.Unsat))
      ⟨s, Labels.label "lrat_check_bytes"⟩ :=
  lrat_check_bytes_x64_unsat_of_fnspec
    (lrat_bytes_module_fnspec k₀ hc hu ("lrat_check_bytes", 968) (by simp [lratBytesBounds])).2
    cnf cnf_ptr prf_ptr work_ptr (encodeDimacs cnf) prfBytes work_len
    (parseDimacs_encodeDimacs hvalid)
    hcnf hprf hwork s ra R hrdi hrsi hrdx hrcx hr8 hr9 hsp hmem

/-- Specialized accepting `FnSpec` for `(nvDimacsBytes, nvLratAcceptBytes, 512)`. -/
theorem lrat_bytes_accepts_fnspec (k₀ : Nat)
    (hc : lratBytesCode.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique) :
    ∀ p ∈ lratBytesBounds,
      Amd64.fastTarget.Defined hh p.1 ∧
        Amd64.fastTarget.FnSpec hh p.1 (lratBytesAcceptEnv p.1) p.2 0 :=
  lrat_bytes_module_fnspec_of lratBytesAcceptEnv k₀ hc hu lratBytesFns_wf lratBytesAcceptEnv_sound

/-- Specialized rejecting `FnSpec` for `(nvDimacsBytes, nvLratRejectBytes, 512)`. -/
theorem lrat_bytes_rejects_fnspec (k₀ : Nat)
    (hc : lratBytesCode.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique) :
    ∀ p ∈ lratBytesBounds,
      Amd64.fastTarget.Defined hh p.1 ∧
        Amd64.fastTarget.FnSpec hh p.1 (lratBytesRejectEnv p.1) p.2 0 :=
  lrat_bytes_module_fnspec_of lratBytesRejectEnv k₀ hc hu lratBytesFns_wf lratBytesRejectEnv_sound

end Generic

/-! ## Concrete x64 executions in `lratBytesHost`: accepting (`rax = 1`) and rejecting (`rax = 0`) -/

attribute [local instance] lratBytesHost

def zeros968 : List UInt8 := List.replicate 968 0
def zeros512 : List UInt8 := List.replicate 512 0

abbrev nvCnfPtr : BitVec 64 := 0x1000#64
abbrev nvPrfPtr (cnfBytes : List UInt8) : BitVec 64 :=
  nvCnfPtr + BitVec.ofNat 64 cnfBytes.length
abbrev nvWorkPtr (cnfBytes prfBytes : List UInt8) : BitVec 64 :=
  nvPrfPtr cnfBytes + BitVec.ofNat 64 prfBytes.length

def lratBytesState (cnfBytes prfBytes : List UInt8) : MachineData :=
  { regs :=
      { rdi := (nvCnfPtr).toNat.toUInt64
        rsi := cnfBytes.length.toUInt64
        rdx := (nvPrfPtr cnfBytes).toNat.toUInt64
        rcx := prfBytes.length.toUInt64
        r8  := (nvWorkPtr cnfBytes prfBytes).toNat.toUInt64
        r9  := 512
        rsp := 0x0ff8 },
    dmem := ((zeros968 ++ raBytes0) ++ ((cnfBytes ++ prfBytes) ++ zeros512)).At 0x0c30#64 }

theorem lratBytesState_mem (cnfBytes prfBytes : List UInt8)
    (hcb : cnfBytes.length ≤ 4096) (hpb : prfBytes.length ≤ 4096) :
    (lratBytesState cnfBytes prfBytes).dmem =⋆
      (Eq (cnfBytes.At nvCnfPtr) ⋆
        Eq (prfBytes.At (nvPrfPtr cnfBytes)) ⋆
        region (nvWorkPtr cnfBytes prfBytes) 512) ⋆
      ((fun f => ∃ bs : List UInt8, bs.length = 968 ∧
          f = bs.At ((lratBytesState cnfBytes prfBytes).regs.get64 .rsp - 968#64)) ⋆
        Eq ((0x1234 : Int64).toUInt64.At ((lratBytesState cnfBytes prfBytes).regs.get64 .rsp))) ⋆
      Std.ExtHashMap.emp := by
  have hra : raBytes0.length = 8 := UInt64.toBytes_length _
  have h968 : zeros968.length = 968 := List.length_replicate
  have h512 : zeros512.length = 512 := List.length_replicate
  have hsp_eq : (lratBytesState cnfBytes prfBytes).regs.get64 .rsp = 0x0ff8#64 := rfl
  have hsp_sub : (lratBytesState cnfBytes prfBytes).regs.get64 .rsp - 968#64 = 0x0c30#64 := by
    rw [hsp_eq]; decide
  rw [hsp_sub, hsp_eq, Std.ExtHashMap.sep_emp]
  have h1 := Mem.At_append_sep (zeros968 ++ raBytes0) ((cnfBytes ++ prfBytes) ++ zeros512) 0x0c30#64
    (by simp only [List.length_append, h968, hra, h512]; omega)
  have e1 : 0x0c30#64 + BitVec.ofNat 64 (zeros968 ++ raBytes0).length = nvCnfPtr := by
    simp [nvCnfPtr, h968, hra]
  rw [e1] at h1
  have h2 := Mem.At_append_sep (cnfBytes ++ prfBytes) zeros512 nvCnfPtr
    (by simp only [List.length_append, h512]; omega)
  have e2 : nvCnfPtr + BitVec.ofNat 64 (cnfBytes ++ prfBytes).length = nvWorkPtr cnfBytes prfBytes := by
    simp only [nvWorkPtr, nvPrfPtr, nvCnfPtr, List.length_append]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  rw [e2] at h2
  have h3 := Mem.At_append_sep cnfBytes prfBytes nvCnfPtr (by omega)
  have h4 := Mem.At_append_sep zeros968 raBytes0 0x0c30#64
    (by simp only [h968, hra]; omega)
  have e4 : 0x0c30#64 + BitVec.ofNat 64 zeros968.length = 0x0ff8#64 := by simp [h968]
  rw [e4] at h4
  have h0 : (Eq (((zeros968 ++ raBytes0) ++ ((cnfBytes ++ prfBytes) ++ zeros512)).At 0x0c30#64))
      (lratBytesState cnfBytes prfBytes).dmem := rfl
  rw [h1, Std.ExtHashMap.sep_comm] at h0
  refine sep_mono (fun fL hfL => ?_) (sep_mono_r (fun fR hfR => ?_) h0)
  · rw [h2] at hfL
    exact sep_mono (fun fC hfC => by rwa [h3] at hfC)
      (sep_mono_r (fun fW hfW => ⟨zeros512, h512, hfW.symm⟩) hfL)
  · rw [h4] at hfR
    exact sep_mono (fun fS hfS => ⟨zeros968, h968, hfS.symm⟩) hfR

/-- Initial x64 state for the concrete accepting witness `(nvDimacsBytes, nvLratAcceptBytes, 512)`. -/
def lratBytesAcceptState0 : MachineData :=
  lratBytesState nvDimacsBytes nvLratAcceptBytes

/-- Concrete accepting execution of compiled `lrat_check_bytes` on Kraken x64: on the 19-byte
ASCII DIMACS formula `nvDimacsBytes` (`(x₁) ∧ (¬x₁)`) and 15-byte 3-step Binary LRAT proof
`nvLratAcceptBytes` (exercising `'a'`, `'d'`, and empty-clause derivation) with a 512-byte scratch
region, execution in `lratBytesHost` from `Labels.label "lrat_check_bytes"` returns to `0x1234`
with `rax = 1` and establishes `nvBytesCnf.Unsat`. -/
theorem lrat_check_bytes_x64_accepts :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧ st.data.regs.get64 .rax = 1 ∧ nvBytesCnf.Unsat)
      ⟨lratBytesAcceptState0, Labels.label "lrat_check_bytes"⟩ := by
  have hmem := lratBytesState_mem nvDimacsBytes nvLratAcceptBytes (by simp) (by simp)
  obtain ⟨f_ab, f_rest, hu1, hd1, ⟨m, f_entry, hu2, hd2, hm_pre, hentry⟩, hrest⟩ := hmem
  let cnf_ptr : BitVec 64 := nvCnfPtr
  let prf_ptr : BitVec 64 := nvPrfPtr nvDimacsBytes
  let work_ptr : BitVec 64 := nvWorkPtr nvDimacsBytes nvLratAcceptBytes
  let P_mem : Mem 64 → Prop :=
    Eq (nvDimacsBytes.At cnf_ptr) ⋆ Eq (nvLratAcceptBytes.At prf_ptr) ⋆ region work_ptr 512
  have hm_emp : (P_mem ⋆ Std.ExtHashMap.emp) m := by
    dsimp [P_mem, cnf_ptr, prf_ptr, work_ptr]; rwa [Std.ExtHashMap.sep_emp]
  have hc : lratBytesCode.IsInfixAt Host.prog 0 := ⟨[], by simp [lratBytesHost_prog]⟩
  have hspec : lratBytesAcceptEnv ("lrat_check_bytes", 968).1
      [cnf_ptr, BitVec.ofNat 64 nvDimacsBytes.length,
       prf_ptr, BitVec.ofNat 64 nvLratAcceptBytes.length,
       work_ptr, 512#64]
      m (fun rs _ => rs = [1] ∧ nvBytesCnf.Unsat) (fun _ _ _ => False) := by
    refine ⟨cnf_ptr, prf_ptr, work_ptr, Std.ExtHashMap.emp, rfl, ?_, ?_, ?_, hm_emp,
      fun _ hunsat _ => ⟨rfl, hunsat⟩⟩
    · simp [cnf_ptr, nvCnfPtr]
    · simp [prf_ptr, nvPrfPtr, nvCnfPtr]
    · simp [work_ptr, nvWorkPtr, nvPrfPtr, nvCnfPtr]
  have hrdi : lratBytesAcceptState0.regs.get64 .rdi = cnf_ptr := rfl
  have hrsi : lratBytesAcceptState0.regs.get64 .rsi = BitVec.ofNat 64 nvDimacsBytes.length := by
    simp [lratBytesAcceptState0, lratBytesState]; rfl
  have hrdx : lratBytesAcceptState0.regs.get64 .rdx = prf_ptr := by
    simp [prf_ptr, lratBytesAcceptState0, lratBytesState, nvPrfPtr, nvCnfPtr]; rfl
  have hrcx : lratBytesAcceptState0.regs.get64 .rcx = BitVec.ofNat 64 nvLratAcceptBytes.length := by
    simp [lratBytesAcceptState0, lratBytesState]; rfl
  have hr8 : lratBytesAcceptState0.regs.get64 .r8 = work_ptr := by
    simp [work_ptr, lratBytesAcceptState0, lratBytesState, nvWorkPtr, nvPrfPtr, nvCnfPtr]; rfl
  have hr9 : lratBytesAcceptState0.regs.get64 .r9 = 512#64 := rfl
  have hargs : Amd64.fastTarget.ArgsIn
      [cnf_ptr, BitVec.ofNat 64 nvDimacsBytes.length,
       prf_ptr, BitVec.ofNat 64 nvLratAcceptBytes.length,
       work_ptr, 512#64] lratBytesAcceptState0 := by
    simp [Target.ArgsIn, Target.ValsIn, Amd64.fastTarget, Amd64.target, Amd64.fastIsa, Amd64.isa,
      hrdi, hrsi, hrdx, hrcx, hr8, hr9]
  have hsp : Amd64.fastTarget.spEntry
      (Amd64.fastTarget.get lratBytesAcceptState0 Amd64.fastTarget.sp) :=
    show (0x0ff8#64 + 8#64).toNat % 16 = 0 by decide
  have hmem' : Amd64.fastTarget.mem lratBytesAcceptState0 =⋆ Eq m ⋆
      Amd64.fastTarget.Entry (Amd64.fastTarget.get lratBytesAcceptState0 Amd64.fastTarget.sp)
        (0x1234 : Int64) 968 ⋆ Std.ExtHashMap.emp :=
    ⟨f_ab, f_rest, hu1, hd1, ⟨m, f_entry, hu2, hd2, rfl, hentry⟩, hrest⟩
  have hf := (lrat_bytes_accepts_fnspec 0 hc lratBytesHost_unique
      ("lrat_check_bytes", 968) (by simp [lratBytesBounds])).2
    [cnf_ptr, BitVec.ofNat 64 nvDimacsBytes.length,
     prf_ptr, BitVec.ofNat 64 nvLratAcceptBytes.length,
     work_ptr, 512#64] m _ _ hspec
    lratBytesAcceptState0 (0x1234 : Int64) Std.ExtHashMap.emp hargs trivial hsp hmem'
  refine eventually_weaken _ _ _ _ ?_ hf
  rintro st (⟨hpc, rets, _, ⟨rfl, hunsat⟩, hrets, -⟩ | ⟨_, _, _, hx, _⟩)
  · have hrax : st.data.regs.get64 .rax = 1 := by
      simpa [Target.RetsIn, Target.ValsIn, Amd64.fastTarget, Amd64.target, Amd64.fastIsa, Amd64.isa]
        using hrets
    exact ⟨hpc, hrax, hunsat⟩
  · exact hx.elim

/-- Initial x64 state for the concrete rejecting witness `(nvDimacsBytes, nvLratRejectBytes, 512)`. -/
def lratBytesRejectState0 : MachineData :=
  lratBytesState nvDimacsBytes nvLratRejectBytes

/-- Concrete rejecting execution of compiled `lrat_check_bytes` on Kraken x64: on `nvDimacsBytes`
and the invalid 5-byte Binary LRAT proof `nvLratRejectBytes` (non-conflict RUP attempt) with a
512-byte scratch region, execution in `lratBytesHost` from `Labels.label "lrat_check_bytes"`
returns cleanly to `0x1234` with `rax = 0`. -/
theorem lrat_check_bytes_x64_rejects :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧ st.data.regs.get64 .rax = 0)
      ⟨lratBytesRejectState0, Labels.label "lrat_check_bytes"⟩ := by
  have hmem := lratBytesState_mem nvDimacsBytes nvLratRejectBytes (by simp) (by simp)
  obtain ⟨f_ab, f_rest, hu1, hd1, ⟨m, f_entry, hu2, hd2, hm_pre, hentry⟩, hrest⟩ := hmem
  let cnf_ptr : BitVec 64 := nvCnfPtr
  let prf_ptr : BitVec 64 := nvPrfPtr nvDimacsBytes
  let work_ptr : BitVec 64 := nvWorkPtr nvDimacsBytes nvLratRejectBytes
  let P_mem : Mem 64 → Prop :=
    Eq (nvDimacsBytes.At cnf_ptr) ⋆ Eq (nvLratRejectBytes.At prf_ptr) ⋆ region work_ptr 512
  have hm_emp : (P_mem ⋆ Std.ExtHashMap.emp) m := by
    dsimp [P_mem, cnf_ptr, prf_ptr, work_ptr]; rwa [Std.ExtHashMap.sep_emp]
  have hc : lratBytesCode.IsInfixAt Host.prog 0 := ⟨[], by simp [lratBytesHost_prog]⟩
  have hspec : lratBytesRejectEnv ("lrat_check_bytes", 968).1
      [cnf_ptr, BitVec.ofNat 64 nvDimacsBytes.length,
       prf_ptr, BitVec.ofNat 64 nvLratRejectBytes.length,
       work_ptr, 512#64]
      m (fun rs _ => rs = [0]) (fun _ _ _ => False) := by
    refine ⟨cnf_ptr, prf_ptr, work_ptr, Std.ExtHashMap.emp, rfl, ?_, ?_, ?_, hm_emp,
      fun _ _ => rfl⟩
    · simp [cnf_ptr, nvCnfPtr]
    · simp [prf_ptr, nvPrfPtr, nvCnfPtr]
    · simp [work_ptr, nvWorkPtr, nvPrfPtr, nvCnfPtr]
  have hrdi : lratBytesRejectState0.regs.get64 .rdi = cnf_ptr := rfl
  have hrsi : lratBytesRejectState0.regs.get64 .rsi = BitVec.ofNat 64 nvDimacsBytes.length := by
    simp [lratBytesRejectState0, lratBytesState]; rfl
  have hrdx : lratBytesRejectState0.regs.get64 .rdx = prf_ptr := by
    simp [prf_ptr, lratBytesRejectState0, lratBytesState, nvPrfPtr, nvCnfPtr]; rfl
  have hrcx : lratBytesRejectState0.regs.get64 .rcx = BitVec.ofNat 64 nvLratRejectBytes.length := by
    simp [lratBytesRejectState0, lratBytesState]; rfl
  have hr8 : lratBytesRejectState0.regs.get64 .r8 = work_ptr := by
    simp [work_ptr, lratBytesRejectState0, lratBytesState, nvWorkPtr, nvPrfPtr, nvCnfPtr]; rfl
  have hr9 : lratBytesRejectState0.regs.get64 .r9 = 512#64 := rfl
  have hargs : Amd64.fastTarget.ArgsIn
      [cnf_ptr, BitVec.ofNat 64 nvDimacsBytes.length,
       prf_ptr, BitVec.ofNat 64 nvLratRejectBytes.length,
       work_ptr, 512#64] lratBytesRejectState0 := by
    simp [Target.ArgsIn, Target.ValsIn, Amd64.fastTarget, Amd64.target, Amd64.fastIsa, Amd64.isa,
      hrdi, hrsi, hrdx, hrcx, hr8, hr9]
  have hsp : Amd64.fastTarget.spEntry
      (Amd64.fastTarget.get lratBytesRejectState0 Amd64.fastTarget.sp) :=
    show (0x0ff8#64 + 8#64).toNat % 16 = 0 by decide
  have hmem' : Amd64.fastTarget.mem lratBytesRejectState0 =⋆ Eq m ⋆
      Amd64.fastTarget.Entry (Amd64.fastTarget.get lratBytesRejectState0 Amd64.fastTarget.sp)
        (0x1234 : Int64) 968 ⋆ Std.ExtHashMap.emp :=
    ⟨f_ab, f_rest, hu1, hd1, ⟨m, f_entry, hu2, hd2, rfl, hentry⟩, hrest⟩
  have hf := (lrat_bytes_rejects_fnspec 0 hc lratBytesHost_unique
      ("lrat_check_bytes", 968) (by simp [lratBytesBounds])).2
    [cnf_ptr, BitVec.ofNat 64 nvDimacsBytes.length,
     prf_ptr, BitVec.ofNat 64 nvLratRejectBytes.length,
     work_ptr, 512#64] m _ _ hspec
    lratBytesRejectState0 (0x1234 : Int64) Std.ExtHashMap.emp hargs trivial hsp hmem'
  refine eventually_weaken _ _ _ _ ?_ hf
  rintro st (⟨hpc, rets, _, rfl, hrets, -⟩ | ⟨_, _, _, hx, _⟩)
  · have hrax : st.data.regs.get64 .rax = 0 := by
      simpa [Target.RetsIn, Target.ValsIn, Amd64.fastTarget, Amd64.target, Amd64.fastIsa, Amd64.isa]
        using hrets
    exact ⟨hpc, hrax⟩
  · exact hx.elim

end LeanQbe.Litmus
