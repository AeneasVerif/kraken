module

public import LeanQbe.RegaLemmas
public import LeanQbe.Examples.LitmusCf
public import LeanQbe.Examples.LitmusProgsLemmas
public import LeanQbe.Amd64.TargLemmas
public import Kraken.X64.Parser
public import LeanQbe.WPLemmas
public import LeanQbe.MainLemmas
public import LeanQbe.Examples.Litmus
public import LeanQbe.Examples.LitmusUf
import all Kraken.Separation
import all Kraken.Mem

/-!
# Control-flow and R3 litmus programs: kernel evaluation and instantiated theorems

For each program of `LitmusProgs.lean`: the code `lower` / `compileFn` produces with the oracle's
hints, written as assembly and parsed by Kraken (`…Code`), checked in the kernel (`rfl` /
`kernel_rfl`); `Func.Wf` by `wf_tac`; and `lowerFn_correct` / `compileFn_correct` /
`compile_correct` instantiated in every x64 host containing the code, plus Kraken-only end-to-end
theorems and concrete non-vacuity instances.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.Litmus

open Rega Amd64

def ifelseCode : Program := parse("ifelse:
  subq $8, %rsp
  testl %edi, %edi
  jne ifelse.L0
  movq %rsi, %r11
  movq %rdi, %r10
  subq %r10, %r11
  movq %r11, %rsi
  movq %rsi, %rax
  addq $8, %rsp
  ret
  ifelse.L0:
  movq %rdi, %r11
  movq %rsi, %r10
  addq %r10, %r11
  movq %r11, %rdi
  movq %rdi, %rax
  addq $8, %rsp
  ret")

theorem ifelse_lower : lowerFn (Spill.hints Amd64.isa ifelse) ⟨[], []⟩ ifelse = .ok ifelseCode := by kernel_rfl

theorem ifelse_fnspec [hh : Host] (k₀ : Nat) (hc : ifelseCode.IsInfixAt Host.prog k₀)
    (hu : Host.LabelsUnique) (Γ : Env) (nX : Nat) :
    Amd64.target.FnSpec hh "ifelse" (Func.spec Γ ifelse.body) 8 nX :=
  lowerFn_correct (T := Amd64.target) hh _ ⟨[], []⟩ ifelse Γ (fun _ => 0) 8 nX ifelseCode k₀
    ifelse_lower hc hu ifelse_wf (of_decide_eq_true (by kernel_rfl)) (by decide)
    (fun _ h => nomatch h) (fun _ h => nomatch h)

def sumtoCode : Program := parse("sumto:
  subq $8, %rsp
  movq %rdi, %rax
  movq $0, %rcx
  sumto.L0:
  testl %eax, %eax
  jne sumto.L1
  movq %rcx, %rax
  addq $8, %rsp
  ret
  sumto.L1:
  movq %rcx, %r11
  movq %rax, %r10
  addq %r10, %r11
  movq %r11, %rcx
  movq %rax, %r11
  movq $1, %r10
  subq %r10, %r11
  movq %r11, %rax
  jmp sumto.L0")

theorem sumto_lower : lowerFn (Spill.hints Amd64.isa sumto) ⟨[], []⟩ sumto = .ok sumtoCode := by kernel_rfl

theorem sumto_fnspec [hh : Host] (k₀ : Nat) (hc : sumtoCode.IsInfixAt Host.prog k₀)
    (hu : Host.LabelsUnique) (Γ : Env) (nX : Nat) :
    Amd64.target.FnSpec hh "sumto" (Func.spec Γ sumto.body) 8 nX :=
  lowerFn_correct (T := Amd64.target) hh _ ⟨[], []⟩ sumto Γ (fun _ => 0) 8 nX sumtoCode k₀
    sumto_lower hc hu sumto_wf (of_decide_eq_true (by kernel_rfl)) (by decide)
    (fun _ h => nomatch h) (fun _ h => nomatch h)

def evenoddCode : Program := parse("evenodd:
  subq $8, %rsp
  movq %rdi, %rax
  jmp evenodd.L0
  evenodd.L1:
  testl %eax, %eax
  jne evenodd.L2
  movq $0, %rax
  addq $8, %rsp
  ret
  evenodd.L2:
  movq %rax, %r11
  movq $1, %r10
  subq %r10, %r11
  movq %r11, %rax
  evenodd.L0:
  testl %eax, %eax
  jne evenodd.L3
  movq $1, %rax
  addq $8, %rsp
  ret
  evenodd.L3:
  movq %rax, %r11
  movq $1, %r10
  subq %r10, %r11
  movq %r11, %rax
  jmp evenodd.L1")

theorem evenodd_lower : lowerFn (Spill.hints Amd64.isa evenodd) ⟨[], []⟩ evenodd = .ok evenoddCode := by kernel_rfl

theorem evenodd_fnspec [hh : Host] (k₀ : Nat) (hc : evenoddCode.IsInfixAt Host.prog k₀)
    (hu : Host.LabelsUnique) (Γ : Env) (nX : Nat) :
    Amd64.target.FnSpec hh "evenodd" (Func.spec Γ evenodd.body) 8 nX :=
  lowerFn_correct (T := Amd64.target) hh _ ⟨[], []⟩ evenodd Γ (fun _ => 0) 8 nX evenoddCode k₀
    evenodd_lower hc hu evenodd_wf (of_decide_eq_true (by kernel_rfl)) (by decide)
    (fun _ h => nomatch h) (fun _ h => nomatch h)

def nestedCode : Program := parse("nested:
  subq $8, %rsp
  movq %rdi, %rax
  movq %rdx, %rdi
  movq $0, %rcx
  nested.L0:
  testl %eax, %eax
  jne nested.L1
  movq %rcx, %rax
  addq $8, %rsp
  ret
  nested.L1:
  movq %rcx, %rdx
  movq %rsi, %rcx
  nested.L2:
  testl %ecx, %ecx
  jne nested.L3
  movq %rax, %r11
  movq $1, %r10
  subq %r10, %r11
  movq %r11, %rax
  movq %rdx, %rcx
  jmp nested.L0
  nested.L3:
  movq %rdx, %r11
  movq %rdi, %r10
  addq %r10, %r11
  movq %r11, %rdx
  movq %rdx, %r11
  movq %rax, %r10
  addq %r10, %r11
  movq %r11, %rdx
  movq %rcx, %r11
  movq $1, %r10
  subq %r10, %r11
  movq %r11, %rcx
  jmp nested.L2")

theorem nested_lower : lowerFn (Spill.hints Amd64.isa nested) ⟨[], []⟩ nested = .ok nestedCode := by kernel_rfl

theorem nested_fnspec [hh : Host] (k₀ : Nat) (hc : nestedCode.IsInfixAt Host.prog k₀)
    (hu : Host.LabelsUnique) (Γ : Env) (nX : Nat) :
    Amd64.target.FnSpec hh "nested" (Func.spec Γ nested.body) 8 nX :=
  lowerFn_correct (T := Amd64.target) hh _ ⟨[], []⟩ nested Γ (fun _ => 0) 8 nX nestedCode k₀
    nested_lower hc hu nested_wf (of_decide_eq_true (by kernel_rfl)) (by decide)
    (fun _ h => nomatch h) (fun _ h => nomatch h)

def swapCode : Program := parse("swap:
  subq $8, %rsp
  movq %rsi, %rcx
  movq %rdi, %rax
  swap.L0:
  testl %eax, %eax
  jne swap.L1
  movq %rcx, %rax
  addq $8, %rsp
  ret
  swap.L1:
  movq %rax, %r11
  movq $1, %r10
  subq %r10, %r11
  movq %r11, %rax
  movq %rcx, %r10
  movq %rdx, %rcx
  movq %r10, %rdx
  jmp swap.L0")

theorem swap_lower : lowerFn (Spill.hints Amd64.isa swap) ⟨[], []⟩ swap = .ok swapCode := by kernel_rfl

theorem swap_fnspec [hh : Host] (k₀ : Nat) (hc : swapCode.IsInfixAt Host.prog k₀)
    (hu : Host.LabelsUnique) (Γ : Env) (nX : Nat) :
    Amd64.target.FnSpec hh "swap" (Func.spec Γ swap.body) 8 nX :=
  lowerFn_correct (T := Amd64.target) hh _ ⟨[], []⟩ swap Γ (fun _ => 0) 8 nX swapCode k₀
    swap_lower hc hu swap_wf (of_decide_eq_true (by kernel_rfl)) (by decide)
    (fun _ h => nomatch h) (fun _ h => nomatch h)

/-! ## R3 litmus programs: calls, exits, stack spills -/

def incCode : Program := parse("inc:
  subq $8, %rsp
  movq %rdi, %r11
  movq $1, %r10
  addq %r10, %r11
  movq %r11, %rdi
  movq %rdi, %rax
  addq $8, %rsp
  ret")

def callincCode : Program := parse("callinc:
  subq $8, %rsp
  movq %rsi, (%rsp)
  call inc
  movq (%rsp), %rcx
  movq %rax, %r11
  movq %rcx, %r10
  addq %r10, %r11
  movq %r11, %rax
  addq $8, %rsp
  ret")

def checkCode : Program := parse("check:
  subq $8, %rsp
  testl %edi, %edi
  jne check.L0
  addq $8, %rsp
  jmp fail
  check.L0:
  movq %rdi, %rax
  addq $8, %rsp
  ret")

def twiceCode : Program := parse("twice:
  subq $24, %rsp
  movq %rsi, (%rsp)
  call check
  movq %rax, 8(%rsp)
  movq (%rsp), %rdi
  call check
  movq 8(%rsp), %rcx
  movq %rcx, %r11
  movq %rax, %r10
  addq %r10, %r11
  movq %r11, %rax
  addq $24, %rsp
  ret")

def spill10Code : Program := parse("spill10:
  subq $56, %rsp
  movq %rdi, %r11
  movq $1, %r10
  addq %r10, %r11
  movq %r11, %rax
  movq %rdi, %r11
  movq $2, %r10
  addq %r10, %r11
  movq %r11, %rcx
  movq %rdi, %r11
  movq $3, %r10
  addq %r10, %r11
  movq %r11, %rdx
  movq %rdi, %r11
  movq $4, %r10
  addq %r10, %r11
  movq %r11, %r8
  movq %rdi, %r11
  movq $5, %r10
  addq %r10, %r11
  movq %r11, %r9
  movq %r9, (%rsp)
  movq %rdi, %r11
  movq $6, %r10
  addq %r10, %r11
  movq %r11, %r9
  movq %r9, 8(%rsp)
  movq %rdi, %r11
  movq $7, %r10
  addq %r10, %r11
  movq %r11, %r9
  movq %r9, 16(%rsp)
  movq %rdi, %r11
  movq $8, %r10
  addq %r10, %r11
  movq %r11, %r9
  movq %r9, 24(%rsp)
  movq %rdi, %r11
  movq $9, %r10
  addq %r10, %r11
  movq %r11, %r9
  movq %r9, 32(%rsp)
  movq %rdi, %r11
  movq $10, %r10
  addq %r10, %r11
  movq %r11, %rdi
  movq %rdi, 40(%rsp)
  movq %rax, %r11
  movq %rcx, %r10
  xorq %r10, %r11
  movq %r11, %rax
  movq %rax, %r11
  movq %rdx, %r10
  xorq %r10, %r11
  movq %r11, %rax
  movq %rax, %r11
  movq %r8, %r10
  xorq %r10, %r11
  movq %r11, %rax
  movq (%rsp), %rcx
  movq %rax, %r11
  movq %rcx, %r10
  xorq %r10, %r11
  movq %r11, %rax
  movq 8(%rsp), %rcx
  movq %rax, %r11
  movq %rcx, %r10
  xorq %r10, %r11
  movq %r11, %rax
  movq 16(%rsp), %rcx
  movq %rax, %r11
  movq %rcx, %r10
  xorq %r10, %r11
  movq %r11, %rax
  movq 24(%rsp), %rcx
  movq %rax, %r11
  movq %rcx, %r10
  xorq %r10, %r11
  movq %r11, %rax
  movq 32(%rsp), %rcx
  movq %rax, %r11
  movq %rcx, %r10
  xorq %r10, %r11
  movq %r11, %rax
  movq 40(%rsp), %rcx
  movq %rax, %r11
  movq %rcx, %r10
  xorq %r10, %r11
  movq %r11, %rax
  movq %rax, %r11
  movq %rsi, %r10
  xorq %r10, %r11
  movq %r11, %rax
  addq $56, %rsp
  ret")

def sumcallCode : Program := parse("sumcall:
  subq $24, %rsp
  movq %rbx, (%rsp)
  movq %rbp, 8(%rsp)
  movq %r12, 16(%rsp)
  movq %rsi, %r12
  movq %rdi, %rbx
  movq $0, %rbp
  sumcall.L0:
  testl %ebx, %ebx
  jne sumcall.L1
  movq %rbp, %r11
  movq %r12, %r10
  addq %r10, %r11
  movq %r11, %rbp
  movq %rbp, %rax
  movq (%rsp), %rbx
  movq 8(%rsp), %rbp
  movq 16(%rsp), %r12
  addq $24, %rsp
  ret
  sumcall.L1:
  movq %rbx, %rdi
  call inc
  movq %rbp, %r11
  movq %rax, %r10
  addq %r10, %r11
  movq %r11, %rbp
  movq %rbx, %r11
  movq $1, %r10
  subq %r10, %r11
  movq %r11, %rbx
  jmp sumcall.L0")

/-! ## Through the whole pipeline (`compileFn` and `compile`: mid-end, oracle, lowering) -/

theorem sumto_compile : compileFn Amd64.isa sumto = .ok sumtoCode := by kernel_rfl
theorem nested_compile : compileFn Amd64.isa nested = .ok nestedCode := by kernel_rfl
theorem evenodd_compile : compileFn Amd64.isa evenodd = .ok evenoddCode := by kernel_rfl
theorem swap_compile : compileFn Amd64.isa swap = .ok swapCode := by kernel_rfl
theorem ifelse_compile : compileFn Amd64.isa ifelse = .ok ifelseCode := by kernel_rfl
def tracerCompiledCode : Program := parse("tracer:
  subq $8, %rsp
  movq %rdi, %rax
  movq %rax, %r11
  movq %rsi, %r10
  addq %r10, %r11
  movq %r11, %rax
  movq %rax, %r11
  movq %r11, (%rdx)
  addq $8, %rsp
  ret")

theorem tracer_compile : compileFn Amd64.isa tracer = .ok tracerCompiledCode := by kernel_rfl
theorem inc_compile : compileFn Amd64.isa inc = .ok incCode := by kernel_rfl
theorem callinc_compile : compileFn Amd64.isa callinc = .ok callincCode := by kernel_rfl
theorem check_compile : compileFn Amd64.isa check = .ok checkCode := by kernel_rfl
theorem twice_compile : compileFn Amd64.isa twice = .ok twiceCode := by kernel_rfl
theorem spill10_compile : compileFn Amd64.isa spill10 = .ok spill10Code := by kernel_rfl
theorem sumcall_compile : compileFn Amd64.isa sumcall = .ok sumcallCode := by kernel_rfl

theorem callinc_module_compile :
    compile Amd64.isa [inc, callinc] = .ok (incCode ++ callincCode) := by kernel_rfl

theorem twice_module_compile :
    compile Amd64.isa [check, twice] = .ok (checkCode ++ twiceCode) := by kernel_rfl

theorem sumcall_module_compile :
    compile Amd64.isa [inc, sumcall] = .ok (incCode ++ sumcallCode) := by kernel_rfl

/-! ## A loop end to end: `sumto` on Kraken x64 -/

private theorem sumto_nslots : sumto.nslots Amd64.isa = 0 := by kernel_rfl
private theorem sumto_callees : sumto.opt.ext.callees = [] := by kernel_rfl
private theorem sumto_exits : sumto.opt.ext.exits = [] := by kernel_rfl

/-- `sumto` compiled by the whole pipeline, on Kraken x64, in every host containing its code:
called with `n < 2^32` in `rdi`, 8 bytes of stack space below `rsp` and the return address at `rsp`,
it returns to `ra` with `1 + … + n` in `rax`, the callee-saved registers intact and `rsp` popped;
the 16 bytes of stack and return-address slot come back with arbitrary contents and the frame `R` is
untouched. -/
theorem sumto_correct [Host] (k₀ : Nat) (hc : sumtoCode.IsInfixAt Host.prog k₀)
    (hu : Host.LabelsUnique) (n : BitVec 64) (hn : n.toNat < 2 ^ 32)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop) (hrdi : s.regs.get64 .rdi = n)
    (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hmem : s.dmem =⋆
      ((fun f => ∃ bs : List UInt8, bs.length = 8 ∧ f = bs.At (s.regs.get64 .rsp - 8#64)) ⋆
        Eq (ra.toUInt64.At (s.regs.get64 .rsp))) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧ st.data.regs.get64 .rax = tri n.toNat ∧
        (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15], st.data.regs.get64 r = s.regs.get64 r) ∧
        st.data.regs.get64 .rsp = s.regs.get64 .rsp + 8#64 ∧
        (st.data.dmem =⋆ (fun f => ∃ bs : List UInt8, bs.length = 16 ∧ f = bs.At (s.regs.get64 .rsp - 8#64)) ⋆ R))
      ⟨s, Host.addrOf k₀⟩ := by
  have hE : (Eq (∅ : Mem 64)) = Std.ExtHashMap.emp := by
    funext x; apply propext; simp [Std.ExtHashMap.emp, eq_comm]
  have hargs : Amd64.target.ArgsIn [n] s := by
    simp [Target.ArgsIn, Target.ValsIn, Amd64.target, Amd64.isa, hrdi]
  have hmem' : Amd64.target.mem s =⋆ Eq ∅ ⋆
      Amd64.target.Entry (Amd64.target.get s Amd64.target.sp) ra 8 ⋆ R := by
    rw [hE, Std.ExtHashMap.emp_sep]; exact hmem
  have h := compileFn_leaf_correct (T := Amd64.target) _ sumto (fun _ _ _ _ _ => False) 8 0 sumtoCode k₀
    sumto_compile hc hu sumto_wf sumto_callees sumto_exits (by rw [sumto_nslots]; decide) (by decide)
    [n] ∅ _ _ (sumto_spec _ n hn ∅) s ra R hargs trivial hsp hmem'
  have hlab : Amd64.target.labelAddr _ sumto.name = Host.addrOf k₀ :=
    labelAddr_of_unique (T := Amd64.target) hu hc.cons.1
  rw [hlab] at h
  refine eventually_weaken _ _ _ _ ?_ h
  rintro st (⟨hpc, rets, m', ⟨rfl, rfl⟩, hrets, ⟨hcs, hsp'⟩, hm'⟩ | ⟨_, _, _, hx, _⟩)
  · refine ⟨hpc, ?_, fun r hr => hcs r hr, hsp', ?_⟩
    · simpa [Target.RetsIn, Target.ValsIn, Amd64.target, Amd64.isa] using hrets
    · rw [hE, Std.ExtHashMap.emp_sep] at hm'; exact hm'
  · exact hx.elim

/-! ## Non-vacuity of `sumto_correct`: a concrete host and state -/

abbrev sumtoHost : Host := .ofLayout sumtoCode (layoutOf sumtoCode) (layoutOf_zero _) (by decide)

def sumtoState : MachineData :=
  { regs := { rdi := 3, rsp := 0x7008 },
    dmem := (zeros8 ++ (0x1234 : Int64).toUInt64.toBytes).At 0x7000#64 }

attribute [local instance] sumtoHost in
theorem sumto_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧ st.data.regs.get64 .rax = 6)
      ⟨sumtoState, Host.addrOf 0⟩ := by
  have hlen : raBytes0.length = 8 := UInt64.toBytes_length _
  have hmem : sumtoState.dmem =⋆
      ((fun f => ∃ bs : List UInt8, bs.length = 8 ∧ f = bs.At (sumtoState.regs.get64 .rsp - 8#64)) ⋆
        Eq ((0x1234 : Int64).toUInt64.At (sumtoState.regs.get64 .rsp))) ⋆
      Std.ExtHashMap.emp := by
    rw [Std.ExtHashMap.sep_emp]
    have h2 := Mem.At_append_sep zeros8 raBytes0 0x7000#64 (by simp [hlen, zeros8])
    have e2 : (0x7000#64 + BitVec.ofNat 64 zeros8.length) = 0x7008#64 := by simp [zeros8]
    rw [e2] at h2
    have h0 : (Eq ((zeros8 ++ raBytes0).At 0x7000#64)) sumtoState.dmem := rfl
    rw [h2] at h0
    exact sep_mono (fun f1 hf1 => ⟨zeros8, by simp [zeros8], hf1.symm⟩) h0
  have h := sumto_correct 0 (List.prefix_refl _) (Host.labelsUnique_of_nodup (by decide)) 3
    (by decide) sumtoState 0x1234 Std.ExtHashMap.emp rfl (by decide) hmem
  refine eventually_weaken _ _ _ _ ?_ h
  rintro st ⟨hpc, hrax, -⟩
  exact ⟨hpc, by rw [hrax]; decide⟩

/-! ## Two-function module with a call and a spill across the call: `[inc, callinc]` -/

def callincEnv : Env := fun g => if g = "inc" then incContract else callincContract
def callincBound : String → Nat := fun g => if g = "inc" then 8 else 24

private theorem inc_nslots : inc.nslots Amd64.isa = 0 := by kernel_rfl
private theorem inc_callees : inc.opt.ext.callees = [] := by kernel_rfl
private theorem inc_exits : inc.opt.ext.exits = [] := by kernel_rfl
private theorem callinc_nslots : callinc.nslots Amd64.isa = 1 := by kernel_rfl
private theorem callinc_callees : callinc.opt.ext.callees = ["inc"] := by kernel_rfl
private theorem callinc_exits : callinc.opt.ext.exits = [] := by kernel_rfl

/-- Linking `[inc, callinc]` via `compile_correct`. -/
theorem callinc_module_fnspec [hh : Host] (k₀ : Nat)
    (hc : (incCode ++ callincCode).IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique) (nX : Nat) :
    ∀ f ∈ [inc, callinc],
      Amd64.target.FnSpec hh f.name (callincEnv f.name) (callincBound f.name) nX := by
  refine compile_correct (T := Amd64.target) hh callincEnv callincBound nX [inc, callinc]
    (incCode ++ callincCode) k₀ callinc_module_compile hc hu ?_
  intro pre f post heq
  rcases pre with _ | ⟨f1, _ | ⟨f2, pre⟩⟩
  · injection heq with hf htl
    subst hf
    refine ⟨inc_wf, inc_spec _, by rw [inc_nslots]; decide, by decide, ?_, ?_⟩
    · rw [inc_callees]; intro _ h; nomatch h
    · rw [inc_exits]; intro _ h; nomatch h
  · injection heq with hf1 htl
    injection htl with hf _
    subst hf1 hf
    refine ⟨callinc_wf, callinc_spec _ rfl, by rw [callinc_nslots]; decide, by decide, ?_, ?_⟩
    · rw [callinc_callees]
      intro g hg
      simp only [List.mem_singleton] at hg
      subst hg
      exact ⟨Or.inl (by simp [inc]), by rw [callinc_nslots]; decide⟩
    · rw [callinc_exits]; intro _ h; nomatch h
  · simp at heq

/-- `callinc` on Kraken x64: in every host containing `incCode ++ callincCode` at index `k₀`,
calling `callinc` (at index `k₀ + incCode.length`) with `a, b` in `rdi, rsi`, 24 bytes of stack
space below `rsp`, and the return address at `rsp` returns to `ra` with `a + 1 + b` in `rax`. -/
theorem callinc_correct [hh : Host] (k₀ : Nat)
    (hc : (incCode ++ callincCode).IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (a b : BitVec 64) (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (ha : s.regs.get64 .rdi = a) (hb : s.regs.get64 .rsi = b)
    (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hmem : s.dmem =⋆
      ((fun f => ∃ bs : List UInt8, bs.length = 24 ∧ f = bs.At (s.regs.get64 .rsp - 24#64)) ⋆
        Eq (ra.toUInt64.At (s.regs.get64 .rsp))) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧ st.data.regs.get64 .rax = a + 1 + b ∧
        (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15], st.data.regs.get64 r = s.regs.get64 r) ∧
        st.data.regs.get64 .rsp = s.regs.get64 .rsp + 8#64 ∧
        (st.data.dmem =⋆ (fun f => ∃ bs : List UInt8, bs.length = 32 ∧ f = bs.At (s.regs.get64 .rsp - 24#64)) ⋆ R))
      ⟨s, Host.addrOf (k₀ + incCode.length)⟩ := by
  have hE : (Eq (∅ : Mem 64)) = Std.ExtHashMap.emp := by
    funext x; apply propext; simp [Std.ExtHashMap.emp, eq_comm]
  have hargs : Amd64.target.ArgsIn [a, b] s := by
    simp [Target.ArgsIn, Target.ValsIn, Amd64.target, Amd64.isa, ha, hb]
  have hmem' : Amd64.target.mem s =⋆ Eq ∅ ⋆
      Amd64.target.Entry (Amd64.target.get s Amd64.target.sp) ra 24 ⋆ R := by
    rw [hE, Std.ExtHashMap.emp_sep]; exact hmem
  have hf := callinc_module_fnspec k₀ hc hu 0 callinc (by simp)
    [a, b] ∅ (fun r m' => r = [a + 1 + b] ∧ m' = ∅) (fun _ _ _ => False) ⟨a, b, rfl, rfl, rfl⟩
    s ra R hargs trivial hsp hmem'
  have hlab : Amd64.target.labelAddr hh callinc.name = Host.addrOf (k₀ + incCode.length) :=
    labelAddr_of_unique (T := Amd64.target) hu hc.append.2.cons.1
  rw [hlab] at hf
  refine eventually_weaken _ _ _ _ ?_ hf
  rintro st (⟨hpc, rets, m', ⟨rfl, rfl⟩, hrets, ⟨hcs, hsp'⟩, hm'⟩ | ⟨_, _, _, hx, _⟩)
  · refine ⟨hpc, ?_, fun r hr => hcs r hr, hsp', ?_⟩
    · simpa [Target.RetsIn, Target.ValsIn, Amd64.target, Amd64.isa] using hrets
    · rw [hE, Std.ExtHashMap.emp_sep] at hm'; exact hm'
  · exact hx.elim

abbrev callincHost : Host :=
  .ofLayout (incCode ++ callincCode) (layoutOf (incCode ++ callincCode)) (layoutOf_zero _) (by decide)

def callincState : MachineData :=
  { regs := { rdi := 40, rsi := 1, rsp := 0x7008 },
    dmem := (zeros24 ++ raBytes0).At 0x6ff0#64 }

attribute [local instance] callincHost in
theorem callinc_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧ st.data.regs.get64 .rax = 42)
      ⟨callincState, Host.addrOf incCode.length⟩ := by
  have hlen : raBytes0.length = 8 := UInt64.toBytes_length _
  have hmem : callincState.dmem =⋆
      ((fun f => ∃ bs : List UInt8, bs.length = 24 ∧ f = bs.At (callincState.regs.get64 .rsp - 24#64)) ⋆
        Eq ((0x1234 : Int64).toUInt64.At (callincState.regs.get64 .rsp))) ⋆
      Std.ExtHashMap.emp := by
    rw [Std.ExtHashMap.sep_emp]
    have h2 := Mem.At_append_sep zeros24 raBytes0 0x6ff0#64 (by simp [hlen, zeros24])
    have e2 : (0x6ff0#64 + BitVec.ofNat 64 zeros24.length) = 0x7008#64 := by simp [zeros24]
    rw [e2] at h2
    have h0 : (Eq ((zeros24 ++ raBytes0).At 0x6ff0#64)) callincState.dmem := rfl
    rw [h2] at h0
    exact sep_mono (fun f1 hf1 => ⟨zeros24, by simp [zeros24], hf1.symm⟩) h0
  have h := callinc_correct 0 (List.prefix_refl _) (Host.labelsUnique_of_nodup (by decide)) 40 1
    callincState 0x1234 Std.ExtHashMap.emp rfl rfl (by decide) hmem
  refine eventually_weaken _ _ _ _ ?_ h
  rintro st ⟨hpc, hrax, -⟩
  exact ⟨hpc, by rw [hrax]; decide⟩

/-! ## Exit propagation through a call: `[check, twice]` -/

def twiceEnv : Env := fun g => if g = "check" then checkContract else twiceContract
def twiceBound : String → Nat := fun g => if g = "check" then 8 else 40

private theorem check_nslots : check.nslots Amd64.isa = 0 := by kernel_rfl
private theorem check_callees : check.opt.ext.callees = [] := by kernel_rfl
private theorem check_exits : check.opt.ext.exits = ["fail"] := by kernel_rfl
private theorem twice_nslots : twice.nslots Amd64.isa = 2 := by kernel_rfl
private theorem twice_callees : twice.opt.ext.callees = ["check", "check"] := by kernel_rfl
private theorem twice_exits : twice.opt.ext.exits = [] := by kernel_rfl

/-- Linking `[check, twice]` via `compile_correct` in any host that also defines `"fail"`. -/
theorem twice_module_fnspec [hh : Host] (k₀ : Nat)
    (hc : (checkCode ++ twiceCode).IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (hfail : Amd64.target.Defined hh "fail") :
    ∀ f ∈ [check, twice],
      Amd64.target.FnSpec hh f.name (twiceEnv f.name) (twiceBound f.name) 8 := by
  refine compile_correct (T := Amd64.target) hh twiceEnv twiceBound 8 [check, twice]
    (checkCode ++ twiceCode) k₀ twice_module_compile hc hu ?_
  intro pre f post heq
  rcases pre with _ | ⟨f1, _ | ⟨f2, pre⟩⟩
  · injection heq with hf htl
    subst hf
    refine ⟨check_wf, check_spec _, by rw [check_nslots]; decide, by decide, ?_, ?_⟩
    · rw [check_callees]; intro _ h; nomatch h
    · rw [check_exits]
      intro g hg
      simp only [List.mem_singleton] at hg
      subst hg
      exact ⟨hfail, by decide⟩
  · injection heq with hf1 htl
    injection htl with hf _
    subst hf1 hf
    refine ⟨twice_wf, twice_spec _ rfl, by rw [twice_nslots]; decide, by decide, ?_, ?_⟩
    · rw [twice_callees]
      intro g hg
      simp only [List.mem_cons] at hg
      rcases hg with rfl | rfl | hg
      · exact ⟨Or.inl (by simp [check]), by rw [twice_nslots]; decide⟩
      · exact ⟨Or.inl (by simp [check]), by rw [twice_nslots]; decide⟩
      · nomatch hg
    · rw [twice_exits]; intro _ h; nomatch h
  · simp at heq

/-- `twice` on Kraken x64: returns `a + b` to `ra` when both have non-zero low 32 bits, or exits to
`"fail"` in a call-ready state with the failing argument in `rdi`. -/
theorem twice_correct [hh : Host] (k₀ k_fail : Nat)
    (hc : (checkCode ++ twiceCode).IsInfixAt Host.prog k₀)
    (hfail : Host.prog[k_fail]? = some (.label "fail")) (hu : Host.LabelsUnique)
    (a b : BitVec 64) (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (ha : s.regs.get64 .rdi = a) (hb : s.regs.get64 .rsi = b)
    (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hmem : s.dmem =⋆
      ((fun f => ∃ bs : List UInt8, bs.length = 40 ∧ f = bs.At (s.regs.get64 .rsp - 40#64)) ⋆
        Eq (ra.toUInt64.At (s.regs.get64 .rsp))) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st =>
        (Truthy a ∧ Truthy b ∧ st.pc = ra ∧ st.data.regs.get64 .rax = a + b ∧
          (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15], st.data.regs.get64 r = s.regs.get64 r) ∧
          st.data.regs.get64 .rsp = s.regs.get64 .rsp + 8#64) ∨
        ((¬Truthy a ∧ st.pc = Host.addrOf k_fail ∧ st.data.regs.get64 .rdi = a ∧
          (st.data.regs.get64 .rsp + 8#64).toNat % 16 = 0) ∨
         (Truthy a ∧ ¬Truthy b ∧ st.pc = Host.addrOf k_fail ∧ st.data.regs.get64 .rdi = b ∧
          (st.data.regs.get64 .rsp + 8#64).toNat % 16 = 0)))
      ⟨s, Host.addrOf (k₀ + checkCode.length)⟩ := by
  have hE : (Eq (∅ : Mem 64)) = Std.ExtHashMap.emp := by
    funext x; apply propext; simp [Std.ExtHashMap.emp, eq_comm]
  have hargs : Amd64.target.ArgsIn [a, b] s := by
    simp [Target.ArgsIn, Target.ValsIn, Amd64.target, Amd64.isa, ha, hb]
  have hmem' : Amd64.target.mem s =⋆ Eq ∅ ⋆
      Amd64.target.Entry (Amd64.target.get s Amd64.target.sp) ra 40 ⋆ R := by
    rw [hE, Std.ExtHashMap.emp_sep]; exact hmem
  let Q : LeanQbe.Post := fun r m' => Truthy a ∧ Truthy b ∧ r = [a + b] ∧ m' = ∅
  let X : XPost := fun g xs m' =>
    g = "fail" ∧ m' = ∅ ∧ ((¬Truthy a ∧ xs = [a]) ∨ (Truthy a ∧ ¬Truthy b ∧ xs = [b]))
  have hspec : twiceContract [a, b] ∅ Q X :=
    ⟨a, b, rfl, fun hta htb => ⟨hta, htb, rfl, rfl⟩,
      fun hna => ⟨rfl, rfl, Or.inl ⟨hna, rfl⟩⟩,
      fun hta hnb => ⟨rfl, rfl, Or.inr ⟨hta, hnb, rfl⟩⟩⟩
  have hf := twice_module_fnspec k₀ hc hu ⟨k_fail, hfail⟩ twice (by simp)
    [a, b] ∅ Q X hspec s ra R hargs trivial hsp hmem'
  have hlab : Amd64.target.labelAddr hh twice.name = Host.addrOf (k₀ + checkCode.length) :=
    labelAddr_of_unique (T := Amd64.target) hu hc.append.2.cons.1
  have hflab : Amd64.target.labelAddr hh "fail" = Host.addrOf k_fail :=
    labelAddr_of_unique (T := Amd64.target) hu hfail
  rw [hlab] at hf
  refine eventually_weaken _ _ _ _ ?_ hf
  rintro st (⟨hpc, rets, m', ⟨hta, htb, rfl, rfl⟩, hrets, ⟨hcs, hsp'⟩, _⟩ |
    ⟨sym', as', m', ⟨rfl, rfl, hcase⟩, _, hpc, has', hspE, _⟩)
  · refine Or.inl ⟨hta, htb, hpc, ?_, fun r hr => hcs r hr, hsp'⟩
    simpa [Target.RetsIn, Target.ValsIn, Amd64.target, Amd64.isa] using hrets
  · rw [hflab] at hpc
    rcases hcase with ⟨hna, rfl⟩ | ⟨hta, hnb, rfl⟩
    · refine Or.inr (Or.inl ⟨hna, hpc, ?_, hspE⟩)
      simpa [Target.ArgsIn, Target.ValsIn, Amd64.target, Amd64.isa] using has'
    · refine Or.inr (Or.inr ⟨hta, hnb, hpc, ?_, hspE⟩)
      simpa [Target.ArgsIn, Target.ValsIn, Amd64.target, Amd64.isa] using has'

def twiceProg : Program := checkCode ++ twiceCode ++ [.label "fail"]

abbrev twiceHost : Host :=
  .ofLayout twiceProg (layoutOf twiceProg) (layoutOf_zero _) (by decide)

def twiceState (a b : UInt64) : MachineData :=
  { regs := { rdi := a, rsi := b, rsp := 0x7008 },
    dmem := (zeros40 ++ raBytes0).At 0x6fe0#64 }

attribute [local instance] twiceHost in
theorem twice_nonvacuous_exit :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (checkCode.length + twiceCode.length) ∧
        st.data.regs.get64 .rdi = 0)
      ⟨twiceState 20 0, Host.addrOf checkCode.length⟩ := by
  have hlen : raBytes0.length = 8 := UInt64.toBytes_length _
  have hmem : (twiceState 20 0).dmem =⋆
      ((fun f => ∃ bs : List UInt8, bs.length = 40 ∧ f = bs.At ((twiceState 20 0).regs.get64 .rsp - 40#64)) ⋆
        Eq ((0x1234 : Int64).toUInt64.At ((twiceState 20 0).regs.get64 .rsp))) ⋆
      Std.ExtHashMap.emp := by
    rw [Std.ExtHashMap.sep_emp]
    have h2 := Mem.At_append_sep zeros40 raBytes0 0x6fe0#64 (by simp [hlen, zeros40])
    have e2 : (0x6fe0#64 + BitVec.ofNat 64 zeros40.length) = 0x7008#64 := by simp [zeros40]
    rw [e2] at h2
    have h0 : (Eq ((zeros40 ++ raBytes0).At 0x6fe0#64)) (twiceState 20 0).dmem := rfl
    rw [h2] at h0
    exact sep_mono (fun f1 hf1 => ⟨zeros40, by simp [zeros40], hf1.symm⟩) h0
  have hc : (checkCode ++ twiceCode).IsInfixAt Host.prog 0 := ⟨[.label "fail"], rfl⟩
  have hfail : Host.prog[checkCode.length + twiceCode.length]? = some (.label "fail") := by decide
  have h := twice_correct 0 (checkCode.length + twiceCode.length) hc hfail
    (Host.labelsUnique_of_nodup (by decide)) 20 0 (twiceState 20 0) 0x1234
    Std.ExtHashMap.emp rfl rfl (by decide) hmem
  refine eventually_weaken _ _ _ _ ?_ h
  rintro st (⟨_, h0, -⟩ | (⟨hna, -⟩ | ⟨_, _, hpc, hrdi, -⟩))
  · exact absurd h0 (by decide)
  · exact absurd (by decide : Truthy 20) hna
  · exact ⟨hpc, hrdi⟩

/-! ## Spill-heavy leaf function: `spill10` (6 stack spill slots, 56-byte frame) -/

private theorem spill10_nslots : spill10.nslots Amd64.isa = 6 := by kernel_rfl
private theorem spill10_callees : spill10.opt.ext.callees = [] := by kernel_rfl
private theorem spill10_exits : spill10.opt.ext.exits = [] := by kernel_rfl

theorem spill10_fnspec [hh : Host] (k₀ : Nat) (hc : spill10Code.IsInfixAt Host.prog k₀)
    (hu : Host.LabelsUnique) (Γ : Env) (nX : Nat) :
    Amd64.target.FnSpec hh spill10.name (Func.spec Γ spill10.body) 56 nX :=
  compileFn_leaf_correct (T := Amd64.target) hh spill10 Γ 56 nX spill10Code k₀ spill10_compile hc hu
    spill10_wf spill10_callees spill10_exits (by rw [spill10_nslots]; decide) (by decide)

theorem spill10_correct [Host] (k₀ : Nat) (hc : spill10Code.IsInfixAt Host.prog k₀)
    (hu : Host.LabelsUnique) (a b : BitVec 64)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (ha : s.regs.get64 .rdi = a) (hb : s.regs.get64 .rsi = b)
    (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hmem : s.dmem =⋆
      ((fun f => ∃ bs : List UInt8, bs.length = 56 ∧ f = bs.At (s.regs.get64 .rsp - 56#64)) ⋆
        Eq (ra.toUInt64.At (s.regs.get64 .rsp))) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧ st.data.regs.get64 .rax = spill10Val a b ∧
        (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15], st.data.regs.get64 r = s.regs.get64 r) ∧
        st.data.regs.get64 .rsp = s.regs.get64 .rsp + 8#64 ∧
        (st.data.dmem =⋆ (fun f => ∃ bs : List UInt8, bs.length = 64 ∧ f = bs.At (s.regs.get64 .rsp - 56#64)) ⋆ R))
      ⟨s, Host.addrOf k₀⟩ := by
  have hE : (Eq (∅ : Mem 64)) = Std.ExtHashMap.emp := by
    funext x; apply propext; simp [Std.ExtHashMap.emp, eq_comm]
  have hargs : Amd64.target.ArgsIn [a, b] s := by
    simp [Target.ArgsIn, Target.ValsIn, Amd64.target, Amd64.isa, ha, hb]
  have hmem' : Amd64.target.mem s =⋆ Eq ∅ ⋆
      Amd64.target.Entry (Amd64.target.get s Amd64.target.sp) ra 56 ⋆ R := by
    rw [hE, Std.ExtHashMap.emp_sep]; exact hmem
  have h := spill10_fnspec k₀ hc hu (fun _ _ _ _ _ => False) 0
    [a, b] ∅ _ _ (spill10_spec _ a b ∅) s ra R hargs trivial hsp hmem'
  have hlab : Amd64.target.labelAddr _ spill10.name = Host.addrOf k₀ :=
    labelAddr_of_unique (T := Amd64.target) hu hc.cons.1
  rw [hlab] at h
  refine eventually_weaken _ _ _ _ ?_ h
  rintro st (⟨hpc, rets, m', ⟨rfl, rfl⟩, hrets, ⟨hcs, hsp'⟩, hm'⟩ | ⟨_, _, _, hx, _⟩)
  · refine ⟨hpc, ?_, fun r hr => hcs r hr, hsp', ?_⟩
    · simpa [Target.RetsIn, Target.ValsIn, Amd64.target, Amd64.isa] using hrets
    · rw [hE, Std.ExtHashMap.emp_sep] at hm'; exact hm'
  · exact hx.elim

abbrev spill10Host : Host :=
  .ofLayout spill10Code (layoutOf spill10Code) (layoutOf_zero _) (of_decide_eq_true (by kernel_rfl))

def spill10State : MachineData :=
  { regs := { rdi := 10, rsi := 7, rsp := 0x7008 },
    dmem := (zeros56 ++ raBytes0).At 0x6fd0#64 }

attribute [local instance] spill10Host in
theorem spill10_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧ st.data.regs.get64 .rax = spill10Val 10 7)
      ⟨spill10State, Host.addrOf 0⟩ := by
  have hlen : raBytes0.length = 8 := UInt64.toBytes_length _
  have hmem : spill10State.dmem =⋆
      ((fun f => ∃ bs : List UInt8, bs.length = 56 ∧ f = bs.At (spill10State.regs.get64 .rsp - 56#64)) ⋆
        Eq ((0x1234 : Int64).toUInt64.At (spill10State.regs.get64 .rsp))) ⋆
      Std.ExtHashMap.emp := by
    rw [Std.ExtHashMap.sep_emp]
    have h2 := Mem.At_append_sep zeros56 raBytes0 0x6fd0#64 (by simp [hlen, zeros56])
    have e2 : (0x6fd0#64 + BitVec.ofNat 64 zeros56.length) = 0x7008#64 := by simp [zeros56]
    rw [e2] at h2
    have h0 : (Eq ((zeros56 ++ raBytes0).At 0x6fd0#64)) spill10State.dmem := rfl
    rw [h2] at h0
    exact sep_mono (fun f1 hf1 => ⟨zeros56, by simp [zeros56], hf1.symm⟩) h0
  have h := spill10_correct 0 (List.prefix_refl _) (Host.labelsUnique_of_nodup (by decide)) 10 7
    spill10State 0x1234 Std.ExtHashMap.emp rfl rfl (by decide) hmem
  refine eventually_weaken _ _ _ _ ?_ h
  rintro st ⟨hpc, hrax, -⟩
  exact ⟨hpc, hrax⟩

end LeanQbe.Litmus
