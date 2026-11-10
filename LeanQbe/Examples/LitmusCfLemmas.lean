module

public import LeanQbe.RegaLemmas
public import LeanQbe.Examples.LitmusCf
public import LeanQbe.Examples.LitmusProgsLemmas
public import LeanQbe.Amd64.TargLemmas
public import Kraken.X64.Parser
public import LeanQbe.WPLemmas
public import LeanQbe.MainLemmas
public import LeanQbe.Examples.Litmus
import all Kraken.Separation

/-!
# Control-flow litmus programs: kernel evaluation and the instantiated theorem

For each program of `LitmusCf.lean`: the code `lower` produces with the oracle's hints, written as
assembly and parsed by Kraken (`…Code`), checked by `rfl` (the kernel runs the oracle and `lower`);
`Func.Wf` by `wf_tac`; and `lowerFn_correct` instantiated in every x64 host containing the code.
-/

set_option autoImplicit false

open Lean Elab Tactic Meta in
/-- Close `lhs = rhs` with `Eq.refl lhs`, checked by the kernel only (the elaborator's `isDefEq`
gives up on the mid-end's table lookups). From Spike A. -/
elab "kernel_rfl" : tactic => do
  let goal ← getMainGoal
  let tgt ← instantiateMVars (← goal.getType)
  let some (α, lhs, _) := tgt.eq?
    | throwError "kernel_rfl: goal is not an equality{indentExpr tgt}"
  let u ← getLevel α
  goal.assign (mkApp2 (mkConst ``Eq.refl [u]) α lhs)
  replaceMainGoal []

@[expose] public section

namespace LeanQbe.Litmus

open Rega

def ifelseCode : Program := parse("ifelse:
  testl %edi, %edi
  jne ifelse.L0
  movq %rsi, %r11
  movq %rdi, %r10
  subq %r10, %r11
  movq %r11, %rax
  ret
  ifelse.L0:
  movq %rdi, %r11
  movq %rsi, %r10
  addq %r10, %r11
  movq %r11, %rax
  ret")

theorem ifelse_lower : lowerFn (Spill.hints Amd64.isa ifelse) ifelse = .ok ifelseCode := by rfl

theorem ifelse_fnspec [hh : Host] (k₀ : Nat) (hc : ifelseCode.IsInfixAt Host.prog k₀)
    (hu : Host.LabelsUnique) (Γ : Env) (nX : Nat) :
    Amd64.target.FnSpec hh "ifelse" (Func.spec Γ ifelse.body) 0 nX :=
  lowerFn_correct (T := Amd64.target) hh _ ifelse Γ 0 ifelseCode k₀ ifelse_lower hc hu ifelse_wf (by decide) nX

def sumtoCode : Program := parse("sumto:
  movq %rdi, %rax
  movq $0, %rcx
  jmp sumto.L0
  sumto.L0:
  testl %eax, %eax
  jne sumto.L1
  movq %rcx, %rax
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

theorem sumto_lower : lowerFn (Spill.hints Amd64.isa sumto) sumto = .ok sumtoCode := by rfl

theorem sumto_fnspec [hh : Host] (k₀ : Nat) (hc : sumtoCode.IsInfixAt Host.prog k₀)
    (hu : Host.LabelsUnique) (Γ : Env) (nX : Nat) :
    Amd64.target.FnSpec hh "sumto" (Func.spec Γ sumto.body) 0 nX :=
  lowerFn_correct (T := Amd64.target) hh _ sumto Γ 0 sumtoCode k₀ sumto_lower hc hu sumto_wf (by decide) nX

def evenoddCode : Program := parse("evenodd:
  movq %rdi, %rax
  jmp evenodd.L0
  evenodd.L1:
  testl %eax, %eax
  jne evenodd.L2
  movq $0, %rax
  ret
  evenodd.L2:
  movq %rax, %r11
  movq $1, %r10
  subq %r10, %r11
  movq %r11, %rax
  jmp evenodd.L0
  evenodd.L0:
  testl %eax, %eax
  jne evenodd.L3
  movq $1, %rax
  ret
  evenodd.L3:
  movq %rax, %r11
  movq $1, %r10
  subq %r10, %r11
  movq %r11, %rax
  jmp evenodd.L1")

theorem evenodd_lower : lowerFn (Spill.hints Amd64.isa evenodd) evenodd = .ok evenoddCode := by rfl

theorem evenodd_fnspec [hh : Host] (k₀ : Nat) (hc : evenoddCode.IsInfixAt Host.prog k₀)
    (hu : Host.LabelsUnique) (Γ : Env) (nX : Nat) :
    Amd64.target.FnSpec hh "evenodd" (Func.spec Γ evenodd.body) 0 nX :=
  lowerFn_correct (T := Amd64.target) hh _ evenodd Γ 0 evenoddCode k₀ evenodd_lower hc hu evenodd_wf (by decide) nX

def nestedCode : Program := parse("nested:
  movq %rdi, %rax
  movq $0, %rcx
  jmp nested.L0
  nested.L0:
  testl %eax, %eax
  jne nested.L1
  movq %rcx, %rax
  ret
  nested.L1:
  movq %rcx, %rdi
  movq %rsi, %rcx
  jmp nested.L2
  nested.L2:
  testl %ecx, %ecx
  jne nested.L3
  movq %rax, %r11
  movq $1, %r10
  subq %r10, %r11
  movq %r11, %rax
  movq %rdi, %rcx
  jmp nested.L0
  nested.L3:
  movq %rdi, %r11
  movq %rdx, %r10
  addq %r10, %r11
  movq %r11, %rdi
  movq %rdi, %r11
  movq %rax, %r10
  addq %r10, %r11
  movq %r11, %rdi
  movq %rcx, %r11
  movq $1, %r10
  subq %r10, %r11
  movq %r11, %rcx
  jmp nested.L2")

theorem nested_lower : lowerFn (Spill.hints Amd64.isa nested) nested = .ok nestedCode := by rfl

theorem nested_fnspec [hh : Host] (k₀ : Nat) (hc : nestedCode.IsInfixAt Host.prog k₀)
    (hu : Host.LabelsUnique) (Γ : Env) (nX : Nat) :
    Amd64.target.FnSpec hh "nested" (Func.spec Γ nested.body) 0 nX :=
  lowerFn_correct (T := Amd64.target) hh _ nested Γ 0 nestedCode k₀ nested_lower hc hu nested_wf (by decide) nX

def swapCode : Program := parse("swap:
  movq %rdi, %rax
  movq %rsi, %rcx
  jmp swap.L0
  swap.L0:
  testl %eax, %eax
  jne swap.L1
  movq %rcx, %rax
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

theorem swap_lower : lowerFn (Spill.hints Amd64.isa swap) swap = .ok swapCode := by rfl

theorem swap_fnspec [hh : Host] (k₀ : Nat) (hc : swapCode.IsInfixAt Host.prog k₀)
    (hu : Host.LabelsUnique) (Γ : Env) (nX : Nat) :
    Amd64.target.FnSpec hh "swap" (Func.spec Γ swap.body) 0 nX :=
  lowerFn_correct (T := Amd64.target) hh _ swap Γ 0 swapCode k₀ swap_lower hc hu swap_wf (by decide) nX

/-! ## Through the whole pipeline (`compileFn`: mid-end, oracle, lowering)

The mid-end finds nothing to do in these programs, so the pipeline emits the same code; the kernel
checks it, running `Func.opt`, the oracle and `lower`. -/

theorem sumto_compile : compileFn Amd64.isa sumto = .ok sumtoCode := by kernel_rfl
theorem nested_compile : compileFn Amd64.isa nested = .ok nestedCode := by kernel_rfl
theorem evenodd_compile : compileFn Amd64.isa evenodd = .ok evenoddCode := by kernel_rfl
theorem swap_compile : compileFn Amd64.isa swap = .ok swapCode := by kernel_rfl
theorem ifelse_compile : compileFn Amd64.isa ifelse = .ok ifelseCode := by kernel_rfl
theorem tracer_compile : compileFn Amd64.isa tracer = .ok tracerCode := by kernel_rfl

/-! ## A loop end to end: `sumto` on Kraken x64 -/

/-- `sumto` compiled by the whole pipeline, on Kraken x64, in every host containing its code: called with `n < 2^32` in `rdi` and
the return address at `rsp`, it returns to `ra` with `1 + … + n` in `rax`, the callee-saved
registers intact and `rsp` popped; the return-address slot comes back with arbitrary contents and
the frame `R` is untouched. -/
theorem sumto_correct [Host] (k₀ : Nat) (hc : sumtoCode.IsInfixAt Host.prog k₀)
    (hu : Host.LabelsUnique) (n : BitVec 64) (hn : n.toNat < 2 ^ 32)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop) (hrdi : s.regs.get64 .rdi = n)
    (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hmem : s.dmem =⋆ Eq (ra.toUInt64.At (s.regs.get64 .rsp)) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧ st.data.regs.get64 .rax = tri n.toNat ∧
        (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15], st.data.regs.get64 r = s.regs.get64 r) ∧
        st.data.regs.get64 .rsp = s.regs.get64 .rsp + 8#64 ∧
        (st.data.dmem =⋆ (fun f => ∃ bs : List UInt8, bs.length = 8 ∧ f = bs.At (s.regs.get64 .rsp)) ⋆ R))
      ⟨s, Host.addrOf k₀⟩ := by
  have hE : (Eq (∅ : Mem 64)) = Std.ExtHashMap.emp := by
    funext x; apply propext; simp [Std.ExtHashMap.emp, eq_comm]
  have hargs : Amd64.target.ArgsIn [n] s := by
    simp [Target.ArgsIn, Target.ValsIn, Amd64.target, Amd64.isa, hrdi]
  have hmem' : Amd64.target.mem s =⋆ Eq ∅ ⋆
      Amd64.target.Entry (Amd64.target.get s Amd64.target.sp) ra 0 ⋆ R := by
    simp only [Target.Entry, region_zero, Std.ExtHashMap.emp_sep, hE]
    exact hmem
  -- the whole pipeline: `compileFn` (mid-end, oracle, lowering) and `compileFn_correct`
  have h := compileFn_correct (T := Amd64.target) _ sumto (fun _ _ _ _ _ => False) 0 0 sumtoCode k₀
    sumto_compile hc hu sumto_wf (by decide) [n] ∅ _ _ (sumto_spec _ n hn ∅) s ra R hargs trivial
    hsp hmem'
  have hlab : Amd64.target.labelAddr _ sumto.name = Host.addrOf k₀ :=
    labelAddr_of_unique (T := Amd64.target) hu hc.cons.1
  rw [hlab] at h
  refine eventually_weaken _ _ _ _ ?_ h
  rintro st (⟨hpc, rets, m', ⟨rfl, rfl⟩, hrets, ⟨hcs, hsp'⟩, hm'⟩ | ⟨_, _, _, hx, _⟩)
  · refine ⟨hpc, ?_, fun r hr => hcs r hr, hsp', ?_⟩
    · simpa [Target.RetsIn, Target.ValsIn, Amd64.target, Amd64.isa] using hrets
    · have hX : Amd64.target.Exit (Amd64.target.get s Amd64.target.sp) 0 =
          fun f => ∃ bs : List UInt8, bs.length = 8 ∧ f = bs.At (s.regs.get64 .rsp) := by
        funext f; simp [Target.Exit, region]
      rw [hX, hE, Std.ExtHashMap.emp_sep] at hm'
      exact hm'
  · exact hx.elim

/-! ## Non-vacuity of `sumto_correct`: a concrete host and state -/

/-- Labels of size 0, every other directive of size 4, from `0x1000`. -/
@[instance_reducible] def layoutOf (p : Program) : Layout :=
  { start := 0x1000, size := fun i => match p[i]? with | some (.label _) => 0 | _ => 4 }

theorem layoutOf_zero (p : Program) :
    ∀ i d, p[i]? = some d → @Kraken.Layout.size _ (layoutOf p) i = 0 → ∃ l, d = .label l := by
  intro i d hd hz
  cases d
  case label l => exact ⟨l, rfl⟩
  all_goals
    have hz' : (match p[i]? with | some (.label _) => 0 | _ => 4) = 0 := hz
    rw [hd] at hz'
    simp at hz'

abbrev sumtoHost : Host := .ofLayout sumtoCode (layoutOf sumtoCode) (layoutOf_zero _) (by decide)

def sumtoState : MachineData :=
  { regs := { rdi := 3, rsp := 0x7008 }, dmem := (0x1234 : Int64).toUInt64.toBytes.At 0x7008#64 }

attribute [local instance] sumtoHost in
theorem sumto_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧ st.data.regs.get64 .rax = 6)
      ⟨sumtoState, Host.addrOf 0⟩ := by
  have hmem : sumtoState.dmem =⋆ Eq ((0x1234 : Int64).toUInt64.At (sumtoState.regs.get64 .rsp)) ⋆
      Std.ExtHashMap.emp := by
    rw [Std.ExtHashMap.sep_emp]; rfl
  have h := sumto_correct 0 (List.prefix_refl _) (Host.labelsUnique_of_nodup (by decide)) 3
    (by decide) sumtoState 0x1234 Std.ExtHashMap.emp rfl (by decide) hmem
  refine eventually_weaken _ _ _ _ ?_ h
  rintro st ⟨hpc, hrax, -⟩
  exact ⟨hpc, by rw [hrax]; decide⟩

end LeanQbe.Litmus
