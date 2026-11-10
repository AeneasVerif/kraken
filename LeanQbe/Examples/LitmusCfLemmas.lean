module

public import LeanQbe.RegaLemmas
public import LeanQbe.Examples.LitmusCf
public import LeanQbe.Amd64.TargLemmas
public import Kraken.X64.Parser
public import LeanQbe.WPLemmas
import all Kraken.Separation

/-!
# Control-flow litmus programs: kernel evaluation and the instantiated theorem

For each program of `LitmusCf.lean`: the code `lower` produces with the oracle's hints, written as
assembly and parsed by Kraken (`…Code`), checked by `rfl` (the kernel runs the oracle and `lower`);
`Func.Wf` by `wf_tac`; and `lowerFn_correct` instantiated in every x64 host containing the code.
-/

set_option autoImplicit false

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

theorem ifelse_wf : Func.Wf ifelse.body := by unfold ifelse; wf_tac

theorem ifelse_fnspec [hh : Host] (k₀ : Nat) (hc : ifelseCode.IsInfixAt Host.prog k₀)
    (hu : Host.LabelsUnique) (Γ : Env) :
    Amd64.target.FnSpec hh "ifelse" (Func.spec Γ ifelse.body) 0 :=
  lowerFn_correct (T := Amd64.target) hh _ ifelse Γ 0 ifelseCode k₀ ifelse_lower hc hu ifelse_wf (by decide)

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

theorem sumto_wf : Func.Wf sumto.body := by unfold sumto; wf_tac

theorem sumto_fnspec [hh : Host] (k₀ : Nat) (hc : sumtoCode.IsInfixAt Host.prog k₀)
    (hu : Host.LabelsUnique) (Γ : Env) :
    Amd64.target.FnSpec hh "sumto" (Func.spec Γ sumto.body) 0 :=
  lowerFn_correct (T := Amd64.target) hh _ sumto Γ 0 sumtoCode k₀ sumto_lower hc hu sumto_wf (by decide)

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

theorem evenodd_wf : Func.Wf evenodd.body := by unfold evenodd; wf_tac

theorem evenodd_fnspec [hh : Host] (k₀ : Nat) (hc : evenoddCode.IsInfixAt Host.prog k₀)
    (hu : Host.LabelsUnique) (Γ : Env) :
    Amd64.target.FnSpec hh "evenodd" (Func.spec Γ evenodd.body) 0 :=
  lowerFn_correct (T := Amd64.target) hh _ evenodd Γ 0 evenoddCode k₀ evenodd_lower hc hu evenodd_wf (by decide)

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

theorem nested_wf : Func.Wf nested.body := by unfold nested; wf_tac

theorem nested_fnspec [hh : Host] (k₀ : Nat) (hc : nestedCode.IsInfixAt Host.prog k₀)
    (hu : Host.LabelsUnique) (Γ : Env) :
    Amd64.target.FnSpec hh "nested" (Func.spec Γ nested.body) 0 :=
  lowerFn_correct (T := Amd64.target) hh _ nested Γ 0 nestedCode k₀ nested_lower hc hu nested_wf (by decide)

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

theorem swap_wf : Func.Wf swap.body := by unfold swap; wf_tac

theorem swap_fnspec [hh : Host] (k₀ : Nat) (hc : swapCode.IsInfixAt Host.prog k₀)
    (hu : Host.LabelsUnique) (Γ : Env) :
    Amd64.target.FnSpec hh "swap" (Func.spec Γ swap.body) 0 :=
  lowerFn_correct (T := Amd64.target) hh _ swap Γ 0 swapCode k₀ swap_lower hc hu swap_wf (by decide)

/-! ## A loop end to end: `sumto` on Kraken x64 -/

/-- `1 + 2 + … + i` in 64-bit arithmetic. -/
def tri : Nat → Val
  | 0 => 0
  | i + 1 => tri i + BitVec.ofNat 64 (i + 1)

/-- The source-level contract of `sumto`, by induction over the loop counter (the join point is
universally quantified and constrained only by its closure hypothesis `hloop`). -/
theorem sumto_spec (Γ : Env) (n : Val) (hn : n.toNat < 2 ^ 32) (m : Mem 64) :
    Func.spec Γ sumto.body [n] m (fun r m' => r = [tri n.toNat] ∧ m' = m) (fun _ _ _ => False) := by
  simp only [Func.spec, sumto, wp, Op.wp, Op.eval, BinOp.eval, Arg.val, List.map,
    closed_param, forall_args_nil, List.nil_append, true_and, Option.some.injEq,
    exists_eq_left']
  intro loop hloop
  suffices h : ∀ k, k ≤ n.toNat → ∀ s, s + tri k = tri n.toNat → loop [BitVec.ofNat 64 k, s] m by
    simpa using h n.toNat (Nat.le_refl _) 0 (by simp)
  intro k
  induction k with
  | zero =>
    intro _ s hs
    refine hloop _ _ _ ⟨fun ht => absurd ht (by decide), fun _ => ⟨?_, rfl⟩⟩
    simpa [tri] using hs
  | succ k ih =>
    intro hk s hs
    have hk32 : k + 1 < 2 ^ 32 := by omega
    have ht : Truthy (BitVec.ofNat 64 (k + 1)) := by
      simp only [Truthy, lo32, ne_eq]
      intro h0
      have := congrArg BitVec.toNat h0
      simp [BitVec.toNat_ofNat] at this
      omega
    refine hloop _ _ _ ⟨fun _ => ?_, fun hnt => absurd ht hnt⟩
    have hsub : BitVec.ofNat 64 (k + 1) - 1 = BitVec.ofNat 64 k := by
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    rw [hsub]
    refine ih (by omega) _ ?_
    rw [← hs]; simp only [tri]; ac_rfl

/-- `sumto` on Kraken x64, in every host containing its code: called with `n < 2^32` in `rdi` and
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
  have h := sumto_fnspec k₀ hc hu (fun _ _ _ _ _ => False) [n] ∅ _ _
    (sumto_spec _ n hn ∅) s ra R hargs trivial hsp hmem'
  have hlab : Amd64.target.labelAddr _ "sumto" = Host.addrOf k₀ :=
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

end LeanQbe.Litmus
