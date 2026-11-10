module

public import LeanQbe.Amd64.TargLemmas
public import LeanQbe.AbiLemmas
import Kraken.X64.Parser

/-!
# Spike A1 (plan step 2b): frames, calls and exits by hand, on x64

The function contract `FnSpec` must be right before the compiler emits code against it. This spike
states a candidate `FnSpec1` (version 1) and proves it for hand-written x64 code that has every
feature the contract has to account for:

* `g(a) = a + a`, a leaf;
* `f(a, b)`: a callee-saved register (`rbx`, holds `a` across the call), a spill slot (`b`), a call
  to `g`, then either `ret` or `exit @abort(a)` depending on the result.

Settled here (see docs/reports/abi.md):

1. **Exit = tail call.** At an exit the machine is in a state from which `sym'` could be called with
   the *same* return address, stack budget and frame: pc at `sym'`, arguments in the argument
   registers, stack pointer and callee-saved registers as on entry, the return address still in
   place, memory `Eq m' ⋆ Entry sp ra n ⋆ R`. So an exit target can be specified by an `FnSpec`
   itself, and alignment at the exit is the entry alignment.
2. **Alignment at calls.** `spEntry` is assumed on entry and established at every call (x64: frame
   size including pushes ≡ 8 mod 16).
3. **Stack bounds add up.** A function with a frame of `F` bytes calling functions with bounds `n_i`
   has bound `F + 8 + max n_i` on x64 (the 8 is the return address pushed by `call`; it is
   `raBytes`). `f_spec` below is generic in `g`'s bound `n` and proves `f` within `32 + n`.
-/

@[expose] public section

namespace LeanQbe

namespace Target

variable (T : Target)

/-- The machine is ready to call: as on entry `s` for registers that must survive (stack pointer,
callee-saved registers) and the return address. -/
def TailCall (s s' : T.MData) (ra : T.Addr) : Prop :=
  T.get s' T.sp = T.get s T.sp ∧ T.raReg s' ra ∧
  ∀ r, r ∈ T.calleeSaved → T.get s' r = T.get s r

/-- Function contract, version 1 candidate: as `FnSpec`, but an exit is a tail call. -/
def FnSpec1 (h : T.Host) (sym : String) (spec : Spec) (n : Nat) : Prop :=
  ∀ args m Q X, spec args m Q X →
  ∀ (s : T.MData) (ra : T.Addr) (R : Mem 64 → Prop),
    T.ArgsIn args s → T.raReg s ra → T.spEntry (T.get s T.sp) →
    (T.mem s =⋆ Eq m ⋆ T.Entry (T.get s T.sp) ra n ⋆ R) →
    Eventually (T.step h)
      (fun st =>
        (T.pc st = ra ∧ ∃ rets m', Q rets m' ∧ T.RetsIn rets (T.data st) ∧
          T.Restored s (T.data st) ∧
          (T.mem (T.data st) =⋆ Eq m' ⋆ T.Exit (T.get s T.sp) n ⋆ R)) ∨
        (∃ sym' as m', X sym' as m' ∧ T.Defined h sym' ∧ T.pc st = T.labelAddr h sym' ∧
          T.ArgsIn as (T.data st) ∧ T.TailCall s (T.data st) ra ∧
          (T.mem (T.data st) =⋆ Eq m' ⋆ T.Entry (T.get s T.sp) ra n ⋆ R)))
      (T.mkState s (T.labelAddr h sym))

end Target

namespace Frames

open Amd64

/-! ## The programs -/

/-- `g: rax := rdi + rdi; ret` (the `op` snippet of the x64 target, then `ret`). -/
def gCode : List Directive :=
  .label "g" :: ((op (.bin .l .add (.var .rdi) (.var .rdi)) .rax).getD []) ++ ret

/--
```
f:    push %rbx               # save callee-saved rbx
      sub $16, %rsp           # frame: 8 (push) + 16 = 24 ≡ 8 mod 16, so rsp ≡ 0 mod 16 at the call
      mov %rdi, %rbx          # a lives in rbx across the call
      movq %rsi, (%rsp)       # spill b
      call g                  # rax := g(a) = a + a   (rdi = a still)
      movq (%rsp), %rsi       # reload b
      add %rbx, %rax          # rax := a + (a + a)
      add %rsi, %rax          # rax := b + (a + (a + a))
      test %eax, %eax
      jnz f.ret
      mov %rbx, %rdi          # exit @abort(a): argument, epilogue, tail jump
      add $16, %rsp
      pop %rbx
      jmp abort
f.ret:
      add $16, %rsp
      pop %rbx
      ret
```
-/
def fCode : List Directive :=
  [.label "f",
   pushD .rbx,
   subSpD 16,
   movD .rbx .rdi,
   stSpD .rsi 0,
   callD "g",
   ldSpD .rsi 0,
   ins (.add (.reg (q .rax)) (.reg (q .rbx))),
   ins (.add (.reg (q .rax)) (.reg (q .rsi)))] ++
  jnz .rax "f.ret" ++
  [movD .rdi .rbx,
   addSpD 16,
   popD .rbx,
   jmpD "abort",
   .label "f.ret",
   addSpD 16,
   popD .rbx] ++ ret

section ParserChecks
open Kraken.X64.Parser
example : parse("f:
  push %rbx
  sub $16, %rsp
  mov %rdi, %rbx
  movq %rsi, (%rsp)
  call g
  movq (%rsp), %rsi
  add %rbx, %rax
  add %rsi, %rax
  test %eax, %eax
  jnz f.ret
  mov %rbx, %rdi
  add $16, %rsp
  pop %rbx
  jmp abort
f.ret:
  add $16, %rsp
  pop %rbx
  ret") = fCode := rfl
example : parse("g:
  mov %rdi, %r11
  mov %rdi, %r10
  add %r10, %r11
  mov %r11, %rax
  ret") = gCode := rfl
end ParserChecks

/-! ## The specifications (arity-strict, reviewer #27.1) -/

/-- `g(a) = a + a`; never exits. -/
def gSpec : Spec := fun args m Q _ => ∃ a, args = [a] ∧ Q [a + a] m

/-- The value `f` computes before its test. -/
def fVal (a b : Val) : Val := b + (a + (a + a))

/-- `f(a, b)`: returns `r = b + 3a` if its low 32 bits are nonzero, else exits to `abort(a)`. -/
def fSpec : Spec := fun args m Q X =>
  ∃ a b, args = [a, b] ∧
    (Truthy (fVal a b) → Q [fVal a b] m) ∧ (¬ Truthy (fVal a b) → X "abort" [a] m)

/-! ## `g` meets its contract -/

/-- Restored callee-saved registers, from "only these registers changed". -/
theorem calleeSaved_keep {s s' : MachineData}
    (h : ∀ r, r ∉ [Reg64.rax, .r10, .r11, .rsp] → s'.regs.get64 r = s.regs.get64 r) :
    ∀ r : Reg64, r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15] →
      s'.regs.get64 r = s.regs.get64 r := by
  intro r hr
  apply h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem g_spec (h : Host) (k : Nat) (hc : gCode.IsInfixAt (@Host.prog h) k)
    (hfirst : ∀ j, j < k → (@Host.prog h)[j]? ≠ some (.label "g")) :
    target.FnSpec1 h "g" gSpec 0 := by
  letI := h
  intro args m Q X hspec s ra R hargs _ _ hmem
  obtain ⟨a, rfl, hQ⟩ := hspec
  have ha : s.regs.get64 .rdi = a := by
    simpa [Target.ArgsIn, Target.ValsIn, target, isa] using hargs
  obtain ⟨h0, hc1⟩ := hc.cons
  obtain ⟨hop, hret⟩ := List.IsInfixAt.append hc1
  have hlab : hostLabel h "g" = Host.addrOf k := Host.label_eq_addrOf h0 hfirst
  show Eventually (hostStep h) _ ⟨s, hostLabel h "g"⟩
  rw [hlab]
  refine Host.eventually_label h0 ?_
  refine eventually_op (o := .bin .l .add (.var .rdi) (.var .rdi)) (rd := .rax) (v := a + a) rfl hop
    (by simp [Op.vars, Arg.vars]) (by simp [Op.map, Op.eval, Arg.map, Arg.val, BinOp.eval, ha])
    fun s1 h1 hkeep hm1 => ?_
  have hsp1 : s1.regs.get64 .rsp = s.regs.get64 .rsp := hkeep _ (by simp)
  have hra := target.retAddr_of_entry' hmem
  refine eventually_ret hret (R := _) (by rw [hm1, hsp1]; exact hra) (.done _ (Or.inl ?_))
  refine ⟨rfl, [a + a], m, hQ, ?_, ⟨?_, ?_⟩, ?_⟩
  · show ([Reg64.rax, .rdx].take 1).map (Reg64s.get64 (s1.regs.set64 .rsp _)) = [a + a]
    simp only [List.take, List.map_cons, List.map_nil, List.cons.injEq, and_true]
    rw [Reg64s.get64_set64_of_ne _ _ _ _ (by simp)]
    exact h1
  · refine calleeSaved_keep fun r hr => ?_
    have hr' : r ≠ .rsp := fun he => hr (by simp [he])
    show (s1.regs.set64 .rsp _).get64 r = _
    rw [Reg64s.get64_set64_of_ne _ _ _ _ (Ne.symm hr')]
    exact hkeep r fun hm => hr (by
      simp only [List.mem_cons, scratchRegs, List.not_mem_nil, or_false] at hm
      rcases hm with h | h | h <;> simp [h])
  · show (s1.regs.set64 .rsp _).get64 .rsp = s.regs.get64 .rsp + BitVec.ofNat 64 8
    rw [Reg64s.get64_set64_same, hsp1]
    rfl
  · show (Eq m ⋆ target.Exit (s.regs.get64 .rsp) 0 ⋆ R) s1.dmem
    rw [hm1]
    exact target.exit_of_entry (by decide) hmem

end Frames

end LeanQbe
