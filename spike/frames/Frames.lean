module

public import LeanQbe.Amd64.TargLemmas
public import LeanQbe.AbiLemmas
import Kraken.X64.Parser

/-!
# Spike A1 (plan step 2b): frames, calls and exits by hand, on x64

The function contract `FnSpec` must be right before the compiler emits code against it. This spike
proves `FnSpec` v1 (`Abi.lean`) for hand-written x64 code that has every feature the contract has
to account for:

* `g(a)`: a leaf that returns `a + a` or exits to `abort(a)`;
* `f(a, b)`: a callee-saved register (`rbx`, holds `a` across the call), a spill slot (`b`), a call
  to `g` (whose exit propagates), then either `ret` or its own `exit @abort(a)`;
* `abort`: an exit target in the host, with its own `FnSpec`.

Settled here (see docs/reports/abi.md). The proof of `f` and the non-vacuity instances are in
`FramesProof.lean`.

1. **Exit = call-ready state.** At an exit the machine is in a state from which `sym'` could be
   called: pc at `sym'`, arguments in the argument registers, an entry-aligned stack pointer, some
   return address and at least `nX` bytes of stack, memory `Eq m' ⋆ Entry sp' ra' n' ⋆ F ⋆ R`. So an
   exit target can be specified by an `FnSpec` itself. (A first candidate, "tail call relative to
   the function's own entry", is not compositional: an exit inside a callee happens in the
   caller's frame.) This is `FnSpec` v1 in `Abi.lean`.
2. **Alignment at calls.** `spEntry` is assumed on entry and established at every call (x64: frame
   size including pushes ≡ 8 mod 16).
3. **Stack bounds add up.** A function with a frame of `F` bytes calling functions with bounds `n_i`
   has bound `F + 8 + max n_i` on x64 (the 8 is the return address pushed by `call`; it is
   `raBytes`). `f_spec` below is generic in `g`'s bound `n` and proves `f` within `32 + n`.
-/

@[expose] public section

namespace LeanQbe

open Std

namespace Frames

open Amd64

/-! ## The programs -/

/-- The `op` snippet `rax := rdi + rdi` of the x64 target. -/
def gAdd : List Directive := (op (.bin .l .add (.var .rdi) (.var .rdi)) .rax).getD []

/--
```
g:     test %edi, %edi       # exit @abort(a) if the low 32 bits of a are 0
       jnz g.ok
       jmp abort
g.ok:  rax := rdi + rdi      # the `op` snippet (through r11, r10)
       ret
```
-/
def gCode : List Directive :=
  [.label "g"] ++ jnz .rdi "g.ok" ++ [jmpD "abort", .label "g.ok"] ++ gAdd ++ ret

/-- An exit target in the host: `abort: ret`. -/
def abortCode : List Directive := .label "abort" :: ret

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
  test %edi, %edi
  jnz g.ok
  jmp abort
g.ok:
  mov %rdi, %r11
  mov %rdi, %r10
  add %r10, %r11
  mov %r11, %rax
  ret") = gCode := rfl
end ParserChecks

/-! ## The specifications (arity-strict, reviewer #27.1) -/

/-- `g(a) = a + a` if the low 32 bits of `a` are nonzero, else exit to `abort(a)`. -/
def gSpec : Spec := fun args m Q X =>
  ∃ a, args = [a] ∧ (Truthy a → Q [a + a] m) ∧ (¬ Truthy a → X "abort" [a] m)

/-- The value `f` computes before its test. -/
def fVal (a b : Val) : Val := b + (a + (a + a))

/-- `f(a, b)`: exits to `abort(a)` inside `g` if `a` is falsy; otherwise returns `r = b + 3a` if
it is truthy, else exits to `abort(a)` itself. -/
def fSpec : Spec := fun args m Q X =>
  ∃ a b, args = [a, b] ∧ (¬ Truthy a → X "abort" [a] m) ∧
    (Truthy a → (Truthy (fVal a b) → Q [fVal a b] m) ∧ (¬ Truthy (fVal a b) → X "abort" [a] m))

/-- `abort(a)` returns nothing. -/
def abortSpec : Spec := fun args m Q _ => ∃ a, args = [a] ∧ Q [] m

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

theorem infix_slice {α : Type} {c l d : List α} {k : Nat} (hc : c.IsInfixAt l k) (i n : Nat)
    (hd : d = (c.drop i).take n) : d.IsInfixAt l (k + i) := by
  subst hd
  rw [List.isInfixAt_iff_getElem?] at hc ⊢
  intro j hj
  simp only [List.length_take, List.length_drop] at hj
  rw [Nat.add_assoc, hc (i + j) (by omega)]
  simp

theorem infix_at {α : Type} {c l : List α} {d : α} {k : Nat} (hc : c.IsInfixAt l k) (i : Nat)
    (hd : c[i]? = some d) : l[k + i]? = some d := by
  rw [List.isInfixAt_iff_getElem?] at hc
  have hi : i < c.length := by
    rcases Nat.lt_or_ge i c.length with h | h
    · exact h
    · simp [List.getElem?_eq_none h] at hd
  rw [hc i hi, ← List.getElem?_eq_getElem hi]
  exact hd

theorem abort_spec (h : Host) (k : Nat) (hc : abortCode.IsInfixAt (@Host.prog h) k)
    (hu : @Host.LabelsUnique h) (n nX : Nat) (hn : n + 8 ≤ 2 ^ 64) :
    target.FnSpec h "abort" abortSpec n nX := by
  letI := h
  intro args m Q X hspec s ra R _ _ _ hmem
  obtain ⟨a, rfl, hQ⟩ := hspec
  obtain ⟨h0, hret⟩ := hc.cons
  show Eventually (hostStep h) _ ⟨s, hostLabel h "abort"⟩
  rw [show hostLabel h "abort" = Host.addrOf k from Host.label_eq_addrOf_of_unique hu h0]
  refine Host.eventually_label h0 ?_
  have hra := target.retAddr_of_entry' hmem
  refine eventually_ret hret (R := _) hra (.done _ (Or.inl ?_))
  refine ⟨rfl, [], m, hQ, rfl, ⟨fun r hr => ?_, ?_⟩, ?_⟩
  · show (s.regs.set64 .rsp _).get64 r = _
    have hr' : r ≠ .rsp := fun he => by subst he; simp at hr
    rw [Reg64s.get64_set64_of_ne _ _ _ _ (Ne.symm hr')]
  · show (s.regs.set64 .rsp _).get64 .rsp = s.regs.get64 .rsp + BitVec.ofNat 64 8
    rw [Reg64s.get64_set64_same]; rfl
  · exact target.exit_of_entry hn hmem

theorem g_spec (h : Host) (k : Nat) (hc : gCode.IsInfixAt (@Host.prog h) k)
    (hu : @Host.LabelsUnique h) (hab : target.Defined h "abort") (n nX : Nat) (hX : nX ≤ n)
    (hn : n + 8 ≤ 2 ^ 64) :
    target.FnSpec h "g" gSpec n nX := by
  letI := h
  intro args m Q X hspec s ra R hargs _ hsp hmem
  obtain ⟨a, rfl, hQ, hXa⟩ := hspec
  have ha : s.regs.get64 .rdi = a := by
    simpa [Target.ArgsIn, Target.ValsIn, target, isa] using hargs
  have h0 : Host.prog[k + 0]? = some (.label "g") := infix_at hc 0 rfl
  have hj := infix_slice (d := jnz .rdi "g.ok") hc 1 2 rfl
  have h3 : Host.prog[k + 3]? = some (jmpD "abort") := infix_at hc 3 rfl
  have h4 : Host.prog[k + 4]? = some (.label "g.ok") := infix_at hc 4 rfl
  have hop := infix_slice (d := gAdd) hc 5 4 rfl
  have hret := infix_slice (d := ret) hc 9 1 rfl
  show Eventually (hostStep h) _ ⟨s, hostLabel h "g"⟩
  rw [show hostLabel h "g" = Host.addrOf (k + 0) from Host.label_eq_addrOf_of_unique hu h0]
  refine Host.eventually_label h0 ?_
  refine eventually_jnz hj (Host.label_eq_addrOf_of_unique hu h4) fun s1 hs1 hm1 => ⟨?_, ?_⟩
  · -- a truthy: compute and return
    intro ht
    refine Host.eventually_label h4 ?_
    refine eventually_op (o := .bin .l .add (.var .rdi) (.var .rdi)) (rd := .rax) (v := a + a)
      rfl hop (by simp [Op.vars, Arg.vars])
      (by simp [Op.map, Op.eval, Arg.map, Arg.val, BinOp.eval, hs1, ha])
      fun s2 h2 hkeep hm2 => ?_
    have hsp2 : s2.regs.get64 .rsp = s.regs.get64 .rsp := by rw [hkeep _ (by simp), hs1]
    have hra := target.retAddr_of_entry' hmem
    refine eventually_ret hret (R := _) (by rw [hm2, hm1, hsp2]; exact hra) (.done _ (Or.inl ?_))
    refine ⟨rfl, [a + a], m, hQ (by simpa [hs1, ha] using ht), ?_, ⟨?_, ?_⟩, ?_⟩
    · show ([Reg64.rax, .rdx].take 1).map (Reg64s.get64 (s2.regs.set64 .rsp _)) = [a + a]
      simp only [List.take, List.map_cons, List.map_nil, List.cons.injEq, and_true]
      rw [Reg64s.get64_set64_of_ne _ _ _ _ (by simp)]
      exact h2
    · refine calleeSaved_keep fun r hr => ?_
      have hr' : r ≠ .rsp := fun he => hr (by simp [he])
      show (s2.regs.set64 .rsp _).get64 r = _
      rw [Reg64s.get64_set64_of_ne _ _ _ _ (Ne.symm hr'), hkeep r ?_, hs1]
      simp only [List.mem_cons, scratchRegs, List.not_mem_nil, or_false]
      intro hm
      rcases hm with h' | h' | h' <;> simp [h'] at hr
    · show (s2.regs.set64 .rsp _).get64 .rsp = s.regs.get64 .rsp + BitVec.ofNat 64 8
      rw [Reg64s.get64_set64_same, hsp2]
      rfl
    · show (Eq m ⋆ target.Exit (s.regs.get64 .rsp) n ⋆ R) s2.dmem
      rw [hm2, hm1]
      exact target.exit_of_entry hn hmem
  · -- a falsy: exit to abort, call-ready with our own entry stack
    intro hf
    refine eventually_jmpD_any h3 (.done _ (Or.inr ?_))
    refine ⟨"abort", [a], m, hXa (by simpa [hs1, ha] using hf), hab, rfl, ?_, ?_, ra, n, ExtHashMap.emp,
      hX, trivial, ?_⟩
    · show ([Reg64.rdi, .rsi, .rdx, .rcx, .r8, .r9].take 1).map (Reg64s.get64 s1.regs) = [a]
      simp [hs1, ha]
    · show (s1.regs.get64 .rsp + 8#64).toNat % 16 = 0
      rw [hs1]; exact hsp
    · show (Eq m ⋆ target.Entry (s1.regs.get64 .rsp) ra n ⋆ ExtHashMap.emp ⋆ R) s1.dmem
      rw [hs1, hm1, ExtHashMap.sep_emp]
      exact hmem

end Frames

end LeanQbe
