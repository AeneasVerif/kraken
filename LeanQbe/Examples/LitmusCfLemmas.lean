module

public import LeanQbe.RegaLemmas
public import LeanQbe.Examples.LitmusCf
public import LeanQbe.Amd64.TargLemmas
public import Kraken.X64.Parser

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

end LeanQbe.Litmus
