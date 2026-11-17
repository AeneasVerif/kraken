module

import Kraken.X64.Semantics
import Kraken.X64.OmniSemantics
import Kraken.X64.Parser
import Kraken
import all Kraken.Separation
import all Kraken.Mem

import Lean

local instance : Coe Label RelRegOrMem where
  coe l := .rel (.sub (.label l) .after_current_instruction)

macro addr:term " ↦ " val:term : term => `(Eq (UInt64.At $val $addr))


def even : Program := ⸨prog|
even:
  test %rdi, %rdi
  jz even_zero
  dec %rdi
  call odd
  ret
even_zero:
  mov $1, %rax
  ret
⸩

def odd : Program := ⸨prog|
odd:
  test %rdi, %rdi
  jz odd_zero
  dec %rdi
  call even
  ret
odd_zero:
  mov $0, %rax
  ret
⸩

def body (succLabel zeroLabel otherLabel: Label) (ret : Int64) : Program := ⸨prog|
❰.label succLabel❱
  test %rdi, %rdi
  jz ❰zeroLabel❱
  dec %rdi
  call ❰otherLabel❱
  ret
❰.label zeroLabel❱
  mov ❰ret❱, %rax
  ret
⸩

theorem even_body : even = body "even" "even_zero" "odd" 1:= rfl

theorem odd_body : odd = body "odd" "odd_zero" "even" 0 := rfl

open Std.ExtHashMap

attribute [local kstep] RelRegOrMem.interp

theorem body.spec [lbls : Labels]
  (succLabel zeroLabel otherLabel: Label) (ret : Int64)
  [layout : WellFormedLayout (body succLabel zeroLabel otherLabel ret)]
  (st : MachineData)

  (n : UInt64)
  (hlabels : (body succLabel zeroLabel otherLabel ret).toExecutable.labels ⊆ lbls)
  (hhasother )
  (hd : st.regs.rdi = n) :
    letI e := (body succLabel zeroLabel otherLabel ret).toExecutable
    Eventually (step1 e)
      (post := fun ⟨st', pc⟩ => ∃ status,
        match n.toNat with
        | 0 =>  st' = {st with
            regs.rax := ret.toUInt64
            status
          } ∧
          pc = st.regs.rsp
        | n' + 1 => st' = {st with
            regs.rdi := UInt64.ofNat n'
            status
          } ∧
          pc = label! otherLabel
      )
      ⟨st, label! succLabel⟩ := by
  have addrOf_0 : label! succLabel = layout.start := rfl
  rw [addrOf_0]
  kprologue body with st
  sorry
