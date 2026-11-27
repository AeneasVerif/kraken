module

public import Lean
import Kraken.X64.Parser
import Kraken.X64.OmniSemantics
import Kraken

open Kraken (Layout)

/-- Swaps `rax` and `rbx`-/
def swap := ⸨prog|
swap: xor %rax, %rbx
      xor %rbx, %rax
      xor %rax, %rbx
      jmp %rcx
⸩

theorem swap.sem (l : Layout) [Program.AssemblableWith swap l]
  (st : MachineData) :
    letI e : Executable := l.apply swap
    letI : Labels := e.labels
    Eventually (step1 e)
      (post := fun ⟨st', pc⟩ =>
        ∃ status,
        st' = {st with
          regs := {st.regs with
            rax := st.regs.rbx
            rbx := st.regs.rax
          }
          status
        } ∧
        pc.toUInt64 = st.regs.rcx
      )
      ⟨st, l.start⟩ := by
  kprologue swap with st
  dsimp only
  sym => kstep; tactic =>
  apply Eventually.done
  rename_i a _ b _ c _
  simp [a, b, c]
  bv_decide


def client := ⸨prog|
  La: mov $41, %rax
      mov $42, %rbx
      mov $Lb,  %rcx

      jmp swap

  Lb: test %rax, %rbx
⸩

def final := client ++ swap

theorem final.sem (l : Layout) [hl : Program.AssemblableWith final l]
  (st : MachineData) :
    letI e : Executable := l.apply final
    Eventually (step1 e)
      (post := fun ⟨st', pc⟩ =>
        pc = e.addrOf (client.length) ∧
        st'.regs.rax = 42 ∧
        st'.regs.rbx = 41)
      ⟨st, l.start⟩ := by
  kprologue final with st
  sym => kstep 4; tactic =>
  have : Program.AssemblableWith swap (l.offset client) := Kraken.Program.AssemblableWith.append_right (p₂ := swap) hl
  -- `swap` starts where `client` ends: definitionally the address of directive 7 of `final`.
  have addrOf_7 : (l.offset client).start = (l.apply final).addrOf 7 := rfl
  refine eventually_trans _ _ _ _
    (Eventually.append_right (p₁ := client) (p₂ := swap) hl (addrOf_7 ▸ swap.sem (l.offset client) _)) ?_
  rintro ⟨st2, pc⟩ ⟨_, rfl, pc_toUInt64⟩
  dsimp at *
  have addrOf_5 : pc = (l.apply final).addrOf 5 := by bv_decide
  rw [addrOf_5]
  sym => kstep 1; tactic =>
  apply Eventually.done
  simp [client]
