module

public import Kraken.StateCfg
import Kraken.X64.Parser

open Kraken.X64.Parser
open Std.WP
open Lean.Order
open scoped Program.WP

set_option experimental.vcgen true

namespace State.Jumps

example [Host] (l : Label) (Q : Unit → MachineData → Prop)
    (E : Int64 → MachineData → Prop) (s : MachineData) (hq : Q () s) :
    WP.wp ([Directive.label l]) Q E s := by
  vcgen
  exact hq

def jmpNext : Program := parse("
  jmp next
next:
  mov $2, %rax")

example [Host] :
    ⦃ fun _ => True ⦄ jmpNext ⦃ fun _ s => s.regs.get64 .rax = 2; fun a _ => a = label "next" ⦄ := by
  kvcgen64 [jmpNext] with finish

def decMid : Program := parse("
top:
  dec %rcx
  jnz top
  mov $1, %rax")

example [Host] :
    ⦃ fun _ => True ⦄ decMid ⦃ fun _ s => s.regs.get64 .rcx = 0; fun a _ => a = label "top" ⦄ := by
  kvcgen64 [decMid] with finish

def jmpOver : Program := parse("
  jmp done
  mov $1, %rbx
done:
  mov $2, %rax")

example [Host] :
    ⦃ fun s => s.regs.get64 .rbx = 0 ⦄ jmpOver
    ⦃ fun _ s => s.regs.get64 .rbx = 0; fun a s => a = label "done" ∧ s.regs.get64 .rbx = 0 ⦄ := by
  kvcgen64 [jmpOver] with finish

def jmpGap : Program := parse("
  jmp b
a:
b:
  mov $2, %rax")

example [Host] :
    ⦃ fun _ => True ⦄ jmpGap ⦃ fun _ s => s.regs.get64 .rax = 2; fun a _ => a = label "b" ⦄ := by
  kvcgen64 [jmpGap] with finish

def jccOver : Program := parse("
  dec %rcx
  jz done
  mov $1, %rbx
done:
  mov $2, %rax")

example [Host] :
    ⦃ fun s => s.regs.get64 .rbx = 0 ⦄ jccOver
    ⦃ fun _ s => s.regs.get64 .rax = 2; fun a s => a = label "done" ∧ s.regs.get64 .rbx = 0 ⦄ := by
  kvcgen64 [jccOver] with finish

def countdown : Program := parse("
top:
  dec %rcx
  jnz top")

example [Host] (hp : countdown.IsInfix Host.prog) (s : MachineData) (h : 0 < s.regs.rcx.toNat) :
    Eventually (step1 Host.exe) (fun st => st.data.regs.rcx = 0) ⟨s, startAddr hp⟩ := by
  letI := BlockEntries.ofLabels (Program.labels countdown)
  apply Program.WP.step1_of_wp hp
  refine Program.WP.cfg_wp (fun _ t => 0 < t.regs.rcx.toNat ∧ t.regs.rsp = s.regs.rsp)
    (fun _ t => t.regs.rcx.toNat) _ ⊥ (fun _ => BlockEntries.mem_ofLabels)
    (fun _ _ _ h₀ ht => MachineData.stackAtOrBelow_of_rsp_eq (by grind)) ?_ s ⟨h, rfl⟩
  cfg_cases [countdown]
  all_goals kvcgen64 with finish

def skip : Program := parse("
start:
  dec %rcx
  jz done
  mov $1, %rbx
done:
  mov $2, %rax")

example [Host] (hp : skip.IsInfix Host.prog) (s : MachineData) :
    Eventually (step1 Host.exe) (fun st => st.data.regs.rax = 2) ⟨s, startAddr hp⟩ := by
  letI := BlockEntries.ofLabels (Program.labels skip)
  apply Program.WP.step1_of_wp hp
  refine Program.WP.cfg_wp (fun _ t => t.regs.rsp = s.regs.rsp) (fun _ _ => 0) _ ⊥
    (fun _ => BlockEntries.mem_ofLabels)
    (fun _ _ _ h₀ ht => MachineData.stackAtOrBelow_of_rsp_eq (by grind)) ?_ s rfl
  cfg_cases [skip]
  all_goals kvcgen64 with finish

end State.Jumps
