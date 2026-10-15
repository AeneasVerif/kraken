module

public import Kraken.StateCfg
import Kraken.SeparationMem
import Kraken.X64.Parser

open Kraken.X64.Parser
open Std.WP
open Lean.Order
open scoped Program.WP

set_option experimental.vcgen true

namespace State

def pswap : Program := parse("
start:
  call swap
  call swap
  jmp done
swap:
  xor %rbx, %rax
  xor %rax, %rbx
  xor %rbx, %rax
  ret
done:
  nop
")

abbrev pswap.body : Program := parse("
swap:
  xor %rbx, %rax
  xor %rax, %rbx
  xor %rbx, %rax
  ret
")

/-- `swap` clobbers `rax` and `rbx`. -/
private abbrev swapMod : Modifies := ⟨[.rax, .rbx]⟩

private abbrev pswap_table (d : MachineData) (R : DataMem → Prop) : Label → MachineData → Prop
  | "start", s => s = d ∧ d.dmem =⋆ Mem.Blocks [(d.regs.get64 .rsp - 8#64, 8)] ⋆ R
  | "done", s => s.regs.get64 .rax = d.regs.get64 .rax ∧ s.regs.get64 .rbx = d.regs.get64 .rbx
      ∧ s.regs.get64 .rsp = d.regs.get64 .rsp
  | _, _ => False

private theorem pswap_body_spec [Host] (R : DataMem → Prop) (s : MachineData) (ra : Int64) :
    ⦃ fun t => t = s.pushRa ra ∧ s.dmem =⋆ Mem.Blocks [(s.regs.get64 .rsp - 8#64, 8)] ⋆ R ⦄
      pswap.body
    ⦃ (fun _ _ => False); fun a s' => a = ra
      ∧ (s'.regs.get64 .rax = s.regs.get64 .rbx ∧ s'.regs.get64 .rbx = s.regs.get64 .rax
        ∧ s'.dmem =⋆ Mem.Blocks [(s.regs.get64 .rsp - 8#64, 8)] ⋆ R)
      ∧ swapMod.Agree s s' ⦄ := by
  kvcgen64 with finish

theorem pswap_correct [Host] (hp : pswap.IsInfix Host.prog)
    (d : MachineData) (R : DataMem → Prop)
    (hmem : d.dmem =⋆ Mem.Blocks [(d.regs.get64 .rsp - 8#64, 8)] ⋆ R) :
    Eventually (step1 Host.exe)
      (fun s => s.data.regs.get64 .rax = d.regs.get64 .rax
        ∧ s.data.regs.get64 .rbx = d.regs.get64 .rbx
        ∧ s.data.regs.get64 .rsp = d.regs.get64 .rsp)
      ⟨d, startAddr hp⟩ := by
  apply Program.WP.step1_of_wp hp
  refine Program.WP.cfg_wp (l₀ := "start") (pswap_table d R) (fun _ _ => 0) _ ⊥ ?_ d ⟨rfl, hmem⟩
  cfg_cases [pswap]
  · intro k hlink
    have hswap := Program.WP.callSpec_of_triple (body := pswap.body.tail) hlink (by rfl)
      (pswap_body_spec (R := R))
    kvcgen64 [hswap] with finish
  · kvcgen64 with finish

end State
