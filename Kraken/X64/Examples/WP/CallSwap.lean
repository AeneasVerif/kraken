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

def swap : Program := parse("
swap:
  xor %rbx, %rax
  xor %rax, %rbx
  xor %rbx, %rax
  ret
")

def pswap : Program := parse("
start:
  call swap
  call swap
  jmp done
") ++ swap ++ parse("
done:
  nop
")

/-- `swap` clobbers `rax`, `rbx` and its return slot. -/
private abbrev swapMod (s : MachineData) : Modifies := ⟨[.rax, .rbx], [(s.regs.get64 .rsp - 8#64, 8)]⟩

theorem swap_spec [Host] [FunDecls] (s : MachineData) (ra : Int64) :
    ⦃ fun t => t = s.pushRa ra ∧ Mem.Mapped [(s.regs.get64 .rsp - 8#64, 8)] s.dmem ⦄
      swap
    ⦃ (fun _ _ => False); fun a s' => a = ra
      ∧ (s'.regs.get64 .rax = s.regs.get64 .rbx ∧ s'.regs.get64 .rbx = s.regs.get64 .rax
        ∧ Mem.Mapped [(s.regs.get64 .rsp - 8#64, 8)] s'.dmem)
      ∧ (swapMod s).Agree s s' ⦄ := by
  refine ⟨fun s₀ ⟨h₀, _⟩ => ?_⟩
  subst h₀
  refine Program.WP.cfg (fun
      | .entry, t | .label "swap", t => t = s.pushRa ra
      | _, _ => False)
    (fun _ _ => 0) ?_ rfl
  cfg_cases
  all_goals kvcgen64 with finish

theorem pswap_correct [Host] (hp : pswap.IsInfix Host.prog)
    (d : MachineData)
    (hmem : Mem.Mapped [(d.regs.get64 .rsp - 8#64, 8)] d.dmem) :
    Eventually (step1 Host.exe)
      (fun s => s.data.regs.get64 .rax = d.regs.get64 .rax
        ∧ s.data.regs.get64 .rbx = d.regs.get64 .rbx
        ∧ s.data.regs.get64 .rsp = d.regs.get64 .rsp)
      ⟨d, startAddr hp⟩ := by
  have hk := List.isInfixAt_infixIdx hp
  generalize pswap.infixIdx Host.prog hp = k at hk
  have hsp : swap.IsInfixAt pswap 4 := ⟨_, rfl⟩
  have hsw : swap.IsInfixAt Host.prog (k + 4) := List.IsInfixAt.trans hsp hk
  letI : Embeds swap := ⟨⟨k + 4, hsw⟩⟩
  letI : FunDecls := ⟨[Fragment.mk swap]⟩
  have hstart : (Fragment.mk swap).startAddr = label "swap" := (Host.label_eq (i := 0) hsw rfl).symm
  have hg : FunDecls.at (label "swap") = some (Fragment.mk swap) := by
    show List.find? _ [_] = _
    simp [hstart]
  have hcall := Program.WP.callSpec_of_triple hg
    swap_spec
  apply Program.WP.step1_of_wp hp
  refine Program.WP.cfg (fun
      | .entry, s | .label "start", s => s = d
      | .label "done", s | .exit, s => s.regs.get64 .rax = d.regs.get64 .rax
          ∧ s.regs.get64 .rbx = d.regs.get64 .rbx ∧ s.regs.get64 .rsp = d.regs.get64 .rsp
      | _, _ => False)
    (fun _ _ => 0) ?_ rfl
  cfg_cases
  all_goals kvcgen64 [hcall] with finish

end State
