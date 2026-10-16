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

/-- `swap` clobbers `rax` and `rbx`. -/
private abbrev swapMod : Modifies := ⟨[.rax, .rbx]⟩

private abbrev swap_table (P : Prop) (s : MachineData) (ra : Int64) : Label → MachineData → Prop
  | "swap", t => t = s.pushRa ra ∧ P
  | _, _ => False

theorem swap_spec [Host] [BlockEntries] [FunDecls] (R : DataMem → Prop)
    (hent : ∀ l ∈ Program.labels swap, l ∈ BlockEntries.labels)
    (s : MachineData) (ra : Int64) :
    ⦃ fun t => t = s.pushRa ra ∧ s.dmem =⋆ Mem.Blocks [(s.regs.get64 .rsp - 8#64, 8)] ⋆ R ⦄
      swap
    ⦃ (fun _ _ => False); fun a s' => a = ra
      ∧ (s'.regs.get64 .rax = s.regs.get64 .rbx ∧ s'.regs.get64 .rbx = s.regs.get64 .rax
        ∧ s'.dmem =⋆ Mem.Blocks [(s.regs.get64 .rsp - 8#64, 8)] ⋆ R)
      ∧ swapMod.Agree s s' ⦄ := by
  refine Program.WP.cfg (p := swap) (swap_table ?_ s ra) (fun _ _ => 0) (fun _ => False) _ hent ?_ ?_
  · intro s₀ l t h₀ ht
    apply MachineData.stackAtOrBelow_of_rsp_eq
    obtain ⟨rfl, -⟩ := h₀
    unfold swap_table at ht
    split at ht <;> grind
  cfg_cases [swap]
  all_goals kvcgen64 with finish

private abbrev pswap_table (d : MachineData) (R : DataMem → Prop) : Label → MachineData → Prop
  | "start", s => s = d ∧ d.dmem =⋆ Mem.Blocks [(d.regs.get64 .rsp - 8#64, 8)] ⋆ R
  | "done", s => s.regs.get64 .rax = d.regs.get64 .rax ∧ s.regs.get64 .rbx = d.regs.get64 .rbx
      ∧ s.regs.get64 .rsp = d.regs.get64 .rsp
  | _, _ => False

theorem pswap_correct [Host] (hp : pswap.IsInfix Host.prog)
    (d : MachineData) (R : DataMem → Prop)
    (hmem : d.dmem =⋆ Mem.Blocks [(d.regs.get64 .rsp - 8#64, 8)] ⋆ R) :
    Eventually (step1 Host.exe)
      (fun s => s.data.regs.get64 .rax = d.regs.get64 .rax
        ∧ s.data.regs.get64 .rbx = d.regs.get64 .rbx
        ∧ s.data.regs.get64 .rsp = d.regs.get64 .rsp)
      ⟨d, startAddr hp⟩ := by
  letI := BlockEntries.ofLabels (Program.labels pswap)
  have hk := List.isInfixAt_infixIdx hp
  generalize pswap.infixIdx Host.prog hp = k at hk
  have hsp : swap.IsInfixAt pswap 4 := ⟨_, rfl⟩
  have hsw : swap.IsInfixAt Host.prog (k + 4) := List.IsInfixAt.trans hsp hk
  letI : Embeds swap := ⟨⟨k + 4, hsw⟩⟩
  letI : FunDecls := ⟨[frag% swap]⟩
  have hstart : (frag% swap).startAddr = label "swap" := (Host.label_eq (i := 0) hsw rfl).symm
  have hg : FunDecls.at (label "swap") = some (frag% swap) := by
    show List.find? _ [_] = _
    simp [hstart]
  have hcall := Program.WP.callSpec_of_triple hg
    (swap_spec R (fun _ h => BlockEntries.mem_ofLabels
      (Program.mem_labels.mpr (hsp.isInfix.subset (Program.mem_labels.mp h)))))
  apply Program.WP.step1_of_wp hp
  refine Program.WP.cfg_wp (l₀ := "start") (pswap_table d R) (fun _ _ => 0) _ ⊥
    (fun _ => BlockEntries.mem_ofLabels) ?_ ?_ d ⟨rfl, hmem⟩
  · intro s₀ l t h₀ ht
    apply MachineData.stackAtOrBelow_of_rsp_eq
    obtain ⟨rfl, -⟩ := h₀
    unfold pswap_table at ht
    split at ht <;> grind
  cfg_cases [pswap, swap]
  · kvcgen64 [hcall] with finish
  · kvcgen64 with finish

end State
