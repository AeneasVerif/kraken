module

public import Kraken.StateCfg
public import Kraken.SeparationMem
import Kraken.X64.Parser

open Kraken.X64.Parser
open Std.WP
open Lean.Order
open scoped Program.WP

set_option experimental.vcgen true

namespace State

def pushPop : Program := parse("
fill:
  push %rax
  dec %rcx
  jnz fill
drain:
  pop %rbx
  dec %rdx
  jnz drain")

theorem pushPop_spec [Host] [FunDecls] (n : Nat) (R : DataMem → Prop) (s : MachineData)
    (hn : 0 < n) (hb : 8 * n < 2 ^ 63) (hrcx : (s.regs.get64 .rcx).toNat = n)
    (hrdx : (s.regs.get64 .rdx).toNat = n)
    (hmem : s.dmem =⋆ Mem.Blocks [(s.regs.get64 .rsp - BitVec.ofNat 64 (8 * n), 8 * n)] ⋆ R) :
    WP.wp pushPop (fun _ t => t.regs.get64 .rsp = s.regs.get64 .rsp) (fun _ _ => False) s := by
  refine Program.WP.cfg
    (fun b t => match b with
      | .entry => t = s
      | .label "fill" => 0 < (t.regs.get64 .rcx).toNat ∧ (t.regs.get64 .rcx).toNat ≤ n
          ∧ t.regs.get64 .rdx = s.regs.get64 .rdx
          ∧ t.regs.get64 .rsp = s.regs.get64 .rsp - BitVec.ofNat 64 (8 * n)
            + BitVec.ofNat 64 (8 * (t.regs.get64 .rcx).toNat)
          ∧ t.dmem =⋆ Mem.Blocks [(s.regs.get64 .rsp - BitVec.ofNat 64 (8 * n), 8 * n)] ⋆ R
      | .label _ => 0 < (t.regs.get64 .rdx).toNat ∧ (t.regs.get64 .rdx).toNat ≤ n
          ∧ t.regs.get64 .rsp = s.regs.get64 .rsp - BitVec.ofNat 64 (8 * n)
            + BitVec.ofNat 64 (8 * (n - (t.regs.get64 .rdx).toNat))
          ∧ t.dmem =⋆ Mem.Blocks [(s.regs.get64 .rsp - BitVec.ofNat 64 (8 * n), 8 * n)] ⋆ R
      | .exit => t.regs.get64 .rsp = s.regs.get64 .rsp)
    (fun l t => match l with
      | "fill" => (t.regs.get64 .rcx).toNat + (t.regs.get64 .rdx).toNat
      | _ => (t.regs.get64 .rdx).toNat) ?_ rfl
  cfg_cases
  all_goals kvcgen64 with finish

end State
