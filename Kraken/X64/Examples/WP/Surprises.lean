module

public import Kraken.StateCfg
import Kraken.X64.Parser

open Kraken.X64.Parser
open Std.WP
open Lean.Order
open scoped Program.WP

set_option experimental.vcgen true

/-
# Where `Program.wp` exits but the machine continues

Each example is a program whose run provably reaches a goal, so
`Eventually (step1 Host.exe)` can show it. `Program.wp` follows a jump only if
the fragment itself can continue there, so the triple with the intended
postcondition does not hold. Each example proves the triple that does hold,
which shows where the run of the fragment exits.

The three rules behind the examples:
* A jump continues only at an internal target: a label of the fragment.
* A jump continues only while the run owns the stack: the stack pointer is
  at or below the stack pointer at the start of the run.
* A jump is a call only if its own step makes the stack deeper.
-/

namespace State.Surprises

/-! ## B1: a loop that releases stack above its start

The machine runs `drain` twice from `rcx = 2` and then falls off the end:
`add $8, %rsp` releases eight bytes per round. Here `drain` is an internal
target, but after the first round the stack pointer is above the start, so
the run no longer owns the state. The back jump leaves the fragment at
`label "drain"` with `rcx = 1`. The loop is only provable as part of a
fragment that started below the released stack, such as the function that
pushed it. -/

def drain : Program := parse("
drain:
  add $8, %rsp
  dec %rcx
  jnz drain")

example [Host] [FunDecls] (s : MachineData) (hc : s.regs.rcx.toNat = 2) :
    WP.wp drain (fun _ _ => False) (fun a t => a = label "drain" ∧ t.regs.rcx.toNat = 1) s := by
  refine Program.WP.cfg
    (fun b t => match b with
      | .exit => False
      | _ => t = s)
    (fun _ _ => 0) ?_ rfl
  cfg_cases
  all_goals kvcgen64 with finish

/-! ## C1: a call made by hand is a jump

The program reserves a return slot and then jumps to `f`. If `f` is a
declared function that returns to the address in the slot, the machine runs
`f` and comes back. But the `jmp` step itself does not make the stack deeper,
so `Executable.StepOut` does not treat it as a call. The jump leaves the
fragment at `label "f"`, whatever `FunDecls` declares. -/

def manualCall : Program := parse("
  sub $8, %rsp
  jmp f")

example [Host] [FunDecls] :
    ⦃ fun _ => True ⦄ manualCall ⦃ fun _ _ => False; fun a _ => a = label "f" ⦄ := by
  kvcgen64 [manualCall] with finish

/-! ## C2: a tail call is a jump

`jmp f` at the end of a function leaves the stack unchanged, so it is no
call. The function's run exits at `label "f"`, and the effect of `f` is not
part of the function's triple. -/

def tailCall : Program := parse("
  mov $1, %rax
  jmp f")

example [Host] [FunDecls] :
    ⦃ fun _ => True ⦄ tailCall ⦃ fun _ _ => False; fun a s => a = label "f" ∧ s.regs.rax = 1 ⦄ := by
  kvcgen64 [tailCall] with finish

end State.Surprises
