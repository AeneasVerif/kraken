module

/-
The squaring loop `p3` in the state wp: starting from `rdx = 2`, each
iteration squares `rdx` by `mulx` and counts `rbx` down to zero, so the loop
computes `rdx = 2 ^ 2 ^ rbx`. The proposition is the baseline's
`p3_correct` with two more hypotheses: `rax` starts at zero, which the
statement needs when the loop does not run, and the layout is valid, which
places the loop's labels. `p3_table` gives the assertion at each label,
`rbx` is the variant, and `Program.WP.cfg` leaves one `kvcgen64` obligation per
block.
-/
public import Kraken.StateCfg
import Kraken.X64.Examples.Examples

open Std.WP
open Lean.Order
open scoped Program.WP

set_option experimental.vcgen true

namespace State

/-- Squaring steps the exponent tower once. -/
@[grind =] private theorem sq_pow (r b : Nat) (hb : b ≠ 0) (hle : b ≤ r) :
    2 ^ 2 ^ (r - b) * 2 ^ 2 ^ (r - b) = 2 ^ 2 ^ (r - (b - 1)) := by
  rw [← Nat.pow_add, ← Nat.mul_two, ← Nat.pow_succ]
  show 2 ^ 2 ^ (r - b + 1) = _
  rw [show r - b + 1 = r - (b - 1) from by omega]

/-- The squared invariant stays below the word size. -/
@[grind .] private theorem sq_lt (r b : Nat) (hbound : 2 ^ 2 ^ r < 2 ^ 64)
    (hb : b ≠ 0) (hle : b ≤ r) :
    2 ^ 2 ^ (r - b) * 2 ^ 2 ^ (r - b) < 2 ^ 64 := by
  rw [sq_pow r b hb hle]
  calc 2 ^ 2 ^ (r - (b - 1))
      ≤ 2 ^ 2 ^ r :=
        Nat.pow_le_pow_right (by omega) (Nat.pow_le_pow_right (by omega) (by omega))
    _ < 2 ^ 64 := hbound

/-- The machine at each label of `p3`, for a run that started on `d`. At
`start` it is the loop invariant. -/
private abbrev p3_table (d : MachineData) : CfgLabel → MachineData → Prop
  | .entry, s | .label "init", s => s = d
  | .label "start", s =>
      s.regs.rdx.toNat = 2 ^ 2 ^ (d.regs.rbx.toNat - s.regs.rbx.toNat)
      ∧ s.regs.rbx.toNat ≤ d.regs.rbx.toNat ∧ s.regs.rax = 0 ∧ s.regs.rsp = d.regs.rsp
  | .label "_end", s => s.regs.rdx.toNat = 2 ^ 2 ^ d.regs.rbx.toNat ∧ s.regs.rax = 0 ∧ s.regs.rsp = d.regs.rsp
  | .exit, s => s.regs.rdx.toNat = 2 ^ 2 ^ d.regs.rbx.toNat ∧ s.regs.rax = 0
  | _, _ => False

/-- The baseline's `p3_correct`, for a start state with `rax = 0` and a valid
layout. -/
theorem p3_correct [Host] (hp : p3.IsInfix Host.prog)
    (d : MachineData) (h_bounds : p3_spec d < 2 ^ 64) (h_rax : d.regs.rax = 0) :
    Eventually (step1 Host.exe)
      (fun s => s.data.regs.rdx.toNat = p3_spec d ∧ s.data.regs.rax = 0) ⟨d, startAddr hp⟩ := by
  simp only [p3_spec] at h_bounds ⊢
  apply Program.WP.step1_of_wp hp
  refine Program.WP.cfg (p3_table d) (fun _ s => s.regs.rbx.toNat) ?_ rfl
  cfg_cases
  all_goals kvcgen64 with finish

end State
