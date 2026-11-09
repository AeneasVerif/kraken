module

public import Kraken.X64.WP.Call
public import Kraken.Win64

/-!
# Why the side conditions are there

The calling-convention specifications carry side conditions: the alignment of `rsp`, and the no-wrap
bound of `Reserve`. These facts show that each one is needed: without it, a proof in
`CallConv.Win64Spill` or `CallConv.Win64Inc` would go through for code that faults, or for a
precondition that cannot hold.
-/

open Kraken.Stack
open Kraken.Win64

namespace CallConv.Controls

-- (1) Alignment is load-bearing: an unaligned `movaps` store has no successful outcome, and a
-- frame of 16 instead of 24 bytes would put the slot at an unaligned address.
example (s : MachineData) (a : BitVec 64) (v : BitVec 128) (ret : MachineData → Effects)
    (post : MachineState → Prop) (h : isAligned AvxWidth.W128.bytes a = false) :
    ¬ (s.storeAvx a (w := .W128) v ret true).All post := by
  simp [MachineData.storeAvx, h, Effects.All]

example (r : BitVec 64) (h : r.toNat % 16 = 8) : isAligned AvxWidth.W128.bytes (r - 16) = false := by
  simp only [isAligned, beq_eq_false_iff_ne]
  show (r - 16).toNat % 16 ≠ 0
  bv_omega

-- (2) The caller's own alignment matters: `CallConv.Win64Inc.caller_spec` assumes `rsp + 8`
-- aligned on entry; from an aligned `rsp` instead, the callee would not be entered aligned.
example : ¬ ∀ r : BitVec 64, r.toNat % 16 = 0 → (r - 48).toNat % 16 = 8 := by
  intro h; have := h 0 (by decide); revert this; decide

-- (3) `Reserve_split` needs the no-wrap bound: at `r = 0` an 8-byte reservation is false.
example (m : Mem 64) : ¬ Reserve 8 0 m := fun h => absurd h.1 (by decide)

end CallConv.Controls
