module

public import Kraken.X64.WP.Call
public import Kraken.X64.Win64

/-!
# Why the alignment side condition is there

The calling-convention preconditions require `rsp + 8` to be 16-byte aligned on entry. These facts
show that it is needed: without it, the proof in `CallConv.Win64Spill` would go through for code
that faults.
-/

open Kraken.X64.Stack
open Kraken.X64.Win64

namespace CallConv.Controls

-- Alignment is load-bearing: an unaligned `movaps` store has no successful outcome, and a
-- frame of 16 instead of 24 bytes would put the slot at an unaligned address.
example (s : MachineData) (a : BitVec 64) (v : BitVec 128) (ret : MachineData → Effects)
    (post : MachineState → Prop) (h : isAligned AvxWidth.W128.bytes a = false) :
    ¬ (s.storeAvx a (w := .W128) v ret true).All post := by
  simp [MachineData.storeAvx, h, Effects.All]

example (r : BitVec 64) (h : r.toNat % 16 = 8) : isAligned AvxWidth.W128.bytes (r - 16) = false := by
  simp only [isAligned, beq_eq_false_iff_ne]
  show (r - 16).toNat % 16 ≠ 0
  bv_omega

end CallConv.Controls
