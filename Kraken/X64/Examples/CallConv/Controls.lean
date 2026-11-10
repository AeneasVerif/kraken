module

public import Kraken.X64.WP.Call
public import Kraken.X64.Win64

/-!
# Why the side conditions are there

The calling-convention preconditions carry side conditions: the alignment of `rsp`, and the bound
`d ≤ rsp.toNat` on the reservation. These facts show that each one is needed: without it, a proof in
`CallConv.Win64Spill` would go through for code that faults, or `Reserve` would describe memory at
the top of the address space.
-/

open Kraken.X64.Stack
open Kraken.X64.Win64

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

-- (2) `Reserve` itself does not prevent wrap-around: at `rsp = 0` an 8-byte reservation is the top
-- 8 bytes of the address space, not memory below the stack pointer. The `d ≤ rsp.toNat` conjunct of
-- `CallPre` rules this out.
example : Reserve 8 0 = Owned 8 (.ofNat 64 (2 ^ 64 - 8)) := rfl

end CallConv.Controls
