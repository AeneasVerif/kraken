module

import LeanQbe.T.Arm64.IselShiftLemmas
meta import LeanQbe.T.Logic.ProofKit
import Kraken.AArch64.Parser

/-!
# Arm64 Shifted-Register ALU Selection Tests

Covers all 5 opcodes × 2 widths × 3 shift modes (`add`/`sub`/`and`/`or`/`xor` × `{32, 64}` ×
`lsl`/`lsr`/`asr`), aliasing, negative bounds (`k >= w`, invalid widths/ops, `.SP`), 32-bit
upper-half zeroing witnesses, and standard-axiom verification.
-/

section

namespace LeanQbeTest.T.Arm64ShiftIselTest

open LeanQbe.T
open LeanQbe.T.Arm64
open Kraken.AArch64.Parser

private def okShift (w : Nat) (c : OpCode [.bits w, .bits w] [.bits w])
    (sh : ArmShiftOp) (k : Nat) : Bool :=
  match armShiftedAlu? w c (.reg .X1) (.reg .X2) sh k (.reg .X0) with
  | some ([_], clob) => clob == maskNone
  | _ => false

private def allShiftsAtWidth (w : Nat) (c : OpCode [.bits w, .bits w] [.bits w])
    (k1 k2 k3 : Nat) : Bool :=
  okShift w c .lsl 0 && okShift w c .lsl k1 &&
  okShift w c .lsr 0 && okShift w c .lsr k2 &&
  okShift w c .asr 0 && okShift w c .asr k3

-- Exhaustive 30-way matrix (5 opcodes × 2 widths × 3 shifts, including k = 0 and k = w - 1)
example :
    allShiftsAtWidth 32 (.add _) 31 7 31 &&
    allShiftsAtWidth 64 (.add _) 63 19 63 &&
    allShiftsAtWidth 32 (.sub _) 5 31 19 &&
    allShiftsAtWidth 64 (.sub _) 9 63 33 &&
    allShiftsAtWidth 32 (.and _) 1 16 31 &&
    allShiftsAtWidth 64 (.and _) 42 63 63 &&
    allShiftsAtWidth 32 (.or  _) 2 31 8 &&
    allShiftsAtWidth 64 (.or  _) 17 63 61 &&
    allShiftsAtWidth 32 (.xor _) 3 31 15 &&
    allShiftsAtWidth 64 (.xor _) 28 48 63 = true := by
  rfl

-- Register aliasing (rd = ra = rb) is safely emitted
example : armShiftedAlu? 64 (.xor _) (.reg .X4) (.reg .X4) .asr 7 (.reg .X4) =
    some (⸨prog| eor x4, x4, x4, asr #7 ⸩, maskNone) := by
  rfl

-- Exact instruction checks across all 5 opcodes, both widths, and all 3 shifts
example : armShiftedAlu? 32 (.add _) (.reg .X1) (.reg .X2) .lsl 4 (.reg .X0) =
    some (⸨prog| add w0, w1, w2, lsl #4 ⸩, maskNone) := by
  rfl

example : armShiftedAlu? 32 (.sub _) (.reg .X1) (.reg .X2) .lsr 5 (.reg .X0) =
    some (⸨prog| sub w0, w1, w2, lsr #5 ⸩, maskNone) := by
  rfl

example : armShiftedAlu? 64 (.and _) (.reg .X1) (.reg .X2) .asr 9 (.reg .X0) =
    some (⸨prog| and x0, x1, x2, asr #9 ⸩, maskNone) := by
  rfl

example : armShiftedAlu? 64 (.or _) (.reg .X1) (.reg .X2) .lsl 0 (.reg .X0) =
    some (⸨prog| orr x0, x1, x2, lsl #0 ⸩, maskNone) := by
  rfl

example : armShiftedAlu? 64 (.xor _) (.reg .X1) (.reg .X2) .lsr 63 (.reg .X0) =
    some (⸨prog| eor x0, x1, x2, lsr #63 ⸩, maskNone) := by
  rfl

-- Negative boundary checks: k >= w, invalid widths, invalid opcodes, and .SP operands
example :
    (armShiftedAlu? 32 (.add _) (.reg .X1) (.reg .X2) .lsl 32 (.reg .X0)).isNone &&
    (armShiftedAlu? 32 (.sub _) (.reg .X1) (.reg .X2) .lsr 33 (.reg .X0)).isNone &&
    (armShiftedAlu? 64 (.and _) (.reg .X1) (.reg .X2) .asr 64 (.reg .X0)).isNone &&
    (armShiftedAlu? 64 (.or  _) (.reg .X1) (.reg .X2) .lsl 99 (.reg .X0)).isNone &&
    (armShiftedAlu? 8  (.add _) (.reg .X1) (.reg .X2) .lsl 1  (.reg .X0)).isNone &&
    (armShiftedAlu? 16 (.xor _) (.reg .X1) (.reg .X2) .asr 3  (.reg .X0)).isNone &&
    (armShiftedAlu? 64 (.mul _) (.reg .X1) (.reg .X2) .lsl 2  (.reg .X0)).isNone &&
    (armShiftedAlu? 32 (.shl _) (.reg .X1) (.reg .X2) .lsl 2  (.reg .X0)).isNone &&
    (armShiftedAlu? 64 (.lshr _) (.reg .X1) (.reg .X2) .lsr 2 (.reg .X0)).isNone &&
    (armShiftedAlu? 32 (.ashr _) (.reg .X1) (.reg .X2) .asr 2 (.reg .X0)).isNone &&
    (armShiftedAlu? 64 (.add _) .SP (.reg .X2) .lsl 1 (.reg .X0)).isNone &&
    (armShiftedAlu? 64 (.add _) (.reg .X1) .SP .lsl 1 (.reg .X0)).isNone &&
    (armShiftedAlu? 64 (.add _) (.reg .X1) (.reg .X2) .lsl 1 .SP).isNone = true := by
  rfl

/-- Witness that 32-bit `armShiftedAlu?` clears upper 32 bits of `rd` on concrete inputs. -/
theorem witness_add_w32_zero_upper (h : Host) (s : MachineData)
    (ha : armMach.getGpr s (.reg .X1) = 0xaaaa_bbbb_0000_1234#64)
    (hb : armMach.getGpr s (.reg .X2) = 0xcccc_dddd_0000_000f#64)
    (post : MachineState → Prop) :
    armMach.FallsTo armCondReads h 1
      [armShiftedAluDirI .add .W32 .X0 .X1 .X2 .lsl 4]
      (.reg .X0 :: armScratch) [] maskNone s
      (fun s' =>
        armMach.getGpr s' (.reg .X0) = 0x0000_0000_0000_1324#64 ∧
        armMach.mem s' = armMach.mem s)
      post := by
  have hspec := armShiftedAlu_zero32 h (steps := 1) (.add _) (.reg .X1) (.reg .X2) .lsl 4
    (.reg .X0) [armShiftedAluDirI .add .W32 .X0 .X1 .X2 .lsl 4] maskNone (by rfl) s
    0x0000_1234#32 0x0000_000f#32
    (by rw [ha]; simp [GprHolds]) (by rw [hb]; simp [GprHolds]) post
  intro hinfix hcont
  refine hspec hinfix (fun s' ⟨hw, hmem, hfr⟩ hfr' => hcont s' ⟨?_, hmem⟩ hfr')
  simpa [OpCode.wp, lift2, ArmShiftOp.eval] using hw

/-- Witness that 64-bit `armShiftedAlu?` with `asr` matches arithmetic right shift. -/
theorem witness_xor_w64_asr (h : Host) (s : MachineData)
    (ha : armMach.getGpr s (.reg .X1) = 0x0000_0000_0000_00ff#64)
    (hb : armMach.getGpr s (.reg .X2) = 0x8000_0000_0000_0000#64)
    (post : MachineState → Prop) :
    armMach.FallsTo armCondReads h 1
      [armShiftedAluDirI .xor .W64 .X0 .X1 .X2 .asr 63]
      (.reg .X0 :: armScratch) [] maskNone s
      (fun s' =>
        GprHolds (armMach.getGpr s' (.reg .X0)) (.bits 64) 0xffff_ffff_ffff_ff00#64 ∧
        armMach.mem s' = armMach.mem s)
      post := by
  have hspec := armShiftedAlu_fallsTo_eval h (steps := 1)
    (c := .xor _) (op := .xor) (.reg .X1) (.reg .X2) .asr 63 (.reg .X0)
    [armShiftedAluDirI .xor .W64 .X0 .X1 .X2 .asr 63] maskNone (by rfl) (by rfl) s
    0x0000_0000_0000_00ff#64 0x8000_0000_0000_0000#64
    (by rw [ha]; simp [GprHolds]) (by rw [hb]; simp [GprHolds]) post
  intro hinfix hcont
  refine hspec hinfix (fun s' ⟨hhold, hmem⟩ hfr => hcont s' ⟨?_, hmem⟩ hfr)
  simpa [ArmShiftAluOp.eval, ArmShiftOp.eval] using hhold.holds

open LeanQbe.T.ProofKit in
check_std_axioms!
  LeanQbe.T.Arm64.armShiftedAluDir_wp
  LeanQbe.T.Arm64.armShiftedAlu_wp
  LeanQbe.T.Arm64.armShiftedAlu_spec
  LeanQbe.T.Arm64.armShiftedAlu_zero32
  LeanQbe.T.Arm64.armShiftedAlu_fallsTo_eval
  LeanQbeTest.T.Arm64ShiftIselTest.witness_add_w32_zero_upper
  LeanQbeTest.T.Arm64ShiftIselTest.witness_xor_w64_asr

end LeanQbeTest.T.Arm64ShiftIselTest
