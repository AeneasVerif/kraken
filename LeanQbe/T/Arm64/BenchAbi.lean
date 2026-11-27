module

public import LeanQbe.T.BenchmarkCertKit
public import LeanQbe.T.Arm64.TargLemmas

/-!
# AAPCS64 Arm64 `BenchAbi` Instance (`Arm64.BenchAbi`)

Connects `LeanQbe.T.BenchmarkCertKit.BenchAbi` to `armTarget`, `armLayout`, `armLegalTarget`,
`armLabelClean`, and `armInit`. Marked `@[expose, reducible]` so concrete Kraken-AArch64 theorem
statements unify definitionally without unfolding overhead.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Arm64

open Std Std.ExtHashMap LeanQbe.T LeanQbe.T.BenchmarkCertKit Kraken

/-- Read the `i`-th AAPCS64 `i64` argument GPR (`X0..X5`) as a 64-bit `BitVec`. -/
@[expose, reducible] def armArgAt (i : Fin 6) (s : MachineData) : BitVec 64 :=
  match i.1 with
  | 0 => (s.regs.getXReg .X0).toBitVec
  | 1 => (s.regs.getXReg .X1).toBitVec
  | 2 => (s.regs.getXReg .X2).toBitVec
  | 3 => (s.regs.getXReg .X3).toBitVec
  | 4 => (s.regs.getXReg .X4).toBitVec
  | _ => (s.regs.getXReg .X5).toBitVec

/-- Concrete AAPCS64 Arm64 instance of `BenchAbi` over `armTarget` and `armInit`. -/
@[expose, reducible] def arm64BenchAbi : BenchAbi where
  T := armTarget
  L := armLayout
  lt := armLegalTarget
  hcl := armLabelClean
  init := armInit
  legalSig_i64 := rfl
  assignArgs_i64 n hn := by
    rcases n with _ | _ | _ | _ | _ | _ | _ | n <;> first | decide | omega
  argAt := armArgAt
  stackPre s ra := s.regs.X30 = ra.toUInt64 ∧ s.regs.SP.toNat % 16 = 0
  exitSpOk st := st.regs.SP.toNat % 16 = 0
  entryFrame s _ b := region (s.regs.SP.toBitVec - BitVec.ofNat 64 b) b
  exitFrame s b := region (s.regs.SP.toBitVec - BitVec.ofNat 64 b) b
  initExitFrame b := region (0x1000#64 - BitVec.ofNat 64 b) b
  calleeSavedOk s s' :=
    ∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
      s'.regs.getXReg r = s.regs.getXReg r
  spRestored s s' := s'.regs.SP = s.regs.SP
  retGpr s := (s.regs.getXReg .X0).toBitVec
  argsIn_1 h0 := ⟨_, rfl, .cons ⟨by decide, by dsimp only [get_reg]; exact h0⟩ .nil⟩
  argsIn_2 h0 h1 :=
    ⟨_, rfl, .cons ⟨by decide, by dsimp only [get_reg]; exact h0⟩
      (.cons ⟨by decide, by dsimp only [get_reg]; exact h1⟩ .nil)⟩
  argsIn_3 h0 h1 h2 :=
    ⟨_, rfl, .cons ⟨by decide, by dsimp only [get_reg]; exact h0⟩
      (.cons ⟨by decide, by dsimp only [get_reg]; exact h1⟩
        (.cons ⟨by decide, by dsimp only [get_reg]; exact h2⟩ .nil))⟩
  argsIn_5 h0 h1 h2 h3 h4 :=
    ⟨_, rfl, .cons ⟨by decide, by dsimp only [get_reg]; exact h0⟩
      (.cons ⟨by decide, by dsimp only [get_reg]; exact h1⟩
        (.cons ⟨by decide, by dsimp only [get_reg]; exact h2⟩
          (.cons ⟨by decide, by dsimp only [get_reg]; exact h3⟩
            (.cons ⟨by decide, by dsimp only [get_reg]; exact h4⟩ .nil))))⟩
  argsIn_6 h0 h1 h2 h3 h4 h5 :=
    ⟨_, rfl, .cons ⟨by decide, by dsimp only [get_reg]; exact h0⟩
      (.cons ⟨by decide, by dsimp only [get_reg]; exact h1⟩
        (.cons ⟨by decide, by dsimp only [get_reg]; exact h2⟩
          (.cons ⟨by decide, by dsimp only [get_reg]; exact h3⟩
            (.cons ⟨by decide, by dsimp only [get_reg]; exact h4⟩
              (.cons ⟨by decide, by dsimp only [get_reg]; exact h5⟩ .nil)))))⟩
  raReg_spEntry_of_stackPre h := ⟨by change _ = _; exact congrArg UInt64.toBitVec h.1, h.2⟩
  entry_of_entryFrame h := by
    dsimp only [Target.Entry, armTarget, armFrameTarget, armFramePreds, get]
    simp only [region_zero, Std.ExtHashMap.sep_emp]
    exact h
  exitFrame_of_exit h := by
    dsimp only [Target.Exit, armTarget, armFrame, get] at h
    simp only [Nat.add_zero] at h
    exact h
  initExitFrame_of_exit {b m} h := by
    simpa only [Target.Exit, armTarget, armFrameTarget, armFramePreds, armFrame, armInit,
      Nat.add_zero] using h
  calleeSavedOk_of_restored {s s'} h r hr := by
    have hreg := h.1 (.reg r) (by simp at hr ⊢; omega)
    exact UInt64.toBitVec_inj.mp hreg
  spRestored_of_restored {s s'} h := by
    have hsp : get s' .SP = get s .SP := by simpa [armFrame] using h.2
    exact UInt64.toBitVec_inj.mp hsp
  retGpr_eq_of_retsIn h := by
    simpa [armInit, get_reg] using armInit.retsIn_singleton _ _ h
  arg0_eq_of_argsIn h := by
    simpa [armArgAt, armInit, get_reg] using armInit.argsIn_singleton _ _ h
  exitSpOk_of_spEntry h := h

end LeanQbe.T.Arm64
