module

public import LeanQbe.T.Examples.Kissat.KissatCertCommon
public import LeanQbe.T.Arm64.TargLemmas

/-!
# AAPCS64 Arm64 `ArchKissatAbi` Instance (`Arm64.KissatAbi`)

Connects `LeanQbe.T.Examples.Kissat.KissatCertCommon.ArchKissatAbi` to `armTarget`, `armLayout`,
`armLegalTarget`, `armLabelClean`, and `armInit`. Reducible so concrete Kraken-AArch64 theorem
statements unify definitionally without unfolding overhead.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Arm64

open Std Std.ExtHashMap LeanQbe.T LeanQbe.T.Examples.Kissat.KissatCertCommon Kraken

/-- Concrete AAPCS64 Arm64 instance of `ArchKissatAbi` over `armTarget` and `armInit`. -/
@[expose, reducible] def arm64KissatAbi : ArchKissatAbi where
  T := armTarget
  L := armLayout
  lt := armLegalTarget
  hcl := armLabelClean
  init := armInit
  args5Ok s a0 a1 a2 a3 a4 :=
    (s.regs.getXReg .X0).toBitVec = a0 ∧ (s.regs.getXReg .X1).toBitVec = a1 ∧
      (s.regs.getXReg .X2).toBitVec = a2 ∧ (s.regs.getXReg .X3).toBitVec = a3 ∧
      (s.regs.getXReg .X4).toBitVec = a4
  stackPre s ra := s.regs.X30 = ra.toUInt64 ∧ s.regs.SP.toNat % 16 = 0
  entryFrame s _ b := region (s.regs.SP.toBitVec - BitVec.ofNat 64 b) b
  exitFrame s b := region (s.regs.SP.toBitVec - BitVec.ofNat 64 b) b
  calleeSpOk s s' :=
    (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
      s'.regs.getXReg r = s.regs.getXReg r) ∧ s'.regs.SP = s.regs.SP
  retGpr s := (s.regs.getXReg .X0).toBitVec
  argsIn_of_args5 h :=
    ⟨_, rfl,
      .cons ⟨by decide, by dsimp only [get_reg]; exact h.1⟩
        (.cons ⟨by decide, by dsimp only [get_reg]; exact h.2.1⟩
          (.cons ⟨by decide, by dsimp only [get_reg]; exact h.2.2.1⟩
            (.cons ⟨by decide, by dsimp only [get_reg]; exact h.2.2.2.1⟩
              (.cons ⟨by decide, by dsimp only [get_reg]; exact h.2.2.2.2⟩ .nil))))⟩
  raReg_spEntry_of_stackPre h := by
    refine ⟨?_, ?_⟩
    · change _ = _; exact congrArg UInt64.toBitVec h.1
    · exact h.2
  entry_of_entryFrame h := by
    dsimp only [Target.Entry, armTarget, armFrameTarget, armFramePreds, get]
    simp only [region_zero, Std.ExtHashMap.sep_emp]
    exact h
  entryFrame_of_entry h := by
    dsimp only [Target.Entry, armTarget, armFrameTarget, armFramePreds, get] at h
    simp only [region_zero, Std.ExtHashMap.sep_emp] at h
    exact h
  exitFrame_of_exit h := by
    dsimp only [Target.Exit, armTarget, armFrame, get] at h
    simp only [Nat.add_zero] at h
    exact h
  calleeSpOk_of_restored {s s'} h := by
    refine ⟨fun r hr => ?_, ?_⟩
    · have hreg := h.1 (.reg r) (by simp at hr ⊢; omega)
      exact UInt64.toBitVec_inj.mp hreg
    · have hsp : get s' .SP = get s .SP := by simpa [armFrame] using h.2
      exact UInt64.toBitVec_inj.mp hsp
  retGpr_eq_of_retsIn h := armInit.retsIn_singleton _ _ h
  init_args5 b bs a0 a1 a2 a3 a4 := by
    obtain ⟨locs, hlocs, hrel⟩ :=
      armInit.argsIn b bs (as := [i64, i64, i64, i64, i64]) (a0, a1, a2, a3, a4, ()) (by decide)
    change some (AbiReg.gpr (.reg .X0), AbiReg.gpr (.reg .X1), AbiReg.gpr (.reg .X2),
      AbiReg.gpr (.reg .X3), AbiReg.gpr (.reg .X4), ()) = some locs at hlocs
    injection hlocs with hlocs
    subst hlocs
    cases hrel with | cons h1 hrel =>
    cases hrel with | cons h2 hrel =>
    cases hrel with | cons h3 hrel =>
    cases hrel with | cons h4 hrel =>
    cases hrel with | cons h5 _ =>
    exact ⟨h1.2.trans (by simp), h2.2.trans (by simp), h3.2.trans (by simp),
      h4.2.trans (by simp), h5.2.trans (by simp)⟩
  init_stackPre := fun b bs {as} args => by
    refine ⟨?_, ?_⟩
    · have hra := armInit.raReg b bs args
      change ((armInit.initState b bs args).regs.X30).toBitVec = armInit.ra0.toBitVec at hra
      exact UInt64.toBitVec_inj.mp hra
    · have hsp := armInit.spEntry
      rw [← armInit.get_sp b bs args] at hsp
      exact hsp

end LeanQbe.T.Arm64
