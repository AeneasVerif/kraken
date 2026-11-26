module

public import LeanQbe.T.Vll.AsmArm64Lemmas
import Kraken.AArch64.Parser
import LeanQbe.T.Logic.MemLemmas
meta import Lean
meta import LeanQbe.T.Vll.Arm64
meta import LeanQbe.T.Vll.AsmArm64
meta import LeanQbe.T.Vll.AsmArm64Lemmas

/-!
# Verification Suite for AArch64 `BedrockMach` L1 (`VllAsmArm64Test`)

Checks `vllFrameTarget`, `Kraken.AArch64.Parser` encodings, end-to-end execution proofs
(`progStraight`, `progControl`), `#print axioms`, and MetaM `importModules`/`collectAxioms`/
`ci.isUnsafe` audits (confirming `0` `Amd64`/`Kraken.X64` leaks).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.VllAsmArm64Test

open LeanQbe.T
open LeanQbe.T.Arm64
open LeanQbe.T.Vll

/-! ## 1. `vllFrameTarget` Instantiation & Parser Encoding Checks -/

/-- Generic `FrameTarget` instantiated automatically from `arm64Arch_wf`. -/
def arm64FrameTarget :
    FrameTarget (vllMach arm64Arch) (vllFrameIsa arm64Arch) arm64Arch.condReads :=
  vllFrameTarget arm64Arch arm64Arch_wf

section ParserChecks
open Kraken.AArch64.Parser
example : ⸨prog| nop ⸩ = asmArm64 (.pad .btiJC) := rfl
example : ⸨prog| adrp x0, f
  add x0, x0, :lo12:f ⸩ = asmArm64 (.symAddr "f" (.reg .X0)) := rfl
example : ⸨prog| bl f ⸩ = asmArm64 (.call "f") := rfl
example : ⸨prog| blr x8 ⸩ = asmArm64 (.icall (.reg .X8)) := rfl
example : ⸨prog| br x8 ⸩ = asmArm64 (.tailJmpR (.reg .X8)) := rfl
example : ⸨prog| br x9 ⸩ = asmArm64 (.ijmp (.reg .X9)) := rfl
example : ⸨prog| ret ⸩ = asmArm64 .ret := rfl
example : ⸨prog| uxtb w16, w0
  cbnz w16, tgt ⸩ = asmArm64 (.jnzGpr (.reg .X0) "tgt") := rfl
example : ⸨prog| sub sp, sp, #16
  str x30, [sp, #8] ⸩ = asmArm64 (.prologue 1) := rfl
example : ⸨prog| ldr x30, [sp, #8]
  add sp, sp, #16 ⸩ = asmArm64 (.epilogue 1) := rfl
example : ⸨prog| str x0, [sp, #0] ⸩ = asmArm64 (.slotSt 0 (.reg .X0)) := rfl
example : ⸨prog| ldr x1, [sp, #0] ⸩ = asmArm64 (.slotLd (.reg .X1) 0) := rfl
example : ⸨prog| adds x0, x0, #5 ⸩ =
    asmArm64 (.alu .add .w64 (.reg .X0) (.reg .X0) (.imm 5#64) true) := rfl
example : asmArm64 (.native (ins (w := .W64) .NOP)) = [ins (w := .W64) .NOP] := rfl
end ParserChecks

/-! ## 2. Uniform 4-Byte Concrete AArch64 Layout & End-to-End Execution Proofs -/

@[expose, instance_reducible] def armUniformLayout : _root_.Layout where
  start := 0x10000
  instrSize _ := 4
  instrSize_pos _ := by decide

@[expose] def progStraightBody : List (Instr arm64Arch) :=
  [ .label "f", .pad .btiJC, .prologue 1, .movi (.reg .X0) 0x1FF#64
  , .alu .add .w8 (.reg .X1) (.reg .X0) (.imm 1#64) true
  , .setcc (.reg .X2) .eq, .slotSt 0 (.reg .X2), .slotLd (.reg .X3) 0
  , .canonAbi i8 (.reg .X0)
  , .native (ins (.ADD_e (.low (.reg .X0) .W64) (.low (.reg .X0) .W64)
      (.imm { imm := .int64 1, shift := .S0 })))
  , .alu .add .w64 (.reg .X0) (.reg .X0) (.reg (.reg .X3)) false
  , .epilogue 1 ]

@[expose] def progStraight : List (Instr arm64Arch) := progStraightBody ++ [.ret]
@[expose, instance_reducible] def hostStraight : Host :=
  Host.ofLayout (asmArm64List progStraight) armUniformLayout (by decide)

theorem progStraight_runs (sv : MachSt arm64Arch) (sm : MachineData)
    (hrel : arm64StateRel sv sm) (hsp : (sv.gpr .SP).toNat % 16 = 0)
    (hraSlot : storeOk sv.mem i64 (sv.gpr .SP - 16#64 + 8#64)) :
    let ra := sv.gpr (.reg .X30)
    let m1 := storeMem sv.mem i64 (sv.gpr .SP - 16#64 + 8#64) ra
    let m2 := storeMem m1 i64 (sv.gpr .SP - 16#64) 1#64
    storeOk m1 i64 (sv.gpr .SP - 16#64) →
    loadVal m2 i64 (sv.gpr .SP - 16#64) = some 1#64 →
    loadVal m2 i64 (sv.gpr .SP - 16#64 + 8#64) = some ra →
    armMach.Run hostStraight 0 sm (fun st =>
      st.pc = Int64.ofBitVec ra ∧
      Arm64.get st.data (.reg .X0) = 257#64 ∧
      Arm64.get st.data (.reg .X1) = 0#64 ∧
      Arm64.get st.data (.reg .X3) = 1#64 ∧
      Arm64.get st.data .SP = sv.gpr .SP) := by
  intro ra m1 m2 hst0' hld0 hldRa
  letI : Host := hostStraight
  let sym := hostSymAddr hostStraight
  have hsp1 : (sv.gpr .SP - 16#64).toNat % 16 = 0 := by rw [BitVec.toNat_sub]; simp; omega
  -- Build `ExecBodyOk` directly along `progStraightBody`
  let s1 := ((sv.setGpr .SP (sv.gpr .SP - 16#64)).setMem m1).setFlags sv.flags
  let s2 := s1.setGpr (.reg .X0) 0x1FF#64
  let f3 := arm64AluFlags .add .w8 true 0xFF#8 1#8 s2.flags
  let s3 := (s2.setGprW .w8 (.reg .X1) (0xFF#8 + 1#8)).setFlags f3
  have hf3_eq : ArmCond.eq.interp f3 = true := by
    simp only [f3, arm64AluFlags, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    decide
  let s4 := s3.setGprW .w8 (.reg .X2) 1#8
  let s5 := s4.setMem m2
  let s6 := s5.setGpr (.reg .X3) 1#64
  let s7 := s6.setGpr (.reg .X0) 0xFF#64
  let s8 := s7.setGpr (.reg .X0) 256#64
  let s9 := s8.setGpr (.reg .X0) 257#64
  let s10 := ((s9.setGpr (.reg .X30) ra).setGpr .SP (sv.gpr .SP)).setFlags s9.flags
  have hnatStep : arm64NativeStep
      (ins (.ADD_e (.low (.reg .X0) .W64) (.low (.reg .X0) .W64)
        (.imm { imm := .int64 1, shift := .S0 }))) sym s7 (.fall s8) := by
    intro p
    simp only [Directive.interp, Instr.interp, Operation.interp, ExtOrImmReg.interp,
      ConstExpr.interp, MachineData.setRegOrSp, Reg64s.setRegOrSp, Reg64s.setRegOrSp64,
      Reg64s.getRegOrSp_reg64, RegWidth.bits, Effects.All, machDataToVll, vllToMachData]
    congr 1
    · funext r
      cases r with
      | SP => rfl
      | reg x => cases x <;> simp [s7, s6, s5, s4, s3, s2, s1, Arm64.get, Reg64s.getRegOrSp64,
          Reg64s.getXReg, Reg64s.setXReg, vllToReg64s, MachSt.setGpr]
    · funext v; exact v.elim
  have hbody : ExecBodyOk sym progStraightBody sv s10 := by
    refine .cons (s₁ := sv) ⟨⟨by simp [Instr.uses], trivial⟩, trivial⟩ rfl ?_
    refine .cons (s₁ := sv) ⟨⟨by simp [Instr.uses], trivial⟩, trivial⟩ rfl ?_
    refine .cons (s₁ := s1)
      ⟨⟨by simp [Instr.uses, Abi.raRegs, RaKind.raRegs, armScratch], trivial⟩, hsp⟩
      ⟨hraSlot, by rfl⟩ ?_
    refine .cons (s₁ := s2) ⟨⟨by simp [Instr.uses], trivial⟩, trivial⟩ rfl ?_
    refine .cons (s₁ := s3) ⟨⟨by simp [Instr.uses, Src.regs, armScratch], trivial⟩, trivial⟩
      (by
        have hx0 : s2.gpr (.reg .X0) = 0x1FF#64 := by simp [s2]
        dsimp only [instrRel]; rw [hx0]; rfl) ?_
    refine .cons (s₁ := s4) ⟨⟨by simp [Instr.uses], trivial⟩, trivial⟩
      (by
        dsimp only [instrRel, arm64Arch]
        change InstrOut.fall s4 =
          InstrOut.fall (s3.setGprW .w8 (.reg .X2) (BitVec.ofNat 8 (ArmCond.eq.interp f3).toNat))
        rw [hf3_eq]; rfl) ?_
    refine .cons (s₁ := s5) ⟨⟨by simp [Instr.uses, armScratch], trivial⟩,
        by dsimp only [arm64InstrDynOk]
           rw [show s4.gpr .SP = sv.gpr .SP - 16#64 by simp [s4, s3, s2, s1]]; exact hsp1⟩
      ⟨by simpa [s4, s3, s2, s1, BitVec.add_zero] using hst0',
        by dsimp only [s5]; congr 1; simp [s4, s3, s2, s1, m2, writeSubZeroExtend, BitVec.add_zero]⟩
      ?_
    refine .cons (s₁ := s6) ⟨⟨by simp [Instr.uses, armScratch], trivial⟩,
        by dsimp only [arm64InstrDynOk]
           rw [show s5.gpr .SP = sv.gpr .SP - 16#64 by simp [s5, s4, s3, s2, s1]]; exact hsp1⟩
      ⟨1#64, by simpa [s5, s4, s3, s2, s1, BitVec.add_zero] using hld0, rfl⟩ ?_
    refine .cons (s₁ := s7) ⟨⟨by simp [Instr.uses, armScratch], by simp⟩, trivial⟩
      (by
        have hx0 : s6.gpr (.reg .X0) = 0x1FF#64 := by simp [s6, s5, s4, s3, s2]
        simp [instrRel, s7, hx0, canonAbiVal, MachSt.setGpr, MachSt.setFlags]) ?_
    refine .cons (s₁ := s8) ⟨⟨by simp [Instr.uses, arm64NativeEffect, opNativeEffect, regOfSp,
        extOrImmUses, armScratch]; decide, trivial⟩, trivial⟩ ⟨.fall s8, hnatStep, rfl⟩ ?_
    refine .cons (s₁ := s9) ⟨⟨by simp [Instr.uses, Src.regs, armScratch], trivial⟩, trivial⟩
      (by
        have hx0 : s8.gpr (.reg .X0) = 256#64 := by simp [s8]
        have hx3 : s8.gpr (.reg .X3) = 1#64 := by simp [s8, s7, s6]
        simp [instrRel, s9, hx0, hx3, CoreAlu.eval, Src.evalW, Src.eval, arm64AluFlags,
          writeSubZeroExtend, MachSt.setGpr, MachSt.setGprW, MachSt.setFlags]) ?_
    have hsp9 : s9.gpr .SP = sv.gpr .SP - 16#64 := by simp [s9, s8, s7, s6, s5, s4, s3, s2, s1]
    refine .cons (s₁ := s10) ⟨⟨by simp [Instr.uses, armScratch], trivial⟩,
        by dsimp only [arm64InstrDynOk]; rw [hsp9]; exact hsp1⟩
      ⟨ra, by simpa [s9, s8, s7, s6, s5, s4, s3, s2, s1] using hldRa, by
        have hcan : sv.gpr .SP - 16#64 + 16#64 = sv.gpr .SP := by
          apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add, BitVec.toNat_sub]; simp; omega
        dsimp only [s10]; rw [hsp9]
        change InstrOut.fall _ = InstrOut.fall (((s9.setGpr (.reg .X30) ra).setGpr .SP
          (sv.gpr .SP - 16#64 + 16#64)).setFlags s9.flags)
        rw [hcan]⟩ .nil
  have hinf : (asmArm64List progStraightBody ++ asmArm64 .ret).IsInfixAt
      (armMach.prog hostStraight) 0 := by
    have heq : armMach.prog hostStraight = asmArm64List progStraightBody ++ asmArm64 .ret := by
      show asmArm64List (progStraightBody ++ [.ret]) = _
      rw [asmArm64List_append]; simp [asmArm64List]
    rw [heq]; exact ⟨[], by simp⟩
  obtain ⟨hinfB, hinfR⟩ := List.IsInfixAt.append hinf
  refine asmArm64List_fallsTo (h := hostStraight) (k := 0) hbody hrel hinfB ?_
  intro sm1 hrel1 _
  refine asmArm64_jump (h := hostStraight) (k := (asmArm64List progStraightBody).length)
    (i := .ret) (sv := s10) (sv' := s10) (pc' := ra)
    (by simpa using hinfR)
    ⟨⟨by simp [Instr.uses, Abi.raRegs, RaKind.raRegs, armScratch], trivial⟩, trivial⟩
    hrel1 (by simp [instrRel, s10]) ?_
  intro sm2 hrel2 _
  refine Eventually.done _ ⟨rfl, ?_, ?_, ?_, ?_⟩
  · simpa [s10, s9, s8, s7, s6, s5, s4, s3, s2, s1] using hrel2.1 (.reg .X0) (by simp [armScratch])
  · simpa [s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, writeSubZeroExtend] using
      hrel2.1 (.reg .X1) (by simp [armScratch])
  · simpa [s10, s9, s8, s7, s6, s5, s4, s3, s2, s1] using hrel2.1 (.reg .X3) (by simp [armScratch])
  · simpa [s10, s9, s8, s7, s6, s5, s4, s3, s2, s1] using hrel2.1 .SP (by simp [armScratch])

/-- Control-flow VLL program exercising `symAddr`, `icall`, `jnzGpr` on `0x02#64`, `call`/`ret`,
`tailJmpR`, `ijmp`, and `pad`, verifying exact `ρ` (`asmArm64Offset`) label preservation. -/
@[expose] def progControl : List (Instr arm64Arch) :=
  [ .label "entry"                   -- idx 0
  , .symAddr "callee" (.reg .X8)     -- idx 1
  , .icall (.reg .X8)                -- idx 2
  , .symAddr "tail" (.reg .X9)       -- idx 3 (return target of `icall`)
  , .tailJmpR (.reg .X9)             -- idx 4
  , .label "callee"                  -- idx 5
  , .pad .btiJC                      -- idx 6
  , .movi (.reg .X1) 0x02#64         -- idx 7 (bit 0 = 0, low byte != 0!)
  , .jnzGpr (.reg .X1) "nz"          -- idx 8
  , .label "nz"                      -- idx 9
  , .mov .w64 (.reg .X19) (.reg .X30) -- idx 10 (save `icall` return addr in callee-saved x19)
  , .call "leaf"                     -- idx 11
  , .mov .w64 (.reg .X30) (.reg .X19) -- idx 12 (restore `icall` return addr)
  , .ret                             -- idx 13 (return to idx 3!)
  , .label "leaf"                    -- idx 14
  , .alu .add .w64 (.reg .X0) (.reg .X0) (.imm 10#64) false -- idx 15
  , .ret                             -- idx 16 (return to idx 12!)
  , .label "tail"                    -- idx 17
  , .symAddr "done" (.reg .X10)      -- idx 18
  , .ijmp (.reg .X10)                -- idx 19
  , .label "done" ]                  -- idx 20

@[expose, instance_reducible] def hostControl : Host :=
  Host.ofLayout (asmArm64List progControl) armUniformLayout (by decide)

theorem progControl_labelsUnique : @Host.LabelsUnique hostControl :=
  letI := hostControl
  asmArm64List_labelsUnique progControl rfl (fun d hm => by simp [progControl] at hm) (by decide)

theorem progControl_runs (sv : MachSt arm64Arch) (sm : MachineData)
    (hrel : arm64StateRel sv sm) :
    letI := hostControl
    armMach.Run hostControl (asmArm64Offset progControl 0) sm (fun st =>
      st.pc = Host.addrOf (asmArm64Offset progControl 20) ∧
      Arm64.get st.data (.reg .X0) = sv.gpr (.reg .X0) + 10#64) := by
  letI : Host := hostControl
  let sym := hostSymAddr hostControl
  have huniq := progControl_labelsUnique
  have hLab : ∀ (k : Nat) (l : Sym), progControl[k]? = some (.label l) →
      Int64.ofBitVec (sym l) = Host.addrOf (asmArm64Offset progControl k) := fun k l hk => by
    have h1 := asmArm64List_label_addr progControl rfl huniq hk
    simpa [sym, hostSymAddr, armMach, hostLabel, Int64.ofBitVec_toBitVec] using h1
  have hInfix : ∀ (k : Nat) (ins : Instr arm64Arch), progControl[k]? = some ins →
      (asmArm64 ins).IsInfixAt (armMach.prog hostControl) (asmArm64Offset progControl k) :=
    fun k ins hk => asmArm64List_infixAt hk
  have hStepF : ∀ (k : Nat) (ins : Instr arm64Arch), progControl[k]? = some ins →
      asmArm64Offset progControl k + (asmArm64 ins).length =
        asmArm64Offset progControl (k + 1) := fun k ins hk => (asmArm64Offset_succ hk).symm
  have stepF : ∀ {k : Nat} {ins : Instr arm64Arch} {sv0 sv1 : MachSt arm64Arch}
      {sm0 : MachineData} {P : MachineState → Prop},
      progControl[k]? = some ins → arm64InstrOk ins sv0 → arm64StateRel sv0 sm0 →
      instrRel arm64Arch sym 0#64 ins sv0 (.fall sv1) →
      (∀ sm1, arm64StateRel sv1 sm1 → armMach.Run hostControl (asmArm64Offset progControl (k + 1))
        sm1 P) → armMach.Run hostControl (asmArm64Offset progControl k) sm0 P :=
    fun hk hok hr hst hc =>
      asmArm64_fallsTo (h := hostControl) hok hr hst (hInfix _ _ hk) fun sm1 hr1 _ => by
        rw [hStepF _ _ hk]; exact hc sm1 hr1
  have stepJ : ∀ {k : Nat} {ins : Instr arm64Arch} {sv0 sv1 : MachSt arm64Arch} {pc' : BitVec 64}
      {sm0 : MachineData} {P : MachineState → Prop},
      progControl[k]? = some ins → arm64InstrOk ins sv0 → arm64StateRel sv0 sm0 →
      instrRel arm64Arch sym
        (armMach.addrOf hostControl (asmArm64Offset progControl (k + 1))).toBitVec
        ins sv0 (.jump pc' sv1) →
      (∀ sm1, arm64StateRel sv1 sm1 → Eventually (armMach.step hostControl) P
        ⟨sm1, Int64.ofBitVec pc'⟩) →
      armMach.Run hostControl (asmArm64Offset progControl k) sm0 P :=
    fun hk hok hr hst hc =>
      asmArm64_jump (h := hostControl) (hInfix _ _ hk) hok hr (by rw [hStepF _ _ hk]; exact hst)
        fun sm1 hr1 _ => hc sm1 hr1
  let s1 := sv.setGpr (.reg .X8) (sym "callee")
  let raMain := (armMach.addrOf hostControl (asmArm64Offset progControl 3)).toBitVec
  let s2 := s1.setGpr (.reg .X30) raMain
  let s5 := s2.setGpr (.reg .X1) 0x02#64
  let s8 := s5.setGpr (.reg .X19) raMain
  let raLeaf := (armMach.addrOf hostControl (asmArm64Offset progControl 12)).toBitVec
  let s9 := s8.setGpr (.reg .X30) raLeaf
  let s11 := s9.setGpr (.reg .X0) (sv.gpr (.reg .X0) + 10#64)
  let s12 := s11.setGpr (.reg .X30) raMain
  let s13 := s12.setGpr (.reg .X9) (sym "tail")
  let s14 := s13.setGpr (.reg .X10) (sym "done")
  refine stepF (k := 0) rfl ⟨⟨by simp [Instr.uses], trivial⟩, trivial⟩ hrel rfl fun _ hrel1 => ?_
  refine stepF (k := 1) rfl ⟨⟨by simp [Instr.uses], trivial⟩, trivial⟩ hrel1 rfl fun _ hrel2 => ?_
  refine stepJ (k := 2) (sv1 := s2) (pc' := sym "callee") rfl
    ⟨⟨by simp [Instr.uses, armScratch], trivial⟩, trivial⟩ hrel2
    (by simp [instrRel, s2, s1, raMain]) fun _ hrel3 => ?_
  rw [hLab 5 "callee" rfl]
  refine stepF (k := 5) rfl ⟨⟨by simp [Instr.uses], trivial⟩, trivial⟩ hrel3 rfl fun _ hrel4 => ?_
  refine stepF (k := 6) rfl ⟨⟨by simp [Instr.uses], trivial⟩, trivial⟩ hrel4 rfl fun _ hrel5 => ?_
  refine stepF (k := 7) rfl ⟨⟨by simp [Instr.uses], trivial⟩, trivial⟩ hrel5 rfl fun _ hrel6 => ?_
  refine stepJ (k := 8) (sv1 := s5) (pc' := sym "nz") rfl
    ⟨⟨by simp [Instr.uses, armScratch], trivial⟩, trivial⟩ hrel6
    (by simp [instrRel, s5, MachSt.setGpr, MachSt.setFlags]) fun _ hrel7 => ?_
  rw [hLab 9 "nz" rfl]
  refine stepF (k := 9) rfl ⟨⟨by simp [Instr.uses], trivial⟩, trivial⟩ hrel7 rfl fun _ hrel8 => ?_
  refine stepF (k := 10) (sv1 := s8) rfl
    ⟨⟨by simp [Instr.uses, armScratch], trivial⟩, trivial⟩ hrel8
    (by
      have hlr : s5.gpr (.reg .X30) = raMain := by simp [s5, s2]
      simp [instrRel, hlr, s8, MachSt.setGprW, writeSubZeroExtend]) fun _ hrel9 => ?_
  refine stepJ (k := 11) (sv1 := s9) (pc' := sym "leaf") rfl
    ⟨⟨by simp [Instr.uses], trivial⟩, trivial⟩ hrel9
    (by simp [instrRel, s9, raLeaf]) fun _ hrel10 => ?_
  rw [hLab 14 "leaf" rfl]
  refine stepF (k := 14) rfl ⟨⟨by simp [Instr.uses], trivial⟩, trivial⟩ hrel10 rfl fun _ h11 => ?_
  refine stepF (k := 15) (sv1 := s11) rfl
    ⟨⟨by simp [Instr.uses, Src.regs, armScratch], trivial⟩, trivial⟩ h11
    (by
      have hx0 : s9.gpr (.reg .X0) = sv.gpr (.reg .X0) := by simp [s9, s8, s5, s2, s1]
      simp [instrRel, s11, hx0, CoreAlu.eval, Src.evalW, Src.eval, arm64AluFlags,
        writeSubZeroExtend, MachSt.setGpr, MachSt.setGprW, MachSt.setFlags]) fun _ hrel12 => ?_
  refine stepJ (k := 16) (sv1 := s11) (pc' := raLeaf) rfl
    ⟨⟨by simp [Instr.uses, Abi.raRegs, RaKind.raRegs, armScratch], trivial⟩, trivial⟩ hrel12
    (by simp [instrRel, s11, s9]) fun _ hrel13 => ?_
  rw [show Int64.ofBitVec raLeaf = Host.addrOf (asmArm64Offset progControl 12) from
    Int64.ofBitVec_toBitVec _]
  refine stepF (k := 12) (sv1 := s12) rfl
    ⟨⟨by simp [Instr.uses, armScratch], trivial⟩, trivial⟩ hrel13
    (by
      have hx19 : s11.gpr (.reg .X19) = raMain := by simp [s11, s9, s8]
      simp [instrRel, hx19, s12, MachSt.setGprW, writeSubZeroExtend]) fun _ hrel14 => ?_
  refine stepJ (k := 13) (sv1 := s12) (pc' := raMain) rfl
    ⟨⟨by simp [Instr.uses, Abi.raRegs, RaKind.raRegs, armScratch], trivial⟩, trivial⟩ hrel14
    (by simp [instrRel, s12]) fun _ hrel15 => ?_
  rw [show Int64.ofBitVec raMain = Host.addrOf (asmArm64Offset progControl 3) from
    Int64.ofBitVec_toBitVec _]
  refine stepF (k := 3) rfl ⟨⟨by simp [Instr.uses], trivial⟩, trivial⟩ hrel15 rfl fun _ hrel16 => ?_
  refine stepJ (k := 4) (sv1 := s13) (pc' := sym "tail") rfl
    ⟨⟨by simp [Instr.uses, armScratch], trivial⟩, trivial⟩ hrel16
    (by simp [instrRel, s13]) fun _ hrel17 => ?_
  rw [hLab 17 "tail" rfl]
  refine stepF (k := 17) rfl ⟨⟨by simp [Instr.uses], trivial⟩, trivial⟩ hrel17 rfl fun _ h18 => ?_
  refine stepF (k := 18) rfl ⟨⟨by simp [Instr.uses], trivial⟩, trivial⟩ h18 rfl fun _ hrel19 => ?_
  refine stepJ (k := 19) (sv1 := s14) (pc' := sym "done") rfl
    ⟨⟨by simp [Instr.uses, armScratch], trivial⟩, trivial⟩ hrel19
    (by simp [instrRel, s14]) fun _ hrel20 => ?_
  rw [hLab 20 "done" rfl]
  refine Eventually.done _ ⟨rfl, ?_⟩
  simpa [s14, s13, s12, s11, s9, s8, s5, s2, s1] using hrel20.1 (.reg .X0) (by simp [armScratch])

/-! ## 3. `#print axioms` Checks (`⊆ [propext, Classical.choice, Quot.sound]`) -/

#print axioms LeanQbe.T.Vll.arm64Arch_wf
#print axioms LeanQbe.T.Vll.arm64Arch_nativeEffectSound
#print axioms LeanQbe.T.Vll.asmArm64List_definedLabels
#print axioms LeanQbe.T.Vll.asmArm64List_label_addr
#print axioms LeanQbe.T.Vll.asmArm64_fallsTo
#print axioms LeanQbe.T.Vll.asmArm64List_fallsTo
#print axioms LeanQbe.T.Vll.asmArm64_jump
#print axioms LeanQbeTest.T.VllAsmArm64Test.progStraight_runs
#print axioms LeanQbeTest.T.VllAsmArm64Test.progControl_runs

/-! ## 4. MetaM `importModules` Isolation, `collectAxioms`, and `ci.isUnsafe` Audit -/

meta section
open Lean

private def allowedStdAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]
private def isForbiddenX64Mod (m : Name) : Bool :=
  (m.toString.splitOn "Amd64").length > 1 || m.toString.startsWith "Kraken.X64"

#eval show MetaM Unit from do
  for modName in [`LeanQbe.T.Vll.Arm64, `LeanQbe.T.Vll.AsmArm64,
      `LeanQbe.T.Vll.AsmArm64Lemmas0, `LeanQbe.T.Vll.AsmArm64Lemmas] do
    let env ← importModules #[{ module := modName }] {}
    let bad := env.header.moduleNames.filter isForbiddenX64Mod
    if !bad.isEmpty then throwError "{modName} imports Amd64/X64: {bad.toList}"
  let testBad := (← getEnv).header.moduleNames.filter isForbiddenX64Mod
  if !testBad.isEmpty then throwError "VllAsmArm64Test imports Amd64/X64: {testBad.toList}"
  let env ← getEnv
  let targets : List Name :=
    [ ``LeanQbe.T.Vll.arm64Arch, ``LeanQbe.T.Vll.arm64Arch_wf
    , ``LeanQbe.T.Vll.arm64Arch_nativeEffectSound, ``LeanQbe.T.Vll.asmArm64
    , ``LeanQbe.T.Vll.asmArm64List, ``LeanQbe.T.Vll.asmArm64Offset
    , ``LeanQbe.T.Vll.asmArm64_noLab, ``LeanQbe.T.Vll.asmArm64List_definedLabels
    , ``LeanQbe.T.Vll.asmArm64List_labelsUnique, ``LeanQbe.T.Vll.asmArm64List_label_addr
    , ``LeanQbe.T.Vll.asmArm64_fallsTo, ``LeanQbe.T.Vll.asmArm64List_fallsTo
    , ``LeanQbe.T.Vll.asmArm64_jump, ``LeanQbeTest.T.VllAsmArm64Test.progStraight_runs
    , ``LeanQbeTest.T.VllAsmArm64Test.progControl_runs ]
  for nm in targets do
    let axs ← Lean.collectAxioms nm
    let badAx := axs.filter fun a => !allowedStdAxioms.contains a
    if !badAx.isEmpty then throwError "Disallowed axioms for {nm}: {badAx.toList}"
    match env.find? nm with
    | some ci => if ci.isUnsafe then throwError "Declaration {nm} failed isUnsafe check"
    | none => throwError "Declaration {nm} not found"

end

end LeanQbeTest.T.VllAsmArm64Test
