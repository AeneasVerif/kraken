module

import LeanQbe.T.BinaryLayout
import LeanQbe.T.BinaryLayoutElab
import LeanQbe.T.Amd64.BinaryLayout
import Kraken.X64.WP.Control

set_option autoImplicit false

namespace LeanQbeTest.T.BinaryLayoutTest

private def sampleProg : _root_.Program :=
  [ .label "entry"
  , .jmpTo "step2"
  , .label "step2"
  , .jmpReg _root_.Reg.rax
  , .label "step3"
  , .ret
  ]

private def sampleSizes : Array Nat :=
  #[1, 5, 1, 2, 1, 1]

private theorem sampleSizes_pos : sampleSizes.all (· > 0) = true :=
  LeanQbe.T.all_pos_of_toList (by rfl)

private theorem sampleProg_small :
    LeanQbe.T.tableProgSmall sampleSizes sampleProg = true := by
  rfl

private theorem sampleProg_nodup :
    LeanQbe.T.labelsNodupBy LeanQbe.T.dirLabel? sampleProg = true := by
  rfl

@[reducible] private def sampleHost : _root_.Host :=
  LeanQbe.T.Amd64.x64HostOfBinary (Int64.ofInt 0x401000) sampleSizes sampleSizes_pos
    sampleProg sampleProg_small

attribute [local instance] sampleHost

private theorem sampleHost_prog :
    _root_.Host.prog = sampleProg :=
  LeanQbe.T.Amd64.x64HostOfBinary_prog (Int64.ofInt 0x401000) sampleSizes sampleSizes_pos
    sampleProg sampleProg_small

private theorem sampleHost_labelsUnique :
    _root_.Host.LabelsUnique :=
  LeanQbe.T.Amd64.x64HostOfBinary_labelsUnique (Int64.ofInt 0x401000) sampleSizes
    sampleSizes_pos sampleProg_small sampleProg_nodup

private theorem step_ok (s0 : _root_.MachineData) (ra : Int64)
    (R : _root_.DataMem → Prop)
    (hrax : s0.regs.get _root_.Reg.rax = (_root_.Host.addrOf 4).toBitVec)
    (hmem : s0.dmem =⋆ Eq (ra.toUInt64.At s0.regs.rsp.toBitVec) ⋆ R) :
    Eventually (_root_.step1 _root_.Host.exe)
      (fun st => st.pc = ra ∧ st.data.regs.rsp = s0.regs.rsp + 8)
      ⟨s0, _root_.Host.addrOf 0⟩ := by
  refine _root_.Host.eventually_of_interp_cps (i := 0) (by rfl) ?_
  simp only [Directive.interp, Effects.All]
  refine _root_.Host.eventually_jmp (i := 1) (k := 2) (L := "step2") (by rfl) (by rfl) ?_ ?_
  · intro j hj
    have hcases : j = 0 ∨ j = 1 := by omega
    rcases hcases with rfl | rfl <;> simp [sampleHost_prog, sampleProg]
  · refine _root_.Host.eventually_of_interp_cps (i := 2) (by rfl) ?_
    simp only [Directive.interp, Effects.All]
    refine _root_.Host.eventually_jmp_reg (i := 3) (r := _root_.Reg.rax)
      (tgt := _root_.Host.addrOf 4) (by rfl) hrax ?_
    refine _root_.Host.eventually_of_interp_cps (i := 4) (by rfl) ?_
    simp only [Directive.interp, Effects.All]
    refine _root_.Host.eventually_ret (i := 5) (ra := ra) (R := R) (by rfl) hmem ?_
    exact Eventually.done _ ⟨rfl, rfl⟩

/-- info:
'_private.LeanQbeTest.T.BinaryLayoutTest.0.LeanQbeTest.T.BinaryLayoutTest.step_ok'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms step_ok

end LeanQbeTest.T.BinaryLayoutTest
