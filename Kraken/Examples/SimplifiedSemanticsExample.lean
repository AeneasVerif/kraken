import Kraken.Tactics
import Kraken.Parser
import Kraken.Eval
import Kraken.SimplifiedSemantics

open Kraken.Parser
open Kraken.Simplified

-- This is the same as p2 in Examples, but without using Executable
def p2 : List Directive := [
  .label "start",
  .instr ⟨ .W64, .W64, .mov Reg.rax (.imm (.int64 1)) ⟩,
  .instr ⟨ .W64, .W64, .xor Reg.rax Reg.rax ⟩,
  .instr ⟨ .W64, .W64, .jcc .nz "start" ⟩,
  .instr ⟨ .W64, .W64, .mov Reg.rax (.imm (.int64 2)) ⟩,
]

-- Replicate the example using the simplified transition relation and polymorphic Eventually
example (s : MachineData) :
  Eventually (simplified_step1 p2) (fun s' => s'.1.regs.rax = 2) (s, Int64.ofNat 0) := by
  dsimp [p2]

  -- initial label
  apply step_cps
  dsimp only [simplified_step1,Kraken.Simplified.step]
  simp -- At this point we have simplified the match term from Simplified.step
  dsimp only [Directive.interp, Effects.all]

  -- first step: mov
  apply step_cps
  dsimp only [simplified_step1, Kraken.Simplified.step]
  simp -- following line does symbolic execution
  dsimp only [Directives.interp,Directive.interp,Instr.interp,Operation.interp,Operand.interp,RegOrMem.interp]
  dsimp only [MachineData.set,Reg64s.set,MachineData.setReg,Reg64s.set64,ConstExpr.interp,CondCode.interp,StatusFlags.from_result, Effects.all]

  -- second step: xor %rax, %rax
  apply step_cps
  dsimp only [simplified_step1, Kraken.Simplified.step]
  simp
  dsimp only [Directives.interp,Directive.interp,Instr.interp,Operation.interp,Operand.interp,RegOrMem.interp]
  dsimp only [MachineData.set,Reg64s.set,MachineData.setReg,Reg64s.set64,ConstExpr.interp,CondCode.interp,StatusFlags.from_result, Effects.all]
  -- unclear if these are needed --> To simplify state
  -- unfold register lookup
  dsimp only [Reg64s.get, Reg64s.get64, Reg.base, Reg.offset]
  -- unfold bitvector arith
  dsimp only [BitVec.drop, BitVec.take, Width.bits]
  intro af

  -- third step: jnz
  apply step_cps
  dsimp only [simplified_step1, Kraken.Simplified.step]
  simp

  -- fifth step: mov
  apply step_cps
  dsimp only [simplified_step1, Kraken.Simplified.step]
  simp
  apply Eventually.done
  dsimp [MachineData.setReg, Reg64s.set, Reg64s.set64, ConstExpr.interp]
  simp (ground := true)
