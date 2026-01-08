import AsmInterp

open AsmInterp

def main : IO Unit := do
  let s : MachineState := {}
  IO.println s!"Initial state: {repr s}"
  
  -- Simple program:
  -- mov rax, 10
  -- add rax, 5
  -- hlt
  let instrs := [
    Instr.mov (.reg .rax) (.imm 10),
    Instr.add (.reg .rax) (.imm 5),
    Instr.hlt
  ]

  let mut currentState := s
  for instr in instrs do
    IO.println s!"Executing: {repr instr}"
    currentState := eval currentState instr
    IO.println s!"Registers: {repr currentState.regs}"
    IO.println s!"RIP: {currentState.rip}"
    IO.println "---"