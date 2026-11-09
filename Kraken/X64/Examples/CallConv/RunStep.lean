module

public import Kraken.X64.WP.Basic

/-!
# `run_step`: stepping one instruction by hand

`run_step h [extra]` runs the head directive of a fragment placed at the infix position `h`
(`Host.run_cons`) and unfolds its semantics with the lemmas a general-purpose register instruction
needs, plus `extra`. What is left are the memory accesses (`Effects.All_store`, ...) and the
continuation.

Why it exists: the project's stepping tactic `kstep` can run the goal `Host.run_cons` leaves (see
`CallConv.SysVInc.inc_spec`), but not yet everything these examples need. It does not reduce
`disp(%r)` addresses (the address width stays an unreduced `match address_size with ...`), it has no
rules for AVX memory accesses (`movaps`, with its alignment side condition), and it does not handle
`call` (`ProcSpec.wp_call`). Once it does, the examples can switch to `kstep` and this file can go.
-/

public section

syntax (name := runStep) "run_step " ident (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| run_step $h:ident) => `(tactic|
      (refine Host.run_cons $h ?_
       simp only [Directive.interp, Instr.interp, Effects.All, Operation.interp, Operand.interp,
         RegOrMem.interp, MachineData.set, MachineData.setReg, Reg64s.get_low64, Reg64s.set_low64,
         ConstExpr.interp, Reg64s.get64_set64_self]))
  | `(tactic| run_step $h:ident [$extra,*]) => do
    let extra : Lean.Syntax.TSepArray [`Lean.Parser.Tactic.simpStar, `Lean.Parser.Tactic.simpErase,
      `Lean.Parser.Tactic.simpLemma] "," := ⟨extra.elemsAndSeps⟩
    `(tactic|
      (refine Host.run_cons $h ?_
       simp only [Directive.interp, Instr.interp, Effects.All, Operation.interp, Operand.interp,
         RegOrMem.interp, MachineData.set, MachineData.setReg, Reg64s.get_low64, Reg64s.set_low64,
         ConstExpr.interp, Reg64s.get64_set64_self, $extra,*]))
