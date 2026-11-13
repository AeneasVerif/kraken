module

public meta import Lean.Meta.Tactic.Simp.RegisterCommand

/-!
# `step_simp`: what the proof of a step lemma unfolds

A step lemma of a backend says what one instruction does to the machine state. Its proof runs
Kraken's instruction interpreter on that instruction, by `simp only [step_simp, …]`: a backend tags
the interpreter functions and the register-file lemmas that every such proof needs, and each proof
lists only what is particular to its instruction.

The set is not Kraken's `kstep` attribute. That one names what Kraken's `kstep` tactic may reduce,
which includes the register accessors (`Reg64s.get64`, `Reg64s.set64`, …); the step lemmas here are
stated with them, so their proofs keep them folded.
-/

public section

/-- Runs the instruction interpreter of a backend on one instruction: `simp only [step_simp, …]`. -/
register_simp_attr step_simp
