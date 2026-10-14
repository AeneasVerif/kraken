module

public import Lean.ToExpr
meta import Lean.Elab.Deriving.ToExpr

/-! Status flag outputs of opcode families, applied by Semantics (`StatusFlags.update`). -/

@[expose] public section

/-- How an instruction sets one status flag. -/
inductive FlagOut | keep | undef | set (b : Bool)
  deriving Repr, DecidableEq

instance : Coe Bool FlagOut := ⟨.set⟩

structure FlagsOut where
  cf : FlagOut := .keep
  pf : FlagOut := .keep
  af : FlagOut := .keep
  zf : FlagOut := .keep
  sf : FlagOut := .keep
  of : FlagOut := .keep
  deriving Repr, DecidableEq

def FlagsOut.allUndef : FlagsOut :=
  { cf := .undef, pf := .undef, af := .undef, zf := .undef, sf := .undef, of := .undef }
