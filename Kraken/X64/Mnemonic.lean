module

public meta import Lean.Elab.Term

@[expose] public section

/-- Opcode enums whose constructor names are their assembly mnemonics (see `mnemonics%`). -/
class Mnemonic (α : Type) where
  names : Array (α × String)

namespace Mnemonic
def name {α} [Mnemonic α] [DecidableEq α] (x : α) : String :=
  ((names.find? (·.1 == x)).map (·.2)).getD "?"
def ofName? {α} [Mnemonic α] (s : String) : Option α := (names.find? (·.2 == s)).map (·.1)
end Mnemonic

open Lean Elab Term in
/-- The mnemonic table of an opcode enum `T`: each nullary constructor `T.c` is named `"c"`, and each
constructor `T.c (op : U)` contributes `U`'s table, mapped through `T.c`. -/
elab "mnemonics% " t:ident : term <= ty => do
  let parts ← (← getConstInfoInduct (← realizeGlobalConstNoOverload t)).ctors.toArray.mapM fun c => do
    if (← getConstInfoCtor c).numFields == 0 then
      `(#[($(mkIdent c), $(quote c.getString!))])
    else
      `(Mnemonic.names.map fun (op, n) => ($(mkIdent c) op, n))
  elabTerm (← parts.foldlM (fun acc p => `($acc ++ $p)) (← `(#[]))) ty
