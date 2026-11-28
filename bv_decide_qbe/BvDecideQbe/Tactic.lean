module

public import Std.Tactic.BVDecide
public import LeanQbe.T.Examples.Bitblast.Ref.BVProg
public import BvDecideQbe.Config
public import BvDecideQbe.NormalizeTheorems
public import BvDecideQbe.Syntax
public import BvDecideQbePlugin

/-!
# Trust-Pure `bv_decide_qbe` & `bv_cut_qbe` Tactic Entrypoint

Lean, zero-`Lean.*`-import user module exporting:
- `bv_decide_qbe`, `bv_decide_qbe_upstream`, `bv_decide_qbe_push`, and `bv_cut_qbe` syntax
  (`BvDecideQbe.Syntax`)
- `QbeMode`, `QbeConfig`, `QbeFeatures` (`BvDecideQbe.Config`)
- Kernel-proved `BVProg` + `NormalizeTheorems` symbols required by proof terms
- Precompiled native tactic elaborators registered via `BvDecideQbePlugin`
  (`BvDecideQbe.TacticImpl`) without loading `Lean.Meta` / `Grind.Main` / `Cut` `.olean`s.
-/

set_option autoImplicit false

public section

namespace BvDecideQbe

open LeanQbe.T.Examples.Bitblast.Ref

/-- Verify `FFI.lean` & `Prover.lean` name constants match `BVProg`. -/
example : ``BVProg.wordsToBytesLE = `LeanQbe.T.Examples.Bitblast.Ref.BVProg.wordsToBytesLE := rfl
example : ``BVProg.parse = `LeanQbe.T.Examples.Bitblast.Ref.BVProg.parse := rfl
example : ``BVProg.unsat_of_bv_solve_words =
    `LeanQbe.T.Examples.Bitblast.Ref.BVProg.unsat_of_bv_solve_words := rfl

end BvDecideQbe
