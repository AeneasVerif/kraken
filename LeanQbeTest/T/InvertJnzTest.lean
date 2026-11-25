module

public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.Spill
public import LeanQbeTest.T.RegaTestKit
meta import LeanQbe.T.Amd64.TargLemmas
meta import LeanQbe.T.Spill
meta import LeanQbeTest.T.RegaTestKit

/-!
# InvertJnz Regression and Fallthrough Layout Tests on x64

Validates execution-weight cold branch inversion & hot fallthrough layout in
`Rega.lean` (`jnzSetup` / `fuseJnzChoice`) and `Spill.lean` (`invertJnz` hint gathering)
on the x64 target:
1. `hotLoopFn`: loop back-edge in `then` arm (`mT > mE`) sets `invertJnz = true`.
2. Lowering inverts the flag condition from `.eq` (`je`) to `.ne` (`jne`), targeting
   the cold exit block while the hot loop body falls through straight-line.
3. `coldThenFn`: exit in `then` arm and loop back-edge in `else` arm (`mT < mE`) leaves
   `invertJnz = false`. Lowering preserves non-inverted `.eq` (`je`) targeting the cold
   exit while the hot loop body falls through straight-line.
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.InvertJnzTest

open LeanQbe.T LeanQbe.T.Amd64
open LeanQbeTest.T.RegaTestKit

/-! ## Helpers -/

/-- Hints from the default heuristics (`Fn.computeHints` = `Spill.hints ∘ Fn.mid`). -/
meta def hintsOf (fs : List Fn) : List x64Target.toIsa.Hints :=
  RegaTestKit.hintsOf x64Target x64LegalTarget fs

/-- End-to-end verified compilation check (lowering, labels, stack bounds). -/
meta def chk (fs : List Fn) : Bool :=
  RegaTestKit.chk x64Target x64Layout x64LegalTarget fs

/-- Emitted code of a module (empty on a compile error). -/
meta def codeOf (fs : List Fn) : List x64Target.toIsa.Directive :=
  RegaTestKit.codeOf x64Target x64LegalTarget fs

meta def isJneDir : Directive → Bool
  | .instr (.regular _ _ (.jcc .ne _)) => true
  | _ => false

meta def isJeDir : Directive → Bool
  | .instr (.regular _ _ (.jcc .e _)) => true
  | _ => false

/-! ## Test Programs -/

/-- Loop where then-arm continues the loop and else-arm exits. -/
def hotLoopFn : Fn := RegaTestKit.hotLoopFn

/-- Loop where then-arm exits and else-arm continues the loop. -/
def coldThenFn : Fn := RegaTestKit.coldThenFn

/-! ## Guard Checks -/

/- Hot loop lowers and compiles cleanly through verified `Rega.lowerFn`. -/
#guard chk [hotLoopFn]

/- Cold-then loop lowers and compiles cleanly through verified `Rega.lowerFn`. -/
#guard chk [coldThenFn]

/- `hotLoopFn` has `invertJnz = true` for its branch IP. -/
#guard match (hintsOf [hotLoopFn]).head? with
  | some h => (h.invertJnz.find? 1 == some true) || (h.invertJnz.find? 12 == some true)
  | none => false

/- `coldThenFn` has `invertJnz = false` (none) for its branch IP. -/
#guard match (hintsOf [coldThenFn]).head? with
  | some h => (h.invertJnz.find? 1 == none) && (h.invertJnz.find? 12 == none)
  | none => false

/- Inverted `hotLoopFn` emits `jne` to exit, allowing hot loop body to fall through. -/
#guard (codeOf [hotLoopFn]).any isJneDir

/- Non-inverted `coldThenFn` emits `je` to exit, allowing hot loop body to fall through. -/
#guard (codeOf [coldThenFn]).any isJeDir

/-! ## Axiom Audit -/

theorem invertJnz_empty_rfl (ip : Nat) :
    (Trie.empty : Trie Bool).getD ip false = false := by
  rfl

#print axioms invertJnz_empty_rfl

end LeanQbeTest.T.InvertJnzTest
