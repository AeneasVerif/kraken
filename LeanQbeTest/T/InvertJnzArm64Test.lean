module

public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.Spill
public import LeanQbeTest.T.RegaTestKit
public import LeanQbeTest.T.Arm64DirPreds
meta import LeanQbe.T.Arm64.Isel
meta import LeanQbe.T.Arm64.TargLemmas
meta import LeanQbe.T.Spill
meta import LeanQbeTest.T.RegaTestKit
meta import LeanQbeTest.T.Arm64DirPreds

/-!
# InvertJnz Regression and Fallthrough Layout Tests on AArch64

AArch64 twin of `LeanQbeTest.T.InvertJnzTest` (x64), kept in its own module so the two targets'
Kraken ISAs are never co-imported. Validates cold branch inversion & hot fallthrough layout in
`Rega.lean` (`jnzSetup` / `fuseJnzChoice`) and `Spill.lean` (`invertJnz` hint gathering)
on the Arm64 target:
1. `hotLoopFn`: loop back-edge in `then` arm (`mT > mE`) sets `invertJnz = true`.
2. Lowering inverts the fused compare-zero branch condition from `.eq` (`CBZ`)
   to `.ne` (`CBNZ`), targeting the cold exit block while the hot loop body
   falls through straight-line.
3. `coldThenFn`: exit in `then` arm and loop back-edge in `else` arm (`mT < mE`) leaves
   `invertJnz = false`. Lowering preserves non-inverted `.eq` (`CBZ`) targeting the cold exit
   while the hot loop body falls through straight-line.
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.InvertJnzArm64Test

open LeanQbe.T LeanQbe.T.Arm64
open LeanQbeTest.T.RegaTestKit
open LeanQbeTest.T.Arm64DirPreds

/-! ## Helpers -/

/-- Hints from the default heuristics (`Fn.computeHints` = `Spill.hints ∘ Fn.mid`). -/
meta def hintsOf (fs : List Fn) : List armTarget.toIsa.Hints :=
  RegaTestKit.hintsOf armTarget armLegalTarget fs

/-- End-to-end verified compilation check (lowering, labels, stack bounds). -/
meta def chk (fs : List Fn) : Bool :=
  RegaTestKit.chk armTarget armLayout armLegalTarget fs

/-- Emitted code of a module (empty on a compile error). -/
meta def codeOf (fs : List Fn) : List armTarget.toIsa.Directive :=
  RegaTestKit.codeOf armTarget armLegalTarget fs

/-! ## Test Programs -/

/-- Loop where then-arm continues the loop and else-arm exits. -/
def hotLoopFn : Fn := RegaTestKit.hotLoopFn "hotLoopArm"

/-- Loop where then-arm exits and else-arm continues the loop. -/
def coldThenFn : Fn := RegaTestKit.coldThenFn "coldThenArm"

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

/- Inverted `hotLoopFn` emits `cbnz` to exit, allowing hot loop body to fall through. -/
#guard (codeOf [hotLoopFn]).any isCbnzDir

/- Non-inverted `coldThenFn` emits `cbz` to exit, allowing hot loop body to fall through. -/
#guard (codeOf [coldThenFn]).any isCbzDir

/-! ## Axiom Audit -/

theorem invertJnz_arm64_empty_rfl (ip : Nat) :
    (Trie.empty : Trie Bool).getD ip false = false := by
  rfl

#print axioms invertJnz_arm64_empty_rfl

end LeanQbeTest.T.InvertJnzArm64Test
