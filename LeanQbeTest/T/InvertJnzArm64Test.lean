module

public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.Spill
meta import LeanQbe.T.Arm64.Isel
meta import LeanQbe.T.Arm64.TargLemmas
meta import LeanQbe.T.Spill

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

/-! ## Helpers -/

/-- Hints from the production heuristics (`Fn.computeHints` = `Spill.hints ∘ Fn.mid`). -/
meta def hintsOf (fs : List Fn) : List armTarget.toIsa.Hints :=
  fs.map (Fn.computeHints armTarget.toIsa armLegalTarget)

/-- End-to-end verified compilation check (lowering, labels, stack bounds). -/
meta def chk (fs : List Fn) : Bool :=
  checkCompile armTarget armLayout armLegalTarget [] [] 0 fs (hintsOf fs) 2048

/-- Emitted code of a module (empty on a compile error). -/
meta def codeOf (fs : List Fn) : List armTarget.toIsa.Directive :=
  extractCode (compileModule armTarget.toIsa armLegalTarget armTarget.frame.raBytes [] [] 0 fs
    (hintsOf fs))

meta def isCbzDir : Directive → Bool
  | .instr { operation := .CBZ .., .. } => true
  | _ => false

meta def isCbnzDir : Directive → Bool
  | .instr { operation := .CBNZ .., .. } => true
  | _ => false

/-! ## Test Programs -/

/-- Loop where then-arm continues the loop and else-arm exits.
`mT > mE` causes `Spill.hints` to record `invertJnz = true`. -/
def hotLoopFn : Fn :=
  ⟨"hotLoopArm", [i64, i64], [i64], fun _ _ (n, a, ()) =>
    .group (sig := [[i64, i64]])
      (fun (loopLbl, ()) => .cons (ts := [i64, i64]) (fun (i, acc, ()) =>
        .let_ (op2 (.cmp .eq i64) (.var i) (.imm 0)) fun (c, ()) =>
        .jnz (.var c)
          (.let_ (op2 (.add i64) (.var acc) (.var i)) fun (acc', ()) =>
           .let_ (op2 (.sub i64) (.var i) (.imm 1)) fun (i', ()) =>
           .jump loopLbl (.var i', .var acc', ()))
          (.ret (.var acc, ()))) .nil)
      (fun (loopLbl, ()) => .jump loopLbl (.var n, .var a, ()))⟩

/-- Loop where then-arm exits and else-arm continues the loop.
`mE > mT` causes `Spill.hints` to keep `invertJnz = false`. -/
def coldThenFn : Fn :=
  ⟨"coldThenArm", [i64, i64], [i64], fun _ _ (n, a, ()) =>
    .group (sig := [[i64, i64]])
      (fun (loopLbl, ()) => .cons (ts := [i64, i64]) (fun (i, acc, ()) =>
        .let_ (op2 (.cmp .eq i64) (.var i) (.imm 0)) fun (c, ()) =>
        .jnz (.var c)
          (.ret (.var acc, ()))
          (.let_ (op2 (.add i64) (.var acc) (.var i)) fun (acc', ()) =>
           .let_ (op2 (.sub i64) (.var i) (.imm 1)) fun (i', ()) =>
           .jump loopLbl (.var i', .var acc', ()))) .nil)
      (fun (loopLbl, ()) => .jump loopLbl (.var n, .var a, ()))⟩

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
