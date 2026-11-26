module

public import LeanQbe.T.MainCertScc
public import LeanQbe.T.Notation
public import LeanQbe.T.Logic.Rules
public import LeanQbeTest.T.MainTest
public import LeanQbeTest.T.MainCertSccFixtures
public meta import Lean
public meta import LeanQbe.T.MainCertScc
public meta import LeanQbeTest.T.RegaLitmusTarget

/-!
# Mixed `LinkedCertScc` Smoke, Composition, & Axiom Audit Tests (`MainCertSccTest`)

Complements `MainCertBudgetSccTest` by exercising:
1. Empty-module `compile_linked_budget_scc!` certificates.
2. Compositional `LinkedCertScc.ofLinkedCert` + `LinkedCertScc.append` across acyclic + cyclic SCCs.
3. Negative validation checks (`checkAcyclic`, `checkCyclic`, unsupported source op, ext collision).
4. Single-line `#print axioms` audit strictly `⊆ [propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.MainCertSccTest

open LeanQbe.T LeanQbe.T.LinkRec LeanQbe.T.LinkScc
open LeanQbe.T.Notation LeanQbe.T.RegaLitmus LeanQbeTest.T.MainTest
open LeanQbeTest.T.MainCertSccFixtures
open Std Std.ExtHashMap Kraken.Bedrock2.Test

/-! ## 1. Compositional Acyclic + Mutual-Recursion `compile_linked_budget_scc!` -/

/-- Acyclic leaf `fnInc1(x) = x + 1`. -/
def fnInc1 : Fn := tqbe $inc1(%x:l) -> l {
  %y =l add %x, 1
  ret %y
}

/-- Mutually recursive `fnEven(n)` via `.call`. -/
def fnEven : Fn := tqbe $even(%n:l) -> l {
  %c =b ceql %n, 0
  jnz %c, {
    ret 1
  }, {
    %n1 =l sub %n, 1
    %r =l call $odd(%n1)
    ret %r
  }
}

/-- Mutually recursive `fnOdd(n)` via `.call`. -/
def fnOdd : Fn := tqbe $odd(%n:l) -> l {
  %c =b ceql %n, 0
  jnz %c, {
    ret 0
  }, {
    %n1 =l sub %n, 1
    %r =l call $even(%n1)
    ret %r
  }
}

/-- Top acyclic caller `fnTop(n) = inc1(even(n))` across chunks. -/
def fnTop : Fn := tqbe $top(%n:l) -> l {
  %e =l call $even(%n)
  %r =l call $inc1(%e)
  ret %r
}

def mixedBudgetMod : BudgetModule :=
  { fns := [⟨fnInc1, 16, 16⟩, ⟨fnEven, 16, 16⟩, ⟨fnOdd, 16, 16⟩, ⟨fnTop, 32, 32⟩] }

def emptySccMod : BudgetModule := { fns := [] }
compile_linked_budget_scc! emptySccCert litmusTarget litmusLayout LegalTarget.aarch64
  litmusLabelClean emptySccMod 2

-- Compositional `LinkedCertScc.ofLinkedCert` + `LinkedCertScc.append` check.
def partModA : Module := { fns := [fnInc1] }
def partModB : BudgetModule :=
  { fns := [⟨fnEven, 16, 16⟩, ⟨fnOdd, 16, 16⟩, ⟨fnTop, 32, 32⟩] }
def partModBExterns : List SigEntry := partModA.fns.map Fn.sig

compile_linked_chunks! partCertA litmusTarget litmusLayout LegalTarget.aarch64 litmusLabelClean
  partModA 1 (compileExt := true)

compile_linked_budget_scc! partCertB litmusTarget litmusLayout LegalTarget.aarch64 litmusLabelClean
  partModB 1 (maxBound := 256) (exportBounds := [("even", 64), ("odd", 64)])
  (ext := partCertA.exportedExt) (extSigs := partModBExterns)

private theorem partCertA_calls :
    checkChunksCalls [] [] (partCertA.chunks.map Chunk.acyc) = true := by rfl

noncomputable def partCertA_scc :
    LinkedCertScc litmusTarget litmusLayout LegalTarget.aarch64 litmusLabelClean partModA :=
  LinkedCertScc.ofLinkedCert partCertA rfl partCertA_calls

noncomputable def appendedMixedCert :
    LinkedCertScc litmusTarget litmusLayout LegalTarget.aarch64 litmusLabelClean
      mixedBudgetMod.toModule :=
  partCertA_scc.append partCertB rfl (by t_kernel_rfl) (by t_kernel_rfl)

theorem emptySccCert_numChunks : emptySccCert.numChunks = 1 := by rfl
theorem partCertB_numChunks : partCertB.numChunks = 2 := by rfl
theorem appendedMixedCert_numChunks : appendedMixedCert.numChunks = 3 := by rfl

/-! ## 2. Negative Validation Checks -/

#guard !Module.checkAcyclic ⟨[fnEven, fnOdd], [], []⟩
#guard !LinkRec.checkCyclic ⟨[fnTop], [], []⟩

private def fnUnsupportedW128 : Fn :=
  ⟨"bad_w128", [.bits 128], [.bits 128], fun _ _ (x, ()) => .ret (.var x, ())⟩

#guard
  match compileModule litmusTarget.toIsa LegalTarget.aarch64
      litmusTarget.frame.raBytes [] [] 0 [fnUnsupportedW128]
      [Fn.computeHints litmusTarget.toIsa LegalTarget.aarch64 fnUnsupportedW128] with
  | .error "bad_w128: unsupported source op for target" => true
  | _ => false

theorem neg_ext_collision_rejected :
    checkLinkSccList litmusLayout [(("inc1", [i64], [i64]), 0)] partCertA_scc.chunks = false := by
  decide

/-! ## 3. Single-Line Axiom Audit (`⊆ [propext, Classical.choice, Quot.sound]`) -/

#print axioms LeanQbe.T.linkChunks_fnSpec
#print axioms LeanQbe.T.linkChunks_fnSpec_host
#print axioms LeanQbe.T.LinkedCertScc.fnSpec_linked
#print axioms LeanQbe.T.LinkedCertScc.fnSpec_host
#print axioms LeanQbe.T.LinkedCertScc.eventually_ret1_i64_of_le
#print axioms emptySccCert
#print axioms partCertA_scc
#print axioms appendedMixedCert

end LeanQbeTest.T.MainCertSccTest
