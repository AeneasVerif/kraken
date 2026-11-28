module

import LeanQbe.T.MainCertScc
import LeanQbe.T.Notation
import LeanQbe.T.Logic.Rules
import LeanQbeTest.T.MainTest
import LeanQbeTest.T.MainCertSccFixtures
meta import Lean
meta import LeanQbe.T.MainCertScc
meta import LeanQbeTest.T.RegaLitmusTarget

/-!
# Mixed `LinkedCertScc` Smoke, Composition, & Axiom Audit Tests (`MainCertSccTest`)

Complements `MainCertBudgetSccTest` by exercising:
1. Empty-module `compile_linked_budget_scc!` certificates.
2. Compositional `LinkedCertScc.ofLinkedCert` + `LinkedCertScc.append` across acyclic + cyclic SCCs.
3. Negative validation checks (`checkAcyclic`, `checkCyclic`, unsupported source op, ext collision).
4. Single-line `#print axioms` audit strictly `⊆ [propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false

section

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

/-! ## 1b. Flat `TFlatFn` `(flat := true)` + Parity + Trap T5 Checks -/

compile_linked_budget_scc! emptySccFlatCert litmusTarget litmusLayout LegalTarget.aarch64
  litmusLabelClean emptySccMod 2 (flat := true)

theorem emptySccFlatCert_code_eq : emptySccFlatCert.code = emptySccCert.code := rfl

def flatInc1Tf : TFlatFn :=
  { name := "flatInc1", as := [i64], rs := [i64]
    body := .let_ ⟨.add i64, (.var 0, .imm 1#64, ())⟩ (.ret (.var 0, ())) }

def flatRecTf : TFlatFn :=
  { name := "flatRec", as := [i64], rs := [i64]
    body :=
      .let_ ⟨.cmp .eq i64, (.var 0, .imm 0#64, ())⟩ <|
      .jnz (.var 0) (.ret (.imm 0#64, ())) <|
      .let_ ⟨.sub i64, (.var 1, .imm 1#64, ())⟩ <|
      .call "flatRec" (as := [i64]) [i64] (.var 0, ()) <|
      .call "flatInc1" (as := [i64]) [i64] (.var 0, ()) <|
      .ret (.var 0, ()) }

def mixedFlatBudgetMod : BudgetModule :=
  { fns := [⟨flatInc1Tf.toFn, 16, 16⟩, ⟨flatRecTf.toFn, 32, 32⟩] }

compile_linked_budget_scc! mixedFlatLegCert litmusTarget litmusLayout LegalTarget.aarch64
  litmusLabelClean mixedFlatBudgetMod 1 (maxBound := 256)
  (exportBounds := [("flatRec", 128)]) (flat := false)

compile_linked_budget_scc! mixedFlatCert litmusTarget litmusLayout LegalTarget.aarch64
  litmusLabelClean mixedFlatBudgetMod 1 (maxBound := 256)
  (exportBounds := [("flatRec", 128)]) (flat := true)

theorem mixedFlatCert_numChunks : mixedFlatCert.numChunks = 2 := by rfl
theorem mixedFlatCert_code_eq : mixedFlatCert.code = mixedFlatLegCert.code := rfl
theorem mixedFlatCert_inc_bound_eq :
    mixedFlatCert.bound "flatInc1" = mixedFlatLegCert.bound "flatInc1" := rfl
theorem mixedFlatCert_rec_bound_eq :
    mixedFlatCert.bound "flatRec" = mixedFlatLegCert.bound "flatRec" := rfl

-- Trap T5: `(flat := true)` must fail loudly on unmaterialized PHOAS `partModB`.
#eval show Lean.Elab.Term.TermElabM Unit from do
  let opts : CertSccOptions := { flatT? := some (← `(true)) }
  let failed ← try
    let _ ← elabAndEvalSccChunks (← `(litmusTarget)) (← `(litmusLayout))
      (← `(LegalTarget.aarch64)) (← `(litmusLabelClean)) (← `(partModB)) 1 opts
    pure false
  catch _ => pure true
  if !failed then
    throwError "expected compile_linked_budget_scc! (flat := true) on partModB to throw"

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
#print axioms emptySccFlatCert
#print axioms mixedFlatCert
#print axioms mixedFlatCert_code_eq
#print axioms partCertA_scc
#print axioms appendedMixedCert

end LeanQbeTest.T.MainCertSccTest
