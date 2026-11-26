module

public import LeanQbeTest.T.MainFlatParityFixtures
public import LeanQbe.T.Amd64.Targ
public import LeanQbe.T.Amd64.PrintAsm0
import LeanQbe.T.FlatDirectLemmas
import LeanQbe.T.RegaFlatLemmas
meta import Lean
meta import LeanQbeTest.T.MainFlatParityFixtures
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Amd64.PrintAsm0

/-!
# SysV x64 Differential Parity & Axiom Audit (`MainFlatParityTest`)

Verifies `compileModuleFlat = compileModule`, `compileFlatFn = compileFn`, byte-exact `printAsm0`
assembly on `Amd64.x64Target` (`x64LegalTarget`) over native `divConst`/`assumeElim`/`mergeRets`/
loop `TFlatFn`s, Litmus programs, and Kissat C0 schedule functions, and audits axioms (`std3` only).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.MainFlatParityTest

open LeanQbe.T
open LeanQbeTest.T.MainFlatParityFixtures

theorem compileModuleFlat_ok_implies_compileModule_x64
    (hints : List Amd64.x64Target.toIsa.Hints)
    {code : List Amd64.x64Target.toIsa.Directive} {bounds : List (Sym × Nat)}
    (hok : compileModuleFlat Amd64.x64Target.toIsa Amd64.x64LegalTarget
      Amd64.x64Target.frame.raBytes [] [] 0 litmusTFlatMod hints = .ok (code, bounds)) :
    compileModule Amd64.x64Target.toIsa Amd64.x64LegalTarget
        Amd64.x64Target.frame.raBytes [] [] 0 (litmusTFlatMod.map TFlatFn.toFn) hints =
      .ok (code, bounds) :=
  compileModule_of_compileModuleFlat _ _ _ [] [] 0 litmusTFlatMod hints code bounds hok

theorem divModFlat_compileFlatFn_eq_x64 (h : Amd64.x64Target.toIsa.Hints) :
    compileFlatFn Amd64.x64Target.toIsa Amd64.x64LegalTarget h divModFlat =
      compileFn Amd64.x64Target.toIsa Amd64.x64LegalTarget h divModFlat.toFn :=
  compileFlatFn_eq_compileFn _ _ _ _ divModFlat_wf

theorem assumeLoopFlat_compileFlatFn_eq_x64 (h : Amd64.x64Target.toIsa.Hints) :
    compileFlatFn Amd64.x64Target.toIsa Amd64.x64LegalTarget h assumeLoopFlat =
      compileFn Amd64.x64Target.toIsa Amd64.x64LegalTarget h assumeLoopFlat.toFn :=
  compileFlatFn_eq_compileFn _ _ _ _ assumeLoopFlat_wf

#eval show IO Unit from
  checkTargetParity "x64" Amd64.x64Target.toIsa Amd64.x64LegalTarget
    Amd64.x64Target.frame.raBytes Amd64.printAsm0

#print axioms LeanQbe.T.denote_toTFlat_eq
#print axioms LeanQbe.T.Func.renorm_eq_self
#print axioms LeanQbe.T.reifyFunc_denoteFunc_eq
#print axioms LeanQbe.T.Func.renorm_denoteFunc
#print axioms LeanQbe.T.TFlat.ext_eq_fn_ext
#print axioms LeanQbe.T.TFlatFn.supportsSource_eq
#print axioms LeanQbe.T.legalFlat_eq
#print axioms LeanQbe.T.Rega.lowerFlatFn_eq_lowerFn
#print axioms LeanQbe.T.earlyOptFlat_toFn
#print axioms LeanQbe.T.midStageFlat_toFn
#print axioms LeanQbe.T.compileFlatFn_eq_compileFn
#print axioms LeanQbe.T.compileModule_of_compileModuleFlat
#print axioms compileModuleFlat_ok_implies_compileModule_x64
#print axioms divModFlat_compileFlatFn_eq_x64
#print axioms assumeLoopFlat_compileFlatFn_eq_x64

end LeanQbeTest.T.MainFlatParityTest
