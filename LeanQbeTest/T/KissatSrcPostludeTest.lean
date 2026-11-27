/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Src.Full
public import LeanQbe.T.Examples.Kissat.Src.Config
public import LeanQbe.T.PrintCpp
public import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Examples.Kissat.Src.Header
meta import LeanQbe.T.Examples.Kissat.Src.Full
meta import LeanQbe.T.Examples.Kissat.Src.Config
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe

/-!
# Kissat `Src/` Generated Postlude & Axiom Cleanliness Test (`KissatSrcPostludeTest`)

Verifies:
1. Generated `<fn>_wf`, `fns`, and `fns_wf` across all `40` upstream `Src/*.lean` modules
   (`410` functions) plus `Src.Config` (`17` functions), including edge-case names like
   `Parse.full_parse_body_wf`.
2. Declarative `kissat_c0! (postlude := false)` + `kissat_src_postlude!` elaboration path.
3. Zero IR drift / acyclicity / printer checks on `Full.kissatModule` and `Config.configModule`.
4. `#print axioms` (`<= std3`, `0` `@[expose]` on generated theorems, `0` `import all`).
-/

set_option autoImplicit false

namespace LeanQbeTest.T.KissatSrcPostludeTest

open LeanQbe.T
open LeanQbe.T.PrintCpp
open LeanQbe.T.Examples.Kissat.Src

@[expose] public section

kissat_c0! (postlude := false) postlude_demo "
u32 demo_inc(u32 x) { return x + 1u; }
u32 demo_add2(u32 x) { return demo_inc(demo_inc(x)); }
"

end

public section

kissat_src_postlude! postlude_demo

#guard postlude_demo_fns.length == 2
#guard fns.length == 2
#guard Full.kissatModule.fns.length == 410
#guard (Full.kissatModule.fns.map Fn.name).eraseDups.length == 410
#guard Full.kissatModule.checkAcyclic == true
#guard Config.configModule.fns.length == 17
#guard Config.configModule.checkAcyclic == true
#guard (ppTModule Full.kissatModule).isOk
#guard (PrintQbe.module Full.kissatModule).isOk
#guard (ppTModule Config.configModule).isOk
#guard (PrintQbe.module Config.configModule).isOk

theorem src_full_wf : ∀ f ∈ Full.kissatModule.fns, f.Wf := Full.kissatModule_wf
theorem src_config_wf : ∀ f ∈ Config.fns, f.Wf := Config.fns_wf
theorem src_parse_body_wf : Func.Wf Parse.full_parse_body_body := Parse.full_parse_body_wf
theorem src_parse_fns_wf : ∀ f ∈ Parse.fns, f.Wf := Parse.fns_wf
theorem src_cong_fns_wf : ∀ f ∈ Congruence.fns, f.Wf := Congruence.fns_wf
theorem src_def_fns_wf : ∀ f ∈ Definition.fns, f.Wf := Definition.fns_wf
theorem src_viv_fns_wf : ∀ f ∈ Vivify.fns, f.Wf := Vivify.fns_wf
theorem src_sweep_fns_wf : ∀ f ∈ Sweep.fns, f.Wf := Sweep.fns_wf
theorem src_demo_wf : ∀ f ∈ fns, f.Wf := fns_wf
theorem src_demo_inc_wf : Func.Wf demo_inc_body := demo_inc_wf
theorem src_demo_add2_wf : Func.Wf demo_add2_body := demo_add2_wf

end

end LeanQbeTest.T.KissatSrcPostludeTest

#print axioms LeanQbeTest.T.KissatSrcPostludeTest.src_full_wf
#print axioms LeanQbeTest.T.KissatSrcPostludeTest.src_config_wf
#print axioms LeanQbeTest.T.KissatSrcPostludeTest.src_parse_body_wf
#print axioms LeanQbeTest.T.KissatSrcPostludeTest.src_parse_fns_wf
#print axioms LeanQbeTest.T.KissatSrcPostludeTest.src_cong_fns_wf
#print axioms LeanQbeTest.T.KissatSrcPostludeTest.src_def_fns_wf
#print axioms LeanQbeTest.T.KissatSrcPostludeTest.src_viv_fns_wf
#print axioms LeanQbeTest.T.KissatSrcPostludeTest.src_sweep_fns_wf
#print axioms LeanQbeTest.T.KissatSrcPostludeTest.src_demo_wf
#print axioms LeanQbeTest.T.KissatSrcPostludeTest.src_demo_inc_wf
#print axioms LeanQbeTest.T.KissatSrcPostludeTest.src_demo_add2_wf
