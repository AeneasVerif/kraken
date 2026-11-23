/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM7SpecBridges

/-!
# Verification and Single-Line Axiom Audit for `FullM7SpecBridges{0,1,}`

Single-line `< 115`-col `#print axioms` audit (`⊆ [propext, Classical.choice, Quot.sound]`)
covering all `Gap A` (`FullM7SpecBridges0`), `Gap B1` (`FullM7SpecBridges1`), and
`Gap B2` (`FullM7SpecBridges`) public bridge theorems and non-bailout concrete `Mem 64` NV checks.
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.KissatM7SpecBridgesTest

open LeanQbe.T.Examples.Kissat.FullM7SpecBridges

#print axioms fullArenaPermEq_refl
#print axioms fullArenaPermEq_trans
#print axioms fullArenaVarsNodup_of_perm
#print axioms m7RephaseWarmupSpec_of
#print axioms m7RephaseWarmupSpec_elim
#print axioms m7RephaseWarmupSpec_monoX
#print axioms m7RephaseM6HdrSpec_monoX
#print axioms full_rephase_m7_warmup_wp
#print axioms full_rephase_m7_warmup_searchLog_wp
#print axioms full_rephase_m7_m6hdr_wp
#print axioms m7Hdr_call_m7Rephase_inv
#print axioms nv_m7_rephase_warmup
#print axioms m7MinShrinkSpec_of
#print axioms m7MinShrinkSpec_elim
#print axioms m7MinShrinkSpec_monoX
#print axioms fullMinShrinkSpec_of_m7MinShrinkSpec
#print axioms m7MinShrinkSpec_of_fullMinShrinkSpec_small
#print axioms full_min_shrink_m6_m7sort_wp
#print axioms full_min_shrink_m7_wp
#print axioms full_analyze_m5_m7_wp
#print axioms m7GapBNvTable_nodup
#print axioms m7GapBNvAnaTable_nodup
#print axioms nv_m7_min_shrink_m6
#print axioms nv_m7_min_shrink
#print axioms nv_m7_analyze
#print axioms nv_m7_analyze_wp

end LeanQbeTest.T.KissatM7SpecBridgesTest
