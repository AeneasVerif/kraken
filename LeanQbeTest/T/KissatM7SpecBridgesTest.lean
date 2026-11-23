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
`Gap B2` (`FullM7SpecBridges`) public bridge theorems and non-bailout concrete `Mem 64` checks.
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.KissatM7SpecBridgesTest

open LeanQbe.T.Examples.Kissat.FullM7SpecBridges

abbrev audit_perm_refl := @fullArenaPermEq_refl
abbrev audit_perm_trans := @fullArenaPermEq_trans
abbrev audit_vars_nodup := @fullArenaVarsNodup_of_perm
abbrev audit_rephase_of := @m7RephaseWarmupSpec_of
abbrev audit_rephase_elim := @m7RephaseWarmupSpec_elim
abbrev audit_rephase_monoX := @m7RephaseWarmupSpec_monoX
abbrev audit_rephase_m6_monoX := @m7RephaseM6HdrSpec_monoX
abbrev audit_rephase_warmup := @full_rephase_m7_warmup_wp
abbrev audit_rephase_slog := @full_rephase_m7_warmup_searchLog_wp
abbrev audit_rephase_m6hdr := @full_rephase_m7_m6hdr_wp
abbrev audit_m7hdr_call := @m7Hdr_call_m7Rephase_inv
abbrev audit_nv_rephase := @nv_m7_rephase_warmup
abbrev audit_min_shrink_of := @m7MinShrinkSpec_of
abbrev audit_min_shrink_elim := @m7MinShrinkSpec_elim
abbrev audit_min_shrink_monoX := @m7MinShrinkSpec_monoX
abbrev audit_full_of_m7 := @fullMinShrinkSpec_of_m7MinShrinkSpec
abbrev audit_m7_of_full_small := @m7MinShrinkSpec_of_fullMinShrinkSpec_small
abbrev audit_ms_m6_m7sort := @full_min_shrink_m6_m7sort_wp
abbrev audit_ms_m7 := @full_min_shrink_m7_wp
abbrev audit_analyze_m5_m7 := @full_analyze_m5_m7_wp
abbrev audit_nv_tbl_nd := @m7GapBNvTable_nodup
abbrev audit_nv_ana_tbl_nd := @m7GapBNvAnaTable_nodup
abbrev audit_nv_ms_m6 := @nv_m7_min_shrink_m6
abbrev audit_nv_ms := @nv_m7_min_shrink
abbrev audit_nv_ana := @nv_m7_analyze
abbrev audit_nv_ana_wp := @nv_m7_analyze_wp

end LeanQbeTest.T.KissatM7SpecBridgesTest

/-! ## Single-Line `< 115c` Root-Namespace `#print axioms` Audit -/

abbrev m7sb_perm_refl := @LeanQbeTest.T.KissatM7SpecBridgesTest.audit_perm_refl
abbrev m7sb_perm_trans := @LeanQbeTest.T.KissatM7SpecBridgesTest.audit_perm_trans
abbrev m7sb_vars_nodup := @LeanQbeTest.T.KissatM7SpecBridgesTest.audit_vars_nodup
abbrev m7sb_rephase_of := @LeanQbeTest.T.KissatM7SpecBridgesTest.audit_rephase_of
abbrev m7sb_rephase_elim := @LeanQbeTest.T.KissatM7SpecBridgesTest.audit_rephase_elim
abbrev m7sb_rephase_monoX := @LeanQbeTest.T.KissatM7SpecBridgesTest.audit_rephase_monoX
abbrev m7sb_rephase_m6_mono := @LeanQbeTest.T.KissatM7SpecBridgesTest.audit_rephase_m6_monoX
abbrev m7sb_rephase_warmup := @LeanQbeTest.T.KissatM7SpecBridgesTest.audit_rephase_warmup
abbrev m7sb_rephase_slog := @LeanQbeTest.T.KissatM7SpecBridgesTest.audit_rephase_slog
abbrev m7sb_rephase_m6hdr := @LeanQbeTest.T.KissatM7SpecBridgesTest.audit_rephase_m6hdr
abbrev m7sb_m7hdr_call := @LeanQbeTest.T.KissatM7SpecBridgesTest.audit_m7hdr_call
abbrev m7sb_nv_rephase := @LeanQbeTest.T.KissatM7SpecBridgesTest.audit_nv_rephase
abbrev m7sb_ms_of := @LeanQbeTest.T.KissatM7SpecBridgesTest.audit_min_shrink_of
abbrev m7sb_ms_elim := @LeanQbeTest.T.KissatM7SpecBridgesTest.audit_min_shrink_elim
abbrev m7sb_ms_monoX := @LeanQbeTest.T.KissatM7SpecBridgesTest.audit_min_shrink_monoX
abbrev m7sb_full_of_m7 := @LeanQbeTest.T.KissatM7SpecBridgesTest.audit_full_of_m7
abbrev m7sb_m7_of_full_sm := @LeanQbeTest.T.KissatM7SpecBridgesTest.audit_m7_of_full_small
abbrev m7sb_ms_m6_m7sort := @LeanQbeTest.T.KissatM7SpecBridgesTest.audit_ms_m6_m7sort
abbrev m7sb_ms_m7 := @LeanQbeTest.T.KissatM7SpecBridgesTest.audit_ms_m7
abbrev m7sb_analyze_m5_m7 := @LeanQbeTest.T.KissatM7SpecBridgesTest.audit_analyze_m5_m7
abbrev m7sb_nv_tbl_nd := @LeanQbeTest.T.KissatM7SpecBridgesTest.audit_nv_tbl_nd
abbrev m7sb_nv_ana_tbl_nd := @LeanQbeTest.T.KissatM7SpecBridgesTest.audit_nv_ana_tbl_nd
abbrev m7sb_nv_ms_m6 := @LeanQbeTest.T.KissatM7SpecBridgesTest.audit_nv_ms_m6
abbrev m7sb_nv_ms := @LeanQbeTest.T.KissatM7SpecBridgesTest.audit_nv_ms
abbrev m7sb_nv_ana := @LeanQbeTest.T.KissatM7SpecBridgesTest.audit_nv_ana
abbrev m7sb_nv_ana_wp := @LeanQbeTest.T.KissatM7SpecBridgesTest.audit_nv_ana_wp

#print axioms m7sb_perm_refl
#print axioms m7sb_perm_trans
#print axioms m7sb_vars_nodup
#print axioms m7sb_rephase_of
#print axioms m7sb_rephase_elim
#print axioms m7sb_rephase_monoX
#print axioms m7sb_rephase_m6_mono
#print axioms m7sb_rephase_warmup
#print axioms m7sb_rephase_slog
#print axioms m7sb_rephase_m6hdr
#print axioms m7sb_m7hdr_call
#print axioms m7sb_nv_rephase
#print axioms m7sb_ms_of
#print axioms m7sb_ms_elim
#print axioms m7sb_ms_monoX
#print axioms m7sb_full_of_m7
#print axioms m7sb_m7_of_full_sm
#print axioms m7sb_ms_m6_m7sort
#print axioms m7sb_ms_m7
#print axioms m7sb_analyze_m5_m7
#print axioms m7sb_nv_tbl_nd
#print axioms m7sb_nv_ana_tbl_nd
#print axioms m7sb_nv_ms_m6
#print axioms m7sb_nv_ms
#print axioms m7sb_nv_ana
#print axioms m7sb_nv_ana_wp
