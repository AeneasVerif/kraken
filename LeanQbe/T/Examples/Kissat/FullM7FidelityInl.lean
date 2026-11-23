/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.MainCertInlineChunk
public import LeanQbe.T.Examples.Kissat.FullM7FidelityAssembly
public import LeanQbe.T.Examples.Kissat.FullM7InlPolicy
public import LeanQbe.T.Examples.Kissat.FullM7FidelityInlBase
public import LeanQbe.T.Examples.Kissat.FullM7FidelityInl0
public import LeanQbe.T.Examples.Kissat.FullM7FidelityInl1
public import LeanQbe.T.Examples.Kissat.FullM7FidelityInl2
public import LeanQbe.T.Examples.Kissat.FullM7FidelityInl3
public import LeanQbe.T.Examples.Kissat.FullM7FidelityInl4
public import LeanQbe.T.Examples.Kissat.FullM7FidelityInl5
public import LeanQbe.T.Examples.Kissat.FullM7FidelityInl6
public import LeanQbe.T.Examples.Kissat.FullM7FidelityInl7
public import LeanQbe.T.Examples.Kissat.FullM7FidelityInl8
public import LeanQbe.T.Examples.Kissat.FullM7FidelityInl9
public import LeanQbe.T.Examples.Kissat.FullM7FidelityInl10
public import LeanQbe.T.Examples.Kissat.FullM7FidelityInl11
public import LeanQbe.T.Examples.Kissat.FullM7FidelityInl12
meta import Lean
meta import LeanQbe.T.MainCertInlineChunk
meta import LeanQbe.T.Examples.Kissat.FullM7FidelityAssembly
meta import LeanQbe.T.Examples.Kissat.FullM7InlPolicy
meta import LeanQbe.T.Examples.Kissat.FullM7FidelityInlBase
meta import LeanQbe.T.Examples.Kissat.FullM7FidelityInl0
meta import LeanQbe.T.Examples.Kissat.FullM7FidelityInl1
meta import LeanQbe.T.Examples.Kissat.FullM7FidelityInl2
meta import LeanQbe.T.Examples.Kissat.FullM7FidelityInl3
meta import LeanQbe.T.Examples.Kissat.FullM7FidelityInl4
meta import LeanQbe.T.Examples.Kissat.FullM7FidelityInl5
meta import LeanQbe.T.Examples.Kissat.FullM7FidelityInl6
meta import LeanQbe.T.Examples.Kissat.FullM7FidelityInl7
meta import LeanQbe.T.Examples.Kissat.FullM7FidelityInl8
meta import LeanQbe.T.Examples.Kissat.FullM7FidelityInl9
meta import LeanQbe.T.Examples.Kissat.FullM7FidelityInl10
meta import LeanQbe.T.Examples.Kissat.FullM7FidelityInl11
meta import LeanQbe.T.Examples.Kissat.FullM7FidelityInl12

/-!
# Materialized Profile-Guided Inlined Module for Kissat M7Fidelity (`FullM7FidelityInl`, `413` fns)

Joins the `13` materialized `denoteFunc`-backed chunks (`FullM7FidelityInl0..12`) into:
* `m7FidInlFns : List Fn` (`413` functions)
* `m7FidInlMod : Module`
* `m7FidInlMod.fns_eq : m7FidInlMod.fns = (m7FidelityModule.optInlinePolicy m7InlPolicy).fns`
* `m7FidInlMod.eq : m7FidInlMod = m7FidelityModule.optInlinePolicy m7InlPolicy`
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM7FidelityInl

open LeanQbe.T LeanQbe.T.Examples.Kissat.FullM7Fidelity
open LeanQbe.T.Examples.Kissat.FullM7InlPolicy

inline_mod_join! m7FidInlMod m7FidInlFns m7FidelityModule m7InlPolicy m7FidInlBase
  [m7FidInlC0, m7FidInlC1, m7FidInlC2, m7FidInlC3, m7FidInlC4, m7FidInlC5, m7FidInlC6,
   m7FidInlC7, m7FidInlC8, m7FidInlC9, m7FidInlC10, m7FidInlC11, m7FidInlC12]

theorem m7FidInlFns_length : m7FidInlFns.length = 413 := by
  t_kernel_rfl

end LeanQbe.T.Examples.Kissat.FullM7FidelityInl

abbrev m7f_inl_mod := @LeanQbe.T.Examples.Kissat.FullM7FidelityInl.m7FidInlMod
abbrev m7f_inl_eq := @LeanQbe.T.Examples.Kissat.FullM7FidelityInl.m7FidInlMod.eq
abbrev m7f_inl_fns_eq := @LeanQbe.T.Examples.Kissat.FullM7FidelityInl.m7FidInlMod.fns_eq

#print axioms m7f_inl_mod
#print axioms m7f_inl_eq
#print axioms m7f_inl_fns_eq
