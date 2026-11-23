/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.MainCertInlineChunk
public import LeanQbe.T.Examples.Kissat.FullM7PlusAssembly
public import LeanQbe.T.Examples.Kissat.FullM7InlPolicy
public import LeanQbe.T.Examples.Kissat.FullM7PlusInlBase
public import LeanQbe.T.Examples.Kissat.FullM7PlusInl0
public import LeanQbe.T.Examples.Kissat.FullM7PlusInl1
public import LeanQbe.T.Examples.Kissat.FullM7PlusInl2
public import LeanQbe.T.Examples.Kissat.FullM7PlusInl3
public import LeanQbe.T.Examples.Kissat.FullM7PlusInl4
public import LeanQbe.T.Examples.Kissat.FullM7PlusInl5
public import LeanQbe.T.Examples.Kissat.FullM7PlusInl6
public import LeanQbe.T.Examples.Kissat.FullM7PlusInl7
public import LeanQbe.T.Examples.Kissat.FullM7PlusInl8
public import LeanQbe.T.Examples.Kissat.FullM7PlusInl9
public import LeanQbe.T.Examples.Kissat.FullM7PlusInl10
public import LeanQbe.T.Examples.Kissat.FullM7PlusInl11
public import LeanQbe.T.Examples.Kissat.FullM7PlusInl12
meta import Lean
meta import LeanQbe.T.MainCertInlineChunk
meta import LeanQbe.T.Examples.Kissat.FullM7PlusAssembly
meta import LeanQbe.T.Examples.Kissat.FullM7InlPolicy
meta import LeanQbe.T.Examples.Kissat.FullM7PlusInlBase
meta import LeanQbe.T.Examples.Kissat.FullM7PlusInl0
meta import LeanQbe.T.Examples.Kissat.FullM7PlusInl1
meta import LeanQbe.T.Examples.Kissat.FullM7PlusInl2
meta import LeanQbe.T.Examples.Kissat.FullM7PlusInl3
meta import LeanQbe.T.Examples.Kissat.FullM7PlusInl4
meta import LeanQbe.T.Examples.Kissat.FullM7PlusInl5
meta import LeanQbe.T.Examples.Kissat.FullM7PlusInl6
meta import LeanQbe.T.Examples.Kissat.FullM7PlusInl7
meta import LeanQbe.T.Examples.Kissat.FullM7PlusInl8
meta import LeanQbe.T.Examples.Kissat.FullM7PlusInl9
meta import LeanQbe.T.Examples.Kissat.FullM7PlusInl10
meta import LeanQbe.T.Examples.Kissat.FullM7PlusInl11
meta import LeanQbe.T.Examples.Kissat.FullM7PlusInl12

/-!
# Materialized Profile-Guided Inlined Module for Kissat M7Plus (`FullM7PlusInl`, `410` fns)

Joins the `13` materialized `denoteFunc`-backed chunks (`FullM7PlusInl0..12`) into:
* `m7PlusInlFns : List Fn` (`410` functions)
* `m7PlusInlMod : Module`
* `m7PlusInlMod.fns_eq : m7PlusInlMod.fns = (m7PlusModule.optInlinePolicy m7InlPolicy).fns`
* `m7PlusInlMod.eq : m7PlusInlMod = m7PlusModule.optInlinePolicy m7InlPolicy`
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM7PlusInl

open LeanQbe.T LeanQbe.T.Examples.Kissat.FullM7Plus
open LeanQbe.T.Examples.Kissat.FullM7InlPolicy

inline_mod_join! m7PlusInlMod m7PlusInlFns m7PlusModule m7InlPolicy m7PlusInlBase
  [m7PlusInlC0, m7PlusInlC1, m7PlusInlC2, m7PlusInlC3, m7PlusInlC4, m7PlusInlC5, m7PlusInlC6,
   m7PlusInlC7, m7PlusInlC8, m7PlusInlC9, m7PlusInlC10, m7PlusInlC11, m7PlusInlC12]

theorem m7PlusInlFns_length : m7PlusInlFns.length = 410 := by
  t_kernel_rfl

end LeanQbe.T.Examples.Kissat.FullM7PlusInl

abbrev m7p_inl_mod := @LeanQbe.T.Examples.Kissat.FullM7PlusInl.m7PlusInlMod
abbrev m7p_inl_eq := @LeanQbe.T.Examples.Kissat.FullM7PlusInl.m7PlusInlMod.eq
abbrev m7p_inl_fns_eq := @LeanQbe.T.Examples.Kissat.FullM7PlusInl.m7PlusInlMod.fns_eq

#print axioms m7p_inl_mod
#print axioms m7p_inl_eq
#print axioms m7p_inl_fns_eq
