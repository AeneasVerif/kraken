/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.MainCertInlineChunk
public import LeanQbe.T.Examples.Kissat.FullM7
public import LeanQbe.T.Examples.Kissat.FullM7InlPolicy
public import LeanQbe.T.Examples.Kissat.FullM7InlBase
public import LeanQbe.T.Examples.Kissat.FullM7Inl0
public import LeanQbe.T.Examples.Kissat.FullM7Inl1
public import LeanQbe.T.Examples.Kissat.FullM7Inl2
public import LeanQbe.T.Examples.Kissat.FullM7Inl3
public import LeanQbe.T.Examples.Kissat.FullM7Inl4
public import LeanQbe.T.Examples.Kissat.FullM7Inl5
public import LeanQbe.T.Examples.Kissat.FullM7Inl6
public import LeanQbe.T.Examples.Kissat.FullM7Inl7
public import LeanQbe.T.Examples.Kissat.FullM7Inl8
public import LeanQbe.T.Examples.Kissat.FullM7Inl9
public import LeanQbe.T.Examples.Kissat.FullM7Inl10
public import LeanQbe.T.Examples.Kissat.FullM7Inl11
public import LeanQbe.T.Examples.Kissat.FullM7Inl12
meta import Lean
meta import LeanQbe.T.MainCertInlineChunk
meta import LeanQbe.T.Examples.Kissat.FullM7
meta import LeanQbe.T.Examples.Kissat.FullM7InlPolicy
meta import LeanQbe.T.Examples.Kissat.FullM7InlBase
meta import LeanQbe.T.Examples.Kissat.FullM7Inl0
meta import LeanQbe.T.Examples.Kissat.FullM7Inl1
meta import LeanQbe.T.Examples.Kissat.FullM7Inl2
meta import LeanQbe.T.Examples.Kissat.FullM7Inl3
meta import LeanQbe.T.Examples.Kissat.FullM7Inl4
meta import LeanQbe.T.Examples.Kissat.FullM7Inl5
meta import LeanQbe.T.Examples.Kissat.FullM7Inl6
meta import LeanQbe.T.Examples.Kissat.FullM7Inl7
meta import LeanQbe.T.Examples.Kissat.FullM7Inl8
meta import LeanQbe.T.Examples.Kissat.FullM7Inl9
meta import LeanQbe.T.Examples.Kissat.FullM7Inl10
meta import LeanQbe.T.Examples.Kissat.FullM7Inl11
meta import LeanQbe.T.Examples.Kissat.FullM7Inl12

/-!
# Materialized Profile-Guided Inlined Module for Unified Kissat M7 (`FullM7Inl`, `410` fns)

Joins the `13` materialized `denoteFunc`-backed chunks (`FullM7Inl0..12`) into:
* `m7InlFns : List Fn` (`410` functions)
* `m7InlMod : Module`
* `m7InlMod.fns_eq : m7InlMod.fns = (m7Module.optInlinePolicy m7InlPolicy).fns`
* `m7InlMod.eq : m7InlMod = m7Module.optInlinePolicy m7InlPolicy`

Peak build RSS per chunk stays well below worker limits (`std3` axioms only).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM7Inl

open LeanQbe.T LeanQbe.T.Examples.Kissat.FullM7
open LeanQbe.T.Examples.Kissat.FullM7InlPolicy

inline_mod_join! m7InlMod m7InlFns m7Module m7InlPolicy m7InlBase
  [m7InlC0, m7InlC1, m7InlC2, m7InlC3, m7InlC4, m7InlC5, m7InlC6,
   m7InlC7, m7InlC8, m7InlC9, m7InlC10, m7InlC11, m7InlC12]

theorem m7InlFns_length : m7InlFns.length = 410 := by
  t_kernel_rfl

#print axioms m7InlMod
#print axioms m7InlMod.eq
#print axioms m7InlMod.fns_eq

end LeanQbe.T.Examples.Kissat.FullM7Inl
