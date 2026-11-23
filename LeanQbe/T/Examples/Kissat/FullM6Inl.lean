module

public import LeanQbe.T.MainCertInlineChunk
public import LeanQbe.T.Examples.Kissat.FullM6
public import LeanQbe.T.Examples.Kissat.FullM6InlPolicy
public import LeanQbe.T.Examples.Kissat.FullM6InlBase
public import LeanQbe.T.Examples.Kissat.FullM6Inl0
public import LeanQbe.T.Examples.Kissat.FullM6Inl1
public import LeanQbe.T.Examples.Kissat.FullM6Inl2
public import LeanQbe.T.Examples.Kissat.FullM6Inl3
public import LeanQbe.T.Examples.Kissat.FullM6Inl4
public import LeanQbe.T.Examples.Kissat.FullM6Inl5
meta import Lean
meta import LeanQbe.T.MainCertInlineChunk
meta import LeanQbe.T.Examples.Kissat.FullM6
meta import LeanQbe.T.Examples.Kissat.FullM6InlPolicy
meta import LeanQbe.T.Examples.Kissat.FullM6InlBase
meta import LeanQbe.T.Examples.Kissat.FullM6Inl0
meta import LeanQbe.T.Examples.Kissat.FullM6Inl1
meta import LeanQbe.T.Examples.Kissat.FullM6Inl2
meta import LeanQbe.T.Examples.Kissat.FullM6Inl3
meta import LeanQbe.T.Examples.Kissat.FullM6Inl4
meta import LeanQbe.T.Examples.Kissat.FullM6Inl5

/-!
# Materialized Profile-Guided Inlined Module for Unified Kissat M6 (`FullM6Inl`, `382` fns)

Joins the 6 materialized `denoteFunc`-backed chunks (`FullM6Inl0..5`) into:
* `m6InlFns : List Fn` (`382` functions)
* `m6InlMod : Module`
* `m6InlMod.fns_eq : m6InlMod.fns = (m6Module.optInlinePolicy m6InlPolicy).fns`
* `m6InlMod.eq : m6InlMod = m6Module.optInlinePolicy m6InlPolicy`

Peak build RSS per chunk stays well under `8 GB` (`std3` axioms only).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM6Inl

open LeanQbe.T LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM6InlPolicy

inline_mod_join! m6InlMod m6InlFns m6Module m6InlPolicy m6InlBase
  [m6InlC0, m6InlC1, m6InlC2, m6InlC3, m6InlC4, m6InlC5]

theorem m6InlFns_length : m6InlFns.length = 382 := by
  t_kernel_rfl

#print axioms m6InlMod
#print axioms m6InlMod.eq
#print axioms m6InlMod.fns_eq

end LeanQbe.T.Examples.Kissat.FullM6Inl
