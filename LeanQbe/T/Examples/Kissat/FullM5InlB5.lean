module

public import LeanQbe.T.MainCertInline
public import LeanQbe.T.Examples.Kissat.FullM5
meta import Lean
meta import LeanQbe.T.MainCertInline
meta import LeanQbe.T.Examples.Kissat.FullM5

/-!
# Materialized `InlinePolicy.b5` Module for Unified Kissat M5 (`FullM5InlB5`, `270` fns)

Evaluates `FullM5.m5Module.optInlinePolicy InlinePolicy.b5` once in MetaM via `inline_mod!`,
exporting:
* `m5InlB5Mod : Module` — literal `denoteFunc`-backed `270`-function inlined module;
* `m5InlB5Fns : List Fn` — `m5InlB5Mod.fns` (`270` functions);
* `m5InlB5Mod.eq : m5InlB5Mod = m5Module.optInlinePolicy InlinePolicy.b5`;
* `m5InlB5Mod.fns_eq : m5InlB5Mod.fns = (m5Module.optInlinePolicy InlinePolicy.b5).fns`.

Shared by both `LeanQbe.T.Amd64.KissatM5*` and `LeanQbe.T.Arm64.KissatM5*` so parallel
`compile_linked_chunks!` slices incur zero repeated inlining.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM5InlB5

open LeanQbe.T LeanQbe.T.Examples.Kissat.FullM5

inline_mod! m5InlB5Mod m5Module InlinePolicy.b5

/-- Materialized `InlinePolicy.b5` function list (`270` functions) for `FullM5`. -/
@[expose] noncomputable def m5InlB5Fns : List Fn := m5InlB5Mod.fns

theorem m5InlB5Fns_length : m5InlB5Fns.length = 270 := by
  t_kernel_rfl

#print axioms m5InlB5Mod
#print axioms m5InlB5Mod.eq

end LeanQbe.T.Examples.Kissat.FullM5InlB5
