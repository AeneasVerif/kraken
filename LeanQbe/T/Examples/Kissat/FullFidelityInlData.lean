/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.MainInline
public import LeanQbe.T.Examples.Kissat.FullFidelityAssembly
public import LeanQbe.T.Examples.Kissat.FullFidelityInlPolicy
public import LeanQbe.T.Examples.Kissat.FullFidelityInlBase

/-!
# Proof-Free PGO-Inlined Module Data for `KissatFidelity` (`FullFidelityInlData`, `499` fns)

Pure data-only split of `FullFidelityInl` carrying `fidInlMod`, `fidInlChunkMod`, and their
proof-free structural identities (`*_eq`, `*_exits`, `*_sigs`), with **zero** `*Proof*` imports
and **zero** `meta import`s of `PrintCpp`, `PrintQbe`, or `Legal`.

Downstream certificate slices import ONLY `FullFidelityInlData` so proof-only edits in
`FullFidelity*Proof*` or printer edits never bust Lake 5.0's `transTrace`/`metaTransTrace` cache.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityInl

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.FullFidelityAssembly
open LeanQbe.T.Examples.Kissat.FullFidelityInlPolicy

/-- PGO-inlined and renormalized Gate-1 `KissatFidelity` module (`499` functions). -/
abbrev fidInlMod : Module :=
  fidModule.optInlinePolicy fidInlPolicy

/-- Definitional unfolding of `fidInlMod`. -/
theorem fidInlMod_eq : fidInlMod = fidModule.optInlinePolicy fidInlPolicy :=
  rfl

/-- `fidInlMod` preserves `exits = []`. -/
theorem fidInlMod_exits : fidInlMod.exits = [] :=
  fid_noExit

/-- `fidInlMod.fns` preserves the exact function-signature list of `fidModule.fns`. -/
theorem fidInlFns_sigs :
    fidInlMod.fns.map Fn.sig = fidModule.fns.map Fn.sig := by
  have h := Module.optInlinePolicy_sigs fidModule fidInlPolicy
  simp only [Module.sigs, Module.optInlinePolicy_externs] at h
  exact List.append_cancel_right h

/-- Zero-scan chunk-materializable Gate-1 PGO-inlined module (`fidInlChunkPolicy`). -/
abbrev fidInlChunkMod : Module :=
  fidModule.optInlinePolicy fidInlChunkPolicy

/-- Definitional unfolding of `fidInlChunkMod`. -/
theorem fidInlChunkMod_eq : fidInlChunkMod = fidModule.optInlinePolicy fidInlChunkPolicy :=
  rfl

/-- `fidInlChunkMod` preserves `exits = []`. -/
theorem fidInlChunkMod_exits : fidInlChunkMod.exits = [] :=
  fid_noExit

/-- `fidInlChunkMod.fns` preserves the exact function-signature list of `fidModule.fns`. -/
theorem fidInlChunkFns_sigs :
    fidInlChunkMod.fns.map Fn.sig = fidModule.fns.map Fn.sig := by
  have h := Module.optInlinePolicy_sigs fidModule fidInlChunkPolicy
  simp only [Module.sigs, Module.optInlinePolicy_externs] at h
  exact List.append_cancel_right h

end LeanQbe.T.Examples.Kissat.FullFidelityInl

end
