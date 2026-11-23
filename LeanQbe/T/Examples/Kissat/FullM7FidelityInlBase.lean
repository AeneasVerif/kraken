/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.MainCertInlineChunk
public import LeanQbe.T.Examples.Kissat.FullM7FidelityAssembly
public import LeanQbe.T.Examples.Kissat.FullM7InlPolicy
meta import Lean
meta import LeanQbe.T.MainCertInlineChunk
meta import LeanQbe.T.Examples.Kissat.FullM7FidelityAssembly
meta import LeanQbe.T.Examples.Kissat.FullM7InlPolicy

/-!
# Chunked `FullM7Fidelity` PGO Inlining Base (`FullM7FidelityInlBase`)

Materializes `m7FidInlBase.siteCounts`, `m7FidInlBase.loopCounts`, and
`m7FidInlBase.rest0_eq` for `m7FidelityModule` (`413` fns) under `FullM7InlPolicy.m7InlPolicy`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM7FidelityInl

open LeanQbe.T LeanQbe.T.Examples.Kissat.FullM7Fidelity
open LeanQbe.T.Examples.Kissat.FullM7InlPolicy

inline_chunk_base! m7FidInlBase m7FidelityModule m7InlPolicy

end LeanQbe.T.Examples.Kissat.FullM7FidelityInl
