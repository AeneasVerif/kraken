/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.MainCertInlineChunk
public import LeanQbe.T.Examples.Kissat.FullM7FidelityAssembly
public import LeanQbe.T.Examples.Kissat.FullM7InlPolicy
public import LeanQbe.T.Examples.Kissat.FullM7FidelityInlBase
public import LeanQbe.T.Examples.Kissat.FullM7FidelityInl4
meta import Lean
meta import LeanQbe.T.MainCertInlineChunk
meta import LeanQbe.T.Examples.Kissat.FullM7FidelityAssembly
meta import LeanQbe.T.Examples.Kissat.FullM7InlPolicy
meta import LeanQbe.T.Examples.Kissat.FullM7FidelityInlBase
meta import LeanQbe.T.Examples.Kissat.FullM7FidelityInl4

/-!
# Chunked `FullM7Fidelity` PGO Inlining Chunk 5 (`[236, 258)`, `22` fns)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM7FidelityInl

open LeanQbe.T LeanQbe.T.Examples.Kissat.FullM7Fidelity
open LeanQbe.T.Examples.Kissat.FullM7InlPolicy

inline_mod_chunk! m7FidInlC5 m7FidInlBase m7FidelityModule m7InlPolicy 236 22
  (prev := m7FidInlC4)

end LeanQbe.T.Examples.Kissat.FullM7FidelityInl
