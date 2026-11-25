/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.MainCertInlineChunk
public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep4
public import LeanQbe.T.Examples.Kissat.FullFidelityInlPolicy
meta import Lean
meta import LeanQbe.T.MainCertInlineChunk
meta import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep4
meta import LeanQbe.T.Examples.Kissat.FullFidelityInlPolicy

/-!
# Chunked `KissatFidelity` PGO Inlining Base (`FullFidelityInlBase`, Step 4: `478` fns)

Materializes `fidInlBase.siteCounts` (`= []`), `fidInlBase.loopCounts` (`= []`), and
`fidInlBase.rest0_eq` for `fidStep4Module` (`478` fns) under `fidInlChunkPolicy` (`< 1s`, zero
`fnsCallSites` / `fnsLoopCallSites` kernel AST scan).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityInl

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep4
open LeanQbe.T.Examples.Kissat.FullFidelityInlPolicy

inline_chunk_base! fidInlBase fidStep4Module fidInlChunkPolicy

end LeanQbe.T.Examples.Kissat.FullFidelityInl
