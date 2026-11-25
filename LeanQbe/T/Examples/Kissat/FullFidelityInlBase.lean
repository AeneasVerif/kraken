/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.MainCertInlineChunk
public import LeanQbe.T.Examples.Kissat.FullFidelityAssembly
public import LeanQbe.T.Examples.Kissat.FullFidelityInlPolicy
meta import Lean
meta import LeanQbe.T.MainCertInlineChunk
meta import LeanQbe.T.Examples.Kissat.FullFidelityAssembly
meta import LeanQbe.T.Examples.Kissat.FullFidelityInlPolicy

/-!
# Chunked `KissatFidelity` PGO Inlining Base (`FullFidelityInlBase`, `499` fns)

Materializes `fidInlBase.siteCounts` (`= []`), `fidInlBase.loopCounts` (`= []`), and
`fidInlBase.rest0_eq` for `fidModule` (`499` fns) under `fidInlChunkPolicy` (`< 1s`, zero
`fnsCallSites` / `fnsLoopCallSites` kernel AST scan).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityInl

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.FullFidelityAssembly
open LeanQbe.T.Examples.Kissat.FullFidelityInlPolicy

inline_chunk_base! fidInlBase fidModule fidInlChunkPolicy

end LeanQbe.T.Examples.Kissat.FullFidelityInl
