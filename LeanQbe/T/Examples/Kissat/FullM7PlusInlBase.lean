/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.MainCertInlineChunk
public import LeanQbe.T.Examples.Kissat.FullM7PlusAssembly
public import LeanQbe.T.Examples.Kissat.FullM7InlPolicy
meta import Lean
meta import LeanQbe.T.MainCertInlineChunk
meta import LeanQbe.T.Examples.Kissat.FullM7PlusAssembly
meta import LeanQbe.T.Examples.Kissat.FullM7InlPolicy

/-!
# Chunked `FullM7Plus` PGO Inlining Base (`FullM7PlusInlBase`)

Materializes `m7PlusInlBase.siteCounts`, `m7PlusInlBase.loopCounts`, and
`m7PlusInlBase.rest0_eq` for `m7PlusModule` (`410` fns) under `FullM7InlPolicy.m7InlPolicy`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM7PlusInl

open LeanQbe.T LeanQbe.T.Examples.Kissat.FullM7Plus
open LeanQbe.T.Examples.Kissat.FullM7InlPolicy

inline_chunk_base! m7PlusInlBase m7PlusModule m7InlPolicy

end LeanQbe.T.Examples.Kissat.FullM7PlusInl
