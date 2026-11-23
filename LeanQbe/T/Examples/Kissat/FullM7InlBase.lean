module

public import LeanQbe.T.MainCertInlineChunk
public import LeanQbe.T.Examples.Kissat.FullM7
public import LeanQbe.T.Examples.Kissat.FullM7InlPolicy
meta import Lean
meta import LeanQbe.T.MainCertInlineChunk
meta import LeanQbe.T.Examples.Kissat.FullM7
meta import LeanQbe.T.Examples.Kissat.FullM7InlPolicy

/-!
# Chunked `FullM7` PGO Inlining Base (`FullM7InlBase`)

Materializes `m7InlBase.siteCounts`, `m7InlBase.loopCounts`, and `m7InlBase.rest0_eq`
connecting `(m7Module.optInlinePolicy m7InlPolicy).fns` to `inlRest ... 0 [] []`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM7Inl

open LeanQbe.T LeanQbe.T.Examples.Kissat.FullM7
open LeanQbe.T.Examples.Kissat.FullM7InlPolicy

inline_chunk_base! m7InlBase m7Module m7InlPolicy

end LeanQbe.T.Examples.Kissat.FullM7Inl
