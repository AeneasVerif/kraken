module

public import LeanQbe.T.MainCertInlineChunk
public import LeanQbe.T.Examples.Kissat.FullM6
public import LeanQbe.T.Examples.Kissat.FullM6InlPolicy
meta import Lean
meta import LeanQbe.T.MainCertInlineChunk
meta import LeanQbe.T.Examples.Kissat.FullM6
meta import LeanQbe.T.Examples.Kissat.FullM6InlPolicy

/-!
# Chunked `FullM6` PGO Inlining Base (`FullM6InlBase`)

Materializes `m6InlBase.siteCounts`, `m6InlBase.loopCounts`, and `m6InlBase.rest0_eq`
connecting `(m6Module.optInlinePolicy m6InlPolicy).fns` to `inlRest ... 0 [] []`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM6Inl

open LeanQbe.T LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM6InlPolicy

inline_chunk_base! m6InlBase m6Module m6InlPolicy

end LeanQbe.T.Examples.Kissat.FullM6Inl
