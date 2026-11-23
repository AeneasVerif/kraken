module

public import LeanQbe.T.MainCertInlineChunk
public import LeanQbe.T.Examples.Kissat.FullM6
public import LeanQbe.T.Examples.Kissat.FullM6InlPolicy
public import LeanQbe.T.Examples.Kissat.FullM6InlBase
public import LeanQbe.T.Examples.Kissat.FullM6Inl1
meta import Lean
meta import LeanQbe.T.MainCertInlineChunk
meta import LeanQbe.T.Examples.Kissat.FullM6
meta import LeanQbe.T.Examples.Kissat.FullM6InlPolicy
meta import LeanQbe.T.Examples.Kissat.FullM6InlBase
meta import LeanQbe.T.Examples.Kissat.FullM6Inl1

/-!
# Chunked `FullM6` PGO Inlining Chunk 2 (`[128, 192)`, `64` fns)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM6Inl

open LeanQbe.T LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM6InlPolicy

inline_mod_chunk! m6InlC2 m6InlBase m6Module m6InlPolicy 128 64 (prev := m6InlC1)

end LeanQbe.T.Examples.Kissat.FullM6Inl
