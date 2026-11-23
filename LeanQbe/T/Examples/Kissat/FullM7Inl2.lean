module

public import LeanQbe.T.MainCertInlineChunk
public import LeanQbe.T.Examples.Kissat.FullM7
public import LeanQbe.T.Examples.Kissat.FullM7InlPolicy
public import LeanQbe.T.Examples.Kissat.FullM7InlBase
public import LeanQbe.T.Examples.Kissat.FullM7Inl1
meta import Lean
meta import LeanQbe.T.MainCertInlineChunk
meta import LeanQbe.T.Examples.Kissat.FullM7
meta import LeanQbe.T.Examples.Kissat.FullM7InlPolicy
meta import LeanQbe.T.Examples.Kissat.FullM7InlBase
meta import LeanQbe.T.Examples.Kissat.FullM7Inl1

/-!
# Chunked `FullM7` PGO Inlining Chunk 2 (`[128, 192)`, `64` fns)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM7Inl

open LeanQbe.T LeanQbe.T.Examples.Kissat.FullM7
open LeanQbe.T.Examples.Kissat.FullM7InlPolicy

inline_mod_chunk! m7InlC2 m7InlBase m7Module m7InlPolicy 128 64 (prev := m7InlC1)

end LeanQbe.T.Examples.Kissat.FullM7Inl
