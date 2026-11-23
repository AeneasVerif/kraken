module

public import LeanQbe.T.MainCertInlineChunk
public import LeanQbe.T.Examples.Kissat.FullM7
public import LeanQbe.T.Examples.Kissat.FullM7InlPolicy
public import LeanQbe.T.Examples.Kissat.FullM7InlBase
public import LeanQbe.T.Examples.Kissat.FullM7Inl4
meta import Lean
meta import LeanQbe.T.MainCertInlineChunk
meta import LeanQbe.T.Examples.Kissat.FullM7
meta import LeanQbe.T.Examples.Kissat.FullM7InlPolicy
meta import LeanQbe.T.Examples.Kissat.FullM7InlBase
meta import LeanQbe.T.Examples.Kissat.FullM7Inl4

/-!
# Chunked `FullM7` PGO Inlining Chunk 5 (`[320, 384)`, `64` fns)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM7Inl

open LeanQbe.T LeanQbe.T.Examples.Kissat.FullM7
open LeanQbe.T.Examples.Kissat.FullM7InlPolicy

inline_mod_chunk! m7InlC5 m7InlBase m7Module m7InlPolicy 320 64 (prev := m7InlC4)

end LeanQbe.T.Examples.Kissat.FullM7Inl
