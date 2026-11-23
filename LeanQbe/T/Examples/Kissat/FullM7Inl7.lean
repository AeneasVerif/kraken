/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.MainCertInlineChunk
public import LeanQbe.T.Examples.Kissat.FullM7
public import LeanQbe.T.Examples.Kissat.FullM7InlPolicy
public import LeanQbe.T.Examples.Kissat.FullM7InlBase
public import LeanQbe.T.Examples.Kissat.FullM7Inl6
meta import Lean
meta import LeanQbe.T.MainCertInlineChunk
meta import LeanQbe.T.Examples.Kissat.FullM7
meta import LeanQbe.T.Examples.Kissat.FullM7InlPolicy
meta import LeanQbe.T.Examples.Kissat.FullM7InlBase
meta import LeanQbe.T.Examples.Kissat.FullM7Inl6

/-!
# Chunked `FullM7` PGO Inlining Chunk 7 (`[280, 302)`, `22` fns)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM7Inl

open LeanQbe.T LeanQbe.T.Examples.Kissat.FullM7
open LeanQbe.T.Examples.Kissat.FullM7InlPolicy

inline_mod_chunk! m7InlC7 m7InlBase m7Module m7InlPolicy 280 22 (prev := m7InlC6)

end LeanQbe.T.Examples.Kissat.FullM7Inl
