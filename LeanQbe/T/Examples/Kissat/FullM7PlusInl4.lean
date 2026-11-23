/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.MainCertInlineChunk
public import LeanQbe.T.Examples.Kissat.FullM7PlusAssembly
public import LeanQbe.T.Examples.Kissat.FullM7InlPolicy
public import LeanQbe.T.Examples.Kissat.FullM7PlusInlBase
public import LeanQbe.T.Examples.Kissat.FullM7PlusInl3
meta import Lean
meta import LeanQbe.T.MainCertInlineChunk
meta import LeanQbe.T.Examples.Kissat.FullM7PlusAssembly
meta import LeanQbe.T.Examples.Kissat.FullM7InlPolicy
meta import LeanQbe.T.Examples.Kissat.FullM7PlusInlBase
meta import LeanQbe.T.Examples.Kissat.FullM7PlusInl3

/-!
# Chunked `FullM7Plus` PGO Inlining Chunk 4 (`[214, 236)`, `22` fns)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM7PlusInl

open LeanQbe.T LeanQbe.T.Examples.Kissat.FullM7Plus
open LeanQbe.T.Examples.Kissat.FullM7InlPolicy

inline_mod_chunk! m7PlusInlC4 m7PlusInlBase m7PlusModule m7InlPolicy 214 22 (prev := m7PlusInlC3)

end LeanQbe.T.Examples.Kissat.FullM7PlusInl
