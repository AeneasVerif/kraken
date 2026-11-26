/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityInlData
public import LeanQbe.T.Examples.Kissat.FullFidelityInlProof

/-!
# Symbolic PGO-Inlined Module Barrel for `KissatFidelity` (`FullFidelityInl`, `499` fns)

Backwards-compatible re-export barrel combining:
- `FullFidelityInlData`: proof-free data (`fidInlMod`, `fidInlChunkMod`, structural identities)
  for certificate slices (`0` `*Proof*` imports, `0` printer `meta import`s).
- `FullFidelityInlProof`: `ModuleOk`, `Fn.Wf`, `checkAcyclic`, and `"kissat_solve_bytes"` proofs.

Executable `PrintCpp`/`PrintQbe` equivalence `#guard`s live in
`LeanQbeTest.T.KissatFidelityCodegenTest`.
-/

set_option autoImplicit false
