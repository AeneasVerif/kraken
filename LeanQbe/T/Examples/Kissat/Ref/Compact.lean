/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Ref

/-- Unmaps a compacted literal `l` using inverse variable table `inv` (`inv[v] = old_v`). -/
@[expose] def compactUnmapLit (inv : List (BitVec 32)) (l : Nat) : Nat :=
  2 * (inv[l / 2]?.getD 0#32).toNat + l % 2

end LeanQbe.T.Examples.Kissat.Ref
