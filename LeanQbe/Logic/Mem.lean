module

public import LeanQbe.WP
public import Kraken.Separation

/-!
# Memory predicates for user proofs

Separation-logic predicates over Kraken's `Mem 64` (`Kraken.Separation`, `⋆`), in the byte layout
that `storeMem` (and so Kraken's x64 and AArch64 stores) produces. Lemmas are in `MemLemmas.lean`.

* `cell64 a v`: the 64-bit word `v` at address `a` (QBE `storel` / `loadl`).
* `array64 a xs`: the words `xs` at `a`, `a + 8`, ...
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe

open Std.ExtHashMap

/-- The 64-bit word `v` at address `a`, and nothing else. -/
def cell64 (a v : Val) : Mem 64 → Prop := Eq ((Int.toBytes 8 v.toInt).At a)

/-- Consecutive 64-bit words from address `a`. -/
def array64 (a : Val) : List Val → Mem 64 → Prop
  | [] => emp
  | v :: vs => cell64 a v ⋆ array64 (a + 8) vs

end LeanQbe
