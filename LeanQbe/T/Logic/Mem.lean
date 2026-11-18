module

public import LeanQbe.T.WP
public import Kraken.Separation

/-!
# Separation-logic memory predicates for `LeanQbe.T` (`T4`)

Predicates over Kraken's `Mem 64` (`Kraken.Separation`, `⋆`) matching `LeanQbe.T.storeMem` /
`LeanQbe.T.loadVal`:

* `cell a v`: typed value `v : Val t` at address `a` (bit-packed in `t.bytes` little-endian bytes).
* `cell64 a v`: 64-bit word `v` at address `a` (definitionally `cell (t := i64) a v`).
* `array a xs`: consecutive `t.bytes`-spaced typed values `xs` starting at `a`.
* `array64 a xs`: consecutive 64-bit words `xs` starting at `a`.
* `bytes a bs`: concrete byte slice `bs` at address `a`.
* `region a n`: `n` arbitrary mapped bytes starting at address `a`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

open Std.ExtHashMap

/-- A typed value `v : Val t` stored at address `a` in `T.storeMem` byte layout, and nothing else. -/
def cell {t : Ty} (a : BitVec 64) (v : Val t) : Mem 64 → Prop :=
  Eq ((Int.toBytes t.bytes ((toBits t v).setWidth (8 * t.bytes)).toInt).At a)

/-- A 64-bit word `v` at address `a`, and nothing else (definitionally `cell (t := i64) a v`). -/
def cell64 (a v : BitVec 64) : Mem 64 → Prop :=
  Eq ((Int.toBytes 8 v.toInt).At a)

/-- Consecutive typed values `xs` at `a`, `a + t.bytes`, … -/
def array {t : Ty} (a : BitVec 64) : List (Val t) → Mem 64 → Prop
  | [] => emp
  | v :: vs => cell a v ⋆ array (a + BitVec.ofNat 64 t.bytes) vs

/-- Consecutive 64-bit words from address `a`. -/
def array64 (a : BitVec 64) : List (BitVec 64) → Mem 64 → Prop
  | [] => emp
  | v :: vs => cell64 a v ⋆ array64 (a + 8) vs

/-- Concrete byte slice `bs` at address `a`. -/
def bytes (a : BitVec 64) (bs : List UInt8) : Mem 64 → Prop :=
  Eq (bs.At a)

/-- `n` mapped bytes starting at `a` (wrapping around), with arbitrary contents. -/
def region (a : BitVec 64) (n : Nat) : Mem 64 → Prop :=
  fun f => ∃ bs : List UInt8, bs.length = n ∧ f = bs.At a

end LeanQbe.T
