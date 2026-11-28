/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Module

/-!
# Gate G1 Toy Source Segment 2 (`Src2`)

Contains `toy_add_inc` (inlines `toy_inc` from `S1/Exports`, exported to `S3`) and
`toy_mix2` (calls out-of-line `toy_helper1`, inlines `toy_add_inc`, isolated via `fn_cert!`).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.SegCertToy.Src2

open LeanQbe.T

/-- Exported helper calling `toy_inc(x)` and adding `y`. -/
@[expose] def fnToyAddInc : Fn :=
  { name := "toy_add_inc", as := [i64, i64], rs := [i64]
    body := fun _ _ (x, y, ()) =>
      .call "toy_inc" (as := [i64]) (bs := [i64]) (.var x, ()) fun (t, ()) =>
      .let_ (ts := [i64]) ⟨.add i64, (.var t, .var y, ())⟩ fun (r, ()) =>
      .ret (.var r, ()) }

/-- Non-exported function isolated as a name-keyed `fn_cert!` target. -/
@[expose] def fnToyMix2 : Fn :=
  { name := "toy_mix2", as := [i64, i64], rs := [i64]
    body := fun _ _ (x, y, ()) =>
      .call "toy_helper1" (as := [i64]) (bs := [i64]) (.var x, ()) fun (a, ()) =>
      .call "toy_add_inc" (as := [i64, i64]) (bs := [i64]) (.var a, .var y, ()) fun (b, ()) =>
      .let_ (ts := [i64]) ⟨.add i64, (.var b, .imm 2#64, ())⟩ fun (r, ()) =>
      .ret (.var r, ()) }

/-- Source functions in segment 2. -/
@[expose] def fns : List Fn := [fnToyAddInc, fnToyMix2]

end LeanQbeTest.T.SegCertToy.Src2
