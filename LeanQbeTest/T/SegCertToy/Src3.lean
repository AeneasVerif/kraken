/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Module

/-!
# Gate G1 Toy Source Segment 3 (`Src3`)

Contains `toy_step3` (inlines `toy_add_inc` from `S2/Exports` and `toy_inc` from `S1/Exports`)
and `toy_main` (calls out-of-line `toy_mix2` and `toy_step3`).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.SegCertToy.Src3

open LeanQbe.T

/-- Non-exported step in segment 3 exercising multi-dep inlining (`S1` + `S2`). -/
@[expose] def fnToyStep3 : Fn :=
  { name := "toy_step3", as := [i64], rs := [i64]
    body := fun _ _ (x, ()) =>
      .call "toy_add_inc" (as := [i64, i64]) (bs := [i64]) (.var x, .imm 10#64, ()) fun (a, ()) =>
      .call "toy_inc" (as := [i64]) (bs := [i64]) (.var a, ()) fun (b, ()) =>
      .let_ (ts := [i64]) ⟨.add i64, (.var b, .imm 5#64, ())⟩ fun (r, ()) =>
      .ret (.var r, ()) }

/-- Entry function combining `toy_mix2` (isolated heavy fn in `S2`) and `toy_step3`. -/
@[expose] def fnToyMain : Fn :=
  { name := "toy_main", as := [i64, i64], rs := [i64]
    body := fun _ _ (x, y, ()) =>
      .call "toy_mix2" (as := [i64, i64]) (bs := [i64]) (.var x, .var y, ()) fun (a, ()) =>
      .call "toy_step3" (as := [i64]) (bs := [i64]) (.var x, ()) fun (b, ()) =>
      .let_ (ts := [i64]) ⟨.add i64, (.var a, .var b, ())⟩ fun (r, ()) =>
      .ret (.var r, ()) }

/-- Source functions in segment 3. -/
@[expose] def fns : List Fn := [fnToyStep3, fnToyMain]

end LeanQbeTest.T.SegCertToy.Src3
