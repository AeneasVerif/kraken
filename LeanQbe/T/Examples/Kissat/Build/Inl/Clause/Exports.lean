module

public import LeanQbe.T.Flat
public import LeanQbe.T.Module

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Inl.Clause.Exports

open LeanQbe.T

@[expose] def flat0 : TFlatFn := {
  name := "full_add_bin",
  as := [i64, i32, i32],
  rs := [i64],
  body :=
    TFlat.call "full_add_bin_m6" (as := [i64, i32, i32]) [i64] (.var 2, .var 1, .var 0, ()) <|
    TFlat.ret (.var 0, ()) }

@[expose] def fns : List Fn := [flat0.toFn]

end LeanQbe.T.Examples.Kissat.Build.Inl.Clause.Exports
