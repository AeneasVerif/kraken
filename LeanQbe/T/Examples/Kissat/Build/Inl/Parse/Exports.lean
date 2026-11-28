module

public import LeanQbe.T.Flat
public import LeanQbe.T.Module

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Inl.Parse.Exports

open LeanQbe.T

@[expose] def flat0 : TFlatFn := {
  name := "full_parse_body",
  as := [i64, i64],
  rs := [i64],
  body :=
    TFlat.call "full_parse_body_m6" (as := [i64, i64]) [i64] (.var 1, .var 0, ()) <|
    TFlat.ret (.var 0, ()) }

@[expose] def fns : List Fn := [flat0.toFn]

end LeanQbe.T.Examples.Kissat.Build.Inl.Parse.Exports
