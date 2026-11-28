module

public import LeanQbe.T.Flat
public import LeanQbe.T.Module

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Inl.Bump.Exports

open LeanQbe.T

@[expose] def flat0 : TFlatFn := {
  name := "full_rescale",
  as := [i64],
  rs := [],
  body :=
    TFlat.call "full_rescale_m6" (as := [i64]) [] (.var 0, ()) <|
    TFlat.ret () }

@[expose] def fns : List Fn := [flat0.toFn]

end LeanQbe.T.Examples.Kissat.Build.Inl.Bump.Exports
