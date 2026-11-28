module

public import LeanQbe.T.Flat
public import LeanQbe.T.Module

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Inl.Gates.Exports

open LeanQbe.T

@[expose] def flat0 : TFlatFn := {
  name := "full_bve_find_ite_m7",
  as := [i64, i32, i32, i32],
  rs := [.bool],
  body :=
    TFlat.call "full_bve_find_ite_side_m7" (as := [i64, i32, i32, i32, .bool]) [.bool]
      (.var 3, .var 2, .var 1, .var 0, .imm false, ()) <|
    TFlat.jnz (.var 0)
      (TFlat.ret (.imm true, ())) <|
    TFlat.call "full_bve_find_ite_side_m7" (as := [i64, i32, i32, i32, .bool]) [.bool]
      (.var 4, .var 3, .var 2, .var 1, .imm true, ()) <|
    TFlat.ret (.var 0, ()) }

@[expose] def flat1 : TFlatFn := {
  name := "full_bve_find_ite_m8",
  as := [i64, i32, i32, i32],
  rs := [.bool],
  body :=
    TFlat.call "full_bve_find_ite_side_m8" (as := [i64, i32, i32, i32, .bool]) [.bool]
      (.var 3, .var 2, .var 1, .var 0, .imm false, ()) <|
    TFlat.jnz (.var 0)
      (TFlat.ret (.imm true, ())) <|
    TFlat.call "full_bve_find_ite_side_m8" (as := [i64, i32, i32, i32, .bool]) [.bool]
      (.var 4, .var 3, .var 2, .var 1, .imm true, ()) <|
    TFlat.ret (.var 0, ()) }

@[expose] def fns : List Fn := [flat0.toFn, flat1.toFn]

end LeanQbe.T.Examples.Kissat.Build.Inl.Gates.Exports
