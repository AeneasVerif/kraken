module

public import LeanQbe.T.Flat
public import LeanQbe.T.Module

set_option autoImplicit false

public section

namespace LeanQbeTest.T.SegCertToy.Build.Inl.S2.Exports

open LeanQbe.T

@[expose] def flat0 : TFlatFn := {
  name := "toy_add_inc",
  as := [i64, i64],
  rs := [i64],
  body :=
    TFlat.group (sig := [[i64]])
      (TBlocks.cons (ts := [i64])
        (TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 0, .var 1, ())⟩ <|
        TFlat.ret (.var 0, ())) <|
      TBlocks.nil) <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 1, .imm (BitVec.ofNat 64 1), ())⟩ <|
    TFlat.jump (ts := [i64]) 0 (.var 0, ()) }

@[expose] def fns : List Fn := [flat0.toFn]

end LeanQbeTest.T.SegCertToy.Build.Inl.S2.Exports
