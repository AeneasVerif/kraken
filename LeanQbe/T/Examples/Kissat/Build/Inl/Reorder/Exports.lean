module

public import LeanQbe.T.Flat
public import LeanQbe.T.Module

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Inl.Reorder.Exports

open LeanQbe.T

@[expose] def flat0 : TFlatFn := {
  name := "full_reorder_m6",
  as := [i64, i64],
  rs := [i64],
  body :=
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 1, .imm (BitVec.ofNat 64 160), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .ne i64 .bool rfl,
      (.var 0, .imm (BitVec.ofNat 64 0), ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.ret (.imm (BitVec.ofNat 64 0), ())) <|
    TFlat.call "full_reorder_queue_m7" (as := [i64]) [i64] (.var 4, ()) <|
    TFlat.ret (.var 0, ()) }

@[expose] def fns : List Fn := [flat0.toFn]

end LeanQbe.T.Examples.Kissat.Build.Inl.Reorder.Exports
