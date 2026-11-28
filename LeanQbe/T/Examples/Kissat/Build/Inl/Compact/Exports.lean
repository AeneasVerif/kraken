module

public import LeanQbe.T.Flat
public import LeanQbe.T.Module

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Inl.Compact.Exports

open LeanQbe.T

@[expose] def flat0 : TFlatFn := {
  name := "full_compact_needed",
  as := [i64],
  rs := [.bool],
  body :=
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 0, .imm (BitVec.ofNat 64 160), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .ne i64 .bool rfl,
      (.var 0, .imm (BitVec.ofNat 64 0), ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.ret (.imm false, ())) <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 3, .imm (BitVec.ofNat 64 1016), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .ne i64 .bool rfl,
      (.var 0, .imm (BitVec.ofNat 64 0), ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.ret (.imm false, ())) <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 6, .imm (BitVec.ofNat 64 776), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .ult i64 .bool rfl,
      (.var 0, .imm (BitVec.ofNat 64 128), ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.ret (.imm false, ())) <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 9, .imm (BitVec.ofNat 64 792), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .ule i64 .bool rfl, (.var 3, .var 0, ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.ret (.imm false, ())) <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 12, .imm (BitVec.ofNat 64 792), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.sub i64, (.var 6, .var 0, ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 10), ())⟩ <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .ugt i64 .bool rfl, (.var 0, .var 8, ())⟩ <|
    TFlat.ret (.var 0, ()) }

@[expose] def fns : List Fn := [flat0.toFn]

end LeanQbe.T.Examples.Kissat.Build.Inl.Compact.Exports
