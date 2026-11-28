module

public import LeanQbe.T.Flat
public import LeanQbe.T.Module

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Inl.Deduce.Exports

open LeanQbe.T

@[expose] def flat0 : TFlatFn := {
  name := "full_clear_ana",
  as := [i64],
  rs := [],
  body :=
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 0, .imm (BitVec.ofNat 64 72), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 2, .imm (BitVec.ofNat 64 848), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 4, .imm (BitVec.ofNat 64 776), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.group (sig := [[i64]])
      (TBlocks.cons (ts := [i64])
        (TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 7, .imm (BitVec.ofNat 64 272), ())⟩ <|
        TFlat.load i64 (.var 0) <|
        TFlat.let_ (ts := [.bool]) ⟨.cmp .ult i64 .bool rfl, (.var 2, .var 0, ())⟩ <|
        TFlat.jnz (.var 0)
          (TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 3, .imm (BitVec.ofNat 64 4), ())⟩ <|
          TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 7, .var 0, ())⟩ <|
          TFlat.load i32 (.var 0) <|
          TFlat.group (sig := [[]])
            (TBlocks.cons (ts := [])
            (TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 6, .imm (BitVec.ofNat 64 1), ())⟩ <|
            TFlat.jump (ts := [i64]) 1 (.var 0, ())) <|
            TBlocks.nil) <|
          TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 0, ())⟩ <|
          TFlat.let_ (ts := [.bool]) ⟨.cmp .ult i64 .bool rfl, (.var 0, .var 8, ())⟩ <|
          TFlat.jnz (.var 0)
            (TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 2, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 14, .var 0, ())⟩ <|
            TFlat.let_ (ts := [i8]) ⟨.trunc 32 8, (.imm (BitVec.ofNat 32 0), ())⟩ <|
            TFlat.store (t := i8) (.var 0) (.var 1) <|
            TFlat.jump (ts := []) 0 ()) <|
          TFlat.jump (ts := []) 0 ()) <|
        TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 10, .imm (BitVec.ofNat 64 272), ())⟩ <|
        TFlat.store (t := i64) (.imm (BitVec.ofNat 64 0)) (.var 0) <|
        TFlat.ret ()) <|
      TBlocks.nil) <|
    TFlat.jump (ts := [i64]) 0 (.imm (BitVec.ofNat 64 0), ()) }

@[expose] def fns : List Fn := [flat0.toFn]

end LeanQbe.T.Examples.Kissat.Build.Inl.Deduce.Exports
