module

public import LeanQbe.T.Flat
public import LeanQbe.T.Module

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Inl.Congruence.Exports

open LeanQbe.T

@[expose] def flat0 : TFlatFn := {
  name := "full_cong_find",
  as := [i64, i32],
  rs := [i32],
  body :=
    TFlat.group (sig := [[i32]])
      (TBlocks.cons (ts := [i32])
        (TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 0, ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 4, .var 0, ())⟩ <|
        TFlat.load i32 (.var 0) <|
        TFlat.let_ (ts := [.bool]) ⟨.cmp .ne i32 .bool rfl, (.var 0, .var 4, ())⟩ <|
        TFlat.jnz (.var 0)
          (TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 5, ())⟩ <|
          TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
          TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 9, .var 0, ())⟩ <|
          TFlat.load i32 (.var 0) <|
          TFlat.jump (ts := [i32]) 0 (.var 0, ())) <|
        TFlat.group (sig := [[i32]])
          (TBlocks.cons (ts := [i32])
            (TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 0, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 10, .var 0, ())⟩ <|
            TFlat.load i32 (.var 0) <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .ne i32 .bool rfl, (.var 0, .var 10, ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 5, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 15, .var 0, ())⟩ <|
            TFlat.load i32 (.var 0) <|
            TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 9, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 19, .var 0, ())⟩ <|
            TFlat.store (t := i32) (.var 18) (.var 0) <|
            TFlat.jump (ts := [i32]) 0 (.var 3, ())) <|
            TFlat.ret (.var 11, ())) <|
          TBlocks.nil) <|
        TFlat.jump (ts := [i32]) 0 (.var 6, ())) <|
      TBlocks.nil) <|
    TFlat.jump (ts := [i32]) 0 (.var 0, ()) }

@[expose] def fns : List Fn := [flat0.toFn]

end LeanQbe.T.Examples.Kissat.Build.Inl.Congruence.Exports
