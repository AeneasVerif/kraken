module

public import LeanQbe.T.Flat
public import LeanQbe.T.Module

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Inl.Arena.Exports

open LeanQbe.T

@[expose] def flat0 : TFlatFn := {
  name := "full_arena_next",
  as := [i64, i32],
  rs := [i32],
  body :=
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 1, .imm (BitVec.ofNat 64 112), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 3, .imm (BitVec.ofNat 64 48), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 4, ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 0, .imm (BitVec.ofNat 64 3), ())⟩ <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .ugt i64 .bool rfl, (.var 0, .var 2, ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.let_ (ts := [i32]) ⟨.trunc 64 32, (.var 3, ())⟩ <|
      TFlat.ret (.var 0, ())) <|
    TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 7, ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 7, .var 0, ())⟩ <|
    TFlat.load i32 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 11, ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 0, .imm (BitVec.ofNat 64 2), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 12, .var 0, ())⟩ <|
    TFlat.load i32 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 16, ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 0, .imm (BitVec.ofNat 64 3), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 2, ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 1, .var 0, ())⟩ <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .ugt i64 .bool rfl, (.var 0, .var 16, ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.let_ (ts := [i32]) ⟨.trunc 64 32, (.var 17, ())⟩ <|
      TFlat.ret (.var 0, ())) <|
    TFlat.group (sig := [[i64]])
      (TBlocks.cons (ts := [i64])
        (TFlat.let_ (ts := [i32]) ⟨.trunc 64 32, (.var 0, ())⟩ <|
        TFlat.ret (.var 0, ())) <|
      TBlocks.nil) <|
    TFlat.let_ (ts := [i32]) ⟨.and i32, (.var 10, .imm (BitVec.ofNat 32 8388608), ())⟩ <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .ne i32 .bool rfl,
      (.var 0, .imm (BitVec.ofNat 32 0), ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.group (sig := [[i64]])
        (TBlocks.cons (ts := [i64])
          (TFlat.group (sig := [[]])
            (TBlocks.cons (ts := [])
            (TFlat.group (sig := [[i64]])
            (TBlocks.cons (ts := [i64])
            (TFlat.jump (ts := [i64]) 3 (.var 0, ())) <|
            TBlocks.nil) <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .ult i64 .bool rfl, (.var 0, .var 20, ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 1, .imm (BitVec.ofNat 64 1), ())⟩ <|
            TFlat.jump (ts := [i64]) 0 (.var 0, ())) <|
            TFlat.jump (ts := [i64]) 0 (.var 1, ())) <|
            TBlocks.nil) <|
          TFlat.let_ (ts := [.bool]) ⟨.cmp .ult i64 .bool rfl, (.var 0, .var 20, ())⟩ <|
          TFlat.jnz (.var 0)
            (TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 1, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 24, .var 0, ())⟩ <|
            TFlat.load i32 (.var 0) <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .ne i32 .bool rfl,
            (.var 0, .imm (BitVec.ofNat 32 4294967295), ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 5, .imm (BitVec.ofNat 64 1), ())⟩ <|
            TFlat.jump (ts := [i64]) 1 (.var 0, ())) <|
            TFlat.jump (ts := []) 0 ()) <|
          TFlat.jump (ts := []) 0 ()) <|
        TBlocks.nil) <|
      TFlat.jump (ts := [i64]) 0 (.var 3, ())) <|
    TFlat.jump (ts := [i64]) 0 (.var 3, ()) }

@[expose] def flat1 : TFlatFn := {
  name := "full_alloc_cl",
  as := [i64, i32, i32, .bool],
  rs := [i64],
  body :=
    TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 2, ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.imm (BitVec.ofNat 64 3), .var 0, ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 5, .imm (BitVec.ofNat 64 32), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 7, .imm (BitVec.ofNat 64 48), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.sub i64, (.var 2, .var 0, ())⟩ <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .ugt i64 .bool rfl, (.var 5, .var 0, ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.ret (.imm (BitVec.ofNat 64 4294967295), ())) <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 11, .imm (BitVec.ofNat 64 48), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 0, .var 8, ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 14, .imm (BitVec.ofNat 64 48), ())⟩ <|
    TFlat.store (t := i64) (.var 1) (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 15, .imm (BitVec.ofNat 64 112), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.group (sig := [[i32]])
      (TBlocks.cons (ts := [i32])
        (TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 5, .imm (BitVec.ofNat 64 4), ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 2, .var 0, ())⟩ <|
        TFlat.group (sig := [[i32]])
          (TBlocks.cons (ts := [i32])
            (TFlat.let_ (ts := [i32]) ⟨.or i32, (.var 3, .var 0, ())⟩ <|
            TFlat.store (t := i32) (.var 0) (.var 2) <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 9, .imm (BitVec.ofNat 64 1), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 7, .var 0, ())⟩ <|
            TFlat.store (t := i32) (.imm (BitVec.ofNat 32 2)) (.var 0) <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 12, .imm (BitVec.ofNat 64 2), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 10, .var 0, ())⟩ <|
            TFlat.store (t := i32) (.var 27) (.var 0) <|
            TFlat.ret (.var 15, ())) <|
          TBlocks.nil) <|
        TFlat.jnz (.var 17)
          (TFlat.jump (ts := [i32]) 0 (.imm (BitVec.ofNat 32 4194304), ())) <|
        TFlat.jump (ts := [i32]) 0 (.imm (BitVec.ofNat 32 0), ())) <|
      TBlocks.nil) <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .ugt i32 .bool rfl,
      (.var 15, .imm (BitVec.ofNat 32 524287), ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.jump (ts := [i32]) 0 (.imm (BitVec.ofNat 32 524287), ())) <|
    TFlat.jump (ts := [i32]) 0 (.var 16, ()) }

@[expose] def fns : List Fn := [flat0.toFn, flat1.toFn]

end LeanQbe.T.Examples.Kissat.Build.Inl.Arena.Exports
