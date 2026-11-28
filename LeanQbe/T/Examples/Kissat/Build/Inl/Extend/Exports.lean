module

public import LeanQbe.T.Flat
public import LeanQbe.T.Module

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Inl.Extend.Exports

open LeanQbe.T

@[expose] def flat0 : TFlatFn := {
  name := "full_extend_push2",
  as := [i64, i32, i32],
  rs := [.bool],
  body :=
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 2, .imm (BitVec.ofNat 64 776), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.sext 32 64, (.imm (BitVec.ofNat 32 1), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.shl i64, (.var 1, .var 0, ())⟩ <|
    TFlat.let_ (ts := [i32]) ⟨.and i32, (.var 4, .imm (BitVec.ofNat 32 2147483647), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 7, .imm (BitVec.ofNat 64 64), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 9, .imm (BitVec.ofNat 64 80), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.group (sig := [[.bool]])
      (TBlocks.cons (ts := [.bool])
        (TFlat.group (sig := [[i64]])
          (TBlocks.cons (ts := [i64])
            (TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 13, .imm (BitVec.ofNat 64 912), ())⟩ <|
            TFlat.load i64 (.var 0) <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 15, .imm (BitVec.ofNat 64 904), ())⟩ <|
            TFlat.load i64 (.var 0) <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .ugt i64 .bool rfl, (.var 2, .var 0, ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.ret (.imm false, ())) <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 18, .imm (BitVec.ofNat 64 904), ())⟩ <|
            TFlat.load i64 (.var 0) <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 20, .imm (BitVec.ofNat 64 912), ())⟩ <|
            TFlat.load i64 (.var 0) <|
            TFlat.let_ (ts := [i64]) ⟨.sub i64, (.var 2, .var 0, ())⟩ <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .ugt i64 .bool rfl, (.var 10, .var 0, ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.ret (.imm false, ())) <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 24, .imm (BitVec.ofNat 64 896), ())⟩ <|
            TFlat.load i64 (.var 0) <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 26, .imm (BitVec.ofNat 64 912), ())⟩ <|
            TFlat.load i64 (.var 0) <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 3, .var 0, ())⟩ <|
            TFlat.let_ (ts := [i32]) ⟨.and i32,
            (.var 29, .imm (BitVec.ofNat 32 2147483647), ())⟩ <|
            TFlat.let_ (ts := [i32]) ⟨.or i32,
            (.var 0, .imm (BitVec.ofNat 32 2147483648), ())⟩ <|
            TFlat.store (t := i32) (.var 0) (.var 2) <|
            TFlat.group (sig := [[]])
            (TBlocks.cons (ts := [])
            (TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 4, .var 19, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 33, .imm (BitVec.ofNat 64 912), ())⟩ <|
            TFlat.store (t := i64) (.var 1) (.var 0) <|
            TFlat.ret (.imm true, ())) <|
            TBlocks.nil) <|
            TFlat.jnz (.var 20)
            (TFlat.jump (ts := []) 0 ()) <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 4, .imm (BitVec.ofNat 64 1), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 8, .var 0, ())⟩ <|
            TFlat.store (t := i32) (.var 28) (.var 0) <|
            TFlat.jump (ts := []) 0 ()) <|
          TBlocks.nil) <|
        TFlat.jnz (.var 0)
          (TFlat.jump (ts := [i64]) 0 (.imm (BitVec.ofNat 64 1), ())) <|
        TFlat.jump (ts := [i64]) 0 (.imm (BitVec.ofNat 64 2), ())) <|
      TBlocks.nil) <|
    TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 4, ())⟩ <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .ult i64 .bool rfl, (.var 0, .var 6, ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.let_ (ts := [i32]) ⟨.lshr i32, (.var 6, .imm (BitVec.ofNat 32 1), ())⟩ <|
      TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 0, ())⟩ <|
      TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
      TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 5, .var 0, ())⟩ <|
      TFlat.load i32 (.var 0) <|
      TFlat.let_ (ts := [.bool]) ⟨.cmp .eq i32 .bool rfl,
        (.var 0, .imm (BitVec.ofNat 32 0), ())⟩ <|
      TFlat.jnz (.var 0)
        (TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 12, ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 11, .var 0, ())⟩ <|
        TFlat.load i8 (.var 0) <|
        TFlat.let_ (ts := [i8]) ⟨.trunc 32 8, (.imm (BitVec.ofNat 32 0), ())⟩ <|
        TFlat.let_ (ts := [i32]) ⟨.sext 8 32, (.var 1, ())⟩ <|
        TFlat.let_ (ts := [i32]) ⟨.sext 8 32, (.var 1, ())⟩ <|
        TFlat.let_ (ts := [.bool]) ⟨.cmp .slt i32 .bool rfl, (.var 1, .var 0, ())⟩ <|
        TFlat.jnz (.var 0)
          (TFlat.jump (ts := [.bool]) 0 (.imm true, ())) <|
        TFlat.jump (ts := [.bool]) 0 (.imm false, ())) <|
      TFlat.jump (ts := [.bool]) 0 (.imm false, ())) <|
    TFlat.jump (ts := [.bool]) 0 (.imm false, ()) }

@[expose] def flat1 : TFlatFn := {
  name := "full_extend",
  as := [i64],
  rs := [],
  body :=
    TFlat.call "full_extend_core_fid" (as := [i64]) [] (.var 0, ()) <|
    TFlat.call "full_unperm_fid" (as := [i64]) [] (.var 0, ()) <|
    TFlat.ret () }

@[expose] def fns : List Fn := [flat0.toFn, flat1.toFn]

end LeanQbe.T.Examples.Kissat.Build.Inl.Extend.Exports
