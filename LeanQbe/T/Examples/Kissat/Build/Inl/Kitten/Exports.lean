module

public import LeanQbe.T.Flat
public import LeanQbe.T.Module

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Inl.Kitten.Exports

open LeanQbe.T

@[expose] def flat0 : TFlatFn := {
  name := "full_m6_max_v",
  as := [i64],
  rs := [i64],
  body :=
    TFlat.let_ (ts := [.bool]) ⟨.cmp .ult i64 .bool rfl,
      (.var 0, .imm (BitVec.ofNat 64 24576), ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.ret (.imm (BitVec.ofNat 64 0), ())) <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .uge i64 .bool rfl,
      (.var 1, .imm (BitVec.ofNat 64 524288), ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.ret (.imm (BitVec.ofNat 64 8192), ())) <|
    TFlat.let_ (ts := [i64]) ⟨.sub i64, (.var 2, .imm (BitVec.ofNat 64 1312), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.udiv 64, (.var 0, .imm (BitVec.ofNat 64 45), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.and i64,
      (.var 0, .imm (BitVec.ofNat 64 18446744073709551552), ())⟩ <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .ult i64 .bool rfl,
      (.var 0, .imm (BitVec.ofNat 64 512), ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.ret (.imm (BitVec.ofNat 64 512), ())) <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .ugt i64 .bool rfl,
      (.var 1, .imm (BitVec.ofNat 64 8192), ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.ret (.imm (BitVec.ofNat 64 8192), ())) <|
    TFlat.ret (.var 2, ()) }

@[expose] def flat1 : TFlatFn := {
  name := "full_k6_flip",
  as := [i64, i32],
  rs := [.bool],
  body :=
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 1, .imm (BitVec.ofNat 64 928), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.group (sig := [[i64]])
      (TBlocks.cons (ts := [i64])
        (TFlat.let_ (ts := [i32]) ⟨.trunc 64 32, (.var 0, ())⟩ <|
        TFlat.let_ (ts := [.bool]) ⟨.cmp .eq i32 .bool rfl,
          (.var 0, .imm (BitVec.ofNat 32 0), ())⟩ <|
        TFlat.jnz (.var 0)
          (TFlat.ret (.imm false, ())) <|
        TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 6, .imm (BitVec.ofNat 64 920), ())⟩ <|
        TFlat.load i64 (.var 0) <|
        TFlat.let_ (ts := [i32]) ⟨.shl i32, (.var 3, .imm (BitVec.ofNat 32 1), ())⟩ <|
        TFlat.let_ (ts := [i32]) ⟨.add i32, (.imm (BitVec.ofNat 32 1280), .var 0, ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 0, ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 4, .var 0, ())⟩ <|
        TFlat.let_ (ts := [i32]) ⟨.lshr i32, (.var 12, .imm (BitVec.ofNat 32 1), ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.imm (BitVec.ofNat 32 32), ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 3, .var 0, ())⟩ <|
        TFlat.let_ (ts := [i32]) ⟨.mul i32, (.imm (BitVec.ofNat 32 10), .var 12, ())⟩ <|
        TFlat.let_ (ts := [i32]) ⟨.add i32, (.imm (BitVec.ofNat 32 32), .var 0, ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 0, ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 8, .var 0, ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.imm (BitVec.ofNat 32 18), ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 11, .var 0, ())⟩ <|
        TFlat.load i32 (.var 0) <|
        TFlat.let_ (ts := [.bool]) ⟨.cmp .ne i32 .bool rfl,
          (.var 0, .imm (BitVec.ofNat 32 10), ())⟩ <|
        TFlat.jnz (.var 0)
          (TFlat.ret (.imm false, ())) <|
        TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.imm (BitVec.ofNat 32 0), ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 16, .var 0, ())⟩ <|
        TFlat.load i32 (.var 0) <|
        TFlat.let_ (ts := [.bool]) ⟨.cmp .uge i32 .bool rfl, (.var 17, .var 0, ())⟩ <|
        TFlat.jnz (.var 0)
          (TFlat.ret (.imm false, ())) <|
        TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 31, ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 12, .var 0, ())⟩ <|
        TFlat.load i32 (.var 0) <|
        TFlat.let_ (ts := [.bool]) ⟨.cmp .ne i32 .bool rfl,
          (.var 0, .imm (BitVec.ofNat 32 1), ())⟩ <|
        TFlat.jnz (.var 0)
          (TFlat.ret (.imm false, ())) <|
        TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 23, ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 22, .var 0, ())⟩ <|
        TFlat.load i32 (.var 0) <|
        TFlat.let_ (ts := [.bool]) ⟨.cmp .eq i32 .bool rfl,
          (.var 0, .imm (BitVec.ofNat 32 0), ())⟩ <|
        TFlat.jnz (.var 0)
          (TFlat.ret (.imm false, ())) <|
        TFlat.let_ (ts := [i32]) ⟨.mul i32, (.imm (BitVec.ofNat 32 12), .var 37, ())⟩ <|
        TFlat.let_ (ts := [i32]) ⟨.add i32, (.imm (BitVec.ofNat 32 32), .var 0, ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 0, ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 33, .var 0, ())⟩ <|
        TFlat.let_ (ts := [i32]) ⟨.mul i32, (.imm (BitVec.ofNat 32 14), .var 42, ())⟩ <|
        TFlat.let_ (ts := [i32]) ⟨.add i32, (.imm (BitVec.ofNat 32 32), .var 0, ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 0, ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 38, .var 0, ())⟩ <|
        TFlat.let_ (ts := [i32]) ⟨.mul i32, (.imm (BitVec.ofNat 32 22), .var 47, ())⟩ <|
        TFlat.let_ (ts := [i32]) ⟨.add i32, (.imm (BitVec.ofNat 32 32), .var 0, ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 0, ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 43, .var 0, ())⟩ <|
        TFlat.let_ (ts := [i32]) ⟨.mul i32, (.imm (BitVec.ofNat 32 30), .var 52, ())⟩ <|
        TFlat.let_ (ts := [i32]) ⟨.add i32, (.imm (BitVec.ofNat 32 32), .var 0, ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 0, ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 48, .var 0, ())⟩ <|
        TFlat.let_ (ts := [i32]) ⟨.mul i32, (.imm (BitVec.ofNat 32 34), .var 57, ())⟩ <|
        TFlat.let_ (ts := [i32]) ⟨.add i32, (.imm (BitVec.ofNat 32 32), .var 0, ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 0, ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 53, .var 0, ())⟩ <|
        TFlat.let_ (ts := [i32]) ⟨.mul i32, (.imm (BitVec.ofNat 32 38), .var 62, ())⟩ <|
        TFlat.let_ (ts := [i32]) ⟨.add i32, (.imm (BitVec.ofNat 32 32), .var 0, ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 0, ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 58, .var 0, ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 71, ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 27, .var 0, ())⟩ <|
        TFlat.load i32 (.var 0) <|
        TFlat.group (sig := [[i32, i32, i64, i64, .bool]])
          (TBlocks.cons (ts := [i32, i32, i64, i64, .bool])
            (TFlat.let_ (ts := [i64]) ⟨.sext 32 64, (.imm (BitVec.ofNat 32 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.lshr i64, (.var 3, .var 0, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 3, .var 0, ())⟩ <|
            TFlat.group (sig := [[]])
            (TBlocks.cons (ts := [])
            (TFlat.jnz (.var 3)
            (TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 83, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 64, .var 0, ())⟩ <|
            TFlat.store (t := i32) (.imm (BitVec.ofNat 32 2)) (.var 0) <|
            TFlat.let_ (ts := [i32]) ⟨.xor i32, (.var 86, .imm (BitVec.ofNat 32 1), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 0, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 68, .var 0, ())⟩ <|
            TFlat.store (t := i32) (.imm (BitVec.ofNat 32 1)) (.var 0) <|
            TFlat.ret (.imm true, ())) <|
            TFlat.ret (.imm false, ())) <|
            TBlocks.nil) <|
            TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.imm (BitVec.ofNat 32 11), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 73, .var 0, ())⟩ <|
            TFlat.load i32 (.var 0) <|
            TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 0, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.sub i64,
            (.imm (BitVec.ofNat 64 4294967295), .var 0, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.imm (BitVec.ofNat 32 11), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 79, .var 0, ())⟩ <|
            TFlat.group (sig := [[i32]])
            (TBlocks.cons (ts := [i32])
            (TFlat.store (t := i32) (.var 0) (.var 1) <|
            TFlat.jump (ts := []) 1 ()) <|
            TBlocks.nil) <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .uge i64 .bool rfl, (.var 9, .var 3, ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.jump (ts := [i32]) 0 (.imm (BitVec.ofNat 32 4294967295), ())) <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 5, .var 10, ())⟩ <|
            TFlat.let_ (ts := [i32]) ⟨.trunc 64 32, (.var 0, ())⟩ <|
            TFlat.jump (ts := [i32]) 0 (.var 0, ())) <|
          TBlocks.nil) <|
        TFlat.group (sig := [[i32, i32, i64, i64]])
          (TBlocks.cons (ts := [i32, i32, i64, i64])
            (TFlat.let_ (ts := [.bool]) ⟨.cmp .ne i32 .bool rfl,
            (.var 3, .imm (BitVec.ofNat 32 4294967295), ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 4, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 31, .var 0, ())⟩ <|
            TFlat.load i32 (.var 0) <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 6, .imm (BitVec.ofNat 64 1), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 9, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 31, .var 0, ())⟩ <|
            TFlat.load i32 (.var 0) <|
            TFlat.let_ (ts := [i32]) ⟨.and i32,
            (.var 0, .imm (BitVec.ofNat 32 2147483647), ())⟩ <|
            TFlat.let_ (ts := [i32]) ⟨.and i32,
            (.var 1, .imm (BitVec.ofNat 32 2147483648), ())⟩ <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .ne i32 .bool rfl,
            (.var 0, .imm (BitVec.ofNat 32 0), ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.let_ (ts := [.bool]) ⟨.cmp .eq i32 .bool rfl, (.var 2, .var 92, ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.jump (ts := [i32, i32, i64, i64, .bool]) 1
            (.var 17, .var 16, .var 8, .var 14, .imm false, ())) <|
            TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 3, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 74, .var 0, ())⟩ <|
            TFlat.load i32 (.var 0) <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .ne i32 .bool rfl,
            (.var 0, .imm (BitVec.ofNat 32 1), ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.jump (ts := [i32, i32, i64, i64, .bool]) 1
            (.var 22, .var 21, .var 13, .var 19, .imm false, ())) <|
            TFlat.jump (ts := [i32, i32, i64, i64]) 0 (.var 14, .var 22, .var 13, .var 19, ())) <|
            TFlat.group (sig := [[]])
            (TBlocks.cons (ts := [])
            (TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 13, .imm (BitVec.ofNat 64 1), ())⟩ <|
            TFlat.let_ (ts := [i32]) ⟨.lshr i32, (.var 17, .imm (BitVec.ofNat 32 1), ())⟩ <|
            TFlat.let_ (ts := [i32]) ⟨.and i32, (.var 18, .imm (BitVec.ofNat 32 1), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 1, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 36, .var 0, ())⟩ <|
            TFlat.load i32 (.var 0) <|
            TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 5, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 35, .var 0, ())⟩ <|
            TFlat.load i32 (.var 0) <|
            TFlat.let_ (ts := [i32]) ⟨.xor i32, (.var 8, .imm (BitVec.ofNat 32 1), ())⟩ <|
            TFlat.let_ (ts := [i32]) ⟨.add i32, (.var 5, .var 0, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 0, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 36, .var 0, ())⟩ <|
            TFlat.load i32 (.var 0) <|
            TFlat.group (sig := [[]])
            (TBlocks.cons (ts := [])
            (TFlat.group (sig := [[i32, i32, i32]])
            (TBlocks.cons (ts := [i32, i32, i32])
            (TFlat.let_ (ts := [.bool]) ⟨.cmp .eq i32 .bool rfl,
            (.var 1, .imm (BitVec.ofNat 32 4294967295), ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.jump (ts := [i32, i32, i64, i64, .bool]) 4
            (.var 37, .var 36, .var 28, .var 20, .imm false, ())) <|
            TFlat.let_ (ts := [i32]) ⟨.add i32, (.var 14, .var 18, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 0, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 45, .var 0, ())⟩ <|
            TFlat.store (t := i32) (.var 5) (.var 0) <|
            TFlat.let_ (ts := [i32]) ⟨.add i32, (.var 18, .var 6, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 0, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 49, .var 0, ())⟩ <|
            TFlat.store (t := i32) (.var 121) (.var 0) <|
            TFlat.group (sig := [[]])
            (TBlocks.cons (ts := [])
            (TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 45, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 67, .var 0, ())⟩ <|
            TFlat.store (t := i32) (.var 15) (.var 0) <|
            TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 48, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 75, .var 0, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 15, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 83, .var 0, ())⟩ <|
            TFlat.load i32 (.var 0) <|
            TFlat.store (t := i32) (.var 0) (.var 4) <|
            TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 19, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 87, .var 0, ())⟩ <|
            TFlat.store (t := i32) (.var 58) (.var 0) <|
            TFlat.jump (ts := [i32, i32, i64, i64]) 4 (.var 50, .var 57, .var 49, .var 41, ())) <|
            TBlocks.nil) <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .eq i32 .bool rfl,
            (.var 44, .imm (BitVec.ofNat 32 4294967295), ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 122, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 78, .var 0, ())⟩ <|
            TFlat.store (t := i32) (.var 41) (.var 0) <|
            TFlat.jump (ts := []) 0 ()) <|
            TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 45, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 73, .var 0, ())⟩ <|
            TFlat.store (t := i32) (.var 41) (.var 0) <|
            TFlat.jump (ts := []) 0 ()) <|
            TBlocks.nil) <|
            TFlat.group (sig := [[i32]])
            (TBlocks.cons (ts := [i32])
            (TFlat.let_ (ts := [.bool]) ⟨.cmp .ult i32 .bool rfl, (.var 0, .var 7, ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.let_ (ts := [i32]) ⟨.add i32, (.var 12, .var 1, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 0, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 43, .var 0, ())⟩ <|
            TFlat.load i32 (.var 0) <|
            TFlat.group (sig := [[]])
            (TBlocks.cons (ts := [])
            (TFlat.let_ (ts := [i32]) ⟨.add i32, (.var 6, .imm (BitVec.ofNat 32 1), ())⟩ <|
            TFlat.jump (ts := [i32]) 1 (.var 0, ())) <|
            TBlocks.nil) <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .ne i32 .bool rfl, (.var 0, .var 116, ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 1, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 98, .var 0, ())⟩ <|
            TFlat.load i32 (.var 0) <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .eq i32 .bool rfl,
            (.var 0, .imm (BitVec.ofNat 32 1), ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.jump (ts := [i32, i32, i32]) 2 (.var 12, .var 12, .var 6, ())) <|
            TFlat.jump (ts := []) 0 ()) <|
            TFlat.jump (ts := []) 0 ()) <|
            TFlat.jump (ts := [i32, i32, i32]) 1
            (.var 1, .imm (BitVec.ofNat 32 4294967295), .imm (BitVec.ofNat 32 0), ())) <|
            TBlocks.nil) <|
            TFlat.jump (ts := [i32]) 0 (.imm (BitVec.ofNat 32 2), ())) <|
            TBlocks.nil) <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .ne i32 .bool rfl, (.var 0, .var 109, ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 1, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 91, .var 0, ())⟩ <|
            TFlat.load i32 (.var 0) <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .eq i32 .bool rfl,
            (.var 0, .imm (BitVec.ofNat 32 1), ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 39, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 61, .var 0, ())⟩ <|
            TFlat.store (t := i32) (.var 9) (.var 0) <|
            TFlat.jump (ts := [i32, i32, i64, i64]) 2 (.var 34, .var 42, .var 33, .var 25, ())) <|
            TFlat.jump (ts := []) 0 ()) <|
            TFlat.jump (ts := []) 0 ()) <|
            TBlocks.nil) <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .ne i32 .bool rfl, (.var 2, .var 92, ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 3, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 74, .var 0, ())⟩ <|
            TFlat.load i32 (.var 0) <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .eq i32 .bool rfl,
            (.var 0, .imm (BitVec.ofNat 32 1), ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.jump (ts := [i32, i32, i64, i64]) 1 (.var 14, .var 22, .var 13, .var 19, ())
            ) <|
            TFlat.jump (ts := []) 0 ()) <|
            TFlat.jump (ts := []) 0 ()) <|
            TFlat.jump (ts := [i32, i32, i64, i64, .bool]) 1
            (.var 4, .var 3, .var 2, .var 1, .imm true, ())) <|
          TBlocks.nil) <|
        TFlat.jump (ts := [i32, i32, i64, i64]) 0
          (.var 0, .imm (BitVec.ofNat 32 4294967295), .imm (BitVec.ofNat 64 0),
            .imm (BitVec.ofNat 64 1), ())) <|
      TBlocks.nil) <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .ult i64 .bool rfl,
      (.var 0, .imm (BitVec.ofNat 64 24576), ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.jump (ts := [i64]) 0 (.imm (BitVec.ofNat 64 0), ())) <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .uge i64 .bool rfl,
      (.var 1, .imm (BitVec.ofNat 64 524288), ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.jump (ts := [i64]) 0 (.imm (BitVec.ofNat 64 8192), ())) <|
    TFlat.let_ (ts := [i64]) ⟨.sub i64, (.var 2, .imm (BitVec.ofNat 64 1312), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.udiv 64, (.var 0, .imm (BitVec.ofNat 64 45), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.and i64,
      (.var 0, .imm (BitVec.ofNat 64 18446744073709551552), ())⟩ <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .ult i64 .bool rfl,
      (.var 0, .imm (BitVec.ofNat 64 512), ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.jump (ts := [i64]) 0 (.imm (BitVec.ofNat 64 512), ())) <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .ugt i64 .bool rfl,
      (.var 1, .imm (BitVec.ofNat 64 8192), ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.jump (ts := [i64]) 0 (.imm (BitVec.ofNat 64 8192), ())) <|
    TFlat.jump (ts := [i64]) 0 (.var 2, ()) }

@[expose] def fns : List Fn := [flat0.toFn, flat1.toFn]

end LeanQbe.T.Examples.Kissat.Build.Inl.Kitten.Exports
