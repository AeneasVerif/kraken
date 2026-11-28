module

public import LeanQbe.T.Flat
public import LeanQbe.T.Module

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Inl.Heap.Exports

open LeanQbe.T

@[expose] def flat0 : TFlatFn := {
  name := "full_heap_up",
  as := [i64, i32],
  rs := [],
  body :=
    TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 0, ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 2, .imm (BitVec.ofNat 64 776), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .uge i64 .bool rfl, (.var 2, .var 0, ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.ret ()) <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 5, .imm (BitVec.ofNat 64 200), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 7, .imm (BitVec.ofNat 64 208), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 9, .imm (BitVec.ofNat 64 216), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 10, ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 4, .var 0, ())⟩ <|
    TFlat.load i32 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 0, ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 16, .imm (BitVec.ofNat 64 248), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .uge i64 .bool rfl, (.var 2, .var 0, ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.ret ()) <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 19, .imm (BitVec.ofNat 64 248), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 21, .imm (BitVec.ofNat 64 776), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .ugt i64 .bool rfl, (.var 2, .var 0, ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.ret ()) <|
    TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 9, ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 19, .var 0, ())⟩ <|
    TFlat.load i32 (.var 0) <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .ne i32 .bool rfl, (.var 0, .var 27, ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.ret ()) <|
    TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 28, ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 8), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 20, .var 0, ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.group (sig := [[i32]])
      (TBlocks.cons (ts := [i32])
        (TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 0, ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 29, .var 0, ())⟩ <|
        TFlat.store (t := i32) (.var 36) (.var 0) <|
        TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 36, ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 30, .var 0, ())⟩ <|
        TFlat.store (t := i32) (.var 6) (.var 0) <|
        TFlat.ret ()) <|
      TBlocks.nil) <|
    TFlat.group (sig := [[i32]])
      (TBlocks.cons (ts := [i32])
        (TFlat.let_ (ts := [.bool]) ⟨.cmp .ugt i32 .bool rfl,
          (.var 0, .imm (BitVec.ofNat 32 0), ())⟩ <|
        TFlat.jnz (.var 0)
          (TFlat.let_ (ts := [i32]) ⟨.sub i32, (.var 1, .imm (BitVec.ofNat 32 1), ())⟩ <|
          TFlat.let_ (ts := [i32]) ⟨.lshr i32, (.var 0, .imm (BitVec.ofNat 32 1), ())⟩ <|
          TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 0, ())⟩ <|
          TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
          TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 32, .var 0, ())⟩ <|
          TFlat.load i32 (.var 0) <|
          TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 0, ())⟩ <|
          TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 42, .imm (BitVec.ofNat 64 776), ())⟩ <|
          TFlat.load i64 (.var 0) <|
          TFlat.let_ (ts := [.bool]) ⟨.cmp .uge i64 .bool rfl, (.var 2, .var 0, ())⟩ <|
          TFlat.jnz (.var 0)
            (TFlat.jump (ts := [i32]) 1 (.var 11, ())) <|
          TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 4, ())⟩ <|
          TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 8), ())⟩ <|
          TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 36, .var 0, ())⟩ <|
          TFlat.load i64 (.var 0) <|
          TFlat.let_ (ts := [.bool]) ⟨.cmp .uge i64 .bool rfl, (.var 0, .var 16, ())⟩ <|
          TFlat.jnz (.var 0)
            (TFlat.jump (ts := [i32]) 1 (.var 16, ())) <|
          TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 16, ())⟩ <|
          TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
          TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 45, .var 0, ())⟩ <|
          TFlat.store (t := i32) (.var 12) (.var 0) <|
          TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 12, ())⟩ <|
          TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
          TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 46, .var 0, ())⟩ <|
          TFlat.store (t := i32) (.var 22) (.var 0) <|
          TFlat.jump (ts := [i32]) 0 (.var 19, ())) <|
        TFlat.jump (ts := [i32]) 1 (.var 1, ())) <|
      TBlocks.nil) <|
    TFlat.jump (ts := [i32]) 0 (.var 18, ()) }

@[expose] def flat1 : TFlatFn := {
  name := "full_heap_down",
  as := [i64, i32],
  rs := [],
  body :=
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 1, .imm (BitVec.ofNat 64 776), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 2, ())⟩ <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .uge i64 .bool rfl, (.var 0, .var 1, ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.ret ()) <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 5, .imm (BitVec.ofNat 64 200), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 7, .imm (BitVec.ofNat 64 208), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 9, .imm (BitVec.ofNat 64 216), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 10, ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 4, .var 0, ())⟩ <|
    TFlat.load i32 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 15, .imm (BitVec.ofNat 64 248), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 2, ())⟩ <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .uge i64 .bool rfl, (.var 0, .var 1, ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.ret ()) <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .ugt i64 .bool rfl, (.var 2, .var 16, ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.ret ()) <|
    TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 5, ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 15, .var 0, ())⟩ <|
    TFlat.load i32 (.var 0) <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .ne i32 .bool rfl, (.var 0, .var 23, ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.ret ()) <|
    TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 24, ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 8), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 16, .var 0, ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.group (sig := [[i32]])
      (TBlocks.cons (ts := [i32])
        (TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 0, ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 25, .var 0, ())⟩ <|
        TFlat.store (t := i32) (.var 32) (.var 0) <|
        TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 32, ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 26, .var 0, ())⟩ <|
        TFlat.store (t := i32) (.var 6) (.var 0) <|
        TFlat.ret ()) <|
      TBlocks.nil) <|
    TFlat.group (sig := [[i32]])
      (TBlocks.cons (ts := [i32])
        (TFlat.jnz (.imm true)
          (TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 0, ())⟩ <|
          TFlat.let_ (ts := [i64]) ⟨.sext 32 64, (.imm (BitVec.ofNat 32 1), ())⟩ <|
          TFlat.let_ (ts := [i64]) ⟨.shl i64, (.var 1, .var 0, ())⟩ <|
          TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 0, .imm (BitVec.ofNat 64 1), ())⟩ <|
          TFlat.let_ (ts := [.bool]) ⟨.cmp .uge i64 .bool rfl, (.var 0, .var 17, ())⟩ <|
          TFlat.jnz (.var 0)
            (TFlat.jump (ts := [i32]) 1 (.var 5, ())) <|
          TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 1, .imm (BitVec.ofNat 64 4), ())⟩ <|
          TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 29, .var 0, ())⟩ <|
          TFlat.load i32 (.var 0) <|
          TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 0, ())⟩ <|
          TFlat.let_ (ts := [.bool]) ⟨.cmp .uge i64 .bool rfl, (.var 0, .var 36, ())⟩ <|
          TFlat.jnz (.var 0)
            (TFlat.jump (ts := [i32]) 1 (.var 10, ())) <|
          TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 2, ())⟩ <|
          TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 8), ())⟩ <|
          TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 31, .var 0, ())⟩ <|
          TFlat.load i64 (.var 0) <|
          TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 10, .imm (BitVec.ofNat 64 1), ())⟩ <|
          TFlat.group (sig := [[i64, i32, i64]])
            (TBlocks.cons (ts := [i64, i32, i64])
            (TFlat.let_ (ts := [.bool]) ⟨.cmp .ule i64 .bool rfl, (.var 0, .var 19, ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.jump (ts := [i32]) 2 (.var 19, ())) <|
            TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 19, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 44, .var 0, ())⟩ <|
            TFlat.store (t := i32) (.var 5) (.var 0) <|
            TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 5, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 45, .var 0, ())⟩ <|
            TFlat.store (t := i32) (.var 25) (.var 0) <|
            TFlat.let_ (ts := [i32]) ⟨.trunc 64 32, (.var 9, ())⟩ <|
            TFlat.jump (ts := [i32]) 1 (.var 0, ())) <|
            TBlocks.nil) <|
          TFlat.let_ (ts := [.bool]) ⟨.cmp .ult i64 .bool rfl, (.var 0, .var 28, ())⟩ <|
          TFlat.jnz (.var 0)
            (TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 1, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 40, .var 0, ())⟩ <|
            TFlat.load i32 (.var 0) <|
            TFlat.group (sig := [[i64, i32, i64]])
            (TBlocks.cons (ts := [i64, i32, i64])
            (TFlat.jump (ts := [i64, i32, i64]) 1 (.var 2, .var 1, .var 0, ())) <|
            TBlocks.nil) <|
            TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 0, ())⟩ <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .ult i64 .bool rfl, (.var 0, .var 47, ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 2, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 8), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 42, .var 0, ())⟩ <|
            TFlat.load i64 (.var 0) <|
            TFlat.group (sig := [[i64, i32, i64]])
            (TBlocks.cons (ts := [i64, i32, i64])
            (TFlat.jump (ts := [i64, i32, i64]) 1 (.var 2, .var 1, .var 0, ())) <|
            TBlocks.nil) <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .ugt i64 .bool rfl, (.var 0, .var 11, ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.jump (ts := [i64, i32, i64]) 0 (.var 11, .var 7, .var 1, ())) <|
            TFlat.jump (ts := [i64, i32, i64]) 0 (.var 22, .var 18, .var 12, ())) <|
            TFlat.jump (ts := [i64, i32, i64]) 0 (.var 17, .var 13, .var 7, ())) <|
          TFlat.jump (ts := [i64, i32, i64]) 0 (.var 12, .var 8, .var 2, ())) <|
        TFlat.jump (ts := [i32]) 1 (.var 0, ())) <|
      TBlocks.nil) <|
    TFlat.jump (ts := [i32]) 0 (.var 14, ()) }

@[expose] def flat2 : TFlatFn := {
  name := "full_heap_push",
  as := [i64, i32],
  rs := [],
  body :=
    TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 0, ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 2, .imm (BitVec.ofNat 64 776), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .uge i64 .bool rfl, (.var 2, .var 0, ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.ret ()) <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 5, .imm (BitVec.ofNat 64 200), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 7, .imm (BitVec.ofNat 64 208), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 8, ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 2, .var 0, ())⟩ <|
    TFlat.load i32 (.var 0) <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .ne i32 .bool rfl,
      (.var 0, .imm (BitVec.ofNat 32 4294967295), ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.ret ()) <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 14, .imm (BitVec.ofNat 64 248), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 16, .imm (BitVec.ofNat 64 776), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .uge i64 .bool rfl, (.var 2, .var 0, ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.ret ()) <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 19, .imm (BitVec.ofNat 64 248), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [i32]) ⟨.trunc 64 32, (.var 0, ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 22, .imm (BitVec.ofNat 64 248), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 0, .imm (BitVec.ofNat 64 1), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 25, .imm (BitVec.ofNat 64 248), ())⟩ <|
    TFlat.store (t := i64) (.var 1) (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 4, ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 21, .var 0, ())⟩ <|
    TFlat.store (t := i32) (.var 28) (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 28, ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 22, .var 0, ())⟩ <|
    TFlat.store (t := i32) (.var 10) (.var 0) <|
    TFlat.group (sig := [[]])
      (TBlocks.cons (ts := [])
        (TFlat.ret ()) <|
      TBlocks.nil) <|
    TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 31, ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 33, .imm (BitVec.ofNat 64 776), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .uge i64 .bool rfl, (.var 2, .var 0, ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.jump (ts := []) 0 ()) <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 36, .imm (BitVec.ofNat 64 200), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 38, .imm (BitVec.ofNat 64 208), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 40, .imm (BitVec.ofNat 64 216), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 41, ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 4, .var 0, ())⟩ <|
    TFlat.load i32 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 0, ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 47, .imm (BitVec.ofNat 64 248), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .uge i64 .bool rfl, (.var 2, .var 0, ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.jump (ts := []) 0 ()) <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 50, .imm (BitVec.ofNat 64 248), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 52, .imm (BitVec.ofNat 64 776), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .ugt i64 .bool rfl, (.var 2, .var 0, ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.jump (ts := []) 0 ()) <|
    TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 9, ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 19, .var 0, ())⟩ <|
    TFlat.load i32 (.var 0) <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .ne i32 .bool rfl, (.var 0, .var 58, ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.jump (ts := []) 0 ()) <|
    TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 59, ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 8), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 20, .var 0, ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.group (sig := [[i32]])
      (TBlocks.cons (ts := [i32])
        (TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 0, ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 29, .var 0, ())⟩ <|
        TFlat.store (t := i32) (.var 67) (.var 0) <|
        TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 67, ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 30, .var 0, ())⟩ <|
        TFlat.store (t := i32) (.var 6) (.var 0) <|
        TFlat.jump (ts := []) 1 ()) <|
      TBlocks.nil) <|
    TFlat.group (sig := [[i32]])
      (TBlocks.cons (ts := [i32])
        (TFlat.let_ (ts := [.bool]) ⟨.cmp .ugt i32 .bool rfl,
          (.var 0, .imm (BitVec.ofNat 32 0), ())⟩ <|
        TFlat.jnz (.var 0)
          (TFlat.let_ (ts := [i32]) ⟨.sub i32, (.var 1, .imm (BitVec.ofNat 32 1), ())⟩ <|
          TFlat.let_ (ts := [i32]) ⟨.lshr i32, (.var 0, .imm (BitVec.ofNat 32 1), ())⟩ <|
          TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 0, ())⟩ <|
          TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
          TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 32, .var 0, ())⟩ <|
          TFlat.load i32 (.var 0) <|
          TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 0, ())⟩ <|
          TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 73, .imm (BitVec.ofNat 64 776), ())⟩ <|
          TFlat.load i64 (.var 0) <|
          TFlat.let_ (ts := [.bool]) ⟨.cmp .uge i64 .bool rfl, (.var 2, .var 0, ())⟩ <|
          TFlat.jnz (.var 0)
            (TFlat.jump (ts := [i32]) 1 (.var 11, ())) <|
          TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 4, ())⟩ <|
          TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 8), ())⟩ <|
          TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 36, .var 0, ())⟩ <|
          TFlat.load i64 (.var 0) <|
          TFlat.let_ (ts := [.bool]) ⟨.cmp .uge i64 .bool rfl, (.var 0, .var 16, ())⟩ <|
          TFlat.jnz (.var 0)
            (TFlat.jump (ts := [i32]) 1 (.var 16, ())) <|
          TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 16, ())⟩ <|
          TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
          TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 45, .var 0, ())⟩ <|
          TFlat.store (t := i32) (.var 12) (.var 0) <|
          TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 12, ())⟩ <|
          TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
          TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 46, .var 0, ())⟩ <|
          TFlat.store (t := i32) (.var 22) (.var 0) <|
          TFlat.jump (ts := [i32]) 0 (.var 19, ())) <|
        TFlat.jump (ts := [i32]) 1 (.var 1, ())) <|
      TBlocks.nil) <|
    TFlat.jump (ts := [i32]) 0 (.var 18, ()) }

@[expose] def flat3 : TFlatFn := {
  name := "full_heap_pop",
  as := [i64],
  rs := [i64],
  body :=
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 0, .imm (BitVec.ofNat 64 776), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 2, .imm (BitVec.ofNat 64 248), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .eq i64 .bool rfl,
      (.var 0, .imm (BitVec.ofNat 64 0), ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.ret (.imm (BitVec.ofNat 64 4294967295), ())) <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .ugt i64 .bool rfl, (.var 1, .var 3, ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.ret (.imm (BitVec.ofNat 64 4294967295), ())) <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 6, .imm (BitVec.ofNat 64 200), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 8, .imm (BitVec.ofNat 64 208), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.sext 32 64, (.imm (BitVec.ofNat 32 0), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 4, .var 0, ())⟩ <|
    TFlat.load i32 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.sub i64, (.var 10, .imm (BitVec.ofNat 64 1), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 15, .imm (BitVec.ofNat 64 248), ())⟩ <|
    TFlat.store (t := i64) (.var 1) (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 1, .imm (BitVec.ofNat 64 4), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 9, .var 0, ())⟩ <|
    TFlat.load i32 (.var 0) <|
    TFlat.group (sig := [[]])
      (TBlocks.cons (ts := [])
        (TFlat.group (sig := [[]])
          (TBlocks.cons (ts := [])
            (TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 5, ())⟩ <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .uge i64 .bool rfl, (.var 0, .var 18, ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.ret (.imm (BitVec.ofNat 64 4294967295), ())) <|
            TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 7, ())⟩ <|
            TFlat.ret (.var 0, ())) <|
          TBlocks.nil) <|
        TFlat.let_ (ts := [.bool]) ⟨.cmp .ugt i64 .bool rfl,
          (.var 4, .imm (BitVec.ofNat 64 0), ())⟩ <|
        TFlat.jnz (.var 0)
          (TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 1, ())⟩ <|
          TFlat.let_ (ts := [.bool]) ⟨.cmp .ult i64 .bool rfl, (.var 0, .var 19, ())⟩ <|
          TFlat.jnz (.var 0)
            (TFlat.let_ (ts := [i64]) ⟨.sext 32 64, (.imm (BitVec.ofNat 32 0), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 16, .var 0, ())⟩ <|
            TFlat.store (t := i32) (.var 6) (.var 0) <|
            TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 6, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 17, .var 0, ())⟩ <|
            TFlat.store (t := i32) (.imm (BitVec.ofNat 32 0)) (.var 0) <|
            TFlat.group (sig := [[]])
            (TBlocks.cons (ts := [])
            (TFlat.jump (ts := []) 1 ()) <|
            TBlocks.nil) <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 28, .imm (BitVec.ofNat 64 776), ())⟩ <|
            TFlat.load i64 (.var 0) <|
            TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 11, ())⟩ <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .uge i64 .bool rfl, (.var 0, .var 1, ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.jump (ts := []) 0 ()) <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 32, .imm (BitVec.ofNat 64 200), ())⟩ <|
            TFlat.load i64 (.var 0) <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 34, .imm (BitVec.ofNat 64 208), ())⟩ <|
            TFlat.load i64 (.var 0) <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 36, .imm (BitVec.ofNat 64 216), ())⟩ <|
            TFlat.load i64 (.var 0) <|
            TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 19, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 4, .var 0, ())⟩ <|
            TFlat.load i32 (.var 0) <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 42, .imm (BitVec.ofNat 64 248), ())⟩ <|
            TFlat.load i64 (.var 0) <|
            TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 2, ())⟩ <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .uge i64 .bool rfl, (.var 0, .var 1, ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.jump (ts := []) 0 ()) <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .ugt i64 .bool rfl, (.var 2, .var 16, ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.jump (ts := []) 0 ()) <|
            TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 5, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 15, .var 0, ())⟩ <|
            TFlat.load i32 (.var 0) <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .ne i32 .bool rfl, (.var 0, .var 32, ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.jump (ts := []) 0 ()) <|
            TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 33, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 8), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 16, .var 0, ())⟩ <|
            TFlat.load i64 (.var 0) <|
            TFlat.group (sig := [[i32]])
            (TBlocks.cons (ts := [i32])
            (TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 0, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 25, .var 0, ())⟩ <|
            TFlat.store (t := i32) (.var 41) (.var 0) <|
            TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 41, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 26, .var 0, ())⟩ <|
            TFlat.store (t := i32) (.var 6) (.var 0) <|
            TFlat.jump (ts := []) 1 ()) <|
            TBlocks.nil) <|
            TFlat.group (sig := [[i32]])
            (TBlocks.cons (ts := [i32])
            (TFlat.jnz (.imm true)
            (TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 0, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.sext 32 64, (.imm (BitVec.ofNat 32 1), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.shl i64, (.var 1, .var 0, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 0, .imm (BitVec.ofNat 64 1), ())⟩ <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .uge i64 .bool rfl, (.var 0, .var 17, ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.jump (ts := [i32]) 1 (.var 5, ())) <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 1, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 29, .var 0, ())⟩ <|
            TFlat.load i32 (.var 0) <|
            TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 0, ())⟩ <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .uge i64 .bool rfl, (.var 0, .var 36, ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.jump (ts := [i32]) 1 (.var 10, ())) <|
            TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 2, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 8), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 31, .var 0, ())⟩ <|
            TFlat.load i64 (.var 0) <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 10, .imm (BitVec.ofNat 64 1), ())⟩ <|
            TFlat.group (sig := [[i64, i32, i64]])
            (TBlocks.cons (ts := [i64, i32, i64])
            (TFlat.let_ (ts := [.bool]) ⟨.cmp .ule i64 .bool rfl, (.var 0, .var 19, ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.jump (ts := [i32]) 2 (.var 19, ())) <|
            TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 19, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 44, .var 0, ())⟩ <|
            TFlat.store (t := i32) (.var 5) (.var 0) <|
            TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 5, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 45, .var 0, ())⟩ <|
            TFlat.store (t := i32) (.var 25) (.var 0) <|
            TFlat.let_ (ts := [i32]) ⟨.trunc 64 32, (.var 9, ())⟩ <|
            TFlat.jump (ts := [i32]) 1 (.var 0, ())) <|
            TBlocks.nil) <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .ult i64 .bool rfl, (.var 0, .var 28, ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 1, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 40, .var 0, ())⟩ <|
            TFlat.load i32 (.var 0) <|
            TFlat.group (sig := [[i64, i32, i64]])
            (TBlocks.cons (ts := [i64, i32, i64])
            (TFlat.jump (ts := [i64, i32, i64]) 1 (.var 2, .var 1, .var 0, ())) <|
            TBlocks.nil) <|
            TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 0, ())⟩ <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .ult i64 .bool rfl, (.var 0, .var 47, ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 2, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 8), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 42, .var 0, ())⟩ <|
            TFlat.load i64 (.var 0) <|
            TFlat.group (sig := [[i64, i32, i64]])
            (TBlocks.cons (ts := [i64, i32, i64])
            (TFlat.jump (ts := [i64, i32, i64]) 1 (.var 2, .var 1, .var 0, ())) <|
            TBlocks.nil) <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .ugt i64 .bool rfl, (.var 0, .var 11, ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.jump (ts := [i64, i32, i64]) 0 (.var 11, .var 7, .var 1, ())) <|
            TFlat.jump (ts := [i64, i32, i64]) 0 (.var 22, .var 18, .var 12, ())) <|
            TFlat.jump (ts := [i64, i32, i64]) 0 (.var 17, .var 13, .var 7, ())) <|
            TFlat.jump (ts := [i64, i32, i64]) 0 (.var 12, .var 8, .var 2, ())) <|
            TFlat.jump (ts := [i32]) 1 (.var 0, ())) <|
            TBlocks.nil) <|
            TFlat.jump (ts := [i32]) 0 (.var 14, ())) <|
          TFlat.jump (ts := []) 0 ()) <|
        TFlat.jump (ts := []) 0 ()) <|
      TBlocks.nil) <|
    TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 5, ())⟩ <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .ult i64 .bool rfl, (.var 0, .var 18, ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 7, ())⟩ <|
      TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
      TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 13, .var 0, ())⟩ <|
      TFlat.store (t := i32) (.imm (BitVec.ofNat 32 4294967295)) (.var 0) <|
      TFlat.jump (ts := []) 0 ()) <|
    TFlat.jump (ts := []) 0 () }

@[expose] def fns : List Fn := [flat0.toFn, flat1.toFn, flat2.toFn, flat3.toFn]

end LeanQbe.T.Examples.Kissat.Build.Inl.Heap.Exports
