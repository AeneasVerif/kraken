module

public import LeanQbe.T.Flat
public import LeanQbe.T.Module

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Inl.Backtrack.Exports

open LeanQbe.T

@[expose] def flat0 : TFlatFn := {
  name := "full_assign_lvl",
  as := [i64, i32, i32, i32],
  rs := [],
  body :=
    TFlat.let_ (ts := [i32]) ⟨.lshr i32, (.var 2, .imm (BitVec.ofNat 32 1), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 0, ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 5, .imm (BitVec.ofNat 64 776), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .uge i64 .bool rfl, (.var 2, .var 0, ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.ret ()) <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 8, .imm (BitVec.ofNat 64 144), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 10, .imm (BitVec.ofNat 64 768), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .uge i64 .bool rfl, (.var 2, .var 0, ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.ret ()) <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 13, .imm (BitVec.ofNat 64 64), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 14, ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 1, .var 0, ())⟩ <|
    TFlat.load i8 (.var 0) <|
    TFlat.let_ (ts := [i8]) ⟨.trunc 32 8, (.imm (BitVec.ofNat 32 0), ())⟩ <|
    TFlat.let_ (ts := [i32]) ⟨.sext 8 32, (.var 1, ())⟩ <|
    TFlat.let_ (ts := [i32]) ⟨.sext 8 32, (.var 1, ())⟩ <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .ne i32 .bool rfl, (.var 1, .var 0, ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.ret ()) <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 22, .imm (BitVec.ofNat 64 224), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 24, .imm (BitVec.ofNat 64 80), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 26, .imm (BitVec.ofNat 64 88), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 28, .imm (BitVec.ofNat 64 96), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 30, .imm (BitVec.ofNat 64 360), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 32, .imm (BitVec.ofNat 64 800), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 33, ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 20, .var 0, ())⟩ <|
    TFlat.let_ (ts := [i8]) ⟨.trunc 32 8, (.imm (BitVec.ofNat 32 1), ())⟩ <|
    TFlat.store (t := i8) (.var 0) (.var 1) <|
    TFlat.let_ (ts := [i32]) ⟨.xor i32, (.var 36, .imm (BitVec.ofNat 32 1), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 0, ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 24, .var 0, ())⟩ <|
    TFlat.let_ (ts := [i32]) ⟨.neg i32, (.imm (BitVec.ofNat 32 1), ())⟩ <|
    TFlat.let_ (ts := [i8]) ⟨.trunc 32 8, (.var 0, ())⟩ <|
    TFlat.store (t := i8) (.var 0) (.var 2) <|
    TFlat.group (sig := [[]])
      (TBlocks.cons (ts := [])
        (TFlat.group (sig := [[]])
          (TBlocks.cons (ts := [])
            (TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 38, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 18, .var 0, ())⟩ <|
            TFlat.store (t := i32) (.var 42) (.var 0) <|
            TFlat.group (sig := [[]])
            (TBlocks.cons (ts := [])
            (TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 41, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 15, .var 0, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 48, .imm (BitVec.ofNat 64 144), ())⟩ <|
            TFlat.load i64 (.var 0) <|
            TFlat.let_ (ts := [i32]) ⟨.trunc 64 32, (.var 0, ())⟩ <|
            TFlat.store (t := i32) (.var 0) (.var 3) <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 51, .imm (BitVec.ofNat 64 144), ())⟩ <|
            TFlat.load i64 (.var 0) <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 24, .var 0, ())⟩ <|
            TFlat.store (t := i32) (.var 54) (.var 0) <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 55, .imm (BitVec.ofNat 64 144), ())⟩ <|
            TFlat.load i64 (.var 0) <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 0, .imm (BitVec.ofNat 64 1), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 58, .imm (BitVec.ofNat 64 144), ())⟩ <|
            TFlat.store (t := i64) (.var 1) (.var 0) <|
            TFlat.ret ()) <|
            TBlocks.nil) <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .eq i32 .bool rfl,
            (.var 42, .imm (BitVec.ofNat 32 0), ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 42, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 20, .var 0, ())⟩ <|
            TFlat.store (t := i32) (.imm (BitVec.ofNat 32 4294967295)) (.var 0) <|
            TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 45, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 17, .var 0, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 48, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 20, .var 0, ())⟩ <|
            TFlat.load i32 (.var 0) <|
            TFlat.let_ (ts := [i32]) ⟨.not i32, (.imm (BitVec.ofNat 32 1), ())⟩ <|
            TFlat.let_ (ts := [i32]) ⟨.and i32, (.var 1, .var 0, ())⟩ <|
            TFlat.store (t := i32) (.var 0) (.var 6) <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 58, .imm (BitVec.ofNat 64 512), ())⟩ <|
            TFlat.load i64 (.var 0) <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 0, .imm (BitVec.ofNat 64 1), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 61, .imm (BitVec.ofNat 64 512), ())⟩ <|
            TFlat.store (t := i64) (.var 1) (.var 0) <|
            TFlat.jump (ts := []) 0 ()) <|
            TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 42, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 20, .var 0, ())⟩ <|
            TFlat.store (t := i32) (.var 47) (.var 0) <|
            TFlat.jump (ts := []) 0 ()) <|
          TBlocks.nil) <|
        TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 42, .imm (BitVec.ofNat 64 520), ())⟩ <|
        TFlat.load i64 (.var 0) <|
        TFlat.let_ (ts := [.bool]) ⟨.cmp .eq i64 .bool rfl,
          (.var 0, .imm (BitVec.ofNat 64 0), ())⟩ <|
        TFlat.jnz (.var 0)
          (TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 41, ())⟩ <|
          TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 22, .var 0, ())⟩ <|
          TFlat.group (sig := [[i32]])
            (TBlocks.cons (ts := [i32])
            (TFlat.let_ (ts := [i8]) ⟨.trunc 32 8, (.var 0, ())⟩ <|
            TFlat.store (t := i8) (.var 0) (.var 2) <|
            TFlat.jump (ts := []) 1 ()) <|
            TBlocks.nil) <|
          TFlat.let_ (ts := [i32]) ⟨.and i32, (.var 46, .imm (BitVec.ofNat 32 1), ())⟩ <|
          TFlat.let_ (ts := [.bool]) ⟨.cmp .ne i32 .bool rfl,
            (.var 0, .imm (BitVec.ofNat 32 0), ())⟩ <|
          TFlat.jnz (.var 0)
            (TFlat.let_ (ts := [i32]) ⟨.neg i32, (.imm (BitVec.ofNat 32 1), ())⟩ <|
            TFlat.let_ (ts := [i8]) ⟨.trunc 32 8, (.var 0, ())⟩ <|
            TFlat.let_ (ts := [i32]) ⟨.sext 8 32, (.var 0, ())⟩ <|
            TFlat.jump (ts := [i32]) 0 (.var 0, ())) <|
          TFlat.let_ (ts := [i8]) ⟨.trunc 32 8, (.imm (BitVec.ofNat 32 1), ())⟩ <|
          TFlat.let_ (ts := [i32]) ⟨.sext 8 32, (.var 0, ())⟩ <|
          TFlat.jump (ts := [i32]) 0 (.var 0, ())) <|
        TFlat.jump (ts := []) 0 ()) <|
      TBlocks.nil) <|
    TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 38, ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 10, .var 0, ())⟩ <|
    TFlat.load i32 (.var 0) <|
    TFlat.let_ (ts := [i32]) ⟨.and i32, (.var 0, .imm (BitVec.ofNat 32 1), ())⟩ <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .ne i32 .bool rfl,
      (.var 0, .imm (BitVec.ofNat 32 0), ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 48, .imm (BitVec.ofNat 64 792), ())⟩ <|
      TFlat.load i64 (.var 0) <|
      TFlat.let_ (ts := [.bool]) ⟨.cmp .ugt i64 .bool rfl,
        (.var 0, .imm (BitVec.ofNat 64 0), ())⟩ <|
      TFlat.jnz (.var 0)
        (TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 51, .imm (BitVec.ofNat 64 792), ())⟩ <|
        TFlat.load i64 (.var 0) <|
        TFlat.let_ (ts := [i64]) ⟨.sub i64, (.var 0, .imm (BitVec.ofNat 64 1), ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 54, .imm (BitVec.ofNat 64 792), ())⟩ <|
        TFlat.store (t := i64) (.var 1) (.var 0) <|
        TFlat.jump (ts := []) 0 ()) <|
      TFlat.jump (ts := []) 0 ()) <|
    TFlat.jump (ts := []) 0 () }

@[expose] def flat1 : TFlatFn := {
  name := "full_assign",
  as := [i64, i32, i32],
  rs := [],
  body :=
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 2, .imm (BitVec.ofNat 64 160), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [i32]) ⟨.trunc 64 32, (.var 0, ())⟩ <|
    TFlat.group (sig := [[]])
      (TBlocks.cons (ts := [])
        (TFlat.ret ()) <|
      TBlocks.nil) <|
    TFlat.let_ (ts := [i32]) ⟨.lshr i32, (.var 4, .imm (BitVec.ofNat 32 1), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 0, ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 7, .imm (BitVec.ofNat 64 776), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .uge i64 .bool rfl, (.var 2, .var 0, ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.jump (ts := []) 0 ()) <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 10, .imm (BitVec.ofNat 64 144), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 12, .imm (BitVec.ofNat 64 768), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .uge i64 .bool rfl, (.var 2, .var 0, ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.jump (ts := []) 0 ()) <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 15, .imm (BitVec.ofNat 64 64), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 16, ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 1, .var 0, ())⟩ <|
    TFlat.load i8 (.var 0) <|
    TFlat.let_ (ts := [i8]) ⟨.trunc 32 8, (.imm (BitVec.ofNat 32 0), ())⟩ <|
    TFlat.let_ (ts := [i32]) ⟨.sext 8 32, (.var 1, ())⟩ <|
    TFlat.let_ (ts := [i32]) ⟨.sext 8 32, (.var 1, ())⟩ <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .ne i32 .bool rfl, (.var 1, .var 0, ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.jump (ts := []) 0 ()) <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 24, .imm (BitVec.ofNat 64 224), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 26, .imm (BitVec.ofNat 64 80), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 28, .imm (BitVec.ofNat 64 88), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 30, .imm (BitVec.ofNat 64 96), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 32, .imm (BitVec.ofNat 64 360), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 34, .imm (BitVec.ofNat 64 800), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 35, ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 20, .var 0, ())⟩ <|
    TFlat.let_ (ts := [i8]) ⟨.trunc 32 8, (.imm (BitVec.ofNat 32 1), ())⟩ <|
    TFlat.store (t := i8) (.var 0) (.var 1) <|
    TFlat.let_ (ts := [i32]) ⟨.xor i32, (.var 38, .imm (BitVec.ofNat 32 1), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 0, ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 24, .var 0, ())⟩ <|
    TFlat.let_ (ts := [i32]) ⟨.neg i32, (.imm (BitVec.ofNat 32 1), ())⟩ <|
    TFlat.let_ (ts := [i8]) ⟨.trunc 32 8, (.var 0, ())⟩ <|
    TFlat.store (t := i8) (.var 0) (.var 2) <|
    TFlat.group (sig := [[]])
      (TBlocks.cons (ts := [])
        (TFlat.group (sig := [[]])
          (TBlocks.cons (ts := [])
            (TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 38, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 18, .var 0, ())⟩ <|
            TFlat.store (t := i32) (.var 42) (.var 0) <|
            TFlat.group (sig := [[]])
            (TBlocks.cons (ts := [])
            (TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 41, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 15, .var 0, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 50, .imm (BitVec.ofNat 64 144), ())⟩ <|
            TFlat.load i64 (.var 0) <|
            TFlat.let_ (ts := [i32]) ⟨.trunc 64 32, (.var 0, ())⟩ <|
            TFlat.store (t := i32) (.var 0) (.var 3) <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 53, .imm (BitVec.ofNat 64 144), ())⟩ <|
            TFlat.load i64 (.var 0) <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 24, .var 0, ())⟩ <|
            TFlat.store (t := i32) (.var 56) (.var 0) <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 57, .imm (BitVec.ofNat 64 144), ())⟩ <|
            TFlat.load i64 (.var 0) <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 0, .imm (BitVec.ofNat 64 1), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 60, .imm (BitVec.ofNat 64 144), ())⟩ <|
            TFlat.store (t := i64) (.var 1) (.var 0) <|
            TFlat.jump (ts := []) 3 ()) <|
            TBlocks.nil) <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .eq i32 .bool rfl,
            (.var 42, .imm (BitVec.ofNat 32 0), ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 42, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 20, .var 0, ())⟩ <|
            TFlat.store (t := i32) (.imm (BitVec.ofNat 32 4294967295)) (.var 0) <|
            TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 45, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 17, .var 0, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 48, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 20, .var 0, ())⟩ <|
            TFlat.load i32 (.var 0) <|
            TFlat.let_ (ts := [i32]) ⟨.not i32, (.imm (BitVec.ofNat 32 1), ())⟩ <|
            TFlat.let_ (ts := [i32]) ⟨.and i32, (.var 1, .var 0, ())⟩ <|
            TFlat.store (t := i32) (.var 0) (.var 6) <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 60, .imm (BitVec.ofNat 64 512), ())⟩ <|
            TFlat.load i64 (.var 0) <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 0, .imm (BitVec.ofNat 64 1), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 63, .imm (BitVec.ofNat 64 512), ())⟩ <|
            TFlat.store (t := i64) (.var 1) (.var 0) <|
            TFlat.jump (ts := []) 0 ()) <|
            TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 42, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 20, .var 0, ())⟩ <|
            TFlat.store (t := i32) (.var 49) (.var 0) <|
            TFlat.jump (ts := []) 0 ()) <|
          TBlocks.nil) <|
        TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 44, .imm (BitVec.ofNat 64 520), ())⟩ <|
        TFlat.load i64 (.var 0) <|
        TFlat.let_ (ts := [.bool]) ⟨.cmp .eq i64 .bool rfl,
          (.var 0, .imm (BitVec.ofNat 64 0), ())⟩ <|
        TFlat.jnz (.var 0)
          (TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 41, ())⟩ <|
          TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 22, .var 0, ())⟩ <|
          TFlat.group (sig := [[i32]])
            (TBlocks.cons (ts := [i32])
            (TFlat.let_ (ts := [i8]) ⟨.trunc 32 8, (.var 0, ())⟩ <|
            TFlat.store (t := i8) (.var 0) (.var 2) <|
            TFlat.jump (ts := []) 1 ()) <|
            TBlocks.nil) <|
          TFlat.let_ (ts := [i32]) ⟨.and i32, (.var 48, .imm (BitVec.ofNat 32 1), ())⟩ <|
          TFlat.let_ (ts := [.bool]) ⟨.cmp .ne i32 .bool rfl,
            (.var 0, .imm (BitVec.ofNat 32 0), ())⟩ <|
          TFlat.jnz (.var 0)
            (TFlat.let_ (ts := [i32]) ⟨.neg i32, (.imm (BitVec.ofNat 32 1), ())⟩ <|
            TFlat.let_ (ts := [i8]) ⟨.trunc 32 8, (.var 0, ())⟩ <|
            TFlat.let_ (ts := [i32]) ⟨.sext 8 32, (.var 0, ())⟩ <|
            TFlat.jump (ts := [i32]) 0 (.var 0, ())) <|
          TFlat.let_ (ts := [i8]) ⟨.trunc 32 8, (.imm (BitVec.ofNat 32 1), ())⟩ <|
          TFlat.let_ (ts := [i32]) ⟨.sext 8 32, (.var 0, ())⟩ <|
          TFlat.jump (ts := [i32]) 0 (.var 0, ())) <|
        TFlat.jump (ts := []) 0 ()) <|
      TBlocks.nil) <|
    TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 38, ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 10, .var 0, ())⟩ <|
    TFlat.load i32 (.var 0) <|
    TFlat.let_ (ts := [i32]) ⟨.and i32, (.var 0, .imm (BitVec.ofNat 32 1), ())⟩ <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .ne i32 .bool rfl,
      (.var 0, .imm (BitVec.ofNat 32 0), ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 50, .imm (BitVec.ofNat 64 792), ())⟩ <|
      TFlat.load i64 (.var 0) <|
      TFlat.let_ (ts := [.bool]) ⟨.cmp .ugt i64 .bool rfl,
        (.var 0, .imm (BitVec.ofNat 64 0), ())⟩ <|
      TFlat.jnz (.var 0)
        (TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 53, .imm (BitVec.ofNat 64 792), ())⟩ <|
        TFlat.load i64 (.var 0) <|
        TFlat.let_ (ts := [i64]) ⟨.sub i64, (.var 0, .imm (BitVec.ofNat 64 1), ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 56, .imm (BitVec.ofNat 64 792), ())⟩ <|
        TFlat.store (t := i64) (.var 1) (.var 0) <|
        TFlat.jump (ts := []) 0 ()) <|
      TFlat.jump (ts := []) 0 ()) <|
    TFlat.jump (ts := []) 0 () }

@[expose] def fns : List Fn := [flat0.toFn, flat1.toFn]

end LeanQbe.T.Examples.Kissat.Build.Inl.Backtrack.Exports
